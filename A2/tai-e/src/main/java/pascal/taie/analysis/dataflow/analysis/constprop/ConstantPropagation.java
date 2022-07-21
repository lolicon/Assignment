/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import fj.test.Bool;
import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        final CPFact fact = new CPFact();
        cfg.getIR().getParams().forEach(v -> fact.update(v, Value.getNAC()));
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.forEach((key, value) -> {
            final Value exists = target.get(key);
            target.update(key, meetValue(value, exists));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isUndef() || v2.isNAC()) {
            return v2;
        } else if (v1.isNAC() || v2.isUndef()) {
            return v1;
        } else if (v1.getConstant() == v2.getConstant()) {
            return v1;
        } else {
            return Value.getNAC();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        var backup = new CPFact();
        backup.copyFrom(out);
        out.copyFrom(in);
        Boolean changed = stmt.accept(new StmtVisitor<>() {
            @Override
            public Boolean visitDefault(Stmt stmt) {
                return false;
            }

            @Override
            public Boolean visit(Invoke stmt) {
                final Var left = stmt.getLValue();
                if (left != null && canHoldInt(left)) {
                    return out.update(left, Value.getNAC());
                }
                return false;
            }

            // a = b
            @Override
            public Boolean visit(Copy stmt) {
                final Var left = stmt.getLValue();
                if (canHoldInt(left)) {
                    final Value value = evaluate(stmt.getRValue(), in);
                    return out.update(left, value);
                }
                return false;
            }

            // a = 1
            @Override
            public Boolean visit(AssignLiteral stmt) {
                final Var left = stmt.getLValue();
                if (canHoldInt(left)) {
                    final Value value = evaluate(stmt.getRValue(), in);
                    return out.update(left, value);
                }
                return false;
            }

            // a = b + c
            @Override
            public Boolean visit(Binary binary) {
                final Var left = binary.getLValue();
                final BinaryExp bin = binary.getRValue();
                var r1 = evaluate(bin.getOperand1(), in);
                var r2 = evaluate(bin.getOperand2(), in);
                if (canHoldInt(left)) {
                    if (!r1.isConstant() || !r2.isConstant()) {
                        return out.update(left, Value.getNAC());
                    } else {
                        int l = r1.getConstant();
                        int r = r2.getConstant();
                        Integer calculated = bin.accept(new ExpVisitor<>() {
                            @Override
                            public Integer visit(ShiftExp exp) {
                                return switch (exp.getOperator()) {
                                    case SHL -> l << r;
                                    case SHR -> l >> r;
                                    case USHR -> 1 >>> r;
                                };
                            }

                            @Override
                            public Integer visit(ConditionExp exp) {
                                return switch (exp.getOperator()) {
                                    case EQ -> l == r ? 1 : 0;
                                    case NE -> l != r ? 1 : 0;
                                    case LT -> l < r ? 1 : 0;
                                    case GT -> l > r ? 1 : 0;
                                    case LE -> l <= r ? 1 : 0;
                                    case GE -> l >= r ? 1 : 0;
                                };
                            }

                            @Override
                            public Integer visit(BitwiseExp exp) {
                                return switch (exp.getOperator()) {
                                    case OR -> l | r;
                                    case AND -> l & r;
                                    case XOR -> l ^ r;
                                };
                            }

                            @Override
                            public Integer visit(ArithmeticExp exp) {
                                return switch (exp.getOperator()) {
                                    case ADD -> l + r;
                                    case SUB -> l - r;
                                    case MUL -> l * r;
                                    case DIV -> l / r;
                                    case REM -> l % r;
                                };
                            }
                        });

                        if (calculated == null) {
                            throw new RuntimeException("actual expression type is: " + bin);
                        } else {
                            return out.update(left, Value.makeConstant(calculated));
                        }
                    }
                }
                return backup.copyFrom(out);
            }


            // a = -c
            @Override
            public Boolean visit(Unary stmt) {
                final Var left = stmt.getLValue();
                if (canHoldInt(left)) {
                    Value value = evaluate(stmt.getRValue(), in);
                    if (value.isConstant()) {
                        value = Value.makeConstant(-value.getConstant());
                    }
                    return out.update(left, value);
                }
                return false;
            }
        });
        return backup.copyFrom(out);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        return exp.accept(new ExpVisitor<Value>() {
            @Override
            public Value visit(IntLiteral literal) {
                return Value.makeConstant(literal.getValue());
            }

            @Override
            public Value visit(Var var) {
                return in.get(var);
            }

            @Override
            public Value visitDefault(Exp exp) {
                return Value.getNAC();
            }
        });
    }
}
