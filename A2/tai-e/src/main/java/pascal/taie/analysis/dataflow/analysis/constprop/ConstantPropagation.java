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

import org.checkerframework.checker.units.qual.C;
import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

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
        CPFact fact = new CPFact();
        IR ir = cfg.getIR();
        for (Var param : ir.getParams()) {
            if (canHoldInt(param)) {
                fact.update(param, Value.getNAC());
            }
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var var : fact.keySet()) {
            Value newVal = fact.get(var);
            if (target.get(var) != Value.getUndef()) {
                target.update(var, meetValue(newVal, target.get(var)));
            } else {
                target.update(var, newVal);
            }
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        if (v1.isUndef()) {
            return v2;
        }
        if (v2.isUndef()) {
            return v1;
        }

        if (v1.isConstant() && v2.isConstant()) {
            if (v1.getConstant() == v2.getConstant()) {
                return v1;
            } else {
                return Value.getNAC();
            }
        }

        return null;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact outCopy = in.copy();

        if (stmt instanceof DefinitionStmt defStmt) {
            LValue lvalue = defStmt.getLValue();
            if (lvalue instanceof Var lhs) {
                if (canHoldInt(lhs)) {
                    Value rhsValue = evaluate(defStmt.getRValue(), in);
                    outCopy.update(lhs, rhsValue);
                }
            }
        }

        if (outCopy.equals(out)) {
            return false;
        } else {
            out.clear();
            for (Var var : outCopy.keySet()) {
                out.update(var, outCopy.get(var));
            }
            return true;
        }
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
        if (exp instanceof IntLiteral) {
            IntLiteral lit = (IntLiteral) exp;
            return Value.makeConstant(lit.getValue());
        }

        if (exp instanceof Var) {
            Var var = (Var) exp;
            if (!canHoldInt(var)) {
                return Value.getNAC();
            }
            Value val = in.get(var);
            if (val == null) {
                return Value.getUndef();
            }
            return val;
        }

        if (exp instanceof BinaryExp) {
            BinaryExp binExp = (BinaryExp) exp;
            Var op1 = binExp.getOperand1();
            Var op2 = binExp.getOperand2();

            Value val1 = in.get(op1);
            Value val2 = in.get(op2);

            if (binExp instanceof ArithmeticExp) {
                ArithmeticExp.Op op = ((ArithmeticExp) binExp).getOperator();
                if (op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM) {
                    if (val2 != null && val2.isConstant() && val2.getConstant() == 0) {
                        return Value.getUndef();
                    }
                }
            }

            if ((val1 != null && val1.isNAC()) || (val2 != null && val2.isNAC())) {
                return Value.getNAC();
            }

            if (val1 == null || val2 == null) {
                return Value.getUndef();
            }
            if (val1.isUndef() || val2.isUndef()) {
                return Value.getUndef();
            }

            if (val1.isConstant() && val2.isConstant()) {
                int i1 = val1.getConstant();
                int i2 = val2.getConstant();

                if (binExp instanceof ArithmeticExp) {
                    ArithmeticExp.Op op = ((ArithmeticExp) binExp).getOperator();
                    if ((op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM) && i2 == 0) {
                        return Value.getUndef();
                    }
                    return computeArithmetic(op, i1, i2);
                } else if (binExp instanceof ConditionExp) {
                    ConditionExp.Op op = ((ConditionExp) binExp).getOperator();
                    boolean result = computeCondition(op, i1, i2);
                    return Value.makeConstant(result ? 1 : 0);
                } else if (binExp instanceof ShiftExp) {
                    ShiftExp.Op op = ((ShiftExp) binExp).getOperator();
                    int shiftDistance = i2 & 0x1F;
                    return computeShift(op, i1, shiftDistance);
                } else if (binExp instanceof BitwiseExp) {
                    BitwiseExp.Op op = ((BitwiseExp) binExp).getOperator();
                    return computeBitwise(op, i1, i2);
                }
            }

            return Value.getNAC();
        }

        return Value.getNAC();
    }

    private static Value computeArithmetic(ArithmeticExp.Op op, int i1, int i2) {
        int result;
        switch (op) {
            case ADD: result = i1 + i2; break;
            case SUB: result = i1 - i2; break;
            case MUL: result = i1 * i2; break;
            case DIV: result = i1 / i2; break;
            case REM: result = i1 % i2; break;
            default: throw new IllegalArgumentException("Unknown arithmetic op: " + op);
        }
        return Value.makeConstant(result);
    }

    private static boolean computeCondition(ConditionExp.Op op, int i1, int i2) {
        switch (op) {
            case EQ: return i1 == i2;
            case NE: return i1 != i2;
            case LT: return i1 < i2;
            case GT: return i1 > i2;
            case LE: return i1 <= i2;
            case GE: return i1 >= i2;
            default: throw new IllegalArgumentException("Unknown condition op: " + op);
        }
    }

    private static Value computeShift(ShiftExp.Op op, int i1, int shift) {
        int result;
        switch (op) {
            case SHL: result = i1 << shift; break;
            case SHR: result = i1 >> shift; break;
            case USHR: result = i1 >>> shift; break;
            default: throw new IllegalArgumentException("Unknown shift op: " + op);
        }
        return Value.makeConstant(result);
    }

    private static Value computeBitwise(BitwiseExp.Op op, int i1, int i2) {
        int result;
        switch (op) {
            case OR: result = i1 | i2; break;
            case AND: result = i1 & i2; break;
            case XOR: result = i1 ^ i2; break;
            default: throw new IllegalArgumentException("Unknown bitwise op: " + op);
        }
        return Value.makeConstant(result);
    }
}
