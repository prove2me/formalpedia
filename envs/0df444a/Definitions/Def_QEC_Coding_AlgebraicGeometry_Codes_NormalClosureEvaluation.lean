-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation
-- name    : QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:21:11.78923+00:00
-- url     : https://prove2.me/theorems/d073d201-0061-4bff-aa28-742d4fc65b2b
-- title:
--   Normal Closure Evaluation
-- statement:
--   Definitions and structural lemmas for Normal Closure Evaluation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureEvaluation.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_ConstantFieldTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationDivisor_selected_eq_zero

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
def f256MultiplicationCode (i : ℕ) : LinearCode F256 (Fin (f256GarciaStichtenothLength i)) :=
  agEvaluationCode (f256MultiplicationDivisor i) (f256GarciaStichtenothSelectedRationalPlace i)
    (f256MultiplicationDivisor_selected_eq_zero i)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


