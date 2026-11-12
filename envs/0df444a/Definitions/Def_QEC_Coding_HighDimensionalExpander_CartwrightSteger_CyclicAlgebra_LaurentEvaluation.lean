-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_LaurentEvaluation
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_LaurentEvaluation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T14:14:01.966358+00:00
-- url     : https://prove2.me/theorems/17376e5a-bc9f-44f6-93b0-8cf342aef8ec
-- title:
--   Laurent Evaluation
-- statement:
--   Definitions and structural lemmas for Laurent Evaluation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/LaurentEvaluation.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstructionTheorem
import Mathlib.Algebra.Polynomial.Laurent
set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
noncomputable def splittingOnePlusYUnit
    (P : BasePrime) (r : Rank) : (SplittingFunctionField P r)ˣ :=
  Units.mk0 (onePlusY P r) (onePlusY_ne_zero P r)
noncomputable def onePlusYLaurentEvaluation
    (P : BasePrime) (r : Rank) :
    LaurentPolynomial (ConstantExtension P r) →+*
      SplittingFunctionField P r :=
  LaurentPolynomial.eval₂
    (algebraMap (ConstantExtension P r) (SplittingFunctionField P r))
    (splittingOnePlusYUnit P r)
noncomputable def functionFieldOnePlusYUnit
    (P : BasePrime) : (FunctionField P)ˣ :=
  Units.mk0 (1 + RatFunc.X) (functionField_onePlusY_ne_zero P)
noncomputable def functionFieldOnePlusYLaurentEvaluation
    (P : BasePrime) :
    LaurentPolynomial (BaseField P) →+* FunctionField P :=
  LaurentPolynomial.eval₂
    (algebraMap (BaseField P) (FunctionField P))
    (functionFieldOnePlusYUnit P)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


