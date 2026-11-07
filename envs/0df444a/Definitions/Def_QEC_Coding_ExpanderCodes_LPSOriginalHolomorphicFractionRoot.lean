-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicFractionRoot
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicFractionRoot
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:19:29.396805+00:00
-- url     : https://prove2.me/theorems/362aa105-9966-4ac0-80cf-8daaf3432a75
-- title:
--   LPSOriginal Holomorphic Fraction Root
-- statement:
--   Definitions and structural lemmas for LPSOriginal Holomorphic Fraction Root, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicFractionRoot.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
import Mathlib.Algebra.Polynomial.Homogenize
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
def lpsOriginalHolomorphicPointEvaluation (τ : ℍ) :
    LPSOriginalHolomorphicRing →+* ℂ where
  toFun f := f.val τ
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
end
end QEC.Coding.TannerLiftedProduct


