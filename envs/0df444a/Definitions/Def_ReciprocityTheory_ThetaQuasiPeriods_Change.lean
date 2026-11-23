-- Prove2me | Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
-- name    : ReciprocityTheory_ThetaQuasiPeriods_Change
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:28.855011+00:00
-- url     : https://prove2.me/theorems/a003fd8e-0b1b-4e1d-9ac3-a2716475347a
-- title:
--   Change
-- statement:
--   Definitions and structural lemmas for Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/Change.lean

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
namespace ReciprocityTheory.PTheta
variable {ι : Type*} [Fintype ι]
def transpEquiv [DecidableEq ι] (U : (Matrix ι ι ℤ)ˣ) : (ι → ℤ) ≃ (ι → ℤ) where
  toFun l := (U : Matrix ι ι ℤ)ᵀ *ᵥ l
  invFun m := ((U⁻¹ : (Matrix ι ι ℤ)ˣ) : Matrix ι ι ℤ)ᵀ *ᵥ m
  left_inv l := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
      Matrix.one_mulVec]
  right_inv m := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
      Matrix.one_mulVec]
end ReciprocityTheory.PTheta


