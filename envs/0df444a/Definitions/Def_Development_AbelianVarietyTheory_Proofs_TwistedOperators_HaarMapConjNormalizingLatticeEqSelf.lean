-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarMapConjNormalizingLatticeEqSelf
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarMapConjNormalizingLatticeEqSelf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:38.272586+00:00
-- url     : https://prove2.me/theorems/9150b809-b017-413e-8962-183811f74ce5
-- title:
--   Haar Map Conj Normalizing Lattice Eq Self
-- statement:
--   Definitions and structural lemmas for Haar Map Conj Normalizing Lattice Eq Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarMapConjNormalizingLatticeEqSelf.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NullMeasurableSetShearImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Function
open scoped Pointwise
namespace GlobalTheory.UnfoldNormal
def conjEquiv {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (N : Subgroup H)
    (γ : H) (h1 : ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (h2 : ∀ n ∈ N, γ⁻¹ * n * γ⁻¹⁻¹ ∈ N) : N ≃ₜ* N where
  toFun n := ⟨γ * n * γ⁻¹, h1 n n.2⟩
  invFun n := ⟨γ⁻¹ * n * γ⁻¹⁻¹, h2 n n.2⟩
  left_inv n := by ext; simp [mul_assoc]
  right_inv n := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
end GlobalTheory.UnfoldNormal


