-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SwapNegApply
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SwapNegApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:54.535546+00:00
-- url     : https://prove2.me/theorems/f549e74c-3031-48d8-8c2c-134d4840ce79
-- title:
--   Swap Neg Apply
-- statement:
--   Definitions and structural lemmas for Swap Neg Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SwapNegApply.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SwapSlice
open GlobalTheory.WeilM
variable {k κ Y : Type}
def barL (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ) where
  toFun Φ := fun y => starRingEnd ℂ (ι (fun x => starRingEnd ℂ (Φ x)) y)
  map_add' Φ Ψ := by
    funext y
    have e : (fun x => starRingEnd ℂ ((Φ + Ψ) x)) = (fun x => starRingEnd ℂ (Φ x)) + fun x => starRingEnd ℂ (Ψ x) := by
      funext x; simp
    show starRingEnd ℂ (ι (fun x => starRingEnd ℂ ((Φ + Ψ) x)) y) = _
    rw [e, map_add, Pi.add_apply, map_add]
    rfl
  map_smul' c Φ := by
    funext y
    have e : (fun x => starRingEnd ℂ ((c • Φ) x)) = starRingEnd ℂ c • fun x => starRingEnd ℂ (Φ x) := by
      funext x; simp
    show starRingEnd ℂ (ι (fun x => starRingEnd ℂ ((c • Φ) x)) y) = _
    rw [e, map_smul, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_conj]
    rfl
def sliceT (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) : ((κ ⊕ κ → k) → ℂ) →ₗ[ℂ] (Y × Y → ℂ) where
  toFun Φ := fun Z => barL ι (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z.1) Z.2
  map_add' Φ Ψ := by
    funext Z
    have e : (fun x₂ => ι (fun x₁ => (Φ + Ψ) (Sum.elim x₁ x₂)) Z.1) =
        (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z.1) + fun x₂ => ι (fun x₁ => Ψ (Sum.elim x₁ x₂)) Z.1 := by
      funext x₂
      have e' : (fun x₁ => (Φ + Ψ) (Sum.elim x₁ x₂)) = (fun x₁ => Φ (Sum.elim x₁ x₂)) + fun x₁ => Ψ (Sum.elim x₁ x₂) := rfl
      rw [e', map_add]
      rfl
    show barL ι (fun x₂ => ι (fun x₁ => (Φ + Ψ) (Sum.elim x₁ x₂)) Z.1) Z.2 = _
    rw [e, map_add]
    rfl
  map_smul' c Φ := by
    funext Z
    have e : (fun x₂ => ι (fun x₁ => (c • Φ) (Sum.elim x₁ x₂)) Z.1) =
        c • fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z.1 := by
      funext x₂
      have e' : (fun x₁ => (c • Φ) (Sum.elim x₁ x₂)) = c • fun x₁ => Φ (Sum.elim x₁ x₂) := rfl
      rw [e', map_smul]
      rfl
    show barL ι (fun x₂ => ι (fun x₁ => (c • Φ) (Sum.elim x₁ x₂)) Z.1) Z.2 = _
    rw [e, map_smul]
    rfl
def swapNeg [Neg Y] (Z : Y × Y) : Y × Y := (-Z.2, -Z.1)
end GlobalTheory.SwapSlice


