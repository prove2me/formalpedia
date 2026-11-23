-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsValuationSubringLeDominatingOfFractionFiel
-- name    : Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsValuationSubringLeDominatingOfFractionFiel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:48.583523+00:00
-- url     : https://prove2.me/theorems/e82cf25a-96ed-4025-b246-57d8d590fe10
-- title:
--   Exists Valuation Subring Le Dominating Of Fraction Fiel
-- statement:
--   Definitions and structural lemmas for Exists Valuation Subring Le Dominating Of Fraction Fiel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsValuationSubringLeDominatingOfFractionFiel.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
namespace GlobalTheory
def compositeValuationSubring {L : Type*} [Field L] (W : ValuationSubring L)
    (V : ValuationSubring (ResidueField W)) : ValuationSubring L where
  toSubring := (V.toSubring.comap (residue W)).map W.subtype
  mem_or_inv_mem' := by
    intro x
    by_cases hx : x ∈ W
    · by_cases hx' : x⁻¹ ∈ W
      · rcases eq_or_ne x 0 with rfl | hx0
        · exact Or.inl (Subring.zero_mem _)
        have hmul : residue W ⟨x, hx⟩ * residue W ⟨x⁻¹, hx'⟩ = 1 := by
          rw [← map_mul, ← map_one (residue W)]
          congr 1
          exact Subtype.ext (mul_inv_cancel₀ hx0)
        rcases V.mem_or_inv_mem (residue W ⟨x, hx⟩) with h | h
        · exact Or.inl ⟨⟨x, hx⟩, h, rfl⟩
        · refine Or.inr ⟨⟨x⁻¹, hx'⟩, ?_, rfl⟩
          rw [← eq_inv_of_mul_eq_one_right hmul] at h
          exact h
      · refine Or.inl ⟨⟨x, hx⟩, ?_, rfl⟩
        have hm : (⟨x, hx⟩ : W) ∈ maximalIdeal W := by
          rw [← ValuationSubring.coe_mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]
          exact Or.inr hx'
        have h0 : residue W ⟨x, hx⟩ = 0 := (residue_eq_zero_iff _).2 hm
        change residue W ⟨x, hx⟩ ∈ V
        rw [h0]
        exact V.zero_mem
    · have hx' : x⁻¹ ∈ W := (W.mem_or_inv_mem x).resolve_left hx
      refine Or.inr ⟨⟨x⁻¹, hx'⟩, ?_, rfl⟩
      have hm : (⟨x⁻¹, hx'⟩ : W) ∈ maximalIdeal W := by
        rw [← ValuationSubring.coe_mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]
        exact Or.inr (by simpa using hx)
      have h0 : residue W ⟨x⁻¹, hx'⟩ = 0 := (residue_eq_zero_iff _).2 hm
      change residue W ⟨x⁻¹, hx'⟩ ∈ V
      rw [h0]
      exact V.zero_mem
end GlobalTheory


