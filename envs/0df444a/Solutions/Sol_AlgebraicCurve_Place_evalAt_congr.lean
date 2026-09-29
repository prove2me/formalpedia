-- Prove2me | solution 1 for AlgebraicCurve.Place.evalAt_congr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/f7e2886f-311b-5b13-ac48-211cc6da7ce4

import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_maximalIdeal_iff_adicValuation_lt_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_evalAt_congr
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

open IsDedekindDomain WithZero IsLocalRing AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) (h : f - g = 0 ∨ 0 < v.ord (f - g)) : v.evalAt f = v.evalAt g := by
  rcases h with h | h
  · rw [sub_eq_zero] at h
    rw [h]
  have hsub : f - g ∈ v.toValuationSubring := sub_mem hf hg

  have hmax : ∀ {x : F} (hx : x ∈ v.toValuationSubring), 0 < v.ord x →
      (⟨x, hx⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    intro x hx hpos
    rcases eq_or_ne x 0 with rfl | hx0
    · exact Submodule.zero_mem _
    rw [v.mem_maximalIdeal_iff_adicValuation_lt_one]
    have hne : v.adicValuation x ≠ 0 := v.adicValuation_ne_zero hx0
    rw [← exp_log hne, show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_lt_exp]
    have : v.ord x = -log (v.adicValuation x) := rfl
    omega
  have hmem : (⟨f, hf⟩ : v.toValuationSubring) - ⟨g, hg⟩ ∈
      IsLocalRing.maximalIdeal v.toValuationSubring := by
    have : (⟨f, hf⟩ : v.toValuationSubring) - ⟨g, hg⟩ = ⟨f - g, hsub⟩ := rfl
    rw [this]
    exact hmax hsub h
  have hres : residue v.toValuationSubring (⟨f, hf⟩ : v.toValuationSubring)
      = residue v.toValuationSubring (⟨g, hg⟩ : v.toValuationSubring) := by
    rw [← sub_eq_zero, ← map_sub]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hmem
  rw [v.evalAt_of_mem hf, v.evalAt_of_mem hg, hres]

end S_AlgebraicCurve_Place_evalAt_congr
end P2MW
export P2MW.S_AlgebraicCurve_Place_evalAt_congr (solution)
