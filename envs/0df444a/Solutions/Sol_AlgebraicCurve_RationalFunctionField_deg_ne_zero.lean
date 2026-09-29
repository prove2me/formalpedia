-- Prove2me | solution 1 for AlgebraicCurve.RationalFunctionField.deg_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/494a1722-ba29-5743-be03-96e4b40d3f61

import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_deg_eq_one_of_forall_ne_ofHeightOneSpectrum
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_deg_ofHeightOneSpectrum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_deg_ne_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

open AlgebraicCurve IsDedekindDomain Polynomial

theorem solution {K : Type*} [Field K] (v : Place K (RatFunc K)) : v.deg ≠ 0 := by
  by_cases h : ∀ w : HeightOneSpectrum K[X], v ≠ Place.ofHeightOneSpectrum w
  · rw [RationalFunctionField.deg_eq_one_of_forall_ne_ofHeightOneSpectrum v h]
    exact one_ne_zero
  · obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum w := by
      simpa using h
    subst hw
    obtain ⟨p, hp⟩ := Submodule.IsPrincipal.principal w.asIdeal
    rw [RationalFunctionField.deg_ofHeightOneSpectrum K hp]
    have hp0 : p ≠ 0 := by
      intro h0
      apply w.ne_bot
      rw [hp, h0]
      exact Ideal.span_singleton_eq_bot.mpr rfl
    have hprime : Prime p := by
      have hpr := w.isPrime
      rw [hp] at hpr
      exact (Ideal.span_singleton_prime hp0).mp hpr
    exact (natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hprime.irreducible)).ne'

end S_AlgebraicCurve_RationalFunctionField_deg_ne_zero
end P2MW
export P2MW.S_AlgebraicCurve_RationalFunctionField_deg_ne_zero (solution)
