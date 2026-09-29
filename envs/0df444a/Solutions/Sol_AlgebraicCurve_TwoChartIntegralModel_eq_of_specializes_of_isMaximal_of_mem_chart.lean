-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.eq_of_specializes_of_isMaximal_of_mem_chart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/177fa7cf-91f5-517c-90f5-f12834fc1f6e

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_ringKrullDim_stalk_le_ringKrullDim_add_one
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_chartAlgFin
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_two_le_ringKrullDim_stalk_of_isMaximal_of_mem
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_jInvChartInf_mem_and_iotaInf_eq_of_not_mem_range_iotaFin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_eq_of_specializes_of_isMaximal_of_mem_chart

set_option autoImplicit false

universe u

open CategoryTheory IsLocalRing AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

namespace ClosedInX

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem ringKrullDim_stalk_iotaFin (y : ↥(XFin R F j)) :
    ringKrullDim ↑((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y)) =
      y.asIdeal.height := by
  obtain ⟨e, -, -⟩ := exists_stalk_iso_localization_chartAlgFin R F j y ⟨y, trivial, rfl⟩
  rw [ringKrullDim_eq_of_ringEquiv e.commRingCatIsoToRingEquiv]
  exact IsLocalization.AtPrime.ringKrullDim_eq_height y.asIdeal (Localization.AtPrime y.asIdeal)

theorem ringKrullDim_stalk_iotaInf (y : ↥(XInf R F j)) :
    ringKrullDim ↑((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιInf R F j).base y)) =
      y.asIdeal.height := by
  obtain ⟨e, -, -⟩ := exists_stalk_iso_localization_chartAlgInf R F j y ⟨y, trivial, rfl⟩
  rw [ringKrullDim_eq_of_ringEquiv e.commRingCatIsoToRingEquiv]
  exact IsLocalization.AtPrime.ringKrullDim_eq_height y.asIdeal (Localization.AtPrime y.asIdeal)

theorem le_of_specializes_iotaFin (y w : ↥(XFin R F j)) (h : (ιFin R F j).base y ⤳ (ιFin R F j).base w) :
    y.asIdeal ≤ w.asIdeal := by
  rw [(ιFin R F j).isOpenEmbedding.toIsEmbedding.toIsInducing.specializes_iff] at h
  exact (PrimeSpectrum.le_iff_specializes y w).mpr h

theorem le_of_specializes_iotaInf (y w : ↥(XInf R F j)) (h : (ιInf R F j).base y ⤳ (ιInf R F j).base w) :
    y.asIdeal ≤ w.asIdeal := by
  rw [(ιInf R F j).isOpenEmbedding.toIsEmbedding.toIsInducing.specializes_iff] at h
  exact (PrimeSpectrum.le_iff_specializes y w).mpr h

end ClosedInX

open ClosedInX in
theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (x : ↥(AlgebraicCurve.TwoChartIntegralModel R F j))

    (hx : (∃ y : ↥(XFin R F j), (ιFin R F j).base y = x ∧ y.asIdeal.IsMaximal ∧
        algebraMap R ↥(chartAlgFin R F j) ϖ ∈ y.asIdeal) ∨
      (∃ y : ↥(XInf R F j), (ιInf R F j).base y = x ∧ y.asIdeal.IsMaximal ∧
        algebraMap R ↥(chartAlgInf R F j) ϖ ∈ y.asIdeal))
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel R F j)) (hz : x ⤳ z) :
    z = x := by
  classical
  have hinj : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R K₀ F]
    exact (algebraMap K₀ F).injective.comp (IsFractionRing.injective R K₀)

  have hR : ringKrullDim R = 1 := IsDiscreteValuationRing.ringKrullDim_eq_one R
  have hub : ∀ z : ↥(AlgebraicCurve.TwoChartIntegralModel R F j),
      ringKrullDim ↑((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z) ≤ 2 := by
    intro z
    have h := ringKrullDim_stalk_le_ringKrullDim_add_one R F j z
    rw [hR] at h
    exact h

  have hlb : 2 ≤ ringKrullDim ↑((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk x) := by
    rcases hx with ⟨y, hyx, hymax, hyϖ⟩ | ⟨y, hyx, hymax, hyϖ⟩
    · rw [← hyx]
      exact two_le_ringKrullDim_stalk_of_isMaximal_of_mem R F j htj ϖ hϖ y hymax hyϖ
    ·
      rw [← hyx, ringKrullDim_stalk_iotaInf R F j y]
      haveI : Fact (j⁻¹ ≠ 0) := ⟨inv_ne_zero (Fact.out : j ≠ 0)⟩
      have htj' : Transcendental R j⁻¹ := fun h => htj (by simpa using h.inv)
      have h2 := two_le_ringKrullDim_stalk_of_isMaximal_of_mem R F j⁻¹ htj' ϖ hϖ y hymax hyϖ
      rwa [ringKrullDim_stalk_iotaFin R F j⁻¹ y] at h2

  have key : ∀ {A : Type u} [CommRing A] (p q : Ideal A) [p.IsPrime] [q.IsPrime],
      p ≤ q → (2 : WithBot ℕ∞) ≤ p.height → (q.height : WithBot ℕ∞) ≤ 2 → p = q := by
    intro A _ p q _ _ hle h2 hq2
    by_contra hne
    have hlt : p < q := lt_of_le_of_ne hle hne
    have hqfin : q.FiniteHeight := ⟨Or.inr (by
      intro htop
      rw [htop] at hq2
      exact absurd hq2 (by decide))⟩
    have hlt' := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
    have h2' : (2 : ℕ∞) ≤ p.height := WithBot.coe_le_coe.mp h2
    have hq2' : q.height ≤ (2 : ℕ∞) := WithBot.coe_le_coe.mp hq2
    exact absurd (lt_of_le_of_lt h2' (lt_of_lt_of_le hlt' hq2')) (lt_irrefl _)

  by_cases hzFin : z ∈ Set.range (ιFin R F j).base
  · obtain ⟨w, rfl⟩ := hzFin
    have hxFin : x ∈ Set.range (ιFin R F j).base :=
      hz.mem_open (ιFin R F j).isOpenEmbedding.isOpen_range ⟨w, rfl⟩
    obtain ⟨y, rfl⟩ := hxFin
    have hle := le_of_specializes_iotaFin R F j y w hz
    have h2 : (2 : WithBot ℕ∞) ≤ y.asIdeal.height := by rwa [ringKrullDim_stalk_iotaFin R F j y] at hlb
    have hw2 : (w.asIdeal.height : WithBot ℕ∞) ≤ 2 := by
      rw [← ringKrullDim_stalk_iotaFin R F j w]; exact hub _
    have := key y.asIdeal w.asIdeal hle h2 hw2
    rw [PrimeSpectrum.ext this.symm]
  · obtain ⟨w, -, rfl⟩ := exists_jInvChartInf_mem_and_iotaInf_eq_of_not_mem_range_iotaFin R F j z hzFin
    have hxInf : x ∈ Set.range (ιInf R F j).base :=
      hz.mem_open (ιInf R F j).isOpenEmbedding.isOpen_range ⟨w, rfl⟩
    obtain ⟨y, rfl⟩ := hxInf
    have hle := le_of_specializes_iotaInf R F j y w hz
    have h2 : (2 : WithBot ℕ∞) ≤ y.asIdeal.height := by rwa [ringKrullDim_stalk_iotaInf R F j y] at hlb
    have hw2 : (w.asIdeal.height : WithBot ℕ∞) ≤ 2 := by
      rw [← ringKrullDim_stalk_iotaInf R F j w]; exact hub _
    have := key y.asIdeal w.asIdeal hle h2 hw2
    rw [PrimeSpectrum.ext this.symm]

end S_AlgebraicCurve_TwoChartIntegralModel_eq_of_specializes_of_isMaximal_of_mem_chart
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_eq_of_specializes_of_isMaximal_of_mem_chart (solution)
