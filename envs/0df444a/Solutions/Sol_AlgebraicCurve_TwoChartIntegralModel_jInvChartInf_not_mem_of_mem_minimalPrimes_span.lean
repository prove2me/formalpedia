-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.jInvChartInf_not_mem_of_mem_minimalPrimes_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b3666c9c-38f8-5e0d-94e7-f3bd11f488a6

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_jInvChartInf_not_mem_of_mem_minimalPrimes_span

set_option autoImplicit false

open AlgebraicCurve.TwoChartIntegralModel

universe u

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : Prime ϖ) :
    ∀ Q ∈ (Ideal.span {algebraMap R ↥(chartAlgInf R F j) ϖ}).minimalPrimes, jInvChartInf R F j ∉ Q := by
  intro Q hQ hjQ
  have hj0 : j ≠ 0 := Fact.out
  haveI : Fact (j⁻¹ ≠ 0) := ⟨inv_ne_zero hj0⟩

  have hadj : IntermediateField.adjoin K₀ ({j⁻¹} : Set F) = IntermediateField.adjoin K₀ ({j} : Set F) := by
    apply le_antisymm
    · exact IntermediateField.adjoin_simple_le_iff.mpr (inv_mem (IntermediateField.mem_adjoin_simple_self K₀ j))
    · refine IntermediateField.adjoin_simple_le_iff.mpr ?_
      have := inv_mem (IntermediateField.mem_adjoin_simple_self K₀ j⁻¹)
      rwa [inv_inv] at this
  have hFD' : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j⁻¹} : Set F)) F := by rw [hadj]; exact hFD
  have hsep' : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j⁻¹} : Set F)) F := by rw [hadj]; exact hsep
  have htj' : Transcendental R j⁻¹ := fun halg => htj (by simpa using halg.inv)

  obtain ⟨V, -, hBV, hcentre, -, hgen⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
      R K₀ F j⁻¹ htj' hFD' hsep' ϖ hϖ Q hQ

  have hX := hgen Polynomial.X (fun ⟨S, hS⟩ => by
    have := congrArg (Polynomial.coeff · 1) hS
    simp only [Polynomial.coeff_X_one, Polynomial.coeff_C_mul] at this
    exact hϖ.not_unit ⟨⟨ϖ, S.coeff 1, this.symm, by rw [mul_comm]; exact this.symm⟩, rfl⟩)
  rw [Polynomial.aeval_X] at hX
  have hmem : ((jInvChartInf R F j : ↥(chartAlgInf R F j)) : F) ∈ V.nonunits := (hcentre _).mp hjQ
  rw [coe_jInvChartInf, ValuationSubring.mem_nonunits_iff] at hmem
  have hle := (V.valuation_le_one_iff _).mpr hX.2
  rw [inv_inv] at hle

  have hv0 : V.valuation j ≠ 0 := (map_ne_zero _).mpr hj0
  rw [map_inv₀] at hmem
  exact not_lt_of_ge hle ((inv_lt_one₀ (zero_lt_iff.mpr hv0)).mp hmem)

end S_AlgebraicCurve_TwoChartIntegralModel_jInvChartInf_not_mem_of_mem_minimalPrimes_span
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_jInvChartInf_not_mem_of_mem_minimalPrimes_span (solution)
