-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.mem_minimalPrimes_span_iff_of_valuationSubring_pair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/cf8415f4-1ecd-5ad5-94c6-da3d37ace7d7

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_minimalPrimes_span_iff_of_valuationSubring_pair

set_option autoImplicit false

universe u

open AlgebraicCurve.TwoChartIntegralModel

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (W₀ W₁ : ValuationSubring F)

    (h1 : ∀ i : Fin 2, (∀ a : R, algebraMap R F a ∈ (![W₀, W₁] i)) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R F a ∈ (![W₀, W₁] i).nonunits)

    (h2 : ∀ i : Fin 2, ∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
      Polynomial.aeval j P ∈ (![W₀, W₁] i) ∧ (Polynomial.aeval j P)⁻¹ ∈ (![W₀, W₁] i))

    (h3 : W₀ ≠ W₁)

    (h5 : ∀ V : ValuationSubring F,
      (∀ a : R, algebraMap R F a ∈ V) → (∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R F a ∈ V.nonunits) →
      (∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
        Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) →
      V = W₀ ∨ V = W₁) :

    (∀ 𝔭 ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ}).minimalPrimes,
      (∀ b : ↥(chartAlgFin R F j), b ∈ 𝔭 ↔ (b : F) ∈ W₀.nonunits) ∨
      (∀ b : ↥(chartAlgFin R F j), b ∈ 𝔭 ↔ (b : F) ∈ W₁.nonunits)) ∧

    (∀ i : Fin 2, ∃ 𝔭 ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ}).minimalPrimes,
      ∀ b : ↥(chartAlgFin R F j), b ∈ 𝔭 ↔ (b : F) ∈ (![W₀, W₁] i).nonunits) ∧

    (∃ b : ↥(chartAlgFin R F j), (b : F) ∈ W₀.nonunits ∧ (b : F) ∉ W₁.nonunits) ∧
    (∃ b : ↥(chartAlgFin R F j), (b : F) ∈ W₁.nonunits ∧ (b : F) ∉ W₀.nonunits) := by
  classical
  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  have hϖp : Prime ϖ := hirr.prime
  have hinjF : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R K₀ F]
    exact (algebraMap K₀ F).injective.comp (IsFractionRing.injective R K₀)
  have hϖA : algebraMap R ↥(chartAlgFin R F j) ϖ ≠ 0 := by
    intro h0
    apply hirr.ne_zero
    apply hinjF
    rw [map_zero]
    exact congrArg Subtype.val h0
  have hcoeA : ∀ a : R, ((algebraMap R ↥(chartAlgFin R F j) a : ↥(chartAlgFin R F j)) : F) = algebraMap R F a :=
    fun a => rfl

  have hred : ∀ P : Polynomial R, P.map (IsLocalRing.residue R) = 0 ↔ Polynomial.C ϖ ∣ P := by
    intro P
    rw [Polynomial.C_dvd_iff_dvd_coeff, Polynomial.ext_iff]
    refine forall_congr' fun i => ?_
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, IsLocalRing.residue_eq_zero_iff, hϖ, Ideal.mem_span_singleton]

  have hBC := fun (V : ValuationSubring F) hVA hVm hVj =>
    AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
      R K₀ F j htj hFD hsep V hVA hVm hVj

  have part_i : ∀ 𝔭 ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ}).minimalPrimes,
      (∀ b : ↥(chartAlgFin R F j), b ∈ 𝔭 ↔ (b : F) ∈ W₀.nonunits) ∨
      (∀ b : ↥(chartAlgFin R F j), b ∈ 𝔭 ↔ (b : F) ∈ W₁.nonunits) := by
    intro 𝔭 h𝔭
    obtain ⟨V, -, hAV, hcentre, hϖV, hVj⟩ :=
      AlgebraicCurve.TwoChartIntegralModel.exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
        R K₀ F j htj hFD hsep ϖ hϖp 𝔭 h𝔭
    have hVA : ∀ a : R, algebraMap R F a ∈ V := fun a => hcoeA a ▸ hAV _
    have hVm : ∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R F a ∈ V.nonunits := by
      intro a ha
      rw [hϖ, Ideal.mem_span_singleton] at ha
      obtain ⟨b, rfl⟩ := ha
      rw [map_mul]
      have hcoe : algebraMap R F ϖ * algebraMap R F b = (((⟨_, hVA ϖ⟩ : V) * ⟨_, hVA b⟩ : V) : F) := rfl
      rw [hcoe, ValuationSubring.coe_mem_nonunits_iff]
      exact Ideal.mul_mem_right _ _ (ValuationSubring.coe_mem_nonunits_iff.mp hϖV)
    have hVj' : ∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
        Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V :=
      fun P hP => hVj P ((hred P).not.mp hP)
    rcases h5 V hVA hVm hVj' with rfl | rfl
    · exact Or.inl hcentre
    · exact Or.inr hcentre

  have part_ii : ∀ i : Fin 2, ∃ 𝔭 ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ}).minimalPrimes,
      ∀ b : ↥(chartAlgFin R F j), b ∈ 𝔭 ↔ (b : F) ∈ (![W₀, W₁] i).nonunits := by
    intro i
    obtain ⟨-, ⟨𝔓, h𝔓p, h𝔓h, h𝔓c, h𝔓m, -⟩, -⟩ := hBC (![W₀, W₁] i) (h1 i).1 (h1 i).2 (h2 i)
    haveI := h𝔓p
    refine ⟨𝔓, ?_, h𝔓c⟩
    have hle : Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ} ≤ 𝔓 := by
      rw [Ideal.span_singleton_le_iff_mem]
      exact h𝔓m ϖ (by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ)
    haveI : 𝔓.FiniteHeight := ⟨Or.inr (by rw [h𝔓h]; exact ENat.one_ne_top)⟩
    refine Ideal.mem_minimalPrimes_of_height_eq hle ?_
    rw [h𝔓h]
    exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖA)

  obtain ⟨-, -, hd₀⟩ := hBC W₀ (h1 0).1 (h1 0).2 (h2 0)
  obtain ⟨-, -, hd₁⟩ := hBC W₁ (h1 1).1 (h1 1).2 (h2 1)
  exact ⟨part_i, part_ii, hd₁ W₀ (h1 0).1 (h1 0).2 (h2 0) h3.symm, hd₀ W₁ (h1 1).1 (h1 1).2 (h2 1) h3⟩

end S_AlgebraicCurve_TwoChartIntegralModel_mem_minimalPrimes_span_iff_of_valuationSubring_pair
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_minimalPrimes_span_iff_of_valuationSubring_pair (solution)
