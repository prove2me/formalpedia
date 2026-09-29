-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.map_span_eq_maximalIdeal_localization_atPrime_of_forall_valuationSubring_mul_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/cce1ab47-eee3-5a04-8966-f8a8d6ff047d

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
import Theorems.Thm_IsIntegrallyClosed_exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_map_span_eq_maximalIdeal_localization_atPrime_of_forall_valuationSubring_mul_inv_mem

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

universe u

open AlgebraicCurve.TwoChartIntegralModel

namespace MultOneGen

theorem eq_of_le_of_height_eq_one
    {C K : Type*} [CommRing C] [IsDomain C] [Field K] [Algebra C K] [IsFractionRing C K]
    (P : Ideal C) [P.IsPrime] (hP : P.height = 1)
    (V₁ : ValuationSubring K)
    (hmem : ∀ x : K, x ∈ V₁ ↔ ∃ c s : C, s ∉ P ∧ x * algebraMap C K s = algebraMap C K c)
    (hCV : ∀ c : C, algebraMap C K c ∈ V₁)
    (hcen : ∀ c : C, algebraMap C K c ∈ V₁.nonunits ↔ c ∈ P)
    (V : ValuationSubring K) (hle : V₁ ≤ V) (hne : V ≠ ⊤) : V = V₁ := by
  classical
  have hinj : Function.Injective (algebraMap C K) := IsFractionRing.injective C K

  let φ : C →+* ↥V₁ := (algebraMap C K).codRestrict V₁.toSubring hCV
  have hφ : ∀ c, ((φ c : ↥V₁) : K) = algebraMap C K c := fun _ => rfl

  have hmax : ∀ c : C, φ c ∈ IsLocalRing.maximalIdeal ↥V₁ ↔ c ∈ P := by
    intro c
    rw [← hcen, ValuationSubring.mem_nonunits_iff, ← hφ c, ValuationSubring.valuation_lt_one_iff]

  set Q : Ideal ↥V₁ := V₁.idealOfLE V hle with hQ
  have hQV : V₁.ofPrime Q = V := ValuationSubring.ofPrime_idealOfLE V₁ V hle
  have hQle : Q ≤ IsLocalRing.maximalIdeal ↥V₁ := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)

  let q : Ideal C := Q.comap φ
  haveI hqprime : q.IsPrime := Ideal.comap_isPrime φ Q
  have hqP : q ≤ P := fun c hc => (hmax c).mp (hQle hc)
  by_cases hqeq : q = P
  ·
    have hQmax : Q = IsLocalRing.maximalIdeal ↥V₁ := by
      refine le_antisymm hQle fun y hy => ?_
      obtain ⟨c, s, hs, hcs⟩ := (hmem y).mp y.2
      have hs0 : algebraMap C K s ≠ 0 := fun h0 => hs (by rw [(hinj (h0.trans (map_zero _).symm) : s = 0)]; exact P.zero_mem)

      have hc : φ c ∈ IsLocalRing.maximalIdeal ↥V₁ := by
        have : φ c = y * φ s := Subtype.ext (by rw [Subring.coe_mul]; exact hcs.symm)
        rw [this]; exact Ideal.mul_mem_right _ _ hy
      have hcq : c ∈ q := by rw [hqeq]; exact (hmax c).mp hc
      have hsu : IsUnit (φ s) := by
        by_contra hns
        exact hs ((hmax s).mp ((IsLocalRing.mem_maximalIdeal _).mpr hns))
      obtain ⟨u, hu⟩ := hsu
      have hyu : y * u = φ c := by
        apply Subtype.ext
        show (y : K) * ((u : ↥V₁) : K) = ((φ c : ↥V₁) : K)
        rw [hu, hφ, hφ, hcs]
      have hy' : y = φ c * ↑u⁻¹ := by rw [← hyu, mul_assoc, Units.mul_inv, mul_one]
      rw [hy']
      exact Ideal.mul_mem_right _ _ hcq
    rw [← hQV]

    have key : ∀ (Q' : Ideal ↥V₁) [Q'.IsPrime], Q' = IsLocalRing.maximalIdeal ↥V₁ → V₁.ofPrime Q' = V₁ := by
      intro Q' _ h; subst h; exact ValuationSubring.ofPrime_top V₁
    exact key Q hQmax
  ·
    exfalso
    have hqlt : q < P := lt_of_le_of_ne hqP hqeq
    have hqbot : q = ⊥ := by
      by_contra hq0
      have hbotlt : (⊥ : Ideal C) < q := lt_of_le_of_ne bot_le (Ne.symm hq0)
      have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hbotlt
      have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hqlt
      rw [hP] at h2
      rw [Ideal.height_bot, zero_add] at h1
      have h3 : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left h1 1).trans (by simpa [add_comm] using h2)
      have h4 : ¬ ((1 : ℕ∞) + 1 ≤ 1) := by decide
      exact h4 h3
    have hQbot : Q = ⊥ := by
      refine le_antisymm (fun x hx => ?_) bot_le
      obtain ⟨c, s, hs, hcs⟩ := (hmem x).mp x.2
      have hs0 : algebraMap C K s ≠ 0 := fun h0 => hs (by rw [(hinj (h0.trans (map_zero _).symm) : s = 0)]; exact P.zero_mem)
      have hc : φ c ∈ Q := by
        have : φ c = x * φ s := Subtype.ext (by rw [Subring.coe_mul]; exact hcs.symm)
        rw [this]; exact Ideal.mul_mem_right _ _ hx
      have hc0 : c = 0 := by
        have : c ∈ q := hc
        rw [hqbot] at this
        exact this
      have hx0 : (x : K) = 0 := by
        have := hcs
        rw [hc0, map_zero, mul_eq_zero] at this
        exact this.resolve_right hs0
      exact (Submodule.mem_bot _).mpr (Subtype.ext hx0)
    apply hne
    rw [← hQV]
    have key : ∀ (Q' : Ideal ↥V₁) [Q'.IsPrime], Q' = ⊥ → V₁.ofPrime Q' = ⊤ := by
      intro Q' _ h; subst h; exact ValuationSubring.ofPrime_bot V₁
    exact key Q hQbot

end MultOneGen

open MultOneGen in
theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : Prime ϖ)
    (hmult : ∀ V : ValuationSubring F, (∀ r : R, algebraMap R F r ∈ V) → algebraMap R F ϖ ∈ V.nonunits →
      (∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) →
      ∀ x : F, x ∈ V.nonunits → x * (algebraMap R F ϖ)⁻¹ ∈ V)
    (𝔭 : Ideal ↥(chartAlgFin R F j)) [𝔭.IsPrime]
    (h𝔭 : 𝔭 ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ}).minimalPrimes) :
    Ideal.map (algebraMap ↥(chartAlgFin R F j) (Localization.AtPrime 𝔭))
        (Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ}) =
      IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) := by
  classical

  haveI : Algebra.FiniteType R ↥(chartAlgFin R F j) := (finiteType_chartAlgFin_and_chartAlgInf R K₀ F j htj hFD hsep).1
  haveI : IsNoetherianRing ↥(chartAlgFin R F j) := Algebra.FiniteType.isNoetherianRing R _
  haveI : IsIntegrallyClosed ↥(chartAlgFin R F j) := isIntegrallyClosed_chartAlg R F _
  haveI := hFD
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F := Algebra.IsAlgebraic.of_finite _ _
  haveI : IsFractionRing ↥(chartAlgFin R F j) F := isFractionRing_chartAlg R K₀ F {j}

  have hϖ0 : algebraMap R F ϖ ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply R K₀ F]
    exact (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective R K₀)).mpr hϖ.ne_zero)
  have hϖA : (algebraMap R ↥(chartAlgFin R F j) ϖ : F) = algebraMap R F ϖ := rfl
  have hϖ𝔭 : algebraMap R ↥(chartAlgFin R F j) ϖ ∈ 𝔭 := h𝔭.1.2 (Ideal.subset_span rfl)
  have h𝔭ne : 𝔭 ≠ ⊥ := fun h => by
    rw [h, Submodule.mem_bot] at hϖ𝔭
    exact hϖ0 (by rw [← hϖA, hϖ𝔭]; simp)
  have hP1 : 𝔭.height = 1 := by
    apply le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ 𝔭 h𝔭)
    have h := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne bot_le (Ne.symm h𝔭ne) : (⊥ : Ideal ↥(chartAlgFin R F j)) < 𝔭)
    rw [Ideal.height_bot] at h
    simpa using h

  obtain ⟨V₁, hmem₁, hAV₁, hcen₁, htrans, -⟩ :=
    IsIntegrallyClosed.exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one (K := F) 𝔭 hP1

  obtain ⟨V, -, hAV, hcen, hϖV, hbr⟩ :=
    exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin R K₀ F j htj hFD hsep ϖ hϖ 𝔭 h𝔭

  have hle : V₁ ≤ V := by
    intro x hx
    obtain ⟨c, s, hs, hcs⟩ := (hmem₁ x).mp hx
    have hs0 : (s : F) ≠ 0 := fun h0 => hs (by rw [show s = 0 from Subtype.ext h0]; exact 𝔭.zero_mem)
    have hsu : (s : F) ∉ V.nonunits := fun h => hs ((hcen s).mpr h)
    have hvs : V.valuation (s : F) = 1 :=
      le_antisymm ((V.valuation_le_one_iff _).mpr (hAV s)) (not_lt.mp (mt (V.mem_nonunits_iff).mpr hsu))
    have hsinv : (s : F)⁻¹ ∈ V := by
      apply (V.valuation_le_one_iff _).mp
      rw [map_inv₀, hvs, inv_one]
    have : x = (c : F) * (s : F)⁻¹ := (eq_mul_inv_iff_mul_eq₀ hs0).mpr hcs
    rw [this]
    exact mul_mem (hAV c) hsinv
  have hne : V ≠ ⊤ := by
    intro h
    have hlt := (V.mem_nonunits_iff).mp hϖV
    have hinvmem : (algebraMap R F ϖ)⁻¹ ∈ V := h ▸ ValuationSubring.mem_top _
    have hle1 := (V.valuation_le_one_iff _).mpr hinvmem
    rw [map_inv₀] at hle1
    have hv0 : V.valuation (algebraMap R F ϖ) ≠ 0 := (map_ne_zero _).mpr hϖ0
    exact absurd hlt (not_lt.mpr ((inv_le_one₀ (zero_lt_iff.mpr hv0)).mp hle1))
  have hVeq : V = V₁ := eq_of_le_of_height_eq_one 𝔭 hP1 V₁ hmem₁ hAV₁ hcen₁ V hle hne

  have hRV : ∀ r : R, algebraMap R F r ∈ V := fun r => hAV (algebraMap R ↥(chartAlgFin R F j) r)
  have hgen : ∀ f : F, f ∈ V₁.nonunits → ∃ g : F, g ∈ V₁ ∧ f = algebraMap ↥(chartAlgFin R F j) F (algebraMap R _ ϖ) * g := by
    intro f hf
    rw [← hVeq] at hf ⊢
    exact ⟨f * (algebraMap R F ϖ)⁻¹, hmult V hRV hϖV hbr f hf, by rw [show algebraMap ↥(chartAlgFin R F j) F (algebraMap R _ ϖ) = algebraMap R F ϖ from rfl, mul_comm, inv_mul_cancel_right₀ hϖ0]⟩
  have hmax := (htrans (algebraMap R ↥(chartAlgFin R F j) ϖ) hϖ𝔭).mp hgen
  rw [Ideal.map_span, Set.image_singleton, hmax]

end S_AlgebraicCurve_TwoChartIntegralModel_map_span_eq_maximalIdeal_localization_atPrime_of_forall_valuationSubring_mul_inv_mem
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_map_span_eq_maximalIdeal_localization_atPrime_of_forall_valuationSubring_mul_inv_mem (solution)
