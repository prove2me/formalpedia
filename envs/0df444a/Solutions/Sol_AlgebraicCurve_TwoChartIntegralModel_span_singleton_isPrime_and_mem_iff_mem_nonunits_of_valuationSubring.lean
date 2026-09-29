-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.span_singleton_isPrime_and_mem_iff_mem_nonunits_of_valuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/7ac8e047-2b25-5714-9c45-6d3422630719

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
import Theorems.Thm_IsIntegrallyClosed_isDiscreteValuationRing_localization_of_mem_associatedPrimes
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_span_singleton_isPrime_and_mem_iff_mem_nonunits_of_valuationSubring
set_option autoImplicit false

open scoped TensorProduct
open AlgebraicCurve

universe u

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : Prime ϖ)
    (V : ValuationSubring F)
    (hRV : ∀ r : R, algebraMap R F r ∈ V) (hϖV : algebraMap R F ϖ ∈ V.nonunits)
    (hjV : ∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V)

    (hunif : ∀ f : F, f ∈ V.nonunits → f * (algebraMap R F ϖ)⁻¹ ∈ V)

    (huniq : ∀ V' : ValuationSubring F, (∀ r : R, algebraMap R F r ∈ V') → algebraMap R F ϖ ∈ V'.nonunits →
      (∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval j P ∈ V' ∧ (Polynomial.aeval j P)⁻¹ ∈ V') → V' = V) :
    (∀ a : ↥(TwoChartIntegralModel.chartAlgFin R F j), (a : F) ∈ V) ∧
    (Ideal.span {algebraMap R ↥(TwoChartIntegralModel.chartAlgFin R F j) ϖ}).IsPrime ∧
    (∀ a : ↥(TwoChartIntegralModel.chartAlgFin R F j),
      a ∈ Ideal.span {algebraMap R ↥(TwoChartIntegralModel.chartAlgFin R F j) ϖ} ↔ (a : F) ∈ V.nonunits) := by
  classical
  haveI : NeZero ϖ := ⟨hϖ.ne_zero⟩
  have hϖF : algebraMap R F ϖ ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply R K₀ F, map_ne_zero]
    exact fun h => hϖ.ne_zero ((IsFractionRing.injective R K₀) (h.trans (map_zero _).symm))

  have hAV : ∀ x ∈ Algebra.adjoin R ({j} : Set F), x ∈ V := by
    intro x hx
    refine Algebra.adjoin_induction (hx := hx) ?_ ?_ ?_ ?_
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have h := (hjV Polynomial.X (fun hd => ?_)).1
      · simpa using h
      · have := Polynomial.natDegree_le_of_dvd hd Polynomial.X_ne_zero

        obtain ⟨q, hq⟩ := hd
        have h1 := congrArg (fun p : Polynomial R => p.coeff 1) hq
        simp only [Polynomial.coeff_X_one, Polynomial.coeff_C_mul] at h1
        exact hϖ.not_unit (isUnit_iff_exists_inv.2 ⟨_, h1.symm⟩)
    · intro r; exact hRV r
    · intro x y _ _ hx hy; exact add_mem hx hy
    · intro x y _ _ hx hy; exact mul_mem hx hy
  have hOV : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin R F j), (a : F) ∈ V := by
    intro a
    obtain ⟨p, hpm, hpx⟩ := (TwoChartIntegralModel.mem_chartAlg_iff R F).1 a.2

    let ψ : ↥(Algebra.adjoin R ({j} : Set F)) →+* ↥V :=
      (Subalgebra.val (Algebra.adjoin R ({j} : Set F))).toRingHom.codRestrict V.toSubring (fun x => hAV x x.2)
    have hint : IsIntegral ↥V (a : F) := by
      refine ⟨p.map ψ, hpm.map ψ, ?_⟩
      rw [Polynomial.eval₂_map]
      exact hpx
    obtain ⟨v, hv⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
    rw [← hv]
    exact v.2

  let ι : ↥(TwoChartIntegralModel.chartAlgFin R F j) →+* ↥V := (Subalgebra.val _).toRingHom.codRestrict V.toSubring (fun a => hOV a)
  have hι : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin R F j), ((ι a : ↥V) : F) = (a : F) := fun a => rfl
  let 𝔭 : Ideal ↥(TwoChartIntegralModel.chartAlgFin R F j) := (IsLocalRing.maximalIdeal ↥V).comap ι
  have h𝔭 : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin R F j), a ∈ 𝔭 ↔ (a : F) ∈ V.nonunits := by
    intro a
    rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff, hι]
  haveI h𝔭prime : 𝔭.IsPrime := Ideal.comap_isPrime ι _

  set ϖ' : ↥(TwoChartIntegralModel.chartAlgFin R F j) := algebraMap R ↥(TwoChartIntegralModel.chartAlgFin R F j) ϖ with hϖ'
  have hϖ'F : (ϖ' : F) = algebraMap R F ϖ := rfl
  have hϖ'0 : ϖ' ≠ 0 := fun h => hϖF (by rw [← hϖ'F, h]; rfl)
  set I : Ideal ↥(TwoChartIntegralModel.chartAlgFin R F j) := Ideal.span {ϖ'} with hI

  have hI𝔭 : I ≤ 𝔭 := by
    rw [hI, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, h𝔭, hϖ'F]
    exact hϖV

  haveI : IsIntegrallyClosed ↥(TwoChartIntegralModel.chartAlgFin R F j) := TwoChartIntegralModel.isIntegrallyClosed_chartAlg R F {j}
  haveI : IsNoetherianRing ↥(TwoChartIntegralModel.chartAlgFin R F j) := by
    letI := (TwoChartIntegralModel.polynomialToChartFin R F j).toRingHom.toAlgebra
    haveI : Module.Finite (Polynomial R) ↥(TwoChartIntegralModel.chartAlgFin R F j) :=
      (TwoChartIntegralModel.finite_polynomial_chartAlgFin_and_chartAlgInf R K₀ F j htj hFD hsep).1
    haveI : Algebra.FiniteType (Polynomial R) ↥(TwoChartIntegralModel.chartAlgFin R F j) := Module.Finite.finiteType ↥(TwoChartIntegralModel.chartAlgFin R F j)
    exact Algebra.FiniteType.isNoetherianRing (Polynomial R) _

  have h𝔭I : 𝔭 ≤ I := by
    intro a ha
    by_contra haI

    have hā : (Ideal.Quotient.mk I a) ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨P, hPass, hcolon⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing ↥(TwoChartIntegralModel.chartAlgFin R F j) (Ideal.Quotient.mk I a) hā
    haveI hPprime : P.IsPrime := hPass.isPrime
    have hcol : ∀ s : ↥(TwoChartIntegralModel.chartAlgFin R F j), s * a ∈ I → s ∈ P := by
      intro s hs
      apply hcolon
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
      change Ideal.Quotient.mk I (s * a) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact hs
    have hIP : I ≤ P := by
      rw [hI, Ideal.span_le, Set.singleton_subset_iff]
      exact hcol ϖ' (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

    haveI hdvr : IsDiscreteValuationRing (Localization.AtPrime P) :=
      IsIntegrallyClosed.isDiscreteValuationRing_localization_of_mem_associatedPrimes hϖ'0 P hPass
    have hinjL : Function.Injective (algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (Localization.AtPrime P)) :=
      IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors

    have hPmin : P ∈ I.minimalPrimes := by
      refine ⟨⟨hPprime, hIP⟩, ?_⟩
      rintro Q ⟨hQ, hIQ⟩ hQP
      haveI := hQ

      have hdisj : Disjoint (P.primeCompl : Set ↥(TwoChartIntegralModel.chartAlgFin R F j)) Q := by
        rw [Set.disjoint_left]; intro s hs hsQ; exact hs (hQP hsQ)
      have hQ' : (Q.map (algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (Localization.AtPrime P))).IsPrime :=
        IsLocalization.isPrime_of_isPrime_disjoint P.primeCompl _ Q hQ hdisj
      have hQ'0 : Q.map (algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (Localization.AtPrime P)) ≠ ⊥ := by
        intro h0
        have : algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (Localization.AtPrime P) ϖ' ∈ Q.map (algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (Localization.AtPrime P)) :=
          Ideal.mem_map_of_mem _ (hIQ (Ideal.mem_span_singleton_self _))
        rw [h0, Ideal.mem_bot, map_eq_zero_iff _ hinjL] at this
        exact hϖ'0 this
      have hQmax : (Q.map (algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (Localization.AtPrime P))).IsMaximal := hQ'.isMaximal hQ'0
      have hQ'eq : Q.map (algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (Localization.AtPrime P)) = IsLocalRing.maximalIdeal _ :=
        IsLocalRing.eq_maximalIdeal hQmax
      intro x hxP
      have hx' : algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (Localization.AtPrime P) x ∈ Q.map (algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (Localization.AtPrime P)) := by
        rw [hQ'eq, ← Localization.AtPrime.map_eq_maximalIdeal]
        exact Ideal.mem_map_of_mem _ hxP
      have := IsLocalization.under_map_of_isPrime_disjoint P.primeCompl (Localization.AtPrime P) hQ hdisj
      rw [← this]
      exact hx'

    obtain ⟨V', -, hOV', hPV', hϖV', hjV'⟩ :=
      TwoChartIntegralModel.exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin R K₀ F j htj hFD hsep ϖ hϖ P hPmin
    have hV' : V' = V :=
      huniq V' (fun r => hOV' (algebraMap R ↥(TwoChartIntegralModel.chartAlgFin R F j) r)) hϖV' hjV'
    obtain rfl : V = V' := hV'.symm

    rcases ValuationRing.dvd_total (algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (Localization.AtPrime P) ϖ') (algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (Localization.AtPrime P) a)
      with ⟨d, hd⟩ | ⟨d, hd⟩
    ·
      obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl d
      have h1 : algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (Localization.AtPrime P) (a * s) = algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (Localization.AtPrime P) (ϖ' * b) := by
        rw [map_mul, map_mul, hd, mul_assoc, IsLocalization.mk'_spec]
      have h2 : (s : ↥(TwoChartIntegralModel.chartAlgFin R F j)) * a = ϖ' * b := by rw [mul_comm]; exact hinjL h1
      exact s.2 (hcol s (h2 ▸ Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
    ·
      obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl d
      have h1 : algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (Localization.AtPrime P) (ϖ' * s) = algebraMap ↥(TwoChartIntegralModel.chartAlgFin R F j) (Localization.AtPrime P) (a * b) := by
        rw [map_mul, map_mul, hd, mul_assoc, IsLocalization.mk'_spec]
      have h2 : ϖ' * s = a * b := hinjL h1
      by_cases hbP : b ∈ P
      · have ha𝔭' : (a : F) ∈ V.nonunits := (h𝔭 a).1 ha
        have haϖ : (a : F) * (algebraMap R F ϖ)⁻¹ ∈ V := hunif _ ha𝔭'
        have hb0 : (b : F) ≠ 0 := by
          intro hb
          have : b = 0 := Subtype.ext hb
          rw [this, mul_zero, mul_eq_zero] at h2
          rcases h2 with h | h
          · exact hϖ'0 h
          · exact s.2 (h ▸ P.zero_mem)

        have hquot : (a : F) * (algebraMap R F ϖ)⁻¹ = (s : ↥(TwoChartIntegralModel.chartAlgFin R F j)) * ((b : ↥(TwoChartIntegralModel.chartAlgFin R F j)) : F)⁻¹ := by
          rw [mul_inv_eq_iff_eq_mul₀ hϖF, mul_assoc, mul_comm ((b : ↥(TwoChartIntegralModel.chartAlgFin R F j)) : F)⁻¹, ← mul_assoc, eq_mul_inv_iff_mul_eq₀ hb0]
          have := congrArg (fun x : ↥(TwoChartIntegralModel.chartAlgFin R F j) => (x : F)) h2
          simp only [Subalgebra.coe_mul] at this
          rw [hϖ'F] at this
          rw [← this, mul_comm]
        rw [hquot] at haϖ

        have hbs : ((b : ↥(TwoChartIntegralModel.chartAlgFin R F j)) : F) * ((s : ↥(TwoChartIntegralModel.chartAlgFin R F j)) : F)⁻¹ ∈ V.nonunits := by
          have hbV : ((b : ↥(TwoChartIntegralModel.chartAlgFin R F j)) : F) ∈ V.nonunits := (hPV' b).1 hbP
          have hsV : ((s : ↥(TwoChartIntegralModel.chartAlgFin R F j)) : F)⁻¹ ∈ V := by
            have hs := (hPV' (s : ↥(TwoChartIntegralModel.chartAlgFin R F j))).not.1 s.2
            rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at hs
            exact hs.2
          have hblt := hbV
          rw [ValuationSubring.mem_nonunits_iff] at hblt
          have hsle := hsV
          rw [← ValuationSubring.valuation_le_one_iff] at hsle
          rw [ValuationSubring.mem_nonunits_iff, map_mul]
          exact lt_of_le_of_lt (by simpa only [mul_one] using mul_le_mul_right hsle (V.valuation ((b : ↥(TwoChartIntegralModel.chartAlgFin R F j)) : F))) hblt
        have hs0 : ((s : ↥(TwoChartIntegralModel.chartAlgFin R F j)) : F) ≠ 0 := fun h => s.2 ((Subtype.ext h : (s : ↥(TwoChartIntegralModel.chartAlgFin R F j)) = 0) ▸ P.zero_mem)
        rcases (V.mem_nonunits_iff_or).1 hbs with h0 | hnot
        · rcases mul_eq_zero.1 h0 with h | h
          · exact hb0 h
          · exact (inv_ne_zero hs0) h
        · apply hnot
          rw [mul_inv_rev, inv_inv]
          exact haϖ
      · exact hbP (hcol b (by rw [mul_comm, ← h2]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

  have hIeq : I = 𝔭 := le_antisymm hI𝔭 h𝔭I
  refine ⟨hOV, hIeq ▸ h𝔭prime, fun a => ?_⟩
  rw [hIeq]
  exact h𝔭 a

#print axioms solution

end S_AlgebraicCurve_TwoChartIntegralModel_span_singleton_isPrime_and_mem_iff_mem_nonunits_of_valuationSubring
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_span_singleton_isPrime_and_mem_iff_mem_nonunits_of_valuationSubring (solution)
