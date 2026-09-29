-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.two_le_ringKrullDim_stalk_of_isMaximal_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/895b4720-140b-5941-b85c-b59415acb652

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_chartAlgFin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_two_le_ringKrullDim_stalk_of_isMaximal_of_mem

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u

open _root_.Polynomial _root_.AlgebraicGeometry.Polynomial in

theorem solution
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (F : Type u) [Field F] [Algebra A F] (j : F) [Fact (j ≠ 0)]
    (htj : Transcendental A j)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (y : ↥(XFin A F j)) (hymax : y.asIdeal.IsMaximal)
    (hyϖ : algebraMap A ↥(chartAlgFin A F j) ϖ ∈ y.asIdeal) :
    2 ≤ ringKrullDim ↑((AlgebraicCurve.TwoChartIntegralModel A F j).presheaf.stalk ((ιFin A F j).base y)) := by
  classical
  haveI hyprime : y.asIdeal.IsPrime := y.isPrime

  obtain ⟨e, -, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_chartAlgFin A F j y ⟨y, trivial, rfl⟩
  rw [ringKrullDim_eq_of_ringEquiv e.commRingCatIsoToRingEquiv]
  show 2 ≤ ringKrullDim (Localization.AtPrime y.asIdeal)
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height y.asIdeal (Localization.AtPrime y.asIdeal)]
  suffices h : (2 : ℕ∞) ≤ y.asIdeal.height by simpa using (WithBot.coe_le_coe.mpr h : ((2 : ℕ∞) : WithBot ℕ∞) ≤ _)

  have hinj : Function.Injective (Polynomial.aeval j : A[X] →ₐ[A] F) := transcendental_iff_injective.mp htj
  let e₀ : A[X] ≃ₐ[A] ↥(Algebra.adjoin A ({j} : Set F)) :=
    (AlgEquiv.ofInjective (Polynomial.aeval j) hinj).trans
      (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval A j).symm)
  have hle : Algebra.adjoin A ({j} : Set F) ≤ chartAlgFin A F j := adjoin_le_chartAlg A F {j}
  let ψ : A[X] →ₐ[A] ↥(chartAlgFin A F j) := (Subalgebra.inclusion hle).comp e₀.toAlgHom
  have hψval : ∀ p : A[X], (ψ p : F) = Polynomial.aeval j p := by
    intro p
    show ((e₀ p : ↥(Algebra.adjoin A ({j} : Set F))) : F) = Polynomial.aeval j p
    rfl
  letI algRB : Algebra A[X] ↥(chartAlgFin A F j) := ψ.toRingHom.toAlgebra
  letI algRF : Algebra A[X] F := ((chartAlgFin A F j).val.comp ψ).toRingHom.toAlgebra
  haveI : IsScalarTower A[X] ↥(chartAlgFin A F j) F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FaithfulSMul A[X] ↥(chartAlgFin A F j) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr ((Subalgebra.inclusion_injective hle).comp e₀.injective)
  haveI : Algebra.IsIntegral A[X] ↥(chartAlgFin A F j) := by
    refine ⟨fun x => ?_⟩
    have h0 : IsIntegral ↥(Algebra.adjoin A ({j} : Set F)) (x : F) := (mem_chartAlg_iff A F).mp x.2
    have h1 : IsIntegral A[X] (x : F) := by
      refine h0.map_of_comp_eq e₀.symm.toAlgHom.toRingHom (RingHom.id F) ?_
      refine RingHom.ext fun r => ?_
      show ((ψ (e₀.symm r) : ↥(chartAlgFin A F j)) : F) = (r : F)
      rw [hψval]
      show ((e₀ (e₀.symm r) : ↥(Algebra.adjoin A ({j} : Set F))) : F) = (r : F)
      rw [AlgEquiv.apply_symm_apply]
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom A[X] ↥(chartAlgFin A F j) F) Subtype.val_injective).mp h1
  haveI : Algebra.HasGoingDown A[X] ↥(chartAlgFin A F j) := inferInstance

  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, Ideal.span_singleton_zero] at hϖ
    exact (IsDiscreteValuationRing.not_isField A) (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hϖ)
  have hϖnu : ¬ IsUnit ϖ := by
    have : ϖ ∈ IsLocalRing.maximalIdeal A := by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
    exact (IsLocalRing.mem_maximalIdeal ϖ).mp this
  have hprime : Prime ϖ := (IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal ϖ hϖ0 hϖ).prime
  let P₁ : Ideal A[X] := Ideal.span {C ϖ}
  haveI hP₁ : P₁.IsPrime :=
    (Ideal.span_singleton_prime (by simpa using hϖ0)).mpr (Polynomial.prime_C_iff.mpr hprime)
  let 𝔫 : Ideal A[X] := y.asIdeal.under A[X]
  haveI h𝔫max : 𝔫.IsMaximal := by
    haveI := hymax
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A[X]) y.asIdeal
  have hCϖ : algebraMap A[X] ↥(chartAlgFin A F j) (C ϖ) = algebraMap A ↥(chartAlgFin A F j) ϖ := by
    apply Subtype.ext
    show ((ψ (C ϖ) : ↥(chartAlgFin A F j)) : F) = ((algebraMap A ↥(chartAlgFin A F j) ϖ : ↥(chartAlgFin A F j)) : F)
    rw [hψval, Polynomial.aeval_C]
    rfl
  have hP₁le : P₁ ≤ 𝔫 := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap A[X] ↥(chartAlgFin A F j) (C ϖ) ∈ y.asIdeal
    rw [hCϖ]
    exact hyϖ
  have hXnot : (X : A[X]) ∉ P₁ := by
    intro h
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp h
    have := congrArg (fun f => Polynomial.coeff f 1) hq
    simp only [Polynomial.coeff_X_one, Polynomial.coeff_C_mul] at this
    exact hϖnu (IsUnit.of_mul_eq_one _ this.symm)
  have hP₁notmax : ¬ P₁.IsMaximal := by
    intro hmax
    have hlt : P₁ < P₁ ⊔ Ideal.span {X} := by
      refine lt_of_le_of_ne le_sup_left (fun h => hXnot ?_)
      rw [h]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self X)
    have htop : P₁ ⊔ Ideal.span {X} = ⊤ := hmax.1.2 _ hlt
    have h1 : (1 : A[X]) ∈ P₁ ⊔ Ideal.span {X} := htop ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
    obtain ⟨a', rfl⟩ := Ideal.mem_span_singleton'.mp ha
    obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton'.mp hb
    have := congrArg (fun f => Polynomial.coeff f 0) hab
    simp only [Polynomial.coeff_add, Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero, Polynomial.coeff_X_zero,
      mul_zero, add_zero, Polynomial.coeff_one_zero] at this
    exact hϖnu (IsUnit.of_mul_eq_one _ (by rwa [mul_comm] at this))
  have hP₁lt : P₁ < 𝔫 := lt_of_le_of_ne hP₁le (fun h => hP₁notmax (h ▸ h𝔫max))
  have hbotlt : (⊥ : Ideal A[X]) < P₁ := by
    refine bot_lt_iff_ne_bot.mpr ?_
    show Ideal.span {C ϖ} ≠ ⊥
    rw [Ne, Ideal.span_singleton_eq_bot, Polynomial.C_eq_zero]
    exact hϖ0

  let n : PrimeSpectrum A[X] := ⟨𝔫, inferInstance⟩
  let p₁ : PrimeSpectrum A[X] := ⟨P₁, hP₁⟩
  let p₀ : PrimeSpectrum A[X] := ⟨⊥, Ideal.isPrime_bot⟩
  let l : LTSeries (PrimeSpectrum A[X]) :=
    ((RelSeries.singleton _ n).cons p₁ (by show p₁ < n; exact hP₁lt)).cons p₀ (by show p₀ < p₁; exact hbotlt)
  have hllen : l.length = 2 := rfl
  have hllast : l.last = n := by simp [l]

  obtain ⟨L, hLlen, hLlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown (S := ↥(chartAlgFin A F j)) l y.asIdeal
    (lo := ⟨by rw [hllast]⟩)
  have hL := Order.length_le_height_last (p := L)
  rw [hLlen, hllen, hLlast] at hL
  have hy : y.asIdeal = (⟨y.asIdeal, inferInstance⟩ : PrimeSpectrum ↥(chartAlgFin A F j)).asIdeal := rfl
  rw [hy, PrimeSpectrum.height_eq_orderHeight]
  exact_mod_cast hL

end S_AlgebraicCurve_TwoChartIntegralModel_two_le_ringKrullDim_stalk_of_isMaximal_of_mem
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_two_le_ringKrullDim_stalk_of_isMaximal_of_mem (solution)
