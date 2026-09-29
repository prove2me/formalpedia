-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.finite_polynomial_chartAlgFin_and_chartAlgInf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/0581d523-9088-5c09-aa98-259930931347

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf

set_option autoImplicit false
open AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

noncomputable section

universe u

set_option maxHeartbeats 32000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F) :
    (letI := (polynomialToChartFin R F j).toRingHom.toAlgebra
     Module.Finite (Polynomial R) ↥(chartAlgFin R F j)) ∧
    (letI := (polynomialToChartInf R F j).toRingHom.toAlgebra
     Module.Finite (Polynomial R) ↥(chartAlgInf R F j)) := by
  classical
  have hZlFinj : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R K₀ F]
    exact (algebraMap K₀ F).injective.comp (IsFractionRing.injective R K₀)

  set K := IntermediateField.adjoin K₀ ({j} : Set F) with hK
  haveI : FiniteDimensional ↥K F := hFD
  have htji : Transcendental R (j⁻¹ : F) := fun halg => by
    have := halg.inv; rw [inv_inv] at this; exact htj this

  have hKinv : IntermediateField.adjoin K₀ ({j⁻¹} : Set F) = K := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      exact Set.singleton_subset_iff.mpr
        (K.inv_mem (IntermediateField.mem_adjoin_simple_self K₀ j))
    · rw [hK, IntermediateField.adjoin_le_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      have h1 := (IntermediateField.adjoin K₀ {j⁻¹}).inv_mem
        (IntermediateField.mem_adjoin_simple_self K₀ j⁻¹)
      rwa [inv_inv] at h1

  suffices h : ∀ (s : F) (hs : Transcendental R s)
      (hFD_s : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({s} : Set F)) F)
      (hsep_s : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({s} : Set F)) F)
      (sC : ↥(chartAlg R F {s})) (hsC : (sC : F) = s),
      letI := (Polynomial.aeval (R := R) sC).toRingHom.toAlgebra
      Module.Finite (Polynomial R) ↥(chartAlg R F {s}) by
    exact ⟨h j htj hFD hsep (jChartFin R F j) rfl, h j⁻¹ htji (hKinv ▸ hFD) (hKinv ▸ hsep) (jInvChartInf R F j) rfl⟩
  intro s hs hFD_s hsep_s sC hsC
  set A := Algebra.adjoin R ({s} : Set F) with hA
  set K' := IntermediateField.adjoin K₀ ({s} : Set F) with hK'def
  haveI hFD' : FiniteDimensional ↥K' F := hFD_s
  haveI hK'sep : Algebra.IsSeparable ↥K' F := hsep_s
  have hsℚ : Transcendental K₀ s :=
    fun h => hs ((IsFractionRing.isAlgebraic_iff R K₀ F).mpr h)

  letI algAC : Algebra ↥A ↥(chartAlg R F {s}) :=
    (Subalgebra.inclusion (adjoin_le_chartAlg R F {s})).toRingHom.toAlgebra
  haveI stAC : IsScalarTower R ↥A ↥(chartAlg R F {s}) :=
    IsScalarTower.of_algebraMap_eq fun a => Subtype.ext rfl
  have hAFT : Algebra.FiniteType R ↥A :=
    (Subalgebra.fg_iff_finiteType A).mp ⟨{s}, by rw [Finset.coe_singleton]⟩

  haveI stACF : IsScalarTower ↥A ↥(chartAlg R F {s}) F :=
    IsScalarTower.of_algebraMap_eq fun a => rfl
  haveI hIIC : IsIntegralClosure ↥(chartAlg R F {s}) ↥A F := {
    algebraMap_injective := Subtype.val_injective
    isIntegral_iff := fun {x} => ⟨fun hx => ⟨⟨x, (mem_chartAlg_iff R F).mpr hx⟩, rfl⟩,
      fun ⟨y, hy⟩ => hy ▸ (mem_chartAlg_iff R F).mp y.2⟩ }

  have haevInj : Function.Injective (Polynomial.aeval (R := R) s) :=
    transcendental_iff_injective.mp hs
  have hmemA : ∀ p : Polynomial R, (Polynomial.aeval (R := R) s) p ∈ A := fun p => by
    rw [hA, Algebra.adjoin_singleton_eq_range_aeval]; exact AlgHom.mem_range_self _ p
  let eA : Polynomial R ≃ₐ[R] ↥A :=
    AlgEquiv.ofBijective ((Polynomial.aeval (R := R) s).codRestrict A hmemA)
      ⟨fun p q h => haevInj (Subtype.ext_iff.mp h),
       fun a => by
         have ha : (a : F) ∈ (Polynomial.aeval (R := R) s).range := by
           rw [← Algebra.adjoin_singleton_eq_range_aeval, ← hA]; exact a.2
         obtain ⟨p, hp⟩ := ha; exact ⟨p, Subtype.ext hp⟩⟩
  haveI hANoeth : IsNoetherianRing ↥A :=
    isNoetherianRing_of_ringEquiv (Polynomial R) eA.toRingEquiv
  haveI hADom : IsDomain ↥A := inferInstance
  haveI hAUfm : UniqueFactorizationMonoid ↥A :=
    MulEquiv.uniqueFactorizationMonoid eA.toRingEquiv.toMulEquiv inferInstance
  haveI hAIIC : IsIntegrallyClosed ↥A := UniqueFactorizationMonoid.instIsIntegrallyClosed

  have hAK' : ∀ a : ↥A, (a : F) ∈ K' := fun a =>
    Algebra.adjoin_induction
      (fun y hy => Set.mem_singleton_iff.mp hy ▸ IntermediateField.mem_adjoin_simple_self K₀ s)
      (fun r => by
        rw [IsScalarTower.algebraMap_apply R K₀ F]
        exact K'.algebraMap_mem (algebraMap R K₀ r))
      (fun _ _ _ _ ha hb => add_mem ha hb)
      (fun _ _ _ _ ha hb => mul_mem ha hb)
      a.2
  let ιAK : ↥A →+* ↥K' := (Subalgebra.val A).toRingHom.codRestrict K'.toSubring (fun a => hAK' a)
  letI algAK : Algebra ↥A ↥K' := ιAK.toAlgebra
  haveI stAKF : IsScalarTower ↥A ↥K' F := IsScalarTower.of_algebraMap_eq fun a => rfl
  haveI stZlAK : IsScalarTower R ↥A ↥K' :=
    IsScalarTower.of_algebraMap_eq fun a => Subtype.ext rfl

  have hιAKinj : Function.Injective (algebraMap ↥A ↥K') := fun a b h =>
    Subtype.ext (congrArg (Subtype.val : ↥K' → F) h)
  have haevNorm : ∀ p : Polynomial K₀, ∃ b ∈ nonZeroDivisors R,
      (Polynomial.aeval (R := R) s)
        (IsLocalization.integerNormalization (nonZeroDivisors R) p) =
      (algebraMap R F b) * (Polynomial.aeval (R := K₀) s) p := by
    intro p
    obtain ⟨b, hb, hbp⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) p
    refine ⟨b, hb, ?_⟩
    rw [← Polynomial.aeval_map_algebraMap K₀ s
        (IsLocalization.integerNormalization (nonZeroDivisors R) p), hbp,
      Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply R K₀ (Polynomial K₀) b,
      AlgHom.commutes, ← IsScalarTower.algebraMap_apply R K₀ F]
  haveI hAFR : IsFractionRing ↥A ↥K' := by
    refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
    · rintro ⟨a, ha⟩
      exact isUnit_iff_ne_zero.mpr fun h0 => (mem_nonZeroDivisors_iff_ne_zero.mp ha)
        (hιAKinj (h0.trans (map_zero _).symm))
    · intro k
      obtain ⟨r, t, hrt⟩ :=
        (IntermediateField.mem_adjoin_simple_iff K₀ (α := s) (k : F)).mp (hK'def ▸ k.2)
      obtain ⟨br, hbr, hbrr⟩ := haevNorm r
      obtain ⟨bt, hbt, hbtt⟩ := haevNorm t
      set r' := IsLocalization.integerNormalization (nonZeroDivisors R) r
      set t' := IsLocalization.integerNormalization (nonZeroDivisors R) t
      by_cases ht0 : (Polynomial.aeval (R := K₀) s) t = 0
      · refine ⟨⟨0, 1⟩, ?_⟩
        have hk0 : k = 0 := Subtype.ext (by
          show (k : F) = 0; rw [hrt, ht0, div_zero])
        simp [hk0]
      · set ar : ↥A := ⟨(Polynomial.aeval (R := R) s) r', hmemA r'⟩
        set at' : ↥A := ⟨(Polynomial.aeval (R := R) s) t', hmemA t'⟩
        set abr : ↥A := algebraMap R ↥A br with habr
        set abt : ↥A := algebraMap R ↥A bt with habt
        have hat'nz : at' ≠ 0 := fun h0 => by
          have h0F : (Polynomial.aeval (R := R) s) t' = 0 :=
            congrArg (Subtype.val : ↥A → F) h0
          rw [hbtt] at h0F
          rcases mul_eq_zero.mp h0F with hc | hc
          · exact (mem_nonZeroDivisors_iff_ne_zero.mp hbt) (hZlFinj (by rw [hc, map_zero]))
          · exact ht0 hc
        have hZlAinj : Function.Injective (algebraMap R ↥A) := fun a b h =>
          hZlFinj (congrArg (Subtype.val : ↥A → F) h)
        have habrnz : abr ≠ 0 := fun h0 =>
          (mem_nonZeroDivisors_iff_ne_zero.mp hbr) (hZlAinj (by rw [← habr, h0, map_zero]))
        refine ⟨⟨abt * ar, ⟨abr * at',
          mem_nonZeroDivisors_iff_ne_zero.mpr (mul_ne_zero habrnz hat'nz)⟩⟩, ?_⟩
        apply Subtype.ext
        show (k : F) * ((Subtype.val : ↥A → F) (abr * at')) =
             (Subtype.val : ↥A → F) (abt * ar)
        have hc1 : ((abr : ↥A) : F) = algebraMap R F br :=
          (IsScalarTower.algebraMap_apply R ↥A F br).symm
        have hc2 : ((abt : ↥A) : F) = algebraMap R F bt :=
          (IsScalarTower.algebraMap_apply R ↥A F bt).symm
        simp only [Subalgebra.coe_mul, hc1, hc2,
          show ((ar : ↥A) : F) = (Polynomial.aeval (R := R) s) r' from rfl,
          show ((at' : ↥A) : F) = (Polynomial.aeval (R := R) s) t' from rfl,
          hbrr, hbtt, hrt]
        rw [div_mul_eq_mul_div, div_eq_iff ht0]
        ring
    · intro a b hab
      exact ⟨1, by simp only [OneMemClass.coe_one, one_mul]; exact hιAKinj hab⟩

  haveI hMF : Module.Finite ↥A ↥(chartAlg R F {s}) :=
    IsIntegralClosure.finite ↥A ↥K' F ↥(chartAlg R F {s})

  letI algPC : Algebra (Polynomial R) ↥(chartAlg R F {s}) := (Polynomial.aeval (R := R) sC).toRingHom.toAlgebra
  letI algPA : Algebra (Polynomial R) ↥A := eA.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower (Polynomial R) ↥A ↥(chartAlg R F {s}) := by
    refine IsScalarTower.of_algebraMap_eq fun p => ?_
    change (Polynomial.aeval (R := R) sC) p =
      (Subalgebra.inclusion (adjoin_le_chartAlg R F {s})) (eA p)
    have hext : (Polynomial.aeval (R := R) sC : Polynomial R →ₐ[R] ↥(chartAlg R F {s})) =
        (Subalgebra.inclusion (adjoin_le_chartAlg R F {s})).comp (eA : Polynomial R →ₐ[R] ↥A) := by
      apply Polynomial.algHom_ext
      apply Subtype.ext
      rw [Polynomial.aeval_X, AlgHom.comp_apply, hsC]
      change s = ((eA Polynomial.X : ↥A) : F)
      show s = (Polynomial.aeval (R := R) s) Polynomial.X
      rw [Polynomial.aeval_X]
    exact congrArg (fun f : Polynomial R →ₐ[R] ↥(chartAlg R F {s}) => f p) hext
  haveI : Module.Finite (Polynomial R) ↥A :=
    Module.Finite.of_surjective (Algebra.linearMap (Polynomial R) ↥A) eA.surjective
  exact Module.Finite.trans ↥A ↥(chartAlg R F {s})

end

end S_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf (solution)
