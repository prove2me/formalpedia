-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.isRegularLocalRing_stalk_of_asIdeal_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/cadeef31-920d-5e54-b6c2-09f33f278b5e

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isRegularLocalRing_localization_fractionRing_tensor_chartAlgFin
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isRegularLocalRing_localization_fractionRing_tensor_chartAlgInf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isRegularLocalRing_stalk_of_asIdeal_eq_bot

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

noncomputable section

namespace RegGenA7c1

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem isRegularLocalRing_localization_of_comap_eq_bot
    (R : Type u) [CommRing R] [IsDomain R] (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (A : Type u) [CommRing A] [IsDomain A] [Algebra R A] (hinj : Function.Injective (algebraMap R A))
    (hR1 : ∀ (m : Ideal (K₀ ⊗[R] A)) [m.IsMaximal],
      IsRegularLocalRing (Localization.AtPrime m) ∧ ringKrullDim (Localization.AtPrime m) = (1 : ℕ∞))
    (q : Ideal A) [hq : q.IsPrime] (hqR : q.comap (algebraMap R A) = ⊥) :
    IsRegularLocalRing (Localization.AtPrime q) := by

  set N : Submonoid A := Algebra.algebraMapSubmonoid A (nonZeroDivisors R) with hN
  haveI hloc : IsLocalization N (K₀ ⊗[R] A) := IsLocalization.tensorRight (R := R) (S := A) K₀ (nonZeroDivisors R)
  have hNle : N ≤ nonZeroDivisors A := by
    rintro _ ⟨r, hr, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero fun h0 =>
      nonZeroDivisors.ne_zero hr (hinj (h0.trans (map_zero _).symm))
  haveI : IsDomain (K₀ ⊗[R] A) := IsLocalization.isDomain_of_le_nonZeroDivisors (K₀ ⊗[R] A) hNle
  have hdisj : Disjoint (N : Set A) (q : Set A) := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrq
    have : r ∈ q.comap (algebraMap R A) := hrq
    rw [hqR, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hr this

  set p : Ideal (K₀ ⊗[R] A) := q.map (algebraMap A (K₀ ⊗[R] A)) with hp
  haveI hpprime : p.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint N _ q hq hdisj
  have hpcomap : p.comap (algebraMap A (K₀ ⊗[R] A)) = q :=
    IsLocalization.under_map_of_isPrime_disjoint N _ hq hdisj

  have hT0 : IsLocalization.AtPrime (Localization.AtPrime p) (p.comap (algebraMap A (K₀ ⊗[R] A))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization N (Localization.AtPrime p) p
  have hT : IsLocalization.AtPrime (Localization.AtPrime p) q := by
    convert hT0 using 2
    exact hpcomap.symm
  let e : Localization.AtPrime q ≃ₐ[A] Localization.AtPrime p :=
    @IsLocalization.algEquiv A _ q.primeCompl (Localization.AtPrime q) _ _ _ (Localization.AtPrime p) _ _ hT

  suffices hreg : IsRegularLocalRing (Localization.AtPrime p) by
    haveI := hreg
    exact IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime p) e.symm.toRingEquiv
  by_cases hmax : p.IsMaximal
  · haveI := hmax
    exact (hR1 p).1
  by_cases hp0 : p = ⊥
  ·
    have hmI : IsLocalRing.maximalIdeal (Localization.AtPrime p) = ⊥ := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, eq_bot_iff]
      exact (Ideal.map_mono hp0.le).trans_eq Ideal.map_bot
    have hF : IsField (Localization.AtPrime p) :=
      (IsLocalRing.isField_iff_maximalIdeal_eq).mpr hmI
    letI := hF.toField
    infer_instance
  ·
    exfalso
    obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hpprime.ne_top
    have hpm' : p ≠ m := fun h => hmax (h ▸ hm)
    haveI := hm
    obtain ⟨-, hdim⟩ := hR1 m
    haveI : IsDomain (Localization.AtPrime m) :=
      IsLocalization.isDomain_of_le_nonZeroDivisors _ (Ideal.primeCompl_le_nonZeroDivisors m)
    have hK : Ring.KrullDimLE 1 (Localization.AtPrime m) := by
      rw [Ring.krullDimLE_iff]
      exact le_of_eq (by rw [hdim]; rfl)
    have hdisj' : Disjoint (m.primeCompl : Set (K₀ ⊗[R] A)) (p : Set _) := by
      rw [Set.disjoint_left]
      intro a ha hap
      exact ha (hpm hap)
    set p' : Ideal (Localization.AtPrime m) := p.map (algebraMap _ (Localization.AtPrime m)) with hp'
    haveI : p'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl _ p hpprime hdisj'
    have hp'comap : p'.comap (algebraMap _ (Localization.AtPrime m)) = p :=
      IsLocalization.under_map_of_isPrime_disjoint m.primeCompl _ hpprime hdisj'
    have hp'0 : p' ≠ ⊥ := by
      intro h
      apply hp0
      rw [← hp'comap, h, Ideal.comap_bot_of_injective]
      exact IsLocalization.injective (Localization.AtPrime m) (Ideal.primeCompl_le_nonZeroDivisors m)
    have hp'max : p'.IsMaximal :=
      (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hK) p' hp'0 inferInstance
    have hp'eq : p' = IsLocalRing.maximalIdeal (Localization.AtPrime m) :=
      IsLocalRing.eq_maximalIdeal hp'max
    apply hpm'
    rw [← hp'comap, hp'eq]
    exact IsLocalization.AtPrime.under_maximalIdeal (S := Localization.AtPrime m) (I := m)

theorem isRegularLocalRing_stalk_of_chart
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {X : Scheme.{u}} (ι : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion ι]
    (f : X ⟶ Spec (CommRingCat.of R)) (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (hreg : ∀ (q : Ideal A) [q.IsPrime], q.comap (algebraMap R A) = ⊥ → IsRegularLocalRing (Localization.AtPrime q))
    (y : PrimeSpectrum A) (hy : ((f.base (ι.base y)).asIdeal) = ⊥) :
    IsRegularLocalRing (X.presheaf.stalk (ι.base y)) := by
  have h1 : f.base (ι.base y) = (Spec.map (CommRingCat.ofHom (algebraMap R A))).base y := by
    rw [← hι]
    rfl
  have hq : y.asIdeal.comap (algebraMap R A) = ⊥ := by
    rw [h1] at hy
    exact hy
  haveI : IsRegularLocalRing (Localization.AtPrime y.asIdeal) := hreg y.asIdeal hq

  let e₁ : Localization.AtPrime y.asIdeal ≃+* (Spec (CommRingCat.of A)).presheaf.stalk y :=
    (StructureSheaf.stalkIso A y).toRingEquiv
  haveI : IsIso (ι.stalkMap y) := inferInstance
  let e₂ : X.presheaf.stalk (ι.base y) ≃+* (Spec (CommRingCat.of A)).presheaf.stalk y :=
    (asIso (ι.stalkMap y)).commRingCatIsoToRingEquiv
  exact IsRegularLocalRing.of_ringEquiv (e₁.trans e₂.symm)

end RegGenA7c1

end

open AlgebraicCurve.TwoChartIntegralModel in

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (x : ↥(AlgebraicCurve.TwoChartIntegralModel R F j))
    (hx : ((AlgebraicCurve.TwoChartIntegralModel.toBase R F j).base x).asIdeal = ⊥) :
    IsRegularLocalRing ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk x) := by
  have hinjF : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R K₀ F]
    exact (algebraMap K₀ F).injective.comp (IsFractionRing.injective R K₀)
  have hinjS : ∀ (S : Set F), Function.Injective (algebraMap R ↥(chartAlg R F S)) := fun S r s h =>
    hinjF (by simpa using congrArg (fun a : ↥(chartAlg R F S) => (a : F)) h)
  rcases mem_range_ιFin_or_mem_range_ιInf R F j x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · refine RegGenA7c1.isRegularLocalRing_stalk_of_chart (ιFin R F j) (toBase R F j) (ιFin_toBase R F j) ?_ y hx
    intro q _ hq
    exact RegGenA7c1.isRegularLocalRing_localization_of_comap_eq_bot R K₀ ↥(chartAlgFin R F j) (hinjS _)
      (fun m _ =>
        AlgebraicCurve.TwoChartIntegralModel.isRegularLocalRing_localization_fractionRing_tensor_chartAlgFin
          R K₀ F j htj hFD hsep m) q hq
  · refine RegGenA7c1.isRegularLocalRing_stalk_of_chart (ιInf R F j) (toBase R F j) (ιInf_toBase R F j) ?_ y hx
    intro q _ hq
    exact RegGenA7c1.isRegularLocalRing_localization_of_comap_eq_bot R K₀ ↥(chartAlgInf R F j) (hinjS _)
      (fun m _ =>
        AlgebraicCurve.TwoChartIntegralModel.isRegularLocalRing_localization_fractionRing_tensor_chartAlgInf
          R K₀ F j htj hFD hsep m) q hq

end S_AlgebraicCurve_TwoChartIntegralModel_isRegularLocalRing_stalk_of_asIdeal_eq_bot
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isRegularLocalRing_stalk_of_asIdeal_eq_bot (solution)
