-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.isReduced_pullback_toBase_of_forall_map_span_eq_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/cef13e7a-08e0-5f97-8abc-2703e988d951

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_IsIntegrallyClosed_isReduced_quotient_span_singleton_of_forall_mem_minimalPrimes
import Theorems.Thm_Algebra_isReduced_tensorProduct_of_perfectField
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_forall_map_span_eq_maximalIdeal

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel IsLocalRing
open scoped TensorProduct

namespace RedFibAux

theorem isReduced_tensorProduct_of_isReduced_quotient
    (R : Type u) [CommRing R] [IsLocalRing R]
    [PerfectField (ResidueField R)]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (B : Type u) [CommRing B] [Algebra R B]
    (hB : IsReduced (B ⧸ Ideal.span {algebraMap R B ϖ}))
    (κ : Type u) [Field κ] [Algebra R κ] (hκ : algebraMap R κ ϖ = 0) :
    IsReduced (B ⊗[R] κ) := by
  classical

  have hker : ∀ a ∈ maximalIdeal R, algebraMap R κ a = 0 := by
    intro a ha
    rw [hϖ, Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, hκ, zero_mul]
  letI algk : Algebra (ResidueField R) κ :=
    (Ideal.Quotient.lift (maximalIdeal R) (algebraMap R κ) hker).toAlgebra
  haveI : IsScalarTower R (ResidueField R) κ :=
    IsScalarTower.of_algebraMap_eq fun r => (Ideal.Quotient.lift_mk (maximalIdeal R) (algebraMap R κ) hker).symm

  have hmap : (maximalIdeal R).map (algebraMap R B) = Ideal.span {algebraMap R B ϖ} := by
    rw [hϖ, Ideal.map_span, Set.image_singleton]
  haveI : IsReduced (B ⧸ (maximalIdeal R).map (algebraMap R B)) := by rw [hmap]; exact hB
  let e₁ : (B ⧸ (maximalIdeal R).map (algebraMap R B)) ≃ₐ[B] B ⊗[R] (ResidueField R) :=
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (maximalIdeal R)
  haveI : IsReduced (B ⊗[R] ResidueField R) := isReduced_of_injective e₁.symm e₁.symm.injective
  let e₂ : ResidueField R ⊗[R] B ≃ₐ[R] B ⊗[R] ResidueField R := Algebra.TensorProduct.comm R _ _
  haveI : IsReduced (ResidueField R ⊗[R] B) := isReduced_of_injective e₂ e₂.injective

  haveI : IsReduced (κ ⊗[ResidueField R] (ResidueField R ⊗[R] B)) :=
    Algebra.isReduced_tensorProduct_of_perfectField (ResidueField R) (ResidueField R ⊗[R] B) κ

  let e₃ : κ ⊗[ResidueField R] (ResidueField R ⊗[R] B) ≃ₐ[ResidueField R] κ ⊗[R] B :=
    Algebra.TensorProduct.cancelBaseChange R (ResidueField R) (ResidueField R) κ B
  let e₄ : κ ⊗[R] B ≃ₐ[R] B ⊗[R] κ := Algebra.TensorProduct.comm R _ _
  haveI : IsReduced (κ ⊗[R] B) := isReduced_of_injective e₃.symm e₃.symm.injective
  exact isReduced_of_injective e₄.symm e₄.symm.injective

theorem isReduced_pullback_spec_chartAlg
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (ResidueField R)]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (F : Type u) [Field F] [Algebra R F] (hinj : Function.Injective (algebraMap R F))
    (S : Set F) [IsNoetherianRing ↥(chartAlg R F S)]
    (h : ∀ (P : Ideal ↥(chartAlg R F S)) [P.IsPrime],
      P ∈ (Ideal.span {algebraMap R ↥(chartAlg R F S) ϖ}).minimalPrimes →
        Ideal.map (algebraMap ↥(chartAlg R F S) (Localization.AtPrime P)) (Ideal.span {algebraMap R ↥(chartAlg R F S) ϖ}) =
          maximalIdeal (Localization.AtPrime P))
    (κ : Type u) [Field κ] [Algebra R κ] (hκ : algebraMap R κ ϖ = 0) :
    AlgebraicGeometry.IsReduced
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap R ↥(chartAlg R F S))))
        (Spec.map (CommRingCat.ofHom (algebraMap R κ)))) := by
  haveI : IsIntegrallyClosed ↥(chartAlg R F S) := isIntegrallyClosed_chartAlg R F S
  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  have hx : algebraMap R ↥(chartAlg R F S) ϖ ≠ 0 := by
    intro h0
    apply hirr.ne_zero
    apply hinj
    rw [map_zero]
    exact congrArg Subtype.val h0
  have hB : _root_.IsReduced (↥(chartAlg R F S) ⧸ Ideal.span {algebraMap R ↥(chartAlg R F S) ϖ}) :=
    IsIntegrallyClosed.isReduced_quotient_span_singleton_of_forall_mem_minimalPrimes hx h
  haveI : _root_.IsReduced (↥(chartAlg R F S) ⊗[R] κ) :=
    isReduced_tensorProduct_of_isReduced_quotient R ϖ hϖ _ hB κ hκ
  haveI : AlgebraicGeometry.IsReduced (Spec (CommRingCat.of (↥(chartAlg R F S) ⊗[R] κ))) := inferInstance
  exact isReduced_of_isOpenImmersion (pullbackSpecIso R ↥(chartAlg R F S) κ).hom

end RedFibAux

open RedFibAux in

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (IsLocalRing.ResidueField R)]
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hFin : ∀ (P : Ideal ↥(chartAlgFin R F j)) [P.IsPrime],
      P ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ}).minimalPrimes →
        Ideal.map (algebraMap ↥(chartAlgFin R F j) (Localization.AtPrime P))
            (Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ}) =
          IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hInf : ∀ (P : Ideal ↥(chartAlgInf R F j)) [P.IsPrime],
      P ∈ (Ideal.span {algebraMap R ↥(chartAlgInf R F j) ϖ}).minimalPrimes →
        Ideal.map (algebraMap ↥(chartAlgInf R F j) (Localization.AtPrime P))
            (Ideal.span {algebraMap R ↥(chartAlgInf R F j) ϖ}) =
          IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (κ : Type u) [Field κ] [Algebra R κ] (hκ : algebraMap R κ ϖ = 0) :
    IsReduced (pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))) := by
  classical

  obtain ⟨hftF, hftI⟩ := finiteType_chartAlgFin_and_chartAlgInf R K₀ F j htj hFD hsep
  haveI : IsNoetherianRing ↥(chartAlgFin R F j) := Algebra.FiniteType.isNoetherianRing R _
  haveI : IsNoetherianRing ↥(chartAlgInf R F j) := Algebra.FiniteType.isNoetherianRing R _
  have hinj : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R K₀ F]
    exact (algebraMap K₀ F).injective.comp (IsFractionRing.injective R K₀)

  have hredF := isReduced_pullback_spec_chartAlg R ϖ hϖ F hinj {j} hFin κ hκ
  have hredI := isReduced_pullback_spec_chartAlg R ϖ hϖ F hinj {j⁻¹} hInf κ hκ

  let 𝒰 : (AlgebraicCurve.TwoChartIntegralModel R F j).OpenCover :=
    Scheme.Cover.mkOfCovers Bool
      (fun b => match b with | true => XFin R F j | false => XInf R F j)
      (fun b => match b with | true => ιFin R F j | false => ιInf R F j)
      (fun x => by
        rcases mem_range_ιFin_or_mem_range_ιInf R F j x with ⟨y, hy⟩ | ⟨y, hy⟩
        · exact ⟨true, y, hy⟩
        · exact ⟨false, y, hy⟩)
      (fun b => by cases b <;> dsimp only <;> infer_instance)
  let 𝒱 := Scheme.Pullback.openCoverOfLeft 𝒰 (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))
  haveI : ∀ i, AlgebraicGeometry.IsReduced (𝒱.X i) := by
    intro i
    change AlgebraicGeometry.IsReduced
      (pullback (𝒰.f i ≫ toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    rcases i with (_ | _)
    · have e : 𝒰.f false ≫ toBase R F j = Spec.map (CommRingCat.ofHom (algebraMap R ↥(chartAlgInf R F j))) :=
        ιInf_toBase R F j
      rw [e]; exact hredI
    · have e : 𝒰.f true ≫ toBase R F j = Spec.map (CommRingCat.ofHom (algebraMap R ↥(chartAlgFin R F j))) :=
        ιFin_toBase R F j
      rw [e]; exact hredF
  exact AlgebraicGeometry.IsReduced.of_openCover _ 𝒱

end S_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_forall_map_span_eq_maximalIdeal
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_forall_map_span_eq_maximalIdeal (solution)
