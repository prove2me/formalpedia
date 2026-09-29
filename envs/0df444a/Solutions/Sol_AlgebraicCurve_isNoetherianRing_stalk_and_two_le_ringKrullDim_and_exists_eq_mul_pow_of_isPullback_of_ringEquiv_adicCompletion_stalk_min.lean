-- Prove2me | solution 1 for AlgebraicCurve.isNoetherianRing_stalk_and_two_le_ringKrullDim_and_exists_eq_mul_pow_of_isPullback_of_ringEquiv_adicCompletion_stalk_min
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/7c5e52a0-8258-50f4-80a7-419f0fd31833

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel

import Theorems.Thm_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_two_le_ringKrullDim
import Theorems.Thm_IsLocalRing_ringKrullDim_adicCompletion_maximalIdeal_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_isNoetherianRing_stalk_and_two_le_ringKrullDim_and_exists_eq_mul_pow_of_isPullback_of_ringEquiv_adicCompletion_stalk_min
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry ModularCurve ModularCurve.UVCrossingModel

theorem solution
    {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ι₀ : A₀ →+* ↥A) [IsLocalHom ι₀] (hι₀ : Function.Injective ι₀)
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})
    (halg : ∀ a : ↥A, IsAlgebraic ↥(ι₀.range) a)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι₀)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι₀)) = toBase)

    (x : X) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x)
    (hbranch : ∃ η : X, η ⤳ x ∧ η ≠ x ∧ toBase.base η = closedPoint ↥A)

    (x₀ : X₀) (hx₀ : (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀))).base x = x₀)
    (w : ℕ) (hw : 1 ≤ w)
    (e : AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀) ≃+*
      UVCrossingModel (AdicCompletion (maximalIdeal A₀) A₀)
        ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w))
    (he : ∀ a : A₀,
      e (algebraMap (X₀.presheaf.stalk x₀) (AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀))
          ((X₀.presheaf.germ ⊤ x₀ trivial).hom
            (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))) =
        const ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w)
          (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) a))

    (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsDiscreteValuationRing A₁]
    (ι₁' : A₀ →+* A₁) [IsLocalHom ι₁'] (ι₁ : A₁ →+* ↥A) [IsLocalHom ι₁] (hι₁ : Function.Injective ι₁)
    (hcomp : ι₁.comp ι₁' = ι₀)
    (ϖ₁ : A₁) (hϖ₁ : maximalIdeal A₁ = Ideal.span {ϖ₁})
    (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁)) (g₁ : X₁ ⟶ X₀)
    (hsq : IsPullback g₁ f₁ toBase₀ (Spec.map (CommRingCat.ofHom ι₁')))
    (e₁ : X ≅ Limits.pullback f₁ (Spec.map (CommRingCat.ofHom ι₁)))
    (he₁ : e₁.hom ≫ Limits.pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁)) = toBase)
    (he₁' : (e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))) ≫ g₁ =
      iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀)))
    :
    IsNoetherianRing (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x)) ∧
    2 ≤ ringKrullDim (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x)) ∧
    (∃ (e' : ℕ) (v : X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x)),
      IsUnit v ∧
      (X₁.presheaf.germ ⊤ ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x) trivial).hom (f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom (ι₁' ϖ₀))) =
        v * (X₁.presheaf.germ ⊤ ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x) trivial).hom (f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom ϖ₁)) ^ e') := by
  set π := e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁)) with hπdef

  have hg : g₁.base (π.base x) = x₀ := by
    have h := congrArg (fun k : X ⟶ X₀ => k.base x) he₁'
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    rw [← hx₀, hπdef]
    simp only [Scheme.Hom.comp_base, TopCat.comp_app]
    exact h

  haveI : LocallyOfFinitePresentation f₁ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hsq inferInstance
  haveI : IsLocallyNoetherian X₁ := LocallyOfFiniteType.isLocallyNoetherian f₁
  haveI : IsLocallyNoetherian X₀ := LocallyOfFiniteType.isLocallyNoetherian toBase₀
  have hnoeth : IsNoetherianRing (X₁.presheaf.stalk (π.base x)) := inferInstance
  refine ⟨hnoeth, ?_, ?_⟩
  ·

    have hirr₀ : Irreducible ϖ₀ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ₀).mpr hϖ₀
    obtain ⟨hdom, hdvr, hcompl, hirr, -, -⟩ :=
      IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete A₀ ϖ₀ hirr₀
    have h2M : 2 ≤ ringKrullDim (UVCrossingModel (AdicCompletion (maximalIdeal A₀) A₀)
        ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w)) :=
      ModularCurve.UVCrossingModel.two_le_ringKrullDim _ hirr w hw
    have h2c : 2 ≤ ringKrullDim (AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀)) := by
      rw [ringKrullDim_eq_of_ringEquiv e]; exact h2M
    have h20 : 2 ≤ ringKrullDim (X₀.presheaf.stalk x₀) := by
      rw [← IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal_eq]; exact h2c
    have h20' : 2 ≤ ringKrullDim (X₀.presheaf.stalk (g₁.base (π.base x))) := by
      rw [hg]; exact h20

    have hι₁' : Function.Injective ι₁' := by
      intro a b hab
      apply hι₀
      rw [← hcomp]
      simp [hab]
    haveI : Flat g₁ := by
      haveI : (CommRingCat.ofHom ι₁').hom.Flat := by
        show ι₁'.Flat
        letI : Algebra A₀ A₁ := ι₁'.toAlgebra
        haveI : Module.IsTorsionFree A₀ A₁ := by
          refine ⟨fun r hr a b hab => ?_⟩
          have hr0 : r ≠ 0 := by
            rintro rfl
            exact not_isRegular_zero hr
          have : ι₁' r * a = ι₁' r * b := hab
          exact mul_left_cancel₀ (fun h => hr0 (hι₁' (by rw [h, map_zero]))) this
        have hflat : Module.Flat A₀ A₁ := by
          rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
          infer_instance
        exact hflat
      haveI : Flat (Spec.map (CommRingCat.ofHom ι₁')) := Flat.SpecMap_iff.mpr ‹_›
      exact MorphismProperty.of_isPullback (P := @Flat) hsq.flip inferInstance

    let ψ : ↑(X₀.presheaf.stalk (g₁.base (π.base x))) →+* ↑(X₁.presheaf.stalk (π.base x)) :=
      (g₁.stalkMap (π.base x)).hom
    letI alg : Algebra ↑(X₀.presheaf.stalk (g₁.base (π.base x))) ↑(X₁.presheaf.stalk (π.base x)) := ψ.toAlgebra
    haveI : Module.Flat ↑(X₀.presheaf.stalk (g₁.base (π.base x))) ↑(X₁.presheaf.stalk (π.base x)) :=
      Flat.stalkMap g₁ (π.base x)
    haveI : (maximalIdeal ↑(X₁.presheaf.stalk (π.base x))).LiesOver
        (maximalIdeal ↑(X₀.presheaf.stalk (g₁.base (π.base x)))) := by
      refine ⟨?_⟩
      have hcm : Ideal.comap ψ (maximalIdeal _) = maximalIdeal _ :=
        ((IsLocalRing.local_hom_TFAE ψ).out 0 4).mp (by simp only [ψ]; infer_instance)
      change _ = Ideal.comap ψ _
      exact hcm.symm
    have hh := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
      (maximalIdeal ↑(X₀.presheaf.stalk (g₁.base (π.base x)))) (maximalIdeal ↑(X₁.presheaf.stalk (π.base x)))
    have hle : (maximalIdeal ↑(X₀.presheaf.stalk (g₁.base (π.base x)))).height ≤
        (maximalIdeal ↑(X₁.presheaf.stalk (π.base x))).height := by
      rw [hh]; exact le_self_add
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at h20' ⊢
    exact le_trans h20' (by exact_mod_cast hle)
  ·
    have hι₁' : Function.Injective ι₁' := by
      intro a b hab
      apply hι₀
      rw [← hcomp]
      simp [hab]
    have hirr₁ : Irreducible ϖ₁ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ₁).mpr hϖ₁
    have h0 : ι₁' ϖ₀ ≠ 0 := by
      intro h
      have hirr₀ : Irreducible ϖ₀ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ₀).mpr hϖ₀
      exact hirr₀.ne_zero (hι₁' (by rw [h, map_zero]))
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hirr₁
    refine ⟨n, (X₁.presheaf.germ ⊤ (π.base x) trivial).hom
      (f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom (u : A₁))), ?_, ?_⟩
    · exact ((u.isUnit.map _).map _).map _
    · rw [hu]
      simp only [map_mul, map_pow]

end S_AlgebraicCurve_isNoetherianRing_stalk_and_two_le_ringKrullDim_and_exists_eq_mul_pow_of_isPullback_of_ringEquiv_adicCompletion_stalk_min
end P2MW
export P2MW.S_AlgebraicCurve_isNoetherianRing_stalk_and_two_le_ringKrullDim_and_exists_eq_mul_pow_of_isPullback_of_ringEquiv_adicCompletion_stalk_min (solution)
