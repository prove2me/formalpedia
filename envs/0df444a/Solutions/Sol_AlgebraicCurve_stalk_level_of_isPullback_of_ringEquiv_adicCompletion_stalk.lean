-- Prove2me | solution 1 for AlgebraicCurve.stalk_level_of_isPullback_of_ringEquiv_adicCompletion_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/eed4c927-6354-5fa8-9513-4306b667d5eb

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel

import Theorems.Thm_AlgebraicCurve_flat_fst_and_forall_isPrime_eq_comap_maximalIdeal_of_isPullback_of_ringEquiv_adicCompletion_stalk
import Theorems.Thm_AlgebraicCurve_isNoetherianRing_stalk_and_two_le_ringKrullDim_and_exists_eq_mul_pow_of_isPullback_of_ringEquiv_adicCompletion_stalk
import Theorems.Thm_AlgebraicCurve_forall_exists_not_isUnit_sub_germ_and_maximalIdeal_le_map_sup_span_of_isPullback_of_ringEquiv_adicCompletion_stalk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_stalk_level_of_isPullback_of_ringEquiv_adicCompletion_stalk
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry ModularCurve ModularCurve.UVCrossingModel

theorem solution
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ι₀ : A₀ →+* ↥A) [IsLocalHom ι₀] (hι₀ : Function.Injective ι₀)
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})
    (halg : ∀ a : ↥A, IsAlgebraic ↥(ι₀.range) a)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι₀)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι₀)) = toBase)

    (x : X) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x)
    (η₁ η₂ : X) (h₁ : η₁ ⤳ x) (h₂ : η₂ ⤳ x) (h₁x : η₁ ≠ x) (h₂x : η₂ ≠ x) (h₁₂ : η₁ ≠ η₂)
    (hη : ∀ η : X, η ⤳ x → η ≠ x → toBase.base η = closedPoint ↥A → η = η₁ ∨ η = η₂)
    {Fbar₁ : Type} [Field Fbar₁] [Algebra (ResidueField ↥A) Fbar₁]
    {Fbar₂ : Type} [Field Fbar₂] [Algebra (ResidueField ↥A) Fbar₂]
    (R₁ : RegularProlongation A F Fbar₁) (R₂ : RegularProlongation A F Fbar₂)
    (hR₁ : R₁.integers.toSubring = SemistableModel.localRing X φ η₁)
    (hR₂ : R₂.integers.toSubring = SemistableModel.localRing X φ η₂)

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

    g₁.base ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x) = x₀ ∧

    IsNoetherianRing (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x)) ∧
    (∀ s : X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x),
      ∃ a : A₁, ¬ IsUnit (s - (X₁.presheaf.germ ⊤ ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x) trivial).hom (f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom a)))) ∧
    (maximalIdeal (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x)) ≤
        (maximalIdeal (X₀.presheaf.stalk (g₁.base ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x)))).map
          (g₁.stalkMap ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x)).hom ⊔
        Ideal.span {(X₁.presheaf.germ ⊤ ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x) trivial).hom
          (f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom ϖ₁))}) ∧
    2 ≤ ringKrullDim (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x)) ∧
    (∃ (e' : ℕ) (v : X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x)),
      IsUnit v ∧
      (X₁.presheaf.germ ⊤ ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x) trivial).hom (f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom (ι₁' ϖ₀))) =
        v * (X₁.presheaf.germ ⊤ ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x) trivial).hom (f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom ϖ₁)) ^ e') ∧

    Flat (e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))) ∧
    (∀ 𝔮 : Ideal (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x)),
      𝔮.IsPrime → 𝔮 ≠ maximalIdeal (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x)) →
        ∃ (y : X) (hy : y ⤳ x), y ≠ x ∧
          𝔮 = (maximalIdeal (X.presheaf.stalk y)).comap
            ((X.presheaf.stalkSpecializes hy).hom.comp
              ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap x).hom)) := by
  obtain ⟨hpt, hflat, hprime⟩ := AlgebraicCurve.flat_fst_and_forall_isPrime_eq_comap_maximalIdeal_of_isPullback_of_ringEquiv_adicCompletion_stalk A hrk X toBase φ hφ A₀ ι₀ hι₀ ϖ₀ hϖ₀ halg X₀ toBase₀ iso hiso x hx hxc η₁ η₂ h₁ h₂ h₁x h₂x h₁₂ hη R₁ R₂ hR₁ hR₂ x₀ hx₀ w hw e he A₁ ι₁' ι₁ hι₁ hcomp ϖ₁ hϖ₁ X₁ f₁ g₁ hsq e₁ he₁ he₁'
  obtain ⟨hnoeth, hdim, hpow⟩ := AlgebraicCurve.isNoetherianRing_stalk_and_two_le_ringKrullDim_and_exists_eq_mul_pow_of_isPullback_of_ringEquiv_adicCompletion_stalk A hrk X toBase φ hφ A₀ ι₀ hι₀ ϖ₀ hϖ₀ halg X₀ toBase₀ iso hiso x hx hxc η₁ η₂ h₁ h₂ h₁x h₂x h₁₂ hη R₁ R₂ hR₁ hR₂ x₀ hx₀ w hw e he A₁ ι₁' ι₁ hι₁ hcomp ϖ₁ hϖ₁ X₁ f₁ g₁ hsq e₁ he₁ he₁'
  obtain ⟨hrat, hmax⟩ := AlgebraicCurve.forall_exists_not_isUnit_sub_germ_and_maximalIdeal_le_map_sup_span_of_isPullback_of_ringEquiv_adicCompletion_stalk A hrk X toBase φ hφ A₀ ι₀ hι₀ ϖ₀ hϖ₀ halg X₀ toBase₀ iso hiso x hx hxc η₁ η₂ h₁ h₂ h₁x h₂x h₁₂ hη R₁ R₂ hR₁ hR₂ x₀ hx₀ w hw e he A₁ ι₁' ι₁ hι₁ hcomp ϖ₁ hϖ₁ X₁ f₁ g₁ hsq e₁ he₁ he₁'
  exact ⟨hpt, hnoeth, hrat, hmax, hdim, hpow, hflat, hprime⟩

end S_AlgebraicCurve_stalk_level_of_isPullback_of_ringEquiv_adicCompletion_stalk
end P2MW
export P2MW.S_AlgebraicCurve_stalk_level_of_isPullback_of_ringEquiv_adicCompletion_stalk (solution)
