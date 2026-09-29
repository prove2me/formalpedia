-- Prove2me | solution 1 for AlgebraicCurve.flat_fst_and_forall_isPrime_eq_comap_maximalIdeal_of_isPullback_of_ringEquiv_adicCompletion_stalk_min
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ac9a6b07-272d-5e5d-8b48-2ea4659a60ba

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel

import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specializes_isLocalization_atPrime_stalk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_flat_fst_and_forall_isPrime_eq_comap_maximalIdeal_of_isPullback_of_ringEquiv_adicCompletion_stalk_min

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

    Flat (e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))) ∧
    (∀ 𝔮 : Ideal (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x)),
      𝔮.IsPrime → 𝔮 ≠ maximalIdeal (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x)) →
        ∃ (y : X) (hy : y ⤳ x), y ≠ x ∧
          𝔮 = (maximalIdeal (X.presheaf.stalk y)).comap
            ((X.presheaf.stalkSpecializes hy).hom.comp
              ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap x).hom)) := by
  set π := e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁)) with hπdef

  haveI hflatπ : Flat π := by
    haveI : (CommRingCat.ofHom ι₁).hom.Flat := by
      show ι₁.Flat
      letI : Algebra A₁ ↥A := ι₁.toAlgebra
      haveI : Module.IsTorsionFree A₁ ↥A := by
        refine ⟨fun r hr a b hab => ?_⟩
        have hr0 : r ≠ 0 := by
          rintro rfl
          exact not_isRegular_zero hr
        have : ι₁ r * a = ι₁ r * b := hab
        exact mul_left_cancel₀ (fun h => hr0 (hι₁ (by rw [h, map_zero]))) this
      have hflat : Module.Flat A₁ ↥A := by
        rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
        infer_instance
      exact hflat
    haveI : Flat (Spec.map (CommRingCat.ofHom ι₁)) := Flat.SpecMap_iff.mpr ‹_›
    rw [hπdef]; infer_instance
  refine ⟨?_, hflatπ, ?_⟩
  ·
    have h := congrArg (fun k : X ⟶ X₀ => k.base x) he₁'
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    rw [← hx₀, hπdef]
    simp only [Scheme.Hom.comp_base, TopCat.comp_app]
    exact h
  ·
    intro 𝔮 h𝔮 hne
    let φ : ↑(X₁.presheaf.stalk (π.base x)) →+* ↑(X.presheaf.stalk x) := (π.stalkMap x).hom
    have hφflat : φ.Flat := Flat.stalkMap π x
    letI alg : Algebra ↑(X₁.presheaf.stalk (π.base x)) ↑(X.presheaf.stalk x) := φ.toAlgebra
    haveI : Module.Flat ↑(X₁.presheaf.stalk (π.base x)) ↑(X.presheaf.stalk x) := hφflat
    haveI : IsLocalHom (algebraMap ↑(X₁.presheaf.stalk (π.base x)) ↑(X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (π.stalkMap x).hom)
    haveI : Module.FaithfullyFlat ↑(X₁.presheaf.stalk (π.base x)) ↑(X.presheaf.stalk x) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    obtain ⟨⟨𝔓, h𝔓⟩, h𝔓𝔮⟩ :=
      PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := ↑(X₁.presheaf.stalk (π.base x)))
        (B := ↑(X.presheaf.stalk x)) ⟨𝔮, h𝔮⟩
    have h𝔓𝔮' : 𝔓.comap φ = 𝔮 := by
      have := congrArg PrimeSpectrum.asIdeal h𝔓𝔮
      simp at this
      exact this
    obtain ⟨y, hy, hloc⟩ := AlgebraicGeometry.Scheme.exists_specializes_isLocalization_atPrime_stalk x 𝔓
    have h𝔓eq : 𝔓 = (maximalIdeal ↑(X.presheaf.stalk y)).comap (X.presheaf.stalkSpecializes hy).hom := by
      letI := (X.presheaf.stalkSpecializes hy).hom.toAlgebra
      haveI := hloc
      exact (IsLocalization.AtPrime.under_maximalIdeal ↑(X.presheaf.stalk y) 𝔓).symm
    refine ⟨y, hy, ?_, ?_⟩
    · rintro rfl
      apply hne
      rw [← h𝔓𝔮', h𝔓eq, TopCat.Presheaf.stalkSpecializes_refl]
      change Ideal.comap φ (Ideal.comap (RingHom.id _) (maximalIdeal _)) = _
      rw [Ideal.comap_id]
      exact ((IsLocalRing.local_hom_TFAE φ).out 0 4).mp (by simp only [φ]; infer_instance)
    · rw [← h𝔓𝔮', h𝔓eq, Ideal.comap_comap]

end S_AlgebraicCurve_flat_fst_and_forall_isPrime_eq_comap_maximalIdeal_of_isPullback_of_ringEquiv_adicCompletion_stalk_min
end P2MW
export P2MW.S_AlgebraicCurve_flat_fst_and_forall_isPrime_eq_comap_maximalIdeal_of_isPullback_of_ringEquiv_adicCompletion_stalk_min (solution)
