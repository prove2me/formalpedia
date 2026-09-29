-- Prove2me | solution 1 for AlgebraicCurve.localRing_le_integers_and_forall_mem_toValuationSubring_and_algebraMap_mem_localRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/5a9e7fe2-369c-5589-8cfa-6535046ec765

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_localRing_le_integers_and_forall_mem_toValuationSubring_and_algebraMap_mem_localRing

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry ModularCurve ModularCurve.UVCrossingModel

set_option linter.unusedVariables false in
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
    (S : Set (Place L F))
    (hS : ∀ P : Place L F, P ∈ S ↔
      ∀ f : F, f ∈ SemistableModel.localRing X φ x → f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
        (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ SemistableModel.localRing X φ x, f * g = 1))
    :
    (∀ f : F, f ∈ SemistableModel.localRing X φ x → f ∈ R₁.integers ∧ f ∈ R₂.integers ∧ ∀ P ∈ S, f ∈ P.toValuationSubring) ∧
      (∀ a : ↥A, algebraMap L F (a : L) ∈ SemistableModel.localRing X φ x) := by

  have hle : ∀ y : X, y ⤳ x → SemistableModel.localRing X φ x ≤ SemistableModel.localRing X φ y := by
    intro y hy f hf
    obtain ⟨t, rfl⟩ := hf
    refine ⟨(X.presheaf.stalkSpecializes hy).hom t, ?_⟩
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.algebraMap_toAlgebra]
    congr 1
    change (X.presheaf.stalkSpecializes hy ≫ X.presheaf.stalkSpecializes _).hom t = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]
  refine ⟨fun f hf => ⟨?_, ?_, fun P hP => ((hS P).mp hP f hf).1⟩, fun a => ?_⟩
  · have := hle η₁ h₁ hf
    rw [← hR₁] at this
    exact this
  · have := hle η₂ h₂ hf
    rw [← hR₂] at this
    exact this
  ·
    refine ⟨(X.presheaf.germ ⊤ x trivial).hom (toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom a)), ?_⟩
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.algebraMap_toAlgebra]
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq, hφ]
    change (X.presheaf.germ ⊤ x trivial ≫ X.presheaf.stalkSpecializes _).hom _ = _
    rw [TopCat.Presheaf.germ_stalkSpecializes]
    rfl

end S_AlgebraicCurve_localRing_le_integers_and_forall_mem_toValuationSubring_and_algebraMap_mem_localRing
end P2MW
export P2MW.S_AlgebraicCurve_localRing_le_integers_and_forall_mem_toValuationSubring_and_algebraMap_mem_localRing (solution)
