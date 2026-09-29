-- Prove2me | solution 1 for AlgebraicGeometry.exists_restrict_twist_of_isPullback_model_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/52cfbef3-3eeb-5344-b1fa-d60baef3c0a1

import Mathlib
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_restrict_twist_of_isPullback_model_of_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

theorem solution
    {A : Type u} [CommRing A] (R₀ : Type u) [CommRing R₀] [Algebra A R₀] (k : Type u) [CommRing k] [Algebra A k] [Algebra R₀ k]
    [IsScalarTower A R₀ k]
    {X : Scheme.{u}} (cX : X ⟶ Spec (CommRingCat.of A))
    (φ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k)) (hφ : φ ≫ specMap R₀ k = specMap R₀ k)
    (F : pullback cX (specMap A k) ⟶ pullback cX (specMap A k))
    (hF₁ : F ≫ pullback.fst cX (specMap A k) = pullback.fst cX (specMap A k))
    (hF₂ : F ≫ pullback.snd cX (specMap A k) = pullback.snd cX (specMap A k) ≫ φ)
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) (i : SchemeHomOver c (baseChange A cX k))
    {Cₚ : Scheme.{u}} (cₚ : Cₚ ⟶ Spec (CommRingCat.of R₀)) (iₚ : Cₚ ⟶ pullback cX (specMap A R₀)) (g : C ⟶ Cₚ)
    (hg : IsPullback g c cₚ (specMap R₀ k))
    (hgi : g ≫ iₚ ≫ pullback.fst cX (specMap A R₀) = i.1 ≫ pullback.fst cX (specMap A k)) :
    ∃ F_C : C ⟶ C,
      F_C ≫ i.1 = i.1 ≫ F ∧ F_C ≫ g = g ∧ IsPullback F_C c c φ ∧
      ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c, ∃ x' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c,
        x'.1 ≫ F_C = φ ≫ x.1 ∧
        x'.1 ≫ i.1 ≫ pullback.fst cX (specMap A k) = φ ≫ x.1 ≫ i.1 ≫ pullback.fst cX (specMap A k) := by

  have hφ' : (c ≫ φ) ≫ specMap R₀ k = g ≫ cₚ := by rw [Category.assoc, hφ]; exact hg.w.symm
  let F_C : C ⟶ C := hg.lift g (c ≫ φ) hφ'.symm
  have hFg : F_C ≫ g = g := hg.lift_fst _ _ _
  have hFc : F_C ≫ c = c ≫ φ := hg.lift_snd _ _ _

  have hAk : specMap A k = specMap R₀ k ≫ specMap A R₀ := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hφA : φ ≫ specMap A k = specMap A k := by rw [hAk, ← Category.assoc, hφ]
  refine ⟨F_C, ?_, hFg, ?_, ?_⟩
  ·
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hF₁, ← hgi, ← Category.assoc, hFg]
    · rw [Category.assoc, Category.assoc, hF₂, i.2, ← Category.assoc, i.2, hFc]
  ·
    refine IsPullback.of_right ?_ hFc hg
    rw [hFg]

    refine IsPullback.of_iso hg (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;>
      simp [hφ]
  ·
    intro x
    have hx : (φ ≫ x.1 ≫ g) ≫ cₚ = 𝟙 _ ≫ specMap R₀ k := by
      simp only [Category.assoc, Category.id_comp]
      rw [hg.w, reassoc_of% x.2, hφ]
    refine ⟨⟨hg.lift (φ ≫ x.1 ≫ g) (𝟙 _) hx, hg.lift_snd _ _ _⟩, ?_, ?_⟩
    ·
      apply hg.hom_ext
      · rw [Category.assoc, hFg, hg.lift_fst, Category.assoc]
      · rw [Category.assoc, hFc, ← Category.assoc, hg.lift_snd, Category.id_comp, Category.assoc, x.2, Category.comp_id]
    · show hg.lift (φ ≫ x.1 ≫ g) (𝟙 _) hx ≫ i.1 ≫ _ = _
      rw [← hgi, ← Category.assoc, hg.lift_fst, Category.assoc, Category.assoc]

end S_AlgebraicGeometry_exists_restrict_twist_of_isPullback_model_of_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_exists_restrict_twist_of_isPullback_model_of_comp_eq (solution)
