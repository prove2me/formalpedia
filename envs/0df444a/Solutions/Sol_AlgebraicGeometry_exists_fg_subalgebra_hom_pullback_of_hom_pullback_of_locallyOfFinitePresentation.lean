-- Prove2me | solution 1 for AlgebraicGeometry.exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/3c0af8f7-9016-54c4-a213-dbf9accbd5d9

import Mathlib
import Definitions.Def_AlgebraicGeometry_SubalgebraStages
import Theorems.Thm_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

open _root_.AlgebraicGeometry.SubalgebraStages in
theorem solution
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ Spec (CommRingCat.of A₀)) (f₂ : X₂ ⟶ Spec (CommRingCat.of A₀))
    [QuasiCompact f₁] [QuasiSeparated f₁] [LocallyOfFinitePresentation f₂]
    (g : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
      pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))
    (hg : g ≫ pullback.snd f₂ _ = pullback.snd f₁ _) (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ g₀ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ⟶
          pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))),
        g₀ ≫ pullback.snd f₂ _ = pullback.snd f₁ _ ∧
        ∀ (q₁ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
              pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))
          (q₂ : pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
              pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))),
          q₁ ≫ pullback.fst f₁ _ = pullback.fst f₁ _ →
          q₁ ≫ pullback.snd f₁ _ = pullback.snd f₁ _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) →
          q₂ ≫ pullback.fst f₂ _ = pullback.fst f₂ _ →
          q₂ ≫ pullback.snd f₂ _ = pullback.snd f₂ _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) →
          q₁ ≫ g₀ = g ≫ q₂ := by
  classical

  let ι : Type u := {T : Subalgebra A₀ A // T.FG ∧ (↑s : Set A) ⊆ T}
  haveI : Nonempty ι := ⟨⟨Algebra.adjoin A₀ ↑s, Subalgebra.fg_adjoin_finset s, Algebra.subset_adjoin⟩⟩
  haveI : IsDirected ι (· ≤ ·) := ⟨fun T₁ T₂ =>
    ⟨⟨T₁.1 ⊔ T₂.1, T₁.2.1.sup T₂.2.1, T₁.2.2.trans (SetLike.coe_subset_coe.mpr le_sup_left)⟩,
      (le_sup_left : T₁.1 ≤ T₁.1 ⊔ T₂.1), (le_sup_right : T₂.1 ≤ T₁.1 ⊔ T₂.1)⟩⟩
  let S : ι →o Subalgebra A₀ A := ⟨fun T => T.1, fun _ _ h => h⟩
  have hS : ∀ x : A, ∃ i, x ∈ S i := fun x =>
    ⟨⟨Algebra.adjoin A₀ ↑(insert x s), Subalgebra.fg_adjoin_finset _,
        fun y hy => Algebra.subset_adjoin (by simp [hy])⟩,
      Algebra.subset_adjoin (by simp)⟩
  obtain ⟨hc⟩ := SubalgebraStages.nonempty_isLimit_cone S hS f₁

  let t : diagram S f₁ ⟶ (Functor.const ιᵒᵖ).obj (Spec (CommRingCat.of A₀)) :=
    { app := fun i => pullback.fst f₁ (specHom S i.unop) ≫ f₁
      naturality := fun i j h => by
        erw [Category.comp_id]
        exact diagram_map_fst_assoc S f₁ h f₁ }

  have hg₀ : g ≫ pullback.snd f₂ (specHomTop (A₀ := A₀) (A := A)) = pullback.snd f₁ (specHomTop (A₀ := A₀) (A := A)) := hg
  have e₁ : pullback.fst f₁ (specHomTop (A₀ := A₀) (A := A)) ≫ f₁ = pullback.snd f₁ (specHomTop (A₀ := A₀) (A := A)) ≫ (specHomTop (A₀ := A₀) (A := A)) := pullback.condition
  have e₂ : pullback.fst f₂ (specHomTop (A₀ := A₀) (A := A)) ≫ f₂ = pullback.snd f₂ (specHomTop (A₀ := A₀) (A := A)) ≫ (specHomTop (A₀ := A₀) (A := A)) := pullback.condition

  let a : (cone S f₁).pt ⟶ X₂ := g ≫ pullback.fst f₂ (specHomTop (A₀ := A₀) (A := A))
  have ha' : ∀ i : ιᵒᵖ, (cone S f₁).π.app i ≫ t.app i = a ≫ f₂ := fun i => by
    change (cone S f₁).π.app i ≫ pullback.fst f₁ (specHom S i.unop) ≫ f₁ = (g ≫ pullback.fst f₂ (specHomTop (A₀ := A₀) (A := A))) ≫ f₂
    refine (cone_π_app_fst_assoc S f₁ i f₁).trans ?_
    refine e₁.trans ?_
    rw [← hg₀, Category.assoc, Category.assoc]
    exact congrArg (g ≫ ·) e₂.symm
  have ha : (cone S f₁).π ≫ t = (Functor.const ιᵒᵖ).map (a ≫ f₂) := by
    ext i
    exact ha' i
  obtain ⟨i, g', h1, h2⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation (diagram S f₁) t f₂ (cone S f₁) hc a ha

  have h2' : g' ≫ f₂ = pullback.snd f₁ (specHom S i.unop) ≫ specHom S i.unop :=
    h2.trans pullback.condition
  refine ⟨S i.unop, i.unop.2.1, i.unop.2.2, pullback.lift g' (pullback.snd f₁ (specHom S i.unop)) h2',
    pullback.lift_snd _ _ _, ?_⟩
  intro q₁ q₂ hq₁ hq₁' hq₂ hq₂'

  have hq : q₁ = (cone S f₁).π.app i := by
    apply pullback.hom_ext
    · exact hq₁.trans (cone_π_app_fst S f₁ i).symm
    · exact hq₁'.trans (cone_π_app_snd S f₁ i).symm
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hq]
    exact h1.trans (((congrArg (g ≫ ·) hq₂).symm).trans (Category.assoc _ _ _).symm)
  · rw [Category.assoc, pullback.lift_snd, Category.assoc, hq₂', ← Category.assoc, hg]
    exact hq₁'

end S_AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
end P2MW
export P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation (solution)
