-- Prove2me | solution 1 for AlgebraicGeometry.exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/bdf0b9f0-c115-5795-8c92-a22c569b3c57

import Mathlib
import Definitions.Def_AlgebraicGeometry_SubalgebraStages
import Theorems.Thm_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

open _root_.AlgebraicGeometry.SubalgebraStages in
theorem solution
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ Spec (CommRingCat.of A₀)) (f₂ : X₂ ⟶ Spec (CommRingCat.of A₀))
    [QuasiCompact f₁] [LocallyOfFiniteType f₂]
    (a b : X₁ ⟶ X₂) (ha : a ≫ f₂ = f₁) (hb : b ≫ f₂ = f₁)
    (hab : pullback.fst f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ≫ a =
      pullback.fst f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ≫ b) (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      pullback.fst f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ≫ a =
        pullback.fst f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ≫ b := by
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
  let i₀ : ιᵒᵖ := op (Classical.arbitrary ι)

  let t : diagram S f₁ ⟶ (Functor.const ιᵒᵖ).obj (Spec (CommRingCat.of A₀)) :=
    { app := fun i => pullback.fst f₁ (specHom S i.unop) ≫ f₁
      naturality := fun i j h => by
        erw [Category.comp_id]
        exact diagram_map_fst_assoc S f₁ h f₁ }
  obtain ⟨k, hki, hk⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType (diagram S f₁) t f₂ (cone S f₁) hc
    (i := i₀) (pullback.fst f₁ (specHom S i₀.unop) ≫ a) (pullback.fst f₁ (specHom S i₀.unop) ≫ b)
    (by rw [Category.assoc, ha]; try rfl) (by rw [Category.assoc, hb]; try rfl)
    (by rw [cone_π_app_fst_assoc S f₁ i₀, cone_π_app_fst_assoc S f₁ i₀]; exact hab)
  refine ⟨S k.unop, k.unop.2.1, k.unop.2.2, ?_⟩
  rw [diagram_map_fst_assoc S f₁ hki, diagram_map_fst_assoc S f₁ hki] at hk
  exact hk

end S_AlgebraicGeometry_exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType
end P2MW
export P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType (solution)
