-- Prove2me | solution 1 for AlgebraicGeometry.exists_fg_subalgebra_opens_preimage_eq_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/25a7e5d9-c18f-53ae-a1eb-33311feadd55

import Mathlib
import Definitions.Def_AlgebraicGeometry_SubalgebraStages
import Theorems.Thm_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_opens_preimage_eq_of_isCompact

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) [QuasiCompact f] [QuasiSeparated f]
    (W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))).Opens)
    (hW : IsCompact (W : Set ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))))) (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ W₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))).Opens,
        IsCompact (W₀ : Set ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))) ∧
        ∀ q : pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
            pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))),
          q ≫ pullback.fst f _ = pullback.fst f _ →
          q ≫ pullback.snd f _ = pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) →
          q ⁻¹ᵁ W₀ = W := by
  classical
  let ι : Type u := {T : Subalgebra A₀ A // T.FG ∧ (↑s : Set A) ⊆ T}
  haveI : Nonempty ι := ⟨⟨Algebra.adjoin A₀ ↑s, Subalgebra.fg_adjoin_finset s, Algebra.subset_adjoin⟩⟩
  haveI : IsDirected ι (· ≤ ·) := ⟨fun T₁ T₂ =>
    ⟨⟨T₁.1 ⊔ T₂.1, T₁.2.1.sup T₂.2.1, T₁.2.2.trans (SetLike.coe_subset_coe.mpr le_sup_left)⟩,
      (le_sup_left : T₁.1 ≤ T₁.1 ⊔ T₂.1), (le_sup_right : T₂.1 ≤ T₁.1 ⊔ T₂.1)⟩⟩
  let S : ι →o Subalgebra A₀ A := ⟨fun T => T.1, fun _ _ h => h⟩
  have hS : ∀ a : A, ∃ i, a ∈ S i := fun a =>
    ⟨⟨Algebra.adjoin A₀ ↑(insert a s), Subalgebra.fg_adjoin_finset _,
        fun x hx => Algebra.subset_adjoin (by simp [hx])⟩,
      Algebra.subset_adjoin (by simp)⟩
  obtain ⟨hc⟩ := SubalgebraStages.nonempty_isLimit_cone S hS f
  obtain ⟨i, W₀, hW₀c, hW₀⟩ :=
    exists_preimage_eq (SubalgebraStages.diagram S f) (SubalgebraStages.cone S f) hc W hW
  refine ⟨(Opposite.unop i).1, (Opposite.unop i).2.1, (Opposite.unop i).2.2, W₀, hW₀c, fun q hq₁ hq₂ => ?_⟩

  have hq : q = SubalgebraStages.leg S f (Opposite.unop i) := by
    apply pullback.hom_ext
    · rw [hq₁, SubalgebraStages.leg_fst]
    · rw [hq₂, SubalgebraStages.leg_snd]
  rw [hq]
  exact hW₀

end S_AlgebraicGeometry_exists_fg_subalgebra_opens_preimage_eq_of_isCompact
end P2MW
export P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_opens_preimage_eq_of_isCompact (solution)
