-- Prove2me | solution 1 for AlgebraicGeometry.isSeparated_of_isFinite_of_surjective_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/eafe99d0-a94b-571e-b199-58f0f2a8a137

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isSeparated_of_isFinite_of_surjective_of_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y S : Scheme.{0}} (p : X ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (h : p ≫ g = f)
    [IsFinite p] [Surjective p] [IsSeparated f] : IsSeparated g := by

  let q : pullback f f ⟶ pullback g g := pullback.map f f g g p p (𝟙 S) (by simp [h]) (by simp [h])
  haveI : UniversallyClosed q :=
    MorphismProperty.pullbackMap (P := @UniversallyClosed) (inferInstance : UniversallyClosed p) (inferInstance : UniversallyClosed p)
      (by simp [h]) (by simp [h])

  have hsq : pullback.diagonal f ≫ q = p ≫ pullback.diagonal g := by
    apply pullback.hom_ext
    · erw [Category.assoc, Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.diagonal_fst, Category.id_comp,
        pullback.diagonal_fst, Category.comp_id]
    · erw [Category.assoc, Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.diagonal_snd, Category.id_comp,
        pullback.diagonal_snd, Category.comp_id]

  have hcomp : ∀ {A B C : Scheme.{0}} (u : A ⟶ B) (v : B ⟶ C), (⇑(u ≫ v).base : A → C) = ⇑v.base ∘ ⇑u.base := by
    intro A B C u v; ext; simp
  have hrange : Set.range (pullback.diagonal g).base = q.base '' Set.range (pullback.diagonal f).base := by
    have h1 : Set.range (p ≫ pullback.diagonal g).base = Set.range (pullback.diagonal g).base := by
      rw [hcomp]; exact Function.Surjective.range_comp p.surjective _
    rw [← h1, ← hsq, hcomp, Set.range_comp]
  have hclosed : IsClosed (Set.range (pullback.diagonal g).base) := by
    rw [hrange]
    exact q.isClosedMap _ (pullback.diagonal f).isClosedEmbedding.isClosed_range
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hclosed⟩

end S_AlgebraicGeometry_isSeparated_of_isFinite_of_surjective_of_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_isSeparated_of_isFinite_of_surjective_of_comp_eq (solution)
