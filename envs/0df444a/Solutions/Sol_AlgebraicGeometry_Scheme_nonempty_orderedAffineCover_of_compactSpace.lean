-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nonempty_orderedAffineCover_of_compactSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/127d0d70-e37b-5695-bbd4-bc05644a6f63

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_compactSpace

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem solution
    (X : Scheme.{0}) [CompactSpace X] : Nonempty X.OrderedAffineCover := by
  classical

  have h : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := fun x => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨U, hU, hxU⟩
  choose U hU hxU using h

  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set X))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxU x⟩)
  refine ⟨{ ι := Fin t.card
            U := fun i => U (t.equivFin.symm i).1
            isAffineOpen := fun i => hU _
            iSup_eq_top := ?_ }⟩
  refine top_le_iff.mp (fun x _ => ?_)
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ t, x ∈ (U y : Set X) := by
    simpa only [Set.mem_iUnion, exists_prop] using ht (Set.mem_univ x)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨t.equivFin ⟨y, hy⟩, by simpa using hxy⟩

end S_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_compactSpace
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_compactSpace (solution)
