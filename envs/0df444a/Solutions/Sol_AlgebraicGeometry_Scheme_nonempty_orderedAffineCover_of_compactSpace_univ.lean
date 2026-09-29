-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nonempty_orderedAffineCover_of_compactSpace_univ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/7824bab9-36f8-5a03-811a-baa840569c26

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_compactSpace_univ

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem solution
    (X : Scheme.{u}) [CompactSpace X] : Nonempty X.OrderedAffineCover := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) (by
      intro x _
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hxU⟩)
  letI : LinearOrder ↥t := LinearOrder.lift' (Fintype.equivFin ↥t) (Fintype.equivFin ↥t).injective
  refine ⟨{ ι := ↥t, U := fun i => i.1.1, isAffineOpen := fun i => i.1.2, iSup_eq_top := ?_ }⟩
  refine eq_top_iff.2 fun x _ => ?_
  have hx := ht (Set.mem_univ x)
  simp only [Set.mem_iUnion, exists_prop] at hx
  obtain ⟨U, hUt, hxU⟩ := hx
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hUt⟩, hxU⟩

end S_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_compactSpace_univ
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_compactSpace_univ (solution)
