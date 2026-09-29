-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.OrderedAffineCover.nonempty_of_compactSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/b2476edd-1508-5df0-b42a-3c17ac429409

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_nonempty_of_compactSpace

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

theorem solution (V : Scheme.{u}) [CompactSpace V] : Nonempty V.OrderedAffineCover := by

  have hcov_all : (Set.univ : Set V) ⊆ ⋃ W : V.affineOpens, (W.1 : Set V) := fun x _ => by
    obtain ⟨W, hWaff, hxW, -⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp V.isBasis_affineOpens
        (show x ∈ (⊤ : V.Opens) from trivial)
    exact Set.mem_iUnion.mpr ⟨⟨W, hWaff⟩, hxW⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun W : V.affineOpens => (W.1 : Set V))
    (fun W => W.1.2) hcov_all

  letI _lo : LinearOrder V.affineOpens := IsWellOrder.linearOrder WellOrderingRel
  refine ⟨{ ι := S, U := fun i => i.1.1, isAffineOpen := fun i => i.1.2, iSup_eq_top := ?_ }⟩
  refine le_antisymm le_top (fun x _ => ?_)
  rcases Set.mem_iUnion₂.mp (hS (Set.mem_univ x)) with ⟨W, hWS, hxW⟩
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hWS⟩, hxW⟩

end S_AlgebraicGeometry_Scheme_OrderedAffineCover_nonempty_of_compactSpace
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_nonempty_of_compactSpace (solution)
