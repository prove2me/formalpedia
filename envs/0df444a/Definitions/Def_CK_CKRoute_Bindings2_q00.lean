-- Prove2me | Definitions.Def_CK_CKRoute_Bindings2_q00
-- name    : CK_CKRoute_Bindings2_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T20:16:39.40998+00:00
-- url     : https://prove2.me/theorems/6de96ead-4f30-438d-b0fb-32d50c16f08d
-- title:
--   Courtade–Kumar proof module `CKRoute.Bindings2 (piece 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKRoute.Bindings2 (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKRoute.Bindings2 (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKRoute.Bindings2 (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKRoute/Bindings2 (piece 1 of 4).lean)

import Definitions.Def_CK_CKRoute_Bindings
import Definitions.Def_CK_CKLaneG3_OUnion_U_none
import Definitions.Def_CK_CKLaneN4_OLeaves
import Definitions.Def_CK_CKLaneM09_Leaves
import Definitions.Def_CK_CKLaneG3_M11_Top
import Definitions.Def_CK_CKLaneG3_M04_Top



/-!
# (O) row: closed per-label families of the archived outer-opposite partition

Labels of `CKLaneD.ArchTree.archTree` (29,495 leaves):
0 endpoint_plane_taylor (open, Lane D fleet), 1 shifted_logsum (open, Lane M2b fleet),
2 global_cap_slope (Lane M09), 3 global_feasible_split (open, Lane M10 fleet),
4 global_eight_ratio, 7 global_parent8, 8 global_low_entropy_025, 9 global_parent16,
10 global_parent_direct (Lane N4), 5 outside, 12 global_corner (Lane D),
6 global_parent_envelope (Lane M11, aggregated by G3), 11 logsum_direct (Lane M04, aggregated by G3).
-/

namespace CKRoute

open GeneralCK

/-- The (O) row from the three still-open label families (0, 1, 3). -/
theorem opCompact_of_labels013
    (h0 : ∀ q ∈ CKLaneD.ArchTree.archTree.leaves, q.2 = 0 →
      CKLaneD.OCompact.OLeafOK (CKLaneD.uvtBox q.1))
    (h1 : ∀ q ∈ CKLaneD.ArchTree.archTree.leaves, q.2 = 1 →
      CKLaneD.OCompact.OLeafOK (CKLaneD.uvtBox q.1))
    (h3 : ∀ q ∈ CKLaneD.ArchTree.archTree.leaves, q.2 = 3 →
      CKLaneD.OCompact.OLeafOK (CKLaneD.uvtBox q.1)) :
    OP_Compact :=
  opCompact_iff_laneD.mpr
    (CKLaneG3.OUnion.U_none.opCompact_of_remaining_labels h0 h1
      (fun q hq hl => CKLaneD.OCompact.oLeafOK_of_semUVT _
        (CKLaneM09.Leaves.cap_slope_leaves q hq hl))
      h3
      CKLaneN4.OLeaves.family_label4
      CKLaneD.Structural.outside_oLeafOK
      CKLaneG3.M11.Top.label_oleaf
      CKLaneN4.OLeaves.family_label7
      CKLaneN4.OLeaves.family_label8
      CKLaneN4.OLeaves.family_label9
      CKLaneN4.OLeaves.family_label10
      CKLaneG3.M04.Top.label_oleaf
      CKLaneD.Structural.corner_oLeafOK)

end CKRoute


