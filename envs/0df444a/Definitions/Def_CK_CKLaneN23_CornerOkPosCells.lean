-- Prove2me | Definitions.Def_CK_CKLaneN23_CornerOkPosCells
-- name    : CK_CKLaneN23_CornerOkPosCells
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-12T13:43:38.634981+00:00
-- url     : https://prove2.me/theorems/3b057a60-b869-4084-a923-adb307f0435d
-- title:
--   Courtade–Kumar proof module `CKLaneN23.CornerOkPosCells` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.CornerOkPosCells` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.CornerOkPosCells` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.CornerOkPosCells (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/CornerOkPosCells.lean)

import Definitions.Def_CK_CKLaneN23_PosCell_C0_0
import Definitions.Def_CK_CKLaneN23_PosCell_C0_1
import Definitions.Def_CK_CKLaneN23_PosCell_C0_2
import Definitions.Def_CK_CKLaneN23_PosCell_C0_3
import Definitions.Def_CK_CKLaneN23_PosCell_C0_4
import Definitions.Def_CK_CKLaneN23_PosCell_C0_5
import Definitions.Def_CK_CKLaneN23_PosCell_C0_6
import Definitions.Def_CK_CKLaneN23_PosCell_C0_7
import Definitions.Def_CK_CKLaneN23_PosCell_C0_8
import Definitions.Def_CK_CKLaneN23_PosCell_C0_9
import Definitions.Def_CK_CKLaneN23_PosCell_C0_10
import Definitions.Def_CK_CKLaneN23_PosCell_C0_11
import Definitions.Def_CK_CKLaneN23_PosCell_C0_12
import Definitions.Def_CK_CKLaneN23_PosCell_C0_13
import Definitions.Def_CK_CKLaneN23_PosCell_C0_14
import Definitions.Def_CK_CKLaneN23_PosCell_C0_15
import Definitions.Def_CK_CKLaneN23_PosCell_C1_0
import Definitions.Def_CK_CKLaneN23_PosCell_C1_1
import Definitions.Def_CK_CKLaneN23_PosCell_C1_2
import Definitions.Def_CK_CKLaneN23_PosCell_C1_3
import Definitions.Def_CK_CKLaneN23_PosCell_C1_4
import Definitions.Def_CK_CKLaneN23_PosCell_C1_5
import Definitions.Def_CK_CKLaneN23_PosCell_C1_6
import Definitions.Def_CK_CKLaneN23_PosCell_C1_7
import Definitions.Def_CK_CKLaneN23_PosCell_C1_8
import Definitions.Def_CK_CKLaneN23_PosCell_C1_9
import Definitions.Def_CK_CKLaneN23_PosCell_C1_10
import Definitions.Def_CK_CKLaneN23_PosCell_C1_11
import Definitions.Def_CK_CKLaneN23_PosCell_C1_12
import Definitions.Def_CK_CKLaneN23_PosCell_C1_13
import Definitions.Def_CK_CKLaneN23_PosCell_C1_14
import Definitions.Def_CK_CKLaneN23_PosCell_C1_15
import Definitions.Def_CK_CKLaneN23_PosCell_C2_0
import Definitions.Def_CK_CKLaneN23_PosCell_C2_1
import Definitions.Def_CK_CKLaneN23_PosCell_C2_2
import Definitions.Def_CK_CKLaneN23_PosCell_C2_3
import Definitions.Def_CK_CKLaneN23_PosCell_C2_4
import Definitions.Def_CK_CKLaneN23_PosCell_C2_5
import Definitions.Def_CK_CKLaneN23_PosCell_C2_6
import Definitions.Def_CK_CKLaneN23_PosCell_C2_7
import Definitions.Def_CK_CKLaneN23_PosCell_C2_8
import Definitions.Def_CK_CKLaneN23_PosCell_C2_9
import Definitions.Def_CK_CKLaneN23_PosCell_C2_10
import Definitions.Def_CK_CKLaneN23_PosCell_C2_11
import Definitions.Def_CK_CKLaneN23_PosCell_C2_12
import Definitions.Def_CK_CKLaneN23_PosCell_C2_13
import Definitions.Def_CK_CKLaneN23_PosCell_C2_14
import Definitions.Def_CK_CKLaneN23_PosCell_C2_15
import Definitions.Def_CK_CKLaneN23_PosCell_C3_0
import Definitions.Def_CK_CKLaneN23_PosCell_C3_1
import Definitions.Def_CK_CKLaneN23_PosCell_C3_2
import Definitions.Def_CK_CKLaneN23_PosCell_C3_3
import Definitions.Def_CK_CKLaneN23_PosCell_C3_4
import Definitions.Def_CK_CKLaneN23_PosCell_C3_5
import Definitions.Def_CK_CKLaneN23_PosCell_C3_6
import Definitions.Def_CK_CKLaneN23_PosCell_C3_7
import Definitions.Def_CK_CKLaneN23_PosCell_C3_8
import Definitions.Def_CK_CKLaneN23_PosCell_C3_9
import Definitions.Def_CK_CKLaneN23_PosCell_C3_10
import Definitions.Def_CK_CKLaneN23_PosCell_C3_11
import Definitions.Def_CK_CKLaneN23_PosCell_C3_12
import Definitions.Def_CK_CKLaneN23_PosCell_C3_13
import Definitions.Def_CK_CKLaneN23_PosCell_C3_14
import Definitions.Def_CK_CKLaneN23_PosCell_C3_15
import Definitions.Def_CK_CKLaneN23_PosCell_C4_0
import Definitions.Def_CK_CKLaneN23_PosCell_C4_1
import Definitions.Def_CK_CKLaneN23_PosCell_C4_2
import Definitions.Def_CK_CKLaneN23_PosCell_C4_3
import Definitions.Def_CK_CKLaneN23_PosCell_C4_4
import Definitions.Def_CK_CKLaneN23_PosCell_C4_5
import Definitions.Def_CK_CKLaneN23_PosCell_C4_6
import Definitions.Def_CK_CKLaneN23_PosCell_C4_7
import Definitions.Def_CK_CKLaneN23_PosCell_C4_8
import Definitions.Def_CK_CKLaneN23_PosCell_C4_9
import Definitions.Def_CK_CKLaneN23_PosCell_C4_10
import Definitions.Def_CK_CKLaneN23_PosCell_C4_11
import Definitions.Def_CK_CKLaneN23_PosCell_C4_12
import Definitions.Def_CK_CKLaneN23_PosCell_C4_13
import Definitions.Def_CK_CKLaneN23_PosCell_C4_14
import Definitions.Def_CK_CKLaneN23_PosCell_C4_15
import Definitions.Def_CK_CKLaneN23_PosCell_C5_0
import Definitions.Def_CK_CKLaneN23_PosCell_C5_1
import Definitions.Def_CK_CKLaneN23_PosCell_C5_2
import Definitions.Def_CK_CKLaneN23_PosCell_C5_3
import Definitions.Def_CK_CKLaneN23_PosCell_C5_4
import Definitions.Def_CK_CKLaneN23_PosCell_C5_5
import Definitions.Def_CK_CKLaneN23_PosCell_C5_6
import Definitions.Def_CK_CKLaneN23_PosCell_C5_7
import Definitions.Def_CK_CKLaneN23_PosCell_C5_8
import Definitions.Def_CK_CKLaneN23_PosCell_C5_9
import Definitions.Def_CK_CKLaneN23_PosCell_C5_10
import Definitions.Def_CK_CKLaneN23_PosCell_C5_11
import Definitions.Def_CK_CKLaneN23_PosCell_C5_12
import Definitions.Def_CK_CKLaneN23_PosCell_C5_13
import Definitions.Def_CK_CKLaneN23_PosCell_C5_14
import Definitions.Def_CK_CKLaneN23_PosCell_C5_15
import Definitions.Def_CK_CKLaneN23_PosCell_C6_0
import Definitions.Def_CK_CKLaneN23_PosCell_C6_1
import Definitions.Def_CK_CKLaneN23_PosCell_C6_2
import Definitions.Def_CK_CKLaneN23_PosCell_C6_3
import Definitions.Def_CK_CKLaneN23_PosCell_C6_4
import Definitions.Def_CK_CKLaneN23_PosCell_C6_5
import Definitions.Def_CK_CKLaneN23_PosCell_C6_6
import Definitions.Def_CK_CKLaneN23_PosCell_C6_7
import Definitions.Def_CK_CKLaneN23_PosCell_C6_8
import Definitions.Def_CK_CKLaneN23_PosCell_C6_9
import Definitions.Def_CK_CKLaneN23_PosCell_C6_10
import Definitions.Def_CK_CKLaneN23_PosCell_C6_11
import Definitions.Def_CK_CKLaneN23_PosCell_C6_12
import Definitions.Def_CK_CKLaneN23_PosCell_C6_13
import Definitions.Def_CK_CKLaneN23_PosCell_C6_14
import Definitions.Def_CK_CKLaneN23_PosCell_C6_15
import Definitions.Def_CK_CKLaneN23_PosCell_C7_0
import Definitions.Def_CK_CKLaneN23_PosCell_C7_1
import Definitions.Def_CK_CKLaneN23_PosCell_C7_2
import Definitions.Def_CK_CKLaneN23_PosCell_C7_3
import Definitions.Def_CK_CKLaneN23_PosCell_C7_4
import Definitions.Def_CK_CKLaneN23_PosCell_C7_5
import Definitions.Def_CK_CKLaneN23_PosCell_C7_6
import Definitions.Def_CK_CKLaneN23_PosCell_C7_7
import Definitions.Def_CK_CKLaneN23_PosCell_C7_8
import Definitions.Def_CK_CKLaneN23_PosCell_C7_9
import Definitions.Def_CK_CKLaneN23_PosCell_C7_10
import Definitions.Def_CK_CKLaneN23_PosCell_C7_11
import Definitions.Def_CK_CKLaneN23_PosCell_C7_12
import Definitions.Def_CK_CKLaneN23_PosCell_C7_13
import Definitions.Def_CK_CKLaneN23_PosCell_C7_14
import Definitions.Def_CK_CKLaneN23_PosCell_C7_15

-- ===== source module CKLaneN23.CornerOkPosCells =====
section

/-!
# CKLaneN23.CornerOkPosCells — the corner positivity check `posCheckC = true` from its 128 cells

Each `cell_j_k : boxCell j k = true` is an independent `decide +kernel` evaluation (module
`CKLaneN23.PosCell.C<j>_<k>`); `posRow_of_cells` / `posCheckC_of_rows` (CKLaneN23.CPosSplit) are
Boolean bookkeeping only.  (Lane N23b)
-/

namespace CKLaneN23.CT

theorem pos_ok : posCheckC = true :=
  posCheckC_of_rows (forall_lt_8 (P := fun j => posRow j = true)
    (posRow_of_cells 0 (forall_lt_16 (P := fun k => boxCell 0 k = true)
      cell_0_0 cell_0_1 cell_0_2 cell_0_3 cell_0_4 cell_0_5 cell_0_6 cell_0_7 cell_0_8 cell_0_9 cell_0_10 cell_0_11 cell_0_12 cell_0_13 cell_0_14 cell_0_15))
    (posRow_of_cells 1 (forall_lt_16 (P := fun k => boxCell 1 k = true)
      cell_1_0 cell_1_1 cell_1_2 cell_1_3 cell_1_4 cell_1_5 cell_1_6 cell_1_7 cell_1_8 cell_1_9 cell_1_10 cell_1_11 cell_1_12 cell_1_13 cell_1_14 cell_1_15))
    (posRow_of_cells 2 (forall_lt_16 (P := fun k => boxCell 2 k = true)
      cell_2_0 cell_2_1 cell_2_2 cell_2_3 cell_2_4 cell_2_5 cell_2_6 cell_2_7 cell_2_8 cell_2_9 cell_2_10 cell_2_11 cell_2_12 cell_2_13 cell_2_14 cell_2_15))
    (posRow_of_cells 3 (forall_lt_16 (P := fun k => boxCell 3 k = true)
      cell_3_0 cell_3_1 cell_3_2 cell_3_3 cell_3_4 cell_3_5 cell_3_6 cell_3_7 cell_3_8 cell_3_9 cell_3_10 cell_3_11 cell_3_12 cell_3_13 cell_3_14 cell_3_15))
    (posRow_of_cells 4 (forall_lt_16 (P := fun k => boxCell 4 k = true)
      cell_4_0 cell_4_1 cell_4_2 cell_4_3 cell_4_4 cell_4_5 cell_4_6 cell_4_7 cell_4_8 cell_4_9 cell_4_10 cell_4_11 cell_4_12 cell_4_13 cell_4_14 cell_4_15))
    (posRow_of_cells 5 (forall_lt_16 (P := fun k => boxCell 5 k = true)
      cell_5_0 cell_5_1 cell_5_2 cell_5_3 cell_5_4 cell_5_5 cell_5_6 cell_5_7 cell_5_8 cell_5_9 cell_5_10 cell_5_11 cell_5_12 cell_5_13 cell_5_14 cell_5_15))
    (posRow_of_cells 6 (forall_lt_16 (P := fun k => boxCell 6 k = true)
      cell_6_0 cell_6_1 cell_6_2 cell_6_3 cell_6_4 cell_6_5 cell_6_6 cell_6_7 cell_6_8 cell_6_9 cell_6_10 cell_6_11 cell_6_12 cell_6_13 cell_6_14 cell_6_15))
    (posRow_of_cells 7 (forall_lt_16 (P := fun k => boxCell 7 k = true)
      cell_7_0 cell_7_1 cell_7_2 cell_7_3 cell_7_4 cell_7_5 cell_7_6 cell_7_7 cell_7_8 cell_7_9 cell_7_10 cell_7_11 cell_7_12 cell_7_13 cell_7_14 cell_7_15)))

end CKLaneN23.CT

end


