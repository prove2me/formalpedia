-- Prove2me | Definitions.Def_CK_CKLaneN1_DiagBand
-- name    : CK_CKLaneN1_DiagBand
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T05:03:23.782035+00:00
-- url     : https://prove2.me/theorems/ddc739fd-8fdc-4c5b-bf16-3072ce0dab6b
-- title:
--   Courtade–Kumar proof module `CKLaneN1.DiagBand` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.DiagBand` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.DiagBand` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.DiagBand (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/DiagBand.lean)

import Definitions.Def_CK_CKLaneN1_DBShard_D00
import Definitions.Def_CK_CKLaneN1_DBShard_D01
import Definitions.Def_CK_CKLaneN1_DBShard_D02
import Definitions.Def_CK_CKLaneN1_DBShard_D03
import Definitions.Def_CK_CKLaneN1_DBShard_D04
import Definitions.Def_CK_CKLaneN1_DBShard_D05
import Definitions.Def_CK_CKLaneN1_DBShard_D06
import Definitions.Def_CK_CKLaneN1_DBShard_D07
import Definitions.Def_CK_CKLaneN1_DBShard_D08
import Definitions.Def_CK_CKLaneN1_DBRow
import Definitions.Def_CK_CKLaneN1_Chunks

-- ===== source module CKLaneN1.DiagBand =====
section

/-!
# Lane N1: NO_SEP §6 cover and the row `NoSepA_ModerateRest` (N23 row 4)

All 325 archived DIAGONAL_BAND leaves pass the kernel check (`dbTree_ok`). The 153 endpoint and
140 log-sum leaves are certified. The 32 prior-cap leaves are certified vacuous in this row
(`I⁺ ≤ 3/40` contradicts `s > 3/40`).
-/

namespace CKLaneN1

theorem dbTree_length : dbTree.leaves.length = 325 := by decide +kernel

/-- Every archived NO_SEP §6 leaf passes the kernel check. -/
theorem dbTree_ok : dbTree.allLeaves dbLeafOK = true := by
  unfold PT.allLeaves
  apply all_of_chunks (fun q => dbLeafOK q.1 q.2) 40 9 dbTree.leaves (by rw [dbTree_length]; decide)
  intro k hk
  interval_cases k
  · exact DBShard.D00
  · exact DBShard.D01
  · exact DBShard.D02
  · exact DBShard.D03
  · exact DBShard.D04
  · exact DBShard.D05
  · exact DBShard.D06
  · exact DBShard.D07
  · exact DBShard.D08

/-- Row 4 (N23): NO_SEP §6 outside the prior-cap leaves. -/
theorem row_noSepA_moderateRest : NoSepA_ModerateRest :=
  noSepA_moderateRest_of_tree dbTree_ok

end CKLaneN1

end


