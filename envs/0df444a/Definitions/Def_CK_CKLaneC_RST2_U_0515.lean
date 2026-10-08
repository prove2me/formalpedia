-- Prove2me | Definitions.Def_CK_CKLaneC_RST2_U_0515
-- name    : CK_CKLaneC_RST2_U_0515
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T20:06:04.060421+00:00
-- url     : https://prove2.me/theorems/16b8ce80-11d4-44e3-aaf8-0b3016258405
-- title:
--   Courtade–Kumar proof module `CKLaneC.RST2.U_0515` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RST2.U_0515` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RST2.U_0515` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RST2.U_0515 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RST2/U_0515.lean)

import Definitions.Def_CK_CKLaneC_RST2_U_0515_q02

namespace CKLaneC.RST2.U_0515
open CKLaneR2.TM3 CKLaneR2.Cell CKLaneR2.Tail CKLaneC.RSTail
theorem region : TailPosI 8646911284551352320 9223372036854775808 6917529027641081856 9223372036854775808 1152921504606846976 2305843009213693952 :=
  (TailPosI.split_s 1630303065108119552 (TailPosI.split_s 1369094286720630784 leaf_0 leaf_1) (TailPosI.split_s 1941051439396683776 leaf_2 leaf_3))

end CKLaneC.RST2.U_0515


