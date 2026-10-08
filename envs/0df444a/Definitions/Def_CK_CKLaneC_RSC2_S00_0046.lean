-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_S00_0046
-- name    : CK_CKLaneC_RSC2_S00_0046
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T23:24:42.857986+00:00
-- url     : https://prove2.me/theorems/1eeb8191-634c-4c60-817d-3b413c0db189
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.S00_0046` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.S00_0046` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.S00_0046` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.S00_0046 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/S00_0046.lean)

import Definitions.Def_CK_CKLaneC_RSC2_S00_0046_q01

namespace CKLaneC.RSC2.S00_0046
open CKLaneC.TM3 CKLaneC.RSCell
theorem region : RegionPosI 844424930131968 914793674309632 13835058055282163712 18446744073709551616 4035225266123964416 4611686018427387904 :=
  (RegionPosI.split_s 4323455642275676160 (RegionPosI.split_b 879609302220800 (RegionPosI.split_s 4179340454199820288 (RegionPosI.of_check c0 q0 ok_0 844424930131968 879609302220800 13835058055282163712 18446744073709551616 4035225266123964416 4179340454199820288 (by decide +kernel)) (RegionPosI.of_check c1 q1 ok_1 844424930131968 879609302220800 13835058055282163712 18446744073709551616 4179340454199820288 4323455642275676160 (by decide +kernel))) (RegionPosI.split_s 4179340454199820288 (RegionPosI.of_check c2 q2 ok_2 879609302220800 914793674309632 13835058055282163712 18446744073709551616 4035225266123964416 4179340454199820288 (by decide +kernel)) (RegionPosI.of_check c3 q3 ok_3 879609302220800 914793674309632 13835058055282163712 18446744073709551616 4179340454199820288 4323455642275676160 (by decide +kernel)))) (RegionPosI.split_b 879609302220800 (RegionPosI.split_s 4467570830351532032 (RegionPosI.of_check c4 q4 ok_4 844424930131968 879609302220800 13835058055282163712 18446744073709551616 4323455642275676160 4467570830351532032 (by decide +kernel)) (RegionPosI.of_check c5 q5 ok_5 844424930131968 879609302220800 13835058055282163712 18446744073709551616 4467570830351532032 4611686018427387904 (by decide +kernel))) (RegionPosI.split_s 4467570830351532032 (RegionPosI.of_check c6 q6 ok_6 879609302220800 914793674309632 13835058055282163712 18446744073709551616 4323455642275676160 4467570830351532032 (by decide +kernel)) (RegionPosI.of_check c7 q7 ok_7 879609302220800 914793674309632 13835058055282163712 18446744073709551616 4467570830351532032 4611686018427387904 (by decide +kernel)))))

end CKLaneC.RSC2.S00_0046


