-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_S01_0162
-- name    : CK_CKLaneC_RSC2_S01_0162
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T01:06:11.429453+00:00
-- url     : https://prove2.me/theorems/4ad90f95-c71b-489c-989a-bd8652bd3ef3
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.S01_0162` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.S01_0162` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.S01_0162` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.S01_0162 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/S01_0162.lean)

import Definitions.Def_CK_CKLaneC_RSC2_S01_0162_q01

namespace CKLaneC.RSC2.S01_0162
open CKLaneC.TM3 CKLaneC.RSCell
theorem region : RegionPosI 1688849860263936 1970324836974592 13835058055282163712 18446744073709551616 5764607523034234880 6341068275337658368 :=
  (RegionPosI.split_b 1829587348619264 (RegionPosI.split_s 6052837899185946624 (RegionPosI.split_b 1759218604441600 (RegionPosI.of_check c0 q0 ok_0 1688849860263936 1759218604441600 13835058055282163712 18446744073709551616 5764607523034234880 6052837899185946624 (by decide +kernel)) (RegionPosI.of_check c1 q1 ok_1 1759218604441600 1829587348619264 13835058055282163712 18446744073709551616 5764607523034234880 6052837899185946624 (by decide +kernel))) (RegionPosI.split_b 1759218604441600 (RegionPosI.of_check c2 q2 ok_2 1688849860263936 1759218604441600 13835058055282163712 18446744073709551616 6052837899185946624 6341068275337658368 (by decide +kernel)) (RegionPosI.of_check c3 q3 ok_3 1759218604441600 1829587348619264 13835058055282163712 18446744073709551616 6052837899185946624 6341068275337658368 (by decide +kernel)))) (RegionPosI.split_s 6052837899185946624 (RegionPosI.split_b 1899956092796928 (RegionPosI.of_check c4 q4 ok_4 1829587348619264 1899956092796928 13835058055282163712 18446744073709551616 5764607523034234880 6052837899185946624 (by decide +kernel)) (RegionPosI.of_check c5 q5 ok_5 1899956092796928 1970324836974592 13835058055282163712 18446744073709551616 5764607523034234880 6052837899185946624 (by decide +kernel))) (RegionPosI.split_b 1899956092796928 (RegionPosI.of_check c6 q6 ok_6 1829587348619264 1899956092796928 13835058055282163712 18446744073709551616 6052837899185946624 6341068275337658368 (by decide +kernel)) (RegionPosI.of_check c7 q7 ok_7 1899956092796928 1970324836974592 13835058055282163712 18446744073709551616 6052837899185946624 6341068275337658368 (by decide +kernel)))))

end CKLaneC.RSC2.S01_0162


