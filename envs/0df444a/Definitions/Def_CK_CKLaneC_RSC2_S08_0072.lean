-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_S08_0072
-- name    : CK_CKLaneC_RSC2_S08_0072
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T21:12:35.507754+00:00
-- url     : https://prove2.me/theorems/4ae0056b-8de2-425b-9b83-bc53ca05e6a0
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.S08_0072` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.S08_0072` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.S08_0072` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.S08_0072 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/S08_0072.lean)

import Definitions.Def_CK_CKLaneC_RSC2_S08_0072_q00

namespace CKLaneC.RSC2.S08_0072
open CKLaneC.TM3 CKLaneC.RSCell
theorem region : RegionPosI 216172782113783808 288230376151711744 13835058055282163712 18446744073709551616 13835058055282163712 18446744073709551616 :=
  (RegionPosI.split_b 252201579132747776 (RegionPosI.split_s 16140901064495857664 (RegionPosI.split_b 234187180623265792 (RegionPosI.of_check c0 q0 ok_0 216172782113783808 234187180623265792 13835058055282163712 18446744073709551616 13835058055282163712 16140901064495857664 (by decide +kernel)) (RegionPosI.of_check c1 q1 ok_1 234187180623265792 252201579132747776 13835058055282163712 18446744073709551616 13835058055282163712 16140901064495857664 (by decide +kernel))) (RegionPosI.split_b 234187180623265792 (RegionPosI.of_check c2 q2 ok_2 216172782113783808 234187180623265792 13835058055282163712 18446744073709551616 16140901064495857664 18446744073709551616 (by decide +kernel)) (RegionPosI.of_check c3 q3 ok_3 234187180623265792 252201579132747776 13835058055282163712 18446744073709551616 16140901064495857664 18446744073709551616 (by decide +kernel)))) (RegionPosI.split_s 16140901064495857664 (RegionPosI.split_s 14987979559889010688 (RegionPosI.of_check c4 q4 ok_4 252201579132747776 288230376151711744 13835058055282163712 18446744073709551616 13835058055282163712 14987979559889010688 (by decide +kernel)) (RegionPosI.of_check c5 q5 ok_5 252201579132747776 288230376151711744 13835058055282163712 18446744073709551616 14987979559889010688 16140901064495857664 (by decide +kernel))) (RegionPosI.split_b 270215977642229760 (RegionPosI.of_check c6 q6 ok_6 252201579132747776 270215977642229760 13835058055282163712 18446744073709551616 16140901064495857664 18446744073709551616 (by decide +kernel)) (RegionPosI.of_check c7 q7 ok_7 270215977642229760 288230376151711744 13835058055282163712 18446744073709551616 16140901064495857664 18446744073709551616 (by decide +kernel)))))

end CKLaneC.RSC2.S08_0072


