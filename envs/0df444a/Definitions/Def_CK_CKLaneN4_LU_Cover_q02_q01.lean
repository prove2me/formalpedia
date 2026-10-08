-- Prove2me | Definitions.Def_CK_CKLaneN4_LU_Cover_q02_q01
-- name    : CK_CKLaneN4_LU_Cover_q02_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T11:49:23.30493+00:00
-- url     : https://prove2.me/theorems/d54ba134-8704-48f7-9500-c264fe737bde
-- title:
--   Courtade–Kumar proof module `CKLaneN4.LU.Cover (piece 3 of 4) (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.LU.Cover (piece 3 of 4) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.LU.Cover (piece 3 of 4) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.LU.Cover (piece 3 of 4) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/LU/Cover (piece 3 of 4) (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneN4_LU_Cover_q02_q00

set_option autoImplicit false
namespace CKLaneN4.LU
theorem col15_good : BoxGood 8098120648358493184 8171907624653331456 0 18446744073709551616 :=
  boxGood_st (m := 9223372036854775808) (boxGood_st (m := 4611686018427387904) (U042.good) (U043.good)) (boxGood_st (m := 13835058055282163712) (U044.good) (boxGood_st (m := 16140901064495857664) (U045.good) (U046.good)))

theorem col16_good : BoxGood 8171907624653331456 8236471228911314944 0 18446744073709551616 :=
  boxGood_st (m := 9223372036854775808) (boxGood_st (m := 4611686018427387904) (U047.good) (U048.good)) (boxGood_st (m := 13835058055282163712) (U049.good) (boxGood_st (m := 16140901064495857664) (U050.good) (U051.good)))

end CKLaneN4.LU


