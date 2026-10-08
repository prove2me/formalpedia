-- Prove2me | Definitions.Def_CK_CKLaneN4_LU_Cover_q01
-- name    : CK_CKLaneN4_LU_Cover_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T10:29:47.049786+00:00
-- url     : https://prove2.me/theorems/48aa8556-1e9a-4615-be8d-5143c766c9ca
-- title:
--   Courtade–Kumar proof module `CKLaneN4.LU.Cover (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.LU.Cover (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.LU.Cover (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.LU.Cover (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/LU/Cover (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneN4_LU_Cover_q00

set_option autoImplicit false
namespace CKLaneN4.LU
theorem col06_good : BoxGood 5534023222112865280 6271892985061248000 0 18446744073709551616 :=
  boxGood_st (m := 9223372036854775808) (U007.good) (boxGood_st (m := 13835058055282163712) (U008.good) (U009.good))

theorem col07_good : BoxGood 6271892985061248000 6825295307272534016 0 18446744073709551616 :=
  boxGood_st (m := 9223372036854775808) (U010.good) (boxGood_st (m := 13835058055282163712) (U011.good) (U012.good))

theorem col08_good : BoxGood 6825295307272534016 7194230188746725376 0 18446744073709551616 :=
  boxGood_st (m := 9223372036854775808) (U013.good) (boxGood_st (m := 13835058055282163712) (U014.good) (U015.good))

theorem col09_good : BoxGood 7194230188746725376 7470931349852368896 0 18446744073709551616 :=
  boxGood_st (m := 9223372036854775808) (U016.good) (boxGood_st (m := 13835058055282163712) (U017.good) (boxGood_st (m := 16140901064495857664) (U018.good) (U019.good)))

theorem col10_good : BoxGood 7470931349852368896 7655398790589463552 0 18446744073709551616 :=
  boxGood_st (m := 9223372036854775808) (U020.good) (boxGood_st (m := 13835058055282163712) (U021.good) (boxGood_st (m := 16140901064495857664) (U022.good) (U023.good)))

theorem col11_good : BoxGood 7655398790589463552 7793749371142285312 0 18446744073709551616 :=
  boxGood_st (m := 9223372036854775808) (U024.good) (boxGood_st (m := 13835058055282163712) (U025.good) (boxGood_st (m := 16140901064495857664) (U026.good) (U027.good)))

theorem col12_good : BoxGood 7793749371142285312 7904429835584542720 0 18446744073709551616 :=
  boxGood_st (m := 9223372036854775808) (U028.good) (boxGood_st (m := 13835058055282163712) (U029.good) (boxGood_st (m := 16140901064495857664) (U030.good) (U031.good)))

end CKLaneN4.LU


