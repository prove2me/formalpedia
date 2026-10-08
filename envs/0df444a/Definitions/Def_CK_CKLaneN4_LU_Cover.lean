-- Prove2me | Definitions.Def_CK_CKLaneN4_LU_Cover
-- name    : CK_CKLaneN4_LU_Cover
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T12:58:06.173085+00:00
-- url     : https://prove2.me/theorems/842be516-319d-4852-bcbf-9c248110a5fe
-- title:
--   Courtade–Kumar proof module `CKLaneN4.LU.Cover` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.LU.Cover` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.LU.Cover` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.LU.Cover (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/LU/Cover.lean)

import Definitions.Def_CK_CKLaneN4_LU_Cover_q02

set_option autoImplicit false
namespace CKLaneN4.LU
theorem root_good : BoxGood 0 ATOP 0 18446744073709551616 :=
  boxGood_sa (m := 288230376151711744) col00_good (boxGood_sa (m := 1152921504606846976) col01_good (boxGood_sa (m := 2305843009213693952) col02_good (boxGood_sa (m := 3458764513820540928) col03_good (boxGood_sa (m := 4611686018427387904) col04_good (boxGood_sa (m := 5534023222112865280) col05_good (boxGood_sa (m := 6271892985061248000) col06_good (boxGood_sa (m := 6825295307272534016) col07_good (boxGood_sa (m := 7194230188746725376) col08_good (boxGood_sa (m := 7470931349852368896) col09_good (boxGood_sa (m := 7655398790589463552) col10_good (boxGood_sa (m := 7793749371142285312) col11_good (boxGood_sa (m := 7904429835584542720) col12_good (boxGood_sa (m := 8005886927989945344) col13_good (boxGood_sa (m := 8098120648358493184) col14_good (boxGood_sa (m := 8171907624653331456) col15_good (boxGood_sa (m := 8236471228911314944) col16_good (boxGood_sa (m := 8291811461132443648) col17_good (boxGood_sa (m := 8337928321316717568) col18_good (col19_good)))))))))))))))))))

end CKLaneN4.LU


