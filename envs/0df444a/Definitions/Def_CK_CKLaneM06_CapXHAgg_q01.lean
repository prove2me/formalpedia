-- Prove2me | Definitions.Def_CK_CKLaneM06_CapXHAgg_q01
-- name    : CK_CKLaneM06_CapXHAgg_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T22:40:11.088114+00:00
-- url     : https://prove2.me/theorems/f6d23dde-94ee-4963-92cf-73455a0f3485
-- title:
--   Courtade–Kumar proof module `CKLaneM06.CapXHAgg (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM06.CapXHAgg (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM06.CapXHAgg (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM06.CapXHAgg (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM06/CapXHAgg (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneM06_CapXHAgg_q00

set_option autoImplicit false
namespace CKLaneM06.Cap.CapXHAgg
open GeneralCK CKLaneM06.Cap
theorem n_030302020 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 0, 2, 0, 2, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 0, 2, 0, 2, 0]) (ax := 1) (by decide) CapXHB.B019.cap_3 CapXHB.B019.cap_4

theorem n_030302021 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 0, 2, 0, 2, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 0, 2, 0, 2, 1]) (ax := 1) (by decide) CapXHB.B019.cap_5 CapXHB.B020.cap_0

theorem n_030302030 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 0, 2, 0, 3, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 0, 2, 0, 3, 0]) (ax := 1) (by decide) CapXHB.B020.cap_1 CapXHB.B020.cap_2

theorem n_030302031 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 0, 2, 0, 3, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 0, 2, 0, 3, 1]) (ax := 1) (by decide) CapXHB.B020.cap_3 CapXHB.B020.cap_4

theorem n_030302120 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 0, 2, 1, 2, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 0, 2, 1, 2, 0]) (ax := 1) (by decide) CapXHB.B020.cap_5 CapXHB.B021.cap_0

theorem n_030302130 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 0, 2, 1, 3, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 0, 2, 1, 3, 0]) (ax := 1) (by decide) CapXHB.B021.cap_2 CapXHB.B021.cap_3

theorem n_030303020 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 0, 3, 0, 2, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 0, 3, 0, 2, 0]) (ax := 1) (by decide) CapXHB.B021.cap_5 CapXHB.B022.cap_0

theorem n_030303021 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 0, 3, 0, 2, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 0, 3, 0, 2, 1]) (ax := 1) (by decide) CapXHB.B022.cap_1 CapXHB.B022.cap_2

theorem n_030303030 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 0, 3, 0, 3, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 0, 3, 0, 3, 0]) (ax := 1) (by decide) CapXHB.B022.cap_3 CapXHB.B022.cap_4

theorem n_02121202 : CapOn (cpathBox xhRoot [0, 2, 1, 2, 1, 2, 0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 1, 2, 1, 2, 0, 2]) (ax := 0) (by decide) CapXHB.B012.cap_0 CapXHB.B012.cap_1

theorem n_02021213 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 1, 2, 1, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 1, 2, 1, 3]) (ax := 0) (by decide) CapXHB.B006.cap_4 CapXHB.B007.cap_0

theorem n_02020212 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 2, 1, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 2, 1, 2]) (ax := 0) (by decide) n_020202120 n_020202121

theorem n_02020213 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 2, 1, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 2, 1, 3]) (ax := 0) (by decide) n_020202130 n_020202131

theorem n_02021203 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 1, 2, 0, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 1, 2, 0, 3]) (ax := 0) (by decide) n_020212030 CapXHB.B005.cap_0

theorem n_02021212 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 1, 2, 1, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 1, 2, 1, 2]) (ax := 0) (by decide) n_020212120 n_020212121

theorem n_02021303 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 1, 3, 0, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 1, 3, 0, 3]) (ax := 0) (by decide) CapXHB.B007.cap_3 CapXHB.B007.cap_4

theorem n_02020202 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 2, 0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 2, 0, 2]) (ax := 0) (by decide) n_020202020 n_020202021

theorem n_02020302 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 3, 0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 3, 0, 2]) (ax := 0) (by decide) CapXH.C030.cap n_020203021

theorem n_02020312 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 3, 1, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 3, 1, 2]) (ax := 0) (by decide) n_020203120 n_020203121

theorem n_02020203 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 2, 0, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 2, 0, 3]) (ax := 0) (by decide) n_020202030 n_020202031

theorem n_02020303 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 3, 0, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 3, 0, 3]) (ax := 0) (by decide) CapXHB.B000.cap_1 n_020203031

theorem n_02120202 : CapOn (cpathBox xhRoot [0, 2, 1, 2, 0, 2, 0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 1, 2, 0, 2, 0, 2]) (ax := 0) (by decide) n_021202020 n_021202021

theorem n_02121212 : CapOn (cpathBox xhRoot [0, 2, 1, 2, 1, 2, 1, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 1, 2, 1, 2, 1, 2]) (ax := 0) (by decide) CapXHB.B012.cap_3 CapXHB.B012.cap_4

theorem n_12020202 : CapOn (cpathBox xhRoot [1, 2, 0, 2, 0, 2, 0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [1, 2, 0, 2, 0, 2, 0, 2]) (ax := 0) (by decide) CapXHB.B024.cap_1 CapXHB.B024.cap_2

theorem n_02020313 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 3, 1, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 3, 1, 3]) (ax := 0) (by decide) n_020203130 n_020203131

theorem n_02021302 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 1, 3, 0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 1, 3, 0, 2]) (ax := 0) (by decide) CapXHB.B007.cap_1 CapXHB.B007.cap_2

theorem n_02120212 : CapOn (cpathBox xhRoot [0, 2, 1, 2, 0, 2, 1, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 1, 2, 0, 2, 1, 2]) (ax := 0) (by decide) n_021202120 n_021202121

theorem n_02021202 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 1, 2, 0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 1, 2, 0, 2]) (ax := 0) (by decide) n_020212020 n_020212021

theorem n_02030302 : CapOn (cpathBox xhRoot [0, 2, 0, 3, 0, 3, 0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 3, 0, 3, 0, 2]) (ax := 0) (by decide) CapXHB.B008.cap_3 CapXHB.B008.cap_4

theorem n_02030303 : CapOn (cpathBox xhRoot [0, 2, 0, 3, 0, 3, 0, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 3, 0, 3, 0, 3]) (ax := 0) (by decide) CapXHB.B008.cap_5 CapXHB.B009.cap_0

theorem n_02030313 : CapOn (cpathBox xhRoot [0, 2, 0, 3, 0, 3, 1, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 3, 0, 3, 1, 3]) (ax := 0) (by decide) CapXHB.B009.cap_2 CapXHB.B009.cap_3

theorem n_03020202 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 0, 2, 0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 0, 2, 0, 2]) (ax := 0) (by decide) CapXHB.B013.cap_2 CapXHB.B013.cap_3

theorem n_03020203 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 0, 2, 0, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 0, 2, 0, 3]) (ax := 0) (by decide) CapXHB.B013.cap_4 CapXHB.B013.cap_5

theorem n_03020212 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 0, 2, 1, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 0, 2, 1, 2]) (ax := 0) (by decide) CapXHB.B014.cap_0 CapXHB.B014.cap_1

theorem n_03020213 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 0, 2, 1, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 0, 2, 1, 3]) (ax := 0) (by decide) CapXHB.B014.cap_2 n_030202131

theorem n_03020302 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 0, 3, 0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 0, 3, 0, 2]) (ax := 0) (by decide) CapXHB.B015.cap_0 CapXHB.B015.cap_1

theorem n_03020303 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 0, 3, 0, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 0, 3, 0, 3]) (ax := 0) (by decide) CapXHB.B015.cap_2 n_030203031

theorem n_03020312 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 0, 3, 1, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 0, 3, 1, 2]) (ax := 0) (by decide) n_030203120 n_030203121

theorem n_03020313 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 0, 3, 1, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 0, 3, 1, 3]) (ax := 0) (by decide) n_030203130 n_030203131

theorem n_03021203 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 1, 2, 0, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 1, 2, 0, 3]) (ax := 0) (by decide) n_030212030 CapXHB.B017.cap_5

theorem n_03021302 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 1, 3, 0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 1, 3, 0, 2]) (ax := 0) (by decide) CapXHB.B018.cap_1 CapXHB.B018.cap_2

theorem n_03021303 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 1, 3, 0, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 1, 3, 0, 3]) (ax := 0) (by decide) CapXHB.B018.cap_3 CapXHB.B018.cap_4

theorem n_03021313 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 1, 3, 1, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 1, 3, 1, 3]) (ax := 0) (by decide) CapXHB.B019.cap_1 CapXHB.B019.cap_2

theorem n_03030202 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 0, 2, 0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 0, 2, 0, 2]) (ax := 0) (by decide) n_030302020 n_030302021

theorem n_03030203 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 0, 2, 0, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 0, 2, 0, 3]) (ax := 0) (by decide) n_030302030 n_030302031

theorem n_03030212 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 0, 2, 1, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 0, 2, 1, 2]) (ax := 0) (by decide) n_030302120 CapXHB.B021.cap_1

theorem n_03030213 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 0, 2, 1, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 0, 2, 1, 3]) (ax := 0) (by decide) n_030302130 CapXHB.B021.cap_4

theorem n_03030302 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 0, 3, 0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 0, 3, 0, 2]) (ax := 0) (by decide) n_030303020 n_030303021

theorem n_03030303 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 0, 3, 0, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 0, 3, 0, 3]) (ax := 0) (by decide) n_030303030 CapXHB.B022.cap_5

theorem n_03031202 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 1, 2, 0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 1, 2, 0, 2]) (ax := 0) (by decide) CapXHB.B023.cap_1 CapXHB.B023.cap_2

theorem n_0202021 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 2, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 2, 1]) (ax := 1) (by decide) n_02020212 n_02020213

theorem n_0202031 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 3, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 3, 1]) (ax := 1) (by decide) n_02020312 n_02020313

theorem n_0202120 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 1, 2, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 1, 2, 0]) (ax := 1) (by decide) n_02021202 n_02021203

theorem n_1202020 : CapOn (cpathBox xhRoot [1, 2, 0, 2, 0, 2, 0]) (3 / 40) :=
  CapOn.merge_path (p := [1, 2, 0, 2, 0, 2, 0]) (ax := 1) (by decide) n_12020202 CapXHB.B024.cap_3

theorem n_0202020 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 2, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 2, 0]) (ax := 1) (by decide) n_02020202 n_02020203

theorem n_0212021 : CapOn (cpathBox xhRoot [0, 2, 1, 2, 0, 2, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 1, 2, 0, 2, 1]) (ax := 1) (by decide) n_02120212 CapXHB.B011.cap_4

theorem n_0212120 : CapOn (cpathBox xhRoot [0, 2, 1, 2, 1, 2, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 1, 2, 1, 2, 0]) (ax := 1) (by decide) n_02121202 CapXHB.B012.cap_2

theorem n_0202121 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 1, 2, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 1, 2, 1]) (ax := 1) (by decide) n_02021212 n_02021213

theorem n_0202130 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 1, 3, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 1, 3, 0]) (ax := 1) (by decide) n_02021302 n_02021303

theorem n_0212121 : CapOn (cpathBox xhRoot [0, 2, 1, 2, 1, 2, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 1, 2, 1, 2, 1]) (ax := 1) (by decide) n_02121212 CapXHB.B012.cap_5

theorem n_0202030 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 3, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 3, 0]) (ax := 1) (by decide) n_02020302 n_02020303

theorem n_0212020 : CapOn (cpathBox xhRoot [0, 2, 1, 2, 0, 2, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 1, 2, 0, 2, 0]) (ax := 1) (by decide) n_02120202 CapXHB.B010.cap_6

end CKLaneM06.Cap.CapXHAgg


