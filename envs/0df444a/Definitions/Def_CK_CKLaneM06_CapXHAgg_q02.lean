-- Prove2me | Definitions.Def_CK_CKLaneM06_CapXHAgg_q02
-- name    : CK_CKLaneM06_CapXHAgg_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T22:45:38.294984+00:00
-- url     : https://prove2.me/theorems/d8c50f1c-a611-4874-813e-d323161d499a
-- title:
--   Courtade–Kumar proof module `CKLaneM06.CapXHAgg (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM06.CapXHAgg (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM06.CapXHAgg (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM06.CapXHAgg (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM06/CapXHAgg (piece 3 of 4).lean)

import Definitions.Def_CK_CKLaneM06_CapXHAgg_q01

set_option autoImplicit false
namespace CKLaneM06.Cap.CapXHAgg
open GeneralCK CKLaneM06.Cap
theorem n_0202131 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 1, 3, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 1, 3, 1]) (ax := 1) (by decide) CapXHB.B007.cap_5 CapXHB.B008.cap_0

theorem n_0203030 : CapOn (cpathBox xhRoot [0, 2, 0, 3, 0, 3, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 3, 0, 3, 0]) (ax := 1) (by decide) n_02030302 n_02030303

theorem n_0203031 : CapOn (cpathBox xhRoot [0, 2, 0, 3, 0, 3, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 3, 0, 3, 1]) (ax := 1) (by decide) CapXHB.B009.cap_1 n_02030313

theorem n_0302020 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 0, 2, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 0, 2, 0]) (ax := 1) (by decide) n_03020202 n_03020203

theorem n_0302021 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 0, 2, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 0, 2, 1]) (ax := 1) (by decide) n_03020212 n_03020213

theorem n_0302030 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 0, 3, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 0, 3, 0]) (ax := 1) (by decide) n_03020302 n_03020303

theorem n_0302031 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 0, 3, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 0, 3, 1]) (ax := 1) (by decide) n_03020312 n_03020313

theorem n_0302120 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 1, 2, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 1, 2, 0]) (ax := 1) (by decide) CapXHB.B017.cap_2 n_03021203

theorem n_0302130 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 1, 3, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 1, 3, 0]) (ax := 1) (by decide) n_03021302 n_03021303

theorem n_0302131 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 1, 3, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 1, 3, 1]) (ax := 1) (by decide) CapXHB.B019.cap_0 n_03021313

theorem n_0303020 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 0, 2, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 0, 2, 0]) (ax := 1) (by decide) n_03030202 n_03030203

theorem n_0303021 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 0, 2, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 0, 2, 1]) (ax := 1) (by decide) n_03030212 n_03030213

theorem n_0303030 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 0, 3, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 0, 3, 0]) (ax := 1) (by decide) n_03030302 n_03030303

theorem n_0303120 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 1, 2, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 1, 2, 0]) (ax := 1) (by decide) n_03031202 CapXHB.B023.cap_3

theorem n_020203 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 3]) (ax := 0) (by decide) n_0202030 n_0202031

theorem n_021212 : CapOn (cpathBox xhRoot [0, 2, 1, 2, 1, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 1, 2, 1, 2]) (ax := 0) (by decide) n_0212120 n_0212121

theorem n_021202 : CapOn (cpathBox xhRoot [0, 2, 1, 2, 0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 1, 2, 0, 2]) (ax := 0) (by decide) n_0212020 n_0212021

theorem n_120212 : CapOn (cpathBox xhRoot [1, 2, 0, 2, 1, 2]) (3 / 40) :=
  CapOn.merge_path (p := [1, 2, 0, 2, 1, 2]) (ax := 0) (by decide) CapXHB.B024.cap_6 CapXHB.B025.cap_0

theorem n_120202 : CapOn (cpathBox xhRoot [1, 2, 0, 2, 0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [1, 2, 0, 2, 0, 2]) (ax := 0) (by decide) n_1202020 CapXHB.B024.cap_4

theorem n_020212 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 1, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 1, 2]) (ax := 0) (by decide) n_0202120 n_0202121

theorem n_020213 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 1, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 1, 3]) (ax := 0) (by decide) n_0202130 n_0202131

theorem n_021203 : CapOn (cpathBox xhRoot [0, 2, 1, 2, 0, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 1, 2, 0, 3]) (ax := 0) (by decide) CapXHB.B011.cap_5 CapXHB.B011.cap_6

theorem n_020202 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 2]) (ax := 0) (by decide) n_0202020 n_0202021

theorem n_020302 : CapOn (cpathBox xhRoot [0, 2, 0, 3, 0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 3, 0, 2]) (ax := 0) (by decide) CapXHB.B008.cap_1 CapXHB.B008.cap_2

theorem n_020303 : CapOn (cpathBox xhRoot [0, 2, 0, 3, 0, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 3, 0, 3]) (ax := 0) (by decide) n_0203030 n_0203031

theorem n_020313 : CapOn (cpathBox xhRoot [0, 2, 0, 3, 1, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 3, 1, 3]) (ax := 0) (by decide) CapXHB.B009.cap_5 CapXHB.B009.cap_6

theorem n_030202 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 0, 2]) (ax := 0) (by decide) n_0302020 n_0302021

theorem n_030203 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 0, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 0, 3]) (ax := 0) (by decide) n_0302030 n_0302031

theorem n_030212 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 1, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 1, 2]) (ax := 0) (by decide) n_0302120 CapXHB.B018.cap_0

theorem n_030213 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 1, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 1, 3]) (ax := 0) (by decide) n_0302130 n_0302131

theorem n_030302 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 0, 2]) (ax := 0) (by decide) n_0303020 n_0303021

theorem n_030303 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 0, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 0, 3]) (ax := 0) (by decide) n_0303030 CapXHB.B023.cap_0

theorem n_030312 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 1, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 1, 2]) (ax := 0) (by decide) n_0303120 CapXHB.B023.cap_4

theorem n_02120 : CapOn (cpathBox xhRoot [0, 2, 1, 2, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 1, 2, 0]) (ax := 1) (by decide) n_021202 n_021203

theorem n_02020 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0]) (ax := 1) (by decide) n_020202 n_020203

theorem n_12021 : CapOn (cpathBox xhRoot [1, 2, 0, 2, 1]) (3 / 40) :=
  CapOn.merge_path (p := [1, 2, 0, 2, 1]) (ax := 1) (by decide) n_120212 CapXHB.B025.cap_1

theorem n_12020 : CapOn (cpathBox xhRoot [1, 2, 0, 2, 0]) (3 / 40) :=
  CapOn.merge_path (p := [1, 2, 0, 2, 0]) (ax := 1) (by decide) n_120202 CapXHB.B024.cap_5

theorem n_02121 : CapOn (cpathBox xhRoot [0, 2, 1, 2, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 1, 2, 1]) (ax := 1) (by decide) n_021212 CapXHB.B013.cap_0

theorem n_02021 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 1]) (ax := 1) (by decide) n_020212 n_020213

theorem n_02030 : CapOn (cpathBox xhRoot [0, 2, 0, 3, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 3, 0]) (ax := 1) (by decide) n_020302 n_020303

theorem n_02031 : CapOn (cpathBox xhRoot [0, 2, 0, 3, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 3, 1]) (ax := 1) (by decide) CapXHB.B009.cap_4 n_020313

theorem n_03020 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 0]) (ax := 1) (by decide) n_030202 n_030203

theorem n_03021 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 1]) (ax := 1) (by decide) n_030212 n_030213

theorem n_03030 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 0]) (ax := 1) (by decide) n_030302 n_030303

theorem n_03031 : CapOn (cpathBox xhRoot [0, 3, 0, 3, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3, 1]) (ax := 1) (by decide) n_030312 CapXHB.B023.cap_5

theorem n_1202 : CapOn (cpathBox xhRoot [1, 2, 0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [1, 2, 0, 2]) (ax := 0) (by decide) n_12020 n_12021

theorem n_0202 : CapOn (cpathBox xhRoot [0, 2, 0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2]) (ax := 0) (by decide) n_02020 n_02021

theorem n_0212 : CapOn (cpathBox xhRoot [0, 2, 1, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 1, 2]) (ax := 0) (by decide) n_02120 n_02121

theorem n_0203 : CapOn (cpathBox xhRoot [0, 2, 0, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 3]) (ax := 0) (by decide) n_02030 n_02031

theorem n_0302 : CapOn (cpathBox xhRoot [0, 3, 0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2]) (ax := 0) (by decide) n_03020 n_03021

theorem n_0303 : CapOn (cpathBox xhRoot [0, 3, 0, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 3]) (ax := 0) (by decide) n_03030 n_03031

theorem n_020 : CapOn (cpathBox xhRoot [0, 2, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0]) (ax := 1) (by decide) n_0202 n_0203

theorem n_120 : CapOn (cpathBox xhRoot [1, 2, 0]) (3 / 40) :=
  CapOn.merge_path (p := [1, 2, 0]) (ax := 1) (by decide) n_1202 CapXHB.B025.cap_2

theorem n_021 : CapOn (cpathBox xhRoot [0, 2, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 1]) (ax := 1) (by decide) n_0212 CapXHB.B013.cap_1

theorem n_030 : CapOn (cpathBox xhRoot [0, 3, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0]) (ax := 1) (by decide) n_0302 n_0303

theorem n_12 : CapOn (cpathBox xhRoot [1, 2]) (3 / 40) :=
  CapOn.merge_path (p := [1, 2]) (ax := 0) (by decide) n_120 CapXHB.B025.cap_3

theorem n_02 : CapOn (cpathBox xhRoot [0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2]) (ax := 0) (by decide) n_020 n_021

theorem n_03 : CapOn (cpathBox xhRoot [0, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3]) (ax := 0) (by decide) n_030 CapXHB.B024.cap_0

theorem n_1 : CapOn (cpathBox xhRoot [1]) (3 / 40) :=
  CapOn.merge_path (p := [1]) (ax := 1) (by decide) n_12 CapXHB.B025.cap_4

theorem n_0 : CapOn (cpathBox xhRoot [0]) (3 / 40) :=
  CapOn.merge_path (p := [0]) (ax := 1) (by decide) n_02 n_03

theorem n_root : CapOn (cpathBox xhRoot []) (3 / 40) :=
  CapOn.merge_path (p := []) (ax := 0) (by decide) n_0 n_1

/-- `CapOn` on the whole archived root. -/
theorem capOn_root : CapOn xhRoot (3 / 40) := n_root

end CKLaneM06.Cap.CapXHAgg


