-- Prove2me | Definitions.Def_CK_CKLaneM06_CapXHAgg_q00_q02
-- name    : CK_CKLaneM06_CapXHAgg_q00_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T22:14:00.023665+00:00
-- url     : https://prove2.me/theorems/513f49ea-5409-4787-a37f-a9b6b46067d4
-- title:
--   Courtade–Kumar proof module `CKLaneM06.CapXHAgg (piece 1 of 4) (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM06.CapXHAgg (piece 1 of 4) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM06.CapXHAgg (piece 1 of 4) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM06.CapXHAgg (piece 1 of 4) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM06/CapXHAgg (piece 1 of 4) (piece 3 of 4).lean)

import Definitions.Def_CK_CKLaneM06_CapXHAgg_q00_q01

set_option autoImplicit false
namespace CKLaneM06.Cap.CapXHAgg
open GeneralCK CKLaneM06.Cap
theorem n_020203021 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 3, 0, 2, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 3, 0, 2, 1]) (ax := 1) (by decide) CapXH.C031.cap CapXHB.B000.cap_0

theorem n_020212120 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 1, 2, 1, 2, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 1, 2, 1, 2, 0]) (ax := 1) (by decide) n_0202121202 CapXHB.B006.cap_0

theorem n_020212021 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 1, 2, 0, 2, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 1, 2, 0, 2, 1]) (ax := 1) (by decide) n_0202120212 n_0202120213

theorem n_020202021 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 2, 0, 2, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 2, 0, 2, 1]) (ax := 1) (by decide) n_0202020212 n_0202020213

theorem n_020203130 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 3, 1, 3, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 3, 1, 3, 0]) (ax := 1) (by decide) CapXHB.B001.cap_2 CapXHB.B001.cap_3

theorem n_021202120 : CapOn (cpathBox xhRoot [0, 2, 1, 2, 0, 2, 1, 2, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 1, 2, 0, 2, 1, 2, 0]) (ax := 1) (by decide) CapXHB.B011.cap_0 CapXHB.B011.cap_1

theorem n_021202021 : CapOn (cpathBox xhRoot [0, 2, 1, 2, 0, 2, 0, 2, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 1, 2, 0, 2, 0, 2, 1]) (ax := 1) (by decide) n_0212020212 CapXHB.B010.cap_5

theorem n_020202020 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 2, 0, 2, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 2, 0, 2, 0]) (ax := 1) (by decide) CapXH.C000.cap CapXH.C001.cap

theorem n_020203031 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 3, 0, 3, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 3, 0, 3, 1]) (ax := 1) (by decide) CapXHB.B000.cap_2 CapXHB.B000.cap_3

theorem n_020203120 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 3, 1, 2, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 3, 1, 2, 0]) (ax := 1) (by decide) CapXHB.B000.cap_4 CapXHB.B000.cap_5

theorem n_020202131 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 2, 1, 3, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 2, 1, 3, 1]) (ax := 1) (by decide) n_0202021312 n_0202021313

theorem n_020203131 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 3, 1, 3, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 3, 1, 3, 1]) (ax := 1) (by decide) CapXHB.B001.cap_4 CapXHB.B002.cap_0

theorem n_021202020 : CapOn (cpathBox xhRoot [0, 2, 1, 2, 0, 2, 0, 2, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 1, 2, 0, 2, 0, 2, 0]) (ax := 1) (by decide) n_0212020202 CapXHB.B010.cap_2

theorem n_020203121 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 3, 1, 2, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 3, 1, 2, 1]) (ax := 1) (by decide) CapXHB.B001.cap_0 CapXHB.B001.cap_1

theorem n_020202031 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 2, 0, 3, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 2, 0, 3, 1]) (ax := 1) (by decide) CapXH.C008.cap CapXH.C009.cap

theorem n_030202131 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 0, 2, 1, 3, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 0, 2, 1, 3, 1]) (ax := 1) (by decide) CapXHB.B014.cap_3 CapXHB.B014.cap_4

theorem n_030203031 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 0, 3, 0, 3, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 0, 3, 0, 3, 1]) (ax := 1) (by decide) CapXHB.B015.cap_3 CapXHB.B015.cap_4

theorem n_030203120 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 0, 3, 1, 2, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 0, 3, 1, 2, 0]) (ax := 1) (by decide) CapXHB.B016.cap_0 CapXHB.B016.cap_1

theorem n_030203121 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 0, 3, 1, 2, 1]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 0, 3, 1, 2, 1]) (ax := 1) (by decide) CapXHB.B016.cap_2 CapXHB.B016.cap_3

theorem n_030203130 : CapOn (cpathBox xhRoot [0, 3, 0, 2, 0, 3, 1, 3, 0]) (3 / 40) :=
  CapOn.merge_path (p := [0, 3, 0, 2, 0, 3, 1, 3, 0]) (ax := 1) (by decide) CapXHB.B016.cap_4 CapXHB.B016.cap_5

end CKLaneM06.Cap.CapXHAgg


