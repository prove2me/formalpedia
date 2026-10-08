-- Prove2me | Definitions.Def_CK_CKLaneM06_CapXHAgg_q00_q01_q01
-- name    : CK_CKLaneM06_CapXHAgg_q00_q01_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T21:09:47.861604+00:00
-- url     : https://prove2.me/theorems/7509d648-2764-4a75-9933-6e167ea95701
-- title:
--   Courtade–Kumar proof module `CKLaneM06.CapXHAgg (piece 1 of 4) (piece 2 of 4) (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM06.CapXHAgg (piece 1 of 4) (piece 2 of 4) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM06.CapXHAgg (piece 1 of 4) (piece 2 of 4) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM06.CapXHAgg (piece 1 of 4) (piece 2 of 4) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM06/CapXHAgg (piece 1 of 4) (piece 2 of 4) (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneM06_CapXHAgg_q00_q01_q01_q01

set_option autoImplicit false
namespace CKLaneM06.Cap.CapXHAgg
open GeneralCK CKLaneM06.Cap
theorem n_0202021203 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 2, 1, 2, 0, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 2, 1, 2, 0, 3]) (ax := 0) (by decide) CapXH.C013.cap CapXH.C014.cap

theorem n_0202120203 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 1, 2, 0, 2, 0, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 1, 2, 0, 2, 0, 3]) (ax := 0) (by decide) CapXHB.B003.cap_1 CapXHB.B003.cap_2

end CKLaneM06.Cap.CapXHAgg


