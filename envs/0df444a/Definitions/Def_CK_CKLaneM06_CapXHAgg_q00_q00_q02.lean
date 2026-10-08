-- Prove2me | Definitions.Def_CK_CKLaneM06_CapXHAgg_q00_q00_q02
-- name    : CK_CKLaneM06_CapXHAgg_q00_q00_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T15:32:54.034984+00:00
-- url     : https://prove2.me/theorems/04a9b054-7f89-44bc-8253-3c9fda4af92b
-- title:
--   Courtade–Kumar proof module `CKLaneM06.CapXHAgg (piece 1 of 4) (piece 1 of 4) (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM06.CapXHAgg (piece 1 of 4) (piece 1 of 4) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM06.CapXHAgg (piece 1 of 4) (piece 1 of 4) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM06.CapXHAgg (piece 1 of 4) (piece 1 of 4) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM06/CapXHAgg (piece 1 of 4) (piece 1 of 4) (piece 3 of 4).lean)

import Definitions.Def_CK_CKLaneM06_CapXHAgg_q00_q00_q02_q01

set_option autoImplicit false
namespace CKLaneM06.Cap.CapXHAgg
open GeneralCK CKLaneM06.Cap
theorem n_0202121202 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 1, 2, 1, 2, 0, 2]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 1, 2, 1, 2, 0, 2]) (ax := 0) (by decide) n_02021212020 n_02021212021

theorem n_0202021213 : CapOn (cpathBox xhRoot [0, 2, 0, 2, 0, 2, 1, 2, 1, 3]) (3 / 40) :=
  CapOn.merge_path (p := [0, 2, 0, 2, 0, 2, 1, 2, 1, 3]) (ax := 0) (by decide) CapXH.C019.cap n_02020212131

end CKLaneM06.Cap.CapXHAgg


