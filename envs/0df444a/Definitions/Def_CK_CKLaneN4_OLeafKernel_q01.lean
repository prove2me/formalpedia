-- Prove2me | Definitions.Def_CK_CKLaneN4_OLeafKernel_q01
-- name    : CK_CKLaneN4_OLeafKernel_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T13:59:29.98554+00:00
-- url     : https://prove2.me/theorems/0fa81721-1372-48b5-9bc1-bf69a9f714f1
-- title:
--   Courtade–Kumar proof module `CKLaneN4.OLeafKernel (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.OLeafKernel (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.OLeafKernel (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.OLeafKernel (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/OLeafKernel (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneN4_OLeafKernel_q00

namespace CKLaneN4
open GeneralCK CKLaneD CKLaneD.OCompact
def l4BoxOK (B : Box) : Bool :=
  decide (0 < B.alo ∧ B.alo ≤ B.ahi ∧ 2 * B.ahi ≤ 1 ∧ 1 ≤ 2 * B.blo ∧ B.blo ≤ B.bhi ∧ B.bhi < 1 ∧
    0 ≤ B.t0 ∧ B.t0 ≤ B.t1 ∧ B.t1 ≤ 1)

/-- Certified upper bound of the mean entropy on the box. -/
def l4EHi (w : L4Witness) : ℚ :=
  EMIN + w.box.t1 * ((Hhi w.box.ahi w.pa + Hhi w.box.blo w.pb) / 2 - EMIN)

end CKLaneN4


