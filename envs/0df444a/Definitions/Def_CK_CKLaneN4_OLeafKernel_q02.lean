-- Prove2me | Definitions.Def_CK_CKLaneN4_OLeafKernel_q02
-- name    : CK_CKLaneN4_OLeafKernel_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T14:18:36.708165+00:00
-- url     : https://prove2.me/theorems/c0ce65f8-e289-456f-89ae-258cd357ce26
-- title:
--   Courtade–Kumar proof module `CKLaneN4.OLeafKernel (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.OLeafKernel (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.OLeafKernel (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.OLeafKernel (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/OLeafKernel (piece 3 of 4).lean)

import Definitions.Def_CK_CKLaneN4_OLeafKernel_q01

namespace CKLaneN4
open GeneralCK CKLaneD CKLaneD.OCompact
/-- The archived label-4 acceptance test (`E.b ≤ 11/200`, `q.b ≤ 2/5`, `d.a ≥ 8 E.b`) bound to the
archived path `p`. -/
def checkL4 (p : List ℕ) (w : L4Witness) : Bool :=
  imageCheck (uvtBox p) w.box && l4BoxOK w.box && checkPt w.box.ahi w.pa &&
  checkPt w.box.blo w.pb &&
  decide (l4EHi w ≤ 11 / 200) && decide (1 - w.box.alo - w.box.blo ≤ 2 / 5) &&
  decide (8 * l4EHi w ≤ w.box.blo - w.box.ahi)

end CKLaneN4


