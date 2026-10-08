-- Prove2me | Definitions.Def_CK_CKLaneN1_R3Assembly_q03
-- name    : CK_CKLaneN1_R3Assembly_q03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T18:06:10.132896+00:00
-- url     : https://prove2.me/theorems/a3a1a1d2-7f0c-48cb-a7f0-a06e106c1d24
-- title:
--   Courtade–Kumar proof module `CKLaneN1.R3Assembly (piece 4 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.R3Assembly (piece 4 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.R3Assembly (piece 4 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.R3Assembly (piece 4 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/R3Assembly (piece 4 of 5).lean)

import Definitions.Def_CK_CKLaneN1_R3Assembly_q02

set_option autoImplicit false
namespace CKLaneN1.R3
open GeneralCK CKLaneN1 CKLaneE.FP GeneralCK.SmallMeanPhiCutoff
/-- the octave root box `[a₀, a₁] × [0,1] × [0, Y]` -/
def octBox (a0 a1 Y : ℚ) : B3 := ⟨a0, a1, 0, 1, 0, Y⟩

end CKLaneN1.R3


