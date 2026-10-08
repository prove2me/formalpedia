-- Prove2me | Definitions.Def_CK_CKLaneA1_FEFinal_q01
-- name    : CK_CKLaneA1_FEFinal_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T04:10:23.307247+00:00
-- url     : https://prove2.me/theorems/a0eeb44a-2b52-42f4-925f-9fa85d151d4b
-- title:
--   Courtade–Kumar proof module `CKLaneA1.FEFinal (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.FEFinal (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.FEFinal (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.FEFinal (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/FEFinal (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneA1_FEFinal_q00

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace CKLaneA1
open GeneralCK GeneralCK.Correction GeneralCK.Correction.Natural GeneralCK.Correction.HighU
theorem feStrips_last : decide (SCz ≤ 50 * lastU 0 feStrips) = true := by decide +kernel

end CKLaneA1


