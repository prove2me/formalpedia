-- Prove2me | Definitions.Def_CK_CKLaneA1_R5Final_q01
-- name    : CK_CKLaneA1_R5Final_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T09:09:14.545272+00:00
-- url     : https://prove2.me/theorems/bb931ccc-7ec1-4576-96d3-cec66d94c2d9
-- title:
--   Courtade–Kumar proof module `CKLaneA1.R5Final (piece 2 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.R5Final (piece 2 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.R5Final (piece 2 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.R5Final (piece 2 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/R5Final (piece 2 of 5).lean)

import Definitions.Def_CK_CKLaneA1_R5Final_q00

set_option autoImplicit false
namespace CKLaneA1.R5
open GeneralCK CKLaneP CKLaneN1.CEStat CKLaneA1.R5Data
theorem allStrips_ok : allStrips.all stripOK = true := by
  simp only [allStrips, List.all_append, strips000_ok, strips001_ok, strips002_ok, strips003_ok, strips004_ok, strips005_ok, strips006_ok, strips007_ok, strips008_ok, strips009_ok, strips010_ok, strips011_ok, strips012_ok, strips013_ok, strips014_ok, strips015_ok, strips016_ok, strips017_ok, Bool.and_self, Bool.and_true, Bool.true_and]

end CKLaneA1.R5


