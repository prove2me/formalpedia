-- Prove2me | Definitions.Def_CK_CKLaneP_Cells_S3_C039_0029
-- name    : CK_CKLaneP_Cells_S3_C039_0029
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T01:06:32.984605+00:00
-- url     : https://prove2.me/theorems/73753e06-b1b5-47ed-9c44-902cb25be078
-- title:
--   Courtade–Kumar proof module `CKLaneP.Cells.S3.C039_0029` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.Cells.S3.C039_0029` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.Cells.S3.C039_0029` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.Cells.S3.C039_0029 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/Cells/S3/C039_0029.lean)

import Definitions.Def_CK_CKLaneP_Cells_S3_C039_0029_part00

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C039_0029

open CKLaneP

theorem check : STree.check (1 / 200000 : ℚ) tree (17 / 500000 : ℚ) (353 / 10000000 : ℚ) (0 : ℚ) (3 / 10 : ℚ) = true := by
  decide +kernel

end CKLaneP.Cells.S3.C039_0029


