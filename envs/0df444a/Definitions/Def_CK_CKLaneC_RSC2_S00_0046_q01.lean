-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_S00_0046_q01
-- name    : CK_CKLaneC_RSC2_S00_0046_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T22:46:26.979992+00:00
-- url     : https://prove2.me/theorems/e9151e22-0de8-4556-8c62-ab905ef98219
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.S00_0046 (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.S00_0046 (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.S00_0046 (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.S00_0046 (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/S00_0046 (piece 2 of 3).lean)

import Definitions.Def_CK_CKLaneC_RSC2_S00_0046_q00

namespace CKLaneC.RSC2.S00_0046
open CKLaneC.TM3 CKLaneC.RSCell
theorem s0_7 : stageC0 w7 q7 = true := by decide +kernel
theorem s1_7 : stageC1 w7 q7 = true := by decide +kernel
theorem s2_7 : stageC2 w7 q7 = true := by decide +kernel
theorem s3_7 : stageC3 w7 q7 = true := by decide +kernel
theorem sE_7 : stageE w7 q7 = true := by decide +kernel
theorem sF_7 : stageF w7 = true := by decide +kernel
theorem ok_7 : (domOK c7 && cellCheck c7 q7) = true :=
  staged_check c7 q7 w7 (by decide +kernel) sB_7 s0_7 s1_7 s2_7 s3_7 sE_7 sF_7

end CKLaneC.RSC2.S00_0046


