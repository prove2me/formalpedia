-- Prove2me | Definitions.Def_CK_CKLaneC2R_Cells_S00_B034_q200
-- name    : CK_CKLaneC2R_Cells_S00_B034_q200
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:14:07.135511+00:00
-- url     : https://prove2.me/theorems/9ebca3b2-3283-4012-b1c6-803df5cd27d2
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.Cells.S00.B034 (piece 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.Cells.S00.B034 (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.Cells.S00.B034 (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.Cells.S00.B034 (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/Cells/S00/B034 (piece 1 of 2).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B034_q02





namespace CKLaneC2R.Cells.S00.B034

open GeneralCK GeneralCK.Certificates CKLaneC2R ReflectionCompactProgramKernel

-- box ['51/320', '103/640', '5491/32000', '2379/12800']  taylor_lower 6572062299434076444413/36028797018963968000000
theorem c699_ok : cellOk c699 = true := by decide +kernel

end CKLaneC2R.Cells.S00.B034


