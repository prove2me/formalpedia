-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_R3Yup
-- name    : CK_CKLaneM07_CE_R3Yup
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T09:15:57.967496+00:00
-- url     : https://prove2.me/theorems/6821c6dc-29cf-4e6a-a065-b7a09b280c91
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.R3Yup` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.R3Yup` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.R3Yup` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.R3Yup (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/R3Yup.lean)

import Definitions.Def_CK_CKLaneM07_CE_R3Roots
import Definitions.Def_CK_CKLaneN1_R3Excl

-- ===== source module CKLaneM07.CE.R3Yup =====
section

/-! Lane M07 row-3 octave heights: `yupOK (1/2^(k-1)) Y<k> = true` for N1's `y_upper` (boundary 08:51Z). -/

namespace CKLaneM07.CE.R3Yup

open CKLaneM07.CE.R3Roots

theorem yup17 : CKLaneN1.R3.yupOK (1 / 65536) Y17 = true := by decide +kernel

theorem yup16 : CKLaneN1.R3.yupOK (1 / 32768) Y16 = true := by decide +kernel

theorem yup15 : CKLaneN1.R3.yupOK (1 / 16384) Y15 = true := by decide +kernel

theorem yup14 : CKLaneN1.R3.yupOK (1 / 8192) Y14 = true := by decide +kernel

theorem yup13 : CKLaneN1.R3.yupOK (1 / 4096) Y13 = true := by decide +kernel

theorem yup12 : CKLaneN1.R3.yupOK (1 / 2048) Y12 = true := by decide +kernel

theorem yup11 : CKLaneN1.R3.yupOK (1 / 1024) Y11 = true := by decide +kernel

theorem yup10 : CKLaneN1.R3.yupOK (1 / 512) Y10 = true := by decide +kernel

theorem yup9 : CKLaneN1.R3.yupOK (1 / 256) Y9 = true := by decide +kernel

theorem yup8 : CKLaneN1.R3.yupOK (1 / 128) Y8 = true := by decide +kernel

theorem yup7 : CKLaneN1.R3.yupOK (1 / 64) Y7 = true := by decide +kernel

end CKLaneM07.CE.R3Yup

end


