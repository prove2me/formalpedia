-- Prove2me | Definitions.Def_CK_CKLaneN23_CornerOkTC_p05
-- name    : CK_CKLaneN23_CornerOkTC_p05
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T17:48:38.228528+00:00
-- url     : https://prove2.me/theorems/0f942bd1-6de7-437e-bd2c-adf3626f1fe6
-- title:
--   Courtade–Kumar proof module `CKLaneN23.CornerOkTC (proof part 6 of 8)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.CornerOkTC (proof part 6 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.CornerOkTC (proof part 6 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.CornerOkTC (proof part 6 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/CornerOkTC (proof part 6 of 8).lean)

import Definitions.Def_CK_CKLaneN23_TChainData_v2

/-! Kernel evaluation of part of the corner checker `tcCheck` (Lane N23b), one conjunct per theorem. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CKLaneN23.CT

theorem tcp_T2_3 : c_tc_T2_3 = true := by decide +kernel
theorem tcp_T3_3 : c_tc_T3_3 = true := by decide +kernel
theorem tcp_nT2_3 : c_tc_nT2_3 = true := by decide +kernel
theorem tcp_T12_3 : c_tc_T12_3 = true := by decide +kernel
theorem tcp_RS3 : c_tc_RS3 = true := by decide +kernel
theorem tcp_z4 : c_tc_z4 = true := by decide +kernel
theorem tcp_W4 : c_tc_W4 = true := by decide +kernel
theorem tcp_Xw4 : c_tc_Xw4 = true := by decide +kernel
theorem tcp_F0_4 : c_tc_F0_4 = true := by decide +kernel

end CKLaneN23.CT


