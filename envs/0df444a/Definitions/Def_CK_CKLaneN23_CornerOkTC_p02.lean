-- Prove2me | Definitions.Def_CK_CKLaneN23_CornerOkTC_p02
-- name    : CK_CKLaneN23_CornerOkTC_p02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T01:19:49.976981+00:00
-- url     : https://prove2.me/theorems/37766c26-b263-4afe-95f1-09271bd9442e
-- title:
--   Courtade–Kumar proof module `CKLaneN23.CornerOkTC (proof part 3 of 8)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.CornerOkTC (proof part 3 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.CornerOkTC (proof part 3 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.CornerOkTC (proof part 3 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/CornerOkTC (proof part 3 of 8).lean)

import Definitions.Def_CK_CKLaneN23_TChainData_v2

/-! Kernel evaluation of part of the corner checker `tcCheck` (Lane N23b), one conjunct per theorem. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CKLaneN23.CT

theorem tcp_T2_1 : c_tc_T2_1 = true := by decide +kernel
theorem tcp_T3_1 : c_tc_T3_1 = true := by decide +kernel
theorem tcp_nT2_1 : c_tc_nT2_1 = true := by decide +kernel
theorem tcp_T12_1 : c_tc_T12_1 = true := by decide +kernel
theorem tcp_RS1 : c_tc_RS1 = true := by decide +kernel
theorem tcp_z2 : c_tc_z2 = true := by decide +kernel
theorem tcp_W2 : c_tc_W2 = true := by decide +kernel
theorem tcp_Xw2 : c_tc_Xw2 = true := by decide +kernel
theorem tcp_F0_2 : c_tc_F0_2 = true := by decide +kernel
theorem tcp_F1_2 : c_tc_F1_2 = true := by decide +kernel
theorem tcp_F2_2 : c_tc_F2_2 = true := by decide +kernel
theorem tcp_zde2 : c_tc_zde2 = true := by decide +kernel
theorem tcp_nzde2 : c_tc_nzde2 = true := by decide +kernel
theorem tcp_a2 : c_tc_a2 = true := by decide +kernel
theorem tcp_aa2 : c_tc_aa2 = true := by decide +kernel
theorem tcp_aae2 : c_tc_aae2 = true := by decide +kernel
theorem tcp_T1_2 : c_tc_T1_2 = true := by decide +kernel
theorem tcp_zd2 : c_tc_zd2 = true := by decide +kernel
theorem tcp_zF2 : c_tc_zF2 = true := by decide +kernel
theorem tcp_T2_2 : c_tc_T2_2 = true := by decide +kernel
theorem tcp_T3_2 : c_tc_T3_2 = true := by decide +kernel
theorem tcp_nT2_2 : c_tc_nT2_2 = true := by decide +kernel
theorem tcp_T12_2 : c_tc_T12_2 = true := by decide +kernel
theorem tcp_RS2 : c_tc_RS2 = true := by decide +kernel
theorem tcp_z3 : c_tc_z3 = true := by decide +kernel
theorem tcp_W3 : c_tc_W3 = true := by decide +kernel
theorem tcp_Xw3 : c_tc_Xw3 = true := by decide +kernel

end CKLaneN23.CT


