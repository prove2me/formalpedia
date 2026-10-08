-- Prove2me | Definitions.Def_CK_CKLaneN23_CornerOkTC_p07
-- name    : CK_CKLaneN23_CornerOkTC_p07
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T02:31:25.185699+00:00
-- url     : https://prove2.me/theorems/4e4784d7-b0f8-408a-b84a-6903226be342
-- title:
--   Courtade–Kumar proof module `CKLaneN23.CornerOkTC (proof part 8 of 8)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.CornerOkTC (proof part 8 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.CornerOkTC (proof part 8 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.CornerOkTC (proof part 8 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/CornerOkTC (proof part 8 of 8).lean)

import Definitions.Def_CK_CKLaneN23_TChainData_v2

/-! Kernel evaluation of part of the corner checker `tcCheck` (Lane N23b), one conjunct per theorem. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CKLaneN23.CT

theorem tcp_T2_4 : c_tc_T2_4 = true := by decide +kernel
theorem tcp_T3_4 : c_tc_T3_4 = true := by decide +kernel
theorem tcp_nT2_4 : c_tc_nT2_4 = true := by decide +kernel
theorem tcp_T12_4 : c_tc_T12_4 = true := by decide +kernel
theorem tcp_RS4 : c_tc_RS4 = true := by decide +kernel
theorem tcp_Xe : c_tc_Xe = true := by decide +kernel
theorem tcp_Sv : c_tc_Sv = true := by decide +kernel
theorem tcp_Kv : c_tc_Kv = true := by decide +kernel
theorem tcp_Ju2 : c_tc_Ju2 = true := by decide +kernel
theorem tcp_Ju22 : c_tc_Ju22 = true := by decide +kernel
theorem tcp_KJ : c_tc_KJ = true := by decide +kernel
theorem tcp_SJ : c_tc_SJ = true := by decide +kernel
theorem tcp_eta : c_tc_eta = true := by decide +kernel
theorem tcp_G1 : c_tc_G1 = true := by decide +kernel
theorem tcp_nRS2 : c_tc_nRS2 = true := by decide +kernel
theorem tcp_G2 : c_tc_G2 = true := by decide +kernel
theorem tcp_G3 : c_tc_G3 = true := by decide +kernel
theorem tcp_neta : c_tc_neta = true := by decide +kernel
theorem tcp_G4 : c_tc_G4 = true := by decide +kernel
theorem tcp_hRS4 : c_tc_hRS4 = true := by decide +kernel
theorem tcp_Gam : c_tc_Gam = true := by decide +kernel

end CKLaneN23.CT


