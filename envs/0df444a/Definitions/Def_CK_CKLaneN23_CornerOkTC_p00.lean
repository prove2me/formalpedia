-- Prove2me | Definitions.Def_CK_CKLaneN23_CornerOkTC_p00
-- name    : CK_CKLaneN23_CornerOkTC_p00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T05:06:12.23091+00:00
-- url     : https://prove2.me/theorems/c8e67cc5-69af-42e3-9dcd-0d06d4cf11b0
-- title:
--   Courtade–Kumar proof module `CKLaneN23.CornerOkTC (proof part 1 of 8)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.CornerOkTC (proof part 1 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.CornerOkTC (proof part 1 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.CornerOkTC (proof part 1 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/CornerOkTC (proof part 1 of 8).lean)

import Definitions.Def_CK_CKLaneN23_TChainData_v2

/-! Kernel evaluation of part of the corner checker `tcCheck` (Lane N23b), one conjunct per theorem. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CKLaneN23.CT

theorem tcp_one : c_tc_one = true := by decide +kernel
theorem tcp_Hu : c_tc_Hu = true := by decide +kernel
theorem tcp_Hb : c_tc_Hb = true := by decide +kernel
theorem tcp_HH : c_tc_HH = true := by decide +kernel
theorem tcp_E : c_tc_E = true := by decide +kernel
theorem tcp_nE : c_tc_nE = true := by decide +kernel
theorem tcp_eps : c_tc_eps = true := by decide +kernel
theorem tcp_invE : c_tc_invE = true := by decide +kernel
theorem tcp_nHu : c_tc_nHu = true := by decide +kernel
theorem tcp_omHu : c_tc_omHu = true := by decide +kernel
theorem tcp_invHu : c_tc_invHu = true := by decide +kernel
theorem tcp_Aus : c_tc_Aus = true := by decide +kernel
theorem tcp_XA : c_tc_XA = true := by decide +kernel
theorem tcp_Ju : c_tc_Ju = true := by decide +kernel
theorem tcp_g4 : c_tc_g4 = true := by decide +kernel
theorem tcp_Jd1 : c_tc_Jd1 = true := by decide +kernel
theorem tcp_g42 : c_tc_g42 = true := by decide +kernel
theorem tcp_Xg42 : c_tc_Xg42 = true := by decide +kernel
theorem tcp_Jd2 : c_tc_Jd2 = true := by decide +kernel
theorem tcp_E1 : c_tc_E1 = true := by decide +kernel
theorem tcp_E2 : c_tc_E2 = true := by decide +kernel
theorem tcp_e1 : c_tc_e1 = true := by decide +kernel
theorem tcp_A1 : c_tc_A1 = true := by decide +kernel
theorem tcp_d32 : c_tc_d32 = true := by decide +kernel
theorem tcp_qd : c_tc_qd = true := by decide +kernel
theorem tcp_A2 : c_tc_A2 = true := by decide +kernel
theorem tcp_Ap : c_tc_Ap = true := by decide +kernel
theorem tcp_td : c_tc_td = true := by decide +kernel
theorem tcp_q2 : c_tc_q2 = true := by decide +kernel
theorem tcp_s3 : c_tc_s3 = true := by decide +kernel
theorem tcp_td2 : c_tc_td2 = true := by decide +kernel
theorem tcp_s4 : c_tc_s4 = true := by decide +kernel
theorem tcp_t2 : c_tc_t2 = true := by decide +kernel
theorem tcp_z1 : c_tc_z1 = true := by decide +kernel
theorem tcp_W1 : c_tc_W1 = true := by decide +kernel
theorem tcp_Xw1 : c_tc_Xw1 = true := by decide +kernel
theorem tcp_F0_1 : c_tc_F0_1 = true := by decide +kernel
theorem tcp_F1_1 : c_tc_F1_1 = true := by decide +kernel

end CKLaneN23.CT


