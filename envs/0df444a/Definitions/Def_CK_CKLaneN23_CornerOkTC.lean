-- Prove2me | Definitions.Def_CK_CKLaneN23_CornerOkTC
-- name    : CK_CKLaneN23_CornerOkTC
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T12:12:28.166454+00:00
-- url     : https://prove2.me/theorems/5170a396-5eaf-4744-b853-90076976c944
-- title:
--   Courtade–Kumar proof module `CKLaneN23.CornerOkTC` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.CornerOkTC` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.CornerOkTC` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.CornerOkTC (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/CornerOkTC.lean)

import Definitions.Def_CK_CKLaneN23_CornerOkTC_p00
import Definitions.Def_CK_CKLaneN23_CornerOkTC_p01
import Definitions.Def_CK_CKLaneN23_CornerOkTC_p02
import Definitions.Def_CK_CKLaneN23_CornerOkTC_p03
import Definitions.Def_CK_CKLaneN23_CornerOkTC_p04
import Definitions.Def_CK_CKLaneN23_CornerOkTC_p05
import Definitions.Def_CK_CKLaneN23_CornerOkTC_p06
import Definitions.Def_CK_CKLaneN23_CornerOkTC_p07

/-! Kernel evaluation of one part of the corner checker (Lane N23b): `tcCheck = true`, assembled from its conjuncts `c_tc_* = true` (each checked by `decide +kernel` in `CornerOkTC_pNN`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CKLaneN23.CT

theorem tc_ok : tcCheck = true := by
  unfold tcCheck
  rw [tcp_one,
    tcp_Hu,
    tcp_Hb,
    tcp_HH,
    tcp_E,
    tcp_nE,
    tcp_eps,
    tcp_invE,
    tcp_nHu,
    tcp_omHu,
    tcp_invHu,
    tcp_Aus,
    tcp_XA,
    tcp_Ju,
    tcp_g4,
    tcp_Jd1,
    tcp_g42,
    tcp_Xg42,
    tcp_Jd2,
    tcp_E1,
    tcp_E2,
    tcp_e1,
    tcp_A1,
    tcp_d32,
    tcp_qd,
    tcp_A2,
    tcp_Ap,
    tcp_td,
    tcp_q2,
    tcp_s3,
    tcp_td2,
    tcp_s4,
    tcp_t2,
    tcp_z1,
    tcp_W1,
    tcp_Xw1,
    tcp_F0_1,
    tcp_F1_1,
    tcp_F2_1,
    tcp_zde1,
    tcp_nzde1,
    tcp_a1,
    tcp_aa1,
    tcp_aae1,
    tcp_T1_1,
    tcp_zd1,
    tcp_zF1,
    tcp_T2_1,
    tcp_T3_1,
    tcp_nT2_1,
    tcp_T12_1,
    tcp_RS1,
    tcp_z2,
    tcp_W2,
    tcp_Xw2,
    tcp_F0_2,
    tcp_F1_2,
    tcp_F2_2,
    tcp_zde2,
    tcp_nzde2,
    tcp_a2,
    tcp_aa2,
    tcp_aae2,
    tcp_T1_2,
    tcp_zd2,
    tcp_zF2,
    tcp_T2_2,
    tcp_T3_2,
    tcp_nT2_2,
    tcp_T12_2,
    tcp_RS2,
    tcp_z3,
    tcp_W3,
    tcp_Xw3,
    tcp_F0_3,
    tcp_F1_3,
    tcp_F2_3,
    tcp_zde3,
    tcp_nzde3,
    tcp_a3,
    tcp_aa3,
    tcp_aae3,
    tcp_T1_3,
    tcp_zd3,
    tcp_zF3,
    tcp_T2_3,
    tcp_T3_3,
    tcp_nT2_3,
    tcp_T12_3,
    tcp_RS3,
    tcp_z4,
    tcp_W4,
    tcp_Xw4,
    tcp_F0_4,
    tcp_F1_4,
    tcp_F2_4,
    tcp_zde4,
    tcp_nzde4,
    tcp_a4,
    tcp_aa4,
    tcp_aae4,
    tcp_T1_4,
    tcp_zd4,
    tcp_zF4,
    tcp_T2_4,
    tcp_T3_4,
    tcp_nT2_4,
    tcp_T12_4,
    tcp_RS4,
    tcp_Xe,
    tcp_Sv,
    tcp_Kv,
    tcp_Ju2,
    tcp_Ju22,
    tcp_KJ,
    tcp_SJ,
    tcp_eta,
    tcp_G1,
    tcp_nRS2,
    tcp_G2,
    tcp_G3,
    tcp_neta,
    tcp_G4,
    tcp_hRS4,
    tcp_Gam]
  rfl

end CKLaneN23.CT


