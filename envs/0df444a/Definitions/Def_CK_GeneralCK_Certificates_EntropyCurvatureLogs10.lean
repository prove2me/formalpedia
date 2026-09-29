-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs10
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLogs10
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:42:11.074761+00:00
-- url     : https://prove2.me/theorems/e0edfc67-7eee-49ce-be9f-3f7ead5a9ad8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLogs10` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLogs10` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLogs10` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLogs10 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLogs10.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureBounds

namespace GeneralCK.Certificates.EntropyCurvature
open Mixed GeneralCK.EntropyCurvature

theorem log_v_160 : (806147181 / 250000000) ≤ -Real.log (6109 / 153600) ∧
    -Real.log (6109 / 153600) ≤ (3224588729 / 1000000000) := by
  have h := checkLog_sound (w := (3491 / 15709)) (n := 12)
    (lo := (113000001 / 250000000)) (hi := (90400001 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 6109) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(9600 / 6109) = 1/(6109 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_160 : (40584663 / 1000000000) ≤ -Real.log (147491 / 153600) ∧
    -Real.log (147491 / 153600) ≤ (5073083 / 125000000) := by
  have h := checkLog_sound (w := (6109 / 301091)) (n := 12)
    (lo := (40584663 / 1000000000)) (hi := (5073083 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 147491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153600 / 147491) = 1/(147491 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_160 : (159200203 / 100000000) ≤ xi (6109 / 153600) ∧ xi (6109 / 153600) ≤ (1592002033 / 1000000000) ∧
    (3265173387 / 2000000000) ≤ kap (6109 / 153600) ∧ kap (6109 / 153600) ≤ (3265173393 / 2000000000) := by
  have h := endpoint_bounds (v := ((6109 / 153600) : ℝ)) (by norm_num) (by norm_num)
    log_v_160.1 (by convert! log_c_160.1 using 1; norm_num)
    log_v_160.2 (by convert! log_c_160.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_161 : (3213640527 / 1000000000) ≤ -Real.log (1647 / 40960) ∧
    -Real.log (1647 / 40960) ≤ (803410133 / 250000000) := by
  have h := checkLog_sound (w := (913 / 4207)) (n := 12)
    (lo := (441051807 / 1000000000)) (hi := (13782869 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1647) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2560 / 1647) = 1/(1647 / 40960) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_161 : (41040727 / 1000000000) ≤ -Real.log (39313 / 40960) ∧
    -Real.log (39313 / 40960) ≤ (5130091 / 125000000) := by
  have h := checkLog_sound (w := (1647 / 80273)) (n := 12)
    (lo := (41040727 / 1000000000)) (hi := (5130091 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40960 / 39313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40960 / 39313) = 1/(39313 / 40960) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_161 : (3172599799 / 2000000000) ≤ xi (1647 / 40960) ∧ xi (1647 / 40960) ≤ (634519961 / 400000000) ∧
    (1627340627 / 1000000000) ≤ kap (1647 / 40960) ∧ kap (1647 / 40960) ≤ (162734063 / 100000000) := by
  have h := endpoint_bounds (v := ((1647 / 40960) : ℝ)) (by norm_num) (by norm_num)
    log_v_161.1 (by convert! log_c_161.1 using 1; norm_num)
    log_v_161.2 (by convert! log_c_161.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_162 : (640562179 / 200000000) ≤ -Real.log (12487 / 307200) ∧
    -Real.log (12487 / 307200) ≤ (32028109 / 10000000) := by
  have h := checkLog_sound (w := (6713 / 31687)) (n := 12)
    (lo := (17208887 / 40000000)) (hi := (13444443 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 12487) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(19200 / 12487) = 1/(12487 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_162 : (41496999 / 1000000000) ≤ -Real.log (294713 / 307200) ∧
    -Real.log (294713 / 307200) ≤ (41497 / 1000000) := by
  have h := checkLog_sound (w := (12487 / 601913)) (n := 12)
    (lo := (41496999 / 1000000000)) (hi := (41497 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 294713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 294713) = 1/(294713 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_162 : (632262779 / 400000000) ≤ xi (12487 / 307200) ∧ xi (12487 / 307200) ≤ (3161313901 / 2000000000) ∧
    (1622153947 / 1000000000) ≤ kap (12487 / 307200) ∧ kap (12487 / 307200) ≤ (32443079 / 20000000) := by
  have h := endpoint_bounds (v := ((12487 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_162.1 (by convert! log_c_162.1 using 1; norm_num)
    log_v_162.2 (by convert! log_c_162.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_163 : (319209729 / 100000000) ≤ -Real.log (25243 / 614400) ∧
    -Real.log (25243 / 614400) ≤ (638419459 / 200000000) := by
  have h := checkLog_sound (w := (13157 / 63643)) (n := 12)
    (lo := (41950857 / 100000000)) (hi := (419508571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 25243) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(38400 / 25243) = 1/(25243 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_163 : (1048837 / 25000000) ≤ -Real.log (589157 / 614400) ∧
    -Real.log (589157 / 614400) ≤ (41953481 / 1000000000) := by
  have h := checkLog_sound (w := (25243 / 1203557)) (n := 12)
    (lo := (1048837 / 25000000)) (hi := (41953481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 589157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 589157) = 1/(589157 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_163 : (3150143809 / 2000000000) ≤ xi (25243 / 614400) ∧ xi (25243 / 614400) ≤ (630028763 / 400000000) ∧
    (323405077 / 200000000) ≤ kap (25243 / 614400) ∧ kap (25243 / 614400) ≤ (404256347 / 250000000) := by
  have h := endpoint_bounds (v := ((25243 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_163.1 (by convert! log_c_163.1 using 1; norm_num)
    log_v_163.2 (by convert! log_c_163.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_164 : (3181497249 / 1000000000) ≤ -Real.log (1063 / 25600) ∧
    -Real.log (1063 / 25600) ≤ (1590748627 / 500000000) := by
  have h := checkLog_sound (w := (537 / 2663)) (n := 12)
    (lo := (408908529 / 1000000000)) (hi := (40890853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1063) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1063) = 1/(1063 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_164 : (42410169 / 1000000000) ≤ -Real.log (24537 / 25600) ∧
    -Real.log (24537 / 25600) ≤ (4241017 / 100000000) := by
  have h := checkLog_sound (w := (1063 / 50137)) (n := 12)
    (lo := (42410169 / 1000000000)) (hi := (4241017 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25600 / 24537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25600 / 24537) = 1/(24537 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_164 : (3139087079 / 2000000000) ≤ xi (1063 / 25600) ∧ xi (1063 / 25600) ≤ (627817417 / 400000000) ∧
    (1611953709 / 1000000000) ≤ kap (1063 / 25600) ∧ kap (1063 / 25600) ≤ (100747107 / 62500000) := by
  have h := endpoint_bounds (v := ((1063 / 25600) : ℝ)) (by norm_num) (by norm_num)
    log_v_164.1 (by convert! log_c_164.1 using 1; norm_num)
    log_v_164.2 (by convert! log_c_164.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_165 : (3171008393 / 1000000000) ≤ -Real.log (25781 / 614400) ∧
    -Real.log (25781 / 614400) ≤ (1585504199 / 500000000) := by
  have h := checkLog_sound (w := (12619 / 64181)) (n := 12)
    (lo := (398419673 / 1000000000)) (hi := (199209837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 25781) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(38400 / 25781) = 1/(25781 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_165 : (21433533 / 500000000) ≤ -Real.log (588619 / 614400) ∧
    -Real.log (588619 / 614400) ≤ (42867067 / 1000000000) := by
  have h := checkLog_sound (w := (25781 / 1203019)) (n := 12)
    (lo := (21433533 / 500000000)) (hi := (42867067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 588619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 588619) = 1/(588619 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_165 : (1564070663 / 1000000000) ≤ xi (25781 / 614400) ∧ xi (25781 / 614400) ≤ (782035333 / 500000000) ∧
    (3213875459 / 2000000000) ≤ kap (25781 / 614400) ∧ kap (25781 / 614400) ≤ (642775093 / 400000000) := by
  have h := endpoint_bounds (v := ((25781 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_165.1 (by convert! log_c_165.1 using 1; norm_num)
    log_v_165.2 (by convert! log_c_165.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_166 : (3160628411 / 1000000000) ≤ -Real.log (521 / 12288) ∧
    -Real.log (521 / 12288) ≤ (49384819 / 15625000) := by
  have h := checkLog_sound (w := (247 / 1289)) (n := 12)
    (lo := (388039691 / 1000000000)) (hi := (97009923 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((768 / 521) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(768 / 521) = 1/(521 / 12288) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_166 : (10831043 / 250000000) ≤ -Real.log (11767 / 12288) ∧
    -Real.log (11767 / 12288) ≤ (43324173 / 1000000000) := by
  have h := checkLog_sound (w := (521 / 24055)) (n := 12)
    (lo := (10831043 / 250000000)) (hi := (43324173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12288 / 11767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12288 / 11767) = 1/(11767 / 12288) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_166 : (1558652119 / 1000000000) ≤ xi (521 / 12288) ∧ xi (521 / 12288) ≤ (779326061 / 500000000) ∧
    (3203952583 / 2000000000) ≤ kap (521 / 12288) ∧ kap (521 / 12288) ≤ (3203952589 / 2000000000) := by
  have h := endpoint_bounds (v := ((521 / 12288) : ℝ)) (by norm_num) (by norm_num)
    log_v_166.1 (by convert! log_c_166.1 using 1; norm_num)
    log_v_166.2 (by convert! log_c_166.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_167 : (3150355067 / 1000000000) ≤ -Real.log (8773 / 204800) ∧
    -Real.log (8773 / 204800) ≤ (24612149 / 7812500) := by
  have h := checkLog_sound (w := (4027 / 21573)) (n := 12)
    (lo := (377766347 / 1000000000)) (hi := (94441587 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 8773) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12800 / 8773) = 1/(8773 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_167 : (2736343 / 62500000) ≤ -Real.log (196027 / 204800) ∧
    -Real.log (196027 / 204800) ≤ (43781489 / 1000000000) := by
  have h := checkLog_sound (w := (8773 / 400827)) (n := 12)
    (lo := (2736343 / 62500000)) (hi := (43781489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204800 / 196027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204800 / 196027) = 1/(196027 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_167 : (1553286789 / 1000000000) ≤ xi (8773 / 204800) ∧ xi (8773 / 204800) ≤ (194160849 / 125000000) ∧
    (638827311 / 400000000) ≤ kap (8773 / 204800) ∧ kap (8773 / 204800) ≤ (3194136561 / 2000000000) := by
  have h := endpoint_bounds (v := ((8773 / 204800) : ℝ)) (by norm_num) (by norm_num)
    log_v_167.1 (by convert! log_c_167.1 using 1; norm_num)
    log_v_167.2 (by convert! log_c_167.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_168 : (3140186193 / 1000000000) ≤ -Real.log (6647 / 153600) ∧
    -Real.log (6647 / 153600) ≤ (1570093099 / 500000000) := by
  have h := checkLog_sound (w := (2953 / 16247)) (n := 12)
    (lo := (367597473 / 1000000000)) (hi := (183798737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 6647) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(9600 / 6647) = 1/(6647 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_168 : (11059753 / 250000000) ≤ -Real.log (146953 / 153600) ∧
    -Real.log (146953 / 153600) ≤ (44239013 / 1000000000) := by
  have h := checkLog_sound (w := (6647 / 300553)) (n := 12)
    (lo := (11059753 / 250000000)) (hi := (44239013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 146953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153600 / 146953) = 1/(146953 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_168 : (154797359 / 100000000) ≤ xi (6647 / 153600) ∧ xi (6647 / 153600) ≤ (1547973593 / 1000000000) ∧
    (636885041 / 400000000) ≤ kap (6647 / 153600) ∧ kap (6647 / 153600) ≤ (3184425211 / 2000000000) := by
  have h := endpoint_bounds (v := ((6647 / 153600) : ℝ)) (by norm_num) (by norm_num)
    log_v_168.1 (by convert! log_c_168.1 using 1; norm_num)
    log_v_168.2 (by convert! log_c_168.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_169 : (782529921 / 250000000) ≤ -Real.log (26857 / 614400) ∧
    -Real.log (26857 / 614400) ≤ (3130119689 / 1000000000) := by
  have h := checkLog_sound (w := (11543 / 65257)) (n := 12)
    (lo := (89382741 / 250000000)) (hi := (71506193 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 26857) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(38400 / 26857) = 1/(26857 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_169 : (44696747 / 1000000000) ≤ -Real.log (587543 / 614400) ∧
    -Real.log (587543 / 614400) ≤ (11174187 / 250000000) := by
  have h := checkLog_sound (w := (26857 / 1201943)) (n := 12)
    (lo := (44696747 / 1000000000)) (hi := (11174187 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 587543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 587543) = 1/(587543 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_169 : (385677867 / 250000000) ≤ xi (26857 / 614400) ∧ xi (26857 / 614400) ≤ (1542711471 / 1000000000) ∧
    (3174816431 / 2000000000) ≤ kap (26857 / 614400) ∧ kap (26857 / 614400) ≤ (3174816437 / 2000000000) := by
  have h := endpoint_bounds (v := ((26857 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_169.1 (by convert! log_c_169.1 using 1; norm_num)
    log_v_169.2 (by convert! log_c_169.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_170 : (1560076751 / 500000000) ≤ -Real.log (4521 / 102400) ∧
    -Real.log (4521 / 102400) ≤ (3120153507 / 1000000000) := by
  have h := checkLog_sound (w := (1879 / 10921)) (n := 12)
    (lo := (173782391 / 500000000)) (hi := (347564783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4521) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 4521) = 1/(4521 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_170 : (4515469 / 100000000) ≤ -Real.log (97879 / 102400) ∧
    -Real.log (97879 / 102400) ≤ (45154691 / 1000000000) := by
  have h := checkLog_sound (w := (4521 / 200279)) (n := 12)
    (lo := (4515469 / 100000000)) (hi := (45154691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102400 / 97879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102400 / 97879) = 1/(97879 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_170 : (3074998811 / 2000000000) ≤ xi (4521 / 102400) ∧ xi (4521 / 102400) ≤ (3074998817 / 2000000000) ∧
    (98915881 / 62500000) ≤ kap (4521 / 102400) ∧ kap (4521 / 102400) ≤ (1582654099 / 1000000000) := by
  have h := endpoint_bounds (v := ((4521 / 102400) : ℝ)) (by norm_num) (by norm_num)
    log_v_170.1 (by convert! log_c_170.1 using 1; norm_num)
    log_v_170.2 (by convert! log_c_170.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_171 : (12402057 / 4000000) ≤ -Real.log (1729 / 38400) ∧
    -Real.log (1729 / 38400) ≤ (620102851 / 200000000) := by
  have h := checkLog_sound (w := (671 / 4129)) (n := 12)
    (lo := (32792553 / 100000000)) (hi := (327925531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2400 / 1729) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2400 / 1729) = 1/(1729 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_171 : (46071207 / 1000000000) ≤ -Real.log (36671 / 38400) ∧
    -Real.log (36671 / 38400) ≤ (5758901 / 125000000) := by
  have h := checkLog_sound (w := (1729 / 75071)) (n := 12)
    (lo := (46071207 / 1000000000)) (hi := (5758901 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 36671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38400 / 36671) = 1/(36671 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_171 : (1527221521 / 1000000000) ≤ xi (1729 / 38400) ∧ xi (1729 / 38400) ≤ (381805381 / 250000000) ∧
    (3146585457 / 2000000000) ≤ kap (1729 / 38400) ∧ kap (1729 / 38400) ≤ (3146585463 / 2000000000) := by
  have h := endpoint_bounds (v := ((1729 / 38400) : ℝ)) (by norm_num) (by norm_num)
    log_v_171.1 (by convert! log_c_171.1 using 1; norm_num)
    log_v_171.2 (by convert! log_c_171.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_172 : (1540626641 / 500000000) ≤ -Real.log (14101 / 307200) ∧
    -Real.log (14101 / 307200) ≤ (3081253287 / 1000000000) := by
  have h := checkLog_sound (w := (5099 / 33301)) (n := 12)
    (lo := (154332281 / 500000000)) (hi := (308664563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 14101) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(19200 / 14101) = 1/(14101 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_172 : (9397713 / 200000000) ≤ -Real.log (293099 / 307200) ∧
    -Real.log (293099 / 307200) ≤ (23494283 / 500000000) := by
  have h := checkLog_sound (w := (14101 / 600299)) (n := 12)
    (lo := (9397713 / 200000000)) (hi := (23494283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 293099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 293099) = 1/(293099 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_172 : (758566179 / 500000000) ≤ xi (14101 / 307200) ∧ xi (14101 / 307200) ≤ (1517132361 / 1000000000) ∧
    (3128241847 / 2000000000) ≤ kap (14101 / 307200) ∧ kap (14101 / 307200) ≤ (3128241853 / 2000000000) := by
  have h := endpoint_bounds (v := ((14101 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_172.1 (by convert! log_c_172.1 using 1; norm_num)
    log_v_172.2 (by convert! log_c_172.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_173 : (1531178149 / 500000000) ≤ -Real.log (479 / 10240) ∧
    -Real.log (479 / 10240) ≤ (3062356303 / 1000000000) := by
  have h := checkLog_sound (w := (161 / 1119)) (n := 12)
    (lo := (144883789 / 500000000)) (hi := (289767579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 479) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 479) = 1/(479 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_173 : (9581353 / 200000000) ≤ -Real.log (9761 / 10240) ∧
    -Real.log (9761 / 10240) ≤ (23953383 / 500000000) := by
  have h := checkLog_sound (w := (479 / 20001)) (n := 12)
    (lo := (9581353 / 200000000)) (hi := (23953383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 9761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 9761) = 1/(9761 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_173 : (753612383 / 500000000) ≤ xi (479 / 10240) ∧ xi (479 / 10240) ≤ (1507224769 / 1000000000) ∧
    (3110263063 / 2000000000) ≤ kap (479 / 10240) ∧ kap (479 / 10240) ≤ (3110263069 / 2000000000) := by
  have h := endpoint_bounds (v := ((479 / 10240) : ℝ)) (by norm_num) (by norm_num)
    log_v_173.1 (by convert! log_c_173.1 using 1; norm_num)
    log_v_173.2 (by convert! log_c_173.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_174 : (1521904899 / 500000000) ≤ -Real.log (14639 / 307200) ∧
    -Real.log (14639 / 307200) ≤ (3043809803 / 1000000000) := by
  have h := checkLog_sound (w := (4561 / 33839)) (n := 12)
    (lo := (135610539 / 500000000)) (hi := (271221079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 14639) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(19200 / 14639) = 1/(14639 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_174 : (48825809 / 1000000000) ≤ -Real.log (292561 / 307200) ∧
    -Real.log (292561 / 307200) ≤ (4882581 / 100000000) := by
  have h := checkLog_sound (w := (14639 / 599761)) (n := 12)
    (lo := (48825809 / 1000000000)) (hi := (4882581 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 292561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 292561) = 1/(292561 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_174 : (748745997 / 500000000) ≤ xi (14639 / 307200) ∧ xi (14639 / 307200) ≤ (1497491997 / 1000000000) ∧
    (3092635607 / 2000000000) ≤ kap (14639 / 307200) ∧ kap (14639 / 307200) ≤ (3092635613 / 2000000000) := by
  have h := endpoint_bounds (v := ((14639 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_174.1 (by convert! log_c_174.1 using 1; norm_num)
    log_v_174.2 (by convert! log_c_174.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_175 : (3025601017 / 1000000000) ≤ -Real.log (3727 / 76800) ∧
    -Real.log (3727 / 76800) ≤ (1512800511 / 500000000) := by
  have h := checkLog_sound (w := (1073 / 8527)) (n := 12)
    (lo := (253012297 / 1000000000)) (hi := (126506149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4800 / 3727) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4800 / 3727) = 1/(3727 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_175 : (24872849 / 500000000) ≤ -Real.log (73073 / 76800) ∧
    -Real.log (73073 / 76800) ≤ (49745699 / 1000000000) := by
  have h := checkLog_sound (w := (3727 / 149873)) (n := 12)
    (lo := (24872849 / 500000000)) (hi := (49745699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 73073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76800 / 73073) = 1/(73073 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_175 : (1487927659 / 1000000000) ≤ xi (3727 / 76800) ∧ xi (3727 / 76800) ≤ (743963831 / 500000000) ∧
    (615069343 / 400000000) ≤ kap (3727 / 76800) ∧ kap (3727 / 76800) ≤ (3075346721 / 2000000000) := by
  have h := endpoint_bounds (v := ((3727 / 76800) : ℝ)) (by norm_num) (by norm_num)
    log_v_175.1 (by convert! log_c_175.1 using 1; norm_num)
    log_v_175.2 (by convert! log_c_175.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.EntropyCurvature


