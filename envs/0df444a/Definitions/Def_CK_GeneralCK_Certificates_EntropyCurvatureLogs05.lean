-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs05
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLogs05
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:44:02.128682+00:00
-- url     : https://prove2.me/theorems/2ffc8a39-54a6-4916-8918-f40e7f23a3aa
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLogs05` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLogs05` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLogs05` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLogs05 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLogs05.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureBounds

namespace GeneralCK.Certificates.EntropyCurvature
open Mixed GeneralCK.EntropyCurvature

theorem log_v_80 : (2033909797 / 500000000) ≤ -Real.log (42061 / 2457600) ∧
    -Real.log (42061 / 2457600) ≤ (10169549 / 2500000) := by
  have h := checkLog_sound (w := (34739 / 118861)) (n := 12)
    (lo := (301041847 / 500000000)) (hi := (120416739 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 42061) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(76800 / 42061) = 1/(42061 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_80 : (17262813 / 1000000000) ≤ -Real.log (2415539 / 2457600) ∧
    -Real.log (2415539 / 2457600) ≤ (8631407 / 500000000) := by
  have h := checkLog_sound (w := (42061 / 4873139)) (n := 12)
    (lo := (17262813 / 1000000000)) (hi := (8631407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2457600 / 2415539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2457600 / 2415539) = 1/(2415539 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_80 : (202527839 / 100000000) ≤ xi (42061 / 2457600) ∧ xi (42061 / 2457600) ≤ (4050556787 / 2000000000) ∧
    (4085082407 / 2000000000) ≤ kap (42061 / 2457600) ∧ kap (42061 / 2457600) ≤ (2042541207 / 1000000000) := by
  have h := endpoint_bounds (v := ((42061 / 2457600) : ℝ)) (by norm_num) (by norm_num)
    log_v_80.1 (by convert! log_c_80.1 using 1; norm_num)
    log_v_80.2 (by convert! log_c_80.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_81 : (812288897 / 200000000) ≤ -Real.log (1411 / 81920) ∧
    -Real.log (1411 / 81920) ≤ (4061444491 / 1000000000) := by
  have h := checkLog_sound (w := (1149 / 3971)) (n := 12)
    (lo := (119141717 / 200000000)) (hi := (297854293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1411) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2560 / 1411) = 1/(1411 / 81920) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_81 : (17374181 / 1000000000) ≤ -Real.log (80509 / 81920) ∧
    -Real.log (80509 / 81920) ≤ (8687091 / 500000000) := by
  have h := checkLog_sound (w := (1411 / 162429)) (n := 12)
    (lo := (17374181 / 1000000000)) (hi := (8687091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81920 / 80509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81920 / 80509) = 1/(80509 / 81920) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_81 : (4044070303 / 2000000000) ≤ xi (1411 / 81920) ∧ xi (1411 / 81920) ≤ (404407031 / 200000000) ∧
    (2039409333 / 1000000000) ≤ kap (1411 / 81920) ∧ kap (1411 / 81920) ≤ (4078818673 / 2000000000) := by
  have h := endpoint_bounds (v := ((1411 / 81920) : ℝ)) (by norm_num) (by norm_num)
    log_v_81.1 (by convert! log_c_81.1 using 1; norm_num)
    log_v_81.2 (by convert! log_c_81.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_82 : (4055109761 / 1000000000) ≤ -Real.log (42599 / 2457600) ∧
    -Real.log (42599 / 2457600) ≤ (4055109767 / 1000000000) := by
  have h := checkLog_sound (w := (34201 / 119399)) (n := 12)
    (lo := (589373861 / 1000000000)) (hi := (294686931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 42599) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(76800 / 42599) = 1/(42599 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_82 : (8742781 / 500000000) ≤ -Real.log (2415001 / 2457600) ∧
    -Real.log (2415001 / 2457600) ≤ (17485563 / 1000000000) := by
  have h := checkLog_sound (w := (42599 / 4872601)) (n := 12)
    (lo := (8742781 / 500000000)) (hi := (17485563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2457600 / 2415001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2457600 / 2415001) = 1/(2415001 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_82 : (2018812099 / 1000000000) ≤ xi (42599 / 2457600) ∧ xi (42599 / 2457600) ≤ (807524841 / 400000000) ∧
    (4072595323 / 2000000000) ≤ kap (42599 / 2457600) ∧ kap (42599 / 2457600) ≤ (407259533 / 200000000) := by
  have h := endpoint_bounds (v := ((42599 / 2457600) : ℝ)) (by norm_num) (by norm_num)
    log_v_82.1 (by convert! log_c_82.1 using 1; norm_num)
    log_v_82.2 (by convert! log_c_82.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_83 : (4048814913 / 1000000000) ≤ -Real.log (10717 / 614400) ∧
    -Real.log (10717 / 614400) ≤ (4048814919 / 1000000000) := by
  have h := checkLog_sound (w := (8483 / 29917)) (n := 12)
    (lo := (583079013 / 1000000000)) (hi := (291539507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 10717) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19200 / 10717) = 1/(10717 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_83 : (4399239 / 250000000) ≤ -Real.log (603683 / 614400) ∧
    -Real.log (603683 / 614400) ≤ (17596957 / 1000000000) := by
  have h := checkLog_sound (w := (10717 / 1218083)) (n := 12)
    (lo := (4399239 / 250000000)) (hi := (17596957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 603683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 603683) = 1/(603683 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_83 : (1007804489 / 500000000) ≤ xi (10717 / 614400) ∧ xi (10717 / 614400) ≤ (4031217963 / 2000000000) ∧
    (4066411869 / 2000000000) ≤ kap (10717 / 614400) ∧ kap (10717 / 614400) ≤ (1016602969 / 500000000) := by
  have h := endpoint_bounds (v := ((10717 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_83.1 (by convert! log_c_83.1 using 1; norm_num)
    log_v_83.2 (by convert! log_c_83.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_84 : (2021279721 / 500000000) ≤ -Real.log (14379 / 819200) ∧
    -Real.log (14379 / 819200) ≤ (505319931 / 125000000) := by
  have h := checkLog_sound (w := (11221 / 39979)) (n := 12)
    (lo := (288411771 / 500000000)) (hi := (576823543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25600 / 14379) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(25600 / 14379) = 1/(14379 / 819200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_84 : (17708361 / 1000000000) ≤ -Real.log (804821 / 819200) ∧
    -Real.log (804821 / 819200) ≤ (8854181 / 500000000) := by
  have h := checkLog_sound (w := (14379 / 1624021)) (n := 12)
    (lo := (17708361 / 1000000000)) (hi := (8854181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819200 / 804821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819200 / 804821) = 1/(804821 / 819200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_84 : (100621277 / 50000000) ≤ xi (14379 / 819200) ∧ xi (14379 / 819200) ≤ (4024851087 / 2000000000) ∧
    (4060267803 / 2000000000) ≤ kap (14379 / 819200) ∧ kap (14379 / 819200) ≤ (406026781 / 200000000) := by
  have h := endpoint_bounds (v := ((14379 / 819200) : ℝ)) (by norm_num) (by norm_num)
    log_v_84.1 (by convert! log_c_84.1 using 1; norm_num)
    log_v_84.2 (by convert! log_c_84.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_85 : (4036342859 / 1000000000) ≤ -Real.log (21703 / 1228800) ∧
    -Real.log (21703 / 1228800) ≤ (807268573 / 200000000) := by
  have h := checkLog_sound (w := (16697 / 60103)) (n := 12)
    (lo := (570606959 / 1000000000)) (hi := (7132587 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 21703) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(38400 / 21703) = 1/(21703 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_85 : (17819779 / 1000000000) ≤ -Real.log (1207097 / 1228800) ∧
    -Real.log (1207097 / 1228800) ≤ (890989 / 50000000) := by
  have h := checkLog_sound (w := (21703 / 2435897)) (n := 12)
    (lo := (17819779 / 1000000000)) (hi := (890989 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 1207097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 1207097) = 1/(1207097 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_85 : (4018523079 / 2000000000) ≤ xi (21703 / 1228800) ∧ xi (21703 / 1228800) ≤ (2009261543 / 1000000000) ∧
    (2027081319 / 1000000000) ≤ kap (21703 / 1228800) ∧ kap (21703 / 1228800) ≤ (810832529 / 400000000) := by
  have h := endpoint_bounds (v := ((21703 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_85.1 (by convert! log_c_85.1 using 1; norm_num)
    log_v_85.2 (by convert! log_c_85.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_86 : (1007541171 / 250000000) ≤ -Real.log (1747 / 98304) ∧
    -Real.log (1747 / 98304) ≤ (403016469 / 100000000) := by
  have h := checkLog_sound (w := (1325 / 4819)) (n := 12)
    (lo := (35276799 / 62500000)) (hi := (112885757 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3072 / 1747) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3072 / 1747) = 1/(1747 / 98304) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_86 : (1793121 / 100000000) ≤ -Real.log (96557 / 98304) ∧
    -Real.log (96557 / 98304) ≤ (17931211 / 1000000000) := by
  have h := checkLog_sound (w := (1747 / 194861)) (n := 12)
    (lo := (1793121 / 100000000)) (hi := (17931211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98304 / 96557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98304 / 96557) = 1/(96557 / 98304) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_86 : (4012233473 / 2000000000) ≤ xi (1747 / 98304) ∧ xi (1747 / 98304) ≤ (100305837 / 50000000) ∧
    (2024047947 / 1000000000) ≤ kap (1747 / 98304) ∧ kap (1747 / 98304) ≤ (4048095901 / 2000000000) := by
  have h := endpoint_bounds (v := ((1747 / 98304) : ℝ)) (by norm_num) (by norm_num)
    log_v_86.1 (by convert! log_c_86.1 using 1; norm_num)
    log_v_86.2 (by convert! log_c_86.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_87 : (1006006111 / 250000000) ≤ -Real.log (1831 / 102400) ∧
    -Real.log (1831 / 102400) ≤ (80480489 / 20000000) := by
  have h := checkLog_sound (w := (1369 / 5031)) (n := 12)
    (lo := (17446517 / 31250000)) (hi := (111657709 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1831) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 1831) = 1/(1831 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_87 : (18042653 / 1000000000) ≤ -Real.log (100569 / 102400) ∧
    -Real.log (100569 / 102400) ≤ (9021327 / 500000000) := by
  have h := checkLog_sound (w := (1831 / 202969)) (n := 12)
    (lo := (18042653 / 1000000000)) (hi := (9021327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102400 / 100569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102400 / 100569) = 1/(100569 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_87 : (400598179 / 200000000) ≤ xi (1831 / 102400) ∧ xi (1831 / 102400) ≤ (4005981797 / 2000000000) ∧
    (4042067097 / 2000000000) ≤ kap (1831 / 102400) ∧ kap (1831 / 102400) ≤ (126314597 / 62500000) := by
  have h := endpoint_bounds (v := ((1831 / 102400) : ℝ)) (by norm_num) (by norm_num)
    log_v_87.1 (by convert! log_c_87.1 using 1; norm_num)
    log_v_87.2 (by convert! log_c_87.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_88 : (4011855927 / 1000000000) ≤ -Real.log (22241 / 1228800) ∧
    -Real.log (22241 / 1228800) ≤ (4011855933 / 1000000000) := by
  have h := checkLog_sound (w := (16159 / 60641)) (n := 12)
    (lo := (546120027 / 1000000000)) (hi := (136530007 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 22241) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(38400 / 22241) = 1/(22241 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_88 : (2283197 / 125000000) ≤ -Real.log (1206559 / 1228800) ∧
    -Real.log (1206559 / 1228800) ≤ (18265577 / 1000000000) := by
  have h := checkLog_sound (w := (22241 / 2435359)) (n := 12)
    (lo := (2283197 / 125000000)) (hi := (18265577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 1206559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 1206559) = 1/(1206559 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_88 : (79871807 / 40000000) ≤ xi (22241 / 1228800) ∧ xi (22241 / 1228800) ≤ (3993590357 / 2000000000) ∧
    (4030121503 / 2000000000) ≤ kap (22241 / 1228800) ∧ kap (22241 / 1228800) ≤ (403012151 / 200000000) := by
  have h := endpoint_bounds (v := ((22241 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_88.1 (by convert! log_c_88.1 using 1; norm_num)
    log_v_88.2 (by convert! log_c_88.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_89 : (499979213 / 125000000) ≤ -Real.log (2251 / 122880) ∧
    -Real.log (2251 / 122880) ≤ (399983371 / 100000000) := by
  have h := checkLog_sound (w := (1589 / 6091)) (n := 12)
    (lo := (133524451 / 250000000)) (hi := (106819561 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3840 / 2251) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3840 / 2251) = 1/(2251 / 122880) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_89 : (18488549 / 1000000000) ≤ -Real.log (120629 / 122880) ∧
    -Real.log (120629 / 122880) ≤ (369771 / 20000000) := by
  have h := checkLog_sound (w := (2251 / 243509)) (n := 12)
    (lo := (18488549 / 1000000000)) (hi := (369771 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122880 / 120629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122880 / 120629) = 1/(120629 / 122880) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_89 : (1990672577 / 1000000000) ≤ xi (2251 / 122880) ∧ xi (2251 / 122880) ≤ (3981345161 / 2000000000) ∧
    (4018322253 / 2000000000) ≤ kap (2251 / 122880) ∧ kap (2251 / 122880) ≤ (200916113 / 100000000) := by
  have h := endpoint_bounds (v := ((2251 / 122880) : ℝ)) (by norm_num) (by norm_num)
    log_v_89.1 (by convert! log_c_89.1 using 1; norm_num)
    log_v_89.2 (by convert! log_c_89.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_90 : (39879543 / 10000000) ≤ -Real.log (7593 / 409600) ∧
    -Real.log (7593 / 409600) ≤ (1993977153 / 500000000) := by
  have h := checkLog_sound (w := (5207 / 20393)) (n := 12)
    (lo := (652773 / 1250000)) (hi := (522218401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 7593) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(12800 / 7593) = 1/(7593 / 409600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_90 : (4677893 / 250000000) ≤ -Real.log (402007 / 409600) ∧
    -Real.log (402007 / 409600) ≤ (18711573 / 1000000000) := by
  have h := checkLog_sound (w := (7593 / 811607)) (n := 12)
    (lo := (4677893 / 250000000)) (hi := (18711573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((409600 / 402007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(409600 / 402007) = 1/(402007 / 409600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_90 : (3969242727 / 2000000000) ≤ xi (7593 / 409600) ∧ xi (7593 / 409600) ≤ (1984621367 / 1000000000) ∧
    (250416617 / 125000000) ≤ kap (7593 / 409600) ∧ kap (7593 / 409600) ≤ (4006665879 / 2000000000) := by
  have h := endpoint_bounds (v := ((7593 / 409600) : ℝ)) (by norm_num) (by norm_num)
    log_v_90.1 (by convert! log_c_90.1 using 1; norm_num)
    log_v_90.2 (by convert! log_c_90.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_91 : (3976214361 / 1000000000) ≤ -Real.log (2881 / 153600) ∧
    -Real.log (2881 / 153600) ≤ (3976214367 / 1000000000) := by
  have h := checkLog_sound (w := (1919 / 7681)) (n := 12)
    (lo := (510478461 / 1000000000)) (hi := (255239231 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4800 / 2881) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4800 / 2881) = 1/(2881 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_91 : (4733661 / 250000000) ≤ -Real.log (150719 / 153600) ∧
    -Real.log (150719 / 153600) ≤ (3786929 / 200000000) := by
  have h := checkLog_sound (w := (2881 / 304319)) (n := 12)
    (lo := (4733661 / 250000000)) (hi := (3786929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 150719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153600 / 150719) = 1/(150719 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_91 : (989319929 / 500000000) ≤ xi (2881 / 153600) ∧ xi (2881 / 153600) ≤ (3957279723 / 2000000000) ∧
    (799029801 / 400000000) ≤ kap (2881 / 153600) ∧ kap (2881 / 153600) ≤ (998787253 / 500000000) := by
  have h := endpoint_bounds (v := ((2881 / 153600) : ℝ)) (by norm_num) (by norm_num)
    log_v_91.1 (by convert! log_c_91.1 using 1; norm_num)
    log_v_91.2 (by convert! log_c_91.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_92 : (3964610651 / 1000000000) ≤ -Real.log (23317 / 1228800) ∧
    -Real.log (23317 / 1228800) ≤ (3964610657 / 1000000000) := by
  have h := checkLog_sound (w := (15083 / 61717)) (n := 12)
    (lo := (498874751 / 1000000000)) (hi := (3897459 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 23317) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(38400 / 23317) = 1/(23317 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_92 : (9578883 / 500000000) ≤ -Real.log (1205483 / 1228800) ∧
    -Real.log (1205483 / 1228800) ≤ (19157767 / 1000000000) := by
  have h := checkLog_sound (w := (23317 / 2434283)) (n := 12)
    (lo := (9578883 / 500000000)) (hi := (19157767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 1205483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 1205483) = 1/(1205483 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_92 : (986363221 / 500000000) ≤ xi (23317 / 1228800) ∧ xi (23317 / 1228800) ≤ (3945452891 / 2000000000) ∧
    (3983768417 / 2000000000) ≤ kap (23317 / 1228800) ∧ kap (23317 / 1228800) ≤ (497971053 / 250000000) := by
  have h := endpoint_bounds (v := ((23317 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_92.1 (by convert! log_c_92.1 using 1; norm_num)
    log_v_92.2 (by convert! log_c_92.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_93 : (3953140043 / 1000000000) ≤ -Real.log (3931 / 204800) ∧
    -Real.log (3931 / 204800) ≤ (3953140049 / 1000000000) := by
  have h := checkLog_sound (w := (2469 / 10331)) (n := 12)
    (lo := (487404143 / 1000000000)) (hi := (30462759 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 3931) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6400 / 3931) = 1/(3931 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_93 : (9690469 / 500000000) ≤ -Real.log (200869 / 204800) ∧
    -Real.log (200869 / 204800) ≤ (19380939 / 1000000000) := by
  have h := checkLog_sound (w := (3931 / 405669)) (n := 12)
    (lo := (9690469 / 500000000)) (hi := (19380939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204800 / 200869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204800 / 200869) = 1/(200869 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_93 : (30732493 / 15625000) ≤ xi (3931 / 204800) ∧ xi (3931 / 204800) ≤ (3933759111 / 2000000000) ∧
    (3972520981 / 2000000000) ≤ kap (3931 / 204800) ∧ kap (3931 / 204800) ≤ (993130247 / 500000000) := by
  have h := endpoint_bounds (v := ((3931 / 204800) : ℝ)) (by norm_num) (by norm_num)
    log_v_93.1 (by convert! log_c_93.1 using 1; norm_num)
    log_v_93.2 (by convert! log_c_93.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_94 : (24636247 / 6250000) ≤ -Real.log (4771 / 245760) ∧
    -Real.log (4771 / 245760) ≤ (1970899763 / 500000000) := by
  have h := checkLog_sound (w := (2909 / 12451)) (n := 12)
    (lo := (23803181 / 50000000)) (hi := (476063621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7680 / 4771) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(7680 / 4771) = 1/(4771 / 245760) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_94 : (61263 / 3125000) ≤ -Real.log (240989 / 245760) ∧
    -Real.log (240989 / 245760) ≤ (19604161 / 1000000000) := by
  have h := checkLog_sound (w := (4771 / 486749)) (n := 12)
    (lo := (61263 / 3125000)) (hi := (19604161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245760 / 240989) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(245760 / 240989) = 1/(240989 / 245760) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_94 : (3922195359 / 2000000000) ≤ xi (4771 / 245760) ∧ xi (4771 / 245760) ≤ (1961097683 / 1000000000) ∧
    (24758773 / 12500000) ≤ kap (4771 / 245760) ∧ kap (4771 / 245760) ≤ (3961403687 / 2000000000) := by
  have h := endpoint_bounds (v := ((4771 / 245760) : ℝ)) (by norm_num) (by norm_num)
    log_v_94.1 (by convert! log_c_94.1 using 1; norm_num)
    log_v_94.2 (by convert! log_c_94.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_95 : (982646541 / 250000000) ≤ -Real.log (6031 / 307200) ∧
    -Real.log (6031 / 307200) ≤ (393058617 / 100000000) := by
  have h := checkLog_sound (w := (3569 / 15631)) (n := 12)
    (lo := (58106283 / 125000000)) (hi := (92970053 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 6031) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(9600 / 6031) = 1/(6031 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_95 : (2478429 / 125000000) ≤ -Real.log (301169 / 307200) ∧
    -Real.log (301169 / 307200) ≤ (19827433 / 1000000000) := by
  have h := checkLog_sound (w := (6031 / 608369)) (n := 12)
    (lo := (2478429 / 125000000)) (hi := (19827433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 301169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 301169) = 1/(301169 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_95 : (3910758731 / 2000000000) ≤ xi (6031 / 307200) ∧ xi (6031 / 307200) ≤ (1955379369 / 1000000000) ∧
    (987603399 / 500000000) ≤ kap (6031 / 307200) ∧ kap (6031 / 307200) ≤ (3950413603 / 2000000000) := by
  have h := endpoint_bounds (v := ((6031 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_95.1 (by convert! log_c_95.1 using 1; norm_num)
    log_v_95.2 (by convert! log_c_95.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.EntropyCurvature


