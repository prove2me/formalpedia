-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs03
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLogs03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:42:02.020594+00:00
-- url     : https://prove2.me/theorems/aee8b967-9008-42bd-9f32-a3944e040dce
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLogs03` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLogs03` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLogs03` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLogs03 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLogs03.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureBounds

namespace GeneralCK.Certificates.EntropyCurvature
open Mixed GeneralCK.EntropyCurvature

theorem log_v_48 : (429679907 / 100000000) ≤ -Real.log (11151 / 819200) ∧
    -Real.log (11151 / 819200) ≤ (4296799077 / 1000000000) := by
  have h := checkLog_sound (w := (1649 / 23951)) (n := 12)
    (lo := (13791599 / 100000000)) (hi := (137915991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 11151) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(12800 / 11151) = 1/(11151 / 819200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_48 : (6852777 / 500000000) ≤ -Real.log (808049 / 819200) ∧
    -Real.log (808049 / 819200) ≤ (2741111 / 200000000) := by
  have h := checkLog_sound (w := (11151 / 1627249)) (n := 12)
    (lo := (6852777 / 500000000)) (hi := (2741111 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819200 / 808049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819200 / 808049) = 1/(808049 / 819200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_48 : (856618703 / 400000000) ≤ xi (11151 / 819200) ∧ xi (11151 / 819200) ≤ (4283093523 / 2000000000) ∧
    (269406539 / 125000000) ≤ kap (11151 / 819200) ∧ kap (11151 / 819200) ≤ (538813079 / 250000000) := by
  have h := endpoint_bounds (v := ((11151 / 819200) : ℝ)) (by norm_num) (by norm_num)
    log_v_48.1 (by convert! log_c_48.1 using 1; norm_num)
    log_v_48.2 (by convert! log_c_48.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_49 : (268049381 / 62500000) ≤ -Real.log (16861 / 1228800) ∧
    -Real.log (16861 / 1228800) ≤ (4288790103 / 1000000000) := by
  have h := checkLog_sound (w := (2339 / 36061)) (n := 12)
    (lo := (16238377 / 125000000)) (hi := (129907017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 16861) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(19200 / 16861) = 1/(16861 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_49 : (13816527 / 1000000000) ≤ -Real.log (1211939 / 1228800) ∧
    -Real.log (1211939 / 1228800) ≤ (863533 / 62500000) := by
  have h := checkLog_sound (w := (16861 / 2440739)) (n := 12)
    (lo := (13816527 / 1000000000)) (hi := (863533 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 1211939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 1211939) = 1/(1211939 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_49 : (33398231 / 15625000) ≤ xi (16861 / 1228800) ∧ xi (16861 / 1228800) ≤ (534371697 / 250000000) ∧
    (4302606623 / 2000000000) ≤ kap (16861 / 1228800) ∧ kap (16861 / 1228800) ≤ (4302606631 / 2000000000) := by
  have h := endpoint_bounds (v := ((16861 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_49.1 (by convert! log_c_49.1 using 1; norm_num)
    log_v_49.2 (by convert! log_c_49.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_50 : (856168951 / 200000000) ≤ -Real.log (33991 / 2457600) ∧
    -Real.log (33991 / 2457600) ≤ (2140422381 / 500000000) := by
  have h := checkLog_sound (w := (4409 / 72391)) (n := 12)
    (lo := (4878467 / 40000000)) (hi := (30490419 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 33991) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(38400 / 33991) = 1/(33991 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_50 : (1740939 / 125000000) ≤ -Real.log (2423609 / 2457600) ∧
    -Real.log (2423609 / 2457600) ≤ (13927513 / 1000000000) := by
  have h := checkLog_sound (w := (33991 / 4881209)) (n := 12)
    (lo := (1740939 / 125000000)) (hi := (13927513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2457600 / 2423609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2457600 / 2423609) = 1/(2423609 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_50 : (2133458621 / 1000000000) ≤ xi (33991 / 2457600) ∧ xi (33991 / 2457600) ≤ (17067669 / 8000000) ∧
    (4294772267 / 2000000000) ≤ kap (33991 / 2457600) ∧ kap (33991 / 2457600) ≤ (171790891 / 80000000) := by
  have h := endpoint_bounds (v := ((33991 / 2457600) : ℝ)) (by norm_num) (by norm_num)
    log_v_50.1 (by convert! log_c_50.1 using 1; norm_num)
    log_v_50.2 (by convert! log_c_50.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_51 : (2136481023 / 500000000) ≤ -Real.log (571 / 40960) ∧
    -Real.log (571 / 40960) ≤ (4272962053 / 1000000000) := by
  have h := checkLog_sound (w := (69 / 1211)) (n := 12)
    (lo := (57039483 / 500000000)) (hi := (114078967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 571) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(640 / 571) = 1/(571 / 40960) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_51 : (1403851 / 100000000) ≤ -Real.log (40389 / 40960) ∧
    -Real.log (40389 / 40960) ≤ (14038511 / 1000000000) := by
  have h := checkLog_sound (w := (571 / 81349)) (n := 12)
    (lo := (1403851 / 100000000)) (hi := (14038511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40960 / 40389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40960 / 40389) = 1/(40389 / 40960) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_51 : (851784707 / 400000000) ≤ xi (571 / 40960) ∧ xi (571 / 40960) ≤ (4258923543 / 2000000000) ∧
    (1071750139 / 500000000) ≤ kap (571 / 40960) ∧ kap (571 / 40960) ≤ (1071750141 / 500000000) := by
  have h := endpoint_bounds (v := ((571 / 40960) : ℝ)) (by norm_num) (by norm_num)
    log_v_51.1 (by convert! log_c_51.1 using 1; norm_num)
    log_v_51.2 (by convert! log_c_51.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_52 : (1066285247 / 250000000) ≤ -Real.log (34529 / 2457600) ∧
    -Real.log (34529 / 2457600) ≤ (853028199 / 200000000) := by
  have h := checkLog_sound (w := (3871 / 72929)) (n := 12)
    (lo := (26564477 / 250000000)) (hi := (106257909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 34529) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(38400 / 34529) = 1/(34529 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_52 : (176869 / 12500000) ≤ -Real.log (2423071 / 2457600) ∧
    -Real.log (2423071 / 2457600) ≤ (14149521 / 1000000000) := by
  have h := checkLog_sound (w := (34529 / 4880671)) (n := 12)
    (lo := (176869 / 12500000)) (hi := (14149521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2457600 / 2423071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2457600 / 2423071) = 1/(2423071 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_52 : (4250991467 / 2000000000) ≤ xi (34529 / 2457600) ∧ xi (34529 / 2457600) ≤ (170039659 / 80000000) ∧
    (1069822627 / 500000000) ≤ kap (34529 / 2457600) ∧ kap (34529 / 2457600) ≤ (1069822629 / 500000000) := by
  have h := endpoint_bounds (v := ((34529 / 2457600) : ℝ)) (by norm_num) (by norm_num)
    log_v_52.1 (by convert! log_c_52.1 using 1; norm_num)
    log_v_52.2 (by convert! log_c_52.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_53 : (6811809 / 1600000) ≤ -Real.log (17399 / 1228800) ∧
    -Real.log (17399 / 1228800) ≤ (532172579 / 125000000) := by
  have h := checkLog_sound (w := (1801 / 36599)) (n := 12)
    (lo := (19699509 / 200000000)) (hi := (49248773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 17399) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(19200 / 17399) = 1/(17399 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_53 : (7130271 / 500000000) ≤ -Real.log (1211401 / 1228800) ∧
    -Real.log (1211401 / 1228800) ≤ (14260543 / 1000000000) := by
  have h := checkLog_sound (w := (17399 / 2440201)) (n := 12)
    (lo := (7130271 / 500000000)) (hi := (14260543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 1211401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 1211401) = 1/(1211401 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_53 : (2121560041 / 1000000000) ≤ xi (17399 / 1228800) ∧ xi (17399 / 1228800) ≤ (424312009 / 200000000) ∧
    (4271641167 / 2000000000) ≤ kap (17399 / 1228800) ∧ kap (17399 / 1228800) ≤ (170865647 / 80000000) := by
  have h := endpoint_bounds (v := ((17399 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_53.1 (by convert! log_c_53.1 using 1; norm_num)
    log_v_53.2 (by convert! log_c_53.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_54 : (2124840011 / 500000000) ≤ -Real.log (11689 / 819200) ∧
    -Real.log (11689 / 819200) ≤ (4249680029 / 1000000000) := by
  have h := checkLog_sound (w := (1111 / 24489)) (n := 12)
    (lo := (45398471 / 500000000)) (hi := (90796943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 11689) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(12800 / 11689) = 1/(11689 / 819200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_54 : (1796447 / 125000000) ≤ -Real.log (807511 / 819200) ∧
    -Real.log (807511 / 819200) ≤ (14371577 / 1000000000) := by
  have h := checkLog_sound (w := (11689 / 1626711)) (n := 12)
    (lo := (1796447 / 125000000)) (hi := (14371577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819200 / 807511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819200 / 807511) = 1/(807511 / 819200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_54 : (847061689 / 400000000) ≤ xi (11689 / 819200) ∧ xi (11689 / 819200) ≤ (4235308453 / 2000000000) ∧
    (2132025799 / 1000000000) ≤ kap (11689 / 819200) ∧ kap (11689 / 819200) ≤ (2132025803 / 1000000000) := by
  have h := endpoint_bounds (v := ((11689 / 819200) : ℝ)) (by norm_num) (by norm_num)
    log_v_54.1 (by convert! log_c_54.1 using 1; norm_num)
    log_v_54.2 (by convert! log_c_54.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_55 : (848407653 / 200000000) ≤ -Real.log (4417 / 307200) ∧
    -Real.log (4417 / 307200) ≤ (8285231 / 1953125) := by
  have h := checkLog_sound (w := (383 / 9217)) (n := 12)
    (lo := (16631037 / 200000000)) (hi := (41577593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4800 / 4417) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4800 / 4417) = 1/(4417 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_55 : (14482623 / 1000000000) ≤ -Real.log (302783 / 307200) ∧
    -Real.log (302783 / 307200) ≤ (226291 / 15625000) := by
  have h := checkLog_sound (w := (4417 / 609983)) (n := 12)
    (lo := (14482623 / 1000000000)) (hi := (226291 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 302783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 302783) = 1/(302783 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_55 : (4227555641 / 2000000000) ≤ xi (4417 / 307200) ∧ xi (4417 / 307200) ≤ (4227555649 / 2000000000) ∧
    (532065111 / 250000000) ≤ kap (4417 / 307200) ∧ kap (4417 / 307200) ≤ (66508139 / 31250000) := by
  have h := endpoint_bounds (v := ((4417 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_55.1 (by convert! log_c_55.1 using 1; norm_num)
    log_v_55.2 (by convert! log_c_55.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_56 : (2117227231 / 500000000) ≤ -Real.log (7121 / 491520) ∧
    -Real.log (7121 / 491520) ≤ (4234454469 / 1000000000) := by
  have h := checkLog_sound (w := (559 / 14801)) (n := 12)
    (lo := (37785691 / 500000000)) (hi := (75571383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7680 / 7121) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7680 / 7121) = 1/(7121 / 491520) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_56 : (14593683 / 1000000000) ≤ -Real.log (484399 / 491520) ∧
    -Real.log (484399 / 491520) ≤ (3648421 / 250000000) := by
  have h := checkLog_sound (w := (7121 / 975919)) (n := 12)
    (lo := (14593683 / 1000000000)) (hi := (3648421 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491520 / 484399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491520 / 484399) = 1/(484399 / 491520) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_56 : (2109930389 / 1000000000) ≤ xi (7121 / 491520) ∧ xi (7121 / 491520) ≤ (2109930393 / 1000000000) ∧
    (849809629 / 400000000) ≤ kap (7121 / 491520) ∧ kap (7121 / 491520) ≤ (4249048153 / 2000000000) := by
  have h := endpoint_bounds (v := ((7121 / 491520) : ℝ)) (by norm_num) (by norm_num)
    log_v_56.1 (by convert! log_c_56.1 using 1; norm_num)
    log_v_56.2 (by convert! log_c_56.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_57 : (211346387 / 50000000) ≤ -Real.log (5979 / 409600) ∧
    -Real.log (5979 / 409600) ≤ (4226927747 / 1000000000) := by
  have h := checkLog_sound (w := (421 / 12379)) (n := 12)
    (lo := (3402233 / 50000000)) (hi := (68044661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 5979) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(6400 / 5979) = 1/(5979 / 409600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_57 : (7352377 / 500000000) ≤ -Real.log (403621 / 409600) ∧
    -Real.log (403621 / 409600) ≤ (2940951 / 200000000) := by
  have h := checkLog_sound (w := (5979 / 813221)) (n := 12)
    (lo := (7352377 / 500000000)) (hi := (2940951 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((409600 / 403621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(409600 / 403621) = 1/(403621 / 409600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_57 : (842444597 / 400000000) ≤ xi (5979 / 409600) ∧ xi (5979 / 409600) ≤ (4212222993 / 2000000000) ∧
    (2120816247 / 1000000000) ≤ kap (5979 / 409600) ∧ kap (5979 / 409600) ≤ (2120816251 / 1000000000) := by
  have h := endpoint_bounds (v := ((5979 / 409600) : ℝ)) (by norm_num) (by norm_num)
    log_v_57.1 (by convert! log_c_57.1 using 1; norm_num)
    log_v_57.2 (by convert! log_c_57.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_58 : (4219457247 / 1000000000) ≤ -Real.log (36143 / 2457600) ∧
    -Real.log (36143 / 2457600) ≤ (2109728627 / 500000000) := by
  have h := checkLog_sound (w := (2257 / 74543)) (n := 12)
    (lo := (60574167 / 1000000000)) (hi := (7571771 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 36143) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(38400 / 36143) = 1/(36143 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_58 : (7407919 / 500000000) ≤ -Real.log (2421457 / 2457600) ∧
    -Real.log (2421457 / 2457600) ≤ (14815839 / 1000000000) := by
  have h := checkLog_sound (w := (36143 / 4879057)) (n := 12)
    (lo := (7407919 / 500000000)) (hi := (14815839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2457600 / 2421457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2457600 / 2421457) = 1/(2421457 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_58 : (32848761 / 15625000) ≤ xi (36143 / 2457600) ∧ xi (36143 / 2457600) ≤ (525580177 / 250000000) ∧
    (846854617 / 400000000) ≤ kap (36143 / 2457600) ∧ kap (36143 / 2457600) ≤ (4234273093 / 2000000000) := by
  have h := endpoint_bounds (v := ((36143 / 2457600) : ℝ)) (by norm_num) (by norm_num)
    log_v_58.1 (by convert! log_c_58.1 using 1; norm_num)
    log_v_58.2 (by convert! log_c_58.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_59 : (1053010537 / 250000000) ≤ -Real.log (9103 / 614400) ∧
    -Real.log (9103 / 614400) ≤ (842408431 / 200000000) := by
  have h := checkLog_sound (w := (497 / 18703)) (n := 12)
    (lo := (13289767 / 250000000)) (hi := (53159069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 9103) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9600 / 9103) = 1/(9103 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_59 : (2985387 / 200000000) ≤ -Real.log (605297 / 614400) ∧
    -Real.log (605297 / 614400) ≤ (1865867 / 125000000) := by
  have h := checkLog_sound (w := (9103 / 1219697)) (n := 12)
    (lo := (2985387 / 200000000)) (hi := (1865867 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 605297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 605297) = 1/(605297 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_59 : (1049278803 / 500000000) ≤ xi (9103 / 614400) ∧ xi (9103 / 614400) ≤ (209855761 / 100000000) ∧
    (4226969083 / 2000000000) ≤ kap (9103 / 614400) ∧ kap (9103 / 614400) ≤ (4226969091 / 2000000000) := by
  have h := endpoint_bounds (v := ((9103 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_59.1 (by convert! log_c_59.1 using 1; norm_num)
    log_v_59.2 (by convert! log_c_59.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_60 : (4204681629 / 1000000000) ≤ -Real.log (12227 / 819200) ∧
    -Real.log (12227 / 819200) ≤ (1051170409 / 250000000) := by
  have h := checkLog_sound (w := (573 / 25027)) (n := 12)
    (lo := (45798549 / 1000000000)) (hi := (915971 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 12227) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(12800 / 12227) = 1/(12227 / 819200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_60 : (15038043 / 1000000000) ≤ -Real.log (806973 / 819200) ∧
    -Real.log (806973 / 819200) ≤ (3759511 / 250000000) := by
  have h := checkLog_sound (w := (12227 / 1626173)) (n := 12)
    (lo := (15038043 / 1000000000)) (hi := (3759511 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819200 / 806973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819200 / 806973) = 1/(806973 / 819200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_60 : (837928717 / 400000000) ≤ xi (12227 / 819200) ∧ xi (12227 / 819200) ≤ (4189643593 / 2000000000) ∧
    (527464959 / 250000000) ≤ kap (12227 / 819200) ∧ kap (12227 / 819200) ≤ (824164 / 390625) := by
  have h := endpoint_bounds (v := ((12227 / 819200) : ℝ)) (by norm_num) (by norm_num)
    log_v_60.1 (by convert! log_c_60.1 using 1; norm_num)
    log_v_60.2 (by convert! log_c_60.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_61 : (1049343723 / 250000000) ≤ -Real.log (739 / 49152) ∧
    -Real.log (739 / 49152) ≤ (4197374899 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 1507)) (n := 12)
    (lo := (9622953 / 250000000)) (hi := (38491813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((768 / 739) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(768 / 739) = 1/(739 / 49152) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_61 : (3787291 / 250000000) ≤ -Real.log (48413 / 49152) ∧
    -Real.log (48413 / 49152) ≤ (3029833 / 200000000) := by
  have h := checkLog_sound (w := (739 / 97565)) (n := 12)
    (lo := (3787291 / 250000000)) (hi := (3029833 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49152 / 48413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49152 / 48413) = 1/(48413 / 49152) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_61 : (4182225727 / 2000000000) ≤ xi (739 / 49152) ∧ xi (739 / 49152) ≤ (836445147 / 400000000) ∧
    (526565507 / 250000000) ≤ kap (739 / 49152) ∧ kap (739 / 49152) ≤ (131641377 / 62500000) := by
  have h := endpoint_bounds (v := ((739 / 49152) : ℝ)) (by norm_num) (by norm_num)
    log_v_61.1 (by convert! log_c_61.1 using 1; norm_num)
    log_v_61.2 (by convert! log_c_61.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_62 : (1047530289 / 250000000) ≤ -Real.log (37219 / 2457600) ∧
    -Real.log (37219 / 2457600) ≤ (4190121163 / 1000000000) := by
  have h := checkLog_sound (w := (1181 / 75619)) (n := 12)
    (lo := (7809519 / 250000000)) (hi := (31238077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 37219) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(38400 / 37219) = 1/(37219 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_62 : (7630149 / 500000000) ≤ -Real.log (2420381 / 2457600) ∧
    -Real.log (2420381 / 2457600) ≤ (15260299 / 1000000000) := by
  have h := checkLog_sound (w := (37219 / 4877981)) (n := 12)
    (lo := (7630149 / 500000000)) (hi := (15260299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2457600 / 2420381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2457600 / 2420381) = 1/(2420381 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_62 : (4174860857 / 2000000000) ≤ xi (37219 / 2457600) ∧ xi (37219 / 2457600) ≤ (834972173 / 400000000) ∧
    (2102690727 / 1000000000) ≤ kap (37219 / 2457600) ∧ kap (37219 / 2457600) ≤ (2102690731 / 1000000000) := by
  have h := endpoint_bounds (v := ((37219 / 2457600) : ℝ)) (by norm_num) (by norm_num)
    log_v_62.1 (by convert! log_c_62.1 using 1; norm_num)
    log_v_62.2 (by convert! log_c_62.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_63 : (4182919657 / 1000000000) ≤ -Real.log (781 / 51200) ∧
    -Real.log (781 / 51200) ≤ (261432479 / 62500000) := by
  have h := checkLog_sound (w := (19 / 1581)) (n := 12)
    (lo := (24036577 / 1000000000)) (hi := (12018289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 781) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(800 / 781) = 1/(781 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_63 : (15371443 / 1000000000) ≤ -Real.log (50419 / 51200) ∧
    -Real.log (50419 / 51200) ≤ (3842861 / 250000000) := by
  have h := checkLog_sound (w := (781 / 101619)) (n := 12)
    (lo := (15371443 / 1000000000)) (hi := (3842861 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51200 / 50419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51200 / 50419) = 1/(50419 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_63 : (4167548213 / 2000000000) ≤ xi (781 / 51200) ∧ xi (781 / 51200) ≤ (4167548221 / 2000000000) ∧
    (41982911 / 20000000) ≤ kap (781 / 51200) ∧ kap (781 / 51200) ≤ (1049572777 / 500000000) := by
  have h := endpoint_bounds (v := ((781 / 51200) : ℝ)) (by norm_num) (by norm_num)
    log_v_63.1 (by convert! log_c_63.1 using 1; norm_num)
    log_v_63.2 (by convert! log_c_63.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.EntropyCurvature


