-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs02
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLogs02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:42:08.709998+00:00
-- url     : https://prove2.me/theorems/08fc7f64-19c3-4d42-8ffa-77c4e4997d60
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLogs02` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLogs02` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLogs02` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLogs02 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLogs02.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureBounds

namespace GeneralCK.Certificates.EntropyCurvature
open Mixed GeneralCK.EntropyCurvature

theorem log_v_32 : (1108629983 / 250000000) ≤ -Real.log (29149 / 2457600) ∧
    -Real.log (29149 / 2457600) ≤ (4434519939 / 1000000000) := by
  have h := checkLog_sound (w := (9251 / 67549)) (n := 12)
    (lo := (68909213 / 250000000)) (hi := (275636853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 29149) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(38400 / 29149) = 1/(29149 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_32 : (5965829 / 500000000) ≤ -Real.log (2428451 / 2457600) ∧
    -Real.log (2428451 / 2457600) ≤ (11931659 / 1000000000) := by
  have h := checkLog_sound (w := (29149 / 4886051)) (n := 12)
    (lo := (5965829 / 500000000)) (hi := (11931659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2457600 / 2428451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2457600 / 2428451) = 1/(2428451 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_32 : (4422588273 / 2000000000) ≤ xi (29149 / 2457600) ∧ xi (29149 / 2457600) ≤ (4422588281 / 2000000000) ∧
    (444645159 / 200000000) ≤ kap (29149 / 2457600) ∧ kap (29149 / 2457600) ≤ (2223225799 / 1000000000) := by
  have h := endpoint_bounds (v := ((29149 / 2457600) : ℝ)) (by norm_num) (by norm_num)
    log_v_32.1 (by convert! log_c_32.1 using 1; norm_num)
    log_v_32.2 (by convert! log_c_32.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_33 : (4425333807 / 1000000000) ≤ -Real.log (4903 / 409600) ∧
    -Real.log (4903 / 409600) ≤ (2212666907 / 500000000) := by
  have h := checkLog_sound (w := (1497 / 11303)) (n := 12)
    (lo := (266450727 / 1000000000)) (hi := (33306341 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4903) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(6400 / 4903) = 1/(4903 / 409600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_33 : (6021217 / 500000000) ≤ -Real.log (404697 / 409600) ∧
    -Real.log (404697 / 409600) ≤ (2408487 / 200000000) := by
  have h := checkLog_sound (w := (4903 / 814297)) (n := 12)
    (lo := (6021217 / 500000000)) (hi := (2408487 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((409600 / 404697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(409600 / 404697) = 1/(404697 / 409600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_33 : (1103322843 / 500000000) ≤ xi (4903 / 409600) ∧ xi (4903 / 409600) ≤ (220664569 / 100000000) ∧
    (4437376241 / 2000000000) ≤ kap (4903 / 409600) ∧ kap (4903 / 409600) ≤ (4437376249 / 2000000000) := by
  have h := endpoint_bounds (v := ((4903 / 409600) : ℝ)) (by norm_num) (by norm_num)
    log_v_33.1 (by convert! log_c_33.1 using 1; norm_num)
    log_v_33.2 (by convert! log_c_33.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_34 : (44162313 / 10000000) ≤ -Real.log (29687 / 2457600) ∧
    -Real.log (29687 / 2457600) ≤ (4416231307 / 1000000000) := by
  have h := checkLog_sound (w := (8713 / 68087)) (n := 12)
    (lo := (12867411 / 50000000)) (hi := (257348221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 29687) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(38400 / 29687) = 1/(29687 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_34 : (12153223 / 1000000000) ≤ -Real.log (2427913 / 2457600) ∧
    -Real.log (2427913 / 2457600) ≤ (1519153 / 125000000) := by
  have h := checkLog_sound (w := (29687 / 4885513)) (n := 12)
    (lo := (12153223 / 1000000000)) (hi := (1519153 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2457600 / 2427913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2457600 / 2427913) = 1/(2427913 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_34 : (1101019519 / 500000000) ≤ xi (29687 / 2457600) ∧ xi (29687 / 2457600) ≤ (1101019521 / 500000000) ∧
    (4428384523 / 2000000000) ≤ kap (29687 / 2457600) ∧ kap (29687 / 2457600) ≤ (4428384531 / 2000000000) := by
  have h := endpoint_bounds (v := ((29687 / 2457600) : ℝ)) (by norm_num) (by norm_num)
    log_v_34.1 (by convert! log_c_34.1 using 1; norm_num)
    log_v_34.2 (by convert! log_c_34.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_35 : (4407210901 / 1000000000) ≤ -Real.log (7489 / 614400) ∧
    -Real.log (7489 / 614400) ≤ (1101802727 / 250000000) := by
  have h := checkLog_sound (w := (2111 / 17089)) (n := 12)
    (lo := (248327821 / 1000000000)) (hi := (124163911 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 7489) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9600 / 7489) = 1/(7489 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_35 : (1533003 / 125000000) ≤ -Real.log (606911 / 614400) ∧
    -Real.log (606911 / 614400) ≤ (490561 / 40000000) := by
  have h := checkLog_sound (w := (7489 / 1221311)) (n := 12)
    (lo := (1533003 / 125000000)) (hi := (490561 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 606911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 606911) = 1/(606911 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_35 : (1098736719 / 500000000) ≤ xi (7489 / 614400) ∧ xi (7489 / 614400) ≤ (1098736721 / 500000000) ∧
    (176778997 / 80000000) ≤ kap (7489 / 614400) ∧ kap (7489 / 614400) ≤ (4419474933 / 2000000000) := by
  have h := endpoint_bounds (v := ((7489 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_35.1 (by convert! log_c_35.1 using 1; norm_num)
    log_v_35.2 (by convert! log_c_35.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_36 : (4398271143 / 1000000000) ≤ -Real.log (403 / 32768) ∧
    -Real.log (403 / 32768) ≤ (87965423 / 20000000) := by
  have h := checkLog_sound (w := (109 / 915)) (n := 12)
    (lo := (239388063 / 1000000000)) (hi := (7480877 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 403) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(512 / 403) = 1/(403 / 32768) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_36 : (12374837 / 1000000000) ≤ -Real.log (32365 / 32768) ∧
    -Real.log (32365 / 32768) ≤ (6187419 / 500000000) := by
  have h := checkLog_sound (w := (403 / 65133)) (n := 12)
    (lo := (12374837 / 1000000000)) (hi := (6187419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32768 / 32365) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32768 / 32365) = 1/(32365 / 32768) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_36 : (877179261 / 400000000) ≤ xi (403 / 32768) ∧ xi (403 / 32768) ≤ (4385896313 / 2000000000) ∧
    (220532299 / 100000000) ≤ kap (403 / 32768) ∧ kap (403 / 32768) ≤ (1102661497 / 500000000) := by
  have h := endpoint_bounds (v := ((403 / 32768) : ℝ)) (by norm_num) (by norm_num)
    log_v_36.1 (by convert! log_c_36.1 using 1; norm_num)
    log_v_36.2 (by convert! log_c_36.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_37 : (1097352649 / 250000000) ≤ -Real.log (15247 / 1228800) ∧
    -Real.log (15247 / 1228800) ≤ (4389410603 / 1000000000) := by
  have h := checkLog_sound (w := (3953 / 34447)) (n := 12)
    (lo := (57631879 / 250000000)) (hi := (230527517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 15247) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(19200 / 15247) = 1/(15247 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_37 : (6242831 / 500000000) ≤ -Real.log (1213553 / 1228800) ∧
    -Real.log (1213553 / 1228800) ≤ (12485663 / 1000000000) := by
  have h := checkLog_sound (w := (15247 / 2442353)) (n := 12)
    (lo := (6242831 / 500000000)) (hi := (12485663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 1213553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 1213553) = 1/(1213553 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_37 : (4376924933 / 2000000000) ≤ xi (15247 / 1228800) ∧ xi (15247 / 1228800) ≤ (4376924941 / 2000000000) ∧
    (2200948129 / 1000000000) ≤ kap (15247 / 1228800) ∧ kap (15247 / 1228800) ≤ (2200948133 / 1000000000) := by
  have h := endpoint_bounds (v := ((15247 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_37.1 (by convert! log_c_37.1 using 1; norm_num)
    log_v_37.2 (by convert! log_c_37.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_38 : (438062787 / 100000000) ≤ -Real.log (30763 / 2457600) ∧
    -Real.log (30763 / 2457600) ≤ (4380627877 / 1000000000) := by
  have h := checkLog_sound (w := (7637 / 69163)) (n := 12)
    (lo := (22174479 / 100000000)) (hi := (221744791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 30763) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(38400 / 30763) = 1/(30763 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_38 : (25193 / 2000000) ≤ -Real.log (2426837 / 2457600) ∧
    -Real.log (2426837 / 2457600) ≤ (12596501 / 1000000000) := by
  have h := checkLog_sound (w := (30763 / 4884437)) (n := 12)
    (lo := (25193 / 2000000)) (hi := (12596501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2457600 / 2426837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2457600 / 2426837) = 1/(2426837 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_38 : (4368031369 / 2000000000) ≤ xi (30763 / 2457600) ∧ xi (30763 / 2457600) ≤ (4368031377 / 2000000000) ∧
    (439322437 / 200000000) ≤ kap (30763 / 2457600) ∧ kap (30763 / 2457600) ≤ (2196612189 / 1000000000) := by
  have h := endpoint_bounds (v := ((30763 / 2457600) : ℝ)) (by norm_num) (by norm_num)
    log_v_38.1 (by convert! log_c_38.1 using 1; norm_num)
    log_v_38.2 (by convert! log_c_38.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_39 : (4371921609 / 1000000000) ≤ -Real.log (1293 / 102400) ∧
    -Real.log (1293 / 102400) ≤ (273245101 / 62500000) := by
  have h := checkLog_sound (w := (307 / 2893)) (n := 12)
    (lo := (213038529 / 1000000000)) (hi := (21303853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1293) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(1600 / 1293) = 1/(1293 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_39 : (254147 / 20000000) ≤ -Real.log (101107 / 102400) ∧
    -Real.log (101107 / 102400) ≤ (12707351 / 1000000000) := by
  have h := checkLog_sound (w := (1293 / 203507)) (n := 12)
    (lo := (254147 / 20000000)) (hi := (12707351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102400 / 101107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102400 / 101107) = 1/(101107 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_39 : (2179607129 / 1000000000) ≤ xi (1293 / 102400) ∧ xi (1293 / 102400) ≤ (2179607133 / 1000000000) ∧
    (4384628959 / 2000000000) ≤ kap (1293 / 102400) ∧ kap (1293 / 102400) ≤ (4384628967 / 2000000000) := by
  have h := endpoint_bounds (v := ((1293 / 102400) : ℝ)) (by norm_num) (by norm_num)
    log_v_39.1 (by convert! log_c_39.1 using 1; norm_num)
    log_v_39.2 (by convert! log_c_39.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_40 : (4363290493 / 1000000000) ≤ -Real.log (31301 / 2457600) ∧
    -Real.log (31301 / 2457600) ≤ (8726581 / 2000000) := by
  have h := checkLog_sound (w := (7099 / 69701)) (n := 12)
    (lo := (204407413 / 1000000000)) (hi := (102203707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 31301) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(38400 / 31301) = 1/(31301 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_40 : (3204553 / 250000000) ≤ -Real.log (2426299 / 2457600) ∧
    -Real.log (2426299 / 2457600) ≤ (12818213 / 1000000000) := by
  have h := checkLog_sound (w := (31301 / 4883899)) (n := 12)
    (lo := (3204553 / 250000000)) (hi := (12818213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2457600 / 2426299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2457600 / 2426299) = 1/(2426299 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_40 : (108761807 / 50000000) ≤ xi (31301 / 2457600) ∧ xi (31301 / 2457600) ≤ (135952259 / 62500000) ∧
    (875221741 / 400000000) ≤ kap (31301 / 2457600) ∧ kap (31301 / 2457600) ≤ (4376108713 / 2000000000) := by
  have h := endpoint_bounds (v := ((31301 / 2457600) : ℝ)) (by norm_num) (by norm_num)
    log_v_40.1 (by convert! log_c_40.1 using 1; norm_num)
    log_v_40.2 (by convert! log_c_40.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_41 : (4354733237 / 1000000000) ≤ -Real.log (3157 / 245760) ∧
    -Real.log (3157 / 245760) ≤ (1088683311 / 250000000) := by
  have h := checkLog_sound (w := (683 / 6997)) (n := 12)
    (lo := (195850157 / 1000000000)) (hi := (97925079 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3840 / 3157) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(3840 / 3157) = 1/(3157 / 245760) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_41 : (12929087 / 1000000000) ≤ -Real.log (242603 / 245760) ∧
    -Real.log (242603 / 245760) ≤ (202017 / 15625000) := by
  have h := checkLog_sound (w := (3157 / 488363)) (n := 12)
    (lo := (12929087 / 1000000000)) (hi := (202017 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245760 / 242603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(245760 / 242603) = 1/(242603 / 245760) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_41 : (4341804149 / 2000000000) ≤ xi (3157 / 245760) ∧ xi (3157 / 245760) ≤ (4341804157 / 2000000000) ∧
    (1091915581 / 500000000) ≤ kap (3157 / 245760) ∧ kap (3157 / 245760) ≤ (1091915583 / 500000000) := by
  have h := endpoint_bounds (v := ((3157 / 245760) : ℝ)) (by norm_num) (by norm_num)
    log_v_41.1 (by convert! log_c_41.1 using 1; norm_num)
    log_v_41.2 (by convert! log_c_41.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_42 : (2173124293 / 500000000) ≤ -Real.log (10613 / 819200) ∧
    -Real.log (10613 / 819200) ≤ (4346248593 / 1000000000) := by
  have h := checkLog_sound (w := (2187 / 23413)) (n := 12)
    (lo := (93682753 / 500000000)) (hi := (187365507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 10613) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(12800 / 10613) = 1/(10613 / 819200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_42 : (6519987 / 500000000) ≤ -Real.log (808587 / 819200) ∧
    -Real.log (808587 / 819200) ≤ (521599 / 40000000) := by
  have h := checkLog_sound (w := (10613 / 1627787)) (n := 12)
    (lo := (6519987 / 500000000)) (hi := (521599 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819200 / 808587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819200 / 808587) = 1/(808587 / 819200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_42 : (4333208611 / 2000000000) ≤ xi (10613 / 819200) ∧ xi (10613 / 819200) ≤ (4333208619 / 2000000000) ∧
    (54491107 / 25000000) ≤ kap (10613 / 819200) ∧ kap (10613 / 819200) ≤ (544911071 / 250000000) := by
  have h := endpoint_bounds (v := ((10613 / 819200) : ℝ)) (by norm_num) (by norm_num)
    log_v_42.1 (by convert! log_c_42.1 using 1; norm_num)
    log_v_42.2 (by convert! log_c_42.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_43 : (4337835319 / 1000000000) ≤ -Real.log (8027 / 614400) ∧
    -Real.log (8027 / 614400) ≤ (2168917663 / 500000000) := by
  have h := checkLog_sound (w := (1573 / 17627)) (n := 12)
    (lo := (178952239 / 1000000000)) (hi := (2236903 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 8027) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9600 / 8027) = 1/(8027 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_43 : (13150873 / 1000000000) ≤ -Real.log (606373 / 614400) ∧
    -Real.log (606373 / 614400) ≤ (6575437 / 500000000) := by
  have h := checkLog_sound (w := (8027 / 1220773)) (n := 12)
    (lo := (13150873 / 1000000000)) (hi := (6575437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 606373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 606373) = 1/(606373 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_43 : (864936889 / 400000000) ≤ xi (8027 / 614400) ∧ xi (8027 / 614400) ≤ (4324684453 / 2000000000) ∧
    (271936637 / 125000000) ≤ kap (8027 / 614400) ∧ kap (8027 / 614400) ≤ (21754931 / 10000000) := by
  have h := endpoint_bounds (v := ((8027 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_43.1 (by convert! log_c_43.1 using 1; norm_num)
    log_v_43.2 (by convert! log_c_43.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_44 : (865898449 / 200000000) ≤ -Real.log (32377 / 2457600) ∧
    -Real.log (32377 / 2457600) ≤ (1082373063 / 250000000) := by
  have h := checkLog_sound (w := (6023 / 70777)) (n := 12)
    (lo := (34121833 / 200000000)) (hi := (85304583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 32377) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(38400 / 32377) = 1/(32377 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_44 : (2652357 / 200000000) ≤ -Real.log (2425223 / 2457600) ∧
    -Real.log (2425223 / 2457600) ≤ (6630893 / 500000000) := by
  have h := checkLog_sound (w := (32377 / 4882823)) (n := 12)
    (lo := (2652357 / 200000000)) (hi := (6630893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2457600 / 2425223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2457600 / 2425223) = 1/(2425223 / 2457600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_44 : (4316230459 / 2000000000) ≤ xi (32377 / 2457600) ∧ xi (32377 / 2457600) ≤ (4316230467 / 2000000000) ∧
    (434275403 / 200000000) ≤ kap (32377 / 2457600) ∧ kap (32377 / 2457600) ≤ (2171377019 / 1000000000) := by
  have h := endpoint_bounds (v := ((32377 / 2457600) : ℝ)) (by norm_num) (by norm_num)
    log_v_44.1 (by convert! log_c_44.1 using 1; norm_num)
    log_v_44.2 (by convert! log_c_44.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_45 : (2160609101 / 500000000) ≤ -Real.log (5441 / 409600) ∧
    -Real.log (5441 / 409600) ≤ (4321218209 / 1000000000) := by
  have h := checkLog_sound (w := (959 / 11841)) (n := 12)
    (lo := (81167561 / 500000000)) (hi := (162335123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 5441) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(6400 / 5441) = 1/(5441 / 409600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_45 : (3343177 / 250000000) ≤ -Real.log (404159 / 409600) ∧
    -Real.log (404159 / 409600) ≤ (13372709 / 1000000000) := by
  have h := checkLog_sound (w := (5441 / 813759)) (n := 12)
    (lo := (3343177 / 250000000)) (hi := (13372709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((409600 / 404159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(409600 / 404159) = 1/(404159 / 409600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_45 : (4307845493 / 2000000000) ≤ xi (5441 / 409600) ∧ xi (5441 / 409600) ≤ (4307845501 / 2000000000) ∧
    (433459091 / 200000000) ≤ kap (5441 / 409600) ∧ kap (5441 / 409600) ≤ (2167295459 / 1000000000) := by
  have h := endpoint_bounds (v := ((5441 / 409600) : ℝ)) (by norm_num) (by norm_num)
    log_v_45.1 (by convert! log_c_45.1 using 1; norm_num)
    log_v_45.2 (by convert! log_c_45.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_46 : (2156506029 / 500000000) ≤ -Real.log (6583 / 491520) ∧
    -Real.log (6583 / 491520) ≤ (862602413 / 200000000) := by
  have h := checkLog_sound (w := (1097 / 14263)) (n := 12)
    (lo := (77064489 / 500000000)) (hi := (154128979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7680 / 6583) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7680 / 6583) = 1/(6583 / 491520) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_46 : (3370911 / 250000000) ≤ -Real.log (484937 / 491520) ∧
    -Real.log (484937 / 491520) ≤ (2696729 / 200000000) := by
  have h := checkLog_sound (w := (6583 / 976457)) (n := 12)
    (lo := (3370911 / 250000000)) (hi := (2696729 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491520 / 484937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491520 / 484937) = 1/(484937 / 491520) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_46 : (4299528413 / 2000000000) ≤ xi (6583 / 491520) ∧ xi (6583 / 491520) ≤ (4299528421 / 2000000000) ∧
    (2163247851 / 1000000000) ≤ kap (6583 / 491520) ∧ kap (6583 / 491520) ≤ (432649571 / 200000000) := by
  have h := endpoint_bounds (v := ((6583 / 491520) : ℝ)) (by norm_num) (by norm_num)
    log_v_46.1 (by convert! log_c_46.1 using 1; norm_num)
    log_v_46.2 (by convert! log_c_46.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_47 : (4304872707 / 1000000000) ≤ -Real.log (1037 / 76800) ∧
    -Real.log (1037 / 76800) ≤ (2152436357 / 500000000) := by
  have h := checkLog_sound (w := (163 / 2237)) (n := 12)
    (lo := (145989627 / 1000000000)) (hi := (36497407 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1200 / 1037) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(1200 / 1037) = 1/(1037 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_47 : (13594593 / 1000000000) ≤ -Real.log (75763 / 76800) ∧
    -Real.log (75763 / 76800) ≤ (6797297 / 500000000) := by
  have h := checkLog_sound (w := (1037 / 152563)) (n := 12)
    (lo := (13594593 / 1000000000)) (hi := (6797297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 75763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76800 / 75763) = 1/(75763 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_47 : (4291278113 / 2000000000) ≤ xi (1037 / 76800) ∧ xi (1037 / 76800) ≤ (4291278121 / 2000000000) ∧
    (43184673 / 20000000) ≤ kap (1037 / 76800) ∧ kap (1037 / 76800) ≤ (1079616827 / 500000000) := by
  have h := endpoint_bounds (v := ((1037 / 76800) : ℝ)) (by norm_num) (by norm_num)
    log_v_47.1 (by convert! log_c_47.1 using 1; norm_num)
    log_v_47.2 (by convert! log_c_47.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.EntropyCurvature


