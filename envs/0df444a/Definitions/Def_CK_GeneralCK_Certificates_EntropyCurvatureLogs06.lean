-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs06
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLogs06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:44:17.699485+00:00
-- url     : https://prove2.me/theorems/41dba878-a0e0-4ed0-81e1-ab89f0b5cdc1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLogs06` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLogs06` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLogs06` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLogs06 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLogs06.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureBounds

namespace GeneralCK.Certificates.EntropyCurvature
open Mixed GeneralCK.EntropyCurvature

theorem log_v_96 : (3919497153 / 1000000000) ≤ -Real.log (8131 / 409600) ∧
    -Real.log (8131 / 409600) ≤ (3919497159 / 1000000000) := by
  have h := checkLog_sound (w := (4669 / 20931)) (n := 12)
    (lo := (453761253 / 1000000000)) (hi := (226880627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 8131) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(12800 / 8131) = 1/(8131 / 409600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_96 : (20050753 / 1000000000) ≤ -Real.log (401469 / 409600) ∧
    -Real.log (401469 / 409600) ≤ (10025377 / 500000000) := by
  have h := checkLog_sound (w := (8131 / 811069)) (n := 12)
    (lo := (20050753 / 1000000000)) (hi := (10025377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((409600 / 401469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(409600 / 401469) = 1/(401469 / 409600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_96 : (3899446399 / 2000000000) ≤ xi (8131 / 409600) ∧ xi (8131 / 409600) ≤ (1949723203 / 1000000000) ∧
    (1969773953 / 1000000000) ≤ kap (8131 / 409600) ∧ kap (8131 / 409600) ≤ (3939547913 / 2000000000) := by
  have h := endpoint_bounds (v := ((8131 / 409600) : ℝ)) (by norm_num) (by norm_num)
    log_v_96.1 (by convert! log_c_96.1 using 1; norm_num)
    log_v_96.2 (by convert! log_c_96.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_97 : (1954264881 / 500000000) ≤ -Real.log (12331 / 614400) ∧
    -Real.log (12331 / 614400) ≤ (488566221 / 125000000) := by
  have h := checkLog_sound (w := (6869 / 31531)) (n := 12)
    (lo := (221396931 / 500000000)) (hi := (442793863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 12331) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19200 / 12331) = 1/(12331 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_97 : (162193 / 8000000) ≤ -Real.log (602069 / 614400) ∧
    -Real.log (602069 / 614400) ≤ (10137063 / 500000000) := by
  have h := checkLog_sound (w := (12331 / 1216469)) (n := 12)
    (lo := (162193 / 8000000)) (hi := (10137063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 602069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 602069) = 1/(602069 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_97 : (972063909 / 500000000) ≤ xi (12331 / 614400) ∧ xi (12331 / 614400) ≤ (3888255643 / 2000000000) ∧
    (3928803887 / 2000000000) ≤ kap (12331 / 614400) ∧ kap (12331 / 614400) ≤ (1964401947 / 1000000000) := by
  have h := endpoint_bounds (v := ((12331 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_97.1 (by convert! log_c_97.1 using 1; norm_num)
    log_v_97.2 (by convert! log_c_97.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_98 : (77953627 / 20000000) ≤ -Real.log (24931 / 1228800) ∧
    -Real.log (24931 / 1228800) ≤ (974420339 / 250000000) := by
  have h := checkLog_sound (w := (13469 / 63331)) (n := 12)
    (lo := (8638909 / 20000000)) (hi := (431945451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 24931) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(38400 / 24931) = 1/(24931 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_98 : (10248773 / 500000000) ≤ -Real.log (1203869 / 1228800) ∧
    -Real.log (1203869 / 1228800) ≤ (20497547 / 1000000000) := by
  have h := checkLog_sound (w := (24931 / 2432669)) (n := 12)
    (lo := (10248773 / 500000000)) (hi := (20497547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 1203869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 1203869) = 1/(1203869 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_98 : (3877183803 / 2000000000) ≤ xi (24931 / 1228800) ∧ xi (24931 / 1228800) ≤ (387718381 / 200000000) ∧
    (244886181 / 125000000) ≤ kap (24931 / 1228800) ∧ kap (24931 / 1228800) ≤ (3918178903 / 2000000000) := by
  have h := endpoint_bounds (v := ((24931 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_98.1 (by convert! log_c_98.1 using 1; norm_num)
    log_v_98.2 (by convert! log_c_98.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_99 : (777389873 / 200000000) ≤ -Real.log (21 / 1024) ∧
    -Real.log (21 / 1024) ≤ (3886949371 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 53)) (n := 12)
    (lo := (84242693 / 200000000)) (hi := (210606733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 21) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(32 / 21) = 1/(21 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_99 : (20721017 / 1000000000) ≤ -Real.log (1003 / 1024) ∧
    -Real.log (1003 / 1024) ≤ (10360509 / 500000000) := by
  have h := checkLog_sound (w := (21 / 2027)) (n := 12)
    (lo := (20721017 / 1000000000)) (hi := (10360509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 1003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 1003) = 1/(1003 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_99 : (3866228347 / 2000000000) ≤ xi (21 / 1024) ∧ xi (21 / 1024) ≤ (1933114177 / 1000000000) ∧
    (1953835191 / 1000000000) ≤ kap (21 / 1024) ∧ kap (21 / 1024) ≤ (3907670389 / 2000000000) := by
  have h := endpoint_bounds (v := ((21 / 1024) : ℝ)) (by norm_num) (by norm_num)
    log_v_99.1 (by convert! log_c_99.1 using 1; norm_num)
    log_v_99.2 (by convert! log_c_99.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_100 : (3876331333 / 1000000000) ≤ -Real.log (25469 / 1228800) ∧
    -Real.log (25469 / 1228800) ≤ (3876331339 / 1000000000) := by
  have h := checkLog_sound (w := (12931 / 63869)) (n := 12)
    (lo := (410595433 / 1000000000)) (hi := (205297717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 25469) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(38400 / 25469) = 1/(25469 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_100 : (10472269 / 500000000) ≤ -Real.log (1203331 / 1228800) ∧
    -Real.log (1203331 / 1228800) ≤ (20944539 / 1000000000) := by
  have h := checkLog_sound (w := (25469 / 2432131)) (n := 12)
    (lo := (10472269 / 500000000)) (hi := (20944539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 1203331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 1203331) = 1/(1203331 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_100 : (1927693397 / 1000000000) ≤ xi (25469 / 1228800) ∧ xi (25469 / 1228800) ≤ (3855386801 / 2000000000) ∧
    (3897275871 / 2000000000) ≤ kap (25469 / 1228800) ∧ kap (25469 / 1228800) ≤ (1948637939 / 1000000000) := by
  have h := endpoint_bounds (v := ((25469 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_100.1 (by convert! log_c_100.1 using 1; norm_num)
    log_v_100.2 (by convert! log_c_100.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_101 : (193291243 / 50000000) ≤ -Real.log (12869 / 614400) ∧
    -Real.log (12869 / 614400) ≤ (1932912433 / 500000000) := by
  have h := checkLog_sound (w := (6331 / 32069)) (n := 12)
    (lo := (625139 / 1562500)) (hi := (400088961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 12869) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19200 / 12869) = 1/(12869 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_101 : (21168109 / 1000000000) ≤ -Real.log (601531 / 614400) ∧
    -Real.log (601531 / 614400) ≤ (2116811 / 100000000) := by
  have h := checkLog_sound (w := (12869 / 1215931)) (n := 12)
    (lo := (21168109 / 1000000000)) (hi := (2116811 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 601531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 601531) = 1/(601531 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_101 : (15378627 / 8000000) ≤ xi (12869 / 614400) ∧ xi (12869 / 614400) ≤ (3844656757 / 2000000000) ∧
    (3886992969 / 2000000000) ≤ kap (12869 / 614400) ∧ kap (12869 / 614400) ≤ (242937061 / 125000000) := by
  have h := endpoint_bounds (v := ((12869 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_101.1 (by convert! log_c_101.1 using 1; norm_num)
    log_v_101.2 (by convert! log_c_101.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_102 : (3855427627 / 1000000000) ≤ -Real.log (8669 / 409600) ∧
    -Real.log (8669 / 409600) ≤ (3855427633 / 1000000000) := by
  have h := checkLog_sound (w := (4131 / 21469)) (n := 12)
    (lo := (389691727 / 1000000000)) (hi := (24355733 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 8669) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(12800 / 8669) = 1/(8669 / 409600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_102 : (21391731 / 1000000000) ≤ -Real.log (400931 / 409600) ∧
    -Real.log (400931 / 409600) ≤ (5347933 / 250000000) := by
  have h := checkLog_sound (w := (8669 / 810531)) (n := 12)
    (lo := (21391731 / 1000000000)) (hi := (5347933 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((409600 / 400931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(409600 / 400931) = 1/(400931 / 409600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_102 : (766807179 / 400000000) ≤ xi (8669 / 409600) ∧ xi (8669 / 409600) ≤ (1917017951 / 1000000000) ∧
    (1938409679 / 1000000000) ≤ kap (8669 / 409600) ∧ kap (8669 / 409600) ≤ (775363873 / 400000000) := by
  have h := endpoint_bounds (v := ((8669 / 409600) : ℝ)) (by norm_num) (by norm_num)
    log_v_102.1 (by convert! log_c_102.1 using 1; norm_num)
    log_v_102.2 (by convert! log_c_102.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_103 : (480642173 / 125000000) ≤ -Real.log (6569 / 307200) ∧
    -Real.log (6569 / 307200) ≤ (384513739 / 100000000) := by
  have h := checkLog_sound (w := (3031 / 16169)) (n := 12)
    (lo := (94850371 / 250000000)) (hi := (75880297 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 6569) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(9600 / 6569) = 1/(6569 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_103 : (10807701 / 500000000) ≤ -Real.log (300631 / 307200) ∧
    -Real.log (300631 / 307200) ≤ (21615403 / 1000000000) := by
  have h := checkLog_sound (w := (6569 / 607831)) (n := 12)
    (lo := (10807701 / 500000000)) (hi := (21615403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 300631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 300631) = 1/(300631 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_103 : (3823521981 / 2000000000) ≤ xi (6569 / 307200) ∧ xi (6569 / 307200) ≤ (955880497 / 500000000) ∧
    (1933376393 / 1000000000) ≤ kap (6569 / 307200) ∧ kap (6569 / 307200) ≤ (3866752793 / 2000000000) := by
  have h := endpoint_bounds (v := ((6569 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_103.1 (by convert! log_c_103.1 using 1; norm_num)
    log_v_103.2 (by convert! log_c_103.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_104 : (3834951953 / 1000000000) ≤ -Real.log (5309 / 245760) ∧
    -Real.log (5309 / 245760) ≤ (3834951959 / 1000000000) := by
  have h := checkLog_sound (w := (2371 / 12989)) (n := 12)
    (lo := (369216053 / 1000000000)) (hi := (184608027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7680 / 5309) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(7680 / 5309) = 1/(5309 / 245760) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_104 : (21839123 / 1000000000) ≤ -Real.log (240451 / 245760) ∧
    -Real.log (240451 / 245760) ≤ (5459781 / 250000000) := by
  have h := checkLog_sound (w := (5309 / 486211)) (n := 12)
    (lo := (21839123 / 1000000000)) (hi := (5459781 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245760 / 240451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(245760 / 240451) = 1/(240451 / 245760) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_104 : (3813112829 / 2000000000) ≤ xi (5309 / 245760) ∧ xi (5309 / 245760) ≤ (953278209 / 500000000) ∧
    (964197769 / 500000000) ≤ kap (5309 / 245760) ∧ kap (5309 / 245760) ≤ (3856791083 / 2000000000) := by
  have h := endpoint_bounds (v := ((5309 / 245760) : ℝ)) (by norm_num) (by norm_num)
    log_v_104.1 (by convert! log_c_104.1 using 1; norm_num)
    log_v_104.2 (by convert! log_c_104.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_105 : (191243461 / 50000000) ≤ -Real.log (4469 / 204800) ∧
    -Real.log (4469 / 204800) ≤ (1912434613 / 500000000) := by
  have h := checkLog_sound (w := (1931 / 10869)) (n := 12)
    (lo := (8978333 / 25000000)) (hi := (359133321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4469) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6400 / 4469) = 1/(4469 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_105 : (11031447 / 500000000) ≤ -Real.log (200331 / 204800) ∧
    -Real.log (200331 / 204800) ≤ (4412579 / 200000000) := by
  have h := checkLog_sound (w := (4469 / 405131)) (n := 12)
    (lo := (11031447 / 500000000)) (hi := (4412579 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204800 / 200331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204800 / 200331) = 1/(200331 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_105 : (152112253 / 80000000) ≤ xi (4469 / 204800) ∧ xi (4469 / 204800) ≤ (950701583 / 500000000) ∧
    (1923466057 / 1000000000) ≤ kap (4469 / 204800) ∧ kap (4469 / 204800) ≤ (3846932121 / 2000000000) := by
  have h := endpoint_bounds (v := ((4469 / 204800) : ℝ)) (by norm_num) (by norm_num)
    log_v_105.1 (by convert! log_c_105.1 using 1; norm_num)
    log_v_105.2 (by convert! log_c_105.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_106 : (1907443567 / 500000000) ≤ -Real.log (27083 / 1228800) ∧
    -Real.log (27083 / 1228800) ≤ (190744357 / 50000000) := by
  have h := checkLog_sound (w := (11317 / 65483)) (n := 12)
    (lo := (174575617 / 500000000)) (hi := (69830247 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 27083) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(38400 / 27083) = 1/(27083 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_106 : (4457343 / 200000000) ≤ -Real.log (1201717 / 1228800) ∧
    -Real.log (1201717 / 1228800) ≤ (5571679 / 250000000) := by
  have h := checkLog_sound (w := (27083 / 2430517)) (n := 12)
    (lo := (4457343 / 200000000)) (hi := (5571679 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 1201717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 1201717) = 1/(1201717 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_106 : (1896300209 / 1000000000) ≤ xi (27083 / 1228800) ∧ xi (27083 / 1228800) ≤ (151704017 / 80000000) ∧
    (3837173849 / 2000000000) ≤ kap (27083 / 1228800) ∧ kap (27083 / 1228800) ≤ (119911683 / 62500000) := by
  have h := endpoint_bounds (v := ((27083 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_106.1 (by convert! log_c_106.1 using 1; norm_num)
    log_v_106.2 (by convert! log_c_106.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_107 : (3805003707 / 1000000000) ≤ -Real.log (3419 / 153600) ∧
    -Real.log (3419 / 153600) ≤ (3805003713 / 1000000000) := by
  have h := checkLog_sound (w := (1381 / 8219)) (n := 12)
    (lo := (339267807 / 1000000000)) (hi := (10602119 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4800 / 3419) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4800 / 3419) = 1/(3419 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_107 : (22510587 / 1000000000) ≤ -Real.log (150181 / 153600) ∧
    -Real.log (150181 / 153600) ≤ (5627647 / 250000000) := by
  have h := checkLog_sound (w := (3419 / 303781)) (n := 12)
    (lo := (22510587 / 1000000000)) (hi := (5627647 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 150181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153600 / 150181) = 1/(150181 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_107 : (3782493119 / 2000000000) ≤ xi (3419 / 153600) ∧ xi (3419 / 153600) ≤ (1891246563 / 1000000000) ∧
    (1913757147 / 1000000000) ≤ kap (3419 / 153600) ∧ kap (3419 / 153600) ≤ (3827514301 / 2000000000) := by
  have h := endpoint_bounds (v := ((3419 / 153600) : ℝ)) (by norm_num) (by norm_num)
    log_v_107.1 (by convert! log_c_107.1 using 1; norm_num)
    log_v_107.2 (by convert! log_c_107.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_108 : (1897608503 / 500000000) ≤ -Real.log (9207 / 409600) ∧
    -Real.log (9207 / 409600) ≤ (948804253 / 250000000) := by
  have h := checkLog_sound (w := (3593 / 22007)) (n := 12)
    (lo := (164740553 / 500000000)) (hi := (329481107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 9207) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(12800 / 9207) = 1/(9207 / 409600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_108 : (5683627 / 250000000) ≤ -Real.log (400393 / 409600) ∧
    -Real.log (400393 / 409600) ≤ (22734509 / 1000000000) := by
  have h := checkLog_sound (w := (9207 / 809993)) (n := 12)
    (lo := (5683627 / 250000000)) (hi := (22734509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((409600 / 400393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(409600 / 400393) = 1/(400393 / 409600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_108 : (3772482497 / 2000000000) ≤ xi (9207 / 409600) ∧ xi (9207 / 409600) ≤ (471560313 / 250000000) ∧
    (1908975757 / 1000000000) ≤ kap (9207 / 409600) ∧ kap (9207 / 409600) ≤ (3817951521 / 2000000000) := by
  have h := endpoint_bounds (v := ((9207 / 409600) : ℝ)) (by norm_num) (by norm_num)
    log_v_108.1 (by convert! log_c_108.1 using 1; norm_num)
    log_v_108.2 (by convert! log_c_108.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_109 : (3785525157 / 1000000000) ≤ -Real.log (2789 / 122880) ∧
    -Real.log (2789 / 122880) ≤ (3785525163 / 1000000000) := by
  have h := checkLog_sound (w := (1051 / 6629)) (n := 12)
    (lo := (319789257 / 1000000000)) (hi := (159894629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3840 / 2789) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3840 / 2789) = 1/(2789 / 122880) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_109 : (286981 / 12500000) ≤ -Real.log (120091 / 122880) ∧
    -Real.log (120091 / 122880) ≤ (22958481 / 1000000000) := by
  have h := checkLog_sound (w := (2789 / 242971)) (n := 12)
    (lo := (286981 / 12500000)) (hi := (22958481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122880 / 120091) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122880 / 120091) = 1/(120091 / 122880) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_109 : (940641669 / 500000000) ≤ xi (2789 / 122880) ∧ xi (2789 / 122880) ≤ (3762566683 / 2000000000) ∧
    (3808483637 / 2000000000) ≤ kap (2789 / 122880) ∧ kap (2789 / 122880) ≤ (952120911 / 500000000) := by
  have h := endpoint_bounds (v := ((2789 / 122880) : ℝ)) (by norm_num) (by norm_num)
    log_v_109.1 (by convert! log_c_109.1 using 1; norm_num)
    log_v_109.2 (by convert! log_c_109.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_110 : (188796317 / 50000000) ≤ -Real.log (28159 / 1228800) ∧
    -Real.log (28159 / 1228800) ≤ (1887963173 / 500000000) := by
  have h := checkLog_sound (w := (10241 / 66559)) (n := 12)
    (lo := (7754761 / 25000000)) (hi := (310190441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 28159) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(38400 / 28159) = 1/(28159 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_110 : (11591251 / 500000000) ≤ -Real.log (1200641 / 1228800) ∧
    -Real.log (1200641 / 1228800) ≤ (23182503 / 1000000000) := by
  have h := checkLog_sound (w := (28159 / 2429441)) (n := 12)
    (lo := (11591251 / 500000000)) (hi := (23182503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 1200641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 1200641) = 1/(1200641 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_110 : (3752743837 / 2000000000) ≤ xi (28159 / 1228800) ∧ xi (28159 / 1228800) ≤ (938185961 / 500000000) ∧
    (1899554421 / 1000000000) ≤ kap (28159 / 1228800) ∧ kap (28159 / 1228800) ≤ (3799108849 / 2000000000) := by
  have h := endpoint_bounds (v := ((28159 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_110.1 (by convert! log_c_110.1 using 1; norm_num)
    log_v_110.2 (by convert! log_c_110.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_111 : (117700587 / 31250000) ≤ -Real.log (2369 / 102400) ∧
    -Real.log (2369 / 102400) ≤ (376641879 / 100000000) := by
  have h := checkLog_sound (w := (831 / 5569)) (n := 12)
    (lo := (75170721 / 250000000)) (hi := (60136577 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2369) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2369) = 1/(2369 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_111 : (11703287 / 500000000) ≤ -Real.log (100031 / 102400) ∧
    -Real.log (100031 / 102400) ≤ (936263 / 40000000) := by
  have h := checkLog_sound (w := (2369 / 202431)) (n := 12)
    (lo := (11703287 / 500000000)) (hi := (936263 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102400 / 100031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102400 / 100031) = 1/(100031 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_111 : (3743012209 / 2000000000) ≤ xi (2369 / 102400) ∧ xi (2369 / 102400) ≤ (467876527 / 250000000) ∧
    (1894912679 / 1000000000) ≤ kap (2369 / 102400) ∧ kap (2369 / 102400) ≤ (757965073 / 400000000) := by
  have h := endpoint_bounds (v := ((2369 / 102400) : ℝ)) (by norm_num) (by norm_num)
    log_v_111.1 (by convert! log_c_111.1 using 1; norm_num)
    log_v_111.2 (by convert! log_c_111.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.EntropyCurvature


