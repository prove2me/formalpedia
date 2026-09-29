-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs11
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLogs11
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:41:44.987047+00:00
-- url     : https://prove2.me/theorems/482c4c3c-eebf-45f8-8289-71dbf42cdef4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLogs11` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLogs11` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLogs11` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLogs11 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLogs11.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureBounds

namespace GeneralCK.Certificates.EntropyCurvature
open Mixed GeneralCK.EntropyCurvature

theorem log_v_176 : (24061743 / 8000000) ≤ -Real.log (5059 / 102400) ∧
    -Real.log (5059 / 102400) ≤ (75192947 / 25000000) := by
  have h := checkLog_sound (w := (1341 / 11459)) (n := 12)
    (lo := (47025831 / 200000000)) (hi := (58782289 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 5059) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 5059) = 1/(5059 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_176 : (25333217 / 500000000) ≤ -Real.log (97341 / 102400) ∧
    -Real.log (97341 / 102400) ≤ (10133287 / 200000000) := by
  have h := checkLog_sound (w := (5059 / 199741)) (n := 12)
    (lo := (25333217 / 500000000)) (hi := (10133287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102400 / 97341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102400 / 97341) = 1/(97341 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_176 : (36963143 / 25000000) ≤ xi (5059 / 102400) ∧ xi (5059 / 102400) ≤ (1478525723 / 1000000000) ∧
    (3058384309 / 2000000000) ≤ kap (5059 / 102400) ∧ kap (5059 / 102400) ≤ (611676863 / 400000000) := by
  have h := endpoint_bounds (v := ((5059 / 102400) : ℝ)) (by norm_num) (by norm_num)
    log_v_176.1 (by convert! log_c_176.1 using 1; norm_num)
    log_v_176.2 (by convert! log_c_176.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_177 : (46721077 / 15625000) ≤ -Real.log (7723 / 153600) ∧
    -Real.log (7723 / 153600) ≤ (2990148933 / 1000000000) := by
  have h := checkLog_sound (w := (1877 / 17323)) (n := 12)
    (lo := (13597513 / 62500000)) (hi := (217560209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 7723) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(9600 / 7723) = 1/(7723 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_177 : (51588019 / 1000000000) ≤ -Real.log (145877 / 153600) ∧
    -Real.log (145877 / 153600) ≤ (2579401 / 50000000) := by
  have h := checkLog_sound (w := (7723 / 299477)) (n := 12)
    (lo := (51588019 / 1000000000)) (hi := (2579401 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 145877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153600 / 145877) = 1/(145877 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_177 : (734640227 / 500000000) ≤ xi (7723 / 153600) ∧ xi (7723 / 153600) ≤ (1469280457 / 1000000000) ∧
    (3041736947 / 2000000000) ≤ kap (7723 / 153600) ∧ kap (7723 / 153600) ≤ (3041736953 / 2000000000) := by
  have h := endpoint_bounds (v := ((7723 / 153600) : ℝ)) (by norm_num) (by norm_num)
    log_v_177.1 (by convert! log_c_177.1 using 1; norm_num)
    log_v_177.2 (by convert! log_c_177.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_178 : (23225651 / 7812500) ≤ -Real.log (3143 / 61440) ∧
    -Real.log (3143 / 61440) ≤ (2972883333 / 1000000000) := by
  have h := checkLog_sound (w := (697 / 6983)) (n := 12)
    (lo := (12518413 / 62500000)) (hi := (200294609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3840 / 3143) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3840 / 3143) = 1/(3143 / 61440) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_178 : (26255227 / 500000000) ≤ -Real.log (58297 / 61440) ∧
    -Real.log (58297 / 61440) ≤ (10502091 / 200000000) := by
  have h := checkLog_sound (w := (3143 / 119737)) (n := 12)
    (lo := (26255227 / 500000000)) (hi := (10502091 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61440 / 58297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61440 / 58297) = 1/(58297 / 61440) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_178 : (2920372873 / 2000000000) ≤ xi (3143 / 61440) ∧ xi (3143 / 61440) ≤ (2920372879 / 2000000000) ∧
    (1512696891 / 1000000000) ≤ kap (3143 / 61440) ∧ kap (3143 / 61440) ≤ (756348447 / 500000000) := by
  have h := endpoint_bounds (v := ((3143 / 61440) : ℝ)) (by norm_num) (by norm_num)
    log_v_178.1 (by convert! log_c_178.1 using 1; norm_num)
    log_v_178.2 (by convert! log_c_178.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_179 : (2955910777 / 1000000000) ≤ -Real.log (333 / 6400) ∧
    -Real.log (333 / 6400) ≤ (1477955391 / 500000000) := by
  have h := checkLog_sound (w := (67 / 733)) (n := 12)
    (lo := (183322057 / 1000000000)) (hi := (91661029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 333) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 333) = 1/(333 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_179 : (53433741 / 1000000000) ≤ -Real.log (6067 / 6400) ∧
    -Real.log (6067 / 6400) ≤ (26716871 / 500000000) := by
  have h := checkLog_sound (w := (333 / 12467)) (n := 12)
    (lo := (53433741 / 1000000000)) (hi := (26716871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 6067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6400 / 6067) = 1/(6067 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_179 : (580495407 / 400000000) ≤ xi (333 / 6400) ∧ xi (333 / 6400) ≤ (2902477041 / 2000000000) ∧
    (1504672259 / 1000000000) ≤ kap (333 / 6400) ∧ kap (333 / 6400) ≤ (752336131 / 500000000) := by
  have h := endpoint_bounds (v := ((333 / 6400) : ℝ)) (by norm_num) (by norm_num)
    log_v_179.1 (by convert! log_c_179.1 using 1; norm_num)
    log_v_179.2 (by convert! log_c_179.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_180 : (2939221491 / 1000000000) ≤ -Real.log (16253 / 307200) ∧
    -Real.log (16253 / 307200) ≤ (367402687 / 125000000) := by
  have h := checkLog_sound (w := (2947 / 35453)) (n := 12)
    (lo := (166632771 / 1000000000)) (hi := (41658193 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 16253) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(19200 / 16253) = 1/(16253 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_180 : (54357881 / 1000000000) ≤ -Real.log (290947 / 307200) ∧
    -Real.log (290947 / 307200) ≤ (27178941 / 500000000) := by
  have h := checkLog_sound (w := (16253 / 598147)) (n := 12)
    (lo := (54357881 / 1000000000)) (hi := (27178941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 290947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 290947) = 1/(290947 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_180 : (2884863609 / 2000000000) ≤ xi (16253 / 307200) ∧ xi (16253 / 307200) ≤ (576972723 / 400000000) ∧
    (748394843 / 500000000) ≤ kap (16253 / 307200) ∧ kap (16253 / 307200) ≤ (1496789689 / 1000000000) := by
  have h := endpoint_bounds (v := ((16253 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_180.1 (by convert! log_c_180.1 using 1; norm_num)
    log_v_180.2 (by convert! log_c_180.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_181 : (730701543 / 250000000) ≤ -Real.log (8261 / 153600) ∧
    -Real.log (8261 / 153600) ≤ (2922806177 / 1000000000) := by
  have h := checkLog_sound (w := (1339 / 17861)) (n := 12)
    (lo := (37554363 / 250000000)) (hi := (150217453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 8261) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(9600 / 8261) = 1/(8261 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_181 : (442263 / 8000000) ≤ -Real.log (145339 / 153600) ∧
    -Real.log (145339 / 153600) ≤ (13820719 / 250000000) := by
  have h := checkLog_sound (w := (8261 / 298939)) (n := 12)
    (lo := (442263 / 8000000)) (hi := (13820719 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 145339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153600 / 145339) = 1/(145339 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_181 : (89610103 / 62500000) ≤ xi (8261 / 153600) ∧ xi (8261 / 153600) ≤ (1433761651 / 1000000000) ∧
    (2978089047 / 2000000000) ≤ kap (8261 / 153600) ∧ kap (8261 / 153600) ≤ (2978089053 / 2000000000) := by
  have h := endpoint_bounds (v := ((8261 / 153600) : ℝ)) (by norm_num) (by norm_num)
    log_v_181.1 (by convert! log_c_181.1 using 1; norm_num)
    log_v_181.2 (by convert! log_c_181.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_182 : (290665597 / 100000000) ≤ -Real.log (5597 / 102400) ∧
    -Real.log (5597 / 102400) ≤ (116266239 / 40000000) := by
  have h := checkLog_sound (w := (803 / 11997)) (n := 12)
    (lo := (536269 / 4000000)) (hi := (134067251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 5597) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 5597) = 1/(5597 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_182 : (56208727 / 1000000000) ≤ -Real.log (96803 / 102400) ∧
    -Real.log (96803 / 102400) ≤ (7026091 / 125000000) := by
  have h := checkLog_sound (w := (5597 / 199203)) (n := 12)
    (lo := (56208727 / 1000000000)) (hi := (7026091 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102400 / 96803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102400 / 96803) = 1/(96803 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_182 : (1425223621 / 1000000000) ≤ xi (5597 / 102400) ∧ xi (5597 / 102400) ≤ (178152953 / 125000000) ∧
    (2962864697 / 2000000000) ≤ kap (5597 / 102400) ∧ kap (5597 / 102400) ≤ (2962864703 / 2000000000) := by
  have h := endpoint_bounds (v := ((5597 / 102400) : ℝ)) (by norm_num) (by norm_num)
    log_v_182.1 (by convert! log_c_182.1 using 1; norm_num)
    log_v_182.2 (by convert! log_c_182.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_183 : (361345307 / 125000000) ≤ -Real.log (853 / 15360) ∧
    -Real.log (853 / 15360) ≤ (2890762461 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 1813)) (n := 12)
    (lo := (14771717 / 125000000)) (hi := (118173737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((960 / 853) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(960 / 853) = 1/(853 / 15360) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_183 : (14283859 / 250000000) ≤ -Real.log (14507 / 15360) ∧
    -Real.log (14507 / 15360) ≤ (57135437 / 1000000000) := by
  have h := checkLog_sound (w := (853 / 29867)) (n := 12)
    (lo := (14283859 / 250000000)) (hi := (57135437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15360 / 14507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15360 / 14507) = 1/(14507 / 15360) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_183 : (2833627019 / 2000000000) ≤ xi (853 / 15360) ∧ xi (853 / 15360) ≤ (113345081 / 80000000) ∧
    (736974473 / 500000000) ≤ kap (853 / 15360) ∧ kap (853 / 15360) ≤ (1473948949 / 1000000000) := by
  have h := endpoint_bounds (v := ((853 / 15360) : ℝ)) (by norm_num) (by norm_num)
    log_v_183.1 (by convert! log_c_183.1 using 1; norm_num)
    log_v_183.2 (by convert! log_c_183.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_184 : (3593897 / 1250000) ≤ -Real.log (17329 / 307200) ∧
    -Real.log (17329 / 307200) ≤ (575023521 / 200000000) := by
  have h := checkLog_sound (w := (1871 / 36529)) (n := 12)
    (lo := (1281611 / 12500000)) (hi := (102528881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 17329) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(19200 / 17329) = 1/(17329 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_184 : (14515751 / 250000000) ≤ -Real.log (289871 / 307200) ∧
    -Real.log (289871 / 307200) ≤ (11612601 / 200000000) := by
  have h := checkLog_sound (w := (17329 / 597071)) (n := 12)
    (lo := (14515751 / 250000000)) (hi := (11612601 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 289871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 289871) = 1/(289871 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_184 : (563410919 / 400000000) ≤ xi (17329 / 307200) ∧ xi (17329 / 307200) ≤ (2817054601 / 2000000000) ∧
    (733295151 / 500000000) ≤ kap (17329 / 307200) ∧ kap (17329 / 307200) ≤ (293318061 / 200000000) := by
  have h := endpoint_bounds (v := ((17329 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_184.1 (by convert! log_c_184.1 using 1; norm_num)
    log_v_184.2 (by convert! log_c_184.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_185 : (2859713739 / 1000000000) ≤ -Real.log (2933 / 51200) ∧
    -Real.log (2933 / 51200) ≤ (178732109 / 62500000) := by
  have h := checkLog_sound (w := (267 / 6133)) (n := 12)
    (lo := (87125019 / 1000000000)) (hi := (4356251 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2933) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2933) = 1/(2933 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_185 : (29495717 / 500000000) ≤ -Real.log (48267 / 51200) ∧
    -Real.log (48267 / 51200) ≤ (11798287 / 200000000) := by
  have h := checkLog_sound (w := (2933 / 99467)) (n := 12)
    (lo := (29495717 / 500000000)) (hi := (11798287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51200 / 48267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51200 / 48267) = 1/(48267 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_185 : (21880643 / 15625000) ≤ xi (2933 / 51200) ∧ xi (2933 / 51200) ≤ (280072231 / 200000000) ∧
    (2918705173 / 2000000000) ≤ kap (2933 / 51200) ∧ kap (2933 / 51200) ≤ (2918705179 / 2000000000) := by
  have h := endpoint_bounds (v := ((2933 / 51200) : ℝ)) (by norm_num) (by norm_num)
    log_v_185.1 (by convert! log_c_185.1 using 1; norm_num)
    log_v_185.2 (by convert! log_c_185.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_186 : (2844543563 / 1000000000) ≤ -Real.log (17867 / 307200) ∧
    -Real.log (17867 / 307200) ≤ (177783973 / 62500000) := by
  have h := checkLog_sound (w := (1333 / 37067)) (n := 12)
    (lo := (71954843 / 1000000000)) (hi := (17988711 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 17867) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(19200 / 17867) = 1/(17867 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_186 : (59920727 / 1000000000) ≤ -Real.log (289333 / 307200) ∧
    -Real.log (289333 / 307200) ≤ (7490091 / 125000000) := by
  have h := checkLog_sound (w := (17867 / 596533)) (n := 12)
    (lo := (59920727 / 1000000000)) (hi := (7490091 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 289333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 289333) = 1/(289333 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_186 : (556924567 / 400000000) ≤ xi (17867 / 307200) ∧ xi (17867 / 307200) ≤ (2784622841 / 2000000000) ∧
    (290446429 / 200000000) ≤ kap (17867 / 307200) ∧ kap (17867 / 307200) ≤ (363058037 / 250000000) := by
  have h := endpoint_bounds (v := ((17867 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_186.1 (by convert! log_c_186.1 using 1; norm_num)
    log_v_186.2 (by convert! log_c_186.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_187 : (565920017 / 200000000) ≤ -Real.log (2267 / 38400) ∧
    -Real.log (2267 / 38400) ≤ (282960009 / 100000000) := by
  have h := checkLog_sound (w := (133 / 4667)) (n := 12)
    (lo := (11402273 / 200000000)) (hi := (28505683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2400 / 2267) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2400 / 2267) = 1/(2267 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_187 : (15212721 / 250000000) ≤ -Real.log (36133 / 38400) ∧
    -Real.log (36133 / 38400) ≤ (12170177 / 200000000) := by
  have h := checkLog_sound (w := (2267 / 74533)) (n := 12)
    (lo := (15212721 / 250000000)) (hi := (12170177 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 36133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38400 / 36133) = 1/(36133 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_187 : (6921873 / 5000000) ≤ xi (2267 / 38400) ∧ xi (2267 / 38400) ≤ (1384374603 / 1000000000) ∧
    (2890450969 / 2000000000) ≤ kap (2267 / 38400) ∧ kap (2267 / 38400) ≤ (115618039 / 80000000) := by
  have h := endpoint_bounds (v := ((2267 / 38400) : ℝ)) (by norm_num) (by norm_num)
    log_v_187.1 (by convert! log_c_187.1 using 1; norm_num)
    log_v_187.2 (by convert! log_c_187.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_188 : (351859579 / 125000000) ≤ -Real.log (1227 / 20480) ∧
    -Real.log (1227 / 20480) ≤ (2814876637 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 2507)) (n := 12)
    (lo := (5285989 / 125000000)) (hi := (42287913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1227) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1280 / 1227) = 1/(1227 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_188 : (61781907 / 1000000000) ≤ -Real.log (19253 / 20480) ∧
    -Real.log (19253 / 20480) ≤ (15445477 / 250000000) := by
  have h := checkLog_sound (w := (1227 / 39733)) (n := 12)
    (lo := (61781907 / 1000000000)) (hi := (15445477 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20480 / 19253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20480 / 19253) = 1/(19253 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_188 : (688273681 / 500000000) ≤ xi (1227 / 20480) ∧ xi (1227 / 20480) ≤ (275309473 / 200000000) ∧
    (2876658539 / 2000000000) ≤ kap (1227 / 20480) ∧ kap (1227 / 20480) ≤ (575331709 / 400000000) := by
  have h := endpoint_bounds (v := ((1227 / 20480) : ℝ)) (by norm_num) (by norm_num)
    log_v_188.1 (by convert! log_c_188.1 using 1; norm_num)
    log_v_188.2 (by convert! log_c_188.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_189 : (87511463 / 31250000) ≤ -Real.log (9337 / 153600) ∧
    -Real.log (9337 / 153600) ≤ (2800366821 / 1000000000) := by
  have h := checkLog_sound (w := (263 / 18937)) (n := 12)
    (lo := (1736131 / 62500000)) (hi := (27778097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 9337) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(9600 / 9337) = 1/(9337 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_189 : (31356899 / 500000000) ≤ -Real.log (144263 / 153600) ∧
    -Real.log (144263 / 153600) ≤ (62713799 / 1000000000) := by
  have h := checkLog_sound (w := (9337 / 297863)) (n := 12)
    (lo := (31356899 / 500000000)) (hi := (62713799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 144263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153600 / 144263) = 1/(144263 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_189 : (2737653017 / 2000000000) ≤ xi (9337 / 153600) ∧ xi (9337 / 153600) ≤ (2737653023 / 2000000000) ∧
    (1431540307 / 1000000000) ≤ kap (9337 / 153600) ∧ kap (9337 / 153600) ≤ (143154031 / 100000000) := by
  have h := endpoint_bounds (v := ((9337 / 153600) : ℝ)) (by norm_num) (by norm_num)
    log_v_189.1 (by convert! log_c_189.1 using 1; norm_num)
    log_v_189.2 (by convert! log_c_189.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_190 : (174129033 / 62500000) ≤ -Real.log (18943 / 307200) ∧
    -Real.log (18943 / 307200) ≤ (2786064533 / 1000000000) := by
  have h := checkLog_sound (w := (257 / 38143)) (n := 12)
    (lo := (421119 / 31250000)) (hi := (13475809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 18943) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(19200 / 18943) = 1/(18943 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_190 : (63646557 / 1000000000) ≤ -Real.log (288257 / 307200) ∧
    -Real.log (288257 / 307200) ≤ (31823279 / 500000000) := by
  have h := checkLog_sound (w := (18943 / 595457)) (n := 12)
    (lo := (63646557 / 1000000000)) (hi := (31823279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 288257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 288257) = 1/(288257 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_190 : (272241797 / 200000000) ≤ xi (18943 / 307200) ∧ xi (18943 / 307200) ≤ (340302247 / 250000000) ∧
    (569942217 / 400000000) ≤ kap (18943 / 307200) ∧ kap (18943 / 307200) ≤ (2849711091 / 2000000000) := by
  have h := endpoint_bounds (v := ((18943 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_190.1 (by convert! log_c_190.1 using 1; norm_num)
    log_v_190.2 (by convert! log_c_190.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_191 : (554392783 / 200000000) ≤ -Real.log (1601 / 25600) ∧
    -Real.log (1601 / 25600) ≤ (2771963919 / 1000000000) := by
  have h := checkLog_sound (w := (1599 / 4801)) (n := 12)
    (lo := (5540179 / 8000000)) (hi := (86565297 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1601) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1601) = 1/(1601 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_191 : (16145047 / 250000000) ≤ -Real.log (23999 / 25600) ∧
    -Real.log (23999 / 25600) ≤ (64580189 / 1000000000) := by
  have h := checkLog_sound (w := (1601 / 49599)) (n := 12)
    (lo := (16145047 / 250000000)) (hi := (64580189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25600 / 23999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25600 / 23999) = 1/(23999 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_191 : (1353691863 / 1000000000) ≤ xi (1601 / 25600) ∧ xi (1601 / 25600) ≤ (2707383731 / 2000000000) ∧
    (2836544103 / 2000000000) ≤ kap (1601 / 25600) ∧ kap (1601 / 25600) ≤ (709136027 / 500000000) := by
  have h := endpoint_bounds (v := ((1601 / 25600) : ℝ)) (by norm_num) (by norm_num)
    log_v_191.1 (by convert! log_c_191.1 using 1; norm_num)
    log_v_191.2 (by convert! log_c_191.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.EntropyCurvature


