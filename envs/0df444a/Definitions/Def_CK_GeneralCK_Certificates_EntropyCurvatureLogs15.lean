-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs15
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLogs15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:41:40.608417+00:00
-- url     : https://prove2.me/theorems/a351578b-ca2b-4430-95e0-9a66c6c51ea6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLogs15` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLogs15` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLogs15` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLogs15 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLogs15.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureBounds

namespace GeneralCK.Certificates.EntropyCurvature
open Mixed GeneralCK.EntropyCurvature

theorem log_v_240 : (862634863 / 500000000) ≤ -Real.log (57 / 320) ∧
    -Real.log (57 / 320) ≤ (1725269729 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 137)) (n := 12)
    (lo := (169487683 / 500000000)) (hi := (338975367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 57) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 57) = 1/(57 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_240 : (196166963 / 1000000000) ≤ -Real.log (263 / 320) ∧
    -Real.log (263 / 320) ≤ (49041741 / 250000000) := by
  have h := checkLog_sound (w := (57 / 583)) (n := 12)
    (lo := (196166963 / 1000000000)) (hi := (49041741 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 263) = 1/(263 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_240 : (764551381 / 1000000000) ≤ xi (57 / 320) ∧ xi (57 / 320) ≤ (764551383 / 1000000000) ∧
    (1921436689 / 2000000000) ≤ kap (57 / 320) ∧ kap (57 / 320) ≤ (1921436693 / 2000000000) := by
  have h := endpoint_bounds (v := ((57 / 320) : ℝ)) (by norm_num) (by norm_num)
    log_v_240.1 (by convert! log_c_240.1 using 1; norm_num)
    log_v_240.2 (by convert! log_c_240.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_241 : (1686695871 / 1000000000) ≤ -Real.log (7109 / 38400) ∧
    -Real.log (7109 / 38400) ≤ (843347937 / 500000000) := by
  have h := checkLog_sound (w := (2491 / 16709)) (n := 12)
    (lo := (300401511 / 1000000000)) (hi := (37550189 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 7109) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(9600 / 7109) = 1/(7109 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_241 : (204726943 / 1000000000) ≤ -Real.log (31291 / 38400) ∧
    -Real.log (31291 / 38400) ≤ (6397717 / 31250000) := by
  have h := checkLog_sound (w := (7109 / 69691)) (n := 12)
    (lo := (204726943 / 1000000000)) (hi := (6397717 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 31291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38400 / 31291) = 1/(31291 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_241 : (1481968927 / 2000000000) ≤ xi (7109 / 38400) ∧ xi (7109 / 38400) ≤ (1481968931 / 2000000000) ∧
    (945711407 / 1000000000) ≤ kap (7109 / 38400) ∧ kap (7109 / 38400) ≤ (945711409 / 1000000000) := by
  have h := endpoint_bounds (v := ((7109 / 38400) : ℝ)) (by norm_num) (by norm_num)
    log_v_241.1 (by convert! log_c_241.1 using 1; norm_num)
    log_v_241.2 (by convert! log_c_241.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_242 : (1649554859 / 1000000000) ≤ -Real.log (3689 / 19200) ∧
    -Real.log (3689 / 19200) ≤ (824777431 / 500000000) := by
  have h := checkLog_sound (w := (1111 / 8489)) (n := 12)
    (lo := (263260499 / 1000000000)) (hi := (526521 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4800 / 3689) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(4800 / 3689) = 1/(3689 / 19200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_242 : (213360829 / 1000000000) ≤ -Real.log (15511 / 19200) ∧
    -Real.log (15511 / 19200) ≤ (21336083 / 100000000) := by
  have h := checkLog_sound (w := (3689 / 34711)) (n := 12)
    (lo := (213360829 / 1000000000)) (hi := (21336083 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 15511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19200 / 15511) = 1/(15511 / 19200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_242 : (1436194029 / 2000000000) ≤ xi (3689 / 19200) ∧ xi (3689 / 19200) ≤ (1436194033 / 2000000000) ∧
    (232864461 / 250000000) ≤ kap (3689 / 19200) ∧ kap (3689 / 19200) ≤ (465728923 / 500000000) := by
  have h := endpoint_bounds (v := ((3689 / 19200) : ℝ)) (by norm_num) (by norm_num)
    log_v_242.1 (by convert! log_c_242.1 using 1; norm_num)
    log_v_242.2 (by convert! log_c_242.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_243 : (403436011 / 250000000) ≤ -Real.log (2549 / 12800) ∧
    -Real.log (2549 / 12800) ≤ (1613744047 / 1000000000) := by
  have h := checkLog_sound (w := (651 / 5749)) (n := 12)
    (lo := (56862421 / 250000000)) (hi := (45489937 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2549) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 2549) = 1/(2549 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_243 : (222069909 / 1000000000) ≤ -Real.log (10251 / 12800) ∧
    -Real.log (10251 / 12800) ≤ (22206991 / 100000000) := by
  have h := checkLog_sound (w := (2549 / 23051)) (n := 12)
    (lo := (222069909 / 1000000000)) (hi := (22206991 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 10251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12800 / 10251) = 1/(10251 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_243 : (695837067 / 1000000000) ≤ xi (2549 / 12800) ∧ xi (2549 / 12800) ≤ (695837069 / 1000000000) ∧
    (1835813953 / 2000000000) ≤ kap (2549 / 12800) ∧ kap (2549 / 12800) ≤ (1835813957 / 2000000000) := by
  have h := endpoint_bounds (v := ((2549 / 12800) : ℝ)) (by norm_num) (by norm_num)
    log_v_243.1 (by convert! log_c_243.1 using 1; norm_num)
    log_v_243.2 (by convert! log_c_243.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_244 : (157917143 / 100000000) ≤ -Real.log (1979 / 9600) ∧
    -Real.log (1979 / 9600) ≤ (1579171433 / 1000000000) := by
  have h := checkLog_sound (w := (421 / 4379)) (n := 12)
    (lo := (19287707 / 100000000)) (hi := (192877071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2400 / 1979) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2400 / 1979) = 1/(1979 / 9600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_244 : (230855503 / 1000000000) ≤ -Real.log (7621 / 9600) ∧
    -Real.log (7621 / 9600) ≤ (14428469 / 62500000) := by
  have h := checkLog_sound (w := (1979 / 17221)) (n := 12)
    (lo := (230855503 / 1000000000)) (hi := (14428469 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 7621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9600 / 7621) = 1/(7621 / 9600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_244 : (674157963 / 1000000000) ≤ xi (1979 / 9600) ∧ xi (1979 / 9600) ≤ (134831593 / 200000000) ∧
    (1810026933 / 2000000000) ≤ kap (1979 / 9600) ∧ kap (1979 / 9600) ≤ (1810026937 / 2000000000) := by
  have h := endpoint_bounds (v := ((1979 / 9600) : ℝ)) (by norm_num) (by norm_num)
    log_v_244.1 (by convert! log_c_244.1 using 1; norm_num)
    log_v_244.2 (by convert! log_c_244.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_245 : (1545754247 / 1000000000) ≤ -Real.log (1637 / 7680) ∧
    -Real.log (1637 / 7680) ≤ (6183017 / 4000000) := by
  have h := checkLog_sound (w := (283 / 3557)) (n := 12)
    (lo := (159459887 / 1000000000)) (hi := (9966243 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1920 / 1637) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1920 / 1637) = 1/(1637 / 7680) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_245 : (239718969 / 1000000000) ≤ -Real.log (6043 / 7680) ∧
    -Real.log (6043 / 7680) ≤ (23971897 / 100000000) := by
  have h := checkLog_sound (w := (1637 / 13723)) (n := 12)
    (lo := (239718969 / 1000000000)) (hi := (23971897 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7680 / 6043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7680 / 6043) = 1/(6043 / 7680) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_245 : (1306035277 / 2000000000) ≤ xi (1637 / 7680) ∧ xi (1637 / 7680) ≤ (1306035281 / 2000000000) ∧
    (27898019 / 31250000) ≤ kap (1637 / 7680) ∧ kap (1637 / 7680) ≤ (89273661 / 100000000) := by
  have h := endpoint_bounds (v := ((1637 / 7680) : ℝ)) (by norm_num) (by norm_num)
    log_v_245.1 (by convert! log_c_245.1 using 1; norm_num)
    log_v_245.2 (by convert! log_c_245.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_246 : (378354439 / 250000000) ≤ -Real.log (1409 / 6400) ∧
    -Real.log (1409 / 6400) ≤ (1513417759 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 3009)) (n := 12)
    (lo := (31780849 / 250000000)) (hi := (127123397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1409) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1409) = 1/(1409 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_246 : (248661699 / 1000000000) ≤ -Real.log (4991 / 6400) ∧
    -Real.log (4991 / 6400) ≤ (2486617 / 10000000) := by
  have h := checkLog_sound (w := (1409 / 11391)) (n := 12)
    (lo := (248661699 / 1000000000)) (hi := (2486617 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6400 / 4991) = 1/(4991 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_246 : (158094507 / 250000000) ≤ xi (1409 / 6400) ∧ xi (1409 / 6400) ≤ (63237803 / 100000000) ∧
    (352415891 / 400000000) ≤ kap (1409 / 6400) ∧ kap (1409 / 6400) ≤ (1762079459 / 2000000000) := by
  have h := endpoint_bounds (v := ((1409 / 6400) : ℝ)) (by norm_num) (by norm_num)
    log_v_246.1 (by convert! log_c_246.1 using 1; norm_num)
    log_v_246.2 (by convert! log_c_246.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_247 : (1482094243 / 1000000000) ≤ -Real.log (8723 / 38400) ∧
    -Real.log (8723 / 38400) ≤ (741047123 / 500000000) := by
  have h := checkLog_sound (w := (877 / 18323)) (n := 12)
    (lo := (95799883 / 1000000000)) (hi := (23949971 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 8723) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(9600 / 8723) = 1/(8723 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_247 : (64421281 / 250000000) ≤ -Real.log (29677 / 38400) ∧
    -Real.log (29677 / 38400) ≤ (2061481 / 8000000) := by
  have h := checkLog_sound (w := (8723 / 68077)) (n := 12)
    (lo := (64421281 / 250000000)) (hi := (2061481 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 29677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38400 / 29677) = 1/(29677 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_247 : (612204559 / 1000000000) ≤ xi (8723 / 38400) ∧ xi (8723 / 38400) ≤ (612204561 / 1000000000) ∧
    (1739779367 / 2000000000) ≤ kap (8723 / 38400) ∧ kap (8723 / 38400) ≤ (1739779371 / 2000000000) := by
  have h := endpoint_bounds (v := ((8723 / 38400) : ℝ)) (by norm_num) (by norm_num)
    log_v_247.1 (by convert! log_c_247.1 using 1; norm_num)
    log_v_247.2 (by convert! log_c_247.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_248 : (290344433 / 200000000) ≤ -Real.log (281 / 1200) ∧
    -Real.log (281 / 1200) ≤ (181465271 / 125000000) := by
  have h := checkLog_sound (w := (19 / 581)) (n := 12)
    (lo := (13085561 / 200000000)) (hi := (32713903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300 / 281) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(300 / 281) = 1/(281 / 1200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_248 : (266790713 / 1000000000) ≤ -Real.log (919 / 1200) ∧
    -Real.log (919 / 1200) ≤ (133395357 / 500000000) := by
  have h := checkLog_sound (w := (281 / 2119)) (n := 12)
    (lo := (266790713 / 1000000000)) (hi := (133395357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1200 / 919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1200 / 919) = 1/(919 / 1200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_248 : (1184931451 / 2000000000) ≤ xi (281 / 1200) ∧ xi (281 / 1200) ≤ (236986291 / 400000000) ∧
    (859256439 / 1000000000) ≤ kap (281 / 1200) ∧ kap (281 / 1200) ≤ (859256441 / 1000000000) := by
  have h := endpoint_bounds (v := ((281 / 1200) : ℝ)) (by norm_num) (by norm_num)
    log_v_248.1 (by convert! log_c_248.1 using 1; norm_num)
    log_v_248.2 (by convert! log_c_248.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_249 : (88890339 / 62500000) ≤ -Real.log (3087 / 12800) ∧
    -Real.log (3087 / 12800) ≤ (1422245427 / 1000000000) := by
  have h := checkLog_sound (w := (113 / 6287)) (n := 12)
    (lo := (4493883 / 125000000)) (hi := (7190213 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3087) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 3087) = 1/(3087 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_249 : (34497497 / 125000000) ≤ -Real.log (9713 / 12800) ∧
    -Real.log (9713 / 12800) ≤ (275979977 / 1000000000) := by
  have h := checkLog_sound (w := (3087 / 22513)) (n := 12)
    (lo := (34497497 / 125000000)) (hi := (275979977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 9713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12800 / 9713) = 1/(9713 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_249 : (1146265447 / 2000000000) ≤ xi (3087 / 12800) ∧ xi (3087 / 12800) ≤ (1146265451 / 2000000000) ∧
    (8491127 / 10000000) ≤ kap (3087 / 12800) ∧ kap (3087 / 12800) ≤ (424556351 / 500000000) := by
  have h := endpoint_bounds (v := ((3087 / 12800) : ℝ)) (by norm_num) (by norm_num)
    log_v_249.1 (by convert! log_c_249.1 using 1; norm_num)
    log_v_249.2 (by convert! log_c_249.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_250 : (69680637 / 50000000) ≤ -Real.log (953 / 3840) ∧
    -Real.log (953 / 3840) ≤ (1393612743 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 1913)) (n := 12)
    (lo := (365919 / 50000000)) (hi := (7318381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((960 / 953) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(960 / 953) = 1/(953 / 3840) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_250 : (57050893 / 200000000) ≤ -Real.log (2887 / 3840) ∧
    -Real.log (2887 / 3840) ≤ (142627233 / 500000000) := by
  have h := checkLog_sound (w := (953 / 6727)) (n := 12)
    (lo := (57050893 / 200000000)) (hi := (142627233 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3840 / 2887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3840 / 2887) = 1/(2887 / 3840) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_250 : (554179137 / 1000000000) ≤ xi (953 / 3840) ∧ xi (953 / 3840) ≤ (554179139 / 1000000000) ∧
    (335773441 / 400000000) ≤ kap (953 / 3840) ∧ kap (953 / 3840) ≤ (1678867209 / 2000000000) := by
  have h := endpoint_bounds (v := ((953 / 3840) : ℝ)) (by norm_num) (by norm_num)
    log_v_250.1 (by convert! log_c_250.1 using 1; norm_num)
    log_v_250.2 (by convert! log_c_250.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_251 : (1365777119 / 1000000000) ≤ -Real.log (9799 / 38400) ∧
    -Real.log (9799 / 38400) ≤ (1365777121 / 1000000000) := by
  have h := checkLog_sound (w := (9401 / 28999)) (n := 12)
    (lo := (672629939 / 1000000000)) (hi := (33631497 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 9799) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(19200 / 9799) = 1/(9799 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_251 : (294615777 / 1000000000) ≤ -Real.log (28601 / 38400) ∧
    -Real.log (28601 / 38400) ≤ (147307889 / 500000000) := by
  have h := checkLog_sound (w := (9799 / 67001)) (n := 12)
    (lo := (294615777 / 1000000000)) (hi := (147307889 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 28601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38400 / 28601) = 1/(28601 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_251 : (1071161341 / 2000000000) ≤ xi (9799 / 38400) ∧ xi (9799 / 38400) ≤ (1046056 / 1953125) ∧
    (25943639 / 31250000) ≤ kap (9799 / 38400) ∧ kap (9799 / 38400) ≤ (1660392899 / 2000000000) := by
  have h := endpoint_bounds (v := ((9799 / 38400) : ℝ)) (by norm_num) (by norm_num)
    log_v_251.1 (by convert! log_c_251.1 using 1; norm_num)
    log_v_251.2 (by convert! log_c_251.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_252 : (1338695381 / 1000000000) ≤ -Real.log (839 / 3200) ∧
    -Real.log (839 / 3200) ≤ (1338695383 / 1000000000) := by
  have h := checkLog_sound (w := (761 / 2439)) (n := 12)
    (lo := (645548201 / 1000000000)) (hi := (322774101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 839) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 839) = 1/(839 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_252 : (304065551 / 1000000000) ≤ -Real.log (2361 / 3200) ∧
    -Real.log (2361 / 3200) ≤ (19004097 / 62500000) := by
  have h := checkLog_sound (w := (839 / 5561)) (n := 12)
    (lo := (304065551 / 1000000000)) (hi := (19004097 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3200 / 2361) = 1/(2361 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_252 : (1034629829 / 2000000000) ≤ xi (839 / 3200) ∧ xi (839 / 3200) ≤ (129328729 / 250000000) ∧
    (410690233 / 500000000) ≤ kap (839 / 3200) ∧ kap (839 / 3200) ≤ (328552187 / 400000000) := by
  have h := endpoint_bounds (v := ((839 / 3200) : ℝ)) (by norm_num) (by norm_num)
    log_v_252.1 (by convert! log_c_252.1 using 1; norm_num)
    log_v_252.2 (by convert! log_c_252.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_253 : (1312327767 / 1000000000) ≤ -Real.log (10337 / 38400) ∧
    -Real.log (10337 / 38400) ≤ (1312327769 / 1000000000) := by
  have h := checkLog_sound (w := (8863 / 29537)) (n := 12)
    (lo := (619180587 / 1000000000)) (hi := (154795147 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 10337) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(19200 / 10337) = 1/(10337 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_253 : (78401369 / 250000000) ≤ -Real.log (28063 / 38400) ∧
    -Real.log (28063 / 38400) ≤ (313605477 / 1000000000) := by
  have h := checkLog_sound (w := (10337 / 66463)) (n := 12)
    (lo := (78401369 / 250000000)) (hi := (313605477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 28063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38400 / 28063) = 1/(28063 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_253 : (99872229 / 200000000) ≤ xi (10337 / 38400) ∧ xi (10337 / 38400) ≤ (998722293 / 2000000000) ∧
    (1625933243 / 2000000000) ≤ kap (10337 / 38400) ∧ kap (10337 / 38400) ≤ (812966623 / 1000000000) := by
  have h := endpoint_bounds (v := ((10337 / 38400) : ℝ)) (by norm_num) (by norm_num)
    log_v_253.1 (by convert! log_c_253.1 using 1; norm_num)
    log_v_253.2 (by convert! log_c_253.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_254 : (64331879 / 50000000) ≤ -Real.log (5303 / 19200) ∧
    -Real.log (5303 / 19200) ≤ (643318791 / 500000000) := by
  have h := checkLog_sound (w := (4297 / 14903)) (n := 12)
    (lo := (741863 / 1250000)) (hi := (593490401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 5303) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(9600 / 5303) = 1/(5303 / 19200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_254 : (323237289 / 1000000000) ≤ -Real.log (13897 / 19200) ∧
    -Real.log (13897 / 19200) ≤ (32323729 / 100000000) := by
  have h := checkLog_sound (w := (5303 / 33097)) (n := 12)
    (lo := (323237289 / 1000000000)) (hi := (32323729 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 13897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19200 / 13897) = 1/(13897 / 19200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_254 : (96340029 / 200000000) ≤ xi (5303 / 19200) ∧ xi (5303 / 19200) ≤ (963400293 / 2000000000) ∧
    (1609874869 / 2000000000) ≤ kap (5303 / 19200) ∧ kap (5303 / 19200) ≤ (201234359 / 250000000) := by
  have h := endpoint_bounds (v := ((5303 / 19200) : ℝ)) (by norm_num) (by norm_num)
    log_v_254.1 (by convert! log_c_254.1 using 1; norm_num)
    log_v_254.2 (by convert! log_c_254.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_255 : (630795441 / 500000000) ≤ -Real.log (145 / 512) ∧
    -Real.log (145 / 512) ≤ (315397721 / 250000000) := by
  have h := checkLog_sound (w := (111 / 401)) (n := 12)
    (lo := (284221851 / 500000000)) (hi := (568443703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 145) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 145) = 1/(145 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_255 : (41620347 / 125000000) ≤ -Real.log (367 / 512) ∧
    -Real.log (367 / 512) ≤ (332962777 / 1000000000) := by
  have h := checkLog_sound (w := (145 / 879)) (n := 12)
    (lo := (41620347 / 125000000)) (hi := (332962777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 367) = 1/(367 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_255 : (185725621 / 400000000) ≤ xi (145 / 512) ∧ xi (145 / 512) ≤ (232157027 / 500000000) ∧
    (797276829 / 1000000000) ≤ kap (145 / 512) ∧ kap (145 / 512) ≤ (1594553661 / 2000000000) := by
  have h := endpoint_bounds (v := ((145 / 512) : ℝ)) (by norm_num) (by norm_num)
    log_v_255.1 (by convert! log_c_255.1 using 1; norm_num)
    log_v_255.2 (by convert! log_c_255.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.EntropyCurvature


