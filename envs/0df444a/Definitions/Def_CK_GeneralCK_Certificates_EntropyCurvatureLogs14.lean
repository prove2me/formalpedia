-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs14
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLogs14
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:41:43.23384+00:00
-- url     : https://prove2.me/theorems/9f9592ff-3668-4491-a125-d0d5eb40b543
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLogs14` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLogs14` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLogs14` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLogs14 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLogs14.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureBounds

namespace GeneralCK.Certificates.EntropyCurvature
open Mixed GeneralCK.EntropyCurvature

theorem log_v_224 : (2162144031 / 1000000000) ≤ -Real.log (1473 / 12800) ∧
    -Real.log (1473 / 12800) ≤ (432428807 / 200000000) := by
  have h := checkLog_sound (w := (127 / 3073)) (n := 12)
    (lo := (82702491 / 1000000000)) (hi := (20675623 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1473) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1473) = 1/(1473 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_224 : (61127957 / 500000000) ≤ -Real.log (11327 / 12800) ∧
    -Real.log (11327 / 12800) ≤ (24451183 / 200000000) := by
  have h := checkLog_sound (w := (1473 / 24127)) (n := 12)
    (lo := (61127957 / 500000000)) (hi := (24451183 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 11327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12800 / 11327) = 1/(11327 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_224 : (509972029 / 500000000) ≤ xi (1473 / 12800) ∧ xi (1473 / 12800) ≤ (2039888121 / 2000000000) ∧
    (456879989 / 400000000) ≤ kap (1473 / 12800) ∧ kap (1473 / 12800) ≤ (45687999 / 40000000) := by
  have h := endpoint_bounds (v := ((1473 / 12800) : ℝ)) (by norm_num) (by norm_num)
    log_v_224.1 (by convert! log_c_224.1 using 1; norm_num)
    log_v_224.2 (by convert! log_c_224.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_225 : (2132161289 / 1000000000) ≤ -Real.log (9107 / 76800) ∧
    -Real.log (9107 / 76800) ≤ (2132161293 / 1000000000) := by
  have h := checkLog_sound (w := (493 / 18707)) (n := 12)
    (lo := (52719749 / 1000000000)) (hi := (210879 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 9107) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(9600 / 9107) = 1/(9107 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_225 : (63110931 / 500000000) ≤ -Real.log (67693 / 76800) ∧
    -Real.log (67693 / 76800) ≤ (126221863 / 1000000000) := by
  have h := checkLog_sound (w := (9107 / 144493)) (n := 12)
    (lo := (63110931 / 500000000)) (hi := (126221863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 67693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76800 / 67693) = 1/(67693 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_225 : (1002969713 / 1000000000) ≤ xi (9107 / 76800) ∧ xi (9107 / 76800) ≤ (2005939431 / 2000000000) ∧
    (2258383151 / 2000000000) ≤ kap (9107 / 76800) ∧ kap (9107 / 76800) ≤ (564595789 / 500000000) := by
  have h := endpoint_bounds (v := ((9107 / 76800) : ℝ)) (by norm_num) (by norm_num)
    log_v_225.1 (by convert! log_c_225.1 using 1; norm_num)
    log_v_225.2 (by convert! log_c_225.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_226 : (420610281 / 200000000) ≤ -Real.log (293 / 2400) ∧
    -Real.log (293 / 2400) ≤ (2103051409 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 593)) (n := 12)
    (lo := (4721973 / 200000000)) (hi := (11804933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300 / 293) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(300 / 293) = 1/(293 / 2400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_226 : (65101801 / 500000000) ≤ -Real.log (2107 / 2400) ∧
    -Real.log (2107 / 2400) ≤ (130203603 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 4507)) (n := 12)
    (lo := (65101801 / 500000000)) (hi := (130203603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2400 / 2107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2400 / 2107) = 1/(2107 / 2400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_226 : (986423901 / 1000000000) ≤ xi (293 / 2400) ∧ xi (293 / 2400) ≤ (1972847807 / 2000000000) ∧
    (2233255007 / 2000000000) ≤ kap (293 / 2400) ∧ kap (293 / 2400) ≤ (558313753 / 500000000) := by
  have h := endpoint_bounds (v := ((293 / 2400) : ℝ)) (by norm_num) (by norm_num)
    log_v_226.1 (by convert! log_c_226.1 using 1; norm_num)
    log_v_226.2 (by convert! log_c_226.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_227 : (32418203 / 15625000) ≤ -Real.log (643 / 5120) ∧
    -Real.log (643 / 5120) ≤ (414952999 / 200000000) := by
  have h := checkLog_sound (w := (637 / 1923)) (n := 12)
    (lo := (86058829 / 125000000)) (hi := (688470633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 643) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1280 / 643) = 1/(643 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_227 : (134201259 / 1000000000) ≤ -Real.log (4477 / 5120) ∧
    -Real.log (4477 / 5120) ≤ (6710063 / 50000000) := by
  have h := checkLog_sound (w := (643 / 9597)) (n := 12)
    (lo := (134201259 / 1000000000)) (hi := (6710063 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4477) = 1/(4477 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_227 : (485140933 / 500000000) ≤ xi (643 / 5120) ∧ xi (643 / 5120) ≤ (242570467 / 250000000) ∧
    (2208966251 / 2000000000) ≤ kap (643 / 5120) ∧ kap (643 / 5120) ≤ (441793251 / 400000000) := by
  have h := endpoint_bounds (v := ((643 / 5120) : ℝ)) (by norm_num) (by norm_num)
    log_v_227.1 (by convert! log_c_227.1 using 1; norm_num)
    log_v_227.2 (by convert! log_c_227.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_228 : (2047256739 / 1000000000) ≤ -Real.log (4957 / 38400) ∧
    -Real.log (4957 / 38400) ≤ (1023628371 / 500000000) := by
  have h := checkLog_sound (w := (4643 / 14557)) (n := 12)
    (lo := (660962379 / 1000000000)) (hi := (33048119 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 4957) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(9600 / 4957) = 1/(4957 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_228 : (69107481 / 500000000) ≤ -Real.log (33443 / 38400) ∧
    -Real.log (33443 / 38400) ≤ (138214963 / 1000000000) := by
  have h := checkLog_sound (w := (4957 / 71843)) (n := 12)
    (lo := (69107481 / 500000000)) (hi := (138214963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 33443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38400 / 33443) = 1/(33443 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_228 : (119315111 / 125000000) ≤ xi (4957 / 38400) ∧ xi (4957 / 38400) ≤ (95452089 / 100000000) ∧
    (2185471701 / 2000000000) ≤ kap (4957 / 38400) ∧ kap (4957 / 38400) ≤ (437094341 / 400000000) := by
  have h := endpoint_bounds (v := ((4957 / 38400) : ℝ)) (by norm_num) (by norm_num)
    log_v_228.1 (by convert! log_c_228.1 using 1; norm_num)
    log_v_228.2 (by convert! log_c_228.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_229 : (80819399 / 40000000) ≤ -Real.log (10183 / 76800) ∧
    -Real.log (10183 / 76800) ≤ (1010242489 / 500000000) := by
  have h := checkLog_sound (w := (9017 / 29383)) (n := 12)
    (lo := (126838123 / 200000000)) (hi := (79273827 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 10183) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(19200 / 10183) = 1/(10183 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_229 : (142244839 / 1000000000) ≤ -Real.log (66617 / 76800) ∧
    -Real.log (66617 / 76800) ≤ (3556121 / 25000000) := by
  have h := checkLog_sound (w := (10183 / 143417)) (n := 12)
    (lo := (142244839 / 1000000000)) (hi := (3556121 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 66617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76800 / 66617) = 1/(66617 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_229 : (375648027 / 400000000) ≤ xi (10183 / 76800) ∧ xi (10183 / 76800) ≤ (1878240139 / 2000000000) ∧
    (1081364907 / 1000000000) ≤ kap (10183 / 76800) ∧ kap (10183 / 76800) ≤ (1081364909 / 1000000000) := by
  have h := endpoint_bounds (v := ((10183 / 76800) : ℝ)) (by norm_num) (by norm_num)
    log_v_229.1 (by convert! log_c_229.1 using 1; norm_num)
    log_v_229.2 (by convert! log_c_229.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_230 : (1994411291 / 1000000000) ≤ -Real.log (871 / 6400) ∧
    -Real.log (871 / 6400) ≤ (997205647 / 500000000) := by
  have h := checkLog_sound (w := (729 / 2471)) (n := 12)
    (lo := (608116931 / 1000000000)) (hi := (152029233 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 871) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 871) = 1/(871 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_230 : (146291023 / 1000000000) ≤ -Real.log (5529 / 6400) ∧
    -Real.log (5529 / 6400) ≤ (9143189 / 62500000) := by
  have h := checkLog_sound (w := (871 / 11929)) (n := 12)
    (lo := (146291023 / 1000000000)) (hi := (9143189 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 5529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6400 / 5529) = 1/(5529 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_230 : (1848120267 / 2000000000) ≤ xi (871 / 6400) ∧ xi (871 / 6400) ≤ (1848120271 / 2000000000) ∧
    (1070351157 / 1000000000) ≤ kap (871 / 6400) ∧ kap (871 / 6400) ≤ (1070351159 / 1000000000) := by
  have h := endpoint_bounds (v := ((871 / 6400) : ℝ)) (by norm_num) (by norm_num)
    log_v_230.1 (by convert! log_c_230.1 using 1; norm_num)
    log_v_230.2 (by convert! log_c_230.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_231 : (492250051 / 250000000) ≤ -Real.log (10721 / 76800) ∧
    -Real.log (10721 / 76800) ≤ (1969000207 / 1000000000) := by
  have h := checkLog_sound (w := (8479 / 29921)) (n := 12)
    (lo := (145676461 / 250000000)) (hi := (116541169 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 10721) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(19200 / 10721) = 1/(10721 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_231 : (37588411 / 250000000) ≤ -Real.log (66079 / 76800) ∧
    -Real.log (66079 / 76800) ≤ (30070729 / 200000000) := by
  have h := checkLog_sound (w := (10721 / 142879)) (n := 12)
    (lo := (37588411 / 250000000)) (hi := (30070729 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 66079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76800 / 66079) = 1/(66079 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_231 : (1818646559 / 2000000000) ≤ xi (10721 / 76800) ∧ xi (10721 / 76800) ≤ (1818646563 / 2000000000) ∧
    (264919231 / 250000000) ≤ kap (10721 / 76800) ∧ kap (10721 / 76800) ≤ (529838463 / 500000000) := by
  have h := endpoint_bounds (v := ((10721 / 76800) : ℝ)) (by norm_num) (by norm_num)
    log_v_231.1 (by convert! log_c_231.1 using 1; norm_num)
    log_v_231.2 (by convert! log_c_231.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_232 : (194421887 / 100000000) ≤ -Real.log (1099 / 7680) ∧
    -Real.log (1099 / 7680) ≤ (1944218873 / 1000000000) := by
  have h := checkLog_sound (w := (821 / 3019)) (n := 12)
    (lo := (55792451 / 100000000)) (hi := (557924511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1920 / 1099) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1920 / 1099) = 1/(1099 / 7680) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_232 : (154432837 / 1000000000) ≤ -Real.log (6581 / 7680) ∧
    -Real.log (6581 / 7680) ≤ (77216419 / 500000000) := by
  have h := checkLog_sound (w := (1099 / 14261)) (n := 12)
    (lo := (154432837 / 1000000000)) (hi := (77216419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7680 / 6581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7680 / 6581) = 1/(6581 / 7680) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_232 : (111861627 / 125000000) ≤ xi (1099 / 7680) ∧ xi (1099 / 7680) ≤ (447446509 / 500000000) ∧
    (2098651707 / 2000000000) ≤ kap (1099 / 7680) ∧ kap (1099 / 7680) ≤ (2098651711 / 2000000000) := by
  have h := endpoint_bounds (v := ((1099 / 7680) : ℝ)) (by norm_num) (by norm_num)
    log_v_232.1 (by convert! log_c_232.1 using 1; norm_num)
    log_v_232.2 (by convert! log_c_232.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_233 : (192003683 / 100000000) ≤ -Real.log (3753 / 25600) ∧
    -Real.log (3753 / 25600) ≤ (1920036833 / 1000000000) := by
  have h := checkLog_sound (w := (2647 / 10153)) (n := 12)
    (lo := (53374247 / 100000000)) (hi := (533742471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 3753) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(6400 / 3753) = 1/(3753 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_233 : (158528739 / 1000000000) ≤ -Real.log (21847 / 25600) ∧
    -Real.log (21847 / 25600) ≤ (7926437 / 50000000) := by
  have h := checkLog_sound (w := (3753 / 47447)) (n := 12)
    (lo := (158528739 / 1000000000)) (hi := (7926437 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25600 / 21847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25600 / 21847) = 1/(21847 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_233 : (176150809 / 200000000) ≤ xi (3753 / 25600) ∧ xi (3753 / 25600) ≤ (880754047 / 1000000000) ∧
    (2078565569 / 2000000000) ≤ kap (3753 / 25600) ∧ kap (3753 / 25600) ≤ (2078565573 / 2000000000) := by
  have h := endpoint_bounds (v := ((3753 / 25600) : ℝ)) (by norm_num) (by norm_num)
    log_v_233.1 (by convert! log_c_233.1 using 1; norm_num)
    log_v_233.2 (by convert! log_c_233.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_234 : (94821289 / 50000000) ≤ -Real.log (1441 / 9600) ∧
    -Real.log (1441 / 9600) ≤ (1896425783 / 1000000000) := by
  have h := checkLog_sound (w := (959 / 3841)) (n := 12)
    (lo := (25506571 / 50000000)) (hi := (510131421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2400 / 1441) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2400 / 1441) = 1/(1441 / 9600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_234 : (81320743 / 500000000) ≤ -Real.log (8159 / 9600) ∧
    -Real.log (8159 / 9600) ≤ (162641487 / 1000000000) := by
  have h := checkLog_sound (w := (1441 / 17759)) (n := 12)
    (lo := (81320743 / 500000000)) (hi := (162641487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 8159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9600 / 8159) = 1/(8159 / 9600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_234 : (1733784293 / 2000000000) ≤ xi (1441 / 9600) ∧ xi (1441 / 9600) ≤ (1733784297 / 2000000000) ∧
    (1029533633 / 1000000000) ≤ kap (1441 / 9600) ∧ kap (1441 / 9600) ≤ (205906727 / 200000000) := by
  have h := endpoint_bounds (v := ((1441 / 9600) : ℝ)) (by norm_num) (by norm_num)
    log_v_234.1 (by convert! log_c_234.1 using 1; norm_num)
    log_v_234.2 (by convert! log_c_234.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_235 : (1873359377 / 1000000000) ≤ -Real.log (11797 / 76800) ∧
    -Real.log (11797 / 76800) ≤ (93667969 / 50000000) := by
  have h := checkLog_sound (w := (7403 / 30997)) (n := 12)
    (lo := (487065017 / 1000000000)) (hi := (243532509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 11797) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(19200 / 11797) = 1/(11797 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_235 : (166771217 / 1000000000) ≤ -Real.log (65003 / 76800) ∧
    -Real.log (65003 / 76800) ≤ (83385609 / 500000000) := by
  have h := checkLog_sound (w := (11797 / 141803)) (n := 12)
    (lo := (166771217 / 1000000000)) (hi := (83385609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 65003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76800 / 65003) = 1/(65003 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_235 : (1706588159 / 2000000000) ≤ xi (11797 / 76800) ∧ xi (11797 / 76800) ≤ (1706588163 / 2000000000) ∧
    (1020065297 / 1000000000) ≤ kap (11797 / 76800) ∧ kap (11797 / 76800) ≤ (1020065299 / 1000000000) := by
  have h := endpoint_bounds (v := ((11797 / 76800) : ℝ)) (by norm_num) (by norm_num)
    log_v_235.1 (by convert! log_c_235.1 using 1; norm_num)
    log_v_235.2 (by convert! log_c_235.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_236 : (1850813059 / 1000000000) ≤ -Real.log (2011 / 12800) ∧
    -Real.log (2011 / 12800) ≤ (925406531 / 500000000) := by
  have h := checkLog_sound (w := (1189 / 5211)) (n := 12)
    (lo := (464518699 / 1000000000)) (hi := (4645187 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2011) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 2011) = 1/(2011 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_236 : (85459037 / 500000000) ≤ -Real.log (10789 / 12800) ∧
    -Real.log (10789 / 12800) ≤ (6836723 / 40000000) := by
  have h := checkLog_sound (w := (2011 / 23589)) (n := 12)
    (lo := (85459037 / 500000000)) (hi := (6836723 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 10789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12800 / 10789) = 1/(10789 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_236 : (209986873 / 250000000) ≤ xi (2011 / 12800) ∧ xi (2011 / 12800) ≤ (419973747 / 500000000) ∧
    (2021731133 / 2000000000) ≤ kap (2011 / 12800) ∧ kap (2011 / 12800) ≤ (2021731137 / 2000000000) := by
  have h := endpoint_bounds (v := ((2011 / 12800) : ℝ)) (by norm_num) (by norm_num)
    log_v_236.1 (by convert! log_c_236.1 using 1; norm_num)
    log_v_236.2 (by convert! log_c_236.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_237 : (1828763889 / 1000000000) ≤ -Real.log (2467 / 15360) ∧
    -Real.log (2467 / 15360) ≤ (457190973 / 250000000) := by
  have h := checkLog_sound (w := (1373 / 6307)) (n := 12)
    (lo := (442469529 / 1000000000)) (hi := (44246953 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3840 / 2467) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3840 / 2467) = 1/(2467 / 15360) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_237 : (175082199 / 1000000000) ≤ -Real.log (12893 / 15360) ∧
    -Real.log (12893 / 15360) ≤ (875411 / 5000000) := by
  have h := checkLog_sound (w := (2467 / 28253)) (n := 12)
    (lo := (175082199 / 1000000000)) (hi := (875411 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15360 / 12893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15360 / 12893) = 1/(12893 / 15360) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_237 : (1653681689 / 2000000000) ≤ xi (2467 / 15360) ∧ xi (2467 / 15360) ≤ (1653681693 / 2000000000) ∧
    (250480761 / 250000000) ≤ kap (2467 / 15360) ∧ kap (2467 / 15360) ≤ (500961523 / 500000000) := by
  have h := endpoint_bounds (v := ((2467 / 15360) : ℝ)) (by norm_num) (by norm_num)
    log_v_237.1 (by convert! log_c_237.1 using 1; norm_num)
    log_v_237.2 (by convert! log_c_237.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_238 : (361438083 / 200000000) ≤ -Real.log (3151 / 19200) ∧
    -Real.log (3151 / 19200) ≤ (903595209 / 500000000) := by
  have h := checkLog_sound (w := (1649 / 7951)) (n := 12)
    (lo := (84179211 / 200000000)) (hi := (52612007 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4800 / 3151) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(4800 / 3151) = 1/(3151 / 19200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_238 : (22407967 / 125000000) ≤ -Real.log (16049 / 19200) ∧
    -Real.log (16049 / 19200) ≤ (179263737 / 1000000000) := by
  have h := checkLog_sound (w := (3151 / 35249)) (n := 12)
    (lo := (22407967 / 125000000)) (hi := (179263737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 16049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19200 / 16049) = 1/(16049 / 19200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_238 : (813963339 / 1000000000) ≤ xi (3151 / 19200) ∧ xi (3151 / 19200) ≤ (813963341 / 1000000000) ∧
    (1986454151 / 2000000000) ≤ kap (3151 / 19200) ∧ kap (3151 / 19200) ≤ (397290831 / 400000000) := by
  have h := endpoint_bounds (v := ((3151 / 19200) : ℝ)) (by norm_num) (by norm_num)
    log_v_238.1 (by convert! log_c_238.1 using 1; norm_num)
    log_v_238.2 (by convert! log_c_238.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_239 : (176539143 / 100000000) ≤ -Real.log (6571 / 38400) ∧
    -Real.log (6571 / 38400) ≤ (1765391433 / 1000000000) := by
  have h := checkLog_sound (w := (3029 / 16171)) (n := 12)
    (lo := (37909707 / 100000000)) (hi := (379097071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 6571) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(9600 / 6571) = 1/(6571 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_239 : (37535927 / 200000000) ≤ -Real.log (31829 / 38400) ∧
    -Real.log (31829 / 38400) ≤ (46919909 / 250000000) := by
  have h := checkLog_sound (w := (6571 / 70229)) (n := 12)
    (lo := (37535927 / 200000000)) (hi := (46919909 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 31829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38400 / 31829) = 1/(31829 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_239 : (788855897 / 1000000000) ≤ xi (6571 / 38400) ∧ xi (6571 / 38400) ≤ (788855899 / 1000000000) ∧
    (390614213 / 400000000) ≤ kap (6571 / 38400) ∧ kap (6571 / 38400) ≤ (1953071069 / 2000000000) := by
  have h := endpoint_bounds (v := ((6571 / 38400) : ℝ)) (by norm_num) (by norm_num)
    log_v_239.1 (by convert! log_c_239.1 using 1; norm_num)
    log_v_239.2 (by convert! log_c_239.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.EntropyCurvature


