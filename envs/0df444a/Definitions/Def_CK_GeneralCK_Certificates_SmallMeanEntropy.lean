-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_SmallMeanEntropy
-- name    : CK_GeneralCK_Certificates_SmallMeanEntropy
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:25:01.286578+00:00
-- url     : https://prove2.me/theorems/792dc7f0-f957-43f2-8ba1-54300d1f7026
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.SmallMeanEntropy` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.SmallMeanEntropy` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.SmallMeanEntropy` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.SmallMeanEntropy (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/SmallMeanEntropy.lean)

import Definitions.Def_CK_GeneralCK_Certificates_SmallMeanBounds

namespace GeneralCK.Certificates.SmallMean
open Mixed

theorem entropy_0 : (0 / 1) ≤ H (0 / 1) ∧ H (0 / 1) ≤ (0 / 1) := by norm_num

theorem log_v_1 : (34657359 / 10000000) ≤ -Real.log (1 / 32) ∧
    -Real.log (1 / 32) ≤ (693147181 / 200000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2 / 1) = 1/(1 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_1 : (15874349 / 500000000) ≤ -Real.log (31 / 32) ∧
    -Real.log (31 / 32) ≤ (31748699 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 63)) (n := 12)
    (lo := (15874349 / 500000000)) (hi := (31748699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 31) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32 / 31) = 1/(31 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem entropy_1 : (200622323 / 1000000000) ≤ H (1 / 32) ∧ H (1 / 32) ≤ (100311163 / 500000000) := by
  exact entropy_bounds (q := (1 / 32)) (a := (34657359 / 10000000)) (b := (15874349 / 500000000))
    (c := (693147181 / 200000000)) (d := (31748699 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    log_v_1.1 (by convert! log_c_1.1 using 1; norm_num)
    log_v_1.2 (by convert! log_c_1.2 using 1; norm_num)
    (by norm_num) (by norm_num)

theorem log_v_2 : (282720387 / 125000000) ≤ -Real.log (5 / 48) ∧
    -Real.log (5 / 48) ≤ (22617631 / 10000000) := by
  have h := checkLog_sound (w := (1 / 11)) (n := 12)
    (lo := (45580389 / 250000000)) (hi := (182321557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6 / 5) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6 / 5) = 1/(5 / 48) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_2 : (22000179 / 200000000) ≤ -Real.log (43 / 48) ∧
    -Real.log (43 / 48) ≤ (429691 / 3906250) := by
  have h := checkLog_sound (w := (5 / 91)) (n := 12)
    (lo := (22000179 / 200000000)) (hi := (429691 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48 / 43) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48 / 43) = 1/(43 / 48) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem entropy_2 : (482066147 / 1000000000) ≤ H (5 / 48) ∧ H (5 / 48) ≤ (9641323 / 20000000) := by
  exact entropy_bounds (q := (5 / 48)) (a := (282720387 / 125000000)) (b := (22000179 / 200000000))
    (c := (22617631 / 10000000)) (d := (429691 / 3906250))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    log_v_2.1 (by convert! log_c_2.1 using 1; norm_num)
    log_v_2.2 (by convert! log_c_2.2 using 1; norm_num)
    (by norm_num) (by norm_num)

theorem log_v_3 : (1856297989 / 1000000000) ≤ -Real.log (5 / 32) ∧
    -Real.log (5 / 32) ≤ (232037249 / 125000000) := by
  have h := checkLog_sound (w := (3 / 13)) (n := 12)
    (lo := (470003629 / 1000000000)) (hi := (47000363 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8 / 5) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(8 / 5) = 1/(5 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_3 : (42474759 / 250000000) ≤ -Real.log (27 / 32) ∧
    -Real.log (27 / 32) ≤ (169899037 / 1000000000) := by
  have h := checkLog_sound (w := (5 / 59)) (n := 12)
    (lo := (42474759 / 250000000)) (hi := (169899037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 27) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32 / 27) = 1/(27 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem entropy_3 : (625262403 / 1000000000) ≤ H (5 / 32) ∧ H (5 / 32) ≤ (625262407 / 1000000000) := by
  exact entropy_bounds (q := (5 / 32)) (a := (1856297989 / 1000000000)) (b := (42474759 / 250000000))
    (c := (232037249 / 125000000)) (d := (169899037 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    log_v_3.1 (by convert! log_c_3.1 using 1; norm_num)
    log_v_3.2 (by convert! log_c_3.2 using 1; norm_num)
    (by norm_num) (by norm_num)

theorem log_v_4 : (392153979 / 250000000) ≤ -Real.log (5 / 24) ∧
    -Real.log (5 / 24) ≤ (1568615919 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 11)) (n := 12)
    (lo := (45580389 / 250000000)) (hi := (182321557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6 / 5) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(6 / 5) = 1/(5 / 24) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_4 : (233614851 / 1000000000) ≤ -Real.log (19 / 24) ∧
    -Real.log (19 / 24) ≤ (58403713 / 250000000) := by
  have h := checkLog_sound (w := (5 / 43)) (n := 12)
    (lo := (233614851 / 1000000000)) (hi := (58403713 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24 / 19) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24 / 19) = 1/(19 / 24) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem entropy_4 : (11535701 / 15625000) ≤ H (5 / 24) ∧ H (5 / 24) ≤ (738284869 / 1000000000) := by
  exact entropy_bounds (q := (5 / 24)) (a := (392153979 / 250000000)) (b := (233614851 / 1000000000))
    (c := (1568615919 / 1000000000)) (d := (58403713 / 250000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    log_v_4.1 (by convert! log_c_4.1 using 1; norm_num)
    log_v_4.2 (by convert! log_c_4.2 using 1; norm_num)
    (by norm_num) (by norm_num)

theorem log_v_5 : (1450832881 / 1000000000) ≤ -Real.log (15 / 64) ∧
    -Real.log (15 / 64) ≤ (362708221 / 250000000) := by
  have h := checkLog_sound (w := (1 / 31)) (n := 12)
    (lo := (64538521 / 1000000000)) (hi := (32269261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 15) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(16 / 15) = 1/(15 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_5 : (53412557 / 200000000) ≤ -Real.log (49 / 64) ∧
    -Real.log (49 / 64) ≤ (133531393 / 500000000) := by
  have h := checkLog_sound (w := (15 / 113)) (n := 12)
    (lo := (53412557 / 200000000)) (hi := (133531393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 49) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 49) = 1/(49 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem entropy_5 : (785560291 / 1000000000) ≤ H (15 / 64) ∧ H (15 / 64) ≤ (157112059 / 200000000) := by
  exact entropy_bounds (q := (15 / 64)) (a := (1450832881 / 1000000000)) (b := (53412557 / 200000000))
    (c := (362708221 / 250000000)) (d := (133531393 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    log_v_5.1 (by convert! log_c_5.1 using 1; norm_num)
    log_v_5.2 (by convert! log_c_5.2 using 1; norm_num)
    (by norm_num) (by norm_num)

theorem log_v_6 : (56649601 / 40000000) ≤ -Real.log (16282259 / 67108864) ∧
    -Real.log (16282259 / 67108864) ≤ (354060007 / 250000000) := by
  have h := checkLog_sound (w := (494957 / 33059475)) (n := 12)
    (lo := (5989133 / 200000000)) (hi := (14972833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16777216 / 16282259) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(16777216 / 16282259) = 1/(16282259 / 67108864) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_6 : (138948099 / 500000000) ≤ -Real.log (50826605 / 67108864) ∧
    -Real.log (50826605 / 67108864) ≤ (277896199 / 1000000000) := by
  have h := checkLog_sound (w := (16282259 / 117935469)) (n := 12)
    (lo := (138948099 / 500000000)) (hi := (277896199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67108864 / 50826605) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67108864 / 50826605) = 1/(50826605 / 67108864) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem entropy_6 : (3122569 / 3906250) ≤ H (16282259 / 67108864) ∧ H (16282259 / 67108864) ≤ (799377669 / 1000000000) := by
  exact entropy_bounds (q := (16282259 / 67108864)) (a := (56649601 / 40000000)) (b := (138948099 / 500000000))
    (c := (354060007 / 250000000)) (d := (277896199 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    log_v_6.1 (by convert! log_c_6.1 using 1; norm_num)
    log_v_6.2 (by convert! log_c_6.2 using 1; norm_num)
    (by norm_num) (by norm_num)

theorem log_v_7 : (1416239963 / 1000000000) ≤ -Real.log (4070565 / 16777216) ∧
    -Real.log (4070565 / 16777216) ≤ (708119983 / 500000000) := by
  have h := checkLog_sound (w := (123739 / 8264869)) (n := 12)
    (lo := (29945603 / 1000000000)) (hi := (7486401 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4194304 / 4070565) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(4194304 / 4070565) = 1/(4070565 / 16777216) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_7 : (138948109 / 500000000) ≤ -Real.log (12706651 / 16777216) ∧
    -Real.log (12706651 / 16777216) ≤ (277896219 / 1000000000) := by
  have h := checkLog_sound (w := (4070565 / 29483867)) (n := 12)
    (lo := (138948109 / 500000000)) (hi := (277896219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16777216 / 12706651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16777216 / 12706651) = 1/(12706651 / 16777216) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem entropy_7 : (799377689 / 1000000000) ≤ H (4070565 / 16777216) ∧ H (4070565 / 16777216) ≤ (799377693 / 1000000000) := by
  exact entropy_bounds (q := (4070565 / 16777216)) (a := (1416239963 / 1000000000)) (b := (138948109 / 500000000))
    (c := (708119983 / 500000000)) (d := (277896219 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    log_v_7.1 (by convert! log_c_7.1 using 1; norm_num)
    log_v_7.2 (by convert! log_c_7.2 using 1; norm_num)
    (by norm_num) (by norm_num)

theorem log_v_8 : (672736183 / 500000000) ≤ -Real.log (25 / 96) ∧
    -Real.log (25 / 96) ≤ (84092023 / 62500000) := by
  have h := checkLog_sound (w := (23 / 73)) (n := 12)
    (lo := (326162593 / 500000000)) (hi := (652325187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48 / 25) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(48 / 25) = 1/(25 / 96) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_8 : (150834157 / 500000000) ≤ -Real.log (71 / 96) ∧
    -Real.log (71 / 96) ≤ (60333663 / 200000000) := by
  have h := checkLog_sound (w := (25 / 167)) (n := 12)
    (lo := (150834157 / 500000000)) (hi := (60333663 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96 / 71) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96 / 71) = 1/(71 / 96) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem entropy_8 : (206843619 / 250000000) ≤ H (25 / 96) ∧ H (25 / 96) ≤ (10342181 / 12500000) := by
  exact entropy_bounds (q := (25 / 96)) (a := (672736183 / 500000000)) (b := (150834157 / 500000000))
    (c := (84092023 / 62500000)) (d := (60333663 / 200000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    log_v_8.1 (by convert! log_c_8.1 using 1; norm_num)
    log_v_8.2 (by convert! log_c_8.2 using 1; norm_num)
    (by norm_num) (by norm_num)

theorem log_v_9 : (1296682201 / 1000000000) ≤ -Real.log (35 / 128) ∧
    -Real.log (35 / 128) ≤ (1296682203 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 99)) (n := 12)
    (lo := (603535021 / 1000000000)) (hi := (301767511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 35) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 35) = 1/(35 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_9 : (31943077 / 100000000) ≤ -Real.log (93 / 128) ∧
    -Real.log (93 / 128) ≤ (319430771 / 1000000000) := by
  have h := checkLog_sound (w := (35 / 221)) (n := 12)
    (lo := (31943077 / 100000000)) (hi := (319430771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 93) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 93) = 1/(93 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem entropy_9 : (846354099 / 1000000000) ≤ H (35 / 128) ∧ H (35 / 128) ≤ (846354103 / 1000000000) := by
  exact entropy_bounds (q := (35 / 128)) (a := (1296682201 / 1000000000)) (b := (31943077 / 100000000))
    (c := (1296682203 / 1000000000)) (d := (319430771 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    log_v_9.1 (by convert! log_c_9.1 using 1; norm_num)
    log_v_9.2 (by convert! log_c_9.2 using 1; norm_num)
    (by norm_num) (by norm_num)

theorem log_v_10 : (625081093 / 500000000) ≤ -Real.log (55 / 192) ∧
    -Real.log (55 / 192) ≤ (312540547 / 250000000) := by
  have h := checkLog_sound (w := (41 / 151)) (n := 12)
    (lo := (278507503 / 500000000)) (hi := (557015007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96 / 55) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(96 / 55) = 1/(55 / 192) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_10 : (168757223 / 500000000) ≤ -Real.log (137 / 192) ∧
    -Real.log (137 / 192) ≤ (337514447 / 1000000000) := by
  have h := checkLog_sound (w := (55 / 329)) (n := 12)
    (lo := (168757223 / 500000000)) (hi := (337514447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((192 / 137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(192 / 137) = 1/(137 / 192) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem entropy_10 : (864102189 / 1000000000) ≤ H (55 / 192) ∧ H (55 / 192) ≤ (864102193 / 1000000000) := by
  exact entropy_bounds (q := (55 / 192)) (a := (625081093 / 500000000)) (b := (168757223 / 500000000))
    (c := (312540547 / 250000000)) (d := (337514447 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    log_v_10.1 (by convert! log_c_10.1 using 1; norm_num)
    log_v_10.2 (by convert! log_c_10.2 using 1; norm_num)
    (by norm_num) (by norm_num)

theorem log_v_11 : (1205710423 / 1000000000) ≤ -Real.log (115 / 384) ∧
    -Real.log (115 / 384) ≤ (48228417 / 40000000) := by
  have h := checkLog_sound (w := (77 / 307)) (n := 12)
    (lo := (512563243 / 1000000000)) (hi := (128140811 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((192 / 115) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(192 / 115) = 1/(115 / 384) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_11 : (88982793 / 250000000) ≤ -Real.log (269 / 384) ∧
    -Real.log (269 / 384) ≤ (355931173 / 1000000000) := by
  have h := checkLog_sound (w := (115 / 653)) (n := 12)
    (lo := (88982793 / 250000000)) (hi := (355931173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((384 / 269) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(384 / 269) = 1/(269 / 384) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem entropy_11 : (440326651 / 500000000) ≤ H (115 / 384) ∧ H (115 / 384) ≤ (440326653 / 500000000) := by
  exact entropy_bounds (q := (115 / 384)) (a := (1205710423 / 1000000000)) (b := (88982793 / 250000000))
    (c := (48228417 / 40000000)) (d := (355931173 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    log_v_11.1 (by convert! log_c_11.1 using 1; norm_num)
    log_v_11.2 (by convert! log_c_11.2 using 1; norm_num)
    (by norm_num) (by norm_num)

theorem log_v_12 : (1163150809 / 1000000000) ≤ -Real.log (5 / 16) ∧
    -Real.log (5 / 16) ≤ (1163150811 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 13)) (n := 12)
    (lo := (470003629 / 1000000000)) (hi := (47000363 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8 / 5) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(8 / 5) = 1/(5 / 16) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_12 : (374693449 / 1000000000) ≤ -Real.log (11 / 16) ∧
    -Real.log (11 / 16) ≤ (7493869 / 20000000) := by
  have h := checkLog_sound (w := (5 / 27)) (n := 12)
    (lo := (374693449 / 1000000000)) (hi := (7493869 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 11) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16 / 11) = 1/(11 / 16) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem entropy_12 : (896038231 / 1000000000) ≤ H (5 / 16) ∧ H (5 / 16) ≤ (179207647 / 200000000) := by
  exact entropy_bounds (q := (5 / 16)) (a := (1163150809 / 1000000000)) (b := (374693449 / 1000000000))
    (c := (1163150811 / 1000000000)) (d := (7493869 / 20000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    log_v_12.1 (by convert! log_c_12.1 using 1; norm_num)
    log_v_12.2 (by convert! log_c_12.2 using 1; norm_num)
    (by norm_num) (by norm_num)

theorem log_v_13 : (571265761 / 500000000) ≤ -Real.log (245 / 768) ∧
    -Real.log (245 / 768) ≤ (285632881 / 250000000) := by
  have h := checkLog_sound (w := (139 / 629)) (n := 12)
    (lo := (224692171 / 500000000)) (hi := (449384343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((384 / 245) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(384 / 245) = 1/(245 / 768) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_13 : (384208269 / 1000000000) ≤ -Real.log (523 / 768) ∧
    -Real.log (523 / 768) ≤ (38420827 / 100000000) := by
  have h := checkLog_sound (w := (245 / 1291)) (n := 12)
    (lo := (384208269 / 1000000000)) (hi := (38420827 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((768 / 523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(768 / 523) = 1/(523 / 768) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem entropy_13 : (903302073 / 1000000000) ≤ H (245 / 768) ∧ H (245 / 768) ≤ (903302077 / 1000000000) := by
  exact entropy_bounds (q := (245 / 768)) (a := (571265761 / 500000000)) (b := (384208269 / 1000000000))
    (c := (285632881 / 250000000)) (d := (38420827 / 100000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    log_v_13.1 (by convert! log_c_13.1 using 1; norm_num)
    log_v_13.2 (by convert! log_c_13.2 using 1; norm_num)
    (by norm_num) (by norm_num)

theorem log_v_14 : (561164407 / 500000000) ≤ -Real.log (125 / 384) ∧
    -Real.log (125 / 384) ≤ (70145551 / 62500000) := by
  have h := checkLog_sound (w := (67 / 317)) (n := 12)
    (lo := (214590817 / 500000000)) (hi := (85836327 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((192 / 125) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(192 / 125) = 1/(125 / 384) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_14 : (39381449 / 100000000) ≤ -Real.log (259 / 384) ∧
    -Real.log (259 / 384) ≤ (393814491 / 1000000000) := by
  have h := checkLog_sound (w := (125 / 643)) (n := 12)
    (lo := (39381449 / 100000000)) (hi := (393814491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((384 / 259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(384 / 259) = 1/(259 / 384) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem entropy_14 : (45514221 / 50000000) ≤ H (125 / 384) ∧ H (125 / 384) ≤ (113785553 / 125000000) := by
  exact entropy_bounds (q := (125 / 384)) (a := (561164407 / 500000000)) (b := (39381449 / 100000000))
    (c := (70145551 / 62500000)) (d := (393814491 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    log_v_14.1 (by convert! log_c_14.1 using 1; norm_num)
    log_v_14.2 (by convert! log_c_14.2 using 1; norm_num)
    (by norm_num) (by norm_num)

theorem log_v_15 : (1102526187 / 1000000000) ≤ -Real.log (85 / 256) ∧
    -Real.log (85 / 256) ≤ (1102526189 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 213)) (n := 12)
    (lo := (409379007 / 1000000000)) (hi := (6396547 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 85) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 85) = 1/(85 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_15 : (403513887 / 1000000000) ≤ -Real.log (171 / 256) ∧
    -Real.log (171 / 256) ≤ (12609809 / 31250000) := by
  have h := checkLog_sound (w := (85 / 427)) (n := 12)
    (lo := (403513887 / 1000000000)) (hi := (12609809 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 171) = 1/(171 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem entropy_15 : (916988241 / 1000000000) ≤ H (85 / 256) ∧ H (85 / 256) ≤ (183397649 / 200000000) := by
  exact entropy_bounds (q := (85 / 256)) (a := (1102526187 / 1000000000)) (b := (403513887 / 1000000000))
    (c := (1102526189 / 1000000000)) (d := (12609809 / 31250000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    log_v_15.1 (by convert! log_c_15.1 using 1; norm_num)
    log_v_15.2 (by convert! log_c_15.2 using 1; norm_num)
    (by norm_num) (by norm_num)

theorem log_v_16 : (1083108101 / 1000000000) ≤ -Real.log (65 / 192) ∧
    -Real.log (65 / 192) ≤ (1083108103 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 161)) (n := 12)
    (lo := (389960921 / 1000000000)) (hi := (194980461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96 / 65) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(96 / 65) = 1/(65 / 192) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_16 : (82661657 / 200000000) ≤ -Real.log (127 / 192) ∧
    -Real.log (127 / 192) ≤ (206654143 / 500000000) := by
  have h := checkLog_sound (w := (65 / 319)) (n := 12)
    (lo := (82661657 / 200000000)) (hi := (206654143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((192 / 127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(192 / 127) = 1/(127 / 192) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem entropy_16 : (923416337 / 1000000000) ≤ H (65 / 192) ∧ H (65 / 192) ≤ (923416341 / 1000000000) := by
  exact entropy_bounds (q := (65 / 192)) (a := (1083108101 / 1000000000)) (b := (82661657 / 200000000))
    (c := (1083108103 / 1000000000)) (d := (206654143 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    log_v_16.1 (by convert! log_c_16.1 using 1; norm_num)
    log_v_16.2 (by convert! log_c_16.2 using 1; norm_num)
    (by norm_num) (by norm_num)

theorem log_v_17 : (532029953 / 500000000) ≤ -Real.log (265 / 768) ∧
    -Real.log (265 / 768) ≤ (266014977 / 250000000) := by
  have h := checkLog_sound (w := (119 / 649)) (n := 12)
    (lo := (185456363 / 500000000)) (hi := (370912727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((384 / 265) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(384 / 265) = 1/(265 / 768) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_17 : (423199563 / 1000000000) ≤ -Real.log (503 / 768) ∧
    -Real.log (503 / 768) ≤ (105799891 / 250000000) := by
  have h := checkLog_sound (w := (265 / 1271)) (n := 12)
    (lo := (423199563 / 1000000000)) (hi := (105799891 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((768 / 503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(768 / 503) = 1/(503 / 768) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem entropy_17 : (232392837 / 250000000) ≤ H (265 / 768) ∧ H (265 / 768) ≤ (116196419 / 125000000) := by
  exact entropy_bounds (q := (265 / 768)) (a := (532029953 / 500000000)) (b := (423199563 / 1000000000))
    (c := (266014977 / 250000000)) (d := (105799891 / 250000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    log_v_17.1 (by convert! log_c_17.1 using 1; norm_num)
    log_v_17.2 (by convert! log_c_17.2 using 1; norm_num)
    (by norm_num) (by norm_num)

theorem log_v_18 : (1045367773 / 1000000000) ≤ -Real.log (45 / 128) ∧
    -Real.log (45 / 128) ≤ (41814711 / 40000000) := by
  have h := checkLog_sound (w := (19 / 109)) (n := 12)
    (lo := (352220593 / 1000000000)) (hi := (176110297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 45) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 45) = 1/(45 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_18 : (54148707 / 125000000) ≤ -Real.log (83 / 128) ∧
    -Real.log (83 / 128) ≤ (433189657 / 1000000000) := by
  have h := checkLog_sound (w := (45 / 211)) (n := 12)
    (lo := (54148707 / 125000000)) (hi := (433189657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 83) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 83) = 1/(83 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem entropy_18 : (935455763 / 1000000000) ≤ H (45 / 128) ∧ H (45 / 128) ≤ (935455767 / 1000000000) := by
  exact entropy_bounds (q := (45 / 128)) (a := (1045367773 / 1000000000)) (b := (54148707 / 125000000))
    (c := (41814711 / 40000000)) (d := (433189657 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    log_v_18.1 (by convert! log_c_18.1 using 1; norm_num)
    log_v_18.2 (by convert! log_c_18.2 using 1; norm_num)
    (by norm_num) (by norm_num)

theorem log_v_19 : (513509317 / 500000000) ≤ -Real.log (275 / 768) ∧
    -Real.log (275 / 768) ≤ (256754659 / 250000000) := by
  have h := checkLog_sound (w := (109 / 659)) (n := 12)
    (lo := (166935727 / 500000000)) (hi := (66774291 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((384 / 275) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(384 / 275) = 1/(275 / 768) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_19 : (443280559 / 1000000000) ≤ -Real.log (493 / 768) ∧
    -Real.log (493 / 768) ≤ (5541007 / 12500000) := by
  have h := checkLog_sound (w := (275 / 1261)) (n := 12)
    (lo := (443280559 / 1000000000)) (hi := (5541007 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((768 / 493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(768 / 493) = 1/(493 / 768) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem entropy_19 : (117633991 / 125000000) ≤ H (275 / 768) ∧ H (275 / 768) ≤ (235267983 / 250000000) := by
  exact entropy_bounds (q := (275 / 768)) (a := (513509317 / 500000000)) (b := (443280559 / 1000000000))
    (c := (256754659 / 250000000)) (d := (5541007 / 12500000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    log_v_19.1 (by convert! log_c_19.1 using 1; norm_num)
    log_v_19.2 (by convert! log_c_19.2 using 1; norm_num)
    (by norm_num) (by norm_num)

theorem log_v_20 : (1009000129 / 1000000000) ≤ -Real.log (35 / 96) ∧
    -Real.log (35 / 96) ≤ (1009000131 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 83)) (n := 12)
    (lo := (315852949 / 1000000000)) (hi := (6317059 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48 / 35) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(48 / 35) = 1/(35 / 96) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_20 : (453474327 / 1000000000) ≤ -Real.log (61 / 96) ∧
    -Real.log (61 / 96) ≤ (56684291 / 125000000) := by
  have h := checkLog_sound (w := (35 / 157)) (n := 12)
    (lo := (453474327 / 1000000000)) (hi := (56684291 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96 / 61) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96 / 61) = 1/(61 / 96) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem entropy_20 : (946422049 / 1000000000) ≤ H (35 / 96) ∧ H (35 / 96) ≤ (946422053 / 1000000000) := by
  exact entropy_bounds (q := (35 / 96)) (a := (1009000129 / 1000000000)) (b := (453474327 / 1000000000))
    (c := (1009000131 / 1000000000)) (d := (56684291 / 125000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    log_v_20.1 (by convert! log_c_20.1 using 1; norm_num)
    log_v_20.2 (by convert! log_c_20.2 using 1; norm_num)
    (by norm_num) (by norm_num)

theorem log_v_21 : (973908809 / 1000000000) ≤ -Real.log (145 / 384) ∧
    -Real.log (145 / 384) ≤ (973908811 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 337)) (n := 12)
    (lo := (280761629 / 1000000000)) (hi := (28076163 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((192 / 145) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(192 / 145) = 1/(145 / 384) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_21 : (474179 / 1000000) ≤ -Real.log (239 / 384) ∧
    -Real.log (239 / 384) ≤ (474179001 / 1000000000) := by
  have h := checkLog_sound (w := (145 / 623)) (n := 12)
    (lo := (474179 / 1000000)) (hi := (474179001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((384 / 239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(384 / 239) = 1/(239 / 384) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem entropy_21 : (956332329 / 1000000000) ≤ H (145 / 384) ∧ H (145 / 384) ≤ (956332333 / 1000000000) := by
  exact entropy_bounds (q := (145 / 384)) (a := (973908809 / 1000000000)) (b := (474179 / 1000000))
    (c := (973908811 / 1000000000)) (d := (474179001 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    log_v_21.1 (by convert! log_c_21.1 using 1; norm_num)
    log_v_21.2 (by convert! log_c_21.2 using 1; norm_num)
    (by norm_num) (by norm_num)

theorem log_v_22 : (940007257 / 1000000000) ≤ -Real.log (25 / 64) ∧
    -Real.log (25 / 64) ≤ (940007259 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 57)) (n := 12)
    (lo := (246860077 / 1000000000)) (hi := (123430039 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 25) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(32 / 25) = 1/(25 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_22 : (495321437 / 1000000000) ≤ -Real.log (39 / 64) ∧
    -Real.log (39 / 64) ≤ (247660719 / 500000000) := by
  have h := checkLog_sound (w := (25 / 103)) (n := 12)
    (lo := (495321437 / 1000000000)) (hi := (247660719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 39) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 39) = 1/(39 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem entropy_22 : (965201697 / 1000000000) ≤ H (25 / 64) ∧ H (25 / 64) ≤ (965201701 / 1000000000) := by
  exact entropy_bounds (q := (25 / 64)) (a := (940007257 / 1000000000)) (b := (495321437 / 1000000000))
    (c := (940007259 / 1000000000)) (d := (247660719 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    log_v_22.1 (by convert! log_c_22.1 using 1; norm_num)
    log_v_22.2 (by convert! log_c_22.2 using 1; norm_num)
    (by norm_num) (by norm_num)

theorem log_v_23 : (13679199 / 15625000) ≤ -Real.log (5 / 12) ∧
    -Real.log (5 / 12) ≤ (437734369 / 500000000) := by
  have h := checkLog_sound (w := (1 / 11)) (n := 12)
    (lo := (45580389 / 250000000)) (hi := (182321557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6 / 5) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(6 / 5) = 1/(5 / 12) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_23 : (1077993 / 2000000) ≤ -Real.log (7 / 12) ∧
    -Real.log (7 / 12) ≤ (538996501 / 1000000000) := by
  have h := checkLog_sound (w := (5 / 19)) (n := 12)
    (lo := (1077993 / 2000000)) (hi := (538996501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12 / 7) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12 / 7) = 1/(7 / 12) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem entropy_23 : (489934377 / 500000000) ≤ H (5 / 12) ∧ H (5 / 12) ≤ (979868759 / 1000000000) := by
  exact entropy_bounds (q := (5 / 12)) (a := (13679199 / 15625000)) (b := (1077993 / 2000000))
    (c := (437734369 / 500000000)) (d := (538996501 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    log_v_23.1 (by convert! log_c_23.1 using 1; norm_num)
    log_v_23.2 (by convert! log_c_23.2 using 1; norm_num)
    (by norm_num) (by norm_num)

end GeneralCK.Certificates.SmallMean


