-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs19
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLogs19
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:44:21.021225+00:00
-- url     : https://prove2.me/theorems/048e6e7b-7513-4b85-afe9-2bf996ef554e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLogs19` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLogs19` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLogs19` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLogs19 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLogs19.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureBounds

namespace GeneralCK.Certificates.EntropyCurvature
open Mixed GeneralCK.EntropyCurvature

theorem log_v_304 : (165019001 / 200000000) ≤ -Real.log (44871 / 102400) ∧
    -Real.log (44871 / 102400) ≤ (825095007 / 1000000000) := by
  have h := checkLog_sound (w := (6329 / 96071)) (n := 12)
    (lo := (5277913 / 40000000)) (hi := (65973913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51200 / 44871) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(51200 / 44871) = 1/(44871 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_304 : (72074693 / 125000000) ≤ -Real.log (57529 / 102400) ∧
    -Real.log (57529 / 102400) ≤ (115319509 / 200000000) := by
  have h := checkLog_sound (w := (44871 / 159929)) (n := 12)
    (lo := (72074693 / 125000000)) (hi := (115319509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102400 / 57529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102400 / 57529) = 1/(57529 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_304 : (12424873 / 100000000) ≤ xi (44871 / 102400) ∧ xi (44871 / 102400) ≤ (248497463 / 2000000000) ∧
    (1401692549 / 2000000000) ≤ kap (44871 / 102400) ∧ kap (44871 / 102400) ≤ (175211569 / 250000000) := by
  have h := endpoint_bounds (v := ((44871 / 102400) : ℝ)) (by norm_num) (by norm_num)
    log_v_304.1 (by convert! log_c_304.1 using 1; norm_num)
    log_v_304.2 (by convert! log_c_304.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_305 : (411549339 / 500000000) ≤ -Real.log (67441 / 153600) ∧
    -Real.log (67441 / 153600) ≤ (20577467 / 25000000) := by
  have h := checkLog_sound (w := (9359 / 144241)) (n := 12)
    (lo := (64975749 / 500000000)) (hi := (129951499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 67441) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(76800 / 67441) = 1/(67441 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_305 : (289078697 / 500000000) ≤ -Real.log (86159 / 153600) ∧
    -Real.log (86159 / 153600) ≤ (115631479 / 200000000) := by
  have h := checkLog_sound (w := (67441 / 239759)) (n := 12)
    (lo := (289078697 / 500000000)) (hi := (115631479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 86159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153600 / 86159) = 1/(86159 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_305 : (244941283 / 2000000000) ≤ xi (67441 / 153600) ∧ xi (67441 / 153600) ≤ (122470643 / 1000000000) ∧
    (175157009 / 250000000) ≤ kap (67441 / 153600) ∧ kap (67441 / 153600) ≤ (56050243 / 80000000) := by
  have h := endpoint_bounds (v := ((67441 / 153600) : ℝ)) (by norm_num) (by norm_num)
    log_v_305.1 (by convert! log_c_305.1 using 1; norm_num)
    log_v_305.2 (by convert! log_c_305.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_306 : (102638291 / 125000000) ≤ -Real.log (135151 / 307200) ∧
    -Real.log (135151 / 307200) ≤ (82110633 / 100000000) := by
  have h := checkLog_sound (w := (18449 / 288751)) (n := 12)
    (lo := (31989787 / 250000000)) (hi := (127959149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 135151) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(153600 / 135151) = 1/(135151 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_306 : (579719681 / 1000000000) ≤ -Real.log (172049 / 307200) ∧
    -Real.log (172049 / 307200) ≤ (289859841 / 500000000) := by
  have h := checkLog_sound (w := (135151 / 479249)) (n := 12)
    (lo := (579719681 / 1000000000)) (hi := (289859841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 172049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 172049) = 1/(172049 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_306 : (120693323 / 1000000000) ≤ xi (135151 / 307200) ∧ xi (135151 / 307200) ≤ (241386649 / 2000000000) ∧
    (1400826009 / 2000000000) ≤ kap (135151 / 307200) ∧ kap (135151 / 307200) ≤ (350206503 / 500000000) := by
  have h := endpoint_bounds (v := ((135151 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_306.1 (by convert! log_c_306.1 using 1; norm_num)
    log_v_306.2 (by convert! log_c_306.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_307 : (40955897 / 50000000) ≤ -Real.log (2257 / 5120) ∧
    -Real.log (2257 / 5120) ≤ (409558971 / 500000000) := by
  have h := checkLog_sound (w := (303 / 4817)) (n := 12)
    (lo := (3149269 / 25000000)) (hi := (125970761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2257) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2257) = 1/(2257 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_307 : (145321103 / 250000000) ≤ -Real.log (2863 / 5120) ∧
    -Real.log (2863 / 5120) ≤ (581284413 / 1000000000) := by
  have h := checkLog_sound (w := (2257 / 7983)) (n := 12)
    (lo := (145321103 / 250000000)) (hi := (581284413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2863) = 1/(2863 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_307 : (237833527 / 2000000000) ≤ xi (2257 / 5120) ∧ xi (2257 / 5120) ≤ (23783353 / 200000000) ∧
    (87525147 / 125000000) ≤ kap (2257 / 5120) ∧ kap (2257 / 5120) ≤ (280080471 / 400000000) := by
  have h := endpoint_bounds (v := ((2257 / 5120) : ℝ)) (by norm_num) (by norm_num)
    log_v_307.1 (by convert! log_c_307.1 using 1; norm_num)
    log_v_307.2 (by convert! log_c_307.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_308 : (408566749 / 500000000) ≤ -Real.log (135689 / 307200) ∧
    -Real.log (135689 / 307200) ≤ (1634267 / 2000000) := by
  have h := checkLog_sound (w := (17911 / 289289)) (n := 12)
    (lo := (61993159 / 500000000)) (hi := (123986319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 135689) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(153600 / 135689) = 1/(135689 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_308 : (145712899 / 250000000) ≤ -Real.log (171511 / 307200) ∧
    -Real.log (171511 / 307200) ≤ (582851597 / 1000000000) := by
  have h := checkLog_sound (w := (135689 / 478711)) (n := 12)
    (lo := (145712899 / 250000000)) (hi := (582851597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 171511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 171511) = 1/(171511 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_308 : (234281901 / 2000000000) ≤ xi (135689 / 307200) ∧ xi (135689 / 307200) ≤ (14642619 / 125000000) ∧
    (699992547 / 1000000000) ≤ kap (135689 / 307200) ∧ kap (135689 / 307200) ≤ (1399985097 / 2000000000) := by
  have h := endpoint_bounds (v := ((135689 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_308.1 (by convert! log_c_308.1 using 1; norm_num)
    log_v_308.2 (by convert! log_c_308.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_309 : (407576493 / 500000000) ≤ -Real.log (67979 / 153600) ∧
    -Real.log (67979 / 153600) ≤ (203788247 / 250000000) := by
  have h := checkLog_sound (w := (8821 / 144779)) (n := 12)
    (lo := (61002903 / 500000000)) (hi := (122005807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 67979) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(76800 / 67979) = 1/(67979 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_309 : (14610531 / 25000000) ≤ -Real.log (85621 / 153600) ∧
    -Real.log (85621 / 153600) ≤ (584421241 / 1000000000) := by
  have h := checkLog_sound (w := (67979 / 239221)) (n := 12)
    (lo := (14610531 / 25000000)) (hi := (584421241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 85621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153600 / 85621) = 1/(85621 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_309 : (46146349 / 400000000) ≤ xi (67979 / 153600) ∧ xi (67979 / 153600) ≤ (57682937 / 500000000) ∧
    (699787113 / 1000000000) ≤ kap (67979 / 153600) ∧ kap (67979 / 153600) ≤ (1399574229 / 2000000000) := by
  have h := endpoint_bounds (v := ((67979 / 153600) : ℝ)) (by norm_num) (by norm_num)
    log_v_309.1 (by convert! log_c_309.1 using 1; norm_num)
    log_v_309.2 (by convert! log_c_309.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_310 : (203294097 / 250000000) ≤ -Real.log (45409 / 102400) ∧
    -Real.log (45409 / 102400) ≤ (81317639 / 100000000) := by
  have h := checkLog_sound (w := (5791 / 96609)) (n := 12)
    (lo := (15003651 / 125000000)) (hi := (120029209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51200 / 45409) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(51200 / 45409) = 1/(45409 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_310 : (585993351 / 1000000000) ≤ -Real.log (56991 / 102400) ∧
    -Real.log (56991 / 102400) ≤ (73249169 / 125000000) := by
  have h := checkLog_sound (w := (45409 / 159391)) (n := 12)
    (lo := (585993351 / 1000000000)) (hi := (73249169 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102400 / 56991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102400 / 56991) = 1/(56991 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_310 : (56795759 / 500000000) ≤ xi (45409 / 102400) ∧ xi (45409 / 102400) ≤ (227183039 / 2000000000) ∧
    (1399169739 / 2000000000) ≤ kap (45409 / 102400) ∧ kap (45409 / 102400) ≤ (699584871 / 1000000000) := by
  have h := endpoint_bounds (v := ((45409 / 102400) : ℝ)) (by norm_num) (by norm_num)
    log_v_310.1 (by convert! log_c_310.1 using 1; norm_num)
    log_v_310.2 (by convert! log_c_310.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_311 : (812189553 / 1000000000) ≤ -Real.log (272723 / 614400) ∧
    -Real.log (272723 / 614400) ≤ (162437911 / 200000000) := by
  have h := checkLog_sound (w := (34477 / 579923)) (n := 12)
    (lo := (119042373 / 1000000000)) (hi := (59521187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 272723) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(307200 / 272723) = 1/(272723 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_311 : (117356067 / 200000000) ≤ -Real.log (341677 / 614400) ∧
    -Real.log (341677 / 614400) ≤ (36673771 / 62500000) := by
  have h := checkLog_sound (w := (272723 / 956077)) (n := 12)
    (lo := (117356067 / 200000000)) (hi := (36673771 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 341677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 341677) = 1/(341677 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_311 : (225409217 / 2000000000) ≤ xi (272723 / 614400) ∧ xi (272723 / 614400) ≤ (11270461 / 100000000) ∧
    (43717809 / 62500000) ≤ kap (272723 / 614400) ∧ kap (272723 / 614400) ≤ (1398969891 / 2000000000) := by
  have h := endpoint_bounds (v := ((272723 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_311.1 (by convert! log_c_311.1 using 1; norm_num)
    log_v_311.2 (by convert! log_c_311.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_312 : (81120369 / 100000000) ≤ -Real.log (8531 / 19200) ∧
    -Real.log (8531 / 19200) ≤ (202800923 / 250000000) := by
  have h := checkLog_sound (w := (1069 / 18131)) (n := 12)
    (lo := (11805651 / 100000000)) (hi := (118056511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 8531) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(9600 / 8531) = 1/(8531 / 19200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_312 : (293783969 / 500000000) ≤ -Real.log (10669 / 19200) ∧
    -Real.log (10669 / 19200) ≤ (587567939 / 1000000000) := by
  have h := checkLog_sound (w := (8531 / 29869)) (n := 12)
    (lo := (293783969 / 500000000)) (hi := (587567939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 10669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19200 / 10669) = 1/(10669 / 19200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_312 : (223635751 / 2000000000) ≤ xi (8531 / 19200) ∧ xi (8531 / 19200) ≤ (111817877 / 1000000000) ∧
    (349692907 / 500000000) ≤ kap (8531 / 19200) ∧ kap (8531 / 19200) ≤ (1398771631 / 2000000000) := by
  have h := endpoint_bounds (v := ((8531 / 19200) : ℝ)) (by norm_num) (by norm_num)
    log_v_312.1 (by convert! log_c_312.1 using 1; norm_num)
    log_v_312.2 (by convert! log_c_312.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_313 : (405109399 / 500000000) ≤ -Real.log (91087 / 204800) ∧
    -Real.log (91087 / 204800) ≤ (2025547 / 2500000) := by
  have h := checkLog_sound (w := (11313 / 193487)) (n := 12)
    (lo := (58535809 / 500000000)) (hi := (117071619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102400 / 91087) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(102400 / 91087) = 1/(91087 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_313 : (294178081 / 500000000) ≤ -Real.log (113713 / 204800) ∧
    -Real.log (113713 / 204800) ≤ (588356163 / 1000000000) := by
  have h := checkLog_sound (w := (91087 / 318513)) (n := 12)
    (lo := (294178081 / 500000000)) (hi := (588356163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204800 / 113713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204800 / 113713) = 1/(113713 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_313 : (44372527 / 400000000) ≤ xi (91087 / 204800) ∧ xi (91087 / 204800) ≤ (110931319 / 1000000000) ∧
    (17482187 / 25000000) ≤ kap (91087 / 204800) ∧ kap (91087 / 204800) ≤ (1398574963 / 2000000000) := by
  have h := endpoint_bounds (v := ((91087 / 204800) : ℝ)) (by norm_num) (by norm_num)
    log_v_313.1 (by convert! log_c_313.1 using 1; norm_num)
    log_v_313.2 (by convert! log_c_313.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_314 : (202308719 / 250000000) ≤ -Real.log (27353 / 61440) ∧
    -Real.log (27353 / 61440) ≤ (404617439 / 500000000) := by
  have h := checkLog_sound (w := (3367 / 58073)) (n := 12)
    (lo := (7255481 / 62500000)) (hi := (116087697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30720 / 27353) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(30720 / 27353) = 1/(27353 / 61440) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_314 : (36821563 / 62500000) ≤ -Real.log (34087 / 61440) ∧
    -Real.log (34087 / 61440) ≤ (589145009 / 1000000000) := by
  have h := checkLog_sound (w := (27353 / 95527)) (n := 12)
    (lo := (36821563 / 62500000)) (hi := (589145009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61440 / 34087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61440 / 34087) = 1/(34087 / 61440) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_314 : (220089867 / 2000000000) ≤ xi (27353 / 61440) ∧ xi (27353 / 61440) ≤ (22008987 / 200000000) ∧
    (349594971 / 500000000) ≤ kap (27353 / 61440) ∧ kap (27353 / 61440) ≤ (1398379887 / 2000000000) := by
  have h := endpoint_bounds (v := ((27353 / 61440) : ℝ)) (by norm_num) (by norm_num)
    log_v_314.1 (by convert! log_c_314.1 using 1; norm_num)
    log_v_314.2 (by convert! log_c_314.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_315 : (10103149 / 12500000) ≤ -Real.log (273799 / 614400) ∧
    -Real.log (273799 / 614400) ≤ (404125961 / 500000000) := by
  have h := checkLog_sound (w := (33401 / 580999)) (n := 12)
    (lo := (5755237 / 50000000)) (hi := (115104741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 273799) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(307200 / 273799) = 1/(273799 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_315 : (589934477 / 1000000000) ≤ -Real.log (340601 / 614400) ∧
    -Real.log (340601 / 614400) ≤ (294967239 / 500000000) := by
  have h := checkLog_sound (w := (273799 / 955001)) (n := 12)
    (lo := (589934477 / 1000000000)) (hi := (294967239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 340601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 340601) = 1/(340601 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_315 : (109158721 / 1000000000) ≤ xi (273799 / 614400) ∧ xi (273799 / 614400) ≤ (43663489 / 400000000) ∧
    (1398186397 / 2000000000) ≤ kap (273799 / 614400) ∧ kap (273799 / 614400) ≤ (1747733 / 2500000) := by
  have h := endpoint_bounds (v := ((273799 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_315.1 (by convert! log_c_315.1 using 1; norm_num)
    log_v_315.2 (by convert! log_c_315.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_316 : (80726993 / 100000000) ≤ -Real.log (22839 / 51200) ∧
    -Real.log (22839 / 51200) ≤ (201817483 / 250000000) := by
  have h := checkLog_sound (w := (2761 / 48439)) (n := 12)
    (lo := (456491 / 4000000)) (hi := (114122751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25600 / 22839) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25600 / 22839) = 1/(22839 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_316 : (59072457 / 100000000) ≤ -Real.log (28361 / 51200) ∧
    -Real.log (28361 / 51200) ≤ (590724571 / 1000000000) := by
  have h := checkLog_sound (w := (22839 / 79561)) (n := 12)
    (lo := (59072457 / 100000000)) (hi := (590724571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51200 / 28361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51200 / 28361) = 1/(28361 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_316 : (216545359 / 2000000000) ≤ xi (22839 / 51200) ∧ xi (22839 / 51200) ≤ (108272681 / 1000000000) ∧
    (2795989 / 4000000) ≤ kap (22839 / 51200) ∧ kap (22839 / 51200) ≤ (1397994503 / 2000000000) := by
  have h := endpoint_bounds (v := ((22839 / 51200) : ℝ)) (by norm_num) (by norm_num)
    log_v_316.1 (by convert! log_c_316.1 using 1; norm_num)
    log_v_316.2 (by convert! log_c_316.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_317 : (806288903 / 1000000000) ≤ -Real.log (274337 / 614400) ∧
    -Real.log (274337 / 614400) ≤ (161257781 / 200000000) := by
  have h := checkLog_sound (w := (32863 / 581537)) (n := 12)
    (lo := (113141723 / 1000000000)) (hi := (28285431 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 274337) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(307200 / 274337) = 1/(274337 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_317 : (591515287 / 1000000000) ≤ -Real.log (340063 / 614400) ∧
    -Real.log (340063 / 614400) ≤ (73939411 / 125000000) := by
  have h := checkLog_sound (w := (274337 / 954463)) (n := 12)
    (lo := (591515287 / 1000000000)) (hi := (73939411 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 340063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 340063) = 1/(340063 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_317 : (42954723 / 400000000) ≤ xi (274337 / 614400) ∧ xi (274337 / 614400) ≤ (107386809 / 1000000000) ∧
    (139780419 / 200000000) ≤ kap (274337 / 614400) ∧ kap (274337 / 614400) ≤ (1397804193 / 2000000000) := by
  have h := endpoint_bounds (v := ((274337 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_317.1 (by convert! log_c_317.1 using 1; norm_num)
    log_v_317.2 (by convert! log_c_317.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_318 : (402654419 / 500000000) ≤ -Real.log (137303 / 307200) ∧
    -Real.log (137303 / 307200) ≤ (20132721 / 25000000) := by
  have h := checkLog_sound (w := (16297 / 290903)) (n := 12)
    (lo := (56080829 / 500000000)) (hi := (112161659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 137303) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(153600 / 137303) = 1/(137303 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_318 : (59230663 / 100000000) ≤ -Real.log (169897 / 307200) ∧
    -Real.log (169897 / 307200) ≤ (592306631 / 1000000000) := by
  have h := checkLog_sound (w := (137303 / 477097)) (n := 12)
    (lo := (59230663 / 100000000)) (hi := (592306631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 169897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 169897) = 1/(169897 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_318 : (213002207 / 2000000000) ≤ xi (137303 / 307200) ∧ xi (137303 / 307200) ≤ (21300221 / 200000000) ∧
    (349403867 / 500000000) ≤ kap (137303 / 307200) ∧ kap (137303 / 307200) ≤ (1397615471 / 2000000000) := by
  have h := endpoint_bounds (v := ((137303 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_318.1 (by convert! log_c_318.1 using 1; norm_num)
    log_v_318.2 (by convert! log_c_318.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_319 : (201082433 / 250000000) ≤ -Real.log (3665 / 8192) ∧
    -Real.log (3665 / 8192) ≤ (402164867 / 500000000) := by
  have h := checkLog_sound (w := (431 / 7761)) (n := 12)
    (lo := (13897819 / 125000000)) (hi := (111182553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4096 / 3665) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(4096 / 3665) = 1/(3665 / 8192) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_319 : (593098599 / 1000000000) ≤ -Real.log (4527 / 8192) ∧
    -Real.log (4527 / 8192) ≤ (2965493 / 5000000) := by
  have h := checkLog_sound (w := (3665 / 12719)) (n := 12)
    (lo := (593098599 / 1000000000)) (hi := (2965493 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8192 / 4527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8192 / 4527) = 1/(4527 / 8192) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_319 : (52807783 / 500000000) ≤ xi (3665 / 8192) ∧ xi (3665 / 8192) ≤ (42246227 / 400000000) ∧
    (1397428331 / 2000000000) ≤ kap (3665 / 8192) ∧ kap (3665 / 8192) ≤ (698714167 / 1000000000) := by
  have h := endpoint_bounds (v := ((3665 / 8192) : ℝ)) (by norm_num) (by norm_num)
    log_v_319.1 (by convert! log_c_319.1 using 1; norm_num)
    log_v_319.2 (by convert! log_c_319.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.EntropyCurvature


