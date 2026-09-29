-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs20
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLogs20
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:44:25.129237+00:00
-- url     : https://prove2.me/theorems/432beb48-5bb5-4437-910a-249babf5f284
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLogs20` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLogs20` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLogs20` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLogs20 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLogs20.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureBounds

namespace GeneralCK.Certificates.EntropyCurvature
open Mixed GeneralCK.EntropyCurvature

theorem log_v_320 : (25104737 / 31250000) ≤ -Real.log (34393 / 76800) ∧
    -Real.log (34393 / 76800) ≤ (401675793 / 500000000) := by
  have h := checkLog_sound (w := (4007 / 72793)) (n := 12)
    (lo := (27551101 / 250000000)) (hi := (22040881 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 34393) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(38400 / 34393) = 1/(34393 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_320 : (593891197 / 1000000000) ≤ -Real.log (42407 / 76800) ∧
    -Real.log (42407 / 76800) ≤ (296945599 / 500000000) := by
  have h := checkLog_sound (w := (34393 / 119207)) (n := 12)
    (lo := (593891197 / 1000000000)) (hi := (296945599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 42407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76800 / 42407) = 1/(42407 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_320 : (104730193 / 1000000000) ≤ xi (34393 / 76800) ∧ xi (34393 / 76800) ≤ (209460389 / 2000000000) ∧
    (1397242781 / 2000000000) ≤ kap (34393 / 76800) ∧ kap (34393 / 76800) ≤ (43663837 / 62500000) := by
  have h := endpoint_bounds (v := ((34393 / 76800) : ℝ)) (by norm_num) (by norm_num)
    log_v_320.1 (by convert! log_c_320.1 using 1; norm_num)
    log_v_320.2 (by convert! log_c_320.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_321 : (100296799 / 125000000) ≤ -Real.log (275413 / 614400) ∧
    -Real.log (275413 / 614400) ≤ (401187197 / 500000000) := by
  have h := checkLog_sound (w := (31787 / 582613)) (n := 12)
    (lo := (27306803 / 250000000)) (hi := (109227213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 275413) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(307200 / 275413) = 1/(275413 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_321 : (594684423 / 1000000000) ≤ -Real.log (338987 / 614400) ∧
    -Real.log (338987 / 614400) ≤ (74335553 / 125000000) := by
  have h := checkLog_sound (w := (275413 / 953387)) (n := 12)
    (lo := (594684423 / 1000000000)) (hi := (74335553 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 338987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 338987) = 1/(338987 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_321 : (12980623 / 125000000) ≤ xi (275413 / 614400) ∧ xi (275413 / 614400) ≤ (207689971 / 2000000000) ∧
    (279411763 / 400000000) ≤ kap (275413 / 614400) ∧ kap (275413 / 614400) ≤ (698529409 / 1000000000) := by
  have h := endpoint_bounds (v := ((275413 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_321.1 (by convert! log_c_321.1 using 1; norm_num)
    log_v_321.2 (by convert! log_c_321.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_322 : (801398153 / 1000000000) ≤ -Real.log (45947 / 102400) ∧
    -Real.log (45947 / 102400) ≤ (160279631 / 200000000) := by
  have h := checkLog_sound (w := (5253 / 97147)) (n := 12)
    (lo := (108250973 / 1000000000)) (hi := (54125487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51200 / 45947) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(51200 / 45947) = 1/(45947 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_322 : (595478279 / 1000000000) ≤ -Real.log (56453 / 102400) ∧
    -Real.log (56453 / 102400) ≤ (14886957 / 25000000) := by
  have h := checkLog_sound (w := (45947 / 158853)) (n := 12)
    (lo := (595478279 / 1000000000)) (hi := (14886957 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102400 / 56453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102400 / 56453) = 1/(56453 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_322 : (205919873 / 2000000000) ≤ xi (45947 / 102400) ∧ xi (45947 / 102400) ≤ (51479969 / 500000000) ∧
    (87304777 / 125000000) ≤ kap (45947 / 102400) ∧ kap (45947 / 102400) ≤ (279375287 / 400000000) := by
  have h := endpoint_bounds (v := ((45947 / 102400) : ℝ)) (by norm_num) (by norm_num)
    log_v_322.1 (by convert! log_c_322.1 using 1; norm_num)
    log_v_322.2 (by convert! log_c_322.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_323 : (800422867 / 1000000000) ≤ -Real.log (275951 / 614400) ∧
    -Real.log (275951 / 614400) ≤ (800422869 / 1000000000) := by
  have h := checkLog_sound (w := (31249 / 583151)) (n := 12)
    (lo := (107275687 / 1000000000)) (hi := (13409461 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 275951) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(307200 / 275951) = 1/(275951 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_323 : (119254553 / 200000000) ≤ -Real.log (338449 / 614400) ∧
    -Real.log (338449 / 614400) ≤ (298136383 / 500000000) := by
  have h := checkLog_sound (w := (275951 / 952849)) (n := 12)
    (lo := (119254553 / 200000000)) (hi := (298136383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 338449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 338449) = 1/(338449 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_323 : (204150101 / 2000000000) ≤ xi (275951 / 614400) ∧ xi (275951 / 614400) ≤ (25518763 / 250000000) ∧
    (87293477 / 125000000) ≤ kap (275951 / 614400) ∧ kap (275951 / 614400) ≤ (279339127 / 400000000) := by
  have h := endpoint_bounds (v := ((275951 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_323.1 (by convert! log_c_323.1 using 1; norm_num)
    log_v_323.2 (by convert! log_c_323.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_324 : (799448531 / 1000000000) ≤ -Real.log (13811 / 30720) ∧
    -Real.log (13811 / 30720) ≤ (799448533 / 1000000000) := by
  have h := checkLog_sound (w := (1549 / 29171)) (n := 12)
    (lo := (106301351 / 1000000000)) (hi := (13287669 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15360 / 13811) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15360 / 13811) = 1/(13811 / 30720) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_324 : (597067883 / 1000000000) ≤ -Real.log (16909 / 30720) ∧
    -Real.log (16909 / 30720) ≤ (149266971 / 250000000) := by
  have h := checkLog_sound (w := (13811 / 47629)) (n := 12)
    (lo := (597067883 / 1000000000)) (hi := (149266971 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30720 / 16909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30720 / 16909) = 1/(16909 / 30720) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_324 : (202380647 / 2000000000) ≤ xi (13811 / 30720) ∧ xi (13811 / 30720) ≤ (4047613 / 40000000) ∧
    (698258207 / 1000000000) ≤ kap (13811 / 30720) ∧ kap (13811 / 30720) ≤ (1396516417 / 2000000000) := by
  have h := endpoint_bounds (v := ((13811 / 30720) : ℝ)) (by norm_num) (by norm_num)
    log_v_324.1 (by convert! log_c_324.1 using 1; norm_num)
    log_v_324.2 (by convert! log_c_324.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_325 : (99809393 / 125000000) ≤ -Real.log (92163 / 204800) ∧
    -Real.log (92163 / 204800) ≤ (399237573 / 500000000) := by
  have h := checkLog_sound (w := (10237 / 194563)) (n := 12)
    (lo := (26331991 / 250000000)) (hi := (21065593 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102400 / 92163) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(102400 / 92163) = 1/(92163 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_325 : (298931817 / 500000000) ≤ -Real.log (112637 / 204800) ∧
    -Real.log (112637 / 204800) ≤ (119572727 / 200000000) := by
  have h := checkLog_sound (w := (92163 / 317437)) (n := 12)
    (lo := (298931817 / 500000000)) (hi := (119572727 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204800 / 112637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204800 / 112637) = 1/(112637 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_325 : (200611509 / 2000000000) ≤ xi (92163 / 204800) ∧ xi (92163 / 204800) ≤ (25076439 / 250000000) ∧
    (698169389 / 1000000000) ≤ kap (92163 / 204800) ∧ kap (92163 / 204800) ≤ (1396338781 / 2000000000) := by
  have h := endpoint_bounds (v := ((92163 / 204800) : ℝ)) (by norm_num) (by norm_num)
    log_v_325.1 (by convert! log_c_325.1 using 1; norm_num)
    log_v_325.2 (by convert! log_c_325.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_326 : (797502703 / 1000000000) ≤ -Real.log (138379 / 307200) ∧
    -Real.log (138379 / 307200) ≤ (159500541 / 200000000) := by
  have h := checkLog_sound (w := (15221 / 291979)) (n := 12)
    (lo := (104355523 / 1000000000)) (hi := (26088881 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 138379) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(153600 / 138379) = 1/(138379 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_326 : (598660019 / 1000000000) ≤ -Real.log (168821 / 307200) ∧
    -Real.log (168821 / 307200) ≤ (29933001 / 50000000) := by
  have h := checkLog_sound (w := (138379 / 476021)) (n := 12)
    (lo := (598660019 / 1000000000)) (hi := (29933001 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 168821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 168821) = 1/(168821 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_326 : (198842683 / 2000000000) ≤ xi (138379 / 307200) ∧ xi (138379 / 307200) ≤ (99421343 / 1000000000) ∧
    (698081361 / 1000000000) ≤ kap (138379 / 307200) ∧ kap (138379 / 307200) ≤ (55846509 / 80000000) := by
  have h := endpoint_bounds (v := ((138379 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_326.1 (by convert! log_c_326.1 using 1; norm_num)
    log_v_326.2 (by convert! log_c_326.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_327 : (398265603 / 500000000) ≤ -Real.log (277027 / 614400) ∧
    -Real.log (277027 / 614400) ≤ (99566401 / 125000000) := by
  have h := checkLog_sound (w := (30173 / 584227)) (n := 12)
    (lo := (51692013 / 500000000)) (hi := (103384027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 277027) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(307200 / 277027) = 1/(277027 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_327 : (299728519 / 500000000) ≤ -Real.log (337373 / 614400) ∧
    -Real.log (337373 / 614400) ≤ (599457039 / 1000000000) := by
  have h := checkLog_sound (w := (277027 / 951773)) (n := 12)
    (lo := (299728519 / 500000000)) (hi := (599457039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 337373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 337373) = 1/(337373 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_327 : (197074167 / 2000000000) ≤ xi (277027 / 614400) ∧ xi (277027 / 614400) ≤ (19707417 / 200000000) ∧
    (348997061 / 500000000) ≤ kap (277027 / 614400) ∧ kap (277027 / 614400) ≤ (1395988247 / 2000000000) := by
  have h := endpoint_bounds (v := ((277027 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_327.1 (by convert! log_c_327.1 using 1; norm_num)
    log_v_327.2 (by convert! log_c_327.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_328 : (795560653 / 1000000000) ≤ -Real.log (5777 / 12800) ∧
    -Real.log (5777 / 12800) ≤ (159112131 / 200000000) := by
  have h := checkLog_sound (w := (623 / 12177)) (n := 12)
    (lo := (102413473 / 1000000000)) (hi := (51206737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 5777) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(6400 / 5777) = 1/(5777 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_328 : (600254693 / 1000000000) ≤ -Real.log (7023 / 12800) ∧
    -Real.log (7023 / 12800) ≤ (300127347 / 500000000) := by
  have h := checkLog_sound (w := (5777 / 19823)) (n := 12)
    (lo := (600254693 / 1000000000)) (hi := (300127347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 7023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12800 / 7023) = 1/(7023 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_328 : (195305959 / 2000000000) ≤ xi (5777 / 12800) ∧ xi (5777 / 12800) ≤ (97652981 / 1000000000) ∧
    (697907673 / 1000000000) ≤ kap (5777 / 12800) ∧ kap (5777 / 12800) ≤ (1395815349 / 2000000000) := by
  have h := endpoint_bounds (v := ((5777 / 12800) : ℝ)) (by norm_num) (by norm_num)
    log_v_328.1 (by convert! log_c_328.1 using 1; norm_num)
    log_v_328.2 (by convert! log_c_328.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_329 : (794591041 / 1000000000) ≤ -Real.log (55513 / 122880) ∧
    -Real.log (55513 / 122880) ≤ (794591043 / 1000000000) := by
  have h := checkLog_sound (w := (5927 / 116953)) (n := 12)
    (lo := (101443861 / 1000000000)) (hi := (50721931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61440 / 55513) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(61440 / 55513) = 1/(55513 / 122880) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_329 : (120210597 / 200000000) ≤ -Real.log (67367 / 122880) ∧
    -Real.log (67367 / 122880) ≤ (300526493 / 500000000) := by
  have h := checkLog_sound (w := (55513 / 190247)) (n := 12)
    (lo := (120210597 / 200000000)) (hi := (300526493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122880 / 67367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122880 / 67367) = 1/(67367 / 122880) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_329 : (38707611 / 400000000) ≤ xi (55513 / 122880) ∧ xi (55513 / 122880) ≤ (96769029 / 1000000000) ∧
    (697822013 / 1000000000) ≤ kap (55513 / 122880) ∧ kap (55513 / 122880) ≤ (1395644029 / 2000000000) := by
  have h := endpoint_bounds (v := ((55513 / 122880) : ℝ)) (by norm_num) (by norm_num)
    log_v_329.1 (by convert! log_c_329.1 using 1; norm_num)
    log_v_329.2 (by convert! log_c_329.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_330 : (24800699 / 31250000) ≤ -Real.log (138917 / 307200) ∧
    -Real.log (138917 / 307200) ≤ (79362237 / 100000000) := by
  have h := checkLog_sound (w := (14683 / 292517)) (n := 12)
    (lo := (25118797 / 250000000)) (hi := (100475189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 138917) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(153600 / 138917) = 1/(138917 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_330 : (120370383 / 200000000) ≤ -Real.log (168283 / 307200) ∧
    -Real.log (168283 / 307200) ≤ (150462979 / 250000000) := by
  have h := checkLog_sound (w := (138917 / 475483)) (n := 12)
    (lo := (120370383 / 200000000)) (hi := (150462979 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 168283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 168283) = 1/(168283 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_330 : (47942613 / 500000000) ≤ xi (138917 / 307200) ∧ xi (138917 / 307200) ≤ (38354091 / 400000000) ∧
    (1395474283 / 2000000000) ≤ kap (138917 / 307200) ∧ kap (138917 / 307200) ≤ (697737143 / 1000000000) := by
  have h := endpoint_bounds (v := ((138917 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_330.1 (by convert! log_c_330.1 using 1; norm_num)
    log_v_330.2 (by convert! log_c_330.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_331 : (99081829 / 125000000) ≤ -Real.log (92701 / 204800) ∧
    -Real.log (92701 / 204800) ≤ (396327317 / 500000000) := by
  have h := checkLog_sound (w := (9699 / 195101)) (n := 12)
    (lo := (24876863 / 250000000)) (hi := (99507453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102400 / 92701) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(102400 / 92701) = 1/(92701 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_331 : (602651483 / 1000000000) ≤ -Real.log (112099 / 204800) ∧
    -Real.log (112099 / 204800) ≤ (150662871 / 250000000) := by
  have h := checkLog_sound (w := (92701 / 316899)) (n := 12)
    (lo := (602651483 / 1000000000)) (hi := (150662871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204800 / 112099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204800 / 112099) = 1/(112099 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_331 : (47500787 / 500000000) ≤ xi (92701 / 204800) ∧ xi (92701 / 204800) ≤ (190003151 / 2000000000) ∧
    (279061223 / 400000000) ≤ kap (92701 / 204800) ∧ kap (92701 / 204800) ≤ (697653059 / 1000000000) := by
  have h := endpoint_bounds (v := ((92701 / 204800) : ℝ)) (by norm_num) (by norm_num)
    log_v_331.1 (by convert! log_c_331.1 using 1; norm_num)
    log_v_331.2 (by convert! log_c_331.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_332 : (98960979 / 125000000) ≤ -Real.log (69593 / 153600) ∧
    -Real.log (69593 / 153600) ≤ (395843917 / 500000000) := by
  have h := checkLog_sound (w := (7207 / 146393)) (n := 12)
    (lo := (24635163 / 250000000)) (hi := (98540653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 69593) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(76800 / 69593) = 1/(69593 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_332 : (150862923 / 250000000) ≤ -Real.log (84007 / 153600) ∧
    -Real.log (84007 / 153600) ≤ (603451693 / 1000000000) := by
  have h := checkLog_sound (w := (69593 / 237607)) (n := 12)
    (lo := (150862923 / 250000000)) (hi := (603451693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 84007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153600 / 84007) = 1/(84007 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_332 : (188236139 / 2000000000) ≤ xi (69593 / 153600) ∧ xi (69593 / 153600) ≤ (94118071 / 1000000000) ∧
    (348784881 / 500000000) ≤ kap (69593 / 153600) ∧ kap (69593 / 153600) ≤ (1395139527 / 2000000000) := by
  have h := endpoint_bounds (v := ((69593 / 153600) : ℝ)) (by norm_num) (by norm_num)
    log_v_332.1 (by convert! log_c_332.1 using 1; norm_num)
    log_v_332.2 (by convert! log_c_332.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_333 : (395360983 / 500000000) ≤ -Real.log (278641 / 614400) ∧
    -Real.log (278641 / 614400) ≤ (49420123 / 62500000) := by
  have h := checkLog_sound (w := (28559 / 585841)) (n := 12)
    (lo := (48787393 / 500000000)) (hi := (97574787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 278641) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(307200 / 278641) = 1/(278641 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_333 : (604252541 / 1000000000) ≤ -Real.log (335759 / 614400) ∧
    -Real.log (335759 / 614400) ≤ (302126271 / 500000000) := by
  have h := checkLog_sound (w := (278641 / 950159)) (n := 12)
    (lo := (604252541 / 1000000000)) (hi := (302126271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 335759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 335759) = 1/(335759 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_333 : (11654339 / 125000000) ≤ xi (278641 / 614400) ∧ xi (278641 / 614400) ≤ (186469427 / 2000000000) ∧
    (1394974507 / 2000000000) ≤ kap (278641 / 614400) ∧ kap (278641 / 614400) ≤ (139497451 / 200000000) := by
  have h := endpoint_bounds (v := ((278641 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_333.1 (by convert! log_c_333.1 using 1; norm_num)
    log_v_333.2 (by convert! log_c_333.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_334 : (98719629 / 125000000) ≤ -Real.log (9297 / 20480) ∧
    -Real.log (9297 / 20480) ≤ (394878517 / 500000000) := by
  have h := checkLog_sound (w := (943 / 19537)) (n := 12)
    (lo := (24152463 / 250000000)) (hi := (96609853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 9297) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(10240 / 9297) = 1/(9297 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_334 : (37815877 / 62500000) ≤ -Real.log (11183 / 20480) ∧
    -Real.log (11183 / 20480) ≤ (605054033 / 1000000000) := by
  have h := checkLog_sound (w := (9297 / 31663)) (n := 12)
    (lo := (37815877 / 62500000)) (hi := (605054033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20480 / 11183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20480 / 11183) = 1/(11183 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_334 : (184702999 / 2000000000) ≤ xi (9297 / 20480) ∧ xi (9297 / 20480) ≤ (92351501 / 1000000000) ∧
    (174351383 / 250000000) ≤ kap (9297 / 20480) ∧ kap (9297 / 20480) ≤ (1394811067 / 2000000000) := by
  have h := endpoint_bounds (v := ((9297 / 20480) : ℝ)) (by norm_num) (by norm_num)
    log_v_334.1 (by convert! log_c_334.1 using 1; norm_num)
    log_v_334.2 (by convert! log_c_334.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_335 : (197198257 / 250000000) ≤ -Real.log (279179 / 614400) ∧
    -Real.log (279179 / 614400) ≤ (78879303 / 100000000) := by
  have h := checkLog_sound (w := (28021 / 586379)) (n := 12)
    (lo := (11955731 / 125000000)) (hi := (95645849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 279179) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(307200 / 279179) = 1/(279179 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_335 : (302928083 / 500000000) ≤ -Real.log (335221 / 614400) ∧
    -Real.log (335221 / 614400) ≤ (605856167 / 1000000000) := by
  have h := checkLog_sound (w := (279179 / 949621)) (n := 12)
    (lo := (302928083 / 500000000)) (hi := (605856167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 335221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 335221) = 1/(335221 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_335 : (182936861 / 2000000000) ≤ xi (279179 / 614400) ∧ xi (279179 / 614400) ≤ (5716777 / 62500000) ∧
    (697324597 / 1000000000) ≤ kap (279179 / 614400) ∧ kap (279179 / 614400) ≤ (1394649197 / 2000000000) := by
  have h := endpoint_bounds (v := ((279179 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_335.1 (by convert! log_c_335.1 using 1; norm_num)
    log_v_335.2 (by convert! log_c_335.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.EntropyCurvature


