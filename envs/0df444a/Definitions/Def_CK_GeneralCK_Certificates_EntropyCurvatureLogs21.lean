-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs21
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLogs21
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:45:22.109369+00:00
-- url     : https://prove2.me/theorems/4c484274-8664-44c1-8100-62ef0110b61b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLogs21` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLogs21` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLogs21` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLogs21 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLogs21.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureBounds

namespace GeneralCK.Certificates.EntropyCurvature
open Mixed GeneralCK.EntropyCurvature

theorem log_v_336 : (12309843 / 15625000) ≤ -Real.log (34931 / 76800) ∧
    -Real.log (34931 / 76800) ≤ (393914977 / 500000000) := by
  have h := checkLog_sound (w := (3469 / 73331)) (n := 12)
    (lo := (23670693 / 250000000)) (hi := (94682773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 34931) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(38400 / 34931) = 1/(34931 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_336 : (606658943 / 1000000000) ≤ -Real.log (41869 / 76800) ∧
    -Real.log (41869 / 76800) ≤ (4739523 / 7812500) := by
  have h := checkLog_sound (w := (34931 / 118669)) (n := 12)
    (lo := (606658943 / 1000000000)) (hi := (4739523 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 41869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76800 / 41869) = 1/(41869 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_336 : (2830797 / 31250000) ≤ xi (34931 / 76800) ∧ xi (34931 / 76800) ≤ (181171011 / 2000000000) ∧
    (278897779 / 400000000) ≤ kap (34931 / 76800) ∧ kap (34931 / 76800) ≤ (697244449 / 1000000000) := by
  have h := endpoint_bounds (v := ((34931 / 76800) : ℝ)) (by norm_num) (by norm_num)
    log_v_336.1 (by convert! log_c_336.1 using 1; norm_num)
    log_v_336.2 (by convert! log_c_336.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_337 : (786867803 / 1000000000) ≤ -Real.log (93239 / 204800) ∧
    -Real.log (93239 / 204800) ≤ (157373561 / 200000000) := by
  have h := checkLog_sound (w := (9161 / 195639)) (n := 12)
    (lo := (93720623 / 1000000000)) (hi := (5857539 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102400 / 93239) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(102400 / 93239) = 1/(93239 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_337 : (303731183 / 500000000) ≤ -Real.log (111561 / 204800) ∧
    -Real.log (111561 / 204800) ≤ (607462367 / 1000000000) := by
  have h := checkLog_sound (w := (93239 / 316361)) (n := 12)
    (lo := (303731183 / 500000000)) (hi := (607462367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204800 / 111561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204800 / 111561) = 1/(111561 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_337 : (44851359 / 500000000) ≤ xi (93239 / 204800) ∧ xi (93239 / 204800) ≤ (179405439 / 2000000000) ∧
    (1394330169 / 2000000000) ≤ kap (93239 / 204800) ∧ kap (93239 / 204800) ≤ (348582543 / 500000000) := by
  have h := endpoint_bounds (v := ((93239 / 204800) : ℝ)) (by norm_num) (by norm_num)
    log_v_337.1 (by convert! log_c_337.1 using 1; norm_num)
    log_v_337.2 (by convert! log_c_337.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_338 : (785906579 / 1000000000) ≤ -Real.log (139993 / 307200) ∧
    -Real.log (139993 / 307200) ≤ (785906581 / 1000000000) := by
  have h := checkLog_sound (w := (13607 / 293593)) (n := 12)
    (lo := (92759399 / 1000000000)) (hi := (463797 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 139993) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(153600 / 139993) = 1/(139993 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_338 : (121653287 / 200000000) ≤ -Real.log (167207 / 307200) ∧
    -Real.log (167207 / 307200) ≤ (152066609 / 250000000) := by
  have h := checkLog_sound (w := (139993 / 474407)) (n := 12)
    (lo := (121653287 / 200000000)) (hi := (152066609 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 167207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 167207) = 1/(167207 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_338 : (177640143 / 2000000000) ≤ xi (139993 / 307200) ∧ xi (139993 / 307200) ≤ (88820073 / 1000000000) ∧
    (697086507 / 1000000000) ≤ kap (139993 / 307200) ∧ kap (139993 / 307200) ≤ (1394173017 / 2000000000) := by
  have h := endpoint_bounds (v := ((139993 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_338.1 (by convert! log_c_338.1 using 1; norm_num)
    log_v_338.2 (by convert! log_c_338.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_339 : (785426313 / 1000000000) ≤ -Real.log (186747 / 409600) ∧
    -Real.log (186747 / 409600) ≤ (157085263 / 200000000) := by
  have h := checkLog_sound (w := (18053 / 391547)) (n := 12)
    (lo := (92279133 / 1000000000)) (hi := (46139567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204800 / 186747) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(204800 / 186747) = 1/(186747 / 409600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_339 : (76083589 / 125000000) ≤ -Real.log (222853 / 409600) ∧
    -Real.log (222853 / 409600) ≤ (608668713 / 1000000000) := by
  have h := checkLog_sound (w := (186747 / 632453)) (n := 12)
    (lo := (76083589 / 125000000)) (hi := (608668713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((409600 / 222853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(409600 / 222853) = 1/(222853 / 409600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_339 : (220947 / 2500000) ≤ xi (186747 / 409600) ∧ xi (186747 / 409600) ≤ (176757603 / 2000000000) ∧
    (55763801 / 80000000) ≤ kap (186747 / 409600) ∧ kap (186747 / 409600) ≤ (348523757 / 500000000) := by
  have h := endpoint_bounds (v := ((186747 / 409600) : ℝ)) (by norm_num) (by norm_num)
    log_v_339.1 (by convert! log_c_339.1 using 1; norm_num)
    log_v_339.2 (by convert! log_c_339.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_340 : (392473139 / 500000000) ≤ -Real.log (56051 / 122880) ∧
    -Real.log (56051 / 122880) ≤ (19623657 / 25000000) := by
  have h := checkLog_sound (w := (5389 / 117491)) (n := 12)
    (lo := (45899549 / 500000000)) (hi := (91799099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61440 / 56051) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(61440 / 56051) = 1/(56051 / 122880) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_340 : (609071151 / 1000000000) ≤ -Real.log (66829 / 122880) ∧
    -Real.log (66829 / 122880) ≤ (38066947 / 62500000) := by
  have h := checkLog_sound (w := (56051 / 189709)) (n := 12)
    (lo := (609071151 / 1000000000)) (hi := (38066947 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122880 / 66829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122880 / 66829) = 1/(66829 / 122880) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_340 : (87937563 / 1000000000) ≤ xi (56051 / 122880) ∧ xi (56051 / 122880) ≤ (175875129 / 2000000000) ∧
    (1394017429 / 2000000000) ≤ kap (56051 / 122880) ∧ kap (56051 / 122880) ≤ (174252179 / 250000000) := by
  have h := endpoint_bounds (v := ((56051 / 122880) : ℝ)) (by norm_num) (by norm_num)
    log_v_340.1 (by convert! log_c_340.1 using 1; norm_num)
    log_v_340.2 (by convert! log_c_340.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_341 : (784466473 / 1000000000) ≤ -Real.log (560779 / 1228800) ∧
    -Real.log (560779 / 1228800) ≤ (31378659 / 40000000) := by
  have h := checkLog_sound (w := (53621 / 1175179)) (n := 12)
    (lo := (91319293 / 1000000000)) (hi := (45659647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 560779) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(614400 / 560779) = 1/(560779 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_341 : (76184219 / 125000000) ≤ -Real.log (668021 / 1228800) ∧
    -Real.log (668021 / 1228800) ≤ (609473753 / 1000000000) := by
  have h := checkLog_sound (w := (560779 / 1896821)) (n := 12)
    (lo := (76184219 / 125000000)) (hi := (609473753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 668021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 668021) = 1/(668021 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_341 : (2187409 / 25000000) ≤ xi (560779 / 1228800) ∧ xi (560779 / 1228800) ≤ (174992723 / 2000000000) ∧
    (55757609 / 80000000) ≤ kap (560779 / 1228800) ∧ kap (560779 / 1228800) ≤ (348485057 / 500000000) := by
  have h := endpoint_bounds (v := ((560779 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_341.1 (by convert! log_c_341.1 using 1; norm_num)
    log_v_341.2 (by convert! log_c_341.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_342 : (391993449 / 500000000) ≤ -Real.log (23377 / 51200) ∧
    -Real.log (23377 / 51200) ≤ (7839869 / 10000000) := by
  have h := checkLog_sound (w := (2223 / 48977)) (n := 12)
    (lo := (45419859 / 500000000)) (hi := (90839719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25600 / 23377) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25600 / 23377) = 1/(23377 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_342 : (121975303 / 200000000) ≤ -Real.log (27823 / 51200) ∧
    -Real.log (27823 / 51200) ≤ (152469129 / 250000000) := by
  have h := checkLog_sound (w := (23377 / 79023)) (n := 12)
    (lo := (121975303 / 200000000)) (hi := (152469129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51200 / 27823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51200 / 27823) = 1/(27823 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_342 : (87055191 / 1000000000) ≤ xi (23377 / 51200) ∧ xi (23377 / 51200) ≤ (34822077 / 400000000) ∧
    (1393863413 / 2000000000) ≤ kap (23377 / 51200) ∧ kap (23377 / 51200) ≤ (174232927 / 250000000) := by
  have h := endpoint_bounds (v := ((23377 / 51200) : ℝ)) (by norm_num) (by norm_num)
    log_v_342.1 (by convert! log_c_342.1 using 1; norm_num)
    log_v_342.2 (by convert! log_c_342.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_343 : (783507553 / 1000000000) ≤ -Real.log (561317 / 1228800) ∧
    -Real.log (561317 / 1228800) ≤ (156701511 / 200000000) := by
  have h := checkLog_sound (w := (53083 / 1175717)) (n := 12)
    (lo := (90360373 / 1000000000)) (hi := (45180187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 561317) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(614400 / 561317) = 1/(561317 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_343 : (7628493 / 12500000) ≤ -Real.log (667483 / 1228800) ∧
    -Real.log (667483 / 1228800) ≤ (610279441 / 1000000000) := by
  have h := checkLog_sound (w := (561317 / 1896283)) (n := 12)
    (lo := (7628493 / 12500000)) (hi := (610279441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 667483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 667483) = 1/(667483 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_343 : (10826757 / 125000000) ≤ xi (561317 / 1228800) ∧ xi (561317 / 1228800) ≤ (34645623 / 400000000) ∧
    (1393786993 / 2000000000) ≤ kap (561317 / 1228800) ∧ kap (561317 / 1228800) ≤ (348446749 / 500000000) := by
  have h := endpoint_bounds (v := ((561317 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_343.1 (by convert! log_c_343.1 using 1; norm_num)
    log_v_343.2 (by convert! log_c_343.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_344 : (391514219 / 500000000) ≤ -Real.log (280793 / 614400) ∧
    -Real.log (280793 / 614400) ≤ (19575711 / 25000000) := by
  have h := checkLog_sound (w := (26407 / 587993)) (n := 12)
    (lo := (44940629 / 500000000)) (hi := (89881259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 280793) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(307200 / 280793) = 1/(280793 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_344 : (19083829 / 31250000) ≤ -Real.log (333607 / 614400) ∧
    -Real.log (333607 / 614400) ≤ (610682529 / 1000000000) := by
  have h := checkLog_sound (w := (280793 / 948007)) (n := 12)
    (lo := (19083829 / 31250000)) (hi := (610682529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 333607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 333607) = 1/(333607 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_344 : (172345909 / 2000000000) ≤ xi (280793 / 614400) ∧ xi (280793 / 614400) ≤ (21543239 / 250000000) ∧
    (696855483 / 1000000000) ≤ kap (280793 / 614400) ∧ kap (280793 / 614400) ≤ (1393710969 / 2000000000) := by
  have h := endpoint_bounds (v := ((280793 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_344.1 (by convert! log_c_344.1 using 1; norm_num)
    log_v_344.2 (by convert! log_c_344.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_345 : (48909347 / 62500000) ≤ -Real.log (37457 / 81920) ∧
    -Real.log (37457 / 81920) ≤ (391274777 / 500000000) := by
  have h := checkLog_sound (w := (3503 / 78417)) (n := 12)
    (lo := (22350593 / 250000000)) (hi := (89402373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40960 / 37457) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40960 / 37457) = 1/(37457 / 81920) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_345 : (305542889 / 500000000) ≤ -Real.log (44463 / 81920) ∧
    -Real.log (44463 / 81920) ≤ (611085779 / 1000000000) := by
  have h := checkLog_sound (w := (37457 / 126383)) (n := 12)
    (lo := (305542889 / 500000000)) (hi := (611085779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81920 / 44463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81920 / 44463) = 1/(44463 / 81920) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_345 : (171463773 / 2000000000) ≤ xi (37457 / 81920) ∧ xi (37457 / 81920) ≤ (5358243 / 62500000) ∧
    (139363533 / 200000000) ≤ kap (37457 / 81920) ∧ kap (37457 / 81920) ≤ (1393635333 / 2000000000) := by
  have h := endpoint_bounds (v := ((37457 / 81920) : ℝ)) (by norm_num) (by norm_num)
    log_v_345.1 (by convert! log_c_345.1 using 1; norm_num)
    log_v_345.2 (by convert! log_c_345.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_346 : (156414179 / 200000000) ≤ -Real.log (140531 / 307200) ∧
    -Real.log (140531 / 307200) ≤ (782070897 / 1000000000) := by
  have h := checkLog_sound (w := (13069 / 294131)) (n := 12)
    (lo := (17784743 / 200000000)) (hi := (22230929 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 140531) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(153600 / 140531) = 1/(140531 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_346 : (611489191 / 1000000000) ≤ -Real.log (166669 / 307200) ∧
    -Real.log (166669 / 307200) ≤ (76436149 / 125000000) := by
  have h := checkLog_sound (w := (140531 / 473869)) (n := 12)
    (lo := (611489191 / 1000000000)) (hi := (76436149 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 166669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 166669) = 1/(166669 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_346 : (170581703 / 2000000000) ≤ xi (140531 / 307200) ∧ xi (140531 / 307200) ≤ (85290853 / 1000000000) ∧
    (696780043 / 1000000000) ≤ kap (140531 / 307200) ∧ kap (140531 / 307200) ≤ (1393560089 / 2000000000) := by
  have h := endpoint_bounds (v := ((140531 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_346.1 (by convert! log_c_346.1 using 1; norm_num)
    log_v_346.2 (by convert! log_c_346.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_347 : (195398117 / 250000000) ≤ -Real.log (562393 / 1228800) ∧
    -Real.log (562393 / 1228800) ≤ (78159247 / 100000000) := by
  have h := checkLog_sound (w := (52007 / 1176793)) (n := 12)
    (lo := (11055661 / 125000000)) (hi := (88445289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 562393) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(614400 / 562393) = 1/(562393 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_347 : (611892767 / 1000000000) ≤ -Real.log (666407 / 1228800) ∧
    -Real.log (666407 / 1228800) ≤ (19121649 / 31250000) := by
  have h := checkLog_sound (w := (562393 / 1895207)) (n := 12)
    (lo := (611892767 / 1000000000)) (hi := (19121649 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 666407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 666407) = 1/(666407 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_347 : (1696997 / 20000000) ≤ xi (562393 / 1228800) ∧ xi (562393 / 1228800) ≤ (169699703 / 2000000000) ∧
    (278697047 / 400000000) ≤ kap (562393 / 1228800) ∧ kap (562393 / 1228800) ≤ (696742619 / 1000000000) := by
  have h := endpoint_bounds (v := ((562393 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_347.1 (by convert! log_c_347.1 using 1; norm_num)
    log_v_347.2 (by convert! log_c_347.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_348 : (781114269 / 1000000000) ≤ -Real.log (93777 / 204800) ∧
    -Real.log (93777 / 204800) ≤ (781114271 / 1000000000) := by
  have h := checkLog_sound (w := (8623 / 196177)) (n := 12)
    (lo := (87967089 / 1000000000)) (hi := (8796709 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102400 / 93777) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(102400 / 93777) = 1/(93777 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_348 : (306148253 / 500000000) ≤ -Real.log (111023 / 204800) ∧
    -Real.log (111023 / 204800) ≤ (612296507 / 1000000000) := by
  have h := checkLog_sound (w := (93777 / 315823)) (n := 12)
    (lo := (306148253 / 500000000)) (hi := (612296507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204800 / 111023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204800 / 111023) = 1/(111023 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_348 : (84408881 / 1000000000) ≤ xi (93777 / 204800) ∧ xi (93777 / 204800) ≤ (33763553 / 400000000) ∧
    (55736431 / 80000000) ≤ kap (93777 / 204800) ∧ kap (93777 / 204800) ≤ (696705389 / 1000000000) := by
  have h := endpoint_bounds (v := ((93777 / 204800) : ℝ)) (by norm_num) (by norm_num)
    log_v_348.1 (by convert! log_c_348.1 using 1; norm_num)
    log_v_348.2 (by convert! log_c_348.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_349 : (390318149 / 500000000) ≤ -Real.log (562931 / 1228800) ∧
    -Real.log (562931 / 1228800) ≤ (7806363 / 10000000) := by
  have h := checkLog_sound (w := (51469 / 1177331)) (n := 12)
    (lo := (43744559 / 500000000)) (hi := (87489119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 562931) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(614400 / 562931) = 1/(562931 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_349 : (612700407 / 1000000000) ≤ -Real.log (665869 / 1228800) ∧
    -Real.log (665869 / 1228800) ≤ (76587551 / 125000000) := by
  have h := checkLog_sound (w := (562931 / 1894669)) (n := 12)
    (lo := (612700407 / 1000000000)) (hi := (76587551 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 665869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 665869) = 1/(665869 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_349 : (16793589 / 200000000) ≤ xi (562931 / 1228800) ∧ xi (562931 / 1228800) ≤ (167935893 / 2000000000) ∧
    (278667341 / 400000000) ≤ kap (562931 / 1228800) ∧ kap (562931 / 1228800) ≤ (348334177 / 500000000) := by
  have h := endpoint_bounds (v := ((562931 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_349.1 (by convert! log_c_349.1 using 1; norm_num)
    log_v_349.2 (by convert! log_c_349.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_350 : (195039639 / 250000000) ≤ -Real.log (11 / 24) ∧
    -Real.log (11 / 24) ≤ (390079279 / 500000000) := by
  have h := checkLog_sound (w := (1 / 23)) (n := 12)
    (lo := (5438211 / 62500000)) (hi := (87011377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12 / 11) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(12 / 11) = 1/(11 / 24) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_350 : (76638059 / 125000000) ≤ -Real.log (13 / 24) ∧
    -Real.log (13 / 24) ≤ (613104473 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 37)) (n := 12)
    (lo := (76638059 / 125000000)) (hi := (613104473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24 / 13) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24 / 13) = 1/(13 / 24) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_350 : (167054083 / 2000000000) ≤ xi (11 / 24) ∧ xi (11 / 24) ≤ (83527043 / 1000000000) ∧
    (348315757 / 500000000) ≤ kap (11 / 24) ∧ kap (11 / 24) ≤ (1393263031 / 2000000000) := by
  have h := endpoint_bounds (v := ((11 / 24) : ℝ)) (by norm_num) (by norm_num)
    log_v_350.1 (by convert! log_c_350.1 using 1; norm_num)
    log_v_350.2 (by convert! log_c_350.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.EntropyCurvature


