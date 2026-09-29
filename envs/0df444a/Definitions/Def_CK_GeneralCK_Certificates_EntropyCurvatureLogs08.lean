-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs08
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLogs08
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:43:22.828784+00:00
-- url     : https://prove2.me/theorems/16282254-f5b1-4afe-91b9-50ed4fa8a197
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLogs08` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLogs08` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLogs08` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLogs08 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLogs08.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureBounds

namespace GeneralCK.Certificates.EntropyCurvature
open Mixed GeneralCK.EntropyCurvature

theorem log_v_128 : (723451099 / 200000000) ≤ -Real.log (33001 / 1228800) ∧
    -Real.log (33001 / 1228800) ≤ (3617255501 / 1000000000) := by
  have h := checkLog_sound (w := (5399 / 71401)) (n := 12)
    (lo := (30303919 / 200000000)) (hi := (37879899 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 33001) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(38400 / 33001) = 1/(33001 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_128 : (13611751 / 500000000) ≤ -Real.log (1195799 / 1228800) ∧
    -Real.log (1195799 / 1228800) ≤ (27223503 / 1000000000) := by
  have h := checkLog_sound (w := (33001 / 2424599)) (n := 12)
    (lo := (13611751 / 500000000)) (hi := (27223503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 1195799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 1195799) = 1/(1195799 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_128 : (448753999 / 250000000) ≤ xi (33001 / 1228800) ∧ xi (33001 / 1228800) ≤ (3590031999 / 2000000000) ∧
    (3644478997 / 2000000000) ≤ kap (33001 / 1228800) ∧ kap (33001 / 1228800) ≤ (911119751 / 500000000) := by
  have h := endpoint_bounds (v := ((33001 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_128.1 (by convert! log_c_128.1 using 1; norm_num)
    log_v_128.2 (by convert! log_c_128.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_129 : (3609137269 / 1000000000) ≤ -Real.log (1109 / 40960) ∧
    -Real.log (1109 / 40960) ≤ (144365491 / 40000000) := by
  have h := checkLog_sound (w := (171 / 2389)) (n := 12)
    (lo := (143401369 / 1000000000)) (hi := (14340137 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1109) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1280 / 1109) = 1/(1109 / 40960) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_129 : (27448481 / 1000000000) ≤ -Real.log (39851 / 40960) ∧
    -Real.log (39851 / 40960) ≤ (13724241 / 500000000) := by
  have h := checkLog_sound (w := (1109 / 80811)) (n := 12)
    (lo := (27448481 / 1000000000)) (hi := (13724241 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40960 / 39851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40960 / 39851) = 1/(39851 / 40960) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_129 : (3581688787 / 2000000000) ≤ xi (1109 / 40960) ∧ xi (1109 / 40960) ≤ (1790844397 / 1000000000) ∧
    (14546343 / 8000000) ≤ kap (1109 / 40960) ∧ kap (1109 / 40960) ≤ (3636585757 / 2000000000) := by
  have h := endpoint_bounds (v := ((1109 / 40960) : ℝ)) (by norm_num) (by norm_num)
    log_v_129.1 (by convert! log_c_129.1 using 1; norm_num)
    log_v_129.2 (by convert! log_c_129.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_130 : (1800542209 / 500000000) ≤ -Real.log (33539 / 1228800) ∧
    -Real.log (33539 / 1228800) ≤ (450135553 / 125000000) := by
  have h := checkLog_sound (w := (4861 / 71939)) (n := 12)
    (lo := (67674259 / 500000000)) (hi := (135348519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 33539) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(38400 / 33539) = 1/(33539 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_130 : (27673511 / 1000000000) ≤ -Real.log (1195261 / 1228800) ∧
    -Real.log (1195261 / 1228800) ≤ (3459189 / 125000000) := by
  have h := checkLog_sound (w := (33539 / 2424061)) (n := 12)
    (lo := (27673511 / 1000000000)) (hi := (3459189 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228800 / 1195261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228800 / 1195261) = 1/(1195261 / 1228800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_130 : (1786705453 / 1000000000) ≤ xi (33539 / 1228800) ∧ xi (33539 / 1228800) ≤ (3573410913 / 2000000000) ∧
    (3628757929 / 2000000000) ≤ kap (33539 / 1228800) ∧ kap (33539 / 1228800) ≤ (226797371 / 125000000) := by
  have h := endpoint_bounds (v := ((33539 / 1228800) : ℝ)) (by norm_num) (by norm_num)
    log_v_130.1 (by convert! log_c_130.1 using 1; norm_num)
    log_v_130.2 (by convert! log_c_130.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_131 : (1796547949 / 500000000) ≤ -Real.log (2113 / 76800) ∧
    -Real.log (2113 / 76800) ≤ (112284247 / 31250000) := by
  have h := checkLog_sound (w := (287 / 4513)) (n := 12)
    (lo := (63679999 / 500000000)) (hi := (127359999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2400 / 2113) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2400 / 2113) = 1/(2113 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_131 : (871831 / 31250000) ≤ -Real.log (74687 / 76800) ∧
    -Real.log (74687 / 76800) ≤ (27898593 / 1000000000) := by
  have h := checkLog_sound (w := (2113 / 151487)) (n := 12)
    (lo := (871831 / 31250000)) (hi := (27898593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 74687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76800 / 74687) = 1/(74687 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_131 : (713039461 / 400000000) ≤ xi (2113 / 76800) ∧ xi (2113 / 76800) ≤ (3481638 / 1953125) ∧
    (362099449 / 200000000) ≤ kap (2113 / 76800) ∧ kap (2113 / 76800) ≤ (3620994497 / 2000000000) := by
  have h := endpoint_bounds (v := ((2113 / 76800) : ℝ)) (by norm_num) (by norm_num)
    log_v_131.1 (by convert! log_c_131.1 using 1; norm_num)
    log_v_131.2 (by convert! log_c_131.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_132 : (3585170689 / 1000000000) ≤ -Real.log (11359 / 409600) ∧
    -Real.log (11359 / 409600) ≤ (717034139 / 200000000) := by
  have h := checkLog_sound (w := (1441 / 24159)) (n := 12)
    (lo := (119434789 / 1000000000)) (hi := (11943479 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 11359) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(12800 / 11359) = 1/(11359 / 409600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_132 : (7030931 / 250000000) ≤ -Real.log (398241 / 409600) ∧
    -Real.log (398241 / 409600) ≤ (1124949 / 40000000) := by
  have h := checkLog_sound (w := (11359 / 807841)) (n := 12)
    (lo := (7030931 / 250000000)) (hi := (1124949 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((409600 / 398241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(409600 / 398241) = 1/(398241 / 409600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_132 : (889261741 / 500000000) ≤ xi (11359 / 409600) ∧ xi (11359 / 409600) ≤ (3557046971 / 2000000000) ∧
    (3613294413 / 2000000000) ≤ kap (11359 / 409600) ∧ kap (11359 / 409600) ≤ (180664721 / 100000000) := by
  have h := endpoint_bounds (v := ((11359 / 409600) : ℝ)) (by norm_num) (by norm_num)
    log_v_132.1 (by convert! log_c_132.1 using 1; norm_num)
    log_v_132.2 (by convert! log_c_132.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_133 : (894326949 / 250000000) ≤ -Real.log (17173 / 614400) ∧
    -Real.log (17173 / 614400) ≤ (1788653901 / 500000000) := by
  have h := checkLog_sound (w := (2027 / 36373)) (n := 12)
    (lo := (13946487 / 125000000)) (hi := (111571897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 17173) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19200 / 17173) = 1/(17173 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_133 : (14174453 / 500000000) ≤ -Real.log (597227 / 614400) ∧
    -Real.log (597227 / 614400) ≤ (28348907 / 1000000000) := by
  have h := checkLog_sound (w := (17173 / 1211627)) (n := 12)
    (lo := (14174453 / 500000000)) (hi := (28348907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 597227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 597227) = 1/(597227 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_133 : (3548958889 / 2000000000) ≤ xi (17173 / 614400) ∧ xi (17173 / 614400) ≤ (221809931 / 125000000) ∧
    (1802828351 / 1000000000) ≤ kap (17173 / 614400) ∧ kap (17173 / 614400) ≤ (3605656709 / 2000000000) := by
  have h := endpoint_bounds (v := ((17173 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_133.1 (by convert! log_c_133.1 using 1; norm_num)
    log_v_133.2 (by convert! log_c_133.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_134 : (111305159 / 31250000) ≤ -Real.log (2907 / 102400) ∧
    -Real.log (2907 / 102400) ≤ (1780882547 / 500000000) := by
  have h := checkLog_sound (w := (293 / 6107)) (n := 12)
    (lo := (24007297 / 250000000)) (hi := (96029189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2907) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2907) = 1/(2907 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_134 : (14399711 / 500000000) ≤ -Real.log (99493 / 102400) ∧
    -Real.log (99493 / 102400) ≤ (28799423 / 1000000000) := by
  have h := checkLog_sound (w := (2907 / 201893)) (n := 12)
    (lo := (14399711 / 500000000)) (hi := (28799423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102400 / 99493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102400 / 99493) = 1/(99493 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_134 : (706593133 / 400000000) ≤ xi (2907 / 102400) ∧ xi (2907 / 102400) ≤ (441620709 / 250000000) ∧
    (359056451 / 200000000) ≤ kap (2907 / 102400) ∧ kap (2907 / 102400) ≤ (3590564517 / 2000000000) := by
  have h := endpoint_bounds (v := ((2907 / 102400) : ℝ)) (by norm_num) (by norm_num)
    log_v_134.1 (by convert! log_c_134.1 using 1; norm_num)
    log_v_134.2 (by convert! log_c_134.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_135 : (3546460263 / 1000000000) ≤ -Real.log (17711 / 614400) ∧
    -Real.log (17711 / 614400) ≤ (3546460269 / 1000000000) := by
  have h := checkLog_sound (w := (1489 / 36911)) (n := 12)
    (lo := (80724363 / 1000000000)) (hi := (20181091 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 17711) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19200 / 17711) = 1/(17711 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_135 : (14625071 / 500000000) ≤ -Real.log (596689 / 614400) ∧
    -Real.log (596689 / 614400) ≤ (29250143 / 1000000000) := by
  have h := checkLog_sound (w := (17711 / 1211089)) (n := 12)
    (lo := (14625071 / 500000000)) (hi := (29250143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 596689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 596689) = 1/(596689 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_135 : (87930253 / 50000000) ≤ xi (17711 / 614400) ∧ xi (17711 / 614400) ≤ (3517210127 / 2000000000) ∧
    (715142081 / 400000000) ≤ kap (17711 / 614400) ∧ kap (17711 / 614400) ≤ (893927603 / 500000000) := by
  have h := endpoint_bounds (v := ((17711 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_135.1 (by convert! log_c_135.1 using 1; norm_num)
    log_v_135.2 (by convert! log_c_135.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_136 : (3531386149 / 1000000000) ≤ -Real.log (899 / 30720) ∧
    -Real.log (899 / 30720) ≤ (706277231 / 200000000) := by
  have h := checkLog_sound (w := (61 / 1859)) (n := 12)
    (lo := (65650249 / 1000000000)) (hi := (262601 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((960 / 899) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(960 / 899) = 1/(899 / 30720) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_136 : (3712633 / 125000000) ≤ -Real.log (29821 / 30720) ∧
    -Real.log (29821 / 30720) ≤ (5940213 / 200000000) := by
  have h := checkLog_sound (w := (899 / 60541)) (n := 12)
    (lo := (3712633 / 125000000)) (hi := (5940213 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30720 / 29821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30720 / 29821) = 1/(29821 / 30720) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_136 : (875421271 / 500000000) ≤ xi (899 / 30720) ∧ xi (899 / 30720) ≤ (3501685091 / 2000000000) ∧
    (3561087213 / 2000000000) ≤ kap (899 / 30720) ∧ kap (899 / 30720) ≤ (178054361 / 100000000) := by
  have h := endpoint_bounds (v := ((899 / 30720) : ℝ)) (by norm_num) (by norm_num)
    log_v_136.1 (by convert! log_c_136.1 using 1; norm_num)
    log_v_136.2 (by convert! log_c_136.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_137 : (703307179 / 200000000) ≤ -Real.log (6083 / 204800) ∧
    -Real.log (6083 / 204800) ≤ (3516535901 / 1000000000) := by
  have h := checkLog_sound (w := (317 / 12483)) (n := 12)
    (lo := (10159999 / 200000000)) (hi := (12699999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 6083) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6400 / 6083) = 1/(6083 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_137 : (30152191 / 1000000000) ≤ -Real.log (198717 / 204800) ∧
    -Real.log (198717 / 204800) ≤ (58891 / 1953125) := by
  have h := checkLog_sound (w := (6083 / 403517)) (n := 12)
    (lo := (30152191 / 1000000000)) (hi := (58891 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204800 / 198717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204800 / 198717) = 1/(198717 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_137 : (3486383703 / 2000000000) ≤ xi (6083 / 204800) ∧ xi (6083 / 204800) ≤ (348638371 / 200000000) ∧
    (1773344043 / 1000000000) ≤ kap (6083 / 204800) ∧ kap (6083 / 204800) ≤ (3546688093 / 2000000000) := by
  have h := endpoint_bounds (v := ((6083 / 204800) : ℝ)) (by norm_num) (by norm_num)
    log_v_137.1 (by convert! log_c_137.1 using 1; norm_num)
    log_v_137.2 (by convert! log_c_137.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_138 : (3501902947 / 1000000000) ≤ -Real.log (9259 / 307200) ∧
    -Real.log (9259 / 307200) ≤ (3501902953 / 1000000000) := by
  have h := checkLog_sound (w := (341 / 18859)) (n := 12)
    (lo := (36167047 / 1000000000)) (hi := (4520881 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 9259) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(9600 / 9259) = 1/(9259 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_138 : (23909 / 781250) ≤ -Real.log (297941 / 307200) ∧
    -Real.log (297941 / 307200) ≤ (30603521 / 1000000000) := by
  have h := checkLog_sound (w := (9259 / 605141)) (n := 12)
    (lo := (23909 / 781250)) (hi := (30603521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 297941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 297941) = 1/(297941 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_138 : (1735649713 / 1000000000) ≤ xi (9259 / 307200) ∧ xi (9259 / 307200) ≤ (3471299433 / 2000000000) ∧
    (3532506467 / 2000000000) ≤ kap (9259 / 307200) ∧ kap (9259 / 307200) ≤ (1766253237 / 1000000000) := by
  have h := endpoint_bounds (v := ((9259 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_138.1 (by convert! log_c_138.1 using 1; norm_num)
    log_v_138.2 (by convert! log_c_138.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_139 : (3487481037 / 1000000000) ≤ -Real.log (18787 / 614400) ∧
    -Real.log (18787 / 614400) ≤ (3487481043 / 1000000000) := by
  have h := checkLog_sound (w := (413 / 37987)) (n := 12)
    (lo := (21745137 / 1000000000)) (hi := (10872569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 18787) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19200 / 18787) = 1/(18787 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_139 : (15527527 / 500000000) ≤ -Real.log (595613 / 614400) ∧
    -Real.log (595613 / 614400) ≤ (6211011 / 200000000) := by
  have h := checkLog_sound (w := (18787 / 1210013)) (n := 12)
    (lo := (15527527 / 500000000)) (hi := (6211011 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614400 / 595613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614400 / 595613) = 1/(595613 / 614400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_139 : (1728212991 / 1000000000) ≤ xi (18787 / 614400) ∧ xi (18787 / 614400) ≤ (3456425989 / 2000000000) ∧
    (3518536091 / 2000000000) ≤ kap (18787 / 614400) ∧ kap (18787 / 614400) ≤ (1759268049 / 1000000000) := by
  have h := endpoint_bounds (v := ((18787 / 614400) : ℝ)) (by norm_num) (by norm_num)
    log_v_139.1 (by convert! log_c_139.1 using 1; norm_num)
    log_v_139.2 (by convert! log_c_139.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_140 : (1736632083 / 500000000) ≤ -Real.log (397 / 12800) ∧
    -Real.log (397 / 12800) ≤ (868316043 / 250000000) := by
  have h := checkLog_sound (w := (3 / 797)) (n := 12)
    (lo := (3764133 / 500000000)) (hi := (7528267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 397) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(400 / 397) = 1/(397 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_140 : (3938349 / 125000000) ≤ -Real.log (12403 / 12800) ∧
    -Real.log (12403 / 12800) ≤ (31506793 / 1000000000) := by
  have h := checkLog_sound (w := (397 / 25203)) (n := 12)
    (lo := (3938349 / 125000000)) (hi := (31506793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 12403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12800 / 12403) = 1/(12403 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_140 : (3441757373 / 2000000000) ≤ xi (397 / 12800) ∧ xi (397 / 12800) ≤ (172087869 / 100000000) ∧
    (1752385479 / 1000000000) ≤ kap (397 / 12800) ∧ kap (397 / 12800) ≤ (700954193 / 400000000) := by
  have h := endpoint_bounds (v := ((397 / 12800) : ℝ)) (by norm_num) (by norm_num)
    log_v_140.1 (by convert! log_c_140.1 using 1; norm_num)
    log_v_140.2 (by convert! log_c_140.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_141 : (691849317 / 200000000) ≤ -Real.log (773 / 24576) ∧
    -Real.log (773 / 24576) ≤ (345924659 / 100000000) := by
  have h := checkLog_sound (w := (763 / 2309)) (n := 12)
    (lo := (137331573 / 200000000)) (hi := (343328933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1536 / 773) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1536 / 773) = 1/(773 / 24576) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_141 : (31958733 / 1000000000) ≤ -Real.log (23803 / 24576) ∧
    -Real.log (23803 / 24576) ≤ (15979367 / 500000000) := by
  have h := checkLog_sound (w := (773 / 48379)) (n := 12)
    (lo := (31958733 / 1000000000)) (hi := (15979367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24576 / 23803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24576 / 23803) = 1/(23803 / 24576) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_141 : (3427287851 / 2000000000) ≤ xi (773 / 24576) ∧ xi (773 / 24576) ≤ (3427287857 / 2000000000) ∧
    (1745602659 / 1000000000) ≤ kap (773 / 24576) ∧ kap (773 / 24576) ≤ (872801331 / 500000000) := by
  have h := endpoint_bounds (v := ((773 / 24576) : ℝ)) (by norm_num) (by norm_num)
    log_v_141.1 (by convert! log_c_141.1 using 1; norm_num)
    log_v_141.2 (by convert! log_c_141.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_142 : (1722711391 / 500000000) ≤ -Real.log (9797 / 307200) ∧
    -Real.log (9797 / 307200) ≤ (3445422787 / 1000000000) := by
  have h := checkLog_sound (w := (9403 / 28997)) (n := 12)
    (lo := (336417031 / 500000000)) (hi := (672834063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 9797) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(19200 / 9797) = 1/(9797 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_142 : (32410879 / 1000000000) ≤ -Real.log (297403 / 307200) ∧
    -Real.log (297403 / 307200) ≤ (25321 / 781250) := by
  have h := checkLog_sound (w := (9797 / 604603)) (n := 12)
    (lo := (32410879 / 1000000000)) (hi := (25321 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307200 / 297403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307200 / 297403) = 1/(297403 / 307200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_142 : (1706505951 / 1000000000) ≤ xi (9797 / 307200) ∧ xi (9797 / 307200) ≤ (853252977 / 500000000) ∧
    (3477833661 / 2000000000) ≤ kap (9797 / 307200) ∧ kap (9797 / 307200) ≤ (3477833667 / 2000000000) := by
  have h := endpoint_bounds (v := ((9797 / 307200) : ℝ)) (by norm_num) (by norm_num)
    log_v_142.1 (by convert! log_c_142.1 using 1; norm_num)
    log_v_142.2 (by convert! log_c_142.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_143 : (1715893737 / 500000000) ≤ -Real.log (6621 / 204800) ∧
    -Real.log (6621 / 204800) ≤ (3431787479 / 1000000000) := by
  have h := checkLog_sound (w := (6179 / 19421)) (n := 12)
    (lo := (329599377 / 500000000)) (hi := (131839751 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 6621) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12800 / 6621) = 1/(6621 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_143 : (3286323 / 100000000) ≤ -Real.log (198179 / 204800) ∧
    -Real.log (198179 / 204800) ≤ (32863231 / 1000000000) := by
  have h := checkLog_sound (w := (6621 / 402979)) (n := 12)
    (lo := (3286323 / 100000000)) (hi := (32863231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204800 / 198179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204800 / 198179) = 1/(198179 / 204800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_143 : (3398924243 / 2000000000) ≤ xi (6621 / 204800) ∧ xi (6621 / 204800) ≤ (3398924249 / 2000000000) ∧
    (216540669 / 125000000) ≤ kap (6621 / 204800) ∧ kap (6621 / 204800) ≤ (346465071 / 200000000) := by
  have h := endpoint_bounds (v := ((6621 / 204800) : ℝ)) (by norm_num) (by norm_num)
    log_v_143.1 (by convert! log_c_143.1 using 1; norm_num)
    log_v_143.2 (by convert! log_c_143.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.EntropyCurvature


