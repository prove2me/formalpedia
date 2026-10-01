-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0390Logs__8
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0390Logs__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:02:58.585527+00:00
-- url     : https://prove2.me/theorems/15e33f48-b859-4079-92d9-334e11662c11
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0390Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0391Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0390Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0391Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0392Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0393Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0394Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0395Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0396Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0397Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0390Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0391Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0392Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0393Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0394Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0395Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0396Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0397Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0390Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0391Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0392Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0393Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0394Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0395Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0396Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0397Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0390Logs (+7 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0391Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0392Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0393Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0394Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0395Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0396Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0397Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0390Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0390
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (40524383 / 200000000) ≤ -Real.log (512 / 627) ∧
    -Real.log (512 / 627) ≤ (50655479 / 250000000) := by
  have h := checkLog_sound (w := (115 / 1139)) (n := 12)
    (lo := (40524383 / 200000000)) (hi := (50655479 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((627 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(627 / 512) = 1/(512 / 627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (40524383 / 200000000) (50655479 / 250000000) (Real.log (627 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (627 / 512) = -Real.log (512 / 627) := by
    rw [show ((627 / 512) : ℝ) = ((512 / 627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (31798543 / 125000000) ≤ -Real.log (397 / 512) ∧
    -Real.log (397 / 512) ≤ (50877669 / 200000000) := by
  have h := checkLog_sound (w := (115 / 909)) (n := 12)
    (lo := (31798543 / 125000000)) (hi := (50877669 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 397) = 1/(397 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-50877669 / 200000000) (-31798543 / 125000000) (Real.log (397 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (50595663 / 250000000) ≤ -Real.log (10240 / 12537) ∧
    -Real.log (10240 / 12537) ≤ (202382653 / 1000000000) := by
  have h := checkLog_sound (w := (2297 / 22777)) (n := 12)
    (lo := (50595663 / 250000000)) (hi := (202382653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12537 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12537 / 10240) = 1/(10240 / 12537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (50595663 / 250000000) (202382653 / 1000000000) (Real.log (12537 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12537 / 10240) = -Real.log (10240 / 12537) := by
    rw [show ((12537 / 10240) : ℝ) = ((10240 / 12537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (254010581 / 1000000000) ≤ -Real.log (7943 / 10240) ∧
    -Real.log (7943 / 10240) ≤ (127005291 / 500000000) := by
  have h := checkLog_sound (w := (2297 / 18183)) (n := 12)
    (lo := (254010581 / 1000000000)) (hi := (127005291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7943) = 1/(7943 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-127005291 / 500000000) (-254010581 / 1000000000) (Real.log (7943 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (185512309 / 500000000) ≤ -Real.log (256 / 371) ∧
    -Real.log (256 / 371) ≤ (371024619 / 1000000000) := by
  have h := checkLog_sound (w := (115 / 627)) (n := 12)
    (lo := (185512309 / 500000000)) (hi := (371024619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((371 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(371 / 256) = 1/(256 / 371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (185512309 / 500000000) (371024619 / 1000000000) (Real.log (371 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (371 / 256) = -Real.log (256 / 371) := by
    rw [show ((371 / 256) : ℝ) = ((256 / 371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (298208777 / 500000000) ≤ -Real.log (141 / 256) ∧
    -Real.log (141 / 256) ≤ (119283511 / 200000000) := by
  have h := checkLog_sound (w := (115 / 397)) (n := 12)
    (lo := (298208777 / 500000000)) (hi := (119283511 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 141) = 1/(141 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-119283511 / 200000000) (-298208777 / 500000000) (Real.log (141 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (370620223 / 1000000000) ≤ -Real.log (5120 / 7417) ∧
    -Real.log (5120 / 7417) ≤ (5790941 / 15625000) := by
  have h := checkLog_sound (w := (2297 / 12537)) (n := 12)
    (lo := (370620223 / 1000000000)) (hi := (5790941 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7417 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7417 / 5120) = 1/(5120 / 7417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (370620223 / 1000000000) (5790941 / 15625000) (Real.log (7417 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7417 / 5120) = -Real.log (5120 / 7417) := by
    rw [show ((7417 / 5120) : ℝ) = ((5120 / 7417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (595354289 / 1000000000) ≤ -Real.log (2823 / 5120) ∧
    -Real.log (2823 / 5120) ≤ (59535429 / 100000000) := by
  have h := checkLog_sound (w := (2297 / 7943)) (n := 12)
    (lo := (595354289 / 1000000000)) (hi := (59535429 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2823) = 1/(2823 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-59535429 / 100000000) (-595354289 / 1000000000) (Real.log (2823 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (277737791 / 1000000000) ≤ -Real.log (50000 / 66007) ∧
    -Real.log (50000 / 66007) ≤ (4339653 / 15625000) := by
  have h := checkLog_sound (w := (16007 / 116007)) (n := 12)
    (lo := (277737791 / 1000000000)) (hi := (4339653 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66007 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(66007 / 50000) = 1/(50000 / 66007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (277737791 / 1000000000) (4339653 / 15625000) (Real.log (66007 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (66007 / 50000) = -Real.log (50000 / 66007) := by
    rw [show ((66007 / 50000) : ℝ) = ((50000 / 66007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (12058387 / 31250000) ≤ -Real.log (33993 / 50000) ∧
    -Real.log (33993 / 50000) ≤ (77173677 / 200000000) := by
  have h := checkLog_sound (w := (16007 / 83993)) (n := 12)
    (lo := (12058387 / 31250000)) (hi := (77173677 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 33993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 33993) = 1/(33993 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-77173677 / 200000000) (-12058387 / 31250000) (Real.log (33993 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (278061947 / 1000000000) ≤ -Real.log (125000 / 165071) ∧
    -Real.log (125000 / 165071) ≤ (69515487 / 250000000) := by
  have h := checkLog_sound (w := (40071 / 290071)) (n := 12)
    (lo := (278061947 / 1000000000)) (hi := (69515487 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165071 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165071 / 125000) = 1/(125000 / 165071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (278061947 / 1000000000) (69515487 / 250000000) (Real.log (165071 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (165071 / 125000) = -Real.log (125000 / 165071) := by
    rw [show ((165071 / 125000) : ℝ) = ((125000 / 165071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (386498123 / 1000000000) ≤ -Real.log (84929 / 125000) ∧
    -Real.log (84929 / 125000) ≤ (96624531 / 250000000) := by
  have h := checkLog_sound (w := (40071 / 209929)) (n := 12)
    (lo := (386498123 / 1000000000)) (hi := (96624531 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 84929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 84929) = 1/(84929 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-96624531 / 250000000) (-386498123 / 1000000000) (Real.log (84929 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (52359109 / 250000000) ≤ -Real.log (1000000 / 1232983) ∧
    -Real.log (1000000 / 1232983) ≤ (209436437 / 1000000000) := by
  have h := checkLog_sound (w := (232983 / 2232983)) (n := 12)
    (lo := (52359109 / 250000000)) (hi := (209436437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1232983 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1232983 / 1000000) = 1/(1000000 / 1232983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (52359109 / 250000000) (209436437 / 1000000000) (Real.log (1232983 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1232983 / 1000000) = -Real.log (1000000 / 1232983) := by
    rw [show ((1232983 / 1000000) : ℝ) = ((1000000 / 1232983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (265246313 / 1000000000) ≤ -Real.log (767017 / 1000000) ∧
    -Real.log (767017 / 1000000) ≤ (132623157 / 500000000) := by
  have h := checkLog_sound (w := (232983 / 1767017)) (n := 12)
    (lo := (265246313 / 1000000000)) (hi := (132623157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 767017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 767017) = 1/(767017 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-132623157 / 500000000) (-265246313 / 1000000000) (Real.log (767017 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (52426011 / 250000000) ≤ -Real.log (1000000 / 1233313) ∧
    -Real.log (1000000 / 1233313) ≤ (41940809 / 200000000) := by
  have h := checkLog_sound (w := (233313 / 2233313)) (n := 12)
    (lo := (52426011 / 250000000)) (hi := (41940809 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1233313 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1233313 / 1000000) = 1/(1000000 / 1233313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (52426011 / 250000000) (41940809 / 200000000) (Real.log (1233313 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1233313 / 1000000) = -Real.log (1000000 / 1233313) := by
    rw [show ((1233313 / 1000000) : ℝ) = ((1000000 / 1233313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (66419161 / 250000000) ≤ -Real.log (766687 / 1000000) ∧
    -Real.log (766687 / 1000000) ≤ (53135329 / 200000000) := by
  have h := checkLog_sound (w := (233313 / 1766687)) (n := 12)
    (lo := (66419161 / 250000000)) (hi := (53135329 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 766687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 766687) = 1/(766687 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-53135329 / 200000000) (-66419161 / 250000000) (Real.log (766687 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (26544247 / 40000000) ≤ -Real.log (500000000000 / 970891065807) ∧
    -Real.log (500000000000 / 970891065807) ≤ (20737693 / 31250000) := by
  have h := checkLog_sound (w := (470891065807 / 1470891065807)) (n := 12)
    (lo := (26544247 / 40000000)) (hi := (20737693 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((970891065807 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(970891065807 / 500000000000) = 1/(500000000000 / 970891065807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (26544247 / 40000000) (20737693 / 31250000) (Real.log (970891065807 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (970891065807 / 500000000000) = -Real.log (500000000000 / 970891065807) := by
    rw [show ((970891065807 / 500000000000) : ℝ) = ((500000000000 / 970891065807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (664560071 / 1000000000) ≤ -Real.log (125000000000 / 242954408977) ∧
    -Real.log (125000000000 / 242954408977) ≤ (83070009 / 125000000) := by
  have h := checkLog_sound (w := (117954408977 / 367954408977)) (n := 12)
    (lo := (664560071 / 1000000000)) (hi := (83070009 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242954408977 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242954408977 / 125000000000) = 1/(125000000000 / 242954408977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (664560071 / 1000000000) (83070009 / 125000000) (Real.log (242954408977 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (242954408977 / 125000000000) = -Real.log (125000000000 / 242954408977) := by
    rw [show ((242954408977 / 125000000000) : ℝ) = ((125000000000 / 242954408977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1898731 / 4000000) ≤ -Real.log (125000000000 / 200938017019) ∧
    -Real.log (125000000000 / 200938017019) ≤ (474682751 / 1000000000) := by
  have h := checkLog_sound (w := (75938017019 / 325938017019)) (n := 12)
    (lo := (1898731 / 4000000)) (hi := (474682751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200938017019 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200938017019 / 125000000000) = 1/(125000000000 / 200938017019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1898731 / 4000000) (474682751 / 1000000000) (Real.log (200938017019 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (200938017019 / 125000000000) = -Real.log (125000000000 / 200938017019) := by
    rw [show ((200938017019 / 125000000000) : ℝ) = ((125000000000 / 200938017019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (29711293 / 62500000) ≤ -Real.log (62500000000 / 100539154179) ∧
    -Real.log (62500000000 / 100539154179) ≤ (475380689 / 1000000000) := by
  have h := checkLog_sound (w := (38039154179 / 163039154179)) (n := 12)
    (lo := (29711293 / 62500000)) (hi := (475380689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100539154179 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100539154179 / 62500000000) = 1/(62500000000 / 100539154179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (29711293 / 62500000) (475380689 / 1000000000) (Real.log (100539154179 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (100539154179 / 62500000000) = -Real.log (62500000000 / 100539154179) := by
    rw [show ((100539154179 / 62500000000) : ℝ) = ((62500000000 / 100539154179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0390

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0391Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0391
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (50595663 / 250000000) ≤ -Real.log (10240 / 12537) ∧
    -Real.log (10240 / 12537) ≤ (202382653 / 1000000000) := by
  have h := checkLog_sound (w := (2297 / 22777)) (n := 12)
    (lo := (50595663 / 250000000)) (hi := (202382653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12537 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12537 / 10240) = 1/(10240 / 12537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (50595663 / 250000000) (202382653 / 1000000000) (Real.log (12537 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12537 / 10240) = -Real.log (10240 / 12537) := by
    rw [show ((12537 / 10240) : ℝ) = ((10240 / 12537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (254010581 / 1000000000) ≤ -Real.log (7943 / 10240) ∧
    -Real.log (7943 / 10240) ≤ (127005291 / 500000000) := by
  have h := checkLog_sound (w := (2297 / 18183)) (n := 12)
    (lo := (254010581 / 1000000000)) (hi := (127005291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7943) = 1/(7943 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-127005291 / 500000000) (-254010581 / 1000000000) (Real.log (7943 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (50535833 / 250000000) ≤ -Real.log (5120 / 6267) ∧
    -Real.log (5120 / 6267) ≤ (202143333 / 1000000000) := by
  have h := checkLog_sound (w := (1147 / 11387)) (n := 12)
    (lo := (50535833 / 250000000)) (hi := (202143333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6267 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6267 / 5120) = 1/(5120 / 6267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (50535833 / 250000000) (202143333 / 1000000000) (Real.log (6267 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6267 / 5120) = -Real.log (5120 / 6267) := by
    rw [show ((6267 / 5120) : ℝ) = ((5120 / 6267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (126816481 / 500000000) ≤ -Real.log (3973 / 5120) ∧
    -Real.log (3973 / 5120) ≤ (253632963 / 1000000000) := by
  have h := checkLog_sound (w := (1147 / 9093)) (n := 12)
    (lo := (126816481 / 500000000)) (hi := (253632963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3973) = 1/(3973 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-253632963 / 1000000000) (-126816481 / 500000000) (Real.log (3973 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (370620223 / 1000000000) ≤ -Real.log (5120 / 7417) ∧
    -Real.log (5120 / 7417) ≤ (5790941 / 15625000) := by
  have h := checkLog_sound (w := (2297 / 12537)) (n := 12)
    (lo := (370620223 / 1000000000)) (hi := (5790941 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7417 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7417 / 5120) = 1/(5120 / 7417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (370620223 / 1000000000) (5790941 / 15625000) (Real.log (7417 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7417 / 5120) = -Real.log (5120 / 7417) := by
    rw [show ((7417 / 5120) : ℝ) = ((5120 / 7417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (595354289 / 1000000000) ≤ -Real.log (2823 / 5120) ∧
    -Real.log (2823 / 5120) ≤ (59535429 / 100000000) := by
  have h := checkLog_sound (w := (2297 / 7943)) (n := 12)
    (lo := (595354289 / 1000000000)) (hi := (59535429 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2823) = 1/(2823 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-59535429 / 100000000) (-595354289 / 1000000000) (Real.log (2823 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (74043133 / 200000000) ≤ -Real.log (2560 / 3707) ∧
    -Real.log (2560 / 3707) ≤ (185107833 / 500000000) := by
  have h := checkLog_sound (w := (1147 / 6267)) (n := 12)
    (lo := (74043133 / 200000000)) (hi := (185107833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3707 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3707 / 2560) = 1/(2560 / 3707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (74043133 / 200000000) (185107833 / 500000000) (Real.log (3707 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3707 / 2560) = -Real.log (2560 / 3707) := by
    rw [show ((3707 / 2560) : ℝ) = ((2560 / 3707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (297146077 / 500000000) ≤ -Real.log (1413 / 2560) ∧
    -Real.log (1413 / 2560) ≤ (118858431 / 200000000) := by
  have h := checkLog_sound (w := (1147 / 3973)) (n := 12)
    (lo := (297146077 / 500000000)) (hi := (118858431 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1413) = 1/(1413 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-118858431 / 200000000) (-297146077 / 500000000) (Real.log (1413 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (138707523 / 500000000) ≤ -Real.log (500000 / 659857) ∧
    -Real.log (500000 / 659857) ≤ (277415047 / 1000000000) := by
  have h := checkLog_sound (w := (159857 / 1159857)) (n := 12)
    (lo := (138707523 / 500000000)) (hi := (277415047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((659857 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(659857 / 500000) = 1/(500000 / 659857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (138707523 / 500000000) (277415047 / 1000000000) (Real.log (659857 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (659857 / 500000) = -Real.log (500000 / 659857) := by
    rw [show ((659857 / 500000) : ℝ) = ((500000 / 659857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (19262099 / 50000000) ≤ -Real.log (340143 / 500000) ∧
    -Real.log (340143 / 500000) ≤ (385241981 / 1000000000) := by
  have h := checkLog_sound (w := (159857 / 840143)) (n := 12)
    (lo := (19262099 / 50000000)) (hi := (385241981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 340143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 340143) = 1/(340143 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-385241981 / 1000000000) (-19262099 / 50000000) (Real.log (340143 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (277738549 / 1000000000) ≤ -Real.log (1000000 / 1320141) ∧
    -Real.log (1000000 / 1320141) ≤ (5554771 / 20000000) := by
  have h := checkLog_sound (w := (320141 / 2320141)) (n := 12)
    (lo := (277738549 / 1000000000)) (hi := (5554771 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1320141 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1320141 / 1000000) = 1/(1000000 / 1320141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (277738549 / 1000000000) (5554771 / 20000000) (Real.log (1320141 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1320141 / 1000000) = -Real.log (1000000 / 1320141) := by
    rw [show ((1320141 / 1000000) : ℝ) = ((1000000 / 1320141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (77173971 / 200000000) ≤ -Real.log (679859 / 1000000) ∧
    -Real.log (679859 / 1000000) ≤ (12058433 / 31250000) := by
  have h := checkLog_sound (w := (320141 / 1679859)) (n := 12)
    (lo := (77173971 / 200000000)) (hi := (12058433 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 679859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 679859) = 1/(679859 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-12058433 / 31250000) (-77173971 / 200000000) (Real.log (679859 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (209170379 / 1000000000) ≤ -Real.log (200000 / 246531) ∧
    -Real.log (200000 / 246531) ≤ (10458519 / 50000000) := by
  have h := checkLog_sound (w := (46531 / 446531)) (n := 12)
    (lo := (209170379 / 1000000000)) (hi := (10458519 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246531 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246531 / 200000) = 1/(200000 / 246531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (209170379 / 1000000000) (10458519 / 50000000) (Real.log (246531 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (246531 / 200000) = -Real.log (200000 / 246531) := by
    rw [show ((246531 / 200000) : ℝ) = ((200000 / 246531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (132409387 / 500000000) ≤ -Real.log (153469 / 200000) ∧
    -Real.log (153469 / 200000) ≤ (10592751 / 40000000) := by
  have h := checkLog_sound (w := (46531 / 353469)) (n := 12)
    (lo := (132409387 / 500000000)) (hi := (10592751 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 153469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 153469) = 1/(153469 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-10592751 / 40000000) (-132409387 / 500000000) (Real.log (153469 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (209437247 / 1000000000) ≤ -Real.log (125000 / 154123) ∧
    -Real.log (125000 / 154123) ≤ (3272457 / 15625000) := by
  have h := checkLog_sound (w := (29123 / 279123)) (n := 12)
    (lo := (209437247 / 1000000000)) (hi := (3272457 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154123 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154123 / 125000) = 1/(125000 / 154123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (209437247 / 1000000000) (3272457 / 15625000) (Real.log (154123 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (154123 / 125000) = -Real.log (125000 / 154123) := by
    rw [show ((154123 / 125000) : ℝ) = ((125000 / 154123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (265247617 / 1000000000) ≤ -Real.log (95877 / 125000) ∧
    -Real.log (95877 / 125000) ≤ (132623809 / 500000000) := by
  have h := checkLog_sound (w := (29123 / 220877)) (n := 12)
    (lo := (265247617 / 1000000000)) (hi := (132623809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 95877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 95877) = 1/(95877 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-132623809 / 500000000) (-265247617 / 1000000000) (Real.log (95877 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (662657027 / 1000000000) ≤ -Real.log (125000000000 / 242492495803) ∧
    -Real.log (125000000000 / 242492495803) ≤ (165664257 / 250000000) := by
  have h := checkLog_sound (w := (117492495803 / 367492495803)) (n := 12)
    (lo := (662657027 / 1000000000)) (hi := (165664257 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242492495803 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242492495803 / 125000000000) = 1/(125000000000 / 242492495803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (662657027 / 1000000000) (165664257 / 250000000) (Real.log (242492495803 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (242492495803 / 125000000000) = -Real.log (125000000000 / 242492495803) := by
    rw [show ((242492495803 / 125000000000) : ℝ) = ((125000000000 / 242492495803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (165902101 / 250000000) ≤ -Real.log (125000000000 / 242723307333) ∧
    -Real.log (125000000000 / 242723307333) ≤ (132721681 / 200000000) := by
  have h := checkLog_sound (w := (117723307333 / 367723307333)) (n := 12)
    (lo := (165902101 / 250000000)) (hi := (132721681 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242723307333 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242723307333 / 125000000000) = 1/(125000000000 / 242723307333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (165902101 / 250000000) (132721681 / 200000000) (Real.log (242723307333 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (242723307333 / 125000000000) = -Real.log (125000000000 / 242723307333) := by
    rw [show ((242723307333 / 125000000000) : ℝ) = ((125000000000 / 242723307333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (473989153 / 1000000000) ≤ -Real.log (62500000000 / 100399347751) ∧
    -Real.log (62500000000 / 100399347751) ≤ (236994577 / 500000000) := by
  have h := checkLog_sound (w := (37899347751 / 162899347751)) (n := 12)
    (lo := (473989153 / 1000000000)) (hi := (236994577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100399347751 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100399347751 / 62500000000) = 1/(62500000000 / 100399347751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (473989153 / 1000000000) (236994577 / 500000000) (Real.log (100399347751 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (100399347751 / 62500000000) = -Real.log (62500000000 / 100399347751) := by
    rw [show ((100399347751 / 62500000000) : ℝ) = ((62500000000 / 100399347751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (7416951 / 15625000) ≤ -Real.log (500000000000 / 803753767849) ∧
    -Real.log (500000000000 / 803753767849) ≤ (94936973 / 200000000) := by
  have h := checkLog_sound (w := (303753767849 / 1303753767849)) (n := 12)
    (lo := (7416951 / 15625000)) (hi := (94936973 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((803753767849 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(803753767849 / 500000000000) = 1/(500000000000 / 803753767849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (7416951 / 15625000) (94936973 / 200000000) (Real.log (803753767849 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (803753767849 / 500000000000) = -Real.log (500000000000 / 803753767849) := by
    rw [show ((803753767849 / 500000000000) : ℝ) = ((500000000000 / 803753767849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0391

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0392Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0392
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (50535833 / 250000000) ≤ -Real.log (5120 / 6267) ∧
    -Real.log (5120 / 6267) ≤ (202143333 / 1000000000) := by
  have h := checkLog_sound (w := (1147 / 11387)) (n := 12)
    (lo := (50535833 / 250000000)) (hi := (202143333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6267 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6267 / 5120) = 1/(5120 / 6267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (50535833 / 250000000) (202143333 / 1000000000) (Real.log (6267 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6267 / 5120) = -Real.log (5120 / 6267) := by
    rw [show ((6267 / 5120) : ℝ) = ((5120 / 6267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (126816481 / 500000000) ≤ -Real.log (3973 / 5120) ∧
    -Real.log (3973 / 5120) ≤ (253632963 / 1000000000) := by
  have h := checkLog_sound (w := (1147 / 9093)) (n := 12)
    (lo := (126816481 / 500000000)) (hi := (253632963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3973) = 1/(3973 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-253632963 / 1000000000) (-126816481 / 500000000) (Real.log (3973 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (100951977 / 500000000) ≤ -Real.log (10240 / 12531) ∧
    -Real.log (10240 / 12531) ≤ (40380791 / 200000000) := by
  have h := checkLog_sound (w := (2291 / 22771)) (n := 12)
    (lo := (100951977 / 500000000)) (hi := (40380791 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12531 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12531 / 10240) = 1/(10240 / 12531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (100951977 / 500000000) (40380791 / 200000000) (Real.log (12531 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12531 / 10240) = -Real.log (10240 / 12531) := by
    rw [show ((12531 / 10240) : ℝ) = ((10240 / 12531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (50651097 / 200000000) ≤ -Real.log (7949 / 10240) ∧
    -Real.log (7949 / 10240) ≤ (126627743 / 500000000) := by
  have h := checkLog_sound (w := (2291 / 18189)) (n := 12)
    (lo := (50651097 / 200000000)) (hi := (126627743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7949) = 1/(7949 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-126627743 / 500000000) (-50651097 / 200000000) (Real.log (7949 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (74043133 / 200000000) ≤ -Real.log (2560 / 3707) ∧
    -Real.log (2560 / 3707) ≤ (185107833 / 500000000) := by
  have h := checkLog_sound (w := (1147 / 6267)) (n := 12)
    (lo := (74043133 / 200000000)) (hi := (185107833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3707 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3707 / 2560) = 1/(2560 / 3707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (74043133 / 200000000) (185107833 / 500000000) (Real.log (3707 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3707 / 2560) = -Real.log (2560 / 3707) := by
    rw [show ((3707 / 2560) : ℝ) = ((2560 / 3707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (297146077 / 500000000) ≤ -Real.log (1413 / 2560) ∧
    -Real.log (1413 / 2560) ≤ (118858431 / 200000000) := by
  have h := checkLog_sound (w := (1147 / 3973)) (n := 12)
    (lo := (297146077 / 500000000)) (hi := (118858431 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1413) = 1/(1413 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-118858431 / 200000000) (-297146077 / 500000000) (Real.log (1413 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (369810943 / 1000000000) ≤ -Real.log (5120 / 7411) ∧
    -Real.log (5120 / 7411) ≤ (722287 / 1953125) := by
  have h := checkLog_sound (w := (2291 / 12531)) (n := 12)
    (lo := (369810943 / 1000000000)) (hi := (722287 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7411 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7411 / 5120) = 1/(5120 / 7411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (369810943 / 1000000000) (722287 / 1953125) (Real.log (7411 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7411 / 5120) = -Real.log (5120 / 7411) := by
    rw [show ((7411 / 5120) : ℝ) = ((5120 / 7411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (296615573 / 500000000) ≤ -Real.log (2829 / 5120) ∧
    -Real.log (2829 / 5120) ≤ (593231147 / 1000000000) := by
  have h := checkLog_sound (w := (2291 / 7949)) (n := 12)
    (lo := (296615573 / 500000000)) (hi := (593231147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2829) = 1/(2829 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-593231147 / 1000000000) (-296615573 / 500000000) (Real.log (2829 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (277092197 / 1000000000) ≤ -Real.log (125000 / 164911) ∧
    -Real.log (125000 / 164911) ≤ (138546099 / 500000000) := by
  have h := checkLog_sound (w := (39911 / 289911)) (n := 12)
    (lo := (277092197 / 1000000000)) (hi := (138546099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164911 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164911 / 125000) = 1/(125000 / 164911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (277092197 / 1000000000) (138546099 / 500000000) (Real.log (164911 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (164911 / 125000) = -Real.log (125000 / 164911) := by
    rw [show ((164911 / 125000) : ℝ) = ((125000 / 164911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (384615969 / 1000000000) ≤ -Real.log (85089 / 125000) ∧
    -Real.log (85089 / 125000) ≤ (38461597 / 100000000) := by
  have h := checkLog_sound (w := (39911 / 210089)) (n := 12)
    (lo := (384615969 / 1000000000)) (hi := (38461597 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 85089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 85089) = 1/(85089 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-38461597 / 100000000) (-384615969 / 1000000000) (Real.log (85089 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (69353951 / 250000000) ≤ -Real.log (200000 / 263943) ∧
    -Real.log (200000 / 263943) ≤ (55483161 / 200000000) := by
  have h := checkLog_sound (w := (63943 / 463943)) (n := 12)
    (lo := (69353951 / 250000000)) (hi := (55483161 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((263943 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(263943 / 200000) = 1/(200000 / 263943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (69353951 / 250000000) (55483161 / 200000000) (Real.log (263943 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (263943 / 200000) = -Real.log (200000 / 263943) := by
    rw [show ((263943 / 200000) : ℝ) = ((200000 / 263943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (7704869 / 20000000) ≤ -Real.log (136057 / 200000) ∧
    -Real.log (136057 / 200000) ≤ (385243451 / 1000000000) := by
  have h := checkLog_sound (w := (63943 / 336057)) (n := 12)
    (lo := (7704869 / 20000000)) (hi := (385243451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 136057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 136057) = 1/(136057 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-385243451 / 1000000000) (-7704869 / 20000000) (Real.log (136057 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (2611293 / 12500000) ≤ -Real.log (500000 / 616163) ∧
    -Real.log (500000 / 616163) ≤ (208903441 / 1000000000) := by
  have h := checkLog_sound (w := (116163 / 1116163)) (n := 12)
    (lo := (2611293 / 12500000)) (hi := (208903441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((616163 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(616163 / 500000) = 1/(500000 / 616163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (2611293 / 12500000) (208903441 / 1000000000) (Real.log (616163 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (616163 / 500000) = -Real.log (500000 / 616163) := by
    rw [show ((616163 / 500000) : ℝ) = ((500000 / 616163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (52878023 / 200000000) ≤ -Real.log (383837 / 500000) ∧
    -Real.log (383837 / 500000) ≤ (66097529 / 250000000) := by
  have h := checkLog_sound (w := (116163 / 883837)) (n := 12)
    (lo := (52878023 / 200000000)) (hi := (66097529 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 383837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 383837) = 1/(383837 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-66097529 / 250000000) (-52878023 / 200000000) (Real.log (383837 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (20917119 / 100000000) ≤ -Real.log (62500 / 77041) ∧
    -Real.log (62500 / 77041) ≤ (209171191 / 1000000000) := by
  have h := checkLog_sound (w := (14541 / 139541)) (n := 12)
    (lo := (20917119 / 100000000)) (hi := (209171191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77041 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77041 / 62500) = 1/(62500 / 77041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (20917119 / 100000000) (209171191 / 1000000000) (Real.log (77041 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (77041 / 62500) = -Real.log (62500 / 77041) := by
    rw [show ((77041 / 62500) : ℝ) = ((62500 / 77041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (264820077 / 1000000000) ≤ -Real.log (47959 / 62500) ∧
    -Real.log (47959 / 62500) ≤ (132410039 / 500000000) := by
  have h := checkLog_sound (w := (14541 / 110459)) (n := 12)
    (lo := (264820077 / 1000000000)) (hi := (132410039 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 47959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 47959) = 1/(47959 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-132410039 / 500000000) (-264820077 / 1000000000) (Real.log (47959 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (330854083 / 500000000) ≤ -Real.log (500000000000 / 969050053473) ∧
    -Real.log (500000000000 / 969050053473) ≤ (661708167 / 1000000000) := by
  have h := checkLog_sound (w := (469050053473 / 1469050053473)) (n := 12)
    (lo := (330854083 / 500000000)) (hi := (661708167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((969050053473 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(969050053473 / 500000000000) = 1/(500000000000 / 969050053473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (330854083 / 500000000) (661708167 / 1000000000) (Real.log (969050053473 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (969050053473 / 500000000000) = -Real.log (500000000000 / 969050053473) := by
    rw [show ((969050053473 / 500000000000) : ℝ) = ((500000000000 / 969050053473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (132531851 / 200000000) ≤ -Real.log (125000000000 / 242493036007) ∧
    -Real.log (125000000000 / 242493036007) ≤ (82832407 / 125000000) := by
  have h := checkLog_sound (w := (117493036007 / 367493036007)) (n := 12)
    (lo := (132531851 / 200000000)) (hi := (82832407 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242493036007 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242493036007 / 125000000000) = 1/(125000000000 / 242493036007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (132531851 / 200000000) (82832407 / 125000000) (Real.log (242493036007 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (242493036007 / 125000000000) = -Real.log (125000000000 / 242493036007) := by
    rw [show ((242493036007 / 125000000000) : ℝ) = ((125000000000 / 242493036007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (94658711 / 200000000) ≤ -Real.log (500000000000 / 802636275293) ∧
    -Real.log (500000000000 / 802636275293) ≤ (118323389 / 250000000) := by
  have h := checkLog_sound (w := (302636275293 / 1302636275293)) (n := 12)
    (lo := (94658711 / 200000000)) (hi := (118323389 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((802636275293 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(802636275293 / 500000000000) = 1/(500000000000 / 802636275293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (94658711 / 200000000) (118323389 / 250000000) (Real.log (802636275293 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (802636275293 / 500000000000) = -Real.log (500000000000 / 802636275293) := by
    rw [show ((802636275293 / 500000000000) : ℝ) = ((500000000000 / 802636275293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (118497817 / 250000000) ≤ -Real.log (500000000000 / 803196480327) ∧
    -Real.log (500000000000 / 803196480327) ≤ (473991269 / 1000000000) := by
  have h := checkLog_sound (w := (303196480327 / 1303196480327)) (n := 12)
    (lo := (118497817 / 250000000)) (hi := (473991269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((803196480327 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(803196480327 / 500000000000) = 1/(500000000000 / 803196480327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (118497817 / 250000000) (473991269 / 1000000000) (Real.log (803196480327 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (803196480327 / 500000000000) = -Real.log (500000000000 / 803196480327) := by
    rw [show ((803196480327 / 500000000000) : ℝ) = ((500000000000 / 803196480327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0392

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0393Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0393
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (100951977 / 500000000) ≤ -Real.log (10240 / 12531) ∧
    -Real.log (10240 / 12531) ≤ (40380791 / 200000000) := by
  have h := checkLog_sound (w := (2291 / 22771)) (n := 12)
    (lo := (100951977 / 500000000)) (hi := (40380791 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12531 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12531 / 10240) = 1/(10240 / 12531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (100951977 / 500000000) (40380791 / 200000000) (Real.log (12531 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12531 / 10240) = -Real.log (10240 / 12531) := by
    rw [show ((12531 / 10240) : ℝ) = ((10240 / 12531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (50651097 / 200000000) ≤ -Real.log (7949 / 10240) ∧
    -Real.log (7949 / 10240) ≤ (126627743 / 500000000) := by
  have h := checkLog_sound (w := (2291 / 18189)) (n := 12)
    (lo := (50651097 / 200000000)) (hi := (126627743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7949) = 1/(7949 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-126627743 / 500000000) (-50651097 / 200000000) (Real.log (7949 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (201664519 / 1000000000) ≤ -Real.log (640 / 783) ∧
    -Real.log (640 / 783) ≤ (5041613 / 25000000) := by
  have h := checkLog_sound (w := (143 / 1423)) (n := 12)
    (lo := (201664519 / 1000000000)) (hi := (5041613 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((783 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(783 / 640) = 1/(640 / 783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (201664519 / 1000000000) (5041613 / 25000000) (Real.log (783 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (783 / 640) = -Real.log (640 / 783) := by
    rw [show ((783 / 640) : ℝ) = ((640 / 783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (5057563 / 20000000) ≤ -Real.log (497 / 640) ∧
    -Real.log (497 / 640) ≤ (252878151 / 1000000000) := by
  have h := checkLog_sound (w := (143 / 1137)) (n := 12)
    (lo := (5057563 / 20000000)) (hi := (252878151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 497) = 1/(497 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-252878151 / 1000000000) (-5057563 / 20000000) (Real.log (497 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (369810943 / 1000000000) ≤ -Real.log (5120 / 7411) ∧
    -Real.log (5120 / 7411) ≤ (722287 / 1953125) := by
  have h := checkLog_sound (w := (2291 / 12531)) (n := 12)
    (lo := (369810943 / 1000000000)) (hi := (722287 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7411 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7411 / 5120) = 1/(5120 / 7411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (369810943 / 1000000000) (722287 / 1953125) (Real.log (7411 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7411 / 5120) = -Real.log (5120 / 7411) := by
    rw [show ((7411 / 5120) : ℝ) = ((5120 / 7411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (296615573 / 500000000) ≤ -Real.log (2829 / 5120) ∧
    -Real.log (2829 / 5120) ≤ (593231147 / 1000000000) := by
  have h := checkLog_sound (w := (2291 / 7949)) (n := 12)
    (lo := (296615573 / 500000000)) (hi := (593231147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2829) = 1/(2829 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-593231147 / 1000000000) (-296615573 / 500000000) (Real.log (2829 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (184703029 / 500000000) ≤ -Real.log (320 / 463) ∧
    -Real.log (320 / 463) ≤ (369406059 / 1000000000) := by
  have h := checkLog_sound (w := (143 / 783)) (n := 12)
    (lo := (184703029 / 500000000)) (hi := (369406059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((463 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(463 / 320) = 1/(320 / 463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (184703029 / 500000000) (369406059 / 1000000000) (Real.log (463 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (463 / 320) = -Real.log (320 / 463) := by
    rw [show ((463 / 320) : ℝ) = ((320 / 463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (592171263 / 1000000000) ≤ -Real.log (177 / 320) ∧
    -Real.log (177 / 320) ≤ (2313169 / 3906250) := by
  have h := checkLog_sound (w := (143 / 497)) (n := 12)
    (lo := (592171263 / 1000000000)) (hi := (2313169 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 177) = 1/(177 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2313169 / 3906250) (-592171263 / 1000000000) (Real.log (177 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (55353697 / 200000000) ≤ -Real.log (1000000 / 1318861) ∧
    -Real.log (1000000 / 1318861) ≤ (138384243 / 500000000) := by
  have h := checkLog_sound (w := (318861 / 2318861)) (n := 12)
    (lo := (55353697 / 200000000)) (hi := (138384243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1318861 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1318861 / 1000000) = 1/(1000000 / 1318861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (55353697 / 200000000) (138384243 / 500000000) (Real.log (1318861 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1318861 / 1000000) = -Real.log (1000000 / 1318861) := by
    rw [show ((1318861 / 1000000) : ℝ) = ((1000000 / 1318861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (191994441 / 500000000) ≤ -Real.log (681139 / 1000000) ∧
    -Real.log (681139 / 1000000) ≤ (383988883 / 1000000000) := by
  have h := checkLog_sound (w := (318861 / 1681139)) (n := 12)
    (lo := (191994441 / 500000000)) (hi := (383988883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 681139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 681139) = 1/(681139 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-383988883 / 1000000000) (-191994441 / 500000000) (Real.log (681139 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (55418591 / 200000000) ≤ -Real.log (1000000 / 1319289) ∧
    -Real.log (1000000 / 1319289) ≤ (69273239 / 250000000) := by
  have h := checkLog_sound (w := (319289 / 2319289)) (n := 12)
    (lo := (55418591 / 200000000)) (hi := (69273239 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1319289 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1319289 / 1000000) = 1/(1000000 / 1319289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (55418591 / 200000000) (69273239 / 250000000) (Real.log (1319289 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1319289 / 1000000) = -Real.log (1000000 / 1319289) := by
    rw [show ((1319289 / 1000000) : ℝ) = ((1000000 / 1319289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (192308719 / 500000000) ≤ -Real.log (680711 / 1000000) ∧
    -Real.log (680711 / 1000000) ≤ (384617439 / 1000000000) := by
  have h := checkLog_sound (w := (319289 / 1680711)) (n := 12)
    (lo := (192308719 / 500000000)) (hi := (384617439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 680711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 680711) = 1/(680711 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-384617439 / 1000000000) (-192308719 / 500000000) (Real.log (680711 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (208637241 / 1000000000) ≤ -Real.log (500000 / 615999) ∧
    -Real.log (500000 / 615999) ≤ (104318621 / 500000000) := by
  have h := checkLog_sound (w := (115999 / 1115999)) (n := 12)
    (lo := (208637241 / 1000000000)) (hi := (104318621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((615999 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(615999 / 500000) = 1/(500000 / 615999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (208637241 / 1000000000) (104318621 / 500000000) (Real.log (615999 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (615999 / 500000) = -Real.log (500000 / 615999) := by
    rw [show ((615999 / 500000) : ℝ) = ((500000 / 615999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (263962941 / 1000000000) ≤ -Real.log (384001 / 500000) ∧
    -Real.log (384001 / 500000) ≤ (131981471 / 500000000) := by
  have h := checkLog_sound (w := (115999 / 884001)) (n := 12)
    (lo := (263962941 / 1000000000)) (hi := (131981471 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 384001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 384001) = 1/(384001 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-131981471 / 500000000) (-263962941 / 1000000000) (Real.log (384001 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (208904251 / 1000000000) ≤ -Real.log (1000000 / 1232327) ∧
    -Real.log (1000000 / 1232327) ≤ (52226063 / 250000000) := by
  have h := checkLog_sound (w := (232327 / 2232327)) (n := 12)
    (lo := (208904251 / 1000000000)) (hi := (52226063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1232327 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1232327 / 1000000) = 1/(1000000 / 1232327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (208904251 / 1000000000) (52226063 / 250000000) (Real.log (1232327 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1232327 / 1000000) = -Real.log (1000000 / 1232327) := by
    rw [show ((1232327 / 1000000) : ℝ) = ((1000000 / 1232327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (264391417 / 1000000000) ≤ -Real.log (767673 / 1000000) ∧
    -Real.log (767673 / 1000000) ≤ (132195709 / 500000000) := by
  have h := checkLog_sound (w := (232327 / 1767673)) (n := 12)
    (lo := (264391417 / 1000000000)) (hi := (132195709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 767673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 767673) = 1/(767673 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-132195709 / 500000000) (-264391417 / 1000000000) (Real.log (767673 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (660757367 / 1000000000) ≤ -Real.log (500000000000 / 968129119019) ∧
    -Real.log (500000000000 / 968129119019) ≤ (82594671 / 125000000) := by
  have h := checkLog_sound (w := (468129119019 / 1468129119019)) (n := 12)
    (lo := (660757367 / 1000000000)) (hi := (82594671 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((968129119019 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(968129119019 / 500000000000) = 1/(500000000000 / 968129119019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (660757367 / 1000000000) (82594671 / 125000000) (Real.log (968129119019 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (968129119019 / 500000000000) = -Real.log (500000000000 / 968129119019) := by
    rw [show ((968129119019 / 500000000000) : ℝ) = ((500000000000 / 968129119019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (661710393 / 1000000000) ≤ -Real.log (100000000000 / 193810442317) ∧
    -Real.log (100000000000 / 193810442317) ≤ (330855197 / 500000000) := by
  have h := checkLog_sound (w := (93810442317 / 293810442317)) (n := 12)
    (lo := (661710393 / 1000000000)) (hi := (330855197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((193810442317 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(193810442317 / 100000000000) = 1/(100000000000 / 193810442317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (661710393 / 1000000000) (330855197 / 500000000) (Real.log (193810442317 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (193810442317 / 100000000000) = -Real.log (100000000000 / 193810442317) := by
    rw [show ((193810442317 / 100000000000) : ℝ) = ((100000000000 / 193810442317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (472600183 / 1000000000) ≤ -Real.log (200000000 / 320831977) ∧
    -Real.log (200000000 / 320831977) ≤ (59075023 / 125000000) := by
  have h := checkLog_sound (w := (120831977 / 520831977)) (n := 12)
    (lo := (472600183 / 1000000000)) (hi := (59075023 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320831977 / 200000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320831977 / 200000000) = 1/(200000000 / 320831977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (472600183 / 1000000000) (59075023 / 125000000) (Real.log (320831977 / 200000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (320831977 / 200000000) = -Real.log (200000000 / 320831977) := by
    rw [show ((320831977 / 200000000) : ℝ) = ((200000000 / 320831977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (473295669 / 1000000000) ≤ -Real.log (250000000000 / 401318986079) ∧
    -Real.log (250000000000 / 401318986079) ≤ (47329567 / 100000000) := by
  have h := checkLog_sound (w := (151318986079 / 651318986079)) (n := 12)
    (lo := (473295669 / 1000000000)) (hi := (47329567 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((401318986079 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(401318986079 / 250000000000) = 1/(250000000000 / 401318986079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (473295669 / 1000000000) (47329567 / 100000000) (Real.log (401318986079 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (401318986079 / 250000000000) = -Real.log (250000000000 / 401318986079) := by
    rw [show ((401318986079 / 250000000000) : ℝ) = ((250000000000 / 401318986079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0393

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0394Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0394
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (201664519 / 1000000000) ≤ -Real.log (640 / 783) ∧
    -Real.log (640 / 783) ≤ (5041613 / 25000000) := by
  have h := checkLog_sound (w := (143 / 1423)) (n := 12)
    (lo := (201664519 / 1000000000)) (hi := (5041613 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((783 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(783 / 640) = 1/(640 / 783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (201664519 / 1000000000) (5041613 / 25000000) (Real.log (783 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (783 / 640) = -Real.log (640 / 783) := by
    rw [show ((783 / 640) : ℝ) = ((640 / 783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (5057563 / 20000000) ≤ -Real.log (497 / 640) ∧
    -Real.log (497 / 640) ≤ (252878151 / 1000000000) := by
  have h := checkLog_sound (w := (143 / 1137)) (n := 12)
    (lo := (5057563 / 20000000)) (hi := (252878151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 497) = 1/(497 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-252878151 / 1000000000) (-5057563 / 20000000) (Real.log (497 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (201425027 / 1000000000) ≤ -Real.log (2048 / 2505) ∧
    -Real.log (2048 / 2505) ≤ (50356257 / 250000000) := by
  have h := checkLog_sound (w := (457 / 4553)) (n := 12)
    (lo := (201425027 / 1000000000)) (hi := (50356257 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2505 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2505 / 2048) = 1/(2048 / 2505) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (201425027 / 1000000000) (50356257 / 250000000) (Real.log (2505 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2505 / 2048) = -Real.log (2048 / 2505) := by
    rw [show ((2505 / 2048) : ℝ) = ((2048 / 2505) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (252500957 / 1000000000) ≤ -Real.log (1591 / 2048) ∧
    -Real.log (1591 / 2048) ≤ (126250479 / 500000000) := by
  have h := checkLog_sound (w := (457 / 3639)) (n := 12)
    (lo := (252500957 / 1000000000)) (hi := (126250479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1591) = 1/(1591 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-126250479 / 500000000) (-252500957 / 1000000000) (Real.log (1591 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (184703029 / 500000000) ≤ -Real.log (320 / 463) ∧
    -Real.log (320 / 463) ≤ (369406059 / 1000000000) := by
  have h := checkLog_sound (w := (143 / 783)) (n := 12)
    (lo := (184703029 / 500000000)) (hi := (369406059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((463 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(463 / 320) = 1/(320 / 463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (184703029 / 500000000) (369406059 / 1000000000) (Real.log (463 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (463 / 320) = -Real.log (320 / 463) := by
    rw [show ((463 / 320) : ℝ) = ((320 / 463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (592171263 / 1000000000) ≤ -Real.log (177 / 320) ∧
    -Real.log (177 / 320) ≤ (2313169 / 3906250) := by
  have h := checkLog_sound (w := (143 / 497)) (n := 12)
    (lo := (592171263 / 1000000000)) (hi := (2313169 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 177) = 1/(177 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2313169 / 3906250) (-592171263 / 1000000000) (Real.log (177 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23062563 / 62500000) ≤ -Real.log (1024 / 1481) ∧
    -Real.log (1024 / 1481) ≤ (369001009 / 1000000000) := by
  have h := checkLog_sound (w := (457 / 2505)) (n := 12)
    (lo := (23062563 / 62500000)) (hi := (369001009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1481 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1481 / 1024) = 1/(1024 / 1481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23062563 / 62500000) (369001009 / 1000000000) (Real.log (1481 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1481 / 1024) = -Real.log (1024 / 1481) := by
    rw [show ((1481 / 1024) : ℝ) = ((1024 / 1481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (591112501 / 1000000000) ≤ -Real.log (567 / 1024) ∧
    -Real.log (567 / 1024) ≤ (295556251 / 500000000) := by
  have h := checkLog_sound (w := (457 / 1591)) (n := 12)
    (lo := (591112501 / 1000000000)) (hi := (295556251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 567) = 1/(567 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-295556251 / 500000000) (-591112501 / 1000000000) (Real.log (567 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (276445427 / 1000000000) ≤ -Real.log (200000 / 263687) ∧
    -Real.log (200000 / 263687) ≤ (69111357 / 250000000) := by
  have h := checkLog_sound (w := (63687 / 463687)) (n := 12)
    (lo := (276445427 / 1000000000)) (hi := (69111357 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((263687 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(263687 / 200000) = 1/(200000 / 263687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (276445427 / 1000000000) (69111357 / 250000000) (Real.log (263687 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (263687 / 200000) = -Real.log (200000 / 263687) := by
    rw [show ((263687 / 200000) : ℝ) = ((200000 / 263687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (191681827 / 500000000) ≤ -Real.log (136313 / 200000) ∧
    -Real.log (136313 / 200000) ≤ (76672731 / 200000000) := by
  have h := checkLog_sound (w := (63687 / 336313)) (n := 12)
    (lo := (191681827 / 500000000)) (hi := (76672731 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 136313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 136313) = 1/(136313 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-76672731 / 200000000) (-191681827 / 500000000) (Real.log (136313 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (276769243 / 1000000000) ≤ -Real.log (500000 / 659431) ∧
    -Real.log (500000 / 659431) ≤ (69192311 / 250000000) := by
  have h := checkLog_sound (w := (159431 / 1159431)) (n := 12)
    (lo := (276769243 / 1000000000)) (hi := (69192311 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((659431 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(659431 / 500000) = 1/(500000 / 659431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (276769243 / 1000000000) (69192311 / 250000000) (Real.log (659431 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (659431 / 500000) = -Real.log (500000 / 659431) := by
    rw [show ((659431 / 500000) : ℝ) = ((500000 / 659431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (7679807 / 20000000) ≤ -Real.log (340569 / 500000) ∧
    -Real.log (340569 / 500000) ≤ (383990351 / 1000000000) := by
  have h := checkLog_sound (w := (159431 / 840569)) (n := 12)
    (lo := (7679807 / 20000000)) (hi := (383990351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 340569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 340569) = 1/(340569 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-383990351 / 1000000000) (-7679807 / 20000000) (Real.log (340569 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (52092743 / 250000000) ≤ -Real.log (100000 / 123167) ∧
    -Real.log (100000 / 123167) ≤ (208370973 / 1000000000) := by
  have h := checkLog_sound (w := (23167 / 223167)) (n := 12)
    (lo := (52092743 / 250000000)) (hi := (208370973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123167 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123167 / 100000) = 1/(100000 / 123167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (52092743 / 250000000) (208370973 / 1000000000) (Real.log (123167 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (123167 / 100000) = -Real.log (100000 / 123167) := by
    rw [show ((123167 / 100000) : ℝ) = ((100000 / 123167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (5270719 / 20000000) ≤ -Real.log (76833 / 100000) ∧
    -Real.log (76833 / 100000) ≤ (263535951 / 1000000000) := by
  have h := checkLog_sound (w := (23167 / 176833)) (n := 12)
    (lo := (5270719 / 20000000)) (hi := (263535951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 76833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 76833) = 1/(76833 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-263535951 / 1000000000) (-5270719 / 20000000) (Real.log (76833 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (208638053 / 1000000000) ≤ -Real.log (1000000 / 1231999) ∧
    -Real.log (1000000 / 1231999) ≤ (104319027 / 500000000) := by
  have h := checkLog_sound (w := (231999 / 2231999)) (n := 12)
    (lo := (208638053 / 1000000000)) (hi := (104319027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1231999 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1231999 / 1000000) = 1/(1000000 / 1231999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (208638053 / 1000000000) (104319027 / 500000000) (Real.log (1231999 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1231999 / 1000000) = -Real.log (1000000 / 1231999) := by
    rw [show ((1231999 / 1000000) : ℝ) = ((1000000 / 1231999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (263964243 / 1000000000) ≤ -Real.log (768001 / 1000000) ∧
    -Real.log (768001 / 1000000) ≤ (65991061 / 250000000) := by
  have h := checkLog_sound (w := (231999 / 1768001)) (n := 12)
    (lo := (263964243 / 1000000000)) (hi := (65991061 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 768001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 768001) = 1/(768001 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-65991061 / 250000000) (-263964243 / 1000000000) (Real.log (768001 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (659809081 / 1000000000) ≤ -Real.log (156250000 / 302253591) ∧
    -Real.log (156250000 / 302253591) ≤ (329904541 / 500000000) := by
  have h := checkLog_sound (w := (146003591 / 458503591)) (n := 12)
    (lo := (659809081 / 1000000000)) (hi := (329904541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302253591 / 156250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302253591 / 156250000) = 1/(156250000 / 302253591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (659809081 / 1000000000) (329904541 / 500000000) (Real.log (302253591 / 156250000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (302253591 / 156250000) = -Real.log (156250000 / 302253591) := by
    rw [show ((302253591 / 156250000) : ℝ) = ((156250000 / 302253591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (660759593 / 1000000000) ≤ -Real.log (500000000000 / 968131274427) ∧
    -Real.log (500000000000 / 968131274427) ≤ (330379797 / 500000000) := by
  have h := checkLog_sound (w := (468131274427 / 1468131274427)) (n := 12)
    (lo := (660759593 / 1000000000)) (hi := (330379797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((968131274427 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(968131274427 / 500000000000) = 1/(500000000000 / 968131274427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (660759593 / 1000000000) (330379797 / 500000000) (Real.log (968131274427 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (968131274427 / 500000000000) = -Real.log (500000000000 / 968131274427) := by
    rw [show ((968131274427 / 500000000000) : ℝ) = ((500000000000 / 968131274427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (235953461 / 500000000) ≤ -Real.log (500000000000 / 801524084703) ∧
    -Real.log (500000000000 / 801524084703) ≤ (471906923 / 1000000000) := by
  have h := checkLog_sound (w := (301524084703 / 1301524084703)) (n := 12)
    (lo := (235953461 / 500000000)) (hi := (471906923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((801524084703 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(801524084703 / 500000000000) = 1/(500000000000 / 801524084703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (235953461 / 500000000) (471906923 / 1000000000) (Real.log (801524084703 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (801524084703 / 500000000000) = -Real.log (500000000000 / 801524084703) := by
    rw [show ((801524084703 / 500000000000) : ℝ) = ((500000000000 / 801524084703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (472602297 / 1000000000) ≤ -Real.log (100000000000 / 160416327583) ∧
    -Real.log (100000000000 / 160416327583) ≤ (236301149 / 500000000) := by
  have h := checkLog_sound (w := (60416327583 / 260416327583)) (n := 12)
    (lo := (472602297 / 1000000000)) (hi := (236301149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160416327583 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160416327583 / 100000000000) = 1/(100000000000 / 160416327583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (472602297 / 1000000000) (236301149 / 500000000) (Real.log (160416327583 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (160416327583 / 100000000000) = -Real.log (100000000000 / 160416327583) := by
    rw [show ((160416327583 / 100000000000) : ℝ) = ((100000000000 / 160416327583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0394

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0395Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0395
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (201425027 / 1000000000) ≤ -Real.log (2048 / 2505) ∧
    -Real.log (2048 / 2505) ≤ (50356257 / 250000000) := by
  have h := checkLog_sound (w := (457 / 4553)) (n := 12)
    (lo := (201425027 / 1000000000)) (hi := (50356257 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2505 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2505 / 2048) = 1/(2048 / 2505) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (201425027 / 1000000000) (50356257 / 250000000) (Real.log (2505 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2505 / 2048) = -Real.log (2048 / 2505) := by
    rw [show ((2505 / 2048) : ℝ) = ((2048 / 2505) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (252500957 / 1000000000) ≤ -Real.log (1591 / 2048) ∧
    -Real.log (1591 / 2048) ≤ (126250479 / 500000000) := by
  have h := checkLog_sound (w := (457 / 3639)) (n := 12)
    (lo := (252500957 / 1000000000)) (hi := (126250479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1591) = 1/(1591 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-126250479 / 500000000) (-252500957 / 1000000000) (Real.log (1591 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (201185477 / 1000000000) ≤ -Real.log (5120 / 6261) ∧
    -Real.log (5120 / 6261) ≤ (100592739 / 500000000) := by
  have h := checkLog_sound (w := (1141 / 11381)) (n := 12)
    (lo := (201185477 / 1000000000)) (hi := (100592739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6261 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6261 / 5120) = 1/(5120 / 6261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (201185477 / 1000000000) (100592739 / 500000000) (Real.log (6261 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6261 / 5120) = -Real.log (5120 / 6261) := by
    rw [show ((6261 / 5120) : ℝ) = ((5120 / 6261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (252123907 / 1000000000) ≤ -Real.log (3979 / 5120) ∧
    -Real.log (3979 / 5120) ≤ (63030977 / 250000000) := by
  have h := checkLog_sound (w := (1141 / 9099)) (n := 12)
    (lo := (252123907 / 1000000000)) (hi := (63030977 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3979) = 1/(3979 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-63030977 / 250000000) (-252123907 / 1000000000) (Real.log (3979 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23062563 / 62500000) ≤ -Real.log (1024 / 1481) ∧
    -Real.log (1024 / 1481) ≤ (369001009 / 1000000000) := by
  have h := checkLog_sound (w := (457 / 2505)) (n := 12)
    (lo := (23062563 / 62500000)) (hi := (369001009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1481 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1481 / 1024) = 1/(1024 / 1481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23062563 / 62500000) (369001009 / 1000000000) (Real.log (1481 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1481 / 1024) = -Real.log (1024 / 1481) := by
    rw [show ((1481 / 1024) : ℝ) = ((1024 / 1481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (591112501 / 1000000000) ≤ -Real.log (567 / 1024) ∧
    -Real.log (567 / 1024) ≤ (295556251 / 500000000) := by
  have h := checkLog_sound (w := (457 / 1591)) (n := 12)
    (lo := (591112501 / 1000000000)) (hi := (295556251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 567) = 1/(567 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-295556251 / 500000000) (-591112501 / 1000000000) (Real.log (567 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (184297897 / 500000000) ≤ -Real.log (2560 / 3701) ∧
    -Real.log (2560 / 3701) ≤ (73719159 / 200000000) := by
  have h := checkLog_sound (w := (1141 / 6261)) (n := 12)
    (lo := (184297897 / 500000000)) (hi := (73719159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3701 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3701 / 2560) = 1/(2560 / 3701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (184297897 / 500000000) (73719159 / 200000000) (Real.log (3701 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3701 / 2560) = -Real.log (2560 / 3701) := by
    rw [show ((3701 / 2560) : ℝ) = ((2560 / 3701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (29502743 / 50000000) ≤ -Real.log (1419 / 2560) ∧
    -Real.log (1419 / 2560) ≤ (590054861 / 1000000000) := by
  have h := checkLog_sound (w := (1141 / 3979)) (n := 12)
    (lo := (29502743 / 50000000)) (hi := (590054861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1419) = 1/(1419 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-590054861 / 1000000000) (-29502743 / 50000000) (Real.log (1419 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (34515283 / 125000000) ≤ -Real.log (1000000 / 1318009) ∧
    -Real.log (1000000 / 1318009) ≤ (55224453 / 200000000) := by
  have h := checkLog_sound (w := (318009 / 2318009)) (n := 12)
    (lo := (34515283 / 125000000)) (hi := (55224453 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1318009 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1318009 / 1000000) = 1/(1000000 / 1318009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (34515283 / 125000000) (55224453 / 200000000) (Real.log (1318009 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1318009 / 1000000) = -Real.log (1000000 / 1318009) := by
    rw [show ((1318009 / 1000000) : ℝ) = ((1000000 / 1318009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (382738817 / 1000000000) ≤ -Real.log (681991 / 1000000) ∧
    -Real.log (681991 / 1000000) ≤ (191369409 / 500000000) := by
  have h := checkLog_sound (w := (318009 / 1681991)) (n := 12)
    (lo := (382738817 / 1000000000)) (hi := (191369409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 681991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 681991) = 1/(681991 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-191369409 / 500000000) (-382738817 / 1000000000) (Real.log (681991 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (55289237 / 200000000) ≤ -Real.log (250000 / 329609) ∧
    -Real.log (250000 / 329609) ≤ (138223093 / 500000000) := by
  have h := checkLog_sound (w := (79609 / 579609)) (n := 12)
    (lo := (55289237 / 200000000)) (hi := (138223093 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329609 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329609 / 250000) = 1/(250000 / 329609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (55289237 / 200000000) (138223093 / 500000000) (Real.log (329609 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (329609 / 250000) = -Real.log (250000 / 329609) := by
    rw [show ((329609 / 250000) : ℝ) = ((250000 / 329609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (383365121 / 1000000000) ≤ -Real.log (170391 / 250000) ∧
    -Real.log (170391 / 250000) ≤ (191682561 / 500000000) := by
  have h := checkLog_sound (w := (79609 / 420391)) (n := 12)
    (lo := (383365121 / 1000000000)) (hi := (191682561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 170391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 170391) = 1/(170391 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-191682561 / 500000000) (-383365121 / 1000000000) (Real.log (170391 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (208104631 / 1000000000) ≤ -Real.log (500000 / 615671) ∧
    -Real.log (500000 / 615671) ≤ (26013079 / 125000000) := by
  have h := checkLog_sound (w := (115671 / 1115671)) (n := 12)
    (lo := (208104631 / 1000000000)) (hi := (26013079 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((615671 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(615671 / 500000) = 1/(500000 / 615671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (208104631 / 1000000000) (26013079 / 125000000) (Real.log (615671 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (615671 / 500000) = -Real.log (500000 / 615671) := by
    rw [show ((615671 / 500000) : ℝ) = ((500000 / 615671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (263109141 / 1000000000) ≤ -Real.log (384329 / 500000) ∧
    -Real.log (384329 / 500000) ≤ (131554571 / 500000000) := by
  have h := checkLog_sound (w := (115671 / 884329)) (n := 12)
    (lo := (263109141 / 1000000000)) (hi := (131554571 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 384329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 384329) = 1/(384329 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-131554571 / 500000000) (-263109141 / 1000000000) (Real.log (384329 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (208371783 / 1000000000) ≤ -Real.log (1000000 / 1231671) ∧
    -Real.log (1000000 / 1231671) ≤ (26046473 / 125000000) := by
  have h := checkLog_sound (w := (231671 / 2231671)) (n := 12)
    (lo := (208371783 / 1000000000)) (hi := (26046473 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1231671 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1231671 / 1000000) = 1/(1000000 / 1231671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (208371783 / 1000000000) (26046473 / 125000000) (Real.log (1231671 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1231671 / 1000000) = -Real.log (1000000 / 1231671) := by
    rw [show ((1231671 / 1000000) : ℝ) = ((1000000 / 1231671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (65884313 / 250000000) ≤ -Real.log (768329 / 1000000) ∧
    -Real.log (768329 / 1000000) ≤ (263537253 / 1000000000) := by
  have h := checkLog_sound (w := (231671 / 1768329)) (n := 12)
    (lo := (65884313 / 250000000)) (hi := (263537253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 768329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 768329) = 1/(768329 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-263537253 / 1000000000) (-65884313 / 250000000) (Real.log (768329 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (329430541 / 500000000) ≤ -Real.log (250000000000 / 483147504879) ∧
    -Real.log (250000000000 / 483147504879) ≤ (658861083 / 1000000000) := by
  have h := checkLog_sound (w := (233147504879 / 733147504879)) (n := 12)
    (lo := (329430541 / 500000000)) (hi := (658861083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((483147504879 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(483147504879 / 250000000000) = 1/(250000000000 / 483147504879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (329430541 / 500000000) (658861083 / 1000000000) (Real.log (483147504879 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (483147504879 / 250000000000) = -Real.log (250000000000 / 483147504879) := by
    rw [show ((483147504879 / 250000000000) : ℝ) = ((250000000000 / 483147504879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (659811307 / 1000000000) ≤ -Real.log (250000000000 / 483606821957) ∧
    -Real.log (250000000000 / 483606821957) ≤ (164952827 / 250000000) := by
  have h := checkLog_sound (w := (233606821957 / 733606821957)) (n := 12)
    (lo := (659811307 / 1000000000)) (hi := (164952827 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((483606821957 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(483606821957 / 250000000000) = 1/(250000000000 / 483606821957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (659811307 / 1000000000) (164952827 / 250000000) (Real.log (483606821957 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (483606821957 / 250000000000) = -Real.log (250000000000 / 483606821957) := by
    rw [show ((483606821957 / 250000000000) : ℝ) = ((250000000000 / 483606821957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (471213773 / 1000000000) ≤ -Real.log (250000000000 / 400484350647) ∧
    -Real.log (250000000000 / 400484350647) ≤ (235606887 / 500000000) := by
  have h := checkLog_sound (w := (150484350647 / 650484350647)) (n := 12)
    (lo := (471213773 / 1000000000)) (hi := (235606887 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400484350647 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400484350647 / 250000000000) = 1/(250000000000 / 400484350647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (471213773 / 1000000000) (235606887 / 500000000) (Real.log (400484350647 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (400484350647 / 250000000000) = -Real.log (250000000000 / 400484350647) := by
    rw [show ((400484350647 / 250000000000) : ℝ) = ((250000000000 / 400484350647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (117977259 / 250000000) ≤ -Real.log (500000000000 / 801525778671) ∧
    -Real.log (500000000000 / 801525778671) ≤ (471909037 / 1000000000) := by
  have h := checkLog_sound (w := (301525778671 / 1301525778671)) (n := 12)
    (lo := (117977259 / 250000000)) (hi := (471909037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((801525778671 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(801525778671 / 500000000000) = 1/(500000000000 / 801525778671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (117977259 / 250000000) (471909037 / 1000000000) (Real.log (801525778671 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (801525778671 / 500000000000) = -Real.log (500000000000 / 801525778671) := by
    rw [show ((801525778671 / 500000000000) : ℝ) = ((500000000000 / 801525778671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0395

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0396Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0396
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (201185477 / 1000000000) ≤ -Real.log (5120 / 6261) ∧
    -Real.log (5120 / 6261) ≤ (100592739 / 500000000) := by
  have h := checkLog_sound (w := (1141 / 11381)) (n := 12)
    (lo := (201185477 / 1000000000)) (hi := (100592739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6261 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6261 / 5120) = 1/(5120 / 6261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (201185477 / 1000000000) (100592739 / 500000000) (Real.log (6261 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6261 / 5120) = -Real.log (5120 / 6261) := by
    rw [show ((6261 / 5120) : ℝ) = ((5120 / 6261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (252123907 / 1000000000) ≤ -Real.log (3979 / 5120) ∧
    -Real.log (3979 / 5120) ≤ (63030977 / 250000000) := by
  have h := checkLog_sound (w := (1141 / 9099)) (n := 12)
    (lo := (252123907 / 1000000000)) (hi := (63030977 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3979) = 1/(3979 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-63030977 / 250000000) (-252123907 / 1000000000) (Real.log (3979 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (20094587 / 100000000) ≤ -Real.log (10240 / 12519) ∧
    -Real.log (10240 / 12519) ≤ (200945871 / 1000000000) := by
  have h := checkLog_sound (w := (2279 / 22759)) (n := 12)
    (lo := (20094587 / 100000000)) (hi := (200945871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12519 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12519 / 10240) = 1/(10240 / 12519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (20094587 / 100000000) (200945871 / 1000000000) (Real.log (12519 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12519 / 10240) = -Real.log (10240 / 12519) := by
    rw [show ((12519 / 10240) : ℝ) = ((10240 / 12519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (251746999 / 1000000000) ≤ -Real.log (7961 / 10240) ∧
    -Real.log (7961 / 10240) ≤ (251747 / 1000000) := by
  have h := checkLog_sound (w := (2279 / 18201)) (n := 12)
    (lo := (251746999 / 1000000000)) (hi := (251747 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7961) = 1/(7961 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-251747 / 1000000) (-251746999 / 1000000000) (Real.log (7961 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (184297897 / 500000000) ≤ -Real.log (2560 / 3701) ∧
    -Real.log (2560 / 3701) ≤ (73719159 / 200000000) := by
  have h := checkLog_sound (w := (1141 / 6261)) (n := 12)
    (lo := (184297897 / 500000000)) (hi := (73719159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3701 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3701 / 2560) = 1/(2560 / 3701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (184297897 / 500000000) (73719159 / 200000000) (Real.log (3701 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3701 / 2560) = -Real.log (2560 / 3701) := by
    rw [show ((3701 / 2560) : ℝ) = ((2560 / 3701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (29502743 / 50000000) ≤ -Real.log (1419 / 2560) ∧
    -Real.log (1419 / 2560) ≤ (590054861 / 1000000000) := by
  have h := checkLog_sound (w := (1141 / 3979)) (n := 12)
    (lo := (29502743 / 50000000)) (hi := (590054861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1419) = 1/(1419 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-590054861 / 1000000000) (-29502743 / 50000000) (Real.log (1419 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23011901 / 62500000) ≤ -Real.log (5120 / 7399) ∧
    -Real.log (5120 / 7399) ≤ (368190417 / 1000000000) := by
  have h := checkLog_sound (w := (2279 / 12519)) (n := 12)
    (lo := (23011901 / 62500000)) (hi := (368190417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7399 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7399 / 5120) = 1/(5120 / 7399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23011901 / 62500000) (368190417 / 1000000000) (Real.log (7399 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7399 / 5120) = -Real.log (5120 / 7399) := by
    rw [show ((7399 / 5120) : ℝ) = ((5120 / 7399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (9203099 / 15625000) ≤ -Real.log (2841 / 5120) ∧
    -Real.log (2841 / 5120) ≤ (588998337 / 1000000000) := by
  have h := checkLog_sound (w := (2279 / 7961)) (n := 12)
    (lo := (9203099 / 15625000)) (hi := (588998337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2841) = 1/(2841 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-588998337 / 1000000000) (-9203099 / 15625000) (Real.log (2841 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (137899119 / 500000000) ≤ -Real.log (500000 / 658791) ∧
    -Real.log (500000 / 658791) ≤ (275798239 / 1000000000) := by
  have h := checkLog_sound (w := (158791 / 1158791)) (n := 12)
    (lo := (137899119 / 500000000)) (hi := (275798239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((658791 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(658791 / 500000) = 1/(500000 / 658791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (137899119 / 500000000) (275798239 / 1000000000) (Real.log (658791 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (658791 / 500000) = -Real.log (500000 / 658791) := by
    rw [show ((658791 / 500000) : ℝ) = ((500000 / 658791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (76422581 / 200000000) ≤ -Real.log (341209 / 500000) ∧
    -Real.log (341209 / 500000) ≤ (191056453 / 500000000) := by
  have h := checkLog_sound (w := (158791 / 841209)) (n := 12)
    (lo := (76422581 / 200000000)) (hi := (191056453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 341209) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 341209) = 1/(341209 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-191056453 / 500000000) (-76422581 / 200000000) (Real.log (341209 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (276123023 / 1000000000) ≤ -Real.log (100000 / 131801) ∧
    -Real.log (100000 / 131801) ≤ (17257689 / 62500000) := by
  have h := checkLog_sound (w := (31801 / 231801)) (n := 12)
    (lo := (276123023 / 1000000000)) (hi := (17257689 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131801 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(131801 / 100000) = 1/(100000 / 131801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (276123023 / 1000000000) (17257689 / 62500000) (Real.log (131801 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (131801 / 100000) = -Real.log (100000 / 131801) := by
    rw [show ((131801 / 100000) : ℝ) = ((100000 / 131801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (95685071 / 250000000) ≤ -Real.log (68199 / 100000) ∧
    -Real.log (68199 / 100000) ≤ (76548057 / 200000000) := by
  have h := checkLog_sound (w := (31801 / 168199)) (n := 12)
    (lo := (95685071 / 250000000)) (hi := (76548057 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 68199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 68199) = 1/(68199 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-76548057 / 200000000) (-95685071 / 250000000) (Real.log (68199 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (10391911 / 50000000) ≤ -Real.log (500000 / 615507) ∧
    -Real.log (500000 / 615507) ≤ (207838221 / 1000000000) := by
  have h := checkLog_sound (w := (115507 / 1115507)) (n := 12)
    (lo := (10391911 / 50000000)) (hi := (207838221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((615507 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(615507 / 500000) = 1/(500000 / 615507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (10391911 / 50000000) (207838221 / 1000000000) (Real.log (615507 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (615507 / 500000) = -Real.log (500000 / 615507) := by
    rw [show ((615507 / 500000) : ℝ) = ((500000 / 615507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (52536503 / 200000000) ≤ -Real.log (384493 / 500000) ∧
    -Real.log (384493 / 500000) ≤ (65670629 / 250000000) := by
  have h := checkLog_sound (w := (115507 / 884493)) (n := 12)
    (lo := (52536503 / 200000000)) (hi := (65670629 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 384493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 384493) = 1/(384493 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-65670629 / 250000000) (-52536503 / 200000000) (Real.log (384493 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (208105443 / 1000000000) ≤ -Real.log (1000000 / 1231343) ∧
    -Real.log (1000000 / 1231343) ≤ (52026361 / 250000000) := by
  have h := checkLog_sound (w := (231343 / 2231343)) (n := 12)
    (lo := (208105443 / 1000000000)) (hi := (52026361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1231343 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1231343 / 1000000) = 1/(1000000 / 1231343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (208105443 / 1000000000) (52026361 / 250000000) (Real.log (1231343 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1231343 / 1000000) = -Real.log (1000000 / 1231343) := by
    rw [show ((1231343 / 1000000) : ℝ) = ((1000000 / 1231343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (131555221 / 500000000) ≤ -Real.log (768657 / 1000000) ∧
    -Real.log (768657 / 1000000) ≤ (263110443 / 1000000000) := by
  have h := checkLog_sound (w := (231343 / 1768657)) (n := 12)
    (lo := (131555221 / 500000000)) (hi := (263110443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 768657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 768657) = 1/(768657 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-263110443 / 1000000000) (-131555221 / 500000000) (Real.log (768657 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (82238893 / 125000000) ≤ -Real.log (500000000000 / 965377525211) ∧
    -Real.log (500000000000 / 965377525211) ≤ (131582229 / 200000000) := by
  have h := checkLog_sound (w := (465377525211 / 1465377525211)) (n := 12)
    (lo := (82238893 / 125000000)) (hi := (131582229 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((965377525211 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(965377525211 / 500000000000) = 1/(500000000000 / 965377525211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (82238893 / 125000000) (131582229 / 200000000) (Real.log (965377525211 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (965377525211 / 500000000000) = -Real.log (500000000000 / 965377525211) := by
    rw [show ((965377525211 / 500000000000) : ℝ) = ((500000000000 / 965377525211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (658863307 / 1000000000) ≤ -Real.log (500000000000 / 966297159783) ∧
    -Real.log (500000000000 / 966297159783) ≤ (164715827 / 250000000) := by
  have h := checkLog_sound (w := (466297159783 / 1466297159783)) (n := 12)
    (lo := (658863307 / 1000000000)) (hi := (164715827 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((966297159783 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(966297159783 / 500000000000) = 1/(500000000000 / 966297159783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (658863307 / 1000000000) (164715827 / 250000000) (Real.log (966297159783 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (966297159783 / 500000000000) = -Real.log (500000000000 / 966297159783) := by
    rw [show ((966297159783 / 500000000000) : ℝ) = ((500000000000 / 966297159783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (94104147 / 200000000) ≤ -Real.log (125000000000 / 200103447917) ∧
    -Real.log (125000000000 / 200103447917) ≤ (14703773 / 31250000) := by
  have h := checkLog_sound (w := (75103447917 / 325103447917)) (n := 12)
    (lo := (94104147 / 200000000)) (hi := (14703773 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200103447917 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200103447917 / 125000000000) = 1/(125000000000 / 200103447917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (94104147 / 200000000) (14703773 / 31250000) (Real.log (200103447917 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (200103447917 / 125000000000) = -Real.log (125000000000 / 200103447917) := by
    rw [show ((200103447917 / 125000000000) : ℝ) = ((125000000000 / 200103447917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (235607943 / 500000000) ≤ -Real.log (500000000000 / 800970393817) ∧
    -Real.log (500000000000 / 800970393817) ≤ (471215887 / 1000000000) := by
  have h := checkLog_sound (w := (300970393817 / 1300970393817)) (n := 12)
    (lo := (235607943 / 500000000)) (hi := (471215887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800970393817 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800970393817 / 500000000000) = 1/(500000000000 / 800970393817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (235607943 / 500000000) (471215887 / 1000000000) (Real.log (800970393817 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (800970393817 / 500000000000) = -Real.log (500000000000 / 800970393817) := by
    rw [show ((800970393817 / 500000000000) : ℝ) = ((500000000000 / 800970393817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0396

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0397Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0397
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (20094587 / 100000000) ≤ -Real.log (10240 / 12519) ∧
    -Real.log (10240 / 12519) ≤ (200945871 / 1000000000) := by
  have h := checkLog_sound (w := (2279 / 22759)) (n := 12)
    (lo := (20094587 / 100000000)) (hi := (200945871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12519 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12519 / 10240) = 1/(10240 / 12519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (20094587 / 100000000) (200945871 / 1000000000) (Real.log (12519 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12519 / 10240) = -Real.log (10240 / 12519) := by
    rw [show ((12519 / 10240) : ℝ) = ((10240 / 12519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (251746999 / 1000000000) ≤ -Real.log (7961 / 10240) ∧
    -Real.log (7961 / 10240) ≤ (251747 / 1000000) := by
  have h := checkLog_sound (w := (2279 / 18201)) (n := 12)
    (lo := (251746999 / 1000000000)) (hi := (251747 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7961) = 1/(7961 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-251747 / 1000000) (-251746999 / 1000000000) (Real.log (7961 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (100353103 / 500000000) ≤ -Real.log (2560 / 3129) ∧
    -Real.log (2560 / 3129) ≤ (200706207 / 1000000000) := by
  have h := checkLog_sound (w := (569 / 5689)) (n := 12)
    (lo := (100353103 / 500000000)) (hi := (200706207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3129 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3129 / 2560) = 1/(2560 / 3129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (100353103 / 500000000) (200706207 / 1000000000) (Real.log (3129 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3129 / 2560) = -Real.log (2560 / 3129) := by
    rw [show ((3129 / 2560) : ℝ) = ((2560 / 3129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (251370233 / 1000000000) ≤ -Real.log (1991 / 2560) ∧
    -Real.log (1991 / 2560) ≤ (125685117 / 500000000) := by
  have h := checkLog_sound (w := (569 / 4551)) (n := 12)
    (lo := (251370233 / 1000000000)) (hi := (125685117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1991) = 1/(1991 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-125685117 / 500000000) (-251370233 / 1000000000) (Real.log (1991 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23011901 / 62500000) ≤ -Real.log (5120 / 7399) ∧
    -Real.log (5120 / 7399) ≤ (368190417 / 1000000000) := by
  have h := checkLog_sound (w := (2279 / 12519)) (n := 12)
    (lo := (23011901 / 62500000)) (hi := (368190417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7399 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7399 / 5120) = 1/(5120 / 7399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23011901 / 62500000) (368190417 / 1000000000) (Real.log (7399 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7399 / 5120) = -Real.log (5120 / 7399) := by
    rw [show ((7399 / 5120) : ℝ) = ((5120 / 7399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (9203099 / 15625000) ≤ -Real.log (2841 / 5120) ∧
    -Real.log (2841 / 5120) ≤ (588998337 / 1000000000) := by
  have h := checkLog_sound (w := (2279 / 7961)) (n := 12)
    (lo := (9203099 / 15625000)) (hi := (588998337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2841) = 1/(2841 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-588998337 / 1000000000) (-9203099 / 15625000) (Real.log (2841 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (183892437 / 500000000) ≤ -Real.log (1280 / 1849) ∧
    -Real.log (1280 / 1849) ≤ (2942279 / 8000000) := by
  have h := checkLog_sound (w := (569 / 3129)) (n := 12)
    (lo := (183892437 / 500000000)) (hi := (2942279 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1849 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1849 / 1280) = 1/(1280 / 1849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (183892437 / 500000000) (2942279 / 8000000) (Real.log (1849 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1849 / 1280) = -Real.log (1280 / 1849) := by
    rw [show ((1849 / 1280) : ℝ) = ((1280 / 1849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (587942927 / 1000000000) ≤ -Real.log (711 / 1280) ∧
    -Real.log (711 / 1280) ≤ (36746433 / 62500000) := by
  have h := checkLog_sound (w := (569 / 1991)) (n := 12)
    (lo := (587942927 / 1000000000)) (hi := (36746433 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 711) = 1/(711 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-36746433 / 62500000) (-587942927 / 1000000000) (Real.log (711 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (137737433 / 500000000) ≤ -Real.log (250000 / 329289) ∧
    -Real.log (250000 / 329289) ≤ (275474867 / 1000000000) := by
  have h := checkLog_sound (w := (79289 / 579289)) (n := 12)
    (lo := (137737433 / 500000000)) (hi := (275474867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329289 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329289 / 250000) = 1/(250000 / 329289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (137737433 / 500000000) (275474867 / 1000000000) (Real.log (329289 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (329289 / 250000) = -Real.log (250000 / 329289) := by
    rw [show ((329289 / 250000) : ℝ) = ((250000 / 329289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (381488849 / 1000000000) ≤ -Real.log (170711 / 250000) ∧
    -Real.log (170711 / 250000) ≤ (7629777 / 20000000) := by
  have h := checkLog_sound (w := (79289 / 420711)) (n := 12)
    (lo := (381488849 / 1000000000)) (hi := (7629777 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 170711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 170711) = 1/(170711 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-7629777 / 20000000) (-381488849 / 1000000000) (Real.log (170711 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (275798997 / 1000000000) ≤ -Real.log (1000000 / 1317583) ∧
    -Real.log (1000000 / 1317583) ≤ (137899499 / 500000000) := by
  have h := checkLog_sound (w := (317583 / 2317583)) (n := 12)
    (lo := (275798997 / 1000000000)) (hi := (137899499 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1317583 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1317583 / 1000000) = 1/(1000000 / 1317583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (275798997 / 1000000000) (137899499 / 500000000) (Real.log (1317583 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1317583 / 1000000) = -Real.log (1000000 / 1317583) := by
    rw [show ((1317583 / 1000000) : ℝ) = ((1000000 / 1317583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (382114371 / 1000000000) ≤ -Real.log (682417 / 1000000) ∧
    -Real.log (682417 / 1000000) ≤ (95528593 / 250000000) := by
  have h := checkLog_sound (w := (317583 / 1682417)) (n := 12)
    (lo := (382114371 / 1000000000)) (hi := (95528593 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 682417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 682417) = 1/(682417 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-95528593 / 250000000) (-382114371 / 1000000000) (Real.log (682417 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (4151451 / 20000000) ≤ -Real.log (1000000 / 1230687) ∧
    -Real.log (1000000 / 1230687) ≤ (207572551 / 1000000000) := by
  have h := checkLog_sound (w := (230687 / 2230687)) (n := 12)
    (lo := (4151451 / 20000000)) (hi := (207572551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1230687 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1230687 / 1000000) = 1/(1000000 / 1230687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (4151451 / 20000000) (207572551 / 1000000000) (Real.log (1230687 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1230687 / 1000000) = -Real.log (1000000 / 1230687) := by
    rw [show ((1230687 / 1000000) : ℝ) = ((1000000 / 1230687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (26225737 / 100000000) ≤ -Real.log (769313 / 1000000) ∧
    -Real.log (769313 / 1000000) ≤ (262257371 / 1000000000) := by
  have h := checkLog_sound (w := (230687 / 1769313)) (n := 12)
    (lo := (26225737 / 100000000)) (hi := (262257371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 769313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 769313) = 1/(769313 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-262257371 / 1000000000) (-26225737 / 100000000) (Real.log (769313 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (25979879 / 125000000) ≤ -Real.log (200000 / 246203) ∧
    -Real.log (200000 / 246203) ≤ (207839033 / 1000000000) := by
  have h := checkLog_sound (w := (46203 / 446203)) (n := 12)
    (lo := (25979879 / 125000000)) (hi := (207839033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246203 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246203 / 200000) = 1/(200000 / 246203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (25979879 / 125000000) (207839033 / 1000000000) (Real.log (246203 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (246203 / 200000) = -Real.log (200000 / 246203) := by
    rw [show ((246203 / 200000) : ℝ) = ((200000 / 246203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (52536763 / 200000000) ≤ -Real.log (153797 / 200000) ∧
    -Real.log (153797 / 200000) ≤ (32835477 / 125000000) := by
  have h := checkLog_sound (w := (46203 / 353797)) (n := 12)
    (lo := (52536763 / 200000000)) (hi := (32835477 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 153797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 153797) = 1/(153797 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-32835477 / 125000000) (-52536763 / 200000000) (Real.log (153797 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (164240929 / 250000000) ≤ -Real.log (500000000000 / 964463332767) ∧
    -Real.log (500000000000 / 964463332767) ≤ (656963717 / 1000000000) := by
  have h := checkLog_sound (w := (464463332767 / 1464463332767)) (n := 12)
    (lo := (164240929 / 250000000)) (hi := (656963717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((964463332767 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(964463332767 / 500000000000) = 1/(500000000000 / 964463332767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (164240929 / 250000000) (656963717 / 1000000000) (Real.log (964463332767 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (964463332767 / 500000000000) = -Real.log (500000000000 / 964463332767) := by
    rw [show ((964463332767 / 500000000000) : ℝ) = ((500000000000 / 964463332767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (82239171 / 125000000) ≤ -Real.log (500000000000 / 965379672547) ∧
    -Real.log (500000000000 / 965379672547) ≤ (657913369 / 1000000000) := by
  have h := checkLog_sound (w := (465379672547 / 1465379672547)) (n := 12)
    (lo := (82239171 / 125000000)) (hi := (657913369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((965379672547 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(965379672547 / 500000000000) = 1/(500000000000 / 965379672547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (82239171 / 125000000) (657913369 / 1000000000) (Real.log (965379672547 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (965379672547 / 500000000000) = -Real.log (500000000000 / 965379672547) := by
    rw [show ((965379672547 / 500000000000) : ℝ) = ((500000000000 / 965379672547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2936437 / 6250000) ≤ -Real.log (250000000000 / 399930522427) ∧
    -Real.log (250000000000 / 399930522427) ≤ (469829921 / 1000000000) := by
  have h := checkLog_sound (w := (149930522427 / 649930522427)) (n := 12)
    (lo := (2936437 / 6250000)) (hi := (469829921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399930522427 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399930522427 / 250000000000) = 1/(250000000000 / 399930522427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2936437 / 6250000) (469829921 / 1000000000) (Real.log (399930522427 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (399930522427 / 250000000000) = -Real.log (250000000000 / 399930522427) := by
    rw [show ((399930522427 / 250000000000) : ℝ) = ((250000000000 / 399930522427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (470522847 / 1000000000) ≤ -Real.log (500000000000 / 800415482747) ∧
    -Real.log (500000000000 / 800415482747) ≤ (14703839 / 31250000) := by
  have h := checkLog_sound (w := (300415482747 / 1300415482747)) (n := 12)
    (lo := (470522847 / 1000000000)) (hi := (14703839 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800415482747 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800415482747 / 500000000000) = 1/(500000000000 / 800415482747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (470522847 / 1000000000) (14703839 / 31250000) (Real.log (800415482747 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (800415482747 / 500000000000) = -Real.log (500000000000 / 800415482747) := by
    rw [show ((800415482747 / 500000000000) : ℝ) = ((500000000000 / 800415482747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0397

end


