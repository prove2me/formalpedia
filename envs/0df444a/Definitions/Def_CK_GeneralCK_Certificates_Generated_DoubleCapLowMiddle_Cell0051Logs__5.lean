-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0051Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0051Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:01:08.782978+00:00
-- url     : https://prove2.me/theorems/d26b979a-0e4f-4a5d-a2a5-d99a5660897c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0051Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0052Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0051Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0052Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0053Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0054Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0055Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0051Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0052Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0053Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0054Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0055Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0051Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0052Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0053Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0054Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0055Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0051Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0052Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0053Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0054Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0055Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0051Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0051
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

theorem reflection_log_1_neg : (10608829 / 15625000) ≤ -Real.log (25600 / 50479) ∧
    -Real.log (25600 / 50479) ≤ (678965057 / 1000000000) := by
  have h := checkLog_sound (w := (24879 / 76079)) (n := 12)
    (lo := (10608829 / 15625000)) (hi := (678965057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50479 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50479 / 25600) = 1/(25600 / 50479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (10608829 / 15625000) (678965057 / 1000000000) (Real.log (50479 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50479 / 25600) = -Real.log (25600 / 50479) := by
    rw [show ((50479 / 25600) : ℝ) = ((25600 / 50479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (356970849 / 100000000) ≤ -Real.log (721 / 25600) ∧
    -Real.log (721 / 25600) ≤ (223106781 / 62500000) := by
  have h := checkLog_sound (w := (79 / 1521)) (n := 12)
    (lo := (10397259 / 100000000)) (hi := (103972591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 721) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 721) = 1/(721 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-223106781 / 62500000) (-356970849 / 100000000) (Real.log (721 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (678870953 / 1000000000) ≤ -Real.log (102400 / 201897) ∧
    -Real.log (102400 / 201897) ≤ (339435477 / 500000000) := by
  have h := checkLog_sound (w := (99497 / 304297)) (n := 12)
    (lo := (678870953 / 1000000000)) (hi := (339435477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201897 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201897 / 102400) = 1/(102400 / 201897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (678870953 / 1000000000) (339435477 / 500000000) (Real.log (201897 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (201897 / 102400) = -Real.log (102400 / 201897) := by
    rw [show ((201897 / 102400) : ℝ) = ((102400 / 201897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (445392753 / 125000000) ≤ -Real.log (2903 / 102400) ∧
    -Real.log (2903 / 102400) ≤ (356314203 / 100000000) := by
  have h := checkLog_sound (w := (297 / 6103)) (n := 12)
    (lo := (24351531 / 250000000)) (hi := (779249 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2903) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2903) = 1/(2903 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-356314203 / 100000000) (-445392753 / 125000000) (Real.log (2903 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (664578903 / 1000000000) ≤ -Real.log (12800 / 24879) ∧
    -Real.log (12800 / 24879) ≤ (83072363 / 125000000) := by
  have h := checkLog_sound (w := (12079 / 37679)) (n := 12)
    (lo := (664578903 / 1000000000)) (hi := (83072363 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24879 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24879 / 12800) = 1/(12800 / 24879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (664578903 / 1000000000) (83072363 / 125000000) (Real.log (24879 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24879 / 12800) = -Real.log (12800 / 24879) := by
    rw [show ((24879 / 12800) : ℝ) = ((12800 / 24879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (287656131 / 100000000) ≤ -Real.log (721 / 12800) ∧
    -Real.log (721 / 12800) ≤ (575312263 / 200000000) := by
  have h := checkLog_sound (w := (79 / 1521)) (n := 12)
    (lo := (10397259 / 100000000)) (hi := (103972591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 721) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 721) = 1/(721 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-575312263 / 200000000) (-287656131 / 100000000) (Real.log (721 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (16609699 / 25000000) ≤ -Real.log (51200 / 99497) ∧
    -Real.log (51200 / 99497) ≤ (664387961 / 1000000000) := by
  have h := checkLog_sound (w := (48297 / 150697)) (n := 12)
    (lo := (16609699 / 25000000)) (hi := (664387961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99497 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99497 / 51200) = 1/(51200 / 99497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (16609699 / 25000000) (664387961 / 1000000000) (Real.log (99497 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99497 / 51200) = -Real.log (51200 / 99497) := by
    rw [show ((99497 / 51200) : ℝ) = ((51200 / 99497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (717498711 / 250000000) ≤ -Real.log (2903 / 51200) ∧
    -Real.log (2903 / 51200) ≤ (2869994849 / 1000000000) := by
  have h := checkLog_sound (w := (297 / 6103)) (n := 12)
    (lo := (24351531 / 250000000)) (hi := (779249 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2903) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2903) = 1/(2903 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2869994849 / 1000000000) (-717498711 / 250000000) (Real.log (2903 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (27247761 / 40000000) ≤ -Real.log (250000 / 494059) ∧
    -Real.log (250000 / 494059) ≤ (340597013 / 500000000) := by
  have h := checkLog_sound (w := (244059 / 744059)) (n := 12)
    (lo := (27247761 / 40000000)) (hi := (340597013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494059 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494059 / 250000) = 1/(250000 / 494059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (27247761 / 40000000) (340597013 / 500000000) (Real.log (494059 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (494059 / 250000) = -Real.log (250000 / 494059) := by
    rw [show ((494059 / 250000) : ℝ) = ((250000 / 494059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (747916689 / 200000000) ≤ -Real.log (5941 / 250000) ∧
    -Real.log (5941 / 250000) ≤ (3739583451 / 1000000000) := by
  have h := checkLog_sound (w := (3743 / 27507)) (n := 12)
    (lo := (54769509 / 200000000)) (hi := (136923773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11882) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11882) = 1/(5941 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3739583451 / 1000000000) (-747916689 / 200000000) (Real.log (5941 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (170317481 / 250000000) ≤ -Real.log (500000 / 988193) ∧
    -Real.log (500000 / 988193) ≤ (27250797 / 40000000) := by
  have h := checkLog_sound (w := (488193 / 1488193)) (n := 12)
    (lo := (170317481 / 250000000)) (hi := (27250797 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988193 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(988193 / 500000) = 1/(500000 / 988193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (170317481 / 250000000) (27250797 / 40000000) (Real.log (988193 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (988193 / 500000) = -Real.log (500000 / 988193) := by
    rw [show ((988193 / 500000) : ℝ) = ((500000 / 988193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3745915519 / 1000000000) ≤ -Real.log (11807 / 500000) ∧
    -Real.log (11807 / 500000) ≤ (149836621 / 40000000) := by
  have h := checkLog_sound (w := (1909 / 13716)) (n := 12)
    (lo := (280179619 / 1000000000)) (hi := (14008981 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11807) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11807) = 1/(11807 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-149836621 / 40000000) (-3745915519 / 1000000000) (Real.log (11807 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (681126723 / 1000000000) ≤ -Real.log (1000000 / 1976103) ∧
    -Real.log (1000000 / 1976103) ≤ (170281681 / 250000000) := by
  have h := checkLog_sound (w := (976103 / 2976103)) (n := 12)
    (lo := (681126723 / 1000000000)) (hi := (170281681 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1976103 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1976103 / 1000000) = 1/(1000000 / 1976103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (681126723 / 1000000000) (170281681 / 250000000) (Real.log (1976103 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1976103 / 1000000) = -Real.log (1000000 / 1976103) := by
    rw [show ((1976103 / 1000000) : ℝ) = ((1000000 / 1976103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (933500587 / 250000000) ≤ -Real.log (23897 / 1000000) ∧
    -Real.log (23897 / 1000000) ≤ (1867001177 / 500000000) := by
  have h := checkLog_sound (w := (7353 / 55147)) (n := 12)
    (lo := (16766653 / 62500000)) (hi := (268266449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23897) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 23897) = 1/(23897 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1867001177 / 500000000) (-933500587 / 250000000) (Real.log (23897 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (681203133 / 1000000000) ≤ -Real.log (500000 / 988127) ∧
    -Real.log (500000 / 988127) ≤ (340601567 / 500000000) := by
  have h := checkLog_sound (w := (488127 / 1488127)) (n := 12)
    (lo := (681203133 / 1000000000)) (hi := (340601567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988127 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(988127 / 500000) = 1/(500000 / 988127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (681203133 / 1000000000) (340601567 / 500000000) (Real.log (988127 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (988127 / 500000) = -Real.log (500000 / 988127) := by
    rw [show ((988127 / 500000) : ℝ) = ((500000 / 988127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (187017059 / 50000000) ≤ -Real.log (11873 / 500000) ∧
    -Real.log (11873 / 500000) ≤ (1870170593 / 500000000) := by
  have h := checkLog_sound (w := (1876 / 13749)) (n := 12)
    (lo := (1716283 / 6250000)) (hi := (274605281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11873) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11873) = 1/(11873 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1870170593 / 500000000) (-187017059 / 50000000) (Real.log (11873 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (442077747 / 100000000) ≤ -Real.log (500000000000 / 41580457835381) ∧
    -Real.log (500000000000 / 41580457835381) ≤ (4420777477 / 1000000000) := by
  have h := checkLog_sound (w := (9580457835381 / 73580457835381)) (n := 12)
    (lo := (26189439 / 100000000)) (hi := (261894391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41580457835381 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(41580457835381 / 32000000000000) = 1/(500000000000 / 41580457835381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (442077747 / 100000000) (4420777477 / 1000000000) (Real.log (41580457835381 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (41580457835381 / 500000000000) = -Real.log (500000000000 / 41580457835381) := by
    rw [show ((41580457835381 / 500000000000) : ℝ) = ((500000000000 / 41580457835381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4427185443 / 1000000000) ≤ -Real.log (500000000000 / 41847759803507) ∧
    -Real.log (500000000000 / 41847759803507) ≤ (88543709 / 20000000) := by
  have h := checkLog_sound (w := (9847759803507 / 73847759803507)) (n := 12)
    (lo := (268302363 / 1000000000)) (hi := (67075591 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41847759803507 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(41847759803507 / 32000000000000) = 1/(500000000000 / 41847759803507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4427185443 / 1000000000) (88543709 / 20000000) (Real.log (41847759803507 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (41847759803507 / 500000000000) = -Real.log (500000000000 / 41847759803507) := by
    rw [show ((41847759803507 / 500000000000) : ℝ) = ((500000000000 / 41847759803507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4415129071 / 1000000000) ≤ -Real.log (125000000000 / 10336564213081) ∧
    -Real.log (125000000000 / 10336564213081) ≤ (2207564539 / 500000000) := by
  have h := checkLog_sound (w := (2336564213081 / 18336564213081)) (n := 12)
    (lo := (256245991 / 1000000000)) (hi := (32030749 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10336564213081 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10336564213081 / 8000000000000) = 1/(125000000000 / 10336564213081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4415129071 / 1000000000) (2207564539 / 500000000) (Real.log (10336564213081 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (10336564213081 / 125000000000) = -Real.log (125000000000 / 10336564213081) := by
    rw [show ((10336564213081 / 125000000000) : ℝ) = ((125000000000 / 10336564213081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4421544313 / 1000000000) ≤ -Real.log (250000000000 / 20806177882591) ∧
    -Real.log (250000000000 / 20806177882591) ≤ (6908663 / 1562500) := by
  have h := checkLog_sound (w := (4806177882591 / 36806177882591)) (n := 12)
    (lo := (262661233 / 1000000000)) (hi := (131330617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20806177882591 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(20806177882591 / 16000000000000) = 1/(250000000000 / 20806177882591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4421544313 / 1000000000) (6908663 / 1562500) (Real.log (20806177882591 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (20806177882591 / 250000000000) = -Real.log (250000000000 / 20806177882591) := by
    rw [show ((20806177882591 / 250000000000) : ℝ) = ((250000000000 / 20806177882591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0051

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0052Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0052
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

theorem reflection_log_1_neg : (678870953 / 1000000000) ≤ -Real.log (102400 / 201897) ∧
    -Real.log (102400 / 201897) ≤ (339435477 / 500000000) := by
  have h := checkLog_sound (w := (99497 / 304297)) (n := 12)
    (lo := (678870953 / 1000000000)) (hi := (339435477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201897 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201897 / 102400) = 1/(102400 / 201897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (678870953 / 1000000000) (339435477 / 500000000) (Real.log (201897 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (201897 / 102400) = -Real.log (102400 / 201897) := by
    rw [show ((201897 / 102400) : ℝ) = ((102400 / 201897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (445392753 / 125000000) ≤ -Real.log (2903 / 102400) ∧
    -Real.log (2903 / 102400) ≤ (356314203 / 100000000) := by
  have h := checkLog_sound (w := (297 / 6103)) (n := 12)
    (lo := (24351531 / 250000000)) (hi := (779249 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2903) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2903) = 1/(2903 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-356314203 / 100000000) (-445392753 / 125000000) (Real.log (2903 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (678776841 / 1000000000) ≤ -Real.log (51200 / 100939) ∧
    -Real.log (51200 / 100939) ≤ (339388421 / 500000000) := by
  have h := checkLog_sound (w := (49739 / 152139)) (n := 12)
    (lo := (678776841 / 1000000000)) (hi := (339388421 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100939 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100939 / 51200) = 1/(51200 / 100939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (678776841 / 1000000000) (339388421 / 500000000) (Real.log (100939 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100939 / 51200) = -Real.log (51200 / 100939) := by
    rw [show ((100939 / 51200) : ℝ) = ((51200 / 100939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (889154599 / 250000000) ≤ -Real.log (1461 / 51200) ∧
    -Real.log (1461 / 51200) ≤ (1778309201 / 500000000) := by
  have h := checkLog_sound (w := (139 / 3061)) (n := 12)
    (lo := (1420039 / 15625000)) (hi := (90882497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1461) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1461) = 1/(1461 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1778309201 / 500000000) (-889154599 / 250000000) (Real.log (1461 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (16609699 / 25000000) ≤ -Real.log (51200 / 99497) ∧
    -Real.log (51200 / 99497) ≤ (664387961 / 1000000000) := by
  have h := checkLog_sound (w := (48297 / 150697)) (n := 12)
    (lo := (16609699 / 25000000)) (hi := (664387961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99497 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99497 / 51200) = 1/(51200 / 99497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (16609699 / 25000000) (664387961 / 1000000000) (Real.log (99497 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99497 / 51200) = -Real.log (51200 / 99497) := by
    rw [show ((99497 / 51200) : ℝ) = ((51200 / 99497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (717498711 / 250000000) ≤ -Real.log (2903 / 51200) ∧
    -Real.log (2903 / 51200) ≤ (2869994849 / 1000000000) := by
  have h := checkLog_sound (w := (297 / 6103)) (n := 12)
    (lo := (24351531 / 250000000)) (hi := (779249 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2903) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2903) = 1/(2903 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2869994849 / 1000000000) (-717498711 / 250000000) (Real.log (2903 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (332098491 / 500000000) ≤ -Real.log (25600 / 49739) ∧
    -Real.log (25600 / 49739) ≤ (664196983 / 1000000000) := by
  have h := checkLog_sound (w := (24139 / 75339)) (n := 12)
    (lo := (332098491 / 500000000)) (hi := (664196983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49739 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49739 / 25600) = 1/(25600 / 49739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (332098491 / 500000000) (664196983 / 1000000000) (Real.log (49739 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49739 / 25600) = -Real.log (25600 / 49739) := by
    rw [show ((49739 / 25600) : ℝ) = ((25600 / 49739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (178966951 / 62500000) ≤ -Real.log (1461 / 25600) ∧
    -Real.log (1461 / 25600) ≤ (2863471221 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 3061)) (n := 12)
    (lo := (1420039 / 15625000)) (hi := (90882497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1461) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1461) = 1/(1461 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2863471221 / 1000000000) (-178966951 / 62500000) (Real.log (1461 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (170279783 / 250000000) ≤ -Real.log (125000 / 247011) ∧
    -Real.log (125000 / 247011) ≤ (681119133 / 1000000000) := by
  have h := checkLog_sound (w := (122011 / 372011)) (n := 12)
    (lo := (170279783 / 250000000)) (hi := (681119133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247011 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247011 / 125000) = 1/(125000 / 247011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (170279783 / 250000000) (681119133 / 1000000000) (Real.log (247011 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (247011 / 125000) = -Real.log (125000 / 247011) := by
    rw [show ((247011 / 125000) : ℝ) = ((125000 / 247011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3733374851 / 1000000000) ≤ -Real.log (2989 / 125000) ∧
    -Real.log (2989 / 125000) ≤ (3733374857 / 1000000000) := by
  have h := checkLog_sound (w := (3669 / 27581)) (n := 12)
    (lo := (267638951 / 1000000000)) (hi := (33454869 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11956) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11956) = 1/(2989 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3733374857 / 1000000000) (-3733374851 / 1000000000) (Real.log (2989 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (681194531 / 1000000000) ≤ -Real.log (1000000 / 1976237) ∧
    -Real.log (1000000 / 1976237) ≤ (170298633 / 250000000) := by
  have h := checkLog_sound (w := (976237 / 2976237)) (n := 12)
    (lo := (681194531 / 1000000000)) (hi := (170298633 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1976237 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1976237 / 1000000) = 1/(1000000 / 1976237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (681194531 / 1000000000) (170298633 / 250000000) (Real.log (1976237 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1976237 / 1000000) = -Real.log (1000000 / 1976237) := by
    rw [show ((1976237 / 1000000) : ℝ) = ((1000000 / 1976237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3739625527 / 1000000000) ≤ -Real.log (23763 / 1000000) ∧
    -Real.log (23763 / 1000000) ≤ (3739625533 / 1000000000) := by
  have h := checkLog_sound (w := (7487 / 55013)) (n := 12)
    (lo := (273889627 / 1000000000)) (hi := (68472407 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23763) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 23763) = 1/(23763 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3739625533 / 1000000000) (-3739625527 / 1000000000) (Real.log (23763 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (681050307 / 1000000000) ≤ -Real.log (62500 / 123497) ∧
    -Real.log (62500 / 123497) ≤ (170262577 / 250000000) := by
  have h := checkLog_sound (w := (60997 / 185997)) (n := 12)
    (lo := (681050307 / 1000000000)) (hi := (170262577 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123497 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123497 / 62500) = 1/(62500 / 123497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (681050307 / 1000000000) (170262577 / 250000000) (Real.log (123497 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (123497 / 62500) = -Real.log (62500 / 123497) := by
    rw [show ((123497 / 62500) : ℝ) = ((62500 / 123497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3727703443 / 1000000000) ≤ -Real.log (1503 / 62500) ∧
    -Real.log (1503 / 62500) ≤ (3727703449 / 1000000000) := by
  have h := checkLog_sound (w := (3601 / 27649)) (n := 12)
    (lo := (261967543 / 1000000000)) (hi := (32745943 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12024) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12024) = 1/(1503 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3727703449 / 1000000000) (-3727703443 / 1000000000) (Real.log (1503 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (681127229 / 1000000000) ≤ -Real.log (125000 / 247013) ∧
    -Real.log (125000 / 247013) ≤ (68112723 / 100000000) := by
  have h := checkLog_sound (w := (122013 / 372013)) (n := 12)
    (lo := (681127229 / 1000000000)) (hi := (68112723 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247013 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247013 / 125000) = 1/(125000 / 247013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (681127229 / 1000000000) (68112723 / 100000000) (Real.log (247013 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (247013 / 125000) = -Real.log (125000 / 247013) := by
    rw [show ((247013 / 125000) : ℝ) = ((125000 / 247013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (746808839 / 200000000) ≤ -Real.log (2987 / 125000) ∧
    -Real.log (2987 / 125000) ≤ (3734044201 / 1000000000) := by
  have h := checkLog_sound (w := (3677 / 27573)) (n := 12)
    (lo := (53661659 / 200000000)) (hi := (33538537 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11948) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11948) = 1/(2987 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3734044201 / 1000000000) (-746808839 / 200000000) (Real.log (2987 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4414493983 / 1000000000) ≤ -Real.log (500000000000 / 41320006691201) ∧
    -Real.log (500000000000 / 41320006691201) ≤ (441449399 / 100000000) := by
  have h := checkLog_sound (w := (9320006691201 / 73320006691201)) (n := 12)
    (lo := (255610903 / 1000000000)) (hi := (31951363 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41320006691201 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(41320006691201 / 32000000000000) = 1/(500000000000 / 41320006691201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4414493983 / 1000000000) (441449399 / 100000000) (Real.log (41320006691201 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (41320006691201 / 500000000000) = -Real.log (500000000000 / 41320006691201) := by
    rw [show ((41320006691201 / 500000000000) : ℝ) = ((500000000000 / 41320006691201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4420820057 / 1000000000) ≤ -Real.log (500000000000 / 41582228674831) ∧
    -Real.log (500000000000 / 41582228674831) ≤ (138150627 / 31250000) := by
  have h := checkLog_sound (w := (9582228674831 / 73582228674831)) (n := 12)
    (lo := (261936977 / 1000000000)) (hi := (130968489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41582228674831 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(41582228674831 / 32000000000000) = 1/(500000000000 / 41582228674831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4420820057 / 1000000000) (138150627 / 31250000) (Real.log (41582228674831 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (41582228674831 / 500000000000) = -Real.log (500000000000 / 41582228674831) := by
    rw [show ((41582228674831 / 500000000000) : ℝ) = ((500000000000 / 41582228674831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3527003 / 800000) ≤ -Real.log (125000000000 / 10270874916833) ∧
    -Real.log (125000000000 / 10270874916833) ≤ (4408753757 / 1000000000) := by
  have h := checkLog_sound (w := (2270874916833 / 18270874916833)) (n := 12)
    (lo := (24987067 / 100000000)) (hi := (249870671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10270874916833 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10270874916833 / 8000000000000) = 1/(125000000000 / 10270874916833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3527003 / 800000) (4408753757 / 1000000000) (Real.log (10270874916833 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (10270874916833 / 125000000000) = -Real.log (125000000000 / 10270874916833) := by
    rw [show ((10270874916833 / 125000000000) : ℝ) = ((125000000000 / 10270874916833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (137974107 / 31250000) ≤ -Real.log (250000000000 / 20674004017409) ∧
    -Real.log (250000000000 / 20674004017409) ≤ (4415171431 / 1000000000) := by
  have h := checkLog_sound (w := (4674004017409 / 36674004017409)) (n := 12)
    (lo := (32036043 / 125000000)) (hi := (51257669 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20674004017409 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(20674004017409 / 16000000000000) = 1/(250000000000 / 20674004017409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (137974107 / 31250000) (4415171431 / 1000000000) (Real.log (20674004017409 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (20674004017409 / 250000000000) = -Real.log (250000000000 / 20674004017409) := by
    rw [show ((20674004017409 / 250000000000) : ℝ) = ((250000000000 / 20674004017409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0052

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0053Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0053
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

theorem reflection_log_1_neg : (678776841 / 1000000000) ≤ -Real.log (51200 / 100939) ∧
    -Real.log (51200 / 100939) ≤ (339388421 / 500000000) := by
  have h := checkLog_sound (w := (49739 / 152139)) (n := 12)
    (lo := (678776841 / 1000000000)) (hi := (339388421 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100939 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100939 / 51200) = 1/(51200 / 100939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (678776841 / 1000000000) (339388421 / 500000000) (Real.log (100939 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100939 / 51200) = -Real.log (51200 / 100939) := by
    rw [show ((100939 / 51200) : ℝ) = ((51200 / 100939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (889154599 / 250000000) ≤ -Real.log (1461 / 51200) ∧
    -Real.log (1461 / 51200) ≤ (1778309201 / 500000000) := by
  have h := checkLog_sound (w := (139 / 3061)) (n := 12)
    (lo := (1420039 / 15625000)) (hi := (90882497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1461) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1461) = 1/(1461 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1778309201 / 500000000) (-889154599 / 250000000) (Real.log (1461 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (678682721 / 1000000000) ≤ -Real.log (102400 / 201859) ∧
    -Real.log (102400 / 201859) ≤ (339341361 / 500000000) := by
  have h := checkLog_sound (w := (99459 / 304259)) (n := 12)
    (lo := (678682721 / 1000000000)) (hi := (339341361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201859 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201859 / 102400) = 1/(102400 / 201859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (678682721 / 1000000000) (339341361 / 500000000) (Real.log (201859 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (201859 / 102400) = -Real.log (102400 / 201859) := by
    rw [show ((201859 / 102400) : ℝ) = ((102400 / 201859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (71002741 / 20000000) ≤ -Real.log (2941 / 102400) ∧
    -Real.log (2941 / 102400) ≤ (110941783 / 31250000) := by
  have h := checkLog_sound (w := (259 / 6141)) (n := 12)
    (lo := (1688023 / 20000000)) (hi := (84401151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2941) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2941) = 1/(2941 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-110941783 / 31250000) (-71002741 / 20000000) (Real.log (2941 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (332098491 / 500000000) ≤ -Real.log (25600 / 49739) ∧
    -Real.log (25600 / 49739) ≤ (664196983 / 1000000000) := by
  have h := checkLog_sound (w := (24139 / 75339)) (n := 12)
    (lo := (332098491 / 500000000)) (hi := (664196983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49739 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49739 / 25600) = 1/(25600 / 49739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (332098491 / 500000000) (664196983 / 1000000000) (Real.log (49739 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49739 / 25600) = -Real.log (25600 / 49739) := by
    rw [show ((49739 / 25600) : ℝ) = ((25600 / 49739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (178966951 / 62500000) ≤ -Real.log (1461 / 25600) ∧
    -Real.log (1461 / 25600) ≤ (2863471221 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 3061)) (n := 12)
    (lo := (1420039 / 15625000)) (hi := (90882497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1461) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1461) = 1/(1461 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2863471221 / 1000000000) (-178966951 / 62500000) (Real.log (1461 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (332002983 / 500000000) ≤ -Real.log (51200 / 99459) ∧
    -Real.log (51200 / 99459) ≤ (664005967 / 1000000000) := by
  have h := checkLog_sound (w := (48259 / 150659)) (n := 12)
    (lo := (332002983 / 500000000)) (hi := (664005967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99459 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99459 / 51200) = 1/(51200 / 99459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (332002983 / 500000000) (664005967 / 1000000000) (Real.log (99459 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99459 / 51200) = -Real.log (51200 / 99459) := by
    rw [show ((99459 / 51200) : ℝ) = ((51200 / 99459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (285698987 / 100000000) ≤ -Real.log (2941 / 51200) ∧
    -Real.log (2941 / 51200) ≤ (22855919 / 8000000) := by
  have h := checkLog_sound (w := (259 / 6141)) (n := 12)
    (lo := (1688023 / 20000000)) (hi := (84401151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2941) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2941) = 1/(2941 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-22855919 / 8000000) (-285698987 / 100000000) (Real.log (2941 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (340522117 / 500000000) ≤ -Real.log (50000 / 98797) ∧
    -Real.log (50000 / 98797) ≤ (136208847 / 200000000) := by
  have h := checkLog_sound (w := (48797 / 148797)) (n := 12)
    (lo := (340522117 / 500000000)) (hi := (136208847 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98797 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98797 / 50000) = 1/(50000 / 98797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (340522117 / 500000000) (136208847 / 200000000) (Real.log (98797 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (98797 / 50000) = -Real.log (50000 / 98797) := by
    rw [show ((98797 / 50000) : ℝ) = ((50000 / 98797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (745440913 / 200000000) ≤ -Real.log (1203 / 50000) ∧
    -Real.log (1203 / 50000) ≤ (3727204571 / 1000000000) := by
  have h := checkLog_sound (w := (719 / 5531)) (n := 12)
    (lo := (52293733 / 200000000)) (hi := (130734333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2406) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2406) = 1/(1203 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3727204571 / 1000000000) (-745440913 / 200000000) (Real.log (1203 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (340559819 / 500000000) ≤ -Real.log (1000000 / 1976089) ∧
    -Real.log (1000000 / 1976089) ≤ (681119639 / 1000000000) := by
  have h := checkLog_sound (w := (976089 / 2976089)) (n := 12)
    (lo := (340559819 / 500000000)) (hi := (681119639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1976089 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1976089 / 1000000) = 1/(1000000 / 1976089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (340559819 / 500000000) (681119639 / 1000000000) (Real.log (1976089 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1976089 / 1000000) = -Real.log (1000000 / 1976089) := by
    rw [show ((1976089 / 1000000) : ℝ) = ((1000000 / 1976089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (116669271 / 31250000) ≤ -Real.log (23911 / 1000000) ∧
    -Real.log (23911 / 1000000) ≤ (1866708339 / 500000000) := by
  have h := checkLog_sound (w := (7339 / 55161)) (n := 12)
    (lo := (66920193 / 250000000)) (hi := (267680773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23911) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 23911) = 1/(23911 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1866708339 / 500000000) (-116669271 / 31250000) (Real.log (23911 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (680974391 / 1000000000) ≤ -Real.log (500000 / 987901) ∧
    -Real.log (500000 / 987901) ≤ (85121799 / 125000000) := by
  have h := checkLog_sound (w := (487901 / 1487901)) (n := 12)
    (lo := (680974391 / 1000000000)) (hi := (85121799 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987901 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987901 / 500000) = 1/(500000 / 987901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (680974391 / 1000000000) (85121799 / 125000000) (Real.log (987901 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (987901 / 500000) = -Real.log (500000 / 987901) := by
    rw [show ((987901 / 500000) : ℝ) = ((500000 / 987901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3721485291 / 1000000000) ≤ -Real.log (12099 / 500000) ∧
    -Real.log (12099 / 500000) ≤ (3721485297 / 1000000000) := by
  have h := checkLog_sound (w := (1763 / 13862)) (n := 12)
    (lo := (255749391 / 1000000000)) (hi := (15984337 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12099) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12099) = 1/(12099 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3721485297 / 1000000000) (-3721485291 / 1000000000) (Real.log (12099 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (681050813 / 1000000000) ≤ -Real.log (1000000 / 1975953) ∧
    -Real.log (1000000 / 1975953) ≤ (340525407 / 500000000) := by
  have h := checkLog_sound (w := (975953 / 2975953)) (n := 12)
    (lo := (681050813 / 1000000000)) (hi := (340525407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975953 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975953 / 1000000) = 1/(1000000 / 1975953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (681050813 / 1000000000) (340525407 / 500000000) (Real.log (1975953 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1975953 / 1000000) = -Real.log (1000000 / 1975953) := by
    rw [show ((1975953 / 1000000) : ℝ) = ((1000000 / 1975953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3727745027 / 1000000000) ≤ -Real.log (24047 / 1000000) ∧
    -Real.log (24047 / 1000000) ≤ (3727745033 / 1000000000) := by
  have h := checkLog_sound (w := (7203 / 55297)) (n := 12)
    (lo := (262009127 / 1000000000)) (hi := (32751141 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24047) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24047) = 1/(24047 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3727745033 / 1000000000) (-3727745027 / 1000000000) (Real.log (24047 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4408248799 / 1000000000) ≤ -Real.log (31250000000 / 2566422485453) ∧
    -Real.log (31250000000 / 2566422485453) ≤ (2204124403 / 500000000) := by
  have h := checkLog_sound (w := (566422485453 / 4566422485453)) (n := 12)
    (lo := (249365719 / 1000000000)) (hi := (6234143 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2566422485453 / 2000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2566422485453 / 2000000000000) = 1/(31250000000 / 2566422485453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4408248799 / 1000000000) (2204124403 / 500000000) (Real.log (2566422485453 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2566422485453 / 31250000000) = -Real.log (31250000000 / 2566422485453) := by
    rw [show ((2566422485453 / 31250000000) : ℝ) = ((31250000000 / 2566422485453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (441453631 / 100000000) ≤ -Real.log (62500000000 / 5165219459663) ∧
    -Real.log (62500000000 / 5165219459663) ≤ (4414536317 / 1000000000) := by
  have h := checkLog_sound (w := (1165219459663 / 9165219459663)) (n := 12)
    (lo := (25565323 / 100000000)) (hi := (255653231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5165219459663 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5165219459663 / 4000000000000) = 1/(62500000000 / 5165219459663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (441453631 / 100000000) (4414536317 / 1000000000) (Real.log (5165219459663 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5165219459663 / 62500000000) = -Real.log (62500000000 / 5165219459663) := by
    rw [show ((5165219459663 / 62500000000) : ℝ) = ((62500000000 / 5165219459663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2201229841 / 500000000) ≤ -Real.log (500000000000 / 40825729399123) ∧
    -Real.log (500000000000 / 40825729399123) ≤ (4402459689 / 1000000000) := by
  have h := checkLog_sound (w := (8825729399123 / 72825729399123)) (n := 12)
    (lo := (121788301 / 500000000)) (hi := (243576603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40825729399123 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(40825729399123 / 32000000000000) = 1/(500000000000 / 40825729399123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2201229841 / 500000000) (4402459689 / 1000000000) (Real.log (40825729399123 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (40825729399123 / 500000000000) = -Real.log (500000000000 / 40825729399123) := by
    rw [show ((40825729399123 / 500000000000) : ℝ) = ((500000000000 / 40825729399123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (13777487 / 3125000) ≤ -Real.log (250000000000 / 20542614463343) ∧
    -Real.log (250000000000 / 20542614463343) ≤ (4408795847 / 1000000000) := by
  have h := checkLog_sound (w := (4542614463343 / 36542614463343)) (n := 12)
    (lo := (6247819 / 25000000)) (hi := (249912761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20542614463343 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(20542614463343 / 16000000000000) = 1/(250000000000 / 20542614463343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (13777487 / 3125000) (4408795847 / 1000000000) (Real.log (20542614463343 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (20542614463343 / 250000000000) = -Real.log (250000000000 / 20542614463343) := by
    rw [show ((20542614463343 / 250000000000) : ℝ) = ((250000000000 / 20542614463343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0053

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0054Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0054
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

theorem reflection_log_1_neg : (678682721 / 1000000000) ≤ -Real.log (102400 / 201859) ∧
    -Real.log (102400 / 201859) ≤ (339341361 / 500000000) := by
  have h := checkLog_sound (w := (99459 / 304259)) (n := 12)
    (lo := (678682721 / 1000000000)) (hi := (339341361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201859 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201859 / 102400) = 1/(102400 / 201859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (678682721 / 1000000000) (339341361 / 500000000) (Real.log (201859 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (201859 / 102400) = -Real.log (102400 / 201859) := by
    rw [show ((201859 / 102400) : ℝ) = ((102400 / 201859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (71002741 / 20000000) ≤ -Real.log (2941 / 102400) ∧
    -Real.log (2941 / 102400) ≤ (110941783 / 31250000) := by
  have h := checkLog_sound (w := (259 / 6141)) (n := 12)
    (lo := (1688023 / 20000000)) (hi := (84401151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2941) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2941) = 1/(2941 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-110941783 / 31250000) (-71002741 / 20000000) (Real.log (2941 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (678588591 / 1000000000) ≤ -Real.log (1280 / 2523) ∧
    -Real.log (1280 / 2523) ≤ (42411787 / 62500000) := by
  have h := checkLog_sound (w := (1243 / 3803)) (n := 12)
    (lo := (678588591 / 1000000000)) (hi := (42411787 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2523 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2523 / 1280) = 1/(1280 / 2523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (678588591 / 1000000000) (42411787 / 62500000) (Real.log (2523 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2523 / 1280) = -Real.log (1280 / 2523) := by
    rw [show ((2523 / 1280) : ℝ) = ((1280 / 2523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3543697441 / 1000000000) ≤ -Real.log (37 / 1280) ∧
    -Real.log (37 / 1280) ≤ (3543697447 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 77)) (n := 12)
    (lo := (77961541 / 1000000000)) (hi := (38980771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 37) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(40 / 37) = 1/(37 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3543697447 / 1000000000) (-3543697441 / 1000000000) (Real.log (37 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (332002983 / 500000000) ≤ -Real.log (51200 / 99459) ∧
    -Real.log (51200 / 99459) ≤ (664005967 / 1000000000) := by
  have h := checkLog_sound (w := (48259 / 150659)) (n := 12)
    (lo := (332002983 / 500000000)) (hi := (664005967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99459 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99459 / 51200) = 1/(51200 / 99459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (332002983 / 500000000) (664005967 / 1000000000) (Real.log (99459 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99459 / 51200) = -Real.log (51200 / 99459) := by
    rw [show ((99459 / 51200) : ℝ) = ((51200 / 99459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (285698987 / 100000000) ≤ -Real.log (2941 / 51200) ∧
    -Real.log (2941 / 51200) ≤ (22855919 / 8000000) := by
  have h := checkLog_sound (w := (259 / 6141)) (n := 12)
    (lo := (1688023 / 20000000)) (hi := (84401151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2941) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2941) = 1/(2941 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-22855919 / 8000000) (-285698987 / 100000000) (Real.log (2941 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (132762983 / 200000000) ≤ -Real.log (640 / 1243) ∧
    -Real.log (640 / 1243) ≤ (165953729 / 250000000) := by
  have h := checkLog_sound (w := (603 / 1883)) (n := 12)
    (lo := (132762983 / 200000000)) (hi := (165953729 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1243 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1243 / 640) = 1/(640 / 1243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (132762983 / 200000000) (165953729 / 250000000) (Real.log (1243 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1243 / 640) = -Real.log (640 / 1243) := by
    rw [show ((1243 / 640) : ℝ) = ((640 / 1243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2850550261 / 1000000000) ≤ -Real.log (37 / 640) ∧
    -Real.log (37 / 640) ≤ (1425275133 / 500000000) := by
  have h := checkLog_sound (w := (3 / 77)) (n := 12)
    (lo := (77961541 / 1000000000)) (hi := (38980771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 37) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(40 / 37) = 1/(37 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1425275133 / 500000000) (-2850550261 / 1000000000) (Real.log (37 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (68096933 / 100000000) ≤ -Real.log (62500 / 123487) ∧
    -Real.log (62500 / 123487) ≤ (680969331 / 1000000000) := by
  have h := checkLog_sound (w := (60987 / 185987)) (n := 12)
    (lo := (68096933 / 100000000)) (hi := (680969331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123487 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123487 / 62500) = 1/(62500 / 123487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (68096933 / 100000000) (680969331 / 1000000000) (Real.log (123487 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (123487 / 62500) = -Real.log (62500 / 123487) := by
    rw [show ((123487 / 62500) : ℝ) = ((62500 / 123487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3721072119 / 1000000000) ≤ -Real.log (1513 / 62500) ∧
    -Real.log (1513 / 62500) ≤ (29768577 / 8000000) := by
  have h := checkLog_sound (w := (3521 / 27729)) (n := 12)
    (lo := (255336219 / 1000000000)) (hi := (12766811 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12104) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12104) = 1/(1513 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-29768577 / 8000000) (-3721072119 / 1000000000) (Real.log (1513 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (34052237 / 50000000) ≤ -Real.log (1000000 / 1975941) ∧
    -Real.log (1000000 / 1975941) ≤ (681044741 / 1000000000) := by
  have h := checkLog_sound (w := (975941 / 2975941)) (n := 12)
    (lo := (34052237 / 50000000)) (hi := (681044741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975941 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975941 / 1000000) = 1/(1000000 / 1975941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (34052237 / 50000000) (681044741 / 1000000000) (Real.log (1975941 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1975941 / 1000000) = -Real.log (1000000 / 1975941) := by
    rw [show ((1975941 / 1000000) : ℝ) = ((1000000 / 1975941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3727246129 / 1000000000) ≤ -Real.log (24059 / 1000000) ∧
    -Real.log (24059 / 1000000) ≤ (745449227 / 200000000) := by
  have h := checkLog_sound (w := (7191 / 55309)) (n := 12)
    (lo := (261510229 / 1000000000)) (hi := (26151023 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24059) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24059) = 1/(24059 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-745449227 / 200000000) (-3727246129 / 1000000000) (Real.log (24059 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (68089847 / 100000000) ≤ -Real.log (250000 / 493913) ∧
    -Real.log (250000 / 493913) ≤ (680898471 / 1000000000) := by
  have h := checkLog_sound (w := (243913 / 743913)) (n := 12)
    (lo := (68089847 / 100000000)) (hi := (680898471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493913 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493913 / 250000) = 1/(250000 / 493913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (68089847 / 100000000) (680898471 / 1000000000) (Real.log (493913 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (493913 / 250000) = -Real.log (250000 / 493913) := by
    rw [show ((493913 / 250000) : ℝ) = ((250000 / 493913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (743061113 / 200000000) ≤ -Real.log (6087 / 250000) ∧
    -Real.log (6087 / 250000) ≤ (3715305571 / 1000000000) := by
  have h := checkLog_sound (w := (3451 / 27799)) (n := 12)
    (lo := (49913933 / 200000000)) (hi := (124784833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12174) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12174) = 1/(6087 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3715305571 / 1000000000) (-743061113 / 200000000) (Real.log (6087 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (680974897 / 1000000000) ≤ -Real.log (1000000 / 1975803) ∧
    -Real.log (1000000 / 1975803) ≤ (680974899 / 1000000000) := by
  have h := checkLog_sound (w := (975803 / 2975803)) (n := 12)
    (lo := (680974897 / 1000000000)) (hi := (680974899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975803 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975803 / 1000000) = 1/(1000000 / 1975803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (680974897 / 1000000000) (680974899 / 1000000000) (Real.log (1975803 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1975803 / 1000000) = -Real.log (1000000 / 1975803) := by
    rw [show ((1975803 / 1000000) : ℝ) = ((1000000 / 1975803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3721526617 / 1000000000) ≤ -Real.log (24197 / 1000000) ∧
    -Real.log (24197 / 1000000) ≤ (3721526623 / 1000000000) := by
  have h := checkLog_sound (w := (7053 / 55447)) (n := 12)
    (lo := (255790717 / 1000000000)) (hi := (127895359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24197) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24197) = 1/(24197 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3721526623 / 1000000000) (-3721526617 / 1000000000) (Real.log (24197 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4402041449 / 1000000000) ≤ -Real.log (250000000000 / 20404329147389) ∧
    -Real.log (250000000000 / 20404329147389) ≤ (275127591 / 62500000) := by
  have h := checkLog_sound (w := (4404329147389 / 36404329147389)) (n := 12)
    (lo := (243158369 / 1000000000)) (hi := (24315837 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20404329147389 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(20404329147389 / 16000000000000) = 1/(250000000000 / 20404329147389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4402041449 / 1000000000) (275127591 / 62500000) (Real.log (20404329147389 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (20404329147389 / 250000000000) = -Real.log (250000000000 / 20404329147389) := by
    rw [show ((20404329147389 / 250000000000) : ℝ) = ((250000000000 / 20404329147389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4408290869 / 1000000000) ≤ -Real.log (10000000000 / 821289746041) ∧
    -Real.log (10000000000 / 821289746041) ≤ (1102072719 / 250000000) := by
  have h := checkLog_sound (w := (181289746041 / 1461289746041)) (n := 12)
    (lo := (249407789 / 1000000000)) (hi := (24940779 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821289746041 / 640000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(821289746041 / 640000000000) = 1/(10000000000 / 821289746041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4408290869 / 1000000000) (1102072719 / 250000000) (Real.log (821289746041 / 10000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (821289746041 / 10000000000) = -Real.log (10000000000 / 821289746041) := by
    rw [show ((821289746041 / 10000000000) : ℝ) = ((10000000000 / 821289746041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (879240807 / 200000000) ≤ -Real.log (500000000000 / 40571135206177) ∧
    -Real.log (500000000000 / 40571135206177) ≤ (2198102021 / 500000000) := by
  have h := checkLog_sound (w := (8571135206177 / 72571135206177)) (n := 12)
    (lo := (47464191 / 200000000)) (hi := (59330239 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40571135206177 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(40571135206177 / 32000000000000) = 1/(500000000000 / 40571135206177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (879240807 / 200000000) (2198102021 / 500000000) (Real.log (40571135206177 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (40571135206177 / 500000000000) = -Real.log (500000000000 / 40571135206177) := by
    rw [show ((40571135206177 / 500000000000) : ℝ) = ((500000000000 / 40571135206177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (880500303 / 200000000) ≤ -Real.log (250000000000 / 20413718642807) ∧
    -Real.log (250000000000 / 20413718642807) ≤ (2201250761 / 500000000) := by
  have h := checkLog_sound (w := (4413718642807 / 36413718642807)) (n := 12)
    (lo := (48723687 / 200000000)) (hi := (60904609 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20413718642807 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(20413718642807 / 16000000000000) = 1/(250000000000 / 20413718642807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (880500303 / 200000000) (2201250761 / 500000000) (Real.log (20413718642807 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (20413718642807 / 250000000000) = -Real.log (250000000000 / 20413718642807) := by
    rw [show ((20413718642807 / 250000000000) : ℝ) = ((250000000000 / 20413718642807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0054

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0055Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0055
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

theorem reflection_log_1_neg : (678588591 / 1000000000) ≤ -Real.log (1280 / 2523) ∧
    -Real.log (1280 / 2523) ≤ (42411787 / 62500000) := by
  have h := checkLog_sound (w := (1243 / 3803)) (n := 12)
    (lo := (678588591 / 1000000000)) (hi := (42411787 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2523 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2523 / 1280) = 1/(1280 / 2523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (678588591 / 1000000000) (42411787 / 62500000) (Real.log (2523 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2523 / 1280) = -Real.log (1280 / 2523) := by
    rw [show ((2523 / 1280) : ℝ) = ((1280 / 2523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3543697441 / 1000000000) ≤ -Real.log (37 / 1280) ∧
    -Real.log (37 / 1280) ≤ (3543697447 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 77)) (n := 12)
    (lo := (77961541 / 1000000000)) (hi := (38980771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 37) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(40 / 37) = 1/(37 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3543697447 / 1000000000) (-3543697441 / 1000000000) (Real.log (37 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (678494453 / 1000000000) ≤ -Real.log (102400 / 201821) ∧
    -Real.log (102400 / 201821) ≤ (339247227 / 500000000) := by
  have h := checkLog_sound (w := (99421 / 304221)) (n := 12)
    (lo := (678494453 / 1000000000)) (hi := (339247227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201821 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201821 / 102400) = 1/(102400 / 201821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (678494453 / 1000000000) (339247227 / 500000000) (Real.log (201821 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (201821 / 102400) = -Real.log (102400 / 201821) := by
    rw [show ((201821 / 102400) : ℝ) = ((102400 / 201821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (884324759 / 250000000) ≤ -Real.log (2979 / 102400) ∧
    -Real.log (2979 / 102400) ≤ (1768649521 / 500000000) := by
  have h := checkLog_sound (w := (221 / 6179)) (n := 12)
    (lo := (559087 / 7812500)) (hi := (71563137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2979) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2979) = 1/(2979 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1768649521 / 500000000) (-884324759 / 250000000) (Real.log (2979 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (132762983 / 200000000) ≤ -Real.log (640 / 1243) ∧
    -Real.log (640 / 1243) ≤ (165953729 / 250000000) := by
  have h := checkLog_sound (w := (603 / 1883)) (n := 12)
    (lo := (132762983 / 200000000)) (hi := (165953729 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1243 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1243 / 640) = 1/(640 / 1243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (132762983 / 200000000) (165953729 / 250000000) (Real.log (1243 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1243 / 640) = -Real.log (640 / 1243) := by
    rw [show ((1243 / 640) : ℝ) = ((640 / 1243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2850550261 / 1000000000) ≤ -Real.log (37 / 640) ∧
    -Real.log (37 / 640) ≤ (1425275133 / 500000000) := by
  have h := checkLog_sound (w := (3 / 77)) (n := 12)
    (lo := (77961541 / 1000000000)) (hi := (38980771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 37) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(40 / 37) = 1/(37 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1425275133 / 500000000) (-2850550261 / 1000000000) (Real.log (37 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (331811913 / 500000000) ≤ -Real.log (51200 / 99421) ∧
    -Real.log (51200 / 99421) ≤ (663623827 / 1000000000) := by
  have h := checkLog_sound (w := (48221 / 150621)) (n := 12)
    (lo := (331811913 / 500000000)) (hi := (663623827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99421 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99421 / 51200) = 1/(51200 / 99421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (331811913 / 500000000) (663623827 / 1000000000) (Real.log (99421 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99421 / 51200) = -Real.log (51200 / 99421) := by
    rw [show ((99421 / 51200) : ℝ) = ((51200 / 99421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (177759491 / 62500000) ≤ -Real.log (2979 / 51200) ∧
    -Real.log (2979 / 51200) ≤ (2844151861 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 6179)) (n := 12)
    (lo := (559087 / 7812500)) (hi := (71563137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2979) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2979) = 1/(2979 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2844151861 / 1000000000) (-177759491 / 62500000) (Real.log (2979 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (680894421 / 1000000000) ≤ -Real.log (250000 / 493911) ∧
    -Real.log (250000 / 493911) ≤ (340447211 / 500000000) := by
  have h := checkLog_sound (w := (243911 / 743911)) (n := 12)
    (lo := (680894421 / 1000000000)) (hi := (340447211 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493911 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493911 / 250000) = 1/(250000 / 493911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (680894421 / 1000000000) (340447211 / 500000000) (Real.log (493911 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (493911 / 250000) = -Real.log (250000 / 493911) := by
    rw [show ((493911 / 250000) : ℝ) = ((250000 / 493911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (74299541 / 20000000) ≤ -Real.log (6089 / 250000) ∧
    -Real.log (6089 / 250000) ≤ (116093033 / 31250000) := by
  have h := checkLog_sound (w := (3447 / 27803)) (n := 12)
    (lo := (4984823 / 20000000)) (hi := (249241151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12178) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12178) = 1/(6089 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-116093033 / 31250000) (-74299541 / 20000000) (Real.log (6089 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (170242459 / 250000000) ≤ -Real.log (1000000 / 1975793) ∧
    -Real.log (1000000 / 1975793) ≤ (680969837 / 1000000000) := by
  have h := checkLog_sound (w := (975793 / 2975793)) (n := 12)
    (lo := (170242459 / 250000000)) (hi := (680969837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975793 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975793 / 1000000) = 1/(1000000 / 1975793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (170242459 / 250000000) (680969837 / 1000000000) (Real.log (1975793 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1975793 / 1000000) = -Real.log (1000000 / 1975793) := by
    rw [show ((1975793 / 1000000) : ℝ) = ((1000000 / 1975793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (930278357 / 250000000) ≤ -Real.log (24207 / 1000000) ∧
    -Real.log (24207 / 1000000) ≤ (1860556717 / 500000000) := by
  have h := checkLog_sound (w := (7043 / 55457)) (n := 12)
    (lo := (31922191 / 125000000)) (hi := (255377529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24207) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24207) = 1/(24207 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1860556717 / 500000000) (-930278357 / 250000000) (Real.log (24207 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (680822543 / 1000000000) ≤ -Real.log (500000 / 987751) ∧
    -Real.log (500000 / 987751) ≤ (42551409 / 62500000) := by
  have h := checkLog_sound (w := (487751 / 1487751)) (n := 12)
    (lo := (680822543 / 1000000000)) (hi := (42551409 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987751 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987751 / 500000) = 1/(500000 / 987751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (680822543 / 1000000000) (42551409 / 62500000) (Real.log (987751 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (987751 / 500000) = -Real.log (500000 / 987751) := by
    rw [show ((987751 / 500000) : ℝ) = ((500000 / 987751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1854581897 / 500000000) ≤ -Real.log (12249 / 500000) ∧
    -Real.log (12249 / 500000) ≤ (18545819 / 5000000) := by
  have h := checkLog_sound (w := (1688 / 13937)) (n := 12)
    (lo := (121713947 / 500000000)) (hi := (48685579 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12249) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12249) = 1/(12249 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-18545819 / 5000000) (-1854581897 / 500000000) (Real.log (12249 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (21278093 / 31250000) ≤ -Real.log (1000000 / 1975653) ∧
    -Real.log (1000000 / 1975653) ≤ (680898977 / 1000000000) := by
  have h := checkLog_sound (w := (975653 / 2975653)) (n := 12)
    (lo := (21278093 / 31250000)) (hi := (680898977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975653 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975653 / 1000000) = 1/(1000000 / 1975653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (21278093 / 31250000) (680898977 / 1000000000) (Real.log (1975653 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1975653 / 1000000) = -Real.log (1000000 / 1975653) := by
    rw [show ((1975653 / 1000000) : ℝ) = ((1000000 / 1975653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3715346637 / 1000000000) ≤ -Real.log (24347 / 1000000) ∧
    -Real.log (24347 / 1000000) ≤ (3715346643 / 1000000000) := by
  have h := checkLog_sound (w := (6903 / 55597)) (n := 12)
    (lo := (249610737 / 1000000000)) (hi := (124805369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24347) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24347) = 1/(24347 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3715346643 / 1000000000) (-3715346637 / 1000000000) (Real.log (24347 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4395871471 / 1000000000) ≤ -Real.log (250000000000 / 20278822466743) ∧
    -Real.log (250000000000 / 20278822466743) ≤ (2197935739 / 500000000) := by
  have h := checkLog_sound (w := (4278822466743 / 36278822466743)) (n := 12)
    (lo := (236988391 / 1000000000)) (hi := (29623549 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20278822466743 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(20278822466743 / 16000000000000) = 1/(250000000000 / 20278822466743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4395871471 / 1000000000) (2197935739 / 500000000) (Real.log (20278822466743 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (20278822466743 / 250000000000) = -Real.log (250000000000 / 20278822466743) := by
    rw [show ((20278822466743 / 250000000000) : ℝ) = ((250000000000 / 20278822466743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (68782551 / 15625000) ≤ -Real.log (500000000000 / 40810364770521) ∧
    -Real.log (500000000000 / 40810364770521) ≤ (4402083271 / 1000000000) := by
  have h := checkLog_sound (w := (8810364770521 / 72810364770521)) (n := 12)
    (lo := (30400023 / 125000000)) (hi := (48640037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40810364770521 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(40810364770521 / 32000000000000) = 1/(500000000000 / 40810364770521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (68782551 / 15625000) (4402083271 / 1000000000) (Real.log (40810364770521 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (40810364770521 / 500000000000) = -Real.log (500000000000 / 40810364770521) := by
    rw [show ((40810364770521 / 500000000000) : ℝ) = ((500000000000 / 40810364770521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4389986337 / 1000000000) ≤ -Real.log (125000000000 / 10079914686913) ∧
    -Real.log (125000000000 / 10079914686913) ≤ (548748293 / 125000000) := by
  have h := checkLog_sound (w := (2079914686913 / 18079914686913)) (n := 12)
    (lo := (231103257 / 1000000000)) (hi := (115551629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10079914686913 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10079914686913 / 8000000000000) = 1/(125000000000 / 10079914686913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4389986337 / 1000000000) (548748293 / 125000000) (Real.log (10079914686913 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (10079914686913 / 125000000000) = -Real.log (125000000000 / 10079914686913) := by
    rw [show ((10079914686913 / 125000000000) : ℝ) = ((125000000000 / 10079914686913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4396245613 / 1000000000) ≤ -Real.log (62500000000 / 5071602764201) ∧
    -Real.log (62500000000 / 5071602764201) ≤ (219812281 / 50000000) := by
  have h := checkLog_sound (w := (1071602764201 / 9071602764201)) (n := 12)
    (lo := (237362533 / 1000000000)) (hi := (118681267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5071602764201 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5071602764201 / 4000000000000) = 1/(62500000000 / 5071602764201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4396245613 / 1000000000) (219812281 / 50000000) (Real.log (5071602764201 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (5071602764201 / 62500000000) = -Real.log (62500000000 / 5071602764201) := by
    rw [show ((5071602764201 / 62500000000) : ℝ) = ((62500000000 / 5071602764201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0055

end


