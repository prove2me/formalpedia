-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0241Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0241Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:17:37.036892+00:00
-- url     : https://prove2.me/theorems/914f65f8-e6e3-4429-b0ce-d22f1eac4599
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0241Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0242Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0241Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0242Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0243Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0244Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0245Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0246Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0247Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0241Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0242Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0243Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0244Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0245Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0246Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0247Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0241Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0242Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0243Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0244Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0245Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0246Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0247Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0241Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0242Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0243Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0244Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0245Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0246Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0247Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0241Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0241
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

theorem reflection_log_1_neg : (123536839 / 500000000) ≤ -Real.log (1024 / 1311) ∧
    -Real.log (1024 / 1311) ≤ (247073679 / 1000000000) := by
  have h := checkLog_sound (w := (287 / 2335)) (n := 12)
    (lo := (123536839 / 500000000)) (hi := (247073679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1311 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1311 / 1024) = 1/(1024 / 1311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (123536839 / 500000000) (247073679 / 1000000000) (Real.log (1311 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1311 / 1024) = -Real.log (1024 / 1311) := by
    rw [show ((1311 / 1024) : ℝ) = ((1024 / 1311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (328883913 / 1000000000) ≤ -Real.log (737 / 1024) ∧
    -Real.log (737 / 1024) ≤ (164441957 / 500000000) := by
  have h := checkLog_sound (w := (287 / 1761)) (n := 12)
    (lo := (328883913 / 1000000000)) (hi := (164441957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 737) = 1/(737 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-164441957 / 500000000) (-328883913 / 1000000000) (Real.log (737 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (246615907 / 1000000000) ≤ -Real.log (640 / 819) ∧
    -Real.log (640 / 819) ≤ (61653977 / 250000000) := by
  have h := checkLog_sound (w := (179 / 1459)) (n := 12)
    (lo := (246615907 / 1000000000)) (hi := (61653977 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819 / 640) = 1/(640 / 819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (246615907 / 1000000000) (61653977 / 250000000) (Real.log (819 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (819 / 640) = -Real.log (640 / 819) := by
    rw [show ((819 / 640) : ℝ) = ((640 / 819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (328070133 / 1000000000) ≤ -Real.log (461 / 640) ∧
    -Real.log (461 / 640) ≤ (164035067 / 500000000) := by
  have h := checkLog_sound (w := (179 / 1101)) (n := 12)
    (lo := (328070133 / 1000000000)) (hi := (164035067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 461) = 1/(461 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-164035067 / 500000000) (-328070133 / 1000000000) (Real.log (461 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (2781477 / 6250000) ≤ -Real.log (512 / 799) ∧
    -Real.log (512 / 799) ≤ (445036321 / 1000000000) := by
  have h := checkLog_sound (w := (287 / 1311)) (n := 12)
    (lo := (2781477 / 6250000)) (hi := (445036321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((799 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(799 / 512) = 1/(512 / 799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (2781477 / 6250000) (445036321 / 1000000000) (Real.log (799 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (799 / 512) = -Real.log (512 / 799) := by
    rw [show ((799 / 512) : ℝ) = ((512 / 799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (411112111 / 500000000) ≤ -Real.log (225 / 512) ∧
    -Real.log (225 / 512) ≤ (25694507 / 31250000) := by
  have h := checkLog_sound (w := (31 / 481)) (n := 12)
    (lo := (64538521 / 500000000)) (hi := (129077043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 225) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 225) = 1/(225 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-25694507 / 31250000) (-411112111 / 500000000) (Real.log (225 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (444285099 / 1000000000) ≤ -Real.log (320 / 499) ∧
    -Real.log (320 / 499) ≤ (4442851 / 10000000) := by
  have h := checkLog_sound (w := (179 / 819)) (n := 12)
    (lo := (444285099 / 1000000000)) (hi := (4442851 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((499 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(499 / 320) = 1/(320 / 499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (444285099 / 1000000000) (4442851 / 10000000) (Real.log (499 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (499 / 320) = -Real.log (320 / 499) := by
    rw [show ((499 / 320) : ℝ) = ((320 / 499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (51222569 / 62500000) ≤ -Real.log (141 / 320) ∧
    -Real.log (141 / 320) ≤ (409780553 / 500000000) := by
  have h := checkLog_sound (w := (19 / 301)) (n := 12)
    (lo := (31603481 / 250000000)) (hi := (5056557 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 141) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 141) = 1/(141 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-409780553 / 500000000) (-51222569 / 62500000) (Real.log (141 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (337546659 / 1000000000) ≤ -Real.log (200000 / 280301) ∧
    -Real.log (200000 / 280301) ≤ (16877333 / 50000000) := by
  have h := checkLog_sound (w := (80301 / 480301)) (n := 12)
    (lo := (337546659 / 1000000000)) (hi := (16877333 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((280301 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(280301 / 200000) = 1/(200000 / 280301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (337546659 / 1000000000) (16877333 / 50000000) (Real.log (280301 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (280301 / 200000) = -Real.log (200000 / 280301) := by
    rw [show ((280301 / 200000) : ℝ) = ((200000 / 280301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (128334277 / 250000000) ≤ -Real.log (119699 / 200000) ∧
    -Real.log (119699 / 200000) ≤ (513337109 / 1000000000) := by
  have h := checkLog_sound (w := (80301 / 319699)) (n := 12)
    (lo := (128334277 / 250000000)) (hi := (513337109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 119699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 119699) = 1/(119699 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-513337109 / 1000000000) (-128334277 / 250000000) (Real.log (119699 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (16908397 / 50000000) ≤ -Real.log (125000 / 175297) ∧
    -Real.log (125000 / 175297) ≤ (338167941 / 1000000000) := by
  have h := checkLog_sound (w := (50297 / 300297)) (n := 12)
    (lo := (16908397 / 50000000)) (hi := (338167941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175297 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175297 / 125000) = 1/(125000 / 175297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (16908397 / 50000000) (338167941 / 1000000000) (Real.log (175297 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (175297 / 125000) = -Real.log (125000 / 175297) := by
    rw [show ((175297 / 125000) : ℝ) = ((125000 / 175297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (102958697 / 200000000) ≤ -Real.log (74703 / 125000) ∧
    -Real.log (74703 / 125000) ≤ (257396743 / 500000000) := by
  have h := checkLog_sound (w := (50297 / 199703)) (n := 12)
    (lo := (102958697 / 200000000)) (hi := (257396743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 74703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 74703) = 1/(74703 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-257396743 / 500000000) (-102958697 / 200000000) (Real.log (74703 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (260168779 / 1000000000) ≤ -Real.log (1000000 / 1297149) ∧
    -Real.log (1000000 / 1297149) ≤ (13008439 / 50000000) := by
  have h := checkLog_sound (w := (297149 / 2297149)) (n := 12)
    (lo := (260168779 / 1000000000)) (hi := (13008439 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1297149 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1297149 / 1000000) = 1/(1000000 / 1297149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (260168779 / 1000000000) (13008439 / 50000000) (Real.log (1297149 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1297149 / 1000000) = -Real.log (1000000 / 1297149) := by
    rw [show ((1297149 / 1000000) : ℝ) = ((1000000 / 1297149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (176305179 / 500000000) ≤ -Real.log (702851 / 1000000) ∧
    -Real.log (702851 / 1000000) ≤ (352610359 / 1000000000) := by
  have h := checkLog_sound (w := (297149 / 1702851)) (n := 12)
    (lo := (176305179 / 500000000)) (hi := (352610359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 702851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 702851) = 1/(702851 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-352610359 / 1000000000) (-176305179 / 500000000) (Real.log (702851 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (260712131 / 1000000000) ≤ -Real.log (500000 / 648927) ∧
    -Real.log (500000 / 648927) ≤ (65178033 / 250000000) := by
  have h := checkLog_sound (w := (148927 / 1148927)) (n := 12)
    (lo := (260712131 / 1000000000)) (hi := (65178033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((648927 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(648927 / 500000) = 1/(500000 / 648927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (260712131 / 1000000000) (65178033 / 250000000) (Real.log (648927 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (648927 / 500000) = -Real.log (500000 / 648927) := by
    rw [show ((648927 / 500000) : ℝ) = ((500000 / 648927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (353613919 / 1000000000) ≤ -Real.log (351073 / 500000) ∧
    -Real.log (351073 / 500000) ≤ (2210087 / 6250000) := by
  have h := checkLog_sound (w := (148927 / 851073)) (n := 12)
    (lo := (353613919 / 1000000000)) (hi := (2210087 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 351073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 351073) = 1/(351073 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2210087 / 6250000) (-353613919 / 1000000000) (Real.log (351073 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (425441883 / 500000000) ≤ -Real.log (250000000000 / 585428867409) ∧
    -Real.log (250000000000 / 585428867409) ≤ (106360471 / 125000000) := by
  have h := checkLog_sound (w := (85428867409 / 1085428867409)) (n := 12)
    (lo := (78868293 / 500000000)) (hi := (157736587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585428867409 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(585428867409 / 500000000000) = 1/(250000000000 / 585428867409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (425441883 / 500000000) (106360471 / 125000000) (Real.log (585428867409 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (585428867409 / 250000000000) = -Real.log (250000000000 / 585428867409) := by
    rw [show ((585428867409 / 250000000000) : ℝ) = ((250000000000 / 585428867409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (34118457 / 40000000) ≤ -Real.log (500000000000 / 1173292906577) ∧
    -Real.log (500000000000 / 1173292906577) ≤ (852961427 / 1000000000) := by
  have h := checkLog_sound (w := (173292906577 / 2173292906577)) (n := 12)
    (lo := (31962849 / 200000000)) (hi := (79907123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1173292906577 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1173292906577 / 1000000000000) = 1/(500000000000 / 1173292906577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (34118457 / 40000000) (852961427 / 1000000000) (Real.log (1173292906577 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1173292906577 / 500000000000) = -Real.log (500000000000 / 1173292906577) := by
    rw [show ((1173292906577 / 500000000000) : ℝ) = ((500000000000 / 1173292906577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (612779137 / 1000000000) ≤ -Real.log (250000000000 / 461388331239) ∧
    -Real.log (250000000000 / 461388331239) ≤ (306389569 / 500000000) := by
  have h := checkLog_sound (w := (211388331239 / 711388331239)) (n := 12)
    (lo := (612779137 / 1000000000)) (hi := (306389569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((461388331239 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(461388331239 / 250000000000) = 1/(250000000000 / 461388331239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (612779137 / 1000000000) (306389569 / 500000000) (Real.log (461388331239 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (461388331239 / 250000000000) = -Real.log (250000000000 / 461388331239) := by
    rw [show ((461388331239 / 250000000000) : ℝ) = ((250000000000 / 461388331239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (12286521 / 20000000) ≤ -Real.log (125000000000 / 231051305569) ∧
    -Real.log (125000000000 / 231051305569) ≤ (614326051 / 1000000000) := by
  have h := checkLog_sound (w := (106051305569 / 356051305569)) (n := 12)
    (lo := (12286521 / 20000000)) (hi := (614326051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231051305569 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231051305569 / 125000000000) = 1/(125000000000 / 231051305569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (12286521 / 20000000) (614326051 / 1000000000) (Real.log (231051305569 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (231051305569 / 125000000000) = -Real.log (125000000000 / 231051305569) := by
    rw [show ((231051305569 / 125000000000) : ℝ) = ((125000000000 / 231051305569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0241

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0242Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0242
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

theorem reflection_log_1_neg : (246615907 / 1000000000) ≤ -Real.log (640 / 819) ∧
    -Real.log (640 / 819) ≤ (61653977 / 250000000) := by
  have h := checkLog_sound (w := (179 / 1459)) (n := 12)
    (lo := (246615907 / 1000000000)) (hi := (61653977 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819 / 640) = 1/(640 / 819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (246615907 / 1000000000) (61653977 / 250000000) (Real.log (819 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (819 / 640) = -Real.log (640 / 819) := by
    rw [show ((819 / 640) : ℝ) = ((640 / 819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (328070133 / 1000000000) ≤ -Real.log (461 / 640) ∧
    -Real.log (461 / 640) ≤ (164035067 / 500000000) := by
  have h := checkLog_sound (w := (179 / 1101)) (n := 12)
    (lo := (328070133 / 1000000000)) (hi := (164035067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 461) = 1/(461 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-164035067 / 500000000) (-328070133 / 1000000000) (Real.log (461 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (246157927 / 1000000000) ≤ -Real.log (5120 / 6549) ∧
    -Real.log (5120 / 6549) ≤ (30769741 / 125000000) := by
  have h := checkLog_sound (w := (1429 / 11669)) (n := 12)
    (lo := (246157927 / 1000000000)) (hi := (30769741 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6549 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6549 / 5120) = 1/(5120 / 6549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (246157927 / 1000000000) (30769741 / 125000000) (Real.log (6549 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6549 / 5120) = -Real.log (5120 / 6549) := by
    rw [show ((6549 / 5120) : ℝ) = ((5120 / 6549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (65451403 / 200000000) ≤ -Real.log (3691 / 5120) ∧
    -Real.log (3691 / 5120) ≤ (40907127 / 125000000) := by
  have h := checkLog_sound (w := (1429 / 8811)) (n := 12)
    (lo := (65451403 / 200000000)) (hi := (40907127 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3691) = 1/(3691 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-40907127 / 125000000) (-65451403 / 200000000) (Real.log (3691 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (444285099 / 1000000000) ≤ -Real.log (320 / 499) ∧
    -Real.log (320 / 499) ≤ (4442851 / 10000000) := by
  have h := checkLog_sound (w := (179 / 819)) (n := 12)
    (lo := (444285099 / 1000000000)) (hi := (4442851 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((499 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(499 / 320) = 1/(320 / 499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (444285099 / 1000000000) (4442851 / 10000000) (Real.log (499 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (499 / 320) = -Real.log (320 / 499) := by
    rw [show ((499 / 320) : ℝ) = ((320 / 499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (51222569 / 62500000) ≤ -Real.log (141 / 320) ∧
    -Real.log (141 / 320) ≤ (409780553 / 500000000) := by
  have h := checkLog_sound (w := (19 / 301)) (n := 12)
    (lo := (31603481 / 250000000)) (hi := (5056557 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 141) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 141) = 1/(141 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-409780553 / 500000000) (-51222569 / 62500000) (Real.log (141 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (221766657 / 500000000) ≤ -Real.log (2560 / 3989) ∧
    -Real.log (2560 / 3989) ≤ (88706663 / 200000000) := by
  have h := checkLog_sound (w := (1429 / 6549)) (n := 12)
    (lo := (221766657 / 500000000)) (hi := (88706663 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3989 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3989 / 2560) = 1/(2560 / 3989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (221766657 / 500000000) (88706663 / 200000000) (Real.log (3989 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3989 / 2560) = -Real.log (2560 / 3989) := by
    rw [show ((3989 / 2560) : ℝ) = ((2560 / 3989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (40845253 / 50000000) ≤ -Real.log (1131 / 2560) ∧
    -Real.log (1131 / 2560) ≤ (408452531 / 500000000) := by
  have h := checkLog_sound (w := (149 / 2411)) (n := 12)
    (lo := (3093947 / 25000000)) (hi := (123757881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1131) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1131) = 1/(1131 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-408452531 / 500000000) (-40845253 / 50000000) (Real.log (1131 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (67385141 / 200000000) ≤ -Real.log (200000 / 280127) ∧
    -Real.log (200000 / 280127) ≤ (168462853 / 500000000) := by
  have h := checkLog_sound (w := (80127 / 480127)) (n := 12)
    (lo := (67385141 / 200000000)) (hi := (168462853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((280127 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(280127 / 200000) = 1/(200000 / 280127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (67385141 / 200000000) (168462853 / 500000000) (Real.log (280127 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (280127 / 200000) = -Real.log (200000 / 280127) := by
    rw [show ((280127 / 200000) : ℝ) = ((200000 / 280127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (511884517 / 1000000000) ≤ -Real.log (119873 / 200000) ∧
    -Real.log (119873 / 200000) ≤ (255942259 / 500000000) := by
  have h := checkLog_sound (w := (80127 / 319873)) (n := 12)
    (lo := (511884517 / 1000000000)) (hi := (255942259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 119873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 119873) = 1/(119873 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-255942259 / 500000000) (-511884517 / 1000000000) (Real.log (119873 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (84386843 / 250000000) ≤ -Real.log (500000 / 700753) ∧
    -Real.log (500000 / 700753) ≤ (337547373 / 1000000000) := by
  have h := checkLog_sound (w := (200753 / 1200753)) (n := 12)
    (lo := (84386843 / 250000000)) (hi := (337547373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((700753 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(700753 / 500000) = 1/(500000 / 700753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (84386843 / 250000000) (337547373 / 1000000000) (Real.log (700753 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (700753 / 500000) = -Real.log (500000 / 700753) := by
    rw [show ((700753 / 500000) : ℝ) = ((500000 / 700753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (513338779 / 1000000000) ≤ -Real.log (299247 / 500000) ∧
    -Real.log (299247 / 500000) ≤ (25666939 / 50000000) := by
  have h := checkLog_sound (w := (200753 / 799247)) (n := 12)
    (lo := (513338779 / 1000000000)) (hi := (25666939 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 299247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 299247) = 1/(299247 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-25666939 / 50000000) (-513338779 / 1000000000) (Real.log (299247 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (129813337 / 500000000) ≤ -Real.log (500000 / 648223) ∧
    -Real.log (500000 / 648223) ≤ (10385067 / 40000000) := by
  have h := checkLog_sound (w := (148223 / 1148223)) (n := 12)
    (lo := (129813337 / 500000000)) (hi := (10385067 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((648223 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(648223 / 500000) = 1/(500000 / 648223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (129813337 / 500000000) (10385067 / 40000000) (Real.log (648223 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (648223 / 500000) = -Real.log (500000 / 648223) := by
    rw [show ((648223 / 500000) : ℝ) = ((500000 / 648223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (175805323 / 500000000) ≤ -Real.log (351777 / 500000) ∧
    -Real.log (351777 / 500000) ≤ (351610647 / 1000000000) := by
  have h := checkLog_sound (w := (148223 / 851777)) (n := 12)
    (lo := (175805323 / 500000000)) (hi := (351610647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 351777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 351777) = 1/(351777 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-351610647 / 1000000000) (-175805323 / 500000000) (Real.log (351777 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (5203391 / 20000000) ≤ -Real.log (20000 / 25943) ∧
    -Real.log (20000 / 25943) ≤ (260169551 / 1000000000) := by
  have h := checkLog_sound (w := (5943 / 45943)) (n := 12)
    (lo := (5203391 / 20000000)) (hi := (260169551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25943 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25943 / 20000) = 1/(20000 / 25943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (5203391 / 20000000) (260169551 / 1000000000) (Real.log (25943 / 20000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (25943 / 20000) = -Real.log (20000 / 25943) := by
    rw [show ((25943 / 20000) : ℝ) = ((20000 / 25943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (352611781 / 1000000000) ≤ -Real.log (14057 / 20000) ∧
    -Real.log (14057 / 20000) ≤ (176305891 / 500000000) := by
  have h := checkLog_sound (w := (5943 / 34057)) (n := 12)
    (lo := (352611781 / 1000000000)) (hi := (176305891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 14057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 14057) = 1/(14057 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-176305891 / 500000000) (-352611781 / 1000000000) (Real.log (14057 / 20000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (424405111 / 500000000) ≤ -Real.log (100000000000 / 233686484863) ∧
    -Real.log (100000000000 / 233686484863) ≤ (53050639 / 62500000) := by
  have h := checkLog_sound (w := (33686484863 / 433686484863)) (n := 12)
    (lo := (77831521 / 500000000)) (hi := (155663043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233686484863 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(233686484863 / 200000000000) = 1/(100000000000 / 233686484863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (424405111 / 500000000) (53050639 / 62500000) (Real.log (233686484863 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (233686484863 / 100000000000) = -Real.log (100000000000 / 233686484863) := by
    rw [show ((233686484863 / 100000000000) : ℝ) = ((100000000000 / 233686484863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (850886151 / 1000000000) ≤ -Real.log (500000000000 / 1170860526589) ∧
    -Real.log (500000000000 / 1170860526589) ≤ (850886153 / 1000000000) := by
  have h := checkLog_sound (w := (170860526589 / 2170860526589)) (n := 12)
    (lo := (157738971 / 1000000000)) (hi := (39434743 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1170860526589 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1170860526589 / 1000000000000) = 1/(500000000000 / 1170860526589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (850886151 / 1000000000) (850886153 / 1000000000) (Real.log (1170860526589 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1170860526589 / 500000000000) = -Real.log (500000000000 / 1170860526589) := by
    rw [show ((1170860526589 / 500000000000) : ℝ) = ((500000000000 / 1170860526589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (15280933 / 25000000) ≤ -Real.log (250000000000 / 460677503077) ∧
    -Real.log (250000000000 / 460677503077) ≤ (611237321 / 1000000000) := by
  have h := checkLog_sound (w := (210677503077 / 710677503077)) (n := 12)
    (lo := (15280933 / 25000000)) (hi := (611237321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((460677503077 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(460677503077 / 250000000000) = 1/(250000000000 / 460677503077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (15280933 / 25000000) (611237321 / 1000000000) (Real.log (460677503077 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (460677503077 / 250000000000) = -Real.log (250000000000 / 460677503077) := by
    rw [show ((460677503077 / 250000000000) : ℝ) = ((250000000000 / 460677503077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (612781331 / 1000000000) ≤ -Real.log (62500000000 / 115347335847) ∧
    -Real.log (62500000000 / 115347335847) ≤ (153195333 / 250000000) := by
  have h := checkLog_sound (w := (52847335847 / 177847335847)) (n := 12)
    (lo := (612781331 / 1000000000)) (hi := (153195333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((115347335847 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(115347335847 / 62500000000) = 1/(62500000000 / 115347335847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (612781331 / 1000000000) (153195333 / 250000000) (Real.log (115347335847 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (115347335847 / 62500000000) = -Real.log (62500000000 / 115347335847) := by
    rw [show ((115347335847 / 62500000000) : ℝ) = ((62500000000 / 115347335847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0242

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0243Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0243
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

theorem reflection_log_1_neg : (246157927 / 1000000000) ≤ -Real.log (5120 / 6549) ∧
    -Real.log (5120 / 6549) ≤ (30769741 / 125000000) := by
  have h := checkLog_sound (w := (1429 / 11669)) (n := 12)
    (lo := (246157927 / 1000000000)) (hi := (30769741 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6549 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6549 / 5120) = 1/(5120 / 6549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (246157927 / 1000000000) (30769741 / 125000000) (Real.log (6549 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6549 / 5120) = -Real.log (5120 / 6549) := by
    rw [show ((6549 / 5120) : ℝ) = ((5120 / 6549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (65451403 / 200000000) ≤ -Real.log (3691 / 5120) ∧
    -Real.log (3691 / 5120) ≤ (40907127 / 125000000) := by
  have h := checkLog_sound (w := (1429 / 8811)) (n := 12)
    (lo := (65451403 / 200000000)) (hi := (40907127 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3691) = 1/(3691 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-40907127 / 125000000) (-65451403 / 200000000) (Real.log (3691 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (245699737 / 1000000000) ≤ -Real.log (2560 / 3273) ∧
    -Real.log (2560 / 3273) ≤ (122849869 / 500000000) := by
  have h := checkLog_sound (w := (713 / 5833)) (n := 12)
    (lo := (245699737 / 1000000000)) (hi := (122849869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3273 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3273 / 2560) = 1/(2560 / 3273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (245699737 / 1000000000) (122849869 / 500000000) (Real.log (3273 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3273 / 2560) = -Real.log (2560 / 3273) := by
    rw [show ((3273 / 2560) : ℝ) = ((2560 / 3273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (326444557 / 1000000000) ≤ -Real.log (1847 / 2560) ∧
    -Real.log (1847 / 2560) ≤ (163222279 / 500000000) := by
  have h := checkLog_sound (w := (713 / 4407)) (n := 12)
    (lo := (326444557 / 1000000000)) (hi := (163222279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1847) = 1/(1847 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-163222279 / 500000000) (-326444557 / 1000000000) (Real.log (1847 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (221766657 / 500000000) ≤ -Real.log (2560 / 3989) ∧
    -Real.log (2560 / 3989) ≤ (88706663 / 200000000) := by
  have h := checkLog_sound (w := (1429 / 6549)) (n := 12)
    (lo := (221766657 / 500000000)) (hi := (88706663 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3989 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3989 / 2560) = 1/(2560 / 3989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (221766657 / 500000000) (88706663 / 200000000) (Real.log (3989 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3989 / 2560) = -Real.log (2560 / 3989) := by
    rw [show ((3989 / 2560) : ℝ) = ((2560 / 3989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (40845253 / 50000000) ≤ -Real.log (1131 / 2560) ∧
    -Real.log (1131 / 2560) ≤ (408452531 / 500000000) := by
  have h := checkLog_sound (w := (149 / 2411)) (n := 12)
    (lo := (3093947 / 25000000)) (hi := (123757881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1131) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1131) = 1/(1131 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-408452531 / 500000000) (-40845253 / 50000000) (Real.log (1131 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (442780963 / 1000000000) ≤ -Real.log (1280 / 1993) ∧
    -Real.log (1280 / 1993) ≤ (110695241 / 250000000) := by
  have h := checkLog_sound (w := (713 / 3273)) (n := 12)
    (lo := (442780963 / 1000000000)) (hi := (110695241 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1993 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1993 / 1280) = 1/(1280 / 1993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (442780963 / 1000000000) (110695241 / 250000000) (Real.log (1993 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1993 / 1280) = -Real.log (1280 / 1993) := by
    rw [show ((1993 / 1280) : ℝ) = ((1280 / 1993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (203564013 / 250000000) ≤ -Real.log (567 / 1280) ∧
    -Real.log (567 / 1280) ≤ (407128027 / 500000000) := by
  have h := checkLog_sound (w := (73 / 1207)) (n := 12)
    (lo := (15138609 / 125000000)) (hi := (121108873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 567) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 567) = 1/(567 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-407128027 / 500000000) (-203564013 / 250000000) (Real.log (567 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (67260873 / 200000000) ≤ -Real.log (200000 / 279953) ∧
    -Real.log (200000 / 279953) ≤ (168152183 / 500000000) := by
  have h := checkLog_sound (w := (79953 / 479953)) (n := 12)
    (lo := (67260873 / 200000000)) (hi := (168152183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279953 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(279953 / 200000) = 1/(200000 / 279953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (67260873 / 200000000) (168152183 / 500000000) (Real.log (279953 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (279953 / 200000) = -Real.log (200000 / 279953) := by
    rw [show ((279953 / 200000) : ℝ) = ((200000 / 279953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (510434033 / 1000000000) ≤ -Real.log (120047 / 200000) ∧
    -Real.log (120047 / 200000) ≤ (255217017 / 500000000) := by
  have h := checkLog_sound (w := (79953 / 320047)) (n := 12)
    (lo := (510434033 / 1000000000)) (hi := (255217017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 120047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 120047) = 1/(120047 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-255217017 / 500000000) (-510434033 / 1000000000) (Real.log (120047 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (336926419 / 1000000000) ≤ -Real.log (250000 / 350159) ∧
    -Real.log (250000 / 350159) ≤ (16846321 / 50000000) := by
  have h := checkLog_sound (w := (100159 / 600159)) (n := 12)
    (lo := (336926419 / 1000000000)) (hi := (16846321 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((350159 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(350159 / 250000) = 1/(250000 / 350159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (336926419 / 1000000000) (16846321 / 50000000) (Real.log (350159 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (350159 / 250000) = -Real.log (250000 / 350159) := by
    rw [show ((350159 / 250000) : ℝ) = ((250000 / 350159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (102377237 / 200000000) ≤ -Real.log (149841 / 250000) ∧
    -Real.log (149841 / 250000) ≤ (255943093 / 500000000) := by
  have h := checkLog_sound (w := (100159 / 399841)) (n := 12)
    (lo := (102377237 / 200000000)) (hi := (255943093 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 149841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 149841) = 1/(149841 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-255943093 / 500000000) (-102377237 / 200000000) (Real.log (149841 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (16192719 / 62500000) ≤ -Real.log (500000 / 647871) ∧
    -Real.log (500000 / 647871) ≤ (51816701 / 200000000) := by
  have h := checkLog_sound (w := (147871 / 1147871)) (n := 12)
    (lo := (16192719 / 62500000)) (hi := (51816701 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((647871 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(647871 / 500000) = 1/(500000 / 647871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (16192719 / 62500000) (51816701 / 200000000) (Real.log (647871 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (647871 / 500000) = -Real.log (500000 / 647871) := by
    rw [show ((647871 / 500000) : ℝ) = ((500000 / 647871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (21913157 / 62500000) ≤ -Real.log (352129 / 500000) ∧
    -Real.log (352129 / 500000) ≤ (350610513 / 1000000000) := by
  have h := checkLog_sound (w := (147871 / 852129)) (n := 12)
    (lo := (21913157 / 62500000)) (hi := (350610513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 352129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 352129) = 1/(352129 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-350610513 / 1000000000) (-21913157 / 62500000) (Real.log (352129 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (51925489 / 200000000) ≤ -Real.log (1000000 / 1296447) ∧
    -Real.log (1000000 / 1296447) ≤ (129813723 / 500000000) := by
  have h := checkLog_sound (w := (296447 / 2296447)) (n := 12)
    (lo := (51925489 / 200000000)) (hi := (129813723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1296447 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1296447 / 1000000) = 1/(1000000 / 1296447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (51925489 / 200000000) (129813723 / 500000000) (Real.log (1296447 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1296447 / 1000000) = -Real.log (1000000 / 1296447) := by
    rw [show ((1296447 / 1000000) : ℝ) = ((1000000 / 1296447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (351612067 / 1000000000) ≤ -Real.log (703553 / 1000000) ∧
    -Real.log (703553 / 1000000) ≤ (87903017 / 250000000) := by
  have h := checkLog_sound (w := (296447 / 1703553)) (n := 12)
    (lo := (351612067 / 1000000000)) (hi := (87903017 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 703553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 703553) = 1/(703553 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-87903017 / 250000000) (-351612067 / 1000000000) (Real.log (703553 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (423369199 / 500000000) ≤ -Real.log (25000000000 / 58300707223) ∧
    -Real.log (25000000000 / 58300707223) ≤ (1058423 / 1250000) := by
  have h := checkLog_sound (w := (8300707223 / 108300707223)) (n := 12)
    (lo := (76795609 / 500000000)) (hi := (153591219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58300707223 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(58300707223 / 50000000000) = 1/(25000000000 / 58300707223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (423369199 / 500000000) (1058423 / 1250000) (Real.log (58300707223 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (58300707223 / 25000000000) = -Real.log (25000000000 / 58300707223) := by
    rw [show ((58300707223 / 25000000000) : ℝ) = ((25000000000 / 58300707223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (212203151 / 250000000) ≤ -Real.log (125000000000 / 292108801997) ∧
    -Real.log (125000000000 / 292108801997) ≤ (424406303 / 500000000) := by
  have h := checkLog_sound (w := (42108801997 / 542108801997)) (n := 12)
    (lo := (9729089 / 62500000)) (hi := (6226617 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292108801997 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(292108801997 / 250000000000) = 1/(125000000000 / 292108801997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (212203151 / 250000000) (424406303 / 500000000) (Real.log (292108801997 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (292108801997 / 125000000000) = -Real.log (125000000000 / 292108801997) := by
    rw [show ((292108801997 / 125000000000) : ℝ) = ((125000000000 / 292108801997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9526469 / 15625000) ≤ -Real.log (500000000000 / 919934171851) ∧
    -Real.log (500000000000 / 919934171851) ≤ (609694017 / 1000000000) := by
  have h := checkLog_sound (w := (419934171851 / 1419934171851)) (n := 12)
    (lo := (9526469 / 15625000)) (hi := (609694017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((919934171851 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(919934171851 / 500000000000) = 1/(500000000000 / 919934171851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (9526469 / 15625000) (609694017 / 1000000000) (Real.log (919934171851 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (919934171851 / 500000000000) = -Real.log (500000000000 / 919934171851) := by
    rw [show ((919934171851 / 500000000000) : ℝ) = ((500000000000 / 919934171851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (611239513 / 1000000000) ≤ -Real.log (62500000000 / 115169628301) ∧
    -Real.log (62500000000 / 115169628301) ≤ (305619757 / 500000000) := by
  have h := checkLog_sound (w := (52669628301 / 177669628301)) (n := 12)
    (lo := (611239513 / 1000000000)) (hi := (305619757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((115169628301 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(115169628301 / 62500000000) = 1/(62500000000 / 115169628301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (611239513 / 1000000000) (305619757 / 500000000) (Real.log (115169628301 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (115169628301 / 62500000000) = -Real.log (62500000000 / 115169628301) := by
    rw [show ((115169628301 / 62500000000) : ℝ) = ((62500000000 / 115169628301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0243

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0244Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0244
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

theorem reflection_log_1_neg : (245699737 / 1000000000) ≤ -Real.log (2560 / 3273) ∧
    -Real.log (2560 / 3273) ≤ (122849869 / 500000000) := by
  have h := checkLog_sound (w := (713 / 5833)) (n := 12)
    (lo := (245699737 / 1000000000)) (hi := (122849869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3273 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3273 / 2560) = 1/(2560 / 3273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (245699737 / 1000000000) (122849869 / 500000000) (Real.log (3273 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3273 / 2560) = -Real.log (2560 / 3273) := by
    rw [show ((3273 / 2560) : ℝ) = ((2560 / 3273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (326444557 / 1000000000) ≤ -Real.log (1847 / 2560) ∧
    -Real.log (1847 / 2560) ≤ (163222279 / 500000000) := by
  have h := checkLog_sound (w := (713 / 4407)) (n := 12)
    (lo := (326444557 / 1000000000)) (hi := (163222279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1847) = 1/(1847 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-163222279 / 500000000) (-326444557 / 1000000000) (Real.log (1847 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (30655167 / 125000000) ≤ -Real.log (5120 / 6543) ∧
    -Real.log (5120 / 6543) ≤ (245241337 / 1000000000) := by
  have h := checkLog_sound (w := (1423 / 11663)) (n := 12)
    (lo := (30655167 / 125000000)) (hi := (245241337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6543 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6543 / 5120) = 1/(5120 / 6543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (30655167 / 125000000) (245241337 / 1000000000) (Real.log (6543 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6543 / 5120) = -Real.log (5120 / 6543) := by
    rw [show ((6543 / 5120) : ℝ) = ((5120 / 6543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (325632759 / 1000000000) ≤ -Real.log (3697 / 5120) ∧
    -Real.log (3697 / 5120) ≤ (8140819 / 25000000) := by
  have h := checkLog_sound (w := (1423 / 8817)) (n := 12)
    (lo := (325632759 / 1000000000)) (hi := (8140819 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3697) = 1/(3697 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-8140819 / 25000000) (-325632759 / 1000000000) (Real.log (3697 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (442780963 / 1000000000) ≤ -Real.log (1280 / 1993) ∧
    -Real.log (1280 / 1993) ≤ (110695241 / 250000000) := by
  have h := checkLog_sound (w := (713 / 3273)) (n := 12)
    (lo := (442780963 / 1000000000)) (hi := (110695241 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1993 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1993 / 1280) = 1/(1280 / 1993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (442780963 / 1000000000) (110695241 / 250000000) (Real.log (1993 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1993 / 1280) = -Real.log (1280 / 1993) := by
    rw [show ((1993 / 1280) : ℝ) = ((1280 / 1993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (203564013 / 250000000) ≤ -Real.log (567 / 1280) ∧
    -Real.log (567 / 1280) ≤ (407128027 / 500000000) := by
  have h := checkLog_sound (w := (73 / 1207)) (n := 12)
    (lo := (15138609 / 125000000)) (hi := (121108873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 567) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 567) = 1/(567 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-407128027 / 500000000) (-203564013 / 250000000) (Real.log (567 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (88405609 / 200000000) ≤ -Real.log (2560 / 3983) ∧
    -Real.log (2560 / 3983) ≤ (221014023 / 500000000) := by
  have h := checkLog_sound (w := (1423 / 6543)) (n := 12)
    (lo := (88405609 / 200000000)) (hi := (221014023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3983 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3983 / 2560) = 1/(2560 / 3983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (88405609 / 200000000) (221014023 / 500000000) (Real.log (3983 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3983 / 2560) = -Real.log (2560 / 3983) := by
    rw [show ((3983 / 2560) : ℝ) = ((2560 / 3983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (811614043 / 1000000000) ≤ -Real.log (1137 / 2560) ∧
    -Real.log (1137 / 2560) ≤ (162322809 / 200000000) := by
  have h := checkLog_sound (w := (143 / 2417)) (n := 12)
    (lo := (118466863 / 1000000000)) (hi := (7404179 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1137) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1137) = 1/(1137 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-162322809 / 200000000) (-811614043 / 1000000000) (Real.log (1137 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (335682639 / 1000000000) ≤ -Real.log (200000 / 279779) ∧
    -Real.log (200000 / 279779) ≤ (4196033 / 12500000) := by
  have h := checkLog_sound (w := (79779 / 479779)) (n := 12)
    (lo := (335682639 / 1000000000)) (hi := (4196033 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279779 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(279779 / 200000) = 1/(200000 / 279779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (335682639 / 1000000000) (4196033 / 12500000) (Real.log (279779 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (279779 / 200000) = -Real.log (200000 / 279779) := by
    rw [show ((279779 / 200000) : ℝ) = ((200000 / 279779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (10179713 / 20000000) ≤ -Real.log (120221 / 200000) ∧
    -Real.log (120221 / 200000) ≤ (508985651 / 1000000000) := by
  have h := checkLog_sound (w := (79779 / 320221)) (n := 12)
    (lo := (10179713 / 20000000)) (hi := (508985651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 120221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 120221) = 1/(120221 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-508985651 / 1000000000) (-10179713 / 20000000) (Real.log (120221 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (336305079 / 1000000000) ≤ -Real.log (500000 / 699883) ∧
    -Real.log (500000 / 699883) ≤ (8407627 / 25000000) := by
  have h := checkLog_sound (w := (199883 / 1199883)) (n := 12)
    (lo := (336305079 / 1000000000)) (hi := (8407627 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699883 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699883 / 500000) = 1/(500000 / 699883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (336305079 / 1000000000) (8407627 / 25000000) (Real.log (699883 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (699883 / 500000) = -Real.log (500000 / 699883) := by
    rw [show ((699883 / 500000) : ℝ) = ((500000 / 699883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (510435699 / 1000000000) ≤ -Real.log (300117 / 500000) ∧
    -Real.log (300117 / 500000) ≤ (5104357 / 10000000) := by
  have h := checkLog_sound (w := (199883 / 800117)) (n := 12)
    (lo := (510435699 / 1000000000)) (hi := (5104357 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 300117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 300117) = 1/(300117 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-5104357 / 10000000) (-510435699 / 1000000000) (Real.log (300117 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (129270791 / 500000000) ≤ -Real.log (3125 / 4047) ∧
    -Real.log (3125 / 4047) ≤ (258541583 / 1000000000) := by
  have h := checkLog_sound (w := (461 / 3586)) (n := 12)
    (lo := (129270791 / 500000000)) (hi := (258541583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4047 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4047 / 3125) = 1/(3125 / 4047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (129270791 / 500000000) (258541583 / 1000000000) (Real.log (4047 / 3125)) := by
  have h := reflection_log_13_neg
  have he : Real.log (4047 / 3125) = -Real.log (3125 / 4047) := by
    rw [show ((4047 / 3125) : ℝ) = ((3125 / 4047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (69922843 / 200000000) ≤ -Real.log (2203 / 3125) ∧
    -Real.log (2203 / 3125) ≤ (43701777 / 125000000) := by
  have h := checkLog_sound (w := (461 / 2664)) (n := 12)
    (lo := (69922843 / 200000000)) (hi := (43701777 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2203) = 1/(2203 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-43701777 / 125000000) (-69922843 / 200000000) (Real.log (2203 / 3125)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (10363371 / 40000000) ≤ -Real.log (1000000 / 1295743) ∧
    -Real.log (1000000 / 1295743) ≤ (64771069 / 250000000) := by
  have h := checkLog_sound (w := (295743 / 2295743)) (n := 12)
    (lo := (10363371 / 40000000)) (hi := (64771069 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1295743 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1295743 / 1000000) = 1/(1000000 / 1295743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (10363371 / 40000000) (64771069 / 250000000) (Real.log (1295743 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1295743 / 1000000) = -Real.log (1000000 / 1295743) := by
    rw [show ((1295743 / 1000000) : ℝ) = ((1000000 / 1295743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (87652983 / 250000000) ≤ -Real.log (704257 / 1000000) ∧
    -Real.log (704257 / 1000000) ≤ (350611933 / 1000000000) := by
  have h := checkLog_sound (w := (295743 / 1704257)) (n := 12)
    (lo := (87652983 / 250000000)) (hi := (350611933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 704257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 704257) = 1/(704257 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-350611933 / 1000000000) (-87652983 / 250000000) (Real.log (704257 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (844668289 / 1000000000) ≤ -Real.log (125000000000 / 290900716181) ∧
    -Real.log (125000000000 / 290900716181) ≤ (844668291 / 1000000000) := by
  have h := checkLog_sound (w := (40900716181 / 540900716181)) (n := 12)
    (lo := (151521109 / 1000000000)) (hi := (15152111 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((290900716181 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(290900716181 / 250000000000) = 1/(125000000000 / 290900716181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (844668289 / 1000000000) (844668291 / 1000000000) (Real.log (290900716181 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (290900716181 / 125000000000) = -Real.log (125000000000 / 290900716181) := by
    rw [show ((290900716181 / 125000000000) : ℝ) = ((125000000000 / 290900716181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (846740779 / 1000000000) ≤ -Real.log (125000000000 / 291504230017) ∧
    -Real.log (125000000000 / 291504230017) ≤ (846740781 / 1000000000) := by
  have h := checkLog_sound (w := (41504230017 / 541504230017)) (n := 12)
    (lo := (153593599 / 1000000000)) (hi := (23999 / 156250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291504230017 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(291504230017 / 250000000000) = 1/(125000000000 / 291504230017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (846740779 / 1000000000) (846740781 / 1000000000) (Real.log (291504230017 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (291504230017 / 125000000000) = -Real.log (125000000000 / 291504230017) := by
    rw [show ((291504230017 / 125000000000) : ℝ) = ((125000000000 / 291504230017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (304077899 / 500000000) ≤ -Real.log (500000000000 / 918520199727) ∧
    -Real.log (500000000000 / 918520199727) ≤ (608155799 / 1000000000) := by
  have h := checkLog_sound (w := (418520199727 / 1418520199727)) (n := 12)
    (lo := (304077899 / 500000000)) (hi := (608155799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((918520199727 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(918520199727 / 500000000000) = 1/(500000000000 / 918520199727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (304077899 / 500000000) (608155799 / 1000000000) (Real.log (918520199727 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (918520199727 / 500000000000) = -Real.log (500000000000 / 918520199727) := by
    rw [show ((918520199727 / 500000000000) : ℝ) = ((500000000000 / 918520199727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (38106013 / 62500000) ≤ -Real.log (125000000000 / 229984047017) ∧
    -Real.log (125000000000 / 229984047017) ≤ (609696209 / 1000000000) := by
  have h := checkLog_sound (w := (104984047017 / 354984047017)) (n := 12)
    (lo := (38106013 / 62500000)) (hi := (609696209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229984047017 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(229984047017 / 125000000000) = 1/(125000000000 / 229984047017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (38106013 / 62500000) (609696209 / 1000000000) (Real.log (229984047017 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (229984047017 / 125000000000) = -Real.log (125000000000 / 229984047017) := by
    rw [show ((229984047017 / 125000000000) : ℝ) = ((125000000000 / 229984047017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0244

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0245Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0245
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

theorem reflection_log_1_neg : (30655167 / 125000000) ≤ -Real.log (5120 / 6543) ∧
    -Real.log (5120 / 6543) ≤ (245241337 / 1000000000) := by
  have h := checkLog_sound (w := (1423 / 11663)) (n := 12)
    (lo := (30655167 / 125000000)) (hi := (245241337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6543 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6543 / 5120) = 1/(5120 / 6543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (30655167 / 125000000) (245241337 / 1000000000) (Real.log (6543 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6543 / 5120) = -Real.log (5120 / 6543) := by
    rw [show ((6543 / 5120) : ℝ) = ((5120 / 6543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (325632759 / 1000000000) ≤ -Real.log (3697 / 5120) ∧
    -Real.log (3697 / 5120) ≤ (8140819 / 25000000) := by
  have h := checkLog_sound (w := (1423 / 8817)) (n := 12)
    (lo := (325632759 / 1000000000)) (hi := (8140819 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3697) = 1/(3697 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-8140819 / 25000000) (-325632759 / 1000000000) (Real.log (3697 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (122391363 / 500000000) ≤ -Real.log (256 / 327) ∧
    -Real.log (256 / 327) ≤ (244782727 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 583)) (n := 12)
    (lo := (122391363 / 500000000)) (hi := (244782727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((327 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(327 / 256) = 1/(256 / 327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (122391363 / 500000000) (244782727 / 1000000000) (Real.log (327 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (327 / 256) = -Real.log (256 / 327) := by
    rw [show ((327 / 256) : ℝ) = ((256 / 327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (324821619 / 1000000000) ≤ -Real.log (185 / 256) ∧
    -Real.log (185 / 256) ≤ (16241081 / 50000000) := by
  have h := checkLog_sound (w := (71 / 441)) (n := 12)
    (lo := (324821619 / 1000000000)) (hi := (16241081 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 185) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 185) = 1/(185 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-16241081 / 50000000) (-324821619 / 1000000000) (Real.log (185 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (88405609 / 200000000) ≤ -Real.log (2560 / 3983) ∧
    -Real.log (2560 / 3983) ≤ (221014023 / 500000000) := by
  have h := checkLog_sound (w := (1423 / 6543)) (n := 12)
    (lo := (88405609 / 200000000)) (hi := (221014023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3983 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3983 / 2560) = 1/(2560 / 3983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (88405609 / 200000000) (221014023 / 500000000) (Real.log (3983 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3983 / 2560) = -Real.log (2560 / 3983) := by
    rw [show ((3983 / 2560) : ℝ) = ((2560 / 3983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (811614043 / 1000000000) ≤ -Real.log (1137 / 2560) ∧
    -Real.log (1137 / 2560) ≤ (162322809 / 200000000) := by
  have h := checkLog_sound (w := (143 / 2417)) (n := 12)
    (lo := (118466863 / 1000000000)) (hi := (7404179 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1137) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1137) = 1/(1137 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-162322809 / 200000000) (-811614043 / 1000000000) (Real.log (1137 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (1378983 / 3125000) ≤ -Real.log (128 / 199) ∧
    -Real.log (128 / 199) ≤ (441274561 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 327)) (n := 12)
    (lo := (1378983 / 3125000)) (hi := (441274561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((199 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(199 / 128) = 1/(128 / 199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (1378983 / 3125000) (441274561 / 1000000000) (Real.log (199 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (199 / 128) = -Real.log (128 / 199) := by
    rw [show ((199 / 128) : ℝ) = ((128 / 199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (161795799 / 200000000) ≤ -Real.log (57 / 128) ∧
    -Real.log (57 / 128) ≤ (808978997 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 121)) (n := 12)
    (lo := (23166363 / 200000000)) (hi := (14478977 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 57) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 57) = 1/(57 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-808978997 / 1000000000) (-161795799 / 200000000) (Real.log (57 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (167530263 / 500000000) ≤ -Real.log (40000 / 55921) ∧
    -Real.log (40000 / 55921) ≤ (335060527 / 1000000000) := by
  have h := checkLog_sound (w := (15921 / 95921)) (n := 12)
    (lo := (167530263 / 500000000)) (hi := (335060527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55921 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55921 / 40000) = 1/(40000 / 55921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (167530263 / 500000000) (335060527 / 1000000000) (Real.log (55921 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (55921 / 40000) = -Real.log (40000 / 55921) := by
    rw [show ((55921 / 40000) : ℝ) = ((40000 / 55921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (253769681 / 500000000) ≤ -Real.log (24079 / 40000) ∧
    -Real.log (24079 / 40000) ≤ (507539363 / 1000000000) := by
  have h := checkLog_sound (w := (15921 / 64079)) (n := 12)
    (lo := (253769681 / 500000000)) (hi := (507539363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 24079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 24079) = 1/(24079 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-507539363 / 1000000000) (-253769681 / 500000000) (Real.log (24079 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (167841677 / 500000000) ≤ -Real.log (62500 / 87431) ∧
    -Real.log (62500 / 87431) ≤ (67136671 / 200000000) := by
  have h := checkLog_sound (w := (24931 / 149931)) (n := 12)
    (lo := (167841677 / 500000000)) (hi := (67136671 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87431 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87431 / 62500) = 1/(62500 / 87431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (167841677 / 500000000) (67136671 / 200000000) (Real.log (87431 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (87431 / 62500) = -Real.log (62500 / 87431) := by
    rw [show ((87431 / 62500) : ℝ) = ((62500 / 87431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (254493657 / 500000000) ≤ -Real.log (37569 / 62500) ∧
    -Real.log (37569 / 62500) ≤ (101797463 / 200000000) := by
  have h := checkLog_sound (w := (24931 / 100069)) (n := 12)
    (lo := (254493657 / 500000000)) (hi := (101797463 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 37569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 37569) = 1/(37569 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-101797463 / 200000000) (-254493657 / 500000000) (Real.log (37569 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (257999367 / 1000000000) ≤ -Real.log (500000 / 647169) ∧
    -Real.log (500000 / 647169) ≤ (32249921 / 125000000) := by
  have h := checkLog_sound (w := (147169 / 1147169)) (n := 12)
    (lo := (257999367 / 1000000000)) (hi := (32249921 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((647169 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(647169 / 500000) = 1/(500000 / 647169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (257999367 / 1000000000) (32249921 / 125000000) (Real.log (647169 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (647169 / 500000) = -Real.log (500000 / 647169) := by
    rw [show ((647169 / 500000) : ℝ) = ((500000 / 647169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (348618909 / 1000000000) ≤ -Real.log (352831 / 500000) ∧
    -Real.log (352831 / 500000) ≤ (34861891 / 100000000) := by
  have h := checkLog_sound (w := (147169 / 852831)) (n := 12)
    (lo := (348618909 / 1000000000)) (hi := (34861891 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 352831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 352831) = 1/(352831 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-34861891 / 100000000) (-348618909 / 1000000000) (Real.log (352831 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (129271177 / 500000000) ≤ -Real.log (1000000 / 1295041) ∧
    -Real.log (1000000 / 1295041) ≤ (51708471 / 200000000) := by
  have h := checkLog_sound (w := (295041 / 2295041)) (n := 12)
    (lo := (129271177 / 500000000)) (hi := (51708471 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1295041 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1295041 / 1000000) = 1/(1000000 / 1295041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (129271177 / 500000000) (51708471 / 200000000) (Real.log (1295041 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1295041 / 1000000) = -Real.log (1000000 / 1295041) := by
    rw [show ((1295041 / 1000000) : ℝ) = ((1000000 / 1295041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (349615633 / 1000000000) ≤ -Real.log (704959 / 1000000) ∧
    -Real.log (704959 / 1000000) ≤ (174807817 / 500000000) := by
  have h := checkLog_sound (w := (295041 / 1704959)) (n := 12)
    (lo := (349615633 / 1000000000)) (hi := (174807817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 704959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 704959) = 1/(704959 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-174807817 / 500000000) (-349615633 / 1000000000) (Real.log (704959 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (52662493 / 62500000) ≤ -Real.log (500000000000 / 1161198554757) ∧
    -Real.log (500000000000 / 1161198554757) ≤ (84259989 / 100000000) := by
  have h := checkLog_sound (w := (161198554757 / 2161198554757)) (n := 12)
    (lo := (37363177 / 250000000)) (hi := (149452709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161198554757 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1161198554757 / 1000000000000) = 1/(500000000000 / 1161198554757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (52662493 / 62500000) (84259989 / 100000000) (Real.log (1161198554757 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1161198554757 / 500000000000) = -Real.log (500000000000 / 1161198554757) := by
    rw [show ((1161198554757 / 500000000000) : ℝ) = ((500000000000 / 1161198554757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (211167667 / 250000000) ≤ -Real.log (31250000000 / 72725352019) ∧
    -Real.log (31250000000 / 72725352019) ≤ (84467067 / 100000000) := by
  have h := checkLog_sound (w := (10225352019 / 135225352019)) (n := 12)
    (lo := (4735109 / 31250000)) (hi := (151523489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72725352019 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(72725352019 / 62500000000) = 1/(31250000000 / 72725352019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (211167667 / 250000000) (84467067 / 100000000) (Real.log (72725352019 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (72725352019 / 31250000000) = -Real.log (31250000000 / 72725352019) := by
    rw [show ((72725352019 / 31250000000) : ℝ) = ((31250000000 / 72725352019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (606618277 / 1000000000) ≤ -Real.log (62500000000 / 114638630109) ∧
    -Real.log (62500000000 / 114638630109) ≤ (303309139 / 500000000) := by
  have h := checkLog_sound (w := (52138630109 / 177138630109)) (n := 12)
    (lo := (606618277 / 1000000000)) (hi := (303309139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114638630109 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(114638630109 / 62500000000) = 1/(62500000000 / 114638630109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (606618277 / 1000000000) (303309139 / 500000000) (Real.log (114638630109 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (114638630109 / 62500000000) = -Real.log (62500000000 / 114638630109) := by
    rw [show ((114638630109 / 62500000000) : ℝ) = ((62500000000 / 114638630109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (152039497 / 250000000) ≤ -Real.log (500000000000 / 918522211931) ∧
    -Real.log (500000000000 / 918522211931) ≤ (608157989 / 1000000000) := by
  have h := checkLog_sound (w := (418522211931 / 1418522211931)) (n := 12)
    (lo := (152039497 / 250000000)) (hi := (608157989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((918522211931 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(918522211931 / 500000000000) = 1/(500000000000 / 918522211931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (152039497 / 250000000) (608157989 / 1000000000) (Real.log (918522211931 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (918522211931 / 500000000000) = -Real.log (500000000000 / 918522211931) := by
    rw [show ((918522211931 / 500000000000) : ℝ) = ((500000000000 / 918522211931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0245

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0246Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0246
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

theorem reflection_log_1_neg : (122391363 / 500000000) ≤ -Real.log (256 / 327) ∧
    -Real.log (256 / 327) ≤ (244782727 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 583)) (n := 12)
    (lo := (122391363 / 500000000)) (hi := (244782727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((327 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(327 / 256) = 1/(256 / 327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (122391363 / 500000000) (244782727 / 1000000000) (Real.log (327 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (327 / 256) = -Real.log (256 / 327) := by
    rw [show ((327 / 256) : ℝ) = ((256 / 327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (324821619 / 1000000000) ≤ -Real.log (185 / 256) ∧
    -Real.log (185 / 256) ≤ (16241081 / 50000000) := by
  have h := checkLog_sound (w := (71 / 441)) (n := 12)
    (lo := (324821619 / 1000000000)) (hi := (16241081 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 185) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 185) = 1/(185 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-16241081 / 50000000) (-324821619 / 1000000000) (Real.log (185 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (48864781 / 200000000) ≤ -Real.log (5120 / 6537) ∧
    -Real.log (5120 / 6537) ≤ (122161953 / 500000000) := by
  have h := checkLog_sound (w := (1417 / 11657)) (n := 12)
    (lo := (48864781 / 200000000)) (hi := (122161953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6537 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6537 / 5120) = 1/(5120 / 6537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (48864781 / 200000000) (122161953 / 500000000) (Real.log (6537 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6537 / 5120) = -Real.log (5120 / 6537) := by
    rw [show ((6537 / 5120) : ℝ) = ((5120 / 6537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (324011137 / 1000000000) ≤ -Real.log (3703 / 5120) ∧
    -Real.log (3703 / 5120) ≤ (162005569 / 500000000) := by
  have h := checkLog_sound (w := (1417 / 8823)) (n := 12)
    (lo := (324011137 / 1000000000)) (hi := (162005569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3703) = 1/(3703 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-162005569 / 500000000) (-324011137 / 1000000000) (Real.log (3703 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (1378983 / 3125000) ≤ -Real.log (128 / 199) ∧
    -Real.log (128 / 199) ≤ (441274561 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 327)) (n := 12)
    (lo := (1378983 / 3125000)) (hi := (441274561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((199 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(199 / 128) = 1/(128 / 199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (1378983 / 3125000) (441274561 / 1000000000) (Real.log (199 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (199 / 128) = -Real.log (128 / 199) := by
    rw [show ((199 / 128) : ℝ) = ((128 / 199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (161795799 / 200000000) ≤ -Real.log (57 / 128) ∧
    -Real.log (57 / 128) ≤ (808978997 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 121)) (n := 12)
    (lo := (23166363 / 200000000)) (hi := (14478977 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 57) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 57) = 1/(57 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-808978997 / 1000000000) (-161795799 / 200000000) (Real.log (57 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (440520507 / 1000000000) ≤ -Real.log (2560 / 3977) ∧
    -Real.log (2560 / 3977) ≤ (110130127 / 250000000) := by
  have h := checkLog_sound (w := (1417 / 6537)) (n := 12)
    (lo := (440520507 / 1000000000)) (hi := (110130127 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3977 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3977 / 2560) = 1/(2560 / 3977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (440520507 / 1000000000) (110130127 / 250000000) (Real.log (3977 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3977 / 2560) = -Real.log (2560 / 3977) := by
    rw [show ((3977 / 2560) : ℝ) = ((2560 / 3977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (806350873 / 1000000000) ≤ -Real.log (1143 / 2560) ∧
    -Real.log (1143 / 2560) ≤ (6450807 / 8000000) := by
  have h := checkLog_sound (w := (137 / 2423)) (n := 12)
    (lo := (113203693 / 1000000000)) (hi := (56601847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1143) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1143) = 1/(1143 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-6450807 / 8000000) (-806350873 / 1000000000) (Real.log (1143 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (334438741 / 1000000000) ≤ -Real.log (250000 / 349289) ∧
    -Real.log (250000 / 349289) ≤ (167219371 / 500000000) := by
  have h := checkLog_sound (w := (99289 / 599289)) (n := 12)
    (lo := (334438741 / 1000000000)) (hi := (167219371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349289 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349289 / 250000) = 1/(250000 / 349289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (334438741 / 1000000000) (167219371 / 500000000) (Real.log (349289 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (349289 / 250000) = -Real.log (250000 / 349289) := by
    rw [show ((349289 / 250000) : ℝ) = ((250000 / 349289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (253048411 / 500000000) ≤ -Real.log (150711 / 250000) ∧
    -Real.log (150711 / 250000) ≤ (506096823 / 1000000000) := by
  have h := checkLog_sound (w := (99289 / 400711)) (n := 12)
    (lo := (253048411 / 500000000)) (hi := (506096823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 150711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 150711) = 1/(150711 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-506096823 / 1000000000) (-253048411 / 500000000) (Real.log (150711 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (335061241 / 1000000000) ≤ -Real.log (500000 / 699013) ∧
    -Real.log (500000 / 699013) ≤ (167530621 / 500000000) := by
  have h := checkLog_sound (w := (199013 / 1199013)) (n := 12)
    (lo := (335061241 / 1000000000)) (hi := (167530621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699013 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699013 / 500000) = 1/(500000 / 699013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (335061241 / 1000000000) (167530621 / 500000000) (Real.log (699013 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (699013 / 500000) = -Real.log (500000 / 699013) := by
    rw [show ((699013 / 500000) : ℝ) = ((500000 / 699013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (507541023 / 1000000000) ≤ -Real.log (300987 / 500000) ∧
    -Real.log (300987 / 500000) ≤ (15860657 / 31250000) := by
  have h := checkLog_sound (w := (199013 / 800987)) (n := 12)
    (lo := (507541023 / 1000000000)) (hi := (15860657 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 300987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 300987) = 1/(300987 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-15860657 / 31250000) (-507541023 / 1000000000) (Real.log (300987 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (257457631 / 1000000000) ≤ -Real.log (1000000 / 1293637) ∧
    -Real.log (1000000 / 1293637) ≤ (8045551 / 31250000) := by
  have h := checkLog_sound (w := (293637 / 2293637)) (n := 12)
    (lo := (257457631 / 1000000000)) (hi := (8045551 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1293637 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1293637 / 1000000) = 1/(1000000 / 1293637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (257457631 / 1000000000) (8045551 / 31250000) (Real.log (1293637 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1293637 / 1000000) = -Real.log (1000000 / 1293637) := by
    rw [show ((1293637 / 1000000) : ℝ) = ((1000000 / 1293637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (347626009 / 1000000000) ≤ -Real.log (706363 / 1000000) ∧
    -Real.log (706363 / 1000000) ≤ (34762601 / 100000000) := by
  have h := checkLog_sound (w := (293637 / 1706363)) (n := 12)
    (lo := (347626009 / 1000000000)) (hi := (34762601 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 706363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 706363) = 1/(706363 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-34762601 / 100000000) (-347626009 / 1000000000) (Real.log (706363 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (12900007 / 50000000) ≤ -Real.log (1000000 / 1294339) ∧
    -Real.log (1000000 / 1294339) ≤ (258000141 / 1000000000) := by
  have h := checkLog_sound (w := (294339 / 2294339)) (n := 12)
    (lo := (12900007 / 50000000)) (hi := (258000141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1294339 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1294339 / 1000000) = 1/(1000000 / 1294339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (12900007 / 50000000) (258000141 / 1000000000) (Real.log (1294339 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1294339 / 1000000) = -Real.log (1000000 / 1294339) := by
    rw [show ((1294339 / 1000000) : ℝ) = ((1000000 / 1294339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (174310163 / 500000000) ≤ -Real.log (705661 / 1000000) ∧
    -Real.log (705661 / 1000000) ≤ (348620327 / 1000000000) := by
  have h := checkLog_sound (w := (294339 / 1705661)) (n := 12)
    (lo := (174310163 / 500000000)) (hi := (348620327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 705661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 705661) = 1/(705661 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-348620327 / 1000000000) (-174310163 / 500000000) (Real.log (705661 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (840535563 / 1000000000) ≤ -Real.log (500000000000 / 1158803936009) ∧
    -Real.log (500000000000 / 1158803936009) ≤ (168107113 / 200000000) := by
  have h := checkLog_sound (w := (158803936009 / 2158803936009)) (n := 12)
    (lo := (147388383 / 1000000000)) (hi := (4605887 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1158803936009 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1158803936009 / 1000000000000) = 1/(500000000000 / 1158803936009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (840535563 / 1000000000) (168107113 / 200000000) (Real.log (1158803936009 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1158803936009 / 500000000000) = -Real.log (500000000000 / 1158803936009) := by
    rw [show ((1158803936009 / 500000000000) : ℝ) = ((500000000000 / 1158803936009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (168520453 / 200000000) ≤ -Real.log (500000000000 / 1161201314343) ∧
    -Real.log (500000000000 / 1161201314343) ≤ (842602267 / 1000000000) := by
  have h := checkLog_sound (w := (161201314343 / 2161201314343)) (n := 12)
    (lo := (29891017 / 200000000)) (hi := (74727543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161201314343 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1161201314343 / 1000000000000) = 1/(500000000000 / 1161201314343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (168520453 / 200000000) (842602267 / 1000000000) (Real.log (1161201314343 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1161201314343 / 500000000000) = -Real.log (500000000000 / 1161201314343) := by
    rw [show ((1161201314343 / 500000000000) : ℝ) = ((500000000000 / 1161201314343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (15127091 / 25000000) ≤ -Real.log (500000000000 / 915702691109) ∧
    -Real.log (500000000000 / 915702691109) ≤ (605083641 / 1000000000) := by
  have h := checkLog_sound (w := (415702691109 / 1415702691109)) (n := 12)
    (lo := (15127091 / 25000000)) (hi := (605083641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((915702691109 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(915702691109 / 500000000000) = 1/(500000000000 / 915702691109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (15127091 / 25000000) (605083641 / 1000000000) (Real.log (915702691109 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (915702691109 / 500000000000) = -Real.log (500000000000 / 915702691109) := by
    rw [show ((915702691109 / 500000000000) : ℝ) = ((500000000000 / 915702691109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (303310233 / 500000000) ≤ -Real.log (250000000000 / 458555524537) ∧
    -Real.log (250000000000 / 458555524537) ≤ (606620467 / 1000000000) := by
  have h := checkLog_sound (w := (208555524537 / 708555524537)) (n := 12)
    (lo := (303310233 / 500000000)) (hi := (606620467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((458555524537 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(458555524537 / 250000000000) = 1/(250000000000 / 458555524537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (303310233 / 500000000) (606620467 / 1000000000) (Real.log (458555524537 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (458555524537 / 250000000000) = -Real.log (250000000000 / 458555524537) := by
    rw [show ((458555524537 / 250000000000) : ℝ) = ((250000000000 / 458555524537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0246

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0247Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0247
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

theorem reflection_log_1_neg : (48864781 / 200000000) ≤ -Real.log (5120 / 6537) ∧
    -Real.log (5120 / 6537) ≤ (122161953 / 500000000) := by
  have h := checkLog_sound (w := (1417 / 11657)) (n := 12)
    (lo := (48864781 / 200000000)) (hi := (122161953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6537 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6537 / 5120) = 1/(5120 / 6537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (48864781 / 200000000) (122161953 / 500000000) (Real.log (6537 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6537 / 5120) = -Real.log (5120 / 6537) := by
    rw [show ((6537 / 5120) : ℝ) = ((5120 / 6537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (324011137 / 1000000000) ≤ -Real.log (3703 / 5120) ∧
    -Real.log (3703 / 5120) ≤ (162005569 / 500000000) := by
  have h := checkLog_sound (w := (1417 / 8823)) (n := 12)
    (lo := (324011137 / 1000000000)) (hi := (162005569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3703) = 1/(3703 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-162005569 / 500000000) (-324011137 / 1000000000) (Real.log (3703 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (121932437 / 500000000) ≤ -Real.log (2560 / 3267) ∧
    -Real.log (2560 / 3267) ≤ (1950919 / 8000000) := by
  have h := checkLog_sound (w := (707 / 5827)) (n := 12)
    (lo := (121932437 / 500000000)) (hi := (1950919 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3267 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3267 / 2560) = 1/(2560 / 3267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (121932437 / 500000000) (1950919 / 8000000) (Real.log (3267 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3267 / 2560) = -Real.log (2560 / 3267) := by
    rw [show ((3267 / 2560) : ℝ) = ((2560 / 3267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (323201311 / 1000000000) ≤ -Real.log (1853 / 2560) ∧
    -Real.log (1853 / 2560) ≤ (10100041 / 31250000) := by
  have h := checkLog_sound (w := (707 / 4413)) (n := 12)
    (lo := (323201311 / 1000000000)) (hi := (10100041 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1853) = 1/(1853 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-10100041 / 31250000) (-323201311 / 1000000000) (Real.log (1853 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (440520507 / 1000000000) ≤ -Real.log (2560 / 3977) ∧
    -Real.log (2560 / 3977) ≤ (110130127 / 250000000) := by
  have h := checkLog_sound (w := (1417 / 6537)) (n := 12)
    (lo := (440520507 / 1000000000)) (hi := (110130127 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3977 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3977 / 2560) = 1/(2560 / 3977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (440520507 / 1000000000) (110130127 / 250000000) (Real.log (3977 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3977 / 2560) = -Real.log (2560 / 3977) := by
    rw [show ((3977 / 2560) : ℝ) = ((2560 / 3977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (806350873 / 1000000000) ≤ -Real.log (1143 / 2560) ∧
    -Real.log (1143 / 2560) ≤ (6450807 / 8000000) := by
  have h := checkLog_sound (w := (137 / 2423)) (n := 12)
    (lo := (113203693 / 1000000000)) (hi := (56601847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1143) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1143) = 1/(1143 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-6450807 / 8000000) (-806350873 / 1000000000) (Real.log (1143 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (87953177 / 200000000) ≤ -Real.log (1280 / 1987) ∧
    -Real.log (1280 / 1987) ≤ (219882943 / 500000000) := by
  have h := checkLog_sound (w := (707 / 3267)) (n := 12)
    (lo := (87953177 / 200000000)) (hi := (219882943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1987 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1987 / 1280) = 1/(1280 / 1987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (87953177 / 200000000) (219882943 / 500000000) (Real.log (1987 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1987 / 1280) = -Real.log (1280 / 1987) := by
    rw [show ((1987 / 1280) : ℝ) = ((1280 / 1987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (803729639 / 1000000000) ≤ -Real.log (573 / 1280) ∧
    -Real.log (573 / 1280) ≤ (803729641 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 1213)) (n := 12)
    (lo := (110582459 / 1000000000)) (hi := (5529123 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 573) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 573) = 1/(573 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-803729641 / 1000000000) (-803729639 / 1000000000) (Real.log (573 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (33381657 / 100000000) ≤ -Real.log (1000000 / 1396287) ∧
    -Real.log (1000000 / 1396287) ≤ (333816571 / 1000000000) := by
  have h := checkLog_sound (w := (396287 / 2396287)) (n := 12)
    (lo := (33381657 / 100000000)) (hi := (333816571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1396287 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1396287 / 1000000) = 1/(1000000 / 1396287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (33381657 / 100000000) (333816571 / 1000000000) (Real.log (1396287 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1396287 / 1000000) = -Real.log (1000000 / 1396287) := by
    rw [show ((1396287 / 1000000) : ℝ) = ((1000000 / 1396287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (504656359 / 1000000000) ≤ -Real.log (603713 / 1000000) ∧
    -Real.log (603713 / 1000000) ≤ (12616409 / 25000000) := by
  have h := checkLog_sound (w := (396287 / 1603713)) (n := 12)
    (lo := (504656359 / 1000000000)) (hi := (12616409 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 603713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 603713) = 1/(603713 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-12616409 / 25000000) (-504656359 / 1000000000) (Real.log (603713 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (334439457 / 1000000000) ≤ -Real.log (1000000 / 1397157) ∧
    -Real.log (1000000 / 1397157) ≤ (167219729 / 500000000) := by
  have h := checkLog_sound (w := (397157 / 2397157)) (n := 12)
    (lo := (334439457 / 1000000000)) (hi := (167219729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1397157 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1397157 / 1000000) = 1/(1000000 / 1397157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (334439457 / 1000000000) (167219729 / 500000000) (Real.log (1397157 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1397157 / 1000000) = -Real.log (1000000 / 1397157) := by
    rw [show ((1397157 / 1000000) : ℝ) = ((1000000 / 1397157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (6326231 / 12500000) ≤ -Real.log (602843 / 1000000) ∧
    -Real.log (602843 / 1000000) ≤ (506098481 / 1000000000) := by
  have h := checkLog_sound (w := (397157 / 1602843)) (n := 12)
    (lo := (6326231 / 12500000)) (hi := (506098481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 602843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 602843) = 1/(602843 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-506098481 / 1000000000) (-6326231 / 12500000) (Real.log (602843 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (256915601 / 1000000000) ≤ -Real.log (125000 / 161617) ∧
    -Real.log (125000 / 161617) ≤ (128457801 / 500000000) := by
  have h := checkLog_sound (w := (36617 / 286617)) (n := 12)
    (lo := (256915601 / 1000000000)) (hi := (128457801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161617 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161617 / 125000) = 1/(125000 / 161617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (256915601 / 1000000000) (128457801 / 500000000) (Real.log (161617 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (161617 / 125000) = -Real.log (125000 / 161617) := by
    rw [show ((161617 / 125000) : ℝ) = ((125000 / 161617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (346634093 / 1000000000) ≤ -Real.log (88383 / 125000) ∧
    -Real.log (88383 / 125000) ≤ (173317047 / 500000000) := by
  have h := checkLog_sound (w := (36617 / 213383)) (n := 12)
    (lo := (346634093 / 1000000000)) (hi := (173317047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 88383) = 1/(88383 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-173317047 / 500000000) (-346634093 / 1000000000) (Real.log (88383 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (64364601 / 250000000) ≤ -Real.log (500000 / 646819) ∧
    -Real.log (500000 / 646819) ≤ (51491681 / 200000000) := by
  have h := checkLog_sound (w := (146819 / 1146819)) (n := 12)
    (lo := (64364601 / 250000000)) (hi := (51491681 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((646819 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(646819 / 500000) = 1/(500000 / 646819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (64364601 / 250000000) (51491681 / 200000000) (Real.log (646819 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (646819 / 500000) = -Real.log (500000 / 646819) := by
    rw [show ((646819 / 500000) : ℝ) = ((500000 / 646819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (13905097 / 40000000) ≤ -Real.log (353181 / 500000) ∧
    -Real.log (353181 / 500000) ≤ (173813713 / 500000000) := by
  have h := checkLog_sound (w := (146819 / 853181)) (n := 12)
    (lo := (13905097 / 40000000)) (hi := (173813713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 353181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 353181) = 1/(353181 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-173813713 / 500000000) (-13905097 / 40000000) (Real.log (353181 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (838472929 / 1000000000) ≤ -Real.log (250000000000 / 578208105507) ∧
    -Real.log (250000000000 / 578208105507) ≤ (838472931 / 1000000000) := by
  have h := checkLog_sound (w := (78208105507 / 1078208105507)) (n := 12)
    (lo := (145325749 / 1000000000)) (hi := (581303 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((578208105507 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(578208105507 / 500000000000) = 1/(250000000000 / 578208105507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (838472929 / 1000000000) (838472931 / 1000000000) (Real.log (578208105507 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (578208105507 / 250000000000) = -Real.log (250000000000 / 578208105507) := by
    rw [show ((578208105507 / 250000000000) : ℝ) = ((250000000000 / 578208105507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (420268969 / 500000000) ≤ -Real.log (250000000000 / 579403343823) ∧
    -Real.log (250000000000 / 579403343823) ≤ (42026897 / 50000000) := by
  have h := checkLog_sound (w := (79403343823 / 1079403343823)) (n := 12)
    (lo := (73695379 / 500000000)) (hi := (147390759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((579403343823 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(579403343823 / 500000000000) = 1/(250000000000 / 579403343823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (420268969 / 500000000) (42026897 / 50000000) (Real.log (579403343823 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (579403343823 / 250000000000) = -Real.log (250000000000 / 579403343823) := by
    rw [show ((579403343823 / 250000000000) : ℝ) = ((250000000000 / 579403343823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (120709939 / 200000000) ≤ -Real.log (500000000000 / 914299129923) ∧
    -Real.log (500000000000 / 914299129923) ≤ (1178808 / 1953125) := by
  have h := checkLog_sound (w := (414299129923 / 1414299129923)) (n := 12)
    (lo := (120709939 / 200000000)) (hi := (1178808 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((914299129923 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(914299129923 / 500000000000) = 1/(500000000000 / 914299129923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (120709939 / 200000000) (1178808 / 1953125) (Real.log (914299129923 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (914299129923 / 500000000000) = -Real.log (500000000000 / 914299129923) := by
    rw [show ((914299129923 / 500000000000) : ℝ) = ((500000000000 / 914299129923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (605085829 / 1000000000) ≤ -Real.log (500000000000 / 915704695327) ∧
    -Real.log (500000000000 / 915704695327) ≤ (60508583 / 100000000) := by
  have h := checkLog_sound (w := (415704695327 / 1415704695327)) (n := 12)
    (lo := (605085829 / 1000000000)) (hi := (60508583 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((915704695327 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(915704695327 / 500000000000) = 1/(500000000000 / 915704695327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (605085829 / 1000000000) (60508583 / 100000000) (Real.log (915704695327 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (915704695327 / 500000000000) = -Real.log (500000000000 / 915704695327) := by
    rw [show ((915704695327 / 500000000000) : ℝ) = ((500000000000 / 915704695327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0247

end


