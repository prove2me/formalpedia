-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0156Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0156Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:24:15.98932+00:00
-- url     : https://prove2.me/theorems/1642a303-4f14-44c6-bee1-df791a8e40f7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0156Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0157Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0156Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0157Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0158Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0159Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0160Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0161Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0162Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0156Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0157Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0158Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0159Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0160Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0161Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0162Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0156Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0157Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0158Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0159Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0160Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0161Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0162Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0156Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0157Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0158Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0159Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0160Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0161Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0162Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0156Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0156
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

theorem reflection_log_1_neg : (285237681 / 1000000000) ≤ -Real.log (512 / 681) ∧
    -Real.log (512 / 681) ≤ (142618841 / 500000000) := by
  have h := checkLog_sound (w := (169 / 1193)) (n := 12)
    (lo := (285237681 / 1000000000)) (hi := (142618841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(681 / 512) = 1/(512 / 681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (285237681 / 1000000000) (142618841 / 500000000) (Real.log (681 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (681 / 512) = -Real.log (512 / 681) := by
    rw [show ((681 / 512) : ℝ) = ((512 / 681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (400594177 / 1000000000) ≤ -Real.log (343 / 512) ∧
    -Real.log (343 / 512) ≤ (200297089 / 500000000) := by
  have h := checkLog_sound (w := (169 / 855)) (n := 12)
    (lo := (400594177 / 1000000000)) (hi := (200297089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 343) = 1/(343 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-200297089 / 500000000) (-400594177 / 1000000000) (Real.log (343 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (56959411 / 200000000) ≤ -Real.log (5120 / 6807) ∧
    -Real.log (5120 / 6807) ≤ (2224977 / 7812500) := by
  have h := checkLog_sound (w := (1687 / 11927)) (n := 12)
    (lo := (56959411 / 200000000)) (hi := (2224977 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6807 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6807 / 5120) = 1/(5120 / 6807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (56959411 / 200000000) (2224977 / 7812500) (Real.log (6807 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6807 / 5120) = -Real.log (5120 / 6807) := by
    rw [show ((6807 / 5120) : ℝ) = ((5120 / 6807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (99929981 / 250000000) ≤ -Real.log (3433 / 5120) ∧
    -Real.log (3433 / 5120) ≤ (15988797 / 40000000) := by
  have h := checkLog_sound (w := (1687 / 8553)) (n := 12)
    (lo := (99929981 / 250000000)) (hi := (15988797 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3433) = 1/(3433 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-15988797 / 40000000) (-99929981 / 250000000) (Real.log (3433 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (126727931 / 250000000) ≤ -Real.log (256 / 425) ∧
    -Real.log (256 / 425) ≤ (20276469 / 40000000) := by
  have h := checkLog_sound (w := (169 / 681)) (n := 12)
    (lo := (126727931 / 250000000)) (hi := (20276469 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((425 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(425 / 256) = 1/(256 / 425) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (126727931 / 250000000) (20276469 / 40000000) (Real.log (425 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (425 / 256) = -Real.log (256 / 425) := by
    rw [show ((425 / 256) : ℝ) = ((256 / 425) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (43170773 / 40000000) ≤ -Real.log (87 / 256) ∧
    -Real.log (87 / 256) ≤ (1079269327 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 215)) (n := 12)
    (lo := (77224429 / 200000000)) (hi := (193061073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 87) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 87) = 1/(87 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1079269327 / 1000000000) (-43170773 / 40000000) (Real.log (87 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (63275699 / 125000000) ≤ -Real.log (2560 / 4247) ∧
    -Real.log (2560 / 4247) ≤ (506205593 / 1000000000) := by
  have h := checkLog_sound (w := (1687 / 6807)) (n := 12)
    (lo := (63275699 / 125000000)) (hi := (506205593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4247 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4247 / 2560) = 1/(2560 / 4247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (63275699 / 125000000) (506205593 / 1000000000) (Real.log (4247 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4247 / 2560) = -Real.log (2560 / 4247) := by
    rw [show ((4247 / 2560) : ℝ) = ((2560 / 4247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1075826981 / 1000000000) ≤ -Real.log (873 / 2560) ∧
    -Real.log (873 / 2560) ≤ (1075826983 / 1000000000) := by
  have h := checkLog_sound (w := (407 / 2153)) (n := 12)
    (lo := (382679801 / 1000000000)) (hi := (191339901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 873) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 873) = 1/(873 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1075826983 / 1000000000) (-1075826981 / 1000000000) (Real.log (873 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (38962227 / 100000000) ≤ -Real.log (1000000 / 1476423) ∧
    -Real.log (1000000 / 1476423) ≤ (389622271 / 1000000000) := by
  have h := checkLog_sound (w := (476423 / 2476423)) (n := 12)
    (lo := (38962227 / 100000000)) (hi := (389622271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1476423 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1476423 / 1000000) = 1/(1000000 / 1476423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (38962227 / 100000000) (389622271 / 1000000000) (Real.log (1476423 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1476423 / 1000000) = -Real.log (1000000 / 1476423) := by
    rw [show ((1476423 / 1000000) : ℝ) = ((1000000 / 1476423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (161767793 / 250000000) ≤ -Real.log (523577 / 1000000) ∧
    -Real.log (523577 / 1000000) ≤ (647071173 / 1000000000) := by
  have h := checkLog_sound (w := (476423 / 1523577)) (n := 12)
    (lo := (161767793 / 250000000)) (hi := (647071173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 523577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 523577) = 1/(523577 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-647071173 / 1000000000) (-161767793 / 250000000) (Real.log (523577 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (195114479 / 500000000) ≤ -Real.log (1000000 / 1477319) ∧
    -Real.log (1000000 / 1477319) ≤ (390228959 / 1000000000) := by
  have h := checkLog_sound (w := (477319 / 2477319)) (n := 12)
    (lo := (195114479 / 500000000)) (hi := (390228959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1477319 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1477319 / 1000000) = 1/(1000000 / 1477319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (195114479 / 500000000) (390228959 / 1000000000) (Real.log (1477319 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1477319 / 1000000) = -Real.log (1000000 / 1477319) := by
    rw [show ((1477319 / 1000000) : ℝ) = ((1000000 / 1477319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (648783943 / 1000000000) ≤ -Real.log (522681 / 1000000) ∧
    -Real.log (522681 / 1000000) ≤ (81097993 / 125000000) := by
  have h := checkLog_sound (w := (477319 / 1522681)) (n := 12)
    (lo := (648783943 / 1000000000)) (hi := (81097993 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 522681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 522681) = 1/(522681 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-81097993 / 125000000) (-648783943 / 1000000000) (Real.log (522681 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (307039747 / 1000000000) ≤ -Real.log (200000 / 271879) ∧
    -Real.log (200000 / 271879) ≤ (76759937 / 250000000) := by
  have h := checkLog_sound (w := (71879 / 471879)) (n := 12)
    (lo := (307039747 / 1000000000)) (hi := (76759937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271879 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271879 / 200000) = 1/(200000 / 271879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (307039747 / 1000000000) (76759937 / 250000000) (Real.log (271879 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (271879 / 200000) = -Real.log (200000 / 271879) := by
    rw [show ((271879 / 200000) : ℝ) = ((200000 / 271879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (111335559 / 250000000) ≤ -Real.log (128121 / 200000) ∧
    -Real.log (128121 / 200000) ≤ (445342237 / 1000000000) := by
  have h := checkLog_sound (w := (71879 / 328121)) (n := 12)
    (lo := (111335559 / 250000000)) (hi := (445342237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 128121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 128121) = 1/(128121 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-445342237 / 1000000000) (-111335559 / 250000000) (Real.log (128121 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (12304123 / 40000000) ≤ -Real.log (1000000 / 1360161) ∧
    -Real.log (1000000 / 1360161) ≤ (76900769 / 250000000) := by
  have h := checkLog_sound (w := (360161 / 2360161)) (n := 12)
    (lo := (12304123 / 40000000)) (hi := (76900769 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1360161 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1360161 / 1000000) = 1/(1000000 / 1360161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (12304123 / 40000000) (76900769 / 250000000) (Real.log (1360161 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1360161 / 1000000) = -Real.log (1000000 / 1360161) := by
    rw [show ((1360161 / 1000000) : ℝ) = ((1000000 / 1360161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (55817337 / 125000000) ≤ -Real.log (639839 / 1000000) ∧
    -Real.log (639839 / 1000000) ≤ (446538697 / 1000000000) := by
  have h := checkLog_sound (w := (360161 / 1639839)) (n := 12)
    (lo := (55817337 / 125000000)) (hi := (446538697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 639839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 639839) = 1/(639839 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-446538697 / 1000000000) (-55817337 / 125000000) (Real.log (639839 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (518346721 / 500000000) ≤ -Real.log (62500000000 / 176242343533) ∧
    -Real.log (62500000000 / 176242343533) ≤ (259173361 / 250000000) := by
  have h := checkLog_sound (w := (51242343533 / 301242343533)) (n := 12)
    (lo := (171773131 / 500000000)) (hi := (343546263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176242343533 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(176242343533 / 125000000000) = 1/(62500000000 / 176242343533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (518346721 / 500000000) (259173361 / 250000000) (Real.log (176242343533 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (176242343533 / 62500000000) = -Real.log (62500000000 / 176242343533) := by
    rw [show ((176242343533 / 62500000000) : ℝ) = ((62500000000 / 176242343533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1039012901 / 1000000000) ≤ -Real.log (500000000000 / 1413212839189) ∧
    -Real.log (500000000000 / 1413212839189) ≤ (1039012903 / 1000000000) := by
  have h := checkLog_sound (w := (413212839189 / 2413212839189)) (n := 12)
    (lo := (345865721 / 1000000000)) (hi := (172932861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1413212839189 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1413212839189 / 1000000000000) = 1/(500000000000 / 1413212839189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1039012901 / 1000000000) (1039012903 / 1000000000) (Real.log (1413212839189 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1413212839189 / 500000000000) = -Real.log (500000000000 / 1413212839189) := by
    rw [show ((1413212839189 / 500000000000) : ℝ) = ((500000000000 / 1413212839189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (752381983 / 1000000000) ≤ -Real.log (250000000000 / 530512172087) ∧
    -Real.log (250000000000 / 530512172087) ≤ (150476397 / 200000000) := by
  have h := checkLog_sound (w := (30512172087 / 1030512172087)) (n := 12)
    (lo := (59234803 / 1000000000)) (hi := (14808701 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((530512172087 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(530512172087 / 500000000000) = 1/(250000000000 / 530512172087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (752381983 / 1000000000) (150476397 / 200000000) (Real.log (530512172087 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (530512172087 / 250000000000) = -Real.log (250000000000 / 530512172087) := by
    rw [show ((530512172087 / 250000000000) : ℝ) = ((250000000000 / 530512172087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (754141771 / 1000000000) ≤ -Real.log (1953125000 / 4151926427) ∧
    -Real.log (1953125000 / 4151926427) ≤ (754141773 / 1000000000) := by
  have h := checkLog_sound (w := (245676427 / 8058176427)) (n := 12)
    (lo := (60994591 / 1000000000)) (hi := (1906081 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4151926427 / 3906250000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(4151926427 / 3906250000) = 1/(1953125000 / 4151926427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (754141771 / 1000000000) (754141773 / 1000000000) (Real.log (4151926427 / 1953125000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4151926427 / 1953125000) = -Real.log (1953125000 / 4151926427) := by
    rw [show ((4151926427 / 1953125000) : ℝ) = ((1953125000 / 4151926427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0156

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0157Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0157
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

theorem reflection_log_1_neg : (56959411 / 200000000) ≤ -Real.log (5120 / 6807) ∧
    -Real.log (5120 / 6807) ≤ (2224977 / 7812500) := by
  have h := checkLog_sound (w := (1687 / 11927)) (n := 12)
    (lo := (56959411 / 200000000)) (hi := (2224977 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6807 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6807 / 5120) = 1/(5120 / 6807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (56959411 / 200000000) (2224977 / 7812500) (Real.log (6807 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6807 / 5120) = -Real.log (5120 / 6807) := by
    rw [show ((6807 / 5120) : ℝ) = ((5120 / 6807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (99929981 / 250000000) ≤ -Real.log (3433 / 5120) ∧
    -Real.log (3433 / 5120) ≤ (15988797 / 40000000) := by
  have h := checkLog_sound (w := (1687 / 8553)) (n := 12)
    (lo := (99929981 / 250000000)) (hi := (15988797 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3433) = 1/(3433 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-15988797 / 40000000) (-99929981 / 250000000) (Real.log (3433 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (56871247 / 200000000) ≤ -Real.log (1280 / 1701) ∧
    -Real.log (1280 / 1701) ≤ (71089059 / 250000000) := by
  have h := checkLog_sound (w := (421 / 2981)) (n := 12)
    (lo := (56871247 / 200000000)) (hi := (71089059 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1701 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1701 / 1280) = 1/(1280 / 1701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (56871247 / 200000000) (71089059 / 250000000) (Real.log (1701 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1701 / 1280) = -Real.log (1280 / 1701) := by
    rw [show ((1701 / 1280) : ℝ) = ((1280 / 1701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (199423217 / 500000000) ≤ -Real.log (859 / 1280) ∧
    -Real.log (859 / 1280) ≤ (79769287 / 200000000) := by
  have h := checkLog_sound (w := (421 / 2139)) (n := 12)
    (lo := (199423217 / 500000000)) (hi := (79769287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 859) = 1/(859 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-79769287 / 200000000) (-199423217 / 500000000) (Real.log (859 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (63275699 / 125000000) ≤ -Real.log (2560 / 4247) ∧
    -Real.log (2560 / 4247) ≤ (506205593 / 1000000000) := by
  have h := checkLog_sound (w := (1687 / 6807)) (n := 12)
    (lo := (63275699 / 125000000)) (hi := (506205593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4247 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4247 / 2560) = 1/(2560 / 4247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (63275699 / 125000000) (506205593 / 1000000000) (Real.log (4247 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4247 / 2560) = -Real.log (2560 / 4247) := by
    rw [show ((4247 / 2560) : ℝ) = ((2560 / 4247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1075826981 / 1000000000) ≤ -Real.log (873 / 2560) ∧
    -Real.log (873 / 2560) ≤ (1075826983 / 1000000000) := by
  have h := checkLog_sound (w := (407 / 2153)) (n := 12)
    (lo := (382679801 / 1000000000)) (hi := (191339901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 873) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 873) = 1/(873 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1075826983 / 1000000000) (-1075826981 / 1000000000) (Real.log (873 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (252749481 / 500000000) ≤ -Real.log (640 / 1061) ∧
    -Real.log (640 / 1061) ≤ (505498963 / 1000000000) := by
  have h := checkLog_sound (w := (421 / 1701)) (n := 12)
    (lo := (252749481 / 500000000)) (hi := (505498963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1061 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1061 / 640) = 1/(640 / 1061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (252749481 / 500000000) (505498963 / 1000000000) (Real.log (1061 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1061 / 640) = -Real.log (640 / 1061) := by
    rw [show ((1061 / 640) : ℝ) = ((640 / 1061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (214479289 / 200000000) ≤ -Real.log (219 / 640) ∧
    -Real.log (219 / 640) ≤ (1072396447 / 1000000000) := by
  have h := checkLog_sound (w := (101 / 539)) (n := 12)
    (lo := (75849853 / 200000000)) (hi := (189624633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 219) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 219) = 1/(219 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1072396447 / 1000000000) (-214479289 / 200000000) (Real.log (219 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (389016569 / 1000000000) ≤ -Real.log (1000000 / 1475529) ∧
    -Real.log (1000000 / 1475529) ≤ (38901657 / 100000000) := by
  have h := checkLog_sound (w := (475529 / 2475529)) (n := 12)
    (lo := (389016569 / 1000000000)) (hi := (38901657 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1475529 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1475529 / 1000000) = 1/(1000000 / 1475529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (389016569 / 1000000000) (38901657 / 100000000) (Real.log (1475529 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1475529 / 1000000) = -Real.log (1000000 / 1475529) := by
    rw [show ((1475529 / 1000000) : ℝ) = ((1000000 / 1475529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (645365143 / 1000000000) ≤ -Real.log (524471 / 1000000) ∧
    -Real.log (524471 / 1000000) ≤ (80670643 / 125000000) := by
  have h := checkLog_sound (w := (475529 / 1524471)) (n := 12)
    (lo := (645365143 / 1000000000)) (hi := (80670643 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 524471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 524471) = 1/(524471 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-80670643 / 125000000) (-645365143 / 1000000000) (Real.log (524471 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (389622947 / 1000000000) ≤ -Real.log (125000 / 184553) ∧
    -Real.log (125000 / 184553) ≤ (97405737 / 250000000) := by
  have h := checkLog_sound (w := (59553 / 309553)) (n := 12)
    (lo := (389622947 / 1000000000)) (hi := (97405737 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184553 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184553 / 125000) = 1/(125000 / 184553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (389622947 / 1000000000) (97405737 / 250000000) (Real.log (184553 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (184553 / 125000) = -Real.log (125000 / 184553) := by
    rw [show ((184553 / 125000) : ℝ) = ((125000 / 184553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (323536541 / 500000000) ≤ -Real.log (65447 / 125000) ∧
    -Real.log (65447 / 125000) ≤ (647073083 / 1000000000) := by
  have h := checkLog_sound (w := (59553 / 190447)) (n := 12)
    (lo := (323536541 / 500000000)) (hi := (647073083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 65447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 65447) = 1/(65447 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-647073083 / 1000000000) (-323536541 / 500000000) (Real.log (65447 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (306478311 / 1000000000) ≤ -Real.log (125000 / 169829) ∧
    -Real.log (125000 / 169829) ≤ (38309789 / 125000000) := by
  have h := checkLog_sound (w := (44829 / 294829)) (n := 12)
    (lo := (306478311 / 1000000000)) (hi := (38309789 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169829 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169829 / 125000) = 1/(125000 / 169829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (306478311 / 1000000000) (38309789 / 125000000) (Real.log (169829 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (169829 / 125000) = -Real.log (125000 / 169829) := by
    rw [show ((169829 / 125000) : ℝ) = ((125000 / 169829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (444151883 / 1000000000) ≤ -Real.log (80171 / 125000) ∧
    -Real.log (80171 / 125000) ≤ (111037971 / 250000000) := by
  have h := checkLog_sound (w := (44829 / 205171)) (n := 12)
    (lo := (444151883 / 1000000000)) (hi := (111037971 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 80171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 80171) = 1/(80171 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-111037971 / 250000000) (-444151883 / 1000000000) (Real.log (80171 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (307040483 / 1000000000) ≤ -Real.log (250000 / 339849) ∧
    -Real.log (250000 / 339849) ≤ (76760121 / 250000000) := by
  have h := checkLog_sound (w := (89849 / 589849)) (n := 12)
    (lo := (307040483 / 1000000000)) (hi := (76760121 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339849 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339849 / 250000) = 1/(250000 / 339849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (307040483 / 1000000000) (76760121 / 250000000) (Real.log (339849 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (339849 / 250000) = -Real.log (250000 / 339849) := by
    rw [show ((339849 / 250000) : ℝ) = ((250000 / 339849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (445343797 / 1000000000) ≤ -Real.log (160151 / 250000) ∧
    -Real.log (160151 / 250000) ≤ (222671899 / 500000000) := by
  have h := checkLog_sound (w := (89849 / 410151)) (n := 12)
    (lo := (445343797 / 1000000000)) (hi := (222671899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 160151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 160151) = 1/(160151 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-222671899 / 500000000) (-445343797 / 1000000000) (Real.log (160151 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (64648857 / 62500000) ≤ -Real.log (250000000000 / 703341557493) ∧
    -Real.log (250000000000 / 703341557493) ≤ (517190857 / 500000000) := by
  have h := checkLog_sound (w := (203341557493 / 1203341557493)) (n := 12)
    (lo := (85308633 / 250000000)) (hi := (341234533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703341557493 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(703341557493 / 500000000000) = 1/(250000000000 / 703341557493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (64648857 / 62500000) (517190857 / 500000000) (Real.log (703341557493 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (703341557493 / 250000000000) = -Real.log (250000000000 / 703341557493) := by
    rw [show ((703341557493 / 250000000000) : ℝ) = ((250000000000 / 703341557493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1036696029 / 1000000000) ≤ -Real.log (250000000000 / 704971198069) ∧
    -Real.log (250000000000 / 704971198069) ≤ (1036696031 / 1000000000) := by
  have h := checkLog_sound (w := (204971198069 / 1204971198069)) (n := 12)
    (lo := (343548849 / 1000000000)) (hi := (6870977 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704971198069 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(704971198069 / 500000000000) = 1/(250000000000 / 704971198069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1036696029 / 1000000000) (1036696031 / 1000000000) (Real.log (704971198069 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (704971198069 / 250000000000) = -Real.log (250000000000 / 704971198069) := by
    rw [show ((704971198069 / 250000000000) : ℝ) = ((250000000000 / 704971198069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (375315097 / 500000000) ≤ -Real.log (500000000000 / 1059167279939) ∧
    -Real.log (500000000000 / 1059167279939) ≤ (187657549 / 250000000) := by
  have h := checkLog_sound (w := (59167279939 / 2059167279939)) (n := 12)
    (lo := (28741507 / 500000000)) (hi := (11496603 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1059167279939 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1059167279939 / 1000000000000) = 1/(500000000000 / 1059167279939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (375315097 / 500000000) (187657549 / 250000000) (Real.log (1059167279939 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1059167279939 / 500000000000) = -Real.log (500000000000 / 1059167279939) := by
    rw [show ((1059167279939 / 500000000000) : ℝ) = ((500000000000 / 1059167279939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (18809607 / 25000000) ≤ -Real.log (31250000000 / 66314173811) ∧
    -Real.log (31250000000 / 66314173811) ≤ (376192141 / 500000000) := by
  have h := checkLog_sound (w := (3814173811 / 128814173811)) (n := 12)
    (lo := (592371 / 10000000)) (hi := (59237101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66314173811 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(66314173811 / 62500000000) = 1/(31250000000 / 66314173811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (18809607 / 25000000) (376192141 / 500000000) (Real.log (66314173811 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (66314173811 / 31250000000) = -Real.log (31250000000 / 66314173811) := by
    rw [show ((66314173811 / 31250000000) : ℝ) = ((31250000000 / 66314173811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0157

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0158Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0158
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

theorem reflection_log_1_neg : (56871247 / 200000000) ≤ -Real.log (1280 / 1701) ∧
    -Real.log (1280 / 1701) ≤ (71089059 / 250000000) := by
  have h := checkLog_sound (w := (421 / 2981)) (n := 12)
    (lo := (56871247 / 200000000)) (hi := (71089059 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1701 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1701 / 1280) = 1/(1280 / 1701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (56871247 / 200000000) (71089059 / 250000000) (Real.log (1701 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1701 / 1280) = -Real.log (1280 / 1701) := by
    rw [show ((1701 / 1280) : ℝ) = ((1280 / 1701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (199423217 / 500000000) ≤ -Real.log (859 / 1280) ∧
    -Real.log (859 / 1280) ≤ (79769287 / 200000000) := by
  have h := checkLog_sound (w := (421 / 2139)) (n := 12)
    (lo := (199423217 / 500000000)) (hi := (79769287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 859) = 1/(859 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-79769287 / 200000000) (-199423217 / 500000000) (Real.log (859 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (283915221 / 1000000000) ≤ -Real.log (5120 / 6801) ∧
    -Real.log (5120 / 6801) ≤ (141957611 / 500000000) := by
  have h := checkLog_sound (w := (1681 / 11921)) (n := 12)
    (lo := (283915221 / 1000000000)) (hi := (141957611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6801 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6801 / 5120) = 1/(5120 / 6801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (283915221 / 1000000000) (141957611 / 500000000) (Real.log (6801 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6801 / 5120) = -Real.log (5120 / 6801) := by
    rw [show ((6801 / 5120) : ℝ) = ((5120 / 6801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (397973707 / 1000000000) ≤ -Real.log (3439 / 5120) ∧
    -Real.log (3439 / 5120) ≤ (99493427 / 250000000) := by
  have h := checkLog_sound (w := (1681 / 8559)) (n := 12)
    (lo := (397973707 / 1000000000)) (hi := (99493427 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3439) = 1/(3439 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-99493427 / 250000000) (-397973707 / 1000000000) (Real.log (3439 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (252749481 / 500000000) ≤ -Real.log (640 / 1061) ∧
    -Real.log (640 / 1061) ≤ (505498963 / 1000000000) := by
  have h := checkLog_sound (w := (421 / 1701)) (n := 12)
    (lo := (252749481 / 500000000)) (hi := (505498963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1061 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1061 / 640) = 1/(640 / 1061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (252749481 / 500000000) (505498963 / 1000000000) (Real.log (1061 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1061 / 640) = -Real.log (640 / 1061) := by
    rw [show ((1061 / 640) : ℝ) = ((640 / 1061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (214479289 / 200000000) ≤ -Real.log (219 / 640) ∧
    -Real.log (219 / 640) ≤ (1072396447 / 1000000000) := by
  have h := checkLog_sound (w := (101 / 539)) (n := 12)
    (lo := (75849853 / 200000000)) (hi := (189624633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 219) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 219) = 1/(219 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1072396447 / 1000000000) (-214479289 / 200000000) (Real.log (219 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (63098979 / 125000000) ≤ -Real.log (2560 / 4241) ∧
    -Real.log (2560 / 4241) ≤ (504791833 / 1000000000) := by
  have h := checkLog_sound (w := (1681 / 6801)) (n := 12)
    (lo := (63098979 / 125000000)) (hi := (504791833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4241 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4241 / 2560) = 1/(2560 / 4241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (63098979 / 125000000) (504791833 / 1000000000) (Real.log (4241 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4241 / 2560) = -Real.log (2560 / 4241) := by
    rw [show ((4241 / 2560) : ℝ) = ((2560 / 4241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1068977639 / 1000000000) ≤ -Real.log (879 / 2560) ∧
    -Real.log (879 / 2560) ≤ (1068977641 / 1000000000) := by
  have h := checkLog_sound (w := (401 / 2159)) (n := 12)
    (lo := (375830459 / 1000000000)) (hi := (18791523 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 879) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 879) = 1/(879 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1068977641 / 1000000000) (-1068977639 / 1000000000) (Real.log (879 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (388411179 / 1000000000) ≤ -Real.log (250000 / 368659) ∧
    -Real.log (250000 / 368659) ≤ (19420559 / 50000000) := by
  have h := checkLog_sound (w := (118659 / 618659)) (n := 12)
    (lo := (388411179 / 1000000000)) (hi := (19420559 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((368659 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(368659 / 250000) = 1/(250000 / 368659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (388411179 / 1000000000) (19420559 / 50000000) (Real.log (368659 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (368659 / 250000) = -Real.log (250000 / 368659) := by
    rw [show ((368659 / 250000) : ℝ) = ((250000 / 368659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (643663923 / 1000000000) ≤ -Real.log (131341 / 250000) ∧
    -Real.log (131341 / 250000) ≤ (160915981 / 250000000) := by
  have h := checkLog_sound (w := (118659 / 381341)) (n := 12)
    (lo := (643663923 / 1000000000)) (hi := (160915981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 131341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 131341) = 1/(131341 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-160915981 / 250000000) (-643663923 / 1000000000) (Real.log (131341 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (389017247 / 1000000000) ≤ -Real.log (100000 / 147553) ∧
    -Real.log (100000 / 147553) ≤ (12156789 / 31250000) := by
  have h := checkLog_sound (w := (47553 / 247553)) (n := 12)
    (lo := (389017247 / 1000000000)) (hi := (12156789 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147553 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147553 / 100000) = 1/(100000 / 147553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (389017247 / 1000000000) (12156789 / 31250000) (Real.log (147553 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (147553 / 100000) = -Real.log (100000 / 147553) := by
    rw [show ((147553 / 100000) : ℝ) = ((100000 / 147553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (12907341 / 20000000) ≤ -Real.log (52447 / 100000) ∧
    -Real.log (52447 / 100000) ≤ (645367051 / 1000000000) := by
  have h := checkLog_sound (w := (47553 / 152447)) (n := 12)
    (lo := (12907341 / 20000000)) (hi := (645367051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 52447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 52447) = 1/(52447 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-645367051 / 1000000000) (-12907341 / 20000000) (Real.log (52447 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (305916559 / 1000000000) ≤ -Real.log (1000000 / 1357869) ∧
    -Real.log (1000000 / 1357869) ≤ (3823957 / 12500000) := by
  have h := checkLog_sound (w := (357869 / 2357869)) (n := 12)
    (lo := (305916559 / 1000000000)) (hi := (3823957 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1357869 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1357869 / 1000000) = 1/(1000000 / 1357869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (305916559 / 1000000000) (3823957 / 12500000) (Real.log (1357869 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1357869 / 1000000) = -Real.log (1000000 / 1357869) := by
    rw [show ((1357869 / 1000000) : ℝ) = ((1000000 / 1357869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (221481473 / 500000000) ≤ -Real.log (642131 / 1000000) ∧
    -Real.log (642131 / 1000000) ≤ (442962947 / 1000000000) := by
  have h := checkLog_sound (w := (357869 / 1642131)) (n := 12)
    (lo := (221481473 / 500000000)) (hi := (442962947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 642131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 642131) = 1/(642131 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-442962947 / 1000000000) (-221481473 / 500000000) (Real.log (642131 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (306479047 / 1000000000) ≤ -Real.log (1000000 / 1358633) ∧
    -Real.log (1000000 / 1358633) ≤ (38309881 / 125000000) := by
  have h := checkLog_sound (w := (358633 / 2358633)) (n := 12)
    (lo := (306479047 / 1000000000)) (hi := (38309881 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1358633 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1358633 / 1000000) = 1/(1000000 / 1358633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (306479047 / 1000000000) (38309881 / 125000000) (Real.log (1358633 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1358633 / 1000000) = -Real.log (1000000 / 1358633) := by
    rw [show ((1358633 / 1000000) : ℝ) = ((1000000 / 1358633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (222076721 / 500000000) ≤ -Real.log (641367 / 1000000) ∧
    -Real.log (641367 / 1000000) ≤ (444153443 / 1000000000) := by
  have h := checkLog_sound (w := (358633 / 1641367)) (n := 12)
    (lo := (222076721 / 500000000)) (hi := (444153443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 641367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 641367) = 1/(641367 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-444153443 / 1000000000) (-222076721 / 500000000) (Real.log (641367 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (516037551 / 500000000) ≤ -Real.log (500000000000 / 1403442184847) ∧
    -Real.log (500000000000 / 1403442184847) ≤ (32252347 / 31250000) := by
  have h := checkLog_sound (w := (403442184847 / 2403442184847)) (n := 12)
    (lo := (169463961 / 500000000)) (hi := (338927923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1403442184847 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1403442184847 / 1000000000000) = 1/(500000000000 / 1403442184847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (516037551 / 500000000) (32252347 / 31250000) (Real.log (1403442184847 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1403442184847 / 500000000000) = -Real.log (500000000000 / 1403442184847) := by
    rw [show ((1403442184847 / 500000000000) : ℝ) = ((500000000000 / 1403442184847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (129298037 / 125000000) ≤ -Real.log (250000000000 / 703343375217) ∧
    -Real.log (250000000000 / 703343375217) ≤ (517192149 / 500000000) := by
  have h := checkLog_sound (w := (203343375217 / 1203343375217)) (n := 12)
    (lo := (85309279 / 250000000)) (hi := (341237117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703343375217 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(703343375217 / 500000000000) = 1/(250000000000 / 703343375217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (129298037 / 125000000) (517192149 / 500000000) (Real.log (703343375217 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (703343375217 / 250000000000) = -Real.log (250000000000 / 703343375217) := by
    rw [show ((703343375217 / 250000000000) : ℝ) = ((250000000000 / 703343375217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (46804969 / 62500000) ≤ -Real.log (250000000000 / 528657314473) ∧
    -Real.log (250000000000 / 528657314473) ≤ (374439753 / 500000000) := by
  have h := checkLog_sound (w := (28657314473 / 1028657314473)) (n := 12)
    (lo := (13933081 / 250000000)) (hi := (2229293 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((528657314473 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(528657314473 / 500000000000) = 1/(250000000000 / 528657314473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (46804969 / 62500000) (374439753 / 500000000) (Real.log (528657314473 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (528657314473 / 250000000000) = -Real.log (250000000000 / 528657314473) := by
    rw [show ((528657314473 / 250000000000) : ℝ) = ((250000000000 / 528657314473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (750632489 / 1000000000) ≤ -Real.log (250000000000 / 529584855473) ∧
    -Real.log (250000000000 / 529584855473) ≤ (750632491 / 1000000000) := by
  have h := checkLog_sound (w := (29584855473 / 1029584855473)) (n := 12)
    (lo := (57485309 / 1000000000)) (hi := (5748531 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((529584855473 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(529584855473 / 500000000000) = 1/(250000000000 / 529584855473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (750632489 / 1000000000) (750632491 / 1000000000) (Real.log (529584855473 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (529584855473 / 250000000000) = -Real.log (250000000000 / 529584855473) := by
    rw [show ((529584855473 / 250000000000) : ℝ) = ((250000000000 / 529584855473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0158

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0159Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0159
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

theorem reflection_log_1_neg : (283915221 / 1000000000) ≤ -Real.log (5120 / 6801) ∧
    -Real.log (5120 / 6801) ≤ (141957611 / 500000000) := by
  have h := checkLog_sound (w := (1681 / 11921)) (n := 12)
    (lo := (283915221 / 1000000000)) (hi := (141957611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6801 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6801 / 5120) = 1/(5120 / 6801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (283915221 / 1000000000) (141957611 / 500000000) (Real.log (6801 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6801 / 5120) = -Real.log (5120 / 6801) := by
    rw [show ((6801 / 5120) : ℝ) = ((5120 / 6801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (397973707 / 1000000000) ≤ -Real.log (3439 / 5120) ∧
    -Real.log (3439 / 5120) ≤ (99493427 / 250000000) := by
  have h := checkLog_sound (w := (1681 / 8559)) (n := 12)
    (lo := (397973707 / 1000000000)) (hi := (99493427 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3439) = 1/(3439 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-99493427 / 250000000) (-397973707 / 1000000000) (Real.log (3439 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (70868503 / 250000000) ≤ -Real.log (2560 / 3399) ∧
    -Real.log (2560 / 3399) ≤ (283474013 / 1000000000) := by
  have h := checkLog_sound (w := (839 / 5959)) (n := 12)
    (lo := (70868503 / 250000000)) (hi := (283474013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3399 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3399 / 2560) = 1/(2560 / 3399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (70868503 / 250000000) (283474013 / 1000000000) (Real.log (3399 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3399 / 2560) = -Real.log (2560 / 3399) := by
    rw [show ((3399 / 2560) : ℝ) = ((2560 / 3399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (397101741 / 1000000000) ≤ -Real.log (1721 / 2560) ∧
    -Real.log (1721 / 2560) ≤ (198550871 / 500000000) := by
  have h := checkLog_sound (w := (839 / 4281)) (n := 12)
    (lo := (397101741 / 1000000000)) (hi := (198550871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1721) = 1/(1721 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-198550871 / 500000000) (-397101741 / 1000000000) (Real.log (1721 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (63098979 / 125000000) ≤ -Real.log (2560 / 4241) ∧
    -Real.log (2560 / 4241) ≤ (504791833 / 1000000000) := by
  have h := checkLog_sound (w := (1681 / 6801)) (n := 12)
    (lo := (63098979 / 125000000)) (hi := (504791833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4241 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4241 / 2560) = 1/(2560 / 4241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (63098979 / 125000000) (504791833 / 1000000000) (Real.log (4241 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4241 / 2560) = -Real.log (2560 / 4241) := by
    rw [show ((4241 / 2560) : ℝ) = ((2560 / 4241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1068977639 / 1000000000) ≤ -Real.log (879 / 2560) ∧
    -Real.log (879 / 2560) ≤ (1068977641 / 1000000000) := by
  have h := checkLog_sound (w := (401 / 2159)) (n := 12)
    (lo := (375830459 / 1000000000)) (hi := (18791523 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 879) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 879) = 1/(879 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1068977641 / 1000000000) (-1068977639 / 1000000000) (Real.log (879 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (504084201 / 1000000000) ≤ -Real.log (1280 / 2119) ∧
    -Real.log (1280 / 2119) ≤ (252042101 / 500000000) := by
  have h := checkLog_sound (w := (839 / 3399)) (n := 12)
    (lo := (504084201 / 1000000000)) (hi := (252042101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2119 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2119 / 1280) = 1/(1280 / 2119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (504084201 / 1000000000) (252042101 / 500000000) (Real.log (2119 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2119 / 1280) = -Real.log (1280 / 2119) := by
    rw [show ((2119 / 1280) : ℝ) = ((1280 / 2119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (13319631 / 12500000) ≤ -Real.log (441 / 1280) ∧
    -Real.log (441 / 1280) ≤ (532785241 / 500000000) := by
  have h := checkLog_sound (w := (199 / 1081)) (n := 12)
    (lo := (3724233 / 10000000)) (hi := (372423301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 441) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 441) = 1/(441 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-532785241 / 500000000) (-13319631 / 12500000) (Real.log (441 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (387805423 / 1000000000) ≤ -Real.log (1000000 / 1473743) ∧
    -Real.log (1000000 / 1473743) ≤ (24237839 / 62500000) := by
  have h := checkLog_sound (w := (473743 / 2473743)) (n := 12)
    (lo := (387805423 / 1000000000)) (hi := (24237839 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1473743 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1473743 / 1000000) = 1/(1000000 / 1473743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (387805423 / 1000000000) (24237839 / 62500000) (Real.log (1473743 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1473743 / 1000000) = -Real.log (1000000 / 1473743) := by
    rw [show ((1473743 / 1000000) : ℝ) = ((1000000 / 1473743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (80245699 / 125000000) ≤ -Real.log (526257 / 1000000) ∧
    -Real.log (526257 / 1000000) ≤ (641965593 / 1000000000) := by
  have h := checkLog_sound (w := (473743 / 1526257)) (n := 12)
    (lo := (80245699 / 125000000)) (hi := (641965593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 526257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 526257) = 1/(526257 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-641965593 / 1000000000) (-80245699 / 125000000) (Real.log (526257 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (388411857 / 1000000000) ≤ -Real.log (1000000 / 1474637) ∧
    -Real.log (1000000 / 1474637) ≤ (194205929 / 500000000) := by
  have h := checkLog_sound (w := (474637 / 2474637)) (n := 12)
    (lo := (388411857 / 1000000000)) (hi := (194205929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1474637 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1474637 / 1000000) = 1/(1000000 / 1474637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (388411857 / 1000000000) (194205929 / 500000000) (Real.log (1474637 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1474637 / 1000000) = -Real.log (1000000 / 1474637) := by
    rw [show ((1474637 / 1000000) : ℝ) = ((1000000 / 1474637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (321832913 / 500000000) ≤ -Real.log (525363 / 1000000) ∧
    -Real.log (525363 / 1000000) ≤ (643665827 / 1000000000) := by
  have h := checkLog_sound (w := (474637 / 1525363)) (n := 12)
    (lo := (321832913 / 500000000)) (hi := (643665827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 525363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 525363) = 1/(525363 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-643665827 / 1000000000) (-321832913 / 500000000) (Real.log (525363 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (76338807 / 250000000) ≤ -Real.log (1000000 / 1357107) ∧
    -Real.log (1000000 / 1357107) ≤ (305355229 / 1000000000) := by
  have h := checkLog_sound (w := (357107 / 2357107)) (n := 12)
    (lo := (76338807 / 250000000)) (hi := (305355229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1357107 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1357107 / 1000000) = 1/(1000000 / 1357107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (76338807 / 250000000) (305355229 / 1000000000) (Real.log (1357107 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1357107 / 1000000) = -Real.log (1000000 / 1357107) := by
    rw [show ((1357107 / 1000000) : ℝ) = ((1000000 / 1357107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (27611061 / 62500000) ≤ -Real.log (642893 / 1000000) ∧
    -Real.log (642893 / 1000000) ≤ (441776977 / 1000000000) := by
  have h := checkLog_sound (w := (357107 / 1642893)) (n := 12)
    (lo := (27611061 / 62500000)) (hi := (441776977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 642893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 642893) = 1/(642893 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-441776977 / 1000000000) (-27611061 / 62500000) (Real.log (642893 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (61183459 / 200000000) ≤ -Real.log (100000 / 135787) ∧
    -Real.log (100000 / 135787) ≤ (19119831 / 62500000) := by
  have h := checkLog_sound (w := (35787 / 235787)) (n := 12)
    (lo := (61183459 / 200000000)) (hi := (19119831 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135787 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135787 / 100000) = 1/(100000 / 135787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (61183459 / 200000000) (19119831 / 62500000) (Real.log (135787 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (135787 / 100000) = -Real.log (100000 / 135787) := by
    rw [show ((135787 / 100000) : ℝ) = ((100000 / 135787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (442964503 / 1000000000) ≤ -Real.log (64213 / 100000) ∧
    -Real.log (64213 / 100000) ≤ (55370563 / 125000000) := by
  have h := checkLog_sound (w := (35787 / 164213)) (n := 12)
    (lo := (442964503 / 1000000000)) (hi := (55370563 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 64213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 64213) = 1/(64213 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-55370563 / 125000000) (-442964503 / 1000000000) (Real.log (64213 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (514885507 / 500000000) ≤ -Real.log (125000000000 / 350053063427) ∧
    -Real.log (125000000000 / 350053063427) ≤ (128721377 / 125000000) := by
  have h := checkLog_sound (w := (100053063427 / 600053063427)) (n := 12)
    (lo := (168311917 / 500000000)) (hi := (67324767 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((350053063427 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(350053063427 / 250000000000) = 1/(125000000000 / 350053063427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (514885507 / 500000000) (128721377 / 125000000) (Real.log (350053063427 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (350053063427 / 125000000000) = -Real.log (125000000000 / 350053063427) := by
    rw [show ((350053063427 / 125000000000) : ℝ) = ((125000000000 / 350053063427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1032077683 / 1000000000) ≤ -Real.log (500000000000 / 1403445807947) ∧
    -Real.log (500000000000 / 1403445807947) ≤ (206415537 / 200000000) := by
  have h := checkLog_sound (w := (403445807947 / 2403445807947)) (n := 12)
    (lo := (338930503 / 1000000000)) (hi := (42366313 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1403445807947 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1403445807947 / 1000000000000) = 1/(500000000000 / 1403445807947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1032077683 / 1000000000) (206415537 / 200000000) (Real.log (1403445807947 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1403445807947 / 500000000000) = -Real.log (500000000000 / 1403445807947) := by
    rw [show ((1403445807947 / 500000000000) : ℝ) = ((500000000000 / 1403445807947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (747132203 / 1000000000) ≤ -Real.log (250000000000 / 527734397481) ∧
    -Real.log (250000000000 / 527734397481) ≤ (149426441 / 200000000) := by
  have h := checkLog_sound (w := (27734397481 / 1027734397481)) (n := 12)
    (lo := (53985023 / 1000000000)) (hi := (210879 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((527734397481 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(527734397481 / 500000000000) = 1/(250000000000 / 527734397481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (747132203 / 1000000000) (149426441 / 200000000) (Real.log (527734397481 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (527734397481 / 250000000000) = -Real.log (250000000000 / 527734397481) := by
    rw [show ((527734397481 / 250000000000) : ℝ) = ((250000000000 / 527734397481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (374440899 / 500000000) ≤ -Real.log (25000000000 / 52865852709) ∧
    -Real.log (25000000000 / 52865852709) ≤ (3744409 / 5000000) := by
  have h := checkLog_sound (w := (2865852709 / 102865852709)) (n := 12)
    (lo := (27867309 / 500000000)) (hi := (55734619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52865852709 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(52865852709 / 50000000000) = 1/(25000000000 / 52865852709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (374440899 / 500000000) (3744409 / 5000000) (Real.log (52865852709 / 25000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (52865852709 / 25000000000) = -Real.log (25000000000 / 52865852709) := by
    rw [show ((52865852709 / 25000000000) : ℝ) = ((25000000000 / 52865852709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0159

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0160Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0160
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

theorem reflection_log_1_neg : (70868503 / 250000000) ≤ -Real.log (2560 / 3399) ∧
    -Real.log (2560 / 3399) ≤ (283474013 / 1000000000) := by
  have h := checkLog_sound (w := (839 / 5959)) (n := 12)
    (lo := (70868503 / 250000000)) (hi := (283474013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3399 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3399 / 2560) = 1/(2560 / 3399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (70868503 / 250000000) (283474013 / 1000000000) (Real.log (3399 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3399 / 2560) = -Real.log (2560 / 3399) := by
    rw [show ((3399 / 2560) : ℝ) = ((2560 / 3399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (397101741 / 1000000000) ≤ -Real.log (1721 / 2560) ∧
    -Real.log (1721 / 2560) ≤ (198550871 / 500000000) := by
  have h := checkLog_sound (w := (839 / 4281)) (n := 12)
    (lo := (397101741 / 1000000000)) (hi := (198550871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1721) = 1/(1721 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-198550871 / 500000000) (-397101741 / 1000000000) (Real.log (1721 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (8844769 / 31250000) ≤ -Real.log (1024 / 1359) ∧
    -Real.log (1024 / 1359) ≤ (283032609 / 1000000000) := by
  have h := checkLog_sound (w := (335 / 2383)) (n := 12)
    (lo := (8844769 / 31250000)) (hi := (283032609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1359 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1359 / 1024) = 1/(1024 / 1359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (8844769 / 31250000) (283032609 / 1000000000) (Real.log (1359 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1359 / 1024) = -Real.log (1024 / 1359) := by
    rw [show ((1359 / 1024) : ℝ) = ((1024 / 1359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (198115267 / 500000000) ≤ -Real.log (689 / 1024) ∧
    -Real.log (689 / 1024) ≤ (79246107 / 200000000) := by
  have h := checkLog_sound (w := (335 / 1713)) (n := 12)
    (lo := (198115267 / 500000000)) (hi := (79246107 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 689) = 1/(689 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-79246107 / 200000000) (-198115267 / 500000000) (Real.log (689 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (504084201 / 1000000000) ≤ -Real.log (1280 / 2119) ∧
    -Real.log (1280 / 2119) ≤ (252042101 / 500000000) := by
  have h := checkLog_sound (w := (839 / 3399)) (n := 12)
    (lo := (504084201 / 1000000000)) (hi := (252042101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2119 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2119 / 1280) = 1/(1280 / 2119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (504084201 / 1000000000) (252042101 / 500000000) (Real.log (2119 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2119 / 1280) = -Real.log (1280 / 2119) := by
    rw [show ((2119 / 1280) : ℝ) = ((1280 / 2119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (13319631 / 12500000) ≤ -Real.log (441 / 1280) ∧
    -Real.log (441 / 1280) ≤ (532785241 / 500000000) := by
  have h := checkLog_sound (w := (199 / 1081)) (n := 12)
    (lo := (3724233 / 10000000)) (hi := (372423301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 441) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 441) = 1/(441 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-532785241 / 500000000) (-13319631 / 12500000) (Real.log (441 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (503376069 / 1000000000) ≤ -Real.log (512 / 847) ∧
    -Real.log (512 / 847) ≤ (50337607 / 100000000) := by
  have h := checkLog_sound (w := (335 / 1359)) (n := 12)
    (lo := (503376069 / 1000000000)) (hi := (50337607 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((847 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(847 / 512) = 1/(512 / 847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (503376069 / 1000000000) (50337607 / 100000000) (Real.log (847 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (847 / 512) = -Real.log (512 / 847) := by
    rw [show ((847 / 512) : ℝ) = ((512 / 847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1062174891 / 1000000000) ≤ -Real.log (177 / 512) ∧
    -Real.log (177 / 512) ≤ (1062174893 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 433)) (n := 12)
    (lo := (369027711 / 1000000000)) (hi := (2883029 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 177) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 177) = 1/(177 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1062174893 / 1000000000) (-1062174891 / 1000000000) (Real.log (177 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (387199299 / 1000000000) ≤ -Real.log (20000 / 29457) ∧
    -Real.log (20000 / 29457) ≤ (3871993 / 10000000) := by
  have h := checkLog_sound (w := (9457 / 49457)) (n := 12)
    (lo := (387199299 / 1000000000)) (hi := (3871993 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29457 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29457 / 20000) = 1/(20000 / 29457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (387199299 / 1000000000) (3871993 / 10000000) (Real.log (29457 / 20000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (29457 / 20000) = -Real.log (20000 / 29457) := by
    rw [show ((29457 / 20000) : ℝ) = ((20000 / 29457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (32013507 / 50000000) ≤ -Real.log (10543 / 20000) ∧
    -Real.log (10543 / 20000) ≤ (640270141 / 1000000000) := by
  have h := checkLog_sound (w := (9457 / 30543)) (n := 12)
    (lo := (32013507 / 50000000)) (hi := (640270141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 10543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 10543) = 1/(10543 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-640270141 / 1000000000) (-32013507 / 50000000) (Real.log (10543 / 20000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (387806101 / 1000000000) ≤ -Real.log (62500 / 92109) ∧
    -Real.log (62500 / 92109) ≤ (193903051 / 500000000) := by
  have h := checkLog_sound (w := (29609 / 154609)) (n := 12)
    (lo := (387806101 / 1000000000)) (hi := (193903051 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92109 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92109 / 62500) = 1/(62500 / 92109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (387806101 / 1000000000) (193903051 / 500000000) (Real.log (92109 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (92109 / 62500) = -Real.log (62500 / 92109) := by
    rw [show ((92109 / 62500) : ℝ) = ((62500 / 92109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (160491873 / 250000000) ≤ -Real.log (32891 / 62500) ∧
    -Real.log (32891 / 62500) ≤ (641967493 / 1000000000) := by
  have h := checkLog_sound (w := (29609 / 95391)) (n := 12)
    (lo := (160491873 / 250000000)) (hi := (641967493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 32891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 32891) = 1/(32891 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-641967493 / 1000000000) (-160491873 / 250000000) (Real.log (32891 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (304794319 / 1000000000) ≤ -Real.log (500000 / 678173) ∧
    -Real.log (500000 / 678173) ≤ (3809929 / 12500000) := by
  have h := checkLog_sound (w := (178173 / 1178173)) (n := 12)
    (lo := (304794319 / 1000000000)) (hi := (3809929 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678173 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(678173 / 500000) = 1/(500000 / 678173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (304794319 / 1000000000) (3809929 / 12500000) (Real.log (678173 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (678173 / 500000) = -Real.log (500000 / 678173) := by
    rw [show ((678173 / 500000) : ℝ) = ((500000 / 678173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (110148491 / 250000000) ≤ -Real.log (321827 / 500000) ∧
    -Real.log (321827 / 500000) ≤ (88118793 / 200000000) := by
  have h := checkLog_sound (w := (178173 / 821827)) (n := 12)
    (lo := (110148491 / 250000000)) (hi := (88118793 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 321827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 321827) = 1/(321827 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-88118793 / 200000000) (-110148491 / 250000000) (Real.log (321827 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (61071193 / 200000000) ≤ -Real.log (250000 / 339277) ∧
    -Real.log (250000 / 339277) ≤ (152677983 / 500000000) := by
  have h := checkLog_sound (w := (89277 / 589277)) (n := 12)
    (lo := (61071193 / 200000000)) (hi := (152677983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339277 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339277 / 250000) = 1/(250000 / 339277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (61071193 / 200000000) (152677983 / 500000000) (Real.log (339277 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (339277 / 250000) = -Real.log (250000 / 339277) := by
    rw [show ((339277 / 250000) : ℝ) = ((250000 / 339277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (441778531 / 1000000000) ≤ -Real.log (160723 / 250000) ∧
    -Real.log (160723 / 250000) ≤ (110444633 / 250000000) := by
  have h := checkLog_sound (w := (89277 / 410723)) (n := 12)
    (lo := (441778531 / 1000000000)) (hi := (110444633 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 160723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 160723) = 1/(160723 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-110444633 / 250000000) (-441778531 / 1000000000) (Real.log (160723 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1027469439 / 1000000000) ≤ -Real.log (500000000000 / 1396993265673) ∧
    -Real.log (500000000000 / 1396993265673) ≤ (1027469441 / 1000000000) := by
  have h := checkLog_sound (w := (396993265673 / 2396993265673)) (n := 12)
    (lo := (334322259 / 1000000000)) (hi := (16716113 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1396993265673 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1396993265673 / 1000000000000) = 1/(500000000000 / 1396993265673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1027469439 / 1000000000) (1027469441 / 1000000000) (Real.log (1396993265673 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1396993265673 / 500000000000) = -Real.log (500000000000 / 1396993265673) := by
    rw [show ((1396993265673 / 500000000000) : ℝ) = ((500000000000 / 1396993265673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1029773593 / 1000000000) ≤ -Real.log (500000000000 / 1400215864523) ∧
    -Real.log (500000000000 / 1400215864523) ≤ (205954719 / 200000000) := by
  have h := checkLog_sound (w := (400215864523 / 2400215864523)) (n := 12)
    (lo := (336626413 / 1000000000)) (hi := (168313207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1400215864523 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1400215864523 / 1000000000000) = 1/(500000000000 / 1400215864523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1029773593 / 1000000000) (205954719 / 200000000) (Real.log (1400215864523 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1400215864523 / 500000000000) = -Real.log (500000000000 / 1400215864523) := by
    rw [show ((1400215864523 / 500000000000) : ℝ) = ((500000000000 / 1400215864523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (372694141 / 500000000) ≤ -Real.log (500000000000 / 1053629745173) ∧
    -Real.log (500000000000 / 1053629745173) ≤ (186347071 / 250000000) := by
  have h := checkLog_sound (w := (53629745173 / 2053629745173)) (n := 12)
    (lo := (26120551 / 500000000)) (hi := (52241103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1053629745173 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1053629745173 / 1000000000000) = 1/(500000000000 / 1053629745173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (372694141 / 500000000) (186347071 / 250000000) (Real.log (1053629745173 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1053629745173 / 500000000000) = -Real.log (500000000000 / 1053629745173) := by
    rw [show ((1053629745173 / 500000000000) : ℝ) = ((500000000000 / 1053629745173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (149426899 / 200000000) ≤ -Real.log (10000000000 / 21109424289) ∧
    -Real.log (10000000000 / 21109424289) ≤ (747134497 / 1000000000) := by
  have h := checkLog_sound (w := (1109424289 / 41109424289)) (n := 12)
    (lo := (10797463 / 200000000)) (hi := (13496829 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21109424289 / 20000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(21109424289 / 20000000000) = 1/(10000000000 / 21109424289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (149426899 / 200000000) (747134497 / 1000000000) (Real.log (21109424289 / 10000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (21109424289 / 10000000000) = -Real.log (10000000000 / 21109424289) := by
    rw [show ((21109424289 / 10000000000) : ℝ) = ((10000000000 / 21109424289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0160

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0161Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0161
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

theorem reflection_log_1_neg : (8844769 / 31250000) ≤ -Real.log (1024 / 1359) ∧
    -Real.log (1024 / 1359) ≤ (283032609 / 1000000000) := by
  have h := checkLog_sound (w := (335 / 2383)) (n := 12)
    (lo := (8844769 / 31250000)) (hi := (283032609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1359 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1359 / 1024) = 1/(1024 / 1359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (8844769 / 31250000) (283032609 / 1000000000) (Real.log (1359 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1359 / 1024) = -Real.log (1024 / 1359) := by
    rw [show ((1359 / 1024) : ℝ) = ((1024 / 1359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (198115267 / 500000000) ≤ -Real.log (689 / 1024) ∧
    -Real.log (689 / 1024) ≤ (79246107 / 200000000) := by
  have h := checkLog_sound (w := (335 / 1713)) (n := 12)
    (lo := (198115267 / 500000000)) (hi := (79246107 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 689) = 1/(689 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-79246107 / 200000000) (-198115267 / 500000000) (Real.log (689 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (282591009 / 1000000000) ≤ -Real.log (640 / 849) ∧
    -Real.log (640 / 849) ≤ (28259101 / 100000000) := by
  have h := checkLog_sound (w := (209 / 1489)) (n := 12)
    (lo := (282591009 / 1000000000)) (hi := (28259101 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((849 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(849 / 640) = 1/(640 / 849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (282591009 / 1000000000) (28259101 / 100000000) (Real.log (849 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (849 / 640) = -Real.log (640 / 849) := by
    rw [show ((849 / 640) : ℝ) = ((640 / 849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (197680043 / 500000000) ≤ -Real.log (431 / 640) ∧
    -Real.log (431 / 640) ≤ (395360087 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 1071)) (n := 12)
    (lo := (197680043 / 500000000)) (hi := (395360087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 431) = 1/(431 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-395360087 / 1000000000) (-197680043 / 500000000) (Real.log (431 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (503376069 / 1000000000) ≤ -Real.log (512 / 847) ∧
    -Real.log (512 / 847) ≤ (50337607 / 100000000) := by
  have h := checkLog_sound (w := (335 / 1359)) (n := 12)
    (lo := (503376069 / 1000000000)) (hi := (50337607 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((847 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(847 / 512) = 1/(512 / 847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (503376069 / 1000000000) (50337607 / 100000000) (Real.log (847 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (847 / 512) = -Real.log (512 / 847) := by
    rw [show ((847 / 512) : ℝ) = ((512 / 847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1062174891 / 1000000000) ≤ -Real.log (177 / 512) ∧
    -Real.log (177 / 512) ≤ (1062174893 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 433)) (n := 12)
    (lo := (369027711 / 1000000000)) (hi := (2883029 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 177) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 177) = 1/(177 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1062174893 / 1000000000) (-1062174891 / 1000000000) (Real.log (177 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (125666859 / 250000000) ≤ -Real.log (320 / 529) ∧
    -Real.log (320 / 529) ≤ (502667437 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 849)) (n := 12)
    (lo := (125666859 / 250000000)) (hi := (502667437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((529 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(529 / 320) = 1/(320 / 529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (125666859 / 250000000) (502667437 / 1000000000) (Real.log (529 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (529 / 320) = -Real.log (320 / 529) := by
    rw [show ((529 / 320) : ℝ) = ((320 / 529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1058790793 / 1000000000) ≤ -Real.log (111 / 320) ∧
    -Real.log (111 / 320) ≤ (211758159 / 200000000) := by
  have h := checkLog_sound (w := (49 / 271)) (n := 12)
    (lo := (365643613 / 1000000000)) (hi := (182821807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 111) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 111) = 1/(111 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-211758159 / 200000000) (-1058790793 / 1000000000) (Real.log (111 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (386592807 / 1000000000) ≤ -Real.log (1000000 / 1471957) ∧
    -Real.log (1000000 / 1471957) ≤ (48324101 / 125000000) := by
  have h := checkLog_sound (w := (471957 / 2471957)) (n := 12)
    (lo := (386592807 / 1000000000)) (hi := (48324101 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1471957 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1471957 / 1000000) = 1/(1000000 / 1471957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (386592807 / 1000000000) (48324101 / 125000000) (Real.log (1471957 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1471957 / 1000000) = -Real.log (1000000 / 1471957) := by
    rw [show ((1471957 / 1000000) : ℝ) = ((1000000 / 1471957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (638577559 / 1000000000) ≤ -Real.log (528043 / 1000000) ∧
    -Real.log (528043 / 1000000) ≤ (15964439 / 25000000) := by
  have h := checkLog_sound (w := (471957 / 1528043)) (n := 12)
    (lo := (638577559 / 1000000000)) (hi := (15964439 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 528043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 528043) = 1/(528043 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-15964439 / 25000000) (-638577559 / 1000000000) (Real.log (528043 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (193599989 / 500000000) ≤ -Real.log (1000000 / 1472851) ∧
    -Real.log (1000000 / 1472851) ≤ (387199979 / 1000000000) := by
  have h := checkLog_sound (w := (472851 / 2472851)) (n := 12)
    (lo := (193599989 / 500000000)) (hi := (387199979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1472851 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1472851 / 1000000) = 1/(1000000 / 1472851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (193599989 / 500000000) (387199979 / 1000000000) (Real.log (1472851 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1472851 / 1000000) = -Real.log (1000000 / 1472851) := by
    rw [show ((1472851 / 1000000) : ℝ) = ((1000000 / 1472851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (640272037 / 1000000000) ≤ -Real.log (527149 / 1000000) ∧
    -Real.log (527149 / 1000000) ≤ (320136019 / 500000000) := by
  have h := checkLog_sound (w := (472851 / 1527149)) (n := 12)
    (lo := (640272037 / 1000000000)) (hi := (320136019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 527149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 527149) = 1/(527149 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-320136019 / 500000000) (-640272037 / 1000000000) (Real.log (527149 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (60846619 / 200000000) ≤ -Real.log (200000 / 271117) ∧
    -Real.log (200000 / 271117) ≤ (38029137 / 125000000) := by
  have h := checkLog_sound (w := (71117 / 471117)) (n := 12)
    (lo := (60846619 / 200000000)) (hi := (38029137 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271117 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271117 / 200000) = 1/(200000 / 271117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (60846619 / 200000000) (38029137 / 125000000) (Real.log (271117 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (271117 / 200000) = -Real.log (200000 / 271117) := by
    rw [show ((271117 / 200000) : ℝ) = ((200000 / 271117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (8788247 / 20000000) ≤ -Real.log (128883 / 200000) ∧
    -Real.log (128883 / 200000) ≤ (439412351 / 1000000000) := by
  have h := checkLog_sound (w := (71117 / 328883)) (n := 12)
    (lo := (8788247 / 20000000)) (hi := (439412351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 128883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 128883) = 1/(128883 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-439412351 / 1000000000) (-8788247 / 20000000) (Real.log (128883 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (19049691 / 62500000) ≤ -Real.log (1000000 / 1356347) ∧
    -Real.log (1000000 / 1356347) ≤ (304795057 / 1000000000) := by
  have h := checkLog_sound (w := (356347 / 2356347)) (n := 12)
    (lo := (19049691 / 62500000)) (hi := (304795057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1356347 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1356347 / 1000000) = 1/(1000000 / 1356347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (19049691 / 62500000) (304795057 / 1000000000) (Real.log (1356347 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1356347 / 1000000) = -Real.log (1000000 / 1356347) := by
    rw [show ((1356347 / 1000000) : ℝ) = ((1000000 / 1356347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (440595517 / 1000000000) ≤ -Real.log (643653 / 1000000) ∧
    -Real.log (643653 / 1000000) ≤ (220297759 / 500000000) := by
  have h := checkLog_sound (w := (356347 / 1643653)) (n := 12)
    (lo := (440595517 / 1000000000)) (hi := (220297759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 643653) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 643653) = 1/(643653 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-220297759 / 500000000) (-440595517 / 1000000000) (Real.log (643653 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (512585183 / 500000000) ≤ -Real.log (500000000000 / 1393785165223) ∧
    -Real.log (500000000000 / 1393785165223) ≤ (16018287 / 15625000) := by
  have h := checkLog_sound (w := (393785165223 / 2393785165223)) (n := 12)
    (lo := (166011593 / 500000000)) (hi := (332023187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1393785165223 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1393785165223 / 1000000000000) = 1/(500000000000 / 1393785165223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (512585183 / 500000000) (16018287 / 15625000) (Real.log (1393785165223 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1393785165223 / 500000000000) = -Real.log (500000000000 / 1393785165223) := by
    rw [show ((1393785165223 / 500000000000) : ℝ) = ((500000000000 / 1393785165223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (205494403 / 200000000) ≤ -Real.log (100000000000 / 279399372853) ∧
    -Real.log (100000000000 / 279399372853) ≤ (1027472017 / 1000000000) := by
  have h := checkLog_sound (w := (79399372853 / 479399372853)) (n := 12)
    (lo := (66864967 / 200000000)) (hi := (83581209 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279399372853 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(279399372853 / 200000000000) = 1/(100000000000 / 279399372853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (205494403 / 200000000) (1027472017 / 1000000000) (Real.log (279399372853 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (279399372853 / 100000000000) = -Real.log (100000000000 / 279399372853) := by
    rw [show ((279399372853 / 100000000000) : ℝ) = ((100000000000 / 279399372853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (148729089 / 200000000) ≤ -Real.log (500000000000 / 1051795038911) ∧
    -Real.log (500000000000 / 1051795038911) ≤ (743645447 / 1000000000) := by
  have h := checkLog_sound (w := (51795038911 / 2051795038911)) (n := 12)
    (lo := (10099653 / 200000000)) (hi := (25249133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1051795038911 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1051795038911 / 1000000000000) = 1/(500000000000 / 1051795038911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (148729089 / 200000000) (743645447 / 1000000000) (Real.log (1051795038911 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1051795038911 / 500000000000) = -Real.log (500000000000 / 1051795038911) := by
    rw [show ((1051795038911 / 500000000000) : ℝ) = ((500000000000 / 1051795038911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (745390573 / 1000000000) ≤ -Real.log (500000000000 / 1053632158943) ∧
    -Real.log (500000000000 / 1053632158943) ≤ (29815623 / 40000000) := by
  have h := checkLog_sound (w := (53632158943 / 2053632158943)) (n := 12)
    (lo := (52243393 / 1000000000)) (hi := (26121697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1053632158943 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1053632158943 / 1000000000000) = 1/(500000000000 / 1053632158943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (745390573 / 1000000000) (29815623 / 40000000) (Real.log (1053632158943 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1053632158943 / 500000000000) = -Real.log (500000000000 / 1053632158943) := by
    rw [show ((1053632158943 / 500000000000) : ℝ) = ((500000000000 / 1053632158943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0161

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0162Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0162
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

theorem reflection_log_1_neg : (282591009 / 1000000000) ≤ -Real.log (640 / 849) ∧
    -Real.log (640 / 849) ≤ (28259101 / 100000000) := by
  have h := checkLog_sound (w := (209 / 1489)) (n := 12)
    (lo := (282591009 / 1000000000)) (hi := (28259101 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((849 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(849 / 640) = 1/(640 / 849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (282591009 / 1000000000) (28259101 / 100000000) (Real.log (849 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (849 / 640) = -Real.log (640 / 849) := by
    rw [show ((849 / 640) : ℝ) = ((640 / 849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (197680043 / 500000000) ≤ -Real.log (431 / 640) ∧
    -Real.log (431 / 640) ≤ (395360087 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 1071)) (n := 12)
    (lo := (197680043 / 500000000)) (hi := (395360087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 431) = 1/(431 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-395360087 / 1000000000) (-197680043 / 500000000) (Real.log (431 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (8817163 / 31250000) ≤ -Real.log (5120 / 6789) ∧
    -Real.log (5120 / 6789) ≤ (282149217 / 1000000000) := by
  have h := checkLog_sound (w := (1669 / 11909)) (n := 12)
    (lo := (8817163 / 31250000)) (hi := (282149217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6789 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6789 / 5120) = 1/(5120 / 6789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (8817163 / 31250000) (282149217 / 1000000000) (Real.log (6789 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6789 / 5120) = -Real.log (5120 / 6789) := by
    rw [show ((6789 / 5120) : ℝ) = ((5120 / 6789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (197245197 / 500000000) ≤ -Real.log (3451 / 5120) ∧
    -Real.log (3451 / 5120) ≤ (78898079 / 200000000) := by
  have h := checkLog_sound (w := (1669 / 8571)) (n := 12)
    (lo := (197245197 / 500000000)) (hi := (78898079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3451) = 1/(3451 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-78898079 / 200000000) (-197245197 / 500000000) (Real.log (3451 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (125666859 / 250000000) ≤ -Real.log (320 / 529) ∧
    -Real.log (320 / 529) ≤ (502667437 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 849)) (n := 12)
    (lo := (125666859 / 250000000)) (hi := (502667437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((529 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(529 / 320) = 1/(320 / 529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (125666859 / 250000000) (502667437 / 1000000000) (Real.log (529 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (529 / 320) = -Real.log (320 / 529) := by
    rw [show ((529 / 320) : ℝ) = ((320 / 529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1058790793 / 1000000000) ≤ -Real.log (111 / 320) ∧
    -Real.log (111 / 320) ≤ (211758159 / 200000000) := by
  have h := checkLog_sound (w := (49 / 271)) (n := 12)
    (lo := (365643613 / 1000000000)) (hi := (182821807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 111) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 111) = 1/(111 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-211758159 / 200000000) (-1058790793 / 1000000000) (Real.log (111 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (501958299 / 1000000000) ≤ -Real.log (2560 / 4229) ∧
    -Real.log (2560 / 4229) ≤ (5019583 / 10000000) := by
  have h := checkLog_sound (w := (1669 / 6789)) (n := 12)
    (lo := (501958299 / 1000000000)) (hi := (5019583 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4229 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4229 / 2560) = 1/(2560 / 4229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (501958299 / 1000000000) (5019583 / 10000000) (Real.log (4229 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4229 / 2560) = -Real.log (2560 / 4229) := by
    rw [show ((4229 / 2560) : ℝ) = ((2560 / 4229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1055418109 / 1000000000) ≤ -Real.log (891 / 2560) ∧
    -Real.log (891 / 2560) ≤ (1055418111 / 1000000000) := by
  have h := checkLog_sound (w := (389 / 2171)) (n := 12)
    (lo := (362270929 / 1000000000)) (hi := (36227093 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 891) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 891) = 1/(891 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1055418111 / 1000000000) (-1055418109 / 1000000000) (Real.log (891 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (96496657 / 250000000) ≤ -Real.log (200000 / 294213) ∧
    -Real.log (200000 / 294213) ≤ (385986629 / 1000000000) := by
  have h := checkLog_sound (w := (94213 / 494213)) (n := 12)
    (lo := (96496657 / 250000000)) (hi := (385986629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294213 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294213 / 200000) = 1/(200000 / 294213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (96496657 / 250000000) (385986629 / 1000000000) (Real.log (294213 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (294213 / 200000) = -Real.log (200000 / 294213) := by
    rw [show ((294213 / 200000) : ℝ) = ((200000 / 294213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (4975701 / 7812500) ≤ -Real.log (105787 / 200000) ∧
    -Real.log (105787 / 200000) ≤ (636889729 / 1000000000) := by
  have h := checkLog_sound (w := (94213 / 305787)) (n := 12)
    (lo := (4975701 / 7812500)) (hi := (636889729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 105787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 105787) = 1/(105787 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-636889729 / 1000000000) (-4975701 / 7812500) (Real.log (105787 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (386593487 / 1000000000) ≤ -Real.log (500000 / 735979) ∧
    -Real.log (500000 / 735979) ≤ (24162093 / 62500000) := by
  have h := checkLog_sound (w := (235979 / 1235979)) (n := 12)
    (lo := (386593487 / 1000000000)) (hi := (24162093 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735979 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735979 / 500000) = 1/(500000 / 735979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (386593487 / 1000000000) (24162093 / 62500000) (Real.log (735979 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (735979 / 500000) = -Real.log (500000 / 735979) := by
    rw [show ((735979 / 500000) : ℝ) = ((500000 / 735979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (159644863 / 250000000) ≤ -Real.log (264021 / 500000) ∧
    -Real.log (264021 / 500000) ≤ (638579453 / 1000000000) := by
  have h := checkLog_sound (w := (235979 / 764021)) (n := 12)
    (lo := (159644863 / 250000000)) (hi := (638579453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 264021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 264021) = 1/(264021 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-638579453 / 1000000000) (-159644863 / 250000000) (Real.log (264021 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (37959129 / 125000000) ≤ -Real.log (500000 / 677413) ∧
    -Real.log (500000 / 677413) ≤ (303673033 / 1000000000) := by
  have h := checkLog_sound (w := (177413 / 1177413)) (n := 12)
    (lo := (37959129 / 125000000)) (hi := (303673033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677413 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677413 / 500000) = 1/(500000 / 677413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (37959129 / 125000000) (303673033 / 1000000000) (Real.log (677413 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (677413 / 500000) = -Real.log (500000 / 677413) := by
    rw [show ((677413 / 500000) : ℝ) = ((500000 / 677413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (438235231 / 1000000000) ≤ -Real.log (322587 / 500000) ∧
    -Real.log (322587 / 500000) ≤ (13694851 / 31250000) := by
  have h := checkLog_sound (w := (177413 / 822587)) (n := 12)
    (lo := (438235231 / 1000000000)) (hi := (13694851 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 322587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 322587) = 1/(322587 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-13694851 / 31250000) (-438235231 / 1000000000) (Real.log (322587 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (304233833 / 1000000000) ≤ -Real.log (500000 / 677793) ∧
    -Real.log (500000 / 677793) ≤ (152116917 / 500000000) := by
  have h := checkLog_sound (w := (177793 / 1177793)) (n := 12)
    (lo := (304233833 / 1000000000)) (hi := (152116917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677793 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677793 / 500000) = 1/(500000 / 677793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (304233833 / 1000000000) (152116917 / 500000000) (Real.log (677793 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (677793 / 500000) = -Real.log (500000 / 677793) := by
    rw [show ((677793 / 500000) : ℝ) = ((500000 / 677793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (219706951 / 500000000) ≤ -Real.log (322207 / 500000) ∧
    -Real.log (322207 / 500000) ≤ (439413903 / 1000000000) := by
  have h := checkLog_sound (w := (177793 / 822207)) (n := 12)
    (lo := (219706951 / 500000000)) (hi := (439413903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 322207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 322207) = 1/(322207 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-439413903 / 1000000000) (-219706951 / 500000000) (Real.log (322207 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (204575271 / 200000000) ≤ -Real.log (500000000000 / 1390591471541) ∧
    -Real.log (500000000000 / 1390591471541) ≤ (1022876357 / 1000000000) := by
  have h := checkLog_sound (w := (390591471541 / 2390591471541)) (n := 12)
    (lo := (13189167 / 40000000)) (hi := (41216147 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1390591471541 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1390591471541 / 1000000000000) = 1/(500000000000 / 1390591471541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (204575271 / 200000000) (1022876357 / 1000000000) (Real.log (1390591471541 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1390591471541 / 500000000000) = -Real.log (500000000000 / 1390591471541) := by
    rw [show ((1390591471541 / 500000000000) : ℝ) = ((500000000000 / 1390591471541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1025172939 / 1000000000) ≤ -Real.log (500000000000 / 1393788751653) ∧
    -Real.log (500000000000 / 1393788751653) ≤ (1025172941 / 1000000000) := by
  have h := checkLog_sound (w := (393788751653 / 2393788751653)) (n := 12)
    (lo := (332025759 / 1000000000)) (hi := (2075161 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1393788751653 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1393788751653 / 1000000000000) = 1/(500000000000 / 1393788751653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1025172939 / 1000000000) (1025172941 / 1000000000) (Real.log (1393788751653 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1393788751653 / 500000000000) = -Real.log (500000000000 / 1393788751653) := by
    rw [show ((1393788751653 / 500000000000) : ℝ) = ((500000000000 / 1393788751653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (741908263 / 1000000000) ≤ -Real.log (500000000000 / 1049969465601) ∧
    -Real.log (500000000000 / 1049969465601) ≤ (148381653 / 200000000) := by
  have h := checkLog_sound (w := (49969465601 / 2049969465601)) (n := 12)
    (lo := (48761083 / 1000000000)) (hi := (12190271 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1049969465601 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1049969465601 / 1000000000000) = 1/(500000000000 / 1049969465601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (741908263 / 1000000000) (148381653 / 200000000) (Real.log (1049969465601 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1049969465601 / 500000000000) = -Real.log (500000000000 / 1049969465601) := by
    rw [show ((1049969465601 / 500000000000) : ℝ) = ((500000000000 / 1049969465601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (371823867 / 500000000) ≤ -Real.log (500000000000 / 1051797446983) ∧
    -Real.log (500000000000 / 1051797446983) ≤ (92955967 / 125000000) := by
  have h := checkLog_sound (w := (51797446983 / 2051797446983)) (n := 12)
    (lo := (25250277 / 500000000)) (hi := (10100111 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1051797446983 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1051797446983 / 1000000000000) = 1/(500000000000 / 1051797446983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (371823867 / 500000000) (92955967 / 125000000) (Real.log (1051797446983 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1051797446983 / 500000000000) = -Real.log (500000000000 / 1051797446983) := by
    rw [show ((1051797446983 / 500000000000) : ℝ) = ((500000000000 / 1051797446983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0162

end


