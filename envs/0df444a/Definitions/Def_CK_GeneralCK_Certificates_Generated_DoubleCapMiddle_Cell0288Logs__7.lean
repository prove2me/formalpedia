-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0288Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0288Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:27:37.0596+00:00
-- url     : https://prove2.me/theorems/330d2913-95b5-4aa2-a667-f0f49aee24cb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0288Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0289Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0288Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0289Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0290Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0291Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0292Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0293Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0294Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0288Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0289Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0290Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0291Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0292Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0293Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0294Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0288Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0289Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0290Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0291Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0292Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0293Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0294Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0288Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0289Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0290Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0291Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0292Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0293Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0294Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0288Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0288
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

theorem reflection_log_1_neg : (226730859 / 1000000000) ≤ -Real.log (5120 / 6423) ∧
    -Real.log (5120 / 6423) ≤ (11336543 / 50000000) := by
  have h := checkLog_sound (w := (1303 / 11543)) (n := 12)
    (lo := (226730859 / 1000000000)) (hi := (11336543 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6423 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6423 / 5120) = 1/(5120 / 6423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (226730859 / 1000000000) (11336543 / 50000000) (Real.log (6423 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6423 / 5120) = -Real.log (5120 / 6423) := by
    rw [show ((6423 / 5120) : ℝ) = ((5120 / 6423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (58737933 / 200000000) ≤ -Real.log (3817 / 5120) ∧
    -Real.log (3817 / 5120) ≤ (146844833 / 500000000) := by
  have h := checkLog_sound (w := (1303 / 8937)) (n := 12)
    (lo := (58737933 / 200000000)) (hi := (146844833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3817) = 1/(3817 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-146844833 / 500000000) (-58737933 / 200000000) (Real.log (3817 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (14156081 / 62500000) ≤ -Real.log (10240 / 12843) ∧
    -Real.log (10240 / 12843) ≤ (226497297 / 1000000000) := by
  have h := checkLog_sound (w := (2603 / 23083)) (n := 12)
    (lo := (14156081 / 62500000)) (hi := (226497297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12843 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12843 / 10240) = 1/(10240 / 12843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (14156081 / 62500000) (226497297 / 1000000000) (Real.log (12843 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12843 / 10240) = -Real.log (10240 / 12843) := by
    rw [show ((12843 / 10240) : ℝ) = ((10240 / 12843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (293296763 / 1000000000) ≤ -Real.log (7637 / 10240) ∧
    -Real.log (7637 / 10240) ≤ (73324191 / 250000000) := by
  have h := checkLog_sound (w := (2603 / 17877)) (n := 12)
    (lo := (293296763 / 1000000000)) (hi := (73324191 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7637) = 1/(7637 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-73324191 / 250000000) (-293296763 / 1000000000) (Real.log (7637 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (16457473 / 40000000) ≤ -Real.log (2560 / 3863) ∧
    -Real.log (2560 / 3863) ≤ (205718413 / 500000000) := by
  have h := checkLog_sound (w := (1303 / 6423)) (n := 12)
    (lo := (16457473 / 40000000)) (hi := (205718413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3863 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3863 / 2560) = 1/(2560 / 3863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (16457473 / 40000000) (205718413 / 500000000) (Real.log (3863 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3863 / 2560) = -Real.log (2560 / 3863) := by
    rw [show ((3863 / 2560) : ℝ) = ((2560 / 3863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (22227479 / 31250000) ≤ -Real.log (1257 / 2560) ∧
    -Real.log (1257 / 2560) ≤ (71127933 / 100000000) := by
  have h := checkLog_sound (w := (23 / 2537)) (n := 12)
    (lo := (4533037 / 250000000)) (hi := (18132149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1257) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1257) = 1/(1257 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-71127933 / 100000000) (-22227479 / 31250000) (Real.log (1257 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (8220969 / 20000000) ≤ -Real.log (5120 / 7723) ∧
    -Real.log (5120 / 7723) ≤ (411048451 / 1000000000) := by
  have h := checkLog_sound (w := (2603 / 12843)) (n := 12)
    (lo := (8220969 / 20000000)) (hi := (411048451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7723 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7723 / 5120) = 1/(5120 / 7723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (8220969 / 20000000) (411048451 / 1000000000) (Real.log (7723 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7723 / 5120) = -Real.log (5120 / 7723) := by
    rw [show ((7723 / 5120) : ℝ) = ((5120 / 7723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (355043361 / 500000000) ≤ -Real.log (2517 / 5120) ∧
    -Real.log (2517 / 5120) ≤ (177521681 / 250000000) := by
  have h := checkLog_sound (w := (43 / 5077)) (n := 12)
    (lo := (8469771 / 500000000)) (hi := (16939543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2517) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2517) = 1/(2517 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-177521681 / 250000000) (-355043361 / 500000000) (Real.log (2517 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (310309383 / 1000000000) ≤ -Real.log (1000000 / 1363847) ∧
    -Real.log (1000000 / 1363847) ≤ (38788673 / 125000000) := by
  have h := checkLog_sound (w := (363847 / 2363847)) (n := 12)
    (lo := (310309383 / 1000000000)) (hi := (38788673 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1363847 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1363847 / 1000000) = 1/(1000000 / 1363847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (310309383 / 1000000000) (38788673 / 125000000) (Real.log (1363847 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1363847 / 1000000) = -Real.log (1000000 / 1363847) := by
    rw [show ((1363847 / 1000000) : ℝ) = ((1000000 / 1363847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (226158089 / 500000000) ≤ -Real.log (636153 / 1000000) ∧
    -Real.log (636153 / 1000000) ≤ (452316179 / 1000000000) := by
  have h := checkLog_sound (w := (363847 / 1636153)) (n := 12)
    (lo := (226158089 / 500000000)) (hi := (452316179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 636153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 636153) = 1/(636153 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-452316179 / 1000000000) (-226158089 / 500000000) (Real.log (636153 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (310626083 / 1000000000) ≤ -Real.log (1000000 / 1364279) ∧
    -Real.log (1000000 / 1364279) ≤ (77656521 / 250000000) := by
  have h := checkLog_sound (w := (364279 / 2364279)) (n := 12)
    (lo := (310626083 / 1000000000)) (hi := (77656521 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1364279 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1364279 / 1000000) = 1/(1000000 / 1364279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (310626083 / 1000000000) (77656521 / 250000000) (Real.log (1364279 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1364279 / 1000000) = -Real.log (1000000 / 1364279) := by
    rw [show ((1364279 / 1000000) : ℝ) = ((1000000 / 1364279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (452995491 / 1000000000) ≤ -Real.log (635721 / 1000000) ∧
    -Real.log (635721 / 1000000) ≤ (113248873 / 250000000) := by
  have h := checkLog_sound (w := (364279 / 1635721)) (n := 12)
    (lo := (452995491 / 1000000000)) (hi := (113248873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 635721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 635721) = 1/(635721 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-113248873 / 250000000) (-452995491 / 1000000000) (Real.log (635721 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (118349233 / 500000000) ≤ -Real.log (1000000 / 1267059) ∧
    -Real.log (1000000 / 1267059) ≤ (236698467 / 1000000000) := by
  have h := checkLog_sound (w := (267059 / 2267059)) (n := 12)
    (lo := (118349233 / 500000000)) (hi := (236698467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1267059 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1267059 / 1000000) = 1/(1000000 / 1267059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (118349233 / 500000000) (236698467 / 1000000000) (Real.log (1267059 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1267059 / 1000000) = -Real.log (1000000 / 1267059) := by
    rw [show ((1267059 / 1000000) : ℝ) = ((1000000 / 1267059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (310690071 / 1000000000) ≤ -Real.log (732941 / 1000000) ∧
    -Real.log (732941 / 1000000) ≤ (38836259 / 125000000) := by
  have h := checkLog_sound (w := (267059 / 1732941)) (n := 12)
    (lo := (310690071 / 1000000000)) (hi := (38836259 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 732941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 732941) = 1/(732941 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-38836259 / 125000000) (-310690071 / 1000000000) (Real.log (732941 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (236967557 / 1000000000) ≤ -Real.log (5000 / 6337) ∧
    -Real.log (5000 / 6337) ≤ (118483779 / 500000000) := by
  have h := checkLog_sound (w := (1337 / 11337)) (n := 12)
    (lo := (236967557 / 1000000000)) (hi := (118483779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6337 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6337 / 5000) = 1/(5000 / 6337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (236967557 / 1000000000) (118483779 / 500000000) (Real.log (6337 / 5000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (6337 / 5000) = -Real.log (5000 / 6337) := by
    rw [show ((6337 / 5000) : ℝ) = ((5000 / 6337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (77788857 / 250000000) ≤ -Real.log (3663 / 5000) ∧
    -Real.log (3663 / 5000) ≤ (311155429 / 1000000000) := by
  have h := checkLog_sound (w := (1337 / 8663)) (n := 12)
    (lo := (77788857 / 250000000)) (hi := (311155429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 3663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 3663) = 1/(3663 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-311155429 / 1000000000) (-77788857 / 250000000) (Real.log (3663 / 5000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (762625561 / 1000000000) ≤ -Real.log (50000000000 / 107194888651) ∧
    -Real.log (50000000000 / 107194888651) ≤ (762625563 / 1000000000) := by
  have h := checkLog_sound (w := (7194888651 / 207194888651)) (n := 12)
    (lo := (69478381 / 1000000000)) (hi := (34739191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107194888651 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(107194888651 / 100000000000) = 1/(50000000000 / 107194888651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (762625561 / 1000000000) (762625563 / 1000000000) (Real.log (107194888651 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (107194888651 / 50000000000) = -Real.log (50000000000 / 107194888651) := by
    rw [show ((107194888651 / 50000000000) : ℝ) = ((50000000000 / 107194888651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (381810787 / 500000000) ≤ -Real.log (500000000000 / 1073017093977) ∧
    -Real.log (500000000000 / 1073017093977) ≤ (95452697 / 125000000) := by
  have h := checkLog_sound (w := (73017093977 / 2073017093977)) (n := 12)
    (lo := (35237197 / 500000000)) (hi := (14094879 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1073017093977 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1073017093977 / 1000000000000) = 1/(500000000000 / 1073017093977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (381810787 / 500000000) (95452697 / 125000000) (Real.log (1073017093977 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1073017093977 / 500000000000) = -Real.log (500000000000 / 1073017093977) := by
    rw [show ((1073017093977 / 500000000000) : ℝ) = ((500000000000 / 1073017093977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (273694269 / 500000000) ≤ -Real.log (250000000000 / 432183149803) ∧
    -Real.log (250000000000 / 432183149803) ≤ (547388539 / 1000000000) := by
  have h := checkLog_sound (w := (182183149803 / 682183149803)) (n := 12)
    (lo := (273694269 / 500000000)) (hi := (547388539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((432183149803 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(432183149803 / 250000000000) = 1/(250000000000 / 432183149803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (273694269 / 500000000) (547388539 / 1000000000) (Real.log (432183149803 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (432183149803 / 250000000000) = -Real.log (250000000000 / 432183149803) := by
    rw [show ((432183149803 / 250000000000) : ℝ) = ((250000000000 / 432183149803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (274061493 / 500000000) ≤ -Real.log (250000000000 / 432500682501) ∧
    -Real.log (250000000000 / 432500682501) ≤ (548122987 / 1000000000) := by
  have h := checkLog_sound (w := (182500682501 / 682500682501)) (n := 12)
    (lo := (274061493 / 500000000)) (hi := (548122987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((432500682501 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(432500682501 / 250000000000) = 1/(250000000000 / 432500682501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (274061493 / 500000000) (548122987 / 1000000000) (Real.log (432500682501 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (432500682501 / 250000000000) = -Real.log (250000000000 / 432500682501) := by
    rw [show ((432500682501 / 250000000000) : ℝ) = ((250000000000 / 432500682501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0288

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0289Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0289
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

theorem reflection_log_1_neg : (14156081 / 62500000) ≤ -Real.log (10240 / 12843) ∧
    -Real.log (10240 / 12843) ≤ (226497297 / 1000000000) := by
  have h := checkLog_sound (w := (2603 / 23083)) (n := 12)
    (lo := (14156081 / 62500000)) (hi := (226497297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12843 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12843 / 10240) = 1/(10240 / 12843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (14156081 / 62500000) (226497297 / 1000000000) (Real.log (12843 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12843 / 10240) = -Real.log (10240 / 12843) := by
    rw [show ((12843 / 10240) : ℝ) = ((10240 / 12843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (293296763 / 1000000000) ≤ -Real.log (7637 / 10240) ∧
    -Real.log (7637 / 10240) ≤ (73324191 / 250000000) := by
  have h := checkLog_sound (w := (2603 / 17877)) (n := 12)
    (lo := (293296763 / 1000000000)) (hi := (73324191 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7637) = 1/(7637 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-73324191 / 250000000) (-293296763 / 1000000000) (Real.log (7637 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (113131839 / 500000000) ≤ -Real.log (256 / 321) ∧
    -Real.log (256 / 321) ≤ (226263679 / 1000000000) := by
  have h := checkLog_sound (w := (65 / 577)) (n := 12)
    (lo := (113131839 / 500000000)) (hi := (226263679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321 / 256) = 1/(256 / 321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (113131839 / 500000000) (226263679 / 1000000000) (Real.log (321 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (321 / 256) = -Real.log (256 / 321) := by
    rw [show ((321 / 256) : ℝ) = ((256 / 321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (18306501 / 62500000) ≤ -Real.log (191 / 256) ∧
    -Real.log (191 / 256) ≤ (292904017 / 1000000000) := by
  have h := checkLog_sound (w := (65 / 447)) (n := 12)
    (lo := (18306501 / 62500000)) (hi := (292904017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 191) = 1/(191 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-292904017 / 1000000000) (-18306501 / 62500000) (Real.log (191 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (8220969 / 20000000) ≤ -Real.log (5120 / 7723) ∧
    -Real.log (5120 / 7723) ≤ (411048451 / 1000000000) := by
  have h := checkLog_sound (w := (2603 / 12843)) (n := 12)
    (lo := (8220969 / 20000000)) (hi := (411048451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7723 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7723 / 5120) = 1/(5120 / 7723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (8220969 / 20000000) (411048451 / 1000000000) (Real.log (7723 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7723 / 5120) = -Real.log (5120 / 7723) := by
    rw [show ((7723 / 5120) : ℝ) = ((5120 / 7723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (355043361 / 500000000) ≤ -Real.log (2517 / 5120) ∧
    -Real.log (2517 / 5120) ≤ (177521681 / 250000000) := by
  have h := checkLog_sound (w := (43 / 5077)) (n := 12)
    (lo := (8469771 / 500000000)) (hi := (16939543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2517) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2517) = 1/(2517 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-177521681 / 250000000) (-355043361 / 500000000) (Real.log (2517 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (102664981 / 250000000) ≤ -Real.log (128 / 193) ∧
    -Real.log (128 / 193) ≤ (16426397 / 40000000) := by
  have h := checkLog_sound (w := (65 / 321)) (n := 12)
    (lo := (102664981 / 250000000)) (hi := (16426397 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((193 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(193 / 128) = 1/(128 / 193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (102664981 / 250000000) (16426397 / 40000000) (Real.log (193 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (193 / 128) = -Real.log (128 / 193) := by
    rw [show ((193 / 128) : ℝ) = ((128 / 193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (44305971 / 62500000) ≤ -Real.log (63 / 128) ∧
    -Real.log (63 / 128) ≤ (354447769 / 500000000) := by
  have h := checkLog_sound (w := (1 / 127)) (n := 12)
    (lo := (3937089 / 250000000)) (hi := (15748357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 63) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 63) = 1/(63 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-354447769 / 500000000) (-44305971 / 62500000) (Real.log (63 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (61998663 / 200000000) ≤ -Real.log (125000 / 170427) ∧
    -Real.log (125000 / 170427) ≤ (77498329 / 250000000) := by
  have h := checkLog_sound (w := (45427 / 295427)) (n := 12)
    (lo := (61998663 / 200000000)) (hi := (77498329 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170427 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(170427 / 125000) = 1/(125000 / 170427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (61998663 / 200000000) (77498329 / 250000000) (Real.log (170427 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (170427 / 125000) = -Real.log (125000 / 170427) := by
    rw [show ((170427 / 125000) : ℝ) = ((125000 / 170427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (451638897 / 1000000000) ≤ -Real.log (79573 / 125000) ∧
    -Real.log (79573 / 125000) ≤ (225819449 / 500000000) := by
  have h := checkLog_sound (w := (45427 / 204573)) (n := 12)
    (lo := (451638897 / 1000000000)) (hi := (225819449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 79573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 79573) = 1/(79573 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-225819449 / 500000000) (-451638897 / 1000000000) (Real.log (79573 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (77577529 / 250000000) ≤ -Real.log (125000 / 170481) ∧
    -Real.log (125000 / 170481) ≤ (310310117 / 1000000000) := by
  have h := checkLog_sound (w := (45481 / 295481)) (n := 12)
    (lo := (77577529 / 250000000)) (hi := (310310117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170481 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(170481 / 125000) = 1/(125000 / 170481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (77577529 / 250000000) (310310117 / 1000000000) (Real.log (170481 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (170481 / 125000) = -Real.log (125000 / 170481) := by
    rw [show ((170481 / 125000) : ℝ) = ((125000 / 170481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1809271 / 4000000) ≤ -Real.log (79519 / 125000) ∧
    -Real.log (79519 / 125000) ≤ (452317751 / 1000000000) := by
  have h := checkLog_sound (w := (45481 / 204519)) (n := 12)
    (lo := (1809271 / 4000000)) (hi := (452317751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 79519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 79519) = 1/(79519 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-452317751 / 1000000000) (-1809271 / 4000000) (Real.log (79519 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (236430093 / 1000000000) ≤ -Real.log (1000000 / 1266719) ∧
    -Real.log (1000000 / 1266719) ≤ (118215047 / 500000000) := by
  have h := checkLog_sound (w := (266719 / 2266719)) (n := 12)
    (lo := (236430093 / 1000000000)) (hi := (118215047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1266719 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1266719 / 1000000) = 1/(1000000 / 1266719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (236430093 / 1000000000) (118215047 / 500000000) (Real.log (1266719 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1266719 / 1000000) = -Real.log (1000000 / 1266719) := by
    rw [show ((1266719 / 1000000) : ℝ) = ((1000000 / 1266719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (155113147 / 500000000) ≤ -Real.log (733281 / 1000000) ∧
    -Real.log (733281 / 1000000) ≤ (62045259 / 200000000) := by
  have h := checkLog_sound (w := (266719 / 1733281)) (n := 12)
    (lo := (155113147 / 500000000)) (hi := (62045259 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 733281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 733281) = 1/(733281 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-62045259 / 200000000) (-155113147 / 500000000) (Real.log (733281 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (29587407 / 125000000) ≤ -Real.log (50000 / 63353) ∧
    -Real.log (50000 / 63353) ≤ (236699257 / 1000000000) := by
  have h := checkLog_sound (w := (13353 / 113353)) (n := 12)
    (lo := (29587407 / 125000000)) (hi := (236699257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63353 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63353 / 50000) = 1/(50000 / 63353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (29587407 / 125000000) (236699257 / 1000000000) (Real.log (63353 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (63353 / 50000) = -Real.log (50000 / 63353) := by
    rw [show ((63353 / 50000) : ℝ) = ((50000 / 63353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (62138287 / 200000000) ≤ -Real.log (36647 / 50000) ∧
    -Real.log (36647 / 50000) ≤ (77672859 / 250000000) := by
  have h := checkLog_sound (w := (13353 / 86647)) (n := 12)
    (lo := (62138287 / 200000000)) (hi := (77672859 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 36647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 36647) = 1/(36647 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-77672859 / 250000000) (-62138287 / 200000000) (Real.log (36647 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (190408053 / 250000000) ≤ -Real.log (250000000000 / 535442298267) ∧
    -Real.log (250000000000 / 535442298267) ≤ (380816107 / 500000000) := by
  have h := checkLog_sound (w := (35442298267 / 1035442298267)) (n := 12)
    (lo := (8560629 / 125000000)) (hi := (68485033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((535442298267 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(535442298267 / 500000000000) = 1/(250000000000 / 535442298267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (190408053 / 250000000) (380816107 / 500000000) (Real.log (535442298267 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (535442298267 / 250000000000) = -Real.log (250000000000 / 535442298267) := by
    rw [show ((535442298267 / 250000000000) : ℝ) = ((250000000000 / 535442298267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (381313933 / 500000000) ≤ -Real.log (250000000000 / 535975678769) ∧
    -Real.log (250000000000 / 535975678769) ≤ (190656967 / 250000000) := by
  have h := checkLog_sound (w := (35975678769 / 1035975678769)) (n := 12)
    (lo := (34740343 / 500000000)) (hi := (69480687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((535975678769 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(535975678769 / 500000000000) = 1/(250000000000 / 535975678769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (381313933 / 500000000) (190656967 / 250000000) (Real.log (535975678769 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (535975678769 / 250000000000) = -Real.log (250000000000 / 535975678769) := by
    rw [show ((535975678769 / 250000000000) : ℝ) = ((250000000000 / 535975678769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (546656387 / 1000000000) ≤ -Real.log (500000000000 / 863733684631) ∧
    -Real.log (500000000000 / 863733684631) ≤ (136664097 / 250000000) := by
  have h := checkLog_sound (w := (363733684631 / 1363733684631)) (n := 12)
    (lo := (546656387 / 1000000000)) (hi := (136664097 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((863733684631 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(863733684631 / 500000000000) = 1/(500000000000 / 863733684631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (546656387 / 1000000000) (136664097 / 250000000) (Real.log (863733684631 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (863733684631 / 500000000000) = -Real.log (500000000000 / 863733684631) := by
    rw [show ((863733684631 / 500000000000) : ℝ) = ((500000000000 / 863733684631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (136847673 / 250000000) ≤ -Real.log (100000000000 / 172873632221) ∧
    -Real.log (100000000000 / 172873632221) ≤ (547390693 / 1000000000) := by
  have h := checkLog_sound (w := (72873632221 / 272873632221)) (n := 12)
    (lo := (136847673 / 250000000)) (hi := (547390693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172873632221 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172873632221 / 100000000000) = 1/(100000000000 / 172873632221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (136847673 / 250000000) (547390693 / 1000000000) (Real.log (172873632221 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (172873632221 / 100000000000) = -Real.log (100000000000 / 172873632221) := by
    rw [show ((172873632221 / 100000000000) : ℝ) = ((100000000000 / 172873632221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0289

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0290Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0290
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

theorem reflection_log_1_neg : (113131839 / 500000000) ≤ -Real.log (256 / 321) ∧
    -Real.log (256 / 321) ≤ (226263679 / 1000000000) := by
  have h := checkLog_sound (w := (65 / 577)) (n := 12)
    (lo := (113131839 / 500000000)) (hi := (226263679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321 / 256) = 1/(256 / 321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (113131839 / 500000000) (226263679 / 1000000000) (Real.log (321 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (321 / 256) = -Real.log (256 / 321) := by
    rw [show ((321 / 256) : ℝ) = ((256 / 321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (18306501 / 62500000) ≤ -Real.log (191 / 256) ∧
    -Real.log (191 / 256) ≤ (292904017 / 1000000000) := by
  have h := checkLog_sound (w := (65 / 447)) (n := 12)
    (lo := (18306501 / 62500000)) (hi := (292904017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 191) = 1/(191 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-292904017 / 1000000000) (-18306501 / 62500000) (Real.log (191 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (113015003 / 500000000) ≤ -Real.log (10240 / 12837) ∧
    -Real.log (10240 / 12837) ≤ (226030007 / 1000000000) := by
  have h := checkLog_sound (w := (2597 / 23077)) (n := 12)
    (lo := (113015003 / 500000000)) (hi := (226030007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12837 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12837 / 10240) = 1/(10240 / 12837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (113015003 / 500000000) (226030007 / 1000000000) (Real.log (12837 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12837 / 10240) = -Real.log (10240 / 12837) := by
    rw [show ((12837 / 10240) : ℝ) = ((10240 / 12837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (292511423 / 1000000000) ≤ -Real.log (7643 / 10240) ∧
    -Real.log (7643 / 10240) ≤ (4570491 / 15625000) := by
  have h := checkLog_sound (w := (2597 / 17883)) (n := 12)
    (lo := (292511423 / 1000000000)) (hi := (4570491 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7643) = 1/(7643 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-4570491 / 15625000) (-292511423 / 1000000000) (Real.log (7643 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (102664981 / 250000000) ≤ -Real.log (128 / 193) ∧
    -Real.log (128 / 193) ≤ (16426397 / 40000000) := by
  have h := checkLog_sound (w := (65 / 321)) (n := 12)
    (lo := (102664981 / 250000000)) (hi := (16426397 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((193 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(193 / 128) = 1/(128 / 193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (102664981 / 250000000) (16426397 / 40000000) (Real.log (193 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (193 / 128) = -Real.log (128 / 193) := by
    rw [show ((193 / 128) : ℝ) = ((128 / 193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (44305971 / 62500000) ≤ -Real.log (63 / 128) ∧
    -Real.log (63 / 128) ≤ (354447769 / 500000000) := by
  have h := checkLog_sound (w := (1 / 127)) (n := 12)
    (lo := (3937089 / 250000000)) (hi := (15748357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 63) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 63) = 1/(63 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-354447769 / 500000000) (-44305971 / 62500000) (Real.log (63 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (25641953 / 62500000) ≤ -Real.log (5120 / 7717) ∧
    -Real.log (5120 / 7717) ≤ (410271249 / 1000000000) := by
  have h := checkLog_sound (w := (2597 / 12837)) (n := 12)
    (lo := (25641953 / 62500000)) (hi := (410271249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7717 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7717 / 5120) = 1/(5120 / 7717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (25641953 / 62500000) (410271249 / 1000000000) (Real.log (7717 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7717 / 5120) = -Real.log (5120 / 7717) := by
    rw [show ((7717 / 5120) : ℝ) = ((5120 / 7717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (88463221 / 125000000) ≤ -Real.log (2523 / 5120) ∧
    -Real.log (2523 / 5120) ≤ (70770577 / 100000000) := by
  have h := checkLog_sound (w := (37 / 5083)) (n := 12)
    (lo := (3639647 / 250000000)) (hi := (14558589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2523) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2523) = 1/(2523 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-70770577 / 100000000) (-88463221 / 125000000) (Real.log (2523 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (309677881 / 1000000000) ≤ -Real.log (500000 / 681493) ∧
    -Real.log (500000 / 681493) ≤ (154838941 / 500000000) := by
  have h := checkLog_sound (w := (181493 / 1181493)) (n := 12)
    (lo := (309677881 / 1000000000)) (hi := (154838941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681493 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(681493 / 500000) = 1/(500000 / 681493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (309677881 / 1000000000) (154838941 / 500000000) (Real.log (681493 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (681493 / 500000) = -Real.log (500000 / 681493) := by
    rw [show ((681493 / 500000) : ℝ) = ((500000 / 681493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (90192729 / 200000000) ≤ -Real.log (318507 / 500000) ∧
    -Real.log (318507 / 500000) ≤ (225481823 / 500000000) := by
  have h := checkLog_sound (w := (181493 / 818507)) (n := 12)
    (lo := (90192729 / 200000000)) (hi := (225481823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 318507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 318507) = 1/(318507 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-225481823 / 500000000) (-90192729 / 200000000) (Real.log (318507 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (4843657 / 15625000) ≤ -Real.log (1000000 / 1363417) ∧
    -Real.log (1000000 / 1363417) ≤ (309994049 / 1000000000) := by
  have h := checkLog_sound (w := (363417 / 2363417)) (n := 12)
    (lo := (4843657 / 15625000)) (hi := (309994049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1363417 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1363417 / 1000000) = 1/(1000000 / 1363417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (4843657 / 15625000) (309994049 / 1000000000) (Real.log (1363417 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1363417 / 1000000) = -Real.log (1000000 / 1363417) := by
    rw [show ((1363417 / 1000000) : ℝ) = ((1000000 / 1363417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (112910117 / 250000000) ≤ -Real.log (636583 / 1000000) ∧
    -Real.log (636583 / 1000000) ≤ (451640469 / 1000000000) := by
  have h := checkLog_sound (w := (363417 / 1636583)) (n := 12)
    (lo := (112910117 / 250000000)) (hi := (451640469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 636583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 636583) = 1/(636583 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-451640469 / 1000000000) (-112910117 / 250000000) (Real.log (636583 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (236161647 / 1000000000) ≤ -Real.log (1000000 / 1266379) ∧
    -Real.log (1000000 / 1266379) ≤ (14760103 / 62500000) := by
  have h := checkLog_sound (w := (266379 / 2266379)) (n := 12)
    (lo := (236161647 / 1000000000)) (hi := (14760103 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1266379 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1266379 / 1000000) = 1/(1000000 / 1266379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (236161647 / 1000000000) (14760103 / 62500000) (Real.log (1266379 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1266379 / 1000000) = -Real.log (1000000 / 1266379) := by
    rw [show ((1266379 / 1000000) : ℝ) = ((1000000 / 1266379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (77440683 / 250000000) ≤ -Real.log (733621 / 1000000) ∧
    -Real.log (733621 / 1000000) ≤ (309762733 / 1000000000) := by
  have h := checkLog_sound (w := (266379 / 1733621)) (n := 12)
    (lo := (77440683 / 250000000)) (hi := (309762733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 733621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 733621) = 1/(733621 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-309762733 / 1000000000) (-77440683 / 250000000) (Real.log (733621 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (118215441 / 500000000) ≤ -Real.log (6250 / 7917) ∧
    -Real.log (6250 / 7917) ≤ (236430883 / 1000000000) := by
  have h := checkLog_sound (w := (1667 / 14167)) (n := 12)
    (lo := (118215441 / 500000000)) (hi := (236430883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7917 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7917 / 6250) = 1/(6250 / 7917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (118215441 / 500000000) (236430883 / 1000000000) (Real.log (7917 / 6250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (7917 / 6250) = -Real.log (6250 / 7917) := by
    rw [show ((7917 / 6250) : ℝ) = ((6250 / 7917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (155113829 / 500000000) ≤ -Real.log (4583 / 6250) ∧
    -Real.log (4583 / 6250) ≤ (310227659 / 1000000000) := by
  have h := checkLog_sound (w := (1667 / 10833)) (n := 12)
    (lo := (155113829 / 500000000)) (hi := (310227659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 4583) = 1/(4583 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-310227659 / 1000000000) (-155113829 / 500000000) (Real.log (4583 / 6250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (380320763 / 500000000) ≤ -Real.log (125000000000 / 267456052771) ∧
    -Real.log (125000000000 / 267456052771) ≤ (95080191 / 125000000) := by
  have h := checkLog_sound (w := (17456052771 / 517456052771)) (n := 12)
    (lo := (33747173 / 500000000)) (hi := (67494347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((267456052771 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(267456052771 / 250000000000) = 1/(125000000000 / 267456052771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (380320763 / 500000000) (95080191 / 125000000) (Real.log (267456052771 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (267456052771 / 125000000000) = -Real.log (125000000000 / 267456052771) := by
    rw [show ((267456052771 / 125000000000) : ℝ) = ((125000000000 / 267456052771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (190408629 / 250000000) ≤ -Real.log (500000000000 / 1070887064217) ∧
    -Real.log (500000000000 / 1070887064217) ≤ (380817259 / 500000000) := by
  have h := checkLog_sound (w := (70887064217 / 2070887064217)) (n := 12)
    (lo := (8560917 / 125000000)) (hi := (68487337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1070887064217 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1070887064217 / 1000000000000) = 1/(500000000000 / 1070887064217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (190408629 / 250000000) (380817259 / 500000000) (Real.log (1070887064217 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1070887064217 / 500000000000) = -Real.log (500000000000 / 1070887064217) := by
    rw [show ((1070887064217 / 500000000000) : ℝ) = ((500000000000 / 1070887064217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (545924379 / 1000000000) ≤ -Real.log (15625000000 / 26971926751) ∧
    -Real.log (15625000000 / 26971926751) ≤ (27296219 / 50000000) := by
  have h := checkLog_sound (w := (11346926751 / 42596926751)) (n := 12)
    (lo := (545924379 / 1000000000)) (hi := (27296219 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26971926751 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26971926751 / 15625000000) = 1/(15625000000 / 26971926751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (545924379 / 1000000000) (27296219 / 50000000) (Real.log (26971926751 / 15625000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (26971926751 / 15625000000) = -Real.log (15625000000 / 26971926751) := by
    rw [show ((26971926751 / 15625000000) : ℝ) = ((15625000000 / 26971926751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (27332927 / 50000000) ≤ -Real.log (125000000000 / 215933886101) ∧
    -Real.log (125000000000 / 215933886101) ≤ (546658541 / 1000000000) := by
  have h := checkLog_sound (w := (90933886101 / 340933886101)) (n := 12)
    (lo := (27332927 / 50000000)) (hi := (546658541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215933886101 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215933886101 / 125000000000) = 1/(125000000000 / 215933886101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (27332927 / 50000000) (546658541 / 1000000000) (Real.log (215933886101 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (215933886101 / 125000000000) = -Real.log (125000000000 / 215933886101) := by
    rw [show ((215933886101 / 125000000000) : ℝ) = ((125000000000 / 215933886101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0290

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0291Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0291
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

theorem reflection_log_1_neg : (113015003 / 500000000) ≤ -Real.log (10240 / 12837) ∧
    -Real.log (10240 / 12837) ≤ (226030007 / 1000000000) := by
  have h := checkLog_sound (w := (2597 / 23077)) (n := 12)
    (lo := (113015003 / 500000000)) (hi := (226030007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12837 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12837 / 10240) = 1/(10240 / 12837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (113015003 / 500000000) (226030007 / 1000000000) (Real.log (12837 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12837 / 10240) = -Real.log (10240 / 12837) := by
    rw [show ((12837 / 10240) : ℝ) = ((10240 / 12837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (292511423 / 1000000000) ≤ -Real.log (7643 / 10240) ∧
    -Real.log (7643 / 10240) ≤ (4570491 / 15625000) := by
  have h := checkLog_sound (w := (2597 / 17883)) (n := 12)
    (lo := (292511423 / 1000000000)) (hi := (4570491 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7643) = 1/(7643 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-4570491 / 15625000) (-292511423 / 1000000000) (Real.log (7643 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (225796279 / 1000000000) ≤ -Real.log (5120 / 6417) ∧
    -Real.log (5120 / 6417) ≤ (5644907 / 25000000) := by
  have h := checkLog_sound (w := (1297 / 11537)) (n := 12)
    (lo := (225796279 / 1000000000)) (hi := (5644907 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6417 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6417 / 5120) = 1/(5120 / 6417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (225796279 / 1000000000) (5644907 / 25000000) (Real.log (6417 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6417 / 5120) = -Real.log (5120 / 6417) := by
    rw [show ((6417 / 5120) : ℝ) = ((5120 / 6417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (36514873 / 125000000) ≤ -Real.log (3823 / 5120) ∧
    -Real.log (3823 / 5120) ≤ (58423797 / 200000000) := by
  have h := checkLog_sound (w := (1297 / 8943)) (n := 12)
    (lo := (36514873 / 125000000)) (hi := (58423797 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3823) = 1/(3823 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-58423797 / 200000000) (-36514873 / 125000000) (Real.log (3823 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (25641953 / 62500000) ≤ -Real.log (5120 / 7717) ∧
    -Real.log (5120 / 7717) ≤ (410271249 / 1000000000) := by
  have h := checkLog_sound (w := (2597 / 12837)) (n := 12)
    (lo := (25641953 / 62500000)) (hi := (410271249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7717 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7717 / 5120) = 1/(5120 / 7717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (25641953 / 62500000) (410271249 / 1000000000) (Real.log (7717 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7717 / 5120) = -Real.log (5120 / 7717) := by
    rw [show ((7717 / 5120) : ℝ) = ((5120 / 7717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (88463221 / 125000000) ≤ -Real.log (2523 / 5120) ∧
    -Real.log (2523 / 5120) ≤ (70770577 / 100000000) := by
  have h := checkLog_sound (w := (37 / 5083)) (n := 12)
    (lo := (3639647 / 250000000)) (hi := (14558589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2523) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2523) = 1/(2523 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-70770577 / 100000000) (-88463221 / 125000000) (Real.log (2523 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (20494121 / 50000000) ≤ -Real.log (2560 / 3857) ∧
    -Real.log (2560 / 3857) ≤ (409882421 / 1000000000) := by
  have h := checkLog_sound (w := (1297 / 6417)) (n := 12)
    (lo := (20494121 / 50000000)) (hi := (409882421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3857 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3857 / 2560) = 1/(2560 / 3857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (20494121 / 50000000) (409882421 / 1000000000) (Real.log (3857 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3857 / 2560) = -Real.log (2560 / 3857) := by
    rw [show ((3857 / 2560) : ℝ) = ((2560 / 3857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (353258707 / 500000000) ≤ -Real.log (1263 / 2560) ∧
    -Real.log (1263 / 2560) ≤ (88314677 / 125000000) := by
  have h := checkLog_sound (w := (17 / 2543)) (n := 12)
    (lo := (6685117 / 500000000)) (hi := (2674047 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1263) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1263) = 1/(1263 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-88314677 / 125000000) (-353258707 / 500000000) (Real.log (1263 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (309361613 / 1000000000) ≤ -Real.log (200000 / 272511) ∧
    -Real.log (200000 / 272511) ≤ (154680807 / 500000000) := by
  have h := checkLog_sound (w := (72511 / 472511)) (n := 12)
    (lo := (309361613 / 1000000000)) (hi := (154680807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272511 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272511 / 200000) = 1/(200000 / 272511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (309361613 / 1000000000) (154680807 / 500000000) (Real.log (272511 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (272511 / 200000) = -Real.log (200000 / 272511) := by
    rw [show ((272511 / 200000) : ℝ) = ((200000 / 272511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (5628591 / 12500000) ≤ -Real.log (127489 / 200000) ∧
    -Real.log (127489 / 200000) ≤ (450287281 / 1000000000) := by
  have h := checkLog_sound (w := (72511 / 327489)) (n := 12)
    (lo := (5628591 / 12500000)) (hi := (450287281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 127489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 127489) = 1/(127489 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-450287281 / 1000000000) (-5628591 / 12500000) (Real.log (127489 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (154839307 / 500000000) ≤ -Real.log (1000000 / 1362987) ∧
    -Real.log (1000000 / 1362987) ≤ (61935723 / 200000000) := by
  have h := checkLog_sound (w := (362987 / 2362987)) (n := 12)
    (lo := (154839307 / 500000000)) (hi := (61935723 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1362987 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1362987 / 1000000) = 1/(1000000 / 1362987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (154839307 / 500000000) (61935723 / 200000000) (Real.log (1362987 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1362987 / 1000000) = -Real.log (1000000 / 1362987) := by
    rw [show ((1362987 / 1000000) : ℝ) = ((1000000 / 1362987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (90193043 / 200000000) ≤ -Real.log (637013 / 1000000) ∧
    -Real.log (637013 / 1000000) ≤ (14092663 / 31250000) := by
  have h := checkLog_sound (w := (362987 / 1637013)) (n := 12)
    (lo := (90193043 / 200000000)) (hi := (14092663 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 637013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 637013) = 1/(637013 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-14092663 / 31250000) (-90193043 / 200000000) (Real.log (637013 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (29486641 / 125000000) ≤ -Real.log (1000000 / 1266039) ∧
    -Real.log (1000000 / 1266039) ≤ (235893129 / 1000000000) := by
  have h := checkLog_sound (w := (266039 / 2266039)) (n := 12)
    (lo := (29486641 / 125000000)) (hi := (235893129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1266039 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1266039 / 1000000) = 1/(1000000 / 1266039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (29486641 / 125000000) (235893129 / 1000000000) (Real.log (1266039 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1266039 / 1000000) = -Real.log (1000000 / 1266039) := by
    rw [show ((1266039 / 1000000) : ℝ) = ((1000000 / 1266039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (61859877 / 200000000) ≤ -Real.log (733961 / 1000000) ∧
    -Real.log (733961 / 1000000) ≤ (154649693 / 500000000) := by
  have h := checkLog_sound (w := (266039 / 1733961)) (n := 12)
    (lo := (61859877 / 200000000)) (hi := (154649693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 733961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 733961) = 1/(733961 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-154649693 / 500000000) (-61859877 / 200000000) (Real.log (733961 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (59040609 / 250000000) ≤ -Real.log (50000 / 63319) ∧
    -Real.log (50000 / 63319) ≤ (236162437 / 1000000000) := by
  have h := checkLog_sound (w := (13319 / 113319)) (n := 12)
    (lo := (59040609 / 250000000)) (hi := (236162437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63319 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63319 / 50000) = 1/(50000 / 63319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (59040609 / 250000000) (236162437 / 1000000000) (Real.log (63319 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (63319 / 50000) = -Real.log (50000 / 63319) := by
    rw [show ((63319 / 50000) : ℝ) = ((50000 / 63319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (61952819 / 200000000) ≤ -Real.log (36681 / 50000) ∧
    -Real.log (36681 / 50000) ≤ (605008 / 1953125) := by
  have h := checkLog_sound (w := (13319 / 86681)) (n := 12)
    (lo := (61952819 / 200000000)) (hi := (605008 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 36681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 36681) = 1/(36681 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-605008 / 1953125) (-61952819 / 200000000) (Real.log (36681 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (759648893 / 1000000000) ≤ -Real.log (500000000000 / 1068762795221) ∧
    -Real.log (500000000000 / 1068762795221) ≤ (151929779 / 200000000) := by
  have h := checkLog_sound (w := (68762795221 / 2068762795221)) (n := 12)
    (lo := (66501713 / 1000000000)) (hi := (33250857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1068762795221 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1068762795221 / 1000000000000) = 1/(500000000000 / 1068762795221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (759648893 / 1000000000) (151929779 / 200000000) (Real.log (1068762795221 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1068762795221 / 500000000000) = -Real.log (500000000000 / 1068762795221) := by
    rw [show ((1068762795221 / 500000000000) : ℝ) = ((500000000000 / 1068762795221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (760643829 / 1000000000) ≤ -Real.log (500000000000 / 1069826675437) ∧
    -Real.log (500000000000 / 1069826675437) ≤ (760643831 / 1000000000) := by
  have h := checkLog_sound (w := (69826675437 / 2069826675437)) (n := 12)
    (lo := (67496649 / 1000000000)) (hi := (1349933 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1069826675437 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1069826675437 / 1000000000000) = 1/(500000000000 / 1069826675437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (760643829 / 1000000000) (760643831 / 1000000000) (Real.log (1069826675437 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1069826675437 / 500000000000) = -Real.log (500000000000 / 1069826675437) := by
    rw [show ((1069826675437 / 500000000000) : ℝ) = ((500000000000 / 1069826675437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (272596257 / 500000000) ≤ -Real.log (250000000000 / 431235106497) ∧
    -Real.log (250000000000 / 431235106497) ≤ (109038503 / 200000000) := by
  have h := checkLog_sound (w := (181235106497 / 681235106497)) (n := 12)
    (lo := (272596257 / 500000000)) (hi := (109038503 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((431235106497 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(431235106497 / 250000000000) = 1/(250000000000 / 431235106497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (272596257 / 500000000) (109038503 / 200000000) (Real.log (431235106497 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (431235106497 / 250000000000) = -Real.log (250000000000 / 431235106497) := by
    rw [show ((431235106497 / 250000000000) : ℝ) = ((250000000000 / 431235106497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (136481633 / 250000000) ≤ -Real.log (500000000000 / 863103514081) ∧
    -Real.log (500000000000 / 863103514081) ≤ (545926533 / 1000000000) := by
  have h := checkLog_sound (w := (363103514081 / 1363103514081)) (n := 12)
    (lo := (136481633 / 250000000)) (hi := (545926533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((863103514081 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(863103514081 / 500000000000) = 1/(500000000000 / 863103514081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (136481633 / 250000000) (545926533 / 1000000000) (Real.log (863103514081 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (863103514081 / 500000000000) = -Real.log (500000000000 / 863103514081) := by
    rw [show ((863103514081 / 500000000000) : ℝ) = ((500000000000 / 863103514081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0291

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0292Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0292
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

theorem reflection_log_1_neg : (225796279 / 1000000000) ≤ -Real.log (5120 / 6417) ∧
    -Real.log (5120 / 6417) ≤ (5644907 / 25000000) := by
  have h := checkLog_sound (w := (1297 / 11537)) (n := 12)
    (lo := (225796279 / 1000000000)) (hi := (5644907 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6417 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6417 / 5120) = 1/(5120 / 6417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (225796279 / 1000000000) (5644907 / 25000000) (Real.log (6417 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6417 / 5120) = -Real.log (5120 / 6417) := by
    rw [show ((6417 / 5120) : ℝ) = ((5120 / 6417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (36514873 / 125000000) ≤ -Real.log (3823 / 5120) ∧
    -Real.log (3823 / 5120) ≤ (58423797 / 200000000) := by
  have h := checkLog_sound (w := (1297 / 8943)) (n := 12)
    (lo := (36514873 / 125000000)) (hi := (58423797 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3823) = 1/(3823 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-58423797 / 200000000) (-36514873 / 125000000) (Real.log (3823 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (112781249 / 500000000) ≤ -Real.log (10240 / 12831) ∧
    -Real.log (10240 / 12831) ≤ (225562499 / 1000000000) := by
  have h := checkLog_sound (w := (2591 / 23071)) (n := 12)
    (lo := (112781249 / 500000000)) (hi := (225562499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12831 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12831 / 10240) = 1/(10240 / 12831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (112781249 / 500000000) (225562499 / 1000000000) (Real.log (12831 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12831 / 10240) = -Real.log (10240 / 12831) := by
    rw [show ((12831 / 10240) : ℝ) = ((10240 / 12831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (291726699 / 1000000000) ≤ -Real.log (7649 / 10240) ∧
    -Real.log (7649 / 10240) ≤ (2917267 / 10000000) := by
  have h := checkLog_sound (w := (2591 / 17889)) (n := 12)
    (lo := (291726699 / 1000000000)) (hi := (2917267 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7649) = 1/(7649 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2917267 / 10000000) (-291726699 / 1000000000) (Real.log (7649 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (20494121 / 50000000) ≤ -Real.log (2560 / 3857) ∧
    -Real.log (2560 / 3857) ≤ (409882421 / 1000000000) := by
  have h := checkLog_sound (w := (1297 / 6417)) (n := 12)
    (lo := (20494121 / 50000000)) (hi := (409882421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3857 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3857 / 2560) = 1/(2560 / 3857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (20494121 / 50000000) (409882421 / 1000000000) (Real.log (3857 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3857 / 2560) = -Real.log (2560 / 3857) := by
    rw [show ((3857 / 2560) : ℝ) = ((2560 / 3857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (353258707 / 500000000) ≤ -Real.log (1263 / 2560) ∧
    -Real.log (1263 / 2560) ≤ (88314677 / 125000000) := by
  have h := checkLog_sound (w := (17 / 2543)) (n := 12)
    (lo := (6685117 / 500000000)) (hi := (2674047 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1263) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1263) = 1/(1263 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-88314677 / 125000000) (-353258707 / 500000000) (Real.log (1263 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (409493441 / 1000000000) ≤ -Real.log (5120 / 7711) ∧
    -Real.log (5120 / 7711) ≤ (204746721 / 500000000) := by
  have h := checkLog_sound (w := (2591 / 12831)) (n := 12)
    (lo := (409493441 / 1000000000)) (hi := (204746721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7711 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7711 / 5120) = 1/(5120 / 7711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (409493441 / 1000000000) (204746721 / 500000000) (Real.log (7711 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7711 / 5120) = -Real.log (5120 / 7711) := by
    rw [show ((7711 / 5120) : ℝ) = ((5120 / 7711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (70533047 / 100000000) ≤ -Real.log (2529 / 5120) ∧
    -Real.log (2529 / 5120) ≤ (88166309 / 125000000) := by
  have h := checkLog_sound (w := (31 / 5089)) (n := 12)
    (lo := (1218329 / 100000000)) (hi := (12183291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2529) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2529) = 1/(2529 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-88166309 / 125000000) (-70533047 / 100000000) (Real.log (2529 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (15452299 / 50000000) ≤ -Real.log (8000 / 10897) ∧
    -Real.log (8000 / 10897) ≤ (309045981 / 1000000000) := by
  have h := checkLog_sound (w := (2897 / 18897)) (n := 12)
    (lo := (15452299 / 50000000)) (hi := (309045981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10897 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10897 / 8000) = 1/(8000 / 10897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (15452299 / 50000000) (309045981 / 1000000000) (Real.log (10897 / 8000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (10897 / 8000) = -Real.log (8000 / 10897) := by
    rw [show ((10897 / 8000) : ℝ) = ((8000 / 10897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (449612939 / 1000000000) ≤ -Real.log (5103 / 8000) ∧
    -Real.log (5103 / 8000) ≤ (22480647 / 50000000) := by
  have h := checkLog_sound (w := (2897 / 13103)) (n := 12)
    (lo := (449612939 / 1000000000)) (hi := (22480647 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 5103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 5103) = 1/(5103 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-22480647 / 50000000) (-449612939 / 1000000000) (Real.log (5103 / 8000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (309362347 / 1000000000) ≤ -Real.log (250000 / 340639) ∧
    -Real.log (250000 / 340639) ≤ (77340587 / 250000000) := by
  have h := checkLog_sound (w := (90639 / 590639)) (n := 12)
    (lo := (309362347 / 1000000000)) (hi := (77340587 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340639 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340639 / 250000) = 1/(250000 / 340639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (309362347 / 1000000000) (77340587 / 250000000) (Real.log (340639 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (340639 / 250000) = -Real.log (250000 / 340639) := by
    rw [show ((340639 / 250000) : ℝ) = ((250000 / 340639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (28143053 / 62500000) ≤ -Real.log (159361 / 250000) ∧
    -Real.log (159361 / 250000) ≤ (450288849 / 1000000000) := by
  have h := checkLog_sound (w := (90639 / 409361)) (n := 12)
    (lo := (28143053 / 62500000)) (hi := (450288849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 159361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 159361) = 1/(159361 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-450288849 / 1000000000) (-28143053 / 62500000) (Real.log (159361 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (117812269 / 500000000) ≤ -Real.log (1000000 / 1265699) ∧
    -Real.log (1000000 / 1265699) ≤ (235624539 / 1000000000) := by
  have h := checkLog_sound (w := (265699 / 2265699)) (n := 12)
    (lo := (117812269 / 500000000)) (hi := (235624539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1265699 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1265699 / 1000000) = 1/(1000000 / 1265699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (117812269 / 500000000) (235624539 / 1000000000) (Real.log (1265699 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1265699 / 1000000) = -Real.log (1000000 / 1265699) := by
    rw [show ((1265699 / 1000000) : ℝ) = ((1000000 / 1265699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (77209063 / 250000000) ≤ -Real.log (734301 / 1000000) ∧
    -Real.log (734301 / 1000000) ≤ (308836253 / 1000000000) := by
  have h := checkLog_sound (w := (265699 / 1734301)) (n := 12)
    (lo := (77209063 / 250000000)) (hi := (308836253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 734301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 734301) = 1/(734301 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-308836253 / 1000000000) (-77209063 / 250000000) (Real.log (734301 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (117946959 / 500000000) ≤ -Real.log (25000 / 31651) ∧
    -Real.log (25000 / 31651) ≤ (235893919 / 1000000000) := by
  have h := checkLog_sound (w := (6651 / 56651)) (n := 12)
    (lo := (117946959 / 500000000)) (hi := (235893919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31651 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31651 / 25000) = 1/(25000 / 31651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (117946959 / 500000000) (235893919 / 1000000000) (Real.log (31651 / 25000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (31651 / 25000) = -Real.log (25000 / 31651) := by
    rw [show ((31651 / 25000) : ℝ) = ((25000 / 31651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (309300747 / 1000000000) ≤ -Real.log (18349 / 25000) ∧
    -Real.log (18349 / 25000) ≤ (77325187 / 250000000) := by
  have h := checkLog_sound (w := (6651 / 43349)) (n := 12)
    (lo := (309300747 / 1000000000)) (hi := (77325187 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 18349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 18349) = 1/(18349 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-77325187 / 250000000) (-309300747 / 1000000000) (Real.log (18349 / 25000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (758658919 / 1000000000) ≤ -Real.log (31250000000 / 66731579463) ∧
    -Real.log (31250000000 / 66731579463) ≤ (758658921 / 1000000000) := by
  have h := checkLog_sound (w := (4231579463 / 129231579463)) (n := 12)
    (lo := (65511739 / 1000000000)) (hi := (3275587 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66731579463 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(66731579463 / 62500000000) = 1/(31250000000 / 66731579463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (758658919 / 1000000000) (758658921 / 1000000000) (Real.log (66731579463 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (66731579463 / 31250000000) = -Real.log (31250000000 / 66731579463) := by
    rw [show ((66731579463 / 31250000000) : ℝ) = ((31250000000 / 66731579463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (189912799 / 250000000) ≤ -Real.log (500000000000 / 1068765256243) ∧
    -Real.log (500000000000 / 1068765256243) ≤ (379825599 / 500000000) := by
  have h := checkLog_sound (w := (68765256243 / 2068765256243)) (n := 12)
    (lo := (4156501 / 62500000)) (hi := (66504017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1068765256243 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1068765256243 / 1000000000000) = 1/(500000000000 / 1068765256243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (189912799 / 250000000) (379825599 / 500000000) (Real.log (1068765256243 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1068765256243 / 500000000000) = -Real.log (500000000000 / 1068765256243) := by
    rw [show ((1068765256243 / 500000000000) : ℝ) = ((500000000000 / 1068765256243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (544460791 / 1000000000) ≤ -Real.log (250000000000 / 430919677353) ∧
    -Real.log (250000000000 / 430919677353) ≤ (68057599 / 125000000) := by
  have h := checkLog_sound (w := (180919677353 / 680919677353)) (n := 12)
    (lo := (544460791 / 1000000000)) (hi := (68057599 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((430919677353 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(430919677353 / 250000000000) = 1/(250000000000 / 430919677353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (544460791 / 1000000000) (68057599 / 125000000) (Real.log (430919677353 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (430919677353 / 250000000000) = -Real.log (250000000000 / 430919677353) := by
    rw [show ((430919677353 / 250000000000) : ℝ) = ((250000000000 / 430919677353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (272597333 / 500000000) ≤ -Real.log (500000000000 / 862472069323) ∧
    -Real.log (500000000000 / 862472069323) ≤ (545194667 / 1000000000) := by
  have h := checkLog_sound (w := (362472069323 / 1362472069323)) (n := 12)
    (lo := (272597333 / 500000000)) (hi := (545194667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((862472069323 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(862472069323 / 500000000000) = 1/(500000000000 / 862472069323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (272597333 / 500000000) (545194667 / 1000000000) (Real.log (862472069323 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (862472069323 / 500000000000) = -Real.log (500000000000 / 862472069323) := by
    rw [show ((862472069323 / 500000000000) : ℝ) = ((500000000000 / 862472069323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0292

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0293Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0293
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

theorem reflection_log_1_neg : (112781249 / 500000000) ≤ -Real.log (10240 / 12831) ∧
    -Real.log (10240 / 12831) ≤ (225562499 / 1000000000) := by
  have h := checkLog_sound (w := (2591 / 23071)) (n := 12)
    (lo := (112781249 / 500000000)) (hi := (225562499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12831 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12831 / 10240) = 1/(10240 / 12831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (112781249 / 500000000) (225562499 / 1000000000) (Real.log (12831 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12831 / 10240) = -Real.log (10240 / 12831) := by
    rw [show ((12831 / 10240) : ℝ) = ((10240 / 12831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (291726699 / 1000000000) ≤ -Real.log (7649 / 10240) ∧
    -Real.log (7649 / 10240) ≤ (2917267 / 10000000) := by
  have h := checkLog_sound (w := (2591 / 17889)) (n := 12)
    (lo := (291726699 / 1000000000)) (hi := (2917267 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7649) = 1/(7649 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2917267 / 10000000) (-291726699 / 1000000000) (Real.log (7649 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (112664331 / 500000000) ≤ -Real.log (2560 / 3207) ∧
    -Real.log (2560 / 3207) ≤ (225328663 / 1000000000) := by
  have h := checkLog_sound (w := (647 / 5767)) (n := 12)
    (lo := (112664331 / 500000000)) (hi := (225328663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3207 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3207 / 2560) = 1/(2560 / 3207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (112664331 / 500000000) (225328663 / 1000000000) (Real.log (3207 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3207 / 2560) = -Real.log (2560 / 3207) := by
    rw [show ((3207 / 2560) : ℝ) = ((2560 / 3207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (36416821 / 125000000) ≤ -Real.log (1913 / 2560) ∧
    -Real.log (1913 / 2560) ≤ (291334569 / 1000000000) := by
  have h := checkLog_sound (w := (647 / 4473)) (n := 12)
    (lo := (36416821 / 125000000)) (hi := (291334569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1913) = 1/(1913 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-291334569 / 1000000000) (-36416821 / 125000000) (Real.log (1913 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (409493441 / 1000000000) ≤ -Real.log (5120 / 7711) ∧
    -Real.log (5120 / 7711) ≤ (204746721 / 500000000) := by
  have h := checkLog_sound (w := (2591 / 12831)) (n := 12)
    (lo := (409493441 / 1000000000)) (hi := (204746721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7711 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7711 / 5120) = 1/(5120 / 7711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (409493441 / 1000000000) (204746721 / 500000000) (Real.log (7711 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7711 / 5120) = -Real.log (5120 / 7711) := by
    rw [show ((7711 / 5120) : ℝ) = ((5120 / 7711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (70533047 / 100000000) ≤ -Real.log (2529 / 5120) ∧
    -Real.log (2529 / 5120) ≤ (88166309 / 125000000) := by
  have h := checkLog_sound (w := (31 / 5089)) (n := 12)
    (lo := (1218329 / 100000000)) (hi := (12183291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2529) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2529) = 1/(2529 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-88166309 / 125000000) (-70533047 / 100000000) (Real.log (2529 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (409104311 / 1000000000) ≤ -Real.log (1280 / 1927) ∧
    -Real.log (1280 / 1927) ≤ (51138039 / 125000000) := by
  have h := checkLog_sound (w := (647 / 3207)) (n := 12)
    (lo := (409104311 / 1000000000)) (hi := (51138039 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1927 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1927 / 1280) = 1/(1280 / 1927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (409104311 / 1000000000) (51138039 / 125000000) (Real.log (1927 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1927 / 1280) = -Real.log (1280 / 1927) := by
    rw [show ((1927 / 1280) : ℝ) = ((1280 / 1927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (352072467 / 500000000) ≤ -Real.log (633 / 1280) ∧
    -Real.log (633 / 1280) ≤ (88018117 / 125000000) := by
  have h := checkLog_sound (w := (7 / 1273)) (n := 12)
    (lo := (5498877 / 500000000)) (hi := (2199551 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 633) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 633) = 1/(633 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-88018117 / 125000000) (-352072467 / 500000000) (Real.log (633 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (38591189 / 125000000) ≤ -Real.log (500000 / 680847) ∧
    -Real.log (500000 / 680847) ≤ (308729513 / 1000000000) := by
  have h := checkLog_sound (w := (180847 / 1180847)) (n := 12)
    (lo := (38591189 / 125000000)) (hi := (308729513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680847 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680847 / 500000) = 1/(500000 / 680847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (38591189 / 125000000) (308729513 / 1000000000) (Real.log (680847 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (680847 / 500000) = -Real.log (500000 / 680847) := by
    rw [show ((680847 / 500000) : ℝ) = ((500000 / 680847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (224468743 / 500000000) ≤ -Real.log (319153 / 500000) ∧
    -Real.log (319153 / 500000) ≤ (448937487 / 1000000000) := by
  have h := checkLog_sound (w := (180847 / 819153)) (n := 12)
    (lo := (224468743 / 500000000)) (hi := (448937487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 319153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 319153) = 1/(319153 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-448937487 / 1000000000) (-224468743 / 500000000) (Real.log (319153 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (154523357 / 500000000) ≤ -Real.log (500000 / 681063) ∧
    -Real.log (500000 / 681063) ≤ (61809343 / 200000000) := by
  have h := checkLog_sound (w := (181063 / 1181063)) (n := 12)
    (lo := (154523357 / 500000000)) (hi := (61809343 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681063 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(681063 / 500000) = 1/(500000 / 681063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (154523357 / 500000000) (61809343 / 200000000) (Real.log (681063 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (681063 / 500000) = -Real.log (500000 / 681063) := by
    rw [show ((681063 / 500000) : ℝ) = ((500000 / 681063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (449614507 / 1000000000) ≤ -Real.log (318937 / 500000) ∧
    -Real.log (318937 / 500000) ≤ (112403627 / 250000000) := by
  have h := checkLog_sound (w := (181063 / 818937)) (n := 12)
    (lo := (449614507 / 1000000000)) (hi := (112403627 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 318937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 318937) = 1/(318937 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-112403627 / 250000000) (-449614507 / 1000000000) (Real.log (318937 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (117678333 / 500000000) ≤ -Real.log (12500 / 15817) ∧
    -Real.log (12500 / 15817) ≤ (235356667 / 1000000000) := by
  have h := checkLog_sound (w := (3317 / 28317)) (n := 12)
    (lo := (117678333 / 500000000)) (hi := (235356667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15817 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15817 / 12500) = 1/(12500 / 15817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (117678333 / 500000000) (235356667 / 1000000000) (Real.log (15817 / 12500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (15817 / 12500) = -Real.log (12500 / 15817) := by
    rw [show ((15817 / 12500) : ℝ) = ((12500 / 15817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (61674939 / 200000000) ≤ -Real.log (9183 / 12500) ∧
    -Real.log (9183 / 12500) ≤ (38546837 / 125000000) := by
  have h := checkLog_sound (w := (3317 / 21683)) (n := 12)
    (lo := (61674939 / 200000000)) (hi := (38546837 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 9183) = 1/(9183 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-38546837 / 125000000) (-61674939 / 200000000) (Real.log (9183 / 12500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (14726583 / 62500000) ≤ -Real.log (10000 / 12657) ∧
    -Real.log (10000 / 12657) ≤ (235625329 / 1000000000) := by
  have h := checkLog_sound (w := (2657 / 22657)) (n := 12)
    (lo := (14726583 / 62500000)) (hi := (235625329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12657 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12657 / 10000) = 1/(10000 / 12657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (14726583 / 62500000) (235625329 / 1000000000) (Real.log (12657 / 10000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (12657 / 10000) = -Real.log (10000 / 12657) := by
    rw [show ((12657 / 10000) : ℝ) = ((10000 / 12657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (154418807 / 500000000) ≤ -Real.log (7343 / 10000) ∧
    -Real.log (7343 / 10000) ≤ (61767523 / 200000000) := by
  have h := checkLog_sound (w := (2657 / 17343)) (n := 12)
    (lo := (154418807 / 500000000)) (hi := (61767523 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 7343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 7343) = 1/(7343 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-61767523 / 200000000) (-154418807 / 500000000) (Real.log (7343 / 10000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (757666999 / 1000000000) ≤ -Real.log (500000000000 / 1066646718031) ∧
    -Real.log (500000000000 / 1066646718031) ≤ (757667001 / 1000000000) := by
  have h := checkLog_sound (w := (66646718031 / 2066646718031)) (n := 12)
    (lo := (64519819 / 1000000000)) (hi := (3225991 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1066646718031 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1066646718031 / 1000000000000) = 1/(500000000000 / 1066646718031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (757666999 / 1000000000) (757667001 / 1000000000) (Real.log (1066646718031 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1066646718031 / 500000000000) = -Real.log (500000000000 / 1066646718031) := by
    rw [show ((1066646718031 / 500000000000) : ℝ) = ((500000000000 / 1066646718031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (758661221 / 1000000000) ≤ -Real.log (500000000000 / 1067707729113) ∧
    -Real.log (500000000000 / 1067707729113) ≤ (758661223 / 1000000000) := by
  have h := checkLog_sound (w := (67707729113 / 2067707729113)) (n := 12)
    (lo := (65514041 / 1000000000)) (hi := (32757021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1067707729113 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1067707729113 / 1000000000000) = 1/(500000000000 / 1067707729113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (758661221 / 1000000000) (758661223 / 1000000000) (Real.log (1067707729113 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1067707729113 / 500000000000) = -Real.log (500000000000 / 1067707729113) := by
    rw [show ((1067707729113 / 500000000000) : ℝ) = ((500000000000 / 1067707729113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (271865681 / 500000000) ≤ -Real.log (250000000000 / 430605466623) ∧
    -Real.log (250000000000 / 430605466623) ≤ (543731363 / 1000000000) := by
  have h := checkLog_sound (w := (180605466623 / 680605466623)) (n := 12)
    (lo := (271865681 / 500000000)) (hi := (543731363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((430605466623 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(430605466623 / 250000000000) = 1/(250000000000 / 430605466623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (271865681 / 500000000) (543731363 / 1000000000) (Real.log (430605466623 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (430605466623 / 250000000000) = -Real.log (250000000000 / 430605466623) := by
    rw [show ((430605466623 / 250000000000) : ℝ) = ((250000000000 / 430605466623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (544462943 / 1000000000) ≤ -Real.log (100000000000 / 172368241863) ∧
    -Real.log (100000000000 / 172368241863) ≤ (17014467 / 31250000) := by
  have h := checkLog_sound (w := (72368241863 / 272368241863)) (n := 12)
    (lo := (544462943 / 1000000000)) (hi := (17014467 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172368241863 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172368241863 / 100000000000) = 1/(100000000000 / 172368241863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (544462943 / 1000000000) (17014467 / 31250000) (Real.log (172368241863 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (172368241863 / 100000000000) = -Real.log (100000000000 / 172368241863) := by
    rw [show ((172368241863 / 100000000000) : ℝ) = ((100000000000 / 172368241863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0293

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0294Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0294
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

theorem reflection_log_1_neg : (112664331 / 500000000) ≤ -Real.log (2560 / 3207) ∧
    -Real.log (2560 / 3207) ≤ (225328663 / 1000000000) := by
  have h := checkLog_sound (w := (647 / 5767)) (n := 12)
    (lo := (112664331 / 500000000)) (hi := (225328663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3207 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3207 / 2560) = 1/(2560 / 3207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (112664331 / 500000000) (225328663 / 1000000000) (Real.log (3207 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3207 / 2560) = -Real.log (2560 / 3207) := by
    rw [show ((3207 / 2560) : ℝ) = ((2560 / 3207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (36416821 / 125000000) ≤ -Real.log (1913 / 2560) ∧
    -Real.log (1913 / 2560) ≤ (291334569 / 1000000000) := by
  have h := checkLog_sound (w := (647 / 4473)) (n := 12)
    (lo := (36416821 / 125000000)) (hi := (291334569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1913) = 1/(1913 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-291334569 / 1000000000) (-36416821 / 125000000) (Real.log (1913 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (225094771 / 1000000000) ≤ -Real.log (2048 / 2565) ∧
    -Real.log (2048 / 2565) ≤ (56273693 / 250000000) := by
  have h := checkLog_sound (w := (517 / 4613)) (n := 12)
    (lo := (225094771 / 1000000000)) (hi := (56273693 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2565 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2565 / 2048) = 1/(2048 / 2565) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (225094771 / 1000000000) (56273693 / 250000000) (Real.log (2565 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2565 / 2048) = -Real.log (2048 / 2565) := by
    rw [show ((2565 / 2048) : ℝ) = ((2048 / 2565) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (29094259 / 100000000) ≤ -Real.log (1531 / 2048) ∧
    -Real.log (1531 / 2048) ≤ (290942591 / 1000000000) := by
  have h := checkLog_sound (w := (517 / 3579)) (n := 12)
    (lo := (29094259 / 100000000)) (hi := (290942591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1531) = 1/(1531 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-290942591 / 1000000000) (-29094259 / 100000000) (Real.log (1531 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (409104311 / 1000000000) ≤ -Real.log (1280 / 1927) ∧
    -Real.log (1280 / 1927) ≤ (51138039 / 125000000) := by
  have h := checkLog_sound (w := (647 / 3207)) (n := 12)
    (lo := (409104311 / 1000000000)) (hi := (51138039 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1927 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1927 / 1280) = 1/(1280 / 1927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (409104311 / 1000000000) (51138039 / 125000000) (Real.log (1927 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1927 / 1280) = -Real.log (1280 / 1927) := by
    rw [show ((1927 / 1280) : ℝ) = ((1280 / 1927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (352072467 / 500000000) ≤ -Real.log (633 / 1280) ∧
    -Real.log (633 / 1280) ≤ (88018117 / 125000000) := by
  have h := checkLog_sound (w := (7 / 1273)) (n := 12)
    (lo := (5498877 / 500000000)) (hi := (2199551 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 633) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 633) = 1/(633 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-88018117 / 125000000) (-352072467 / 500000000) (Real.log (633 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (408715029 / 1000000000) ≤ -Real.log (1024 / 1541) ∧
    -Real.log (1024 / 1541) ≤ (40871503 / 100000000) := by
  have h := checkLog_sound (w := (517 / 2565)) (n := 12)
    (lo := (408715029 / 1000000000)) (hi := (40871503 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1541 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1541 / 1024) = 1/(1024 / 1541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (408715029 / 1000000000) (40871503 / 100000000) (Real.log (1541 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1541 / 1024) = -Real.log (1024 / 1541) := by
    rw [show ((1541 / 1024) : ℝ) = ((1024 / 1541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (702960801 / 1000000000) ≤ -Real.log (507 / 1024) ∧
    -Real.log (507 / 1024) ≤ (702960803 / 1000000000) := by
  have h := checkLog_sound (w := (5 / 1019)) (n := 12)
    (lo := (9813621 / 1000000000)) (hi := (4906811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 507) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(512 / 507) = 1/(507 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-702960803 / 1000000000) (-702960801 / 1000000000) (Real.log (507 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (308413679 / 1000000000) ≤ -Real.log (62500 / 85079) ∧
    -Real.log (62500 / 85079) ≤ (3855171 / 12500000) := by
  have h := checkLog_sound (w := (22579 / 147579)) (n := 12)
    (lo := (308413679 / 1000000000)) (hi := (3855171 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85079 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85079 / 62500) = 1/(62500 / 85079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (308413679 / 1000000000) (3855171 / 12500000) (Real.log (85079 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (85079 / 62500) = -Real.log (62500 / 85079) := by
    rw [show ((85079 / 62500) : ℝ) = ((62500 / 85079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (89652811 / 200000000) ≤ -Real.log (39921 / 62500) ∧
    -Real.log (39921 / 62500) ≤ (56033007 / 125000000) := by
  have h := checkLog_sound (w := (22579 / 102421)) (n := 12)
    (lo := (89652811 / 200000000)) (hi := (56033007 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 39921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 39921) = 1/(39921 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-56033007 / 125000000) (-89652811 / 200000000) (Real.log (39921 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (308730247 / 1000000000) ≤ -Real.log (200000 / 272339) ∧
    -Real.log (200000 / 272339) ≤ (38591281 / 125000000) := by
  have h := checkLog_sound (w := (72339 / 472339)) (n := 12)
    (lo := (308730247 / 1000000000)) (hi := (38591281 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272339 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272339 / 200000) = 1/(200000 / 272339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (308730247 / 1000000000) (38591281 / 125000000) (Real.log (272339 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (272339 / 200000) = -Real.log (200000 / 272339) := by
    rw [show ((272339 / 200000) : ℝ) = ((200000 / 272339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (448939053 / 1000000000) ≤ -Real.log (127661 / 200000) ∧
    -Real.log (127661 / 200000) ≤ (224469527 / 500000000) := by
  have h := checkLog_sound (w := (72339 / 327661)) (n := 12)
    (lo := (448939053 / 1000000000)) (hi := (224469527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 127661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 127661) = 1/(127661 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-224469527 / 500000000) (-448939053 / 1000000000) (Real.log (127661 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (58771983 / 250000000) ≤ -Real.log (50000 / 63251) ∧
    -Real.log (50000 / 63251) ≤ (235087933 / 1000000000) := by
  have h := checkLog_sound (w := (13251 / 113251)) (n := 12)
    (lo := (58771983 / 250000000)) (hi := (235087933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63251 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63251 / 50000) = 1/(50000 / 63251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (58771983 / 250000000) (235087933 / 1000000000) (Real.log (63251 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (63251 / 50000) = -Real.log (50000 / 63251) := by
    rw [show ((63251 / 50000) : ℝ) = ((50000 / 63251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (307911991 / 1000000000) ≤ -Real.log (36749 / 50000) ∧
    -Real.log (36749 / 50000) ≤ (38488999 / 125000000) := by
  have h := checkLog_sound (w := (13251 / 86749)) (n := 12)
    (lo := (307911991 / 1000000000)) (hi := (38488999 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 36749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 36749) = 1/(36749 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-38488999 / 125000000) (-307911991 / 1000000000) (Real.log (36749 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (14709841 / 62500000) ≤ -Real.log (1000000 / 1265361) ∧
    -Real.log (1000000 / 1265361) ≤ (235357457 / 1000000000) := by
  have h := checkLog_sound (w := (265361 / 2265361)) (n := 12)
    (lo := (14709841 / 62500000)) (hi := (235357457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1265361 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1265361 / 1000000) = 1/(1000000 / 1265361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (14709841 / 62500000) (235357457 / 1000000000) (Real.log (1265361 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1265361 / 1000000) = -Real.log (1000000 / 1265361) := by
    rw [show ((1265361 / 1000000) : ℝ) = ((1000000 / 1265361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (38547007 / 125000000) ≤ -Real.log (734639 / 1000000) ∧
    -Real.log (734639 / 1000000) ≤ (308376057 / 1000000000) := by
  have h := checkLog_sound (w := (265361 / 1734639)) (n := 12)
    (lo := (38547007 / 125000000)) (hi := (308376057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 734639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 734639) = 1/(734639 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-308376057 / 1000000000) (-38547007 / 125000000) (Real.log (734639 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (378338867 / 500000000) ≤ -Real.log (500000000000 / 1065592044287) ∧
    -Real.log (500000000000 / 1065592044287) ≤ (94584717 / 125000000) := by
  have h := checkLog_sound (w := (65592044287 / 2065592044287)) (n := 12)
    (lo := (31765277 / 500000000)) (hi := (12706111 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1065592044287 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1065592044287 / 1000000000000) = 1/(500000000000 / 1065592044287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (378338867 / 500000000) (94584717 / 125000000) (Real.log (1065592044287 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1065592044287 / 500000000000) = -Real.log (500000000000 / 1065592044287) := by
    rw [show ((1065592044287 / 500000000000) : ℝ) = ((500000000000 / 1065592044287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (7576693 / 10000000) ≤ -Real.log (250000000000 / 533324586209) ∧
    -Real.log (250000000000 / 533324586209) ≤ (378834651 / 500000000) := by
  have h := checkLog_sound (w := (33324586209 / 1033324586209)) (n := 12)
    (lo := (1613053 / 25000000)) (hi := (64522121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((533324586209 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(533324586209 / 500000000000) = 1/(250000000000 / 533324586209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (7576693 / 10000000) (378834651 / 500000000) (Real.log (533324586209 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (533324586209 / 250000000000) = -Real.log (250000000000 / 533324586209) := by
    rw [show ((533324586209 / 250000000000) : ℝ) = ((250000000000 / 533324586209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (542999923 / 1000000000) ≤ -Real.log (100000000000 / 172116248061) ∧
    -Real.log (100000000000 / 172116248061) ≤ (135749981 / 250000000) := by
  have h := checkLog_sound (w := (72116248061 / 272116248061)) (n := 12)
    (lo := (542999923 / 1000000000)) (hi := (135749981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172116248061 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172116248061 / 100000000000) = 1/(100000000000 / 172116248061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (542999923 / 1000000000) (135749981 / 250000000) (Real.log (172116248061 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (172116248061 / 100000000000) = -Real.log (100000000000 / 172116248061) := by
    rw [show ((172116248061 / 100000000000) : ℝ) = ((100000000000 / 172116248061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (543733513 / 1000000000) ≤ -Real.log (15625000000 / 26912899567) ∧
    -Real.log (15625000000 / 26912899567) ≤ (271866757 / 500000000) := by
  have h := checkLog_sound (w := (11287899567 / 42537899567)) (n := 12)
    (lo := (543733513 / 1000000000)) (hi := (271866757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26912899567 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26912899567 / 15625000000) = 1/(15625000000 / 26912899567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (543733513 / 1000000000) (271866757 / 500000000) (Real.log (26912899567 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (26912899567 / 15625000000) = -Real.log (15625000000 / 26912899567) := by
    rw [show ((26912899567 / 15625000000) : ℝ) = ((15625000000 / 26912899567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0294

end


