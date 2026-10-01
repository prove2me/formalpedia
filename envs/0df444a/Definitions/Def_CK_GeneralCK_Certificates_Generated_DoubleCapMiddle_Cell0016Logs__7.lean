-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0016Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0016Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:37:24.833807+00:00
-- url     : https://prove2.me/theorems/d3953bd5-cdaa-47d5-9e0c-bc1964882543
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0016Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0017Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0016Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0017Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0018Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0019Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0020Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0021Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0022Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0016Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0017Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0018Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0019Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0020Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0021Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0022Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0016Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0017Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0018Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0019Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0020Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0021Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0022Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0016Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0017Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0018Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0019Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0020Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0021Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0022Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0016Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0016
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

theorem reflection_log_1_neg : (50193901 / 125000000) ≤ -Real.log (512 / 765) ∧
    -Real.log (512 / 765) ≤ (401551209 / 1000000000) := by
  have h := checkLog_sound (w := (253 / 1277)) (n := 12)
    (lo := (50193901 / 125000000)) (hi := (401551209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((765 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(765 / 512) = 1/(512 / 765) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (50193901 / 125000000) (401551209 / 1000000000) (Real.log (765 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (765 / 512) = -Real.log (512 / 765) := by
    rw [show ((765 / 512) : ℝ) = ((512 / 765) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (681496563 / 1000000000) ≤ -Real.log (259 / 512) ∧
    -Real.log (259 / 512) ≤ (170374141 / 250000000) := by
  have h := checkLog_sound (w := (253 / 771)) (n := 12)
    (lo := (681496563 / 1000000000)) (hi := (170374141 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 259) = 1/(259 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-170374141 / 250000000) (-681496563 / 1000000000) (Real.log (259 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (400766587 / 1000000000) ≤ -Real.log (1280 / 1911) ∧
    -Real.log (1280 / 1911) ≤ (100191647 / 250000000) := by
  have h := checkLog_sound (w := (631 / 3191)) (n := 12)
    (lo := (400766587 / 1000000000)) (hi := (100191647 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1911 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1911 / 1280) = 1/(1280 / 1911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (400766587 / 1000000000) (100191647 / 250000000) (Real.log (1911 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1911 / 1280) = -Real.log (1280 / 1911) := by
    rw [show ((1911 / 1280) : ℝ) = ((1280 / 1911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (8489783 / 12500000) ≤ -Real.log (649 / 1280) ∧
    -Real.log (649 / 1280) ≤ (679182641 / 1000000000) := by
  have h := checkLog_sound (w := (631 / 1929)) (n := 12)
    (lo := (8489783 / 12500000)) (hi := (679182641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 649) = 1/(649 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-679182641 / 1000000000) (-8489783 / 12500000) (Real.log (649 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (171817643 / 250000000) ≤ -Real.log (256 / 509) ∧
    -Real.log (256 / 509) ≤ (687270573 / 1000000000) := by
  have h := checkLog_sound (w := (253 / 765)) (n := 12)
    (lo := (171817643 / 250000000)) (hi := (687270573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((509 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(509 / 256) = 1/(256 / 509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (171817643 / 250000000) (687270573 / 1000000000) (Real.log (509 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (509 / 256) = -Real.log (256 / 509) := by
    rw [show ((509 / 256) : ℝ) = ((256 / 509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (138955161 / 31250000) ≤ -Real.log (3 / 256) ∧
    -Real.log (3 / 256) ≤ (4446565159 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4 / 3) = 1/(3 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-4446565159 / 1000000000) (-138955161 / 31250000) (Real.log (3 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (343045547 / 500000000) ≤ -Real.log (640 / 1271) ∧
    -Real.log (640 / 1271) ≤ (137218219 / 200000000) := by
  have h := checkLog_sound (w := (631 / 1911)) (n := 12)
    (lo := (343045547 / 500000000)) (hi := (137218219 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1271 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1271 / 640) = 1/(640 / 1271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (343045547 / 500000000) (137218219 / 200000000) (Real.log (1271 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1271 / 640) = -Real.log (640 / 1271) := by
    rw [show ((1271 / 640) : ℝ) = ((640 / 1271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (852848719 / 200000000) ≤ -Real.log (9 / 640) ∧
    -Real.log (9 / 640) ≤ (2132121801 / 500000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10 / 9) = 1/(9 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2132121801 / 500000000) (-852848719 / 200000000) (Real.log (9 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (70622813 / 125000000) ≤ -Real.log (1000000 / 1759417) ∧
    -Real.log (1000000 / 1759417) ≤ (112996501 / 200000000) := by
  have h := checkLog_sound (w := (759417 / 2759417)) (n := 12)
    (lo := (70622813 / 125000000)) (hi := (112996501 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1759417 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1759417 / 1000000) = 1/(1000000 / 1759417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (70622813 / 125000000) (112996501 / 200000000) (Real.log (1759417 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1759417 / 1000000) = -Real.log (1000000 / 1759417) := by
    rw [show ((1759417 / 1000000) : ℝ) = ((1000000 / 1759417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1424690133 / 1000000000) ≤ -Real.log (240583 / 1000000) ∧
    -Real.log (240583 / 1000000) ≤ (178086267 / 125000000) := by
  have h := checkLog_sound (w := (9417 / 490583)) (n := 12)
    (lo := (38395773 / 1000000000)) (hi := (19197887 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 240583) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 240583) = 1/(240583 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-178086267 / 125000000) (-1424690133 / 1000000000) (Real.log (240583 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (566662331 / 1000000000) ≤ -Real.log (8000 / 14099) ∧
    -Real.log (8000 / 14099) ≤ (141665583 / 250000000) := by
  have h := checkLog_sound (w := (6099 / 22099)) (n := 12)
    (lo := (566662331 / 1000000000)) (hi := (141665583 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14099 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14099 / 8000) = 1/(8000 / 14099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (566662331 / 1000000000) (141665583 / 250000000) (Real.log (14099 / 8000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (14099 / 8000) = -Real.log (8000 / 14099) := by
    rw [show ((14099 / 8000) : ℝ) = ((8000 / 14099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1437061477 / 1000000000) ≤ -Real.log (1901 / 8000) ∧
    -Real.log (1901 / 8000) ≤ (35926537 / 25000000) := by
  have h := checkLog_sound (w := (99 / 3901)) (n := 12)
    (lo := (50767117 / 1000000000)) (hi := (25383559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1901) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2000 / 1901) = 1/(1901 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-35926537 / 25000000) (-1437061477 / 1000000000) (Real.log (1901 / 8000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (492367923 / 1000000000) ≤ -Real.log (500000 / 818093) ∧
    -Real.log (500000 / 818093) ≤ (123091981 / 250000000) := by
  have h := checkLog_sound (w := (318093 / 1318093)) (n := 12)
    (lo := (492367923 / 1000000000)) (hi := (123091981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((818093 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(818093 / 500000) = 1/(500000 / 818093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (492367923 / 1000000000) (123091981 / 250000000) (Real.log (818093 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (818093 / 500000) = -Real.log (500000 / 818093) := by
    rw [show ((818093 / 500000) : ℝ) = ((500000 / 818093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (101111253 / 100000000) ≤ -Real.log (181907 / 500000) ∧
    -Real.log (181907 / 500000) ≤ (252778133 / 250000000) := by
  have h := checkLog_sound (w := (68093 / 431907)) (n := 12)
    (lo := (6359307 / 20000000)) (hi := (317965351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 181907) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 181907) = 1/(181907 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-252778133 / 250000000) (-101111253 / 100000000) (Real.log (181907 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (494383997 / 1000000000) ≤ -Real.log (15625 / 25617) ∧
    -Real.log (15625 / 25617) ≤ (247191999 / 500000000) := by
  have h := checkLog_sound (w := (4996 / 20621)) (n := 12)
    (lo := (494383997 / 1000000000)) (hi := (247191999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25617 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25617 / 15625) = 1/(15625 / 25617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (494383997 / 1000000000) (247191999 / 500000000) (Real.log (25617 / 15625)) := by
  have h := reflection_log_15_neg
  have he : Real.log (25617 / 15625) = -Real.log (15625 / 25617) := by
    rw [show ((25617 / 15625) : ℝ) = ((15625 / 25617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (204046007 / 200000000) ≤ -Real.log (5633 / 15625) ∧
    -Real.log (5633 / 15625) ≤ (1020230037 / 1000000000) := by
  have h := checkLog_sound (w := (4359 / 26891)) (n := 12)
    (lo := (65416571 / 200000000)) (hi := (40885357 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11266) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15625 / 11266) = 1/(5633 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1020230037 / 1000000000) (-204046007 / 200000000) (Real.log (5633 / 15625)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1989672637 / 1000000000) ≤ -Real.log (100000000000 / 731313933237) ∧
    -Real.log (100000000000 / 731313933237) ≤ (6217727 / 3125000) := by
  have h := checkLog_sound (w := (331313933237 / 1131313933237)) (n := 12)
    (lo := (603378277 / 1000000000)) (hi := (301689139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731313933237 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(731313933237 / 400000000000) = 1/(100000000000 / 731313933237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1989672637 / 1000000000) (6217727 / 3125000) (Real.log (731313933237 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (731313933237 / 100000000000) = -Real.log (100000000000 / 731313933237) := by
    rw [show ((731313933237 / 100000000000) : ℝ) = ((100000000000 / 731313933237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (62616369 / 31250000) ≤ -Real.log (100000000000 / 741662283009) ∧
    -Real.log (100000000000 / 741662283009) ≤ (2003723811 / 1000000000) := by
  have h := checkLog_sound (w := (341662283009 / 1141662283009)) (n := 12)
    (lo := (77178681 / 125000000)) (hi := (617429449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741662283009 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(741662283009 / 400000000000) = 1/(100000000000 / 741662283009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (62616369 / 31250000) (2003723811 / 1000000000) (Real.log (741662283009 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (741662283009 / 100000000000) = -Real.log (100000000000 / 741662283009) := by
    rw [show ((741662283009 / 100000000000) : ℝ) = ((100000000000 / 741662283009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1503480453 / 1000000000) ≤ -Real.log (250000000000 / 1124328640459) ∧
    -Real.log (250000000000 / 1124328640459) ≤ (187935057 / 125000000) := by
  have h := checkLog_sound (w := (124328640459 / 2124328640459)) (n := 12)
    (lo := (117186093 / 1000000000)) (hi := (58593047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1124328640459 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1124328640459 / 1000000000000) = 1/(250000000000 / 1124328640459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1503480453 / 1000000000) (187935057 / 125000000) (Real.log (1124328640459 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1124328640459 / 250000000000) = -Real.log (250000000000 / 1124328640459) := by
    rw [show ((1124328640459 / 250000000000) : ℝ) = ((250000000000 / 1124328640459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (94663377 / 62500000) ≤ -Real.log (50000000000 / 227383277117) ∧
    -Real.log (50000000000 / 227383277117) ≤ (302922807 / 200000000) := by
  have h := checkLog_sound (w := (27383277117 / 427383277117)) (n := 12)
    (lo := (16039959 / 125000000)) (hi := (128319673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((227383277117 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(227383277117 / 200000000000) = 1/(50000000000 / 227383277117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (94663377 / 62500000) (302922807 / 200000000) (Real.log (227383277117 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (227383277117 / 50000000000) = -Real.log (50000000000 / 227383277117) := by
    rw [show ((227383277117 / 50000000000) : ℝ) = ((50000000000 / 227383277117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0016

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0017Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0017
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

theorem reflection_log_1_neg : (400766587 / 1000000000) ≤ -Real.log (1280 / 1911) ∧
    -Real.log (1280 / 1911) ≤ (100191647 / 250000000) := by
  have h := checkLog_sound (w := (631 / 3191)) (n := 12)
    (lo := (400766587 / 1000000000)) (hi := (100191647 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1911 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1911 / 1280) = 1/(1280 / 1911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (400766587 / 1000000000) (100191647 / 250000000) (Real.log (1911 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1911 / 1280) = -Real.log (1280 / 1911) := by
    rw [show ((1911 / 1280) : ℝ) = ((1280 / 1911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (8489783 / 12500000) ≤ -Real.log (649 / 1280) ∧
    -Real.log (649 / 1280) ≤ (679182641 / 1000000000) := by
  have h := checkLog_sound (w := (631 / 1929)) (n := 12)
    (lo := (8489783 / 12500000)) (hi := (679182641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 649) = 1/(649 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-679182641 / 1000000000) (-8489783 / 12500000) (Real.log (649 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (399981349 / 1000000000) ≤ -Real.log (2560 / 3819) ∧
    -Real.log (2560 / 3819) ≤ (7999627 / 20000000) := by
  have h := checkLog_sound (w := (1259 / 6379)) (n := 12)
    (lo := (399981349 / 1000000000)) (hi := (7999627 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3819 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3819 / 2560) = 1/(2560 / 3819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (399981349 / 1000000000) (7999627 / 20000000) (Real.log (3819 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3819 / 2560) = -Real.log (2560 / 3819) := by
    rw [show ((3819 / 2560) : ℝ) = ((2560 / 3819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (338437029 / 500000000) ≤ -Real.log (1301 / 2560) ∧
    -Real.log (1301 / 2560) ≤ (676874059 / 1000000000) := by
  have h := checkLog_sound (w := (1259 / 3861)) (n := 12)
    (lo := (338437029 / 500000000)) (hi := (676874059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1301) = 1/(1301 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-676874059 / 1000000000) (-338437029 / 500000000) (Real.log (1301 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (343045547 / 500000000) ≤ -Real.log (640 / 1271) ∧
    -Real.log (640 / 1271) ≤ (137218219 / 200000000) := by
  have h := checkLog_sound (w := (631 / 1911)) (n := 12)
    (lo := (343045547 / 500000000)) (hi := (137218219 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1271 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1271 / 640) = 1/(640 / 1271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (343045547 / 500000000) (137218219 / 200000000) (Real.log (1271 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1271 / 640) = -Real.log (640 / 1271) := by
    rw [show ((1271 / 640) : ℝ) = ((640 / 1271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (852848719 / 200000000) ≤ -Real.log (9 / 640) ∧
    -Real.log (9 / 640) ≤ (2132121801 / 500000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10 / 9) = 1/(9 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2132121801 / 500000000) (-852848719 / 200000000) (Real.log (9 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (42806889 / 62500000) ≤ -Real.log (1280 / 2539) ∧
    -Real.log (1280 / 2539) ≤ (27396409 / 40000000) := by
  have h := checkLog_sound (w := (1259 / 3819)) (n := 12)
    (lo := (42806889 / 62500000)) (hi := (27396409 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2539 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2539 / 1280) = 1/(1280 / 2539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (42806889 / 62500000) (27396409 / 40000000) (Real.log (2539 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2539 / 1280) = -Real.log (1280 / 2539) := by
    rw [show ((2539 / 1280) : ℝ) = ((1280 / 2539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1027523229 / 250000000) ≤ -Real.log (21 / 1280) ∧
    -Real.log (21 / 1280) ≤ (2055046461 / 500000000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(40 / 21) = 1/(21 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2055046461 / 500000000) (-1027523229 / 250000000) (Real.log (21 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (281672413 / 500000000) ≤ -Real.log (500000 / 878269) ∧
    -Real.log (500000 / 878269) ≤ (563344827 / 1000000000) := by
  have h := checkLog_sound (w := (378269 / 1378269)) (n := 12)
    (lo := (281672413 / 500000000)) (hi := (563344827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((878269 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(878269 / 500000) = 1/(500000 / 878269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (281672413 / 500000000) (563344827 / 1000000000) (Real.log (878269 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (878269 / 500000) = -Real.log (500000 / 878269) := by
    rw [show ((878269 / 500000) : ℝ) = ((500000 / 878269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (282558881 / 200000000) ≤ -Real.log (121731 / 500000) ∧
    -Real.log (121731 / 500000) ≤ (176599301 / 125000000) := by
  have h := checkLog_sound (w := (3269 / 246731)) (n := 12)
    (lo := (5300009 / 200000000)) (hi := (13250023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 121731) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 121731) = 1/(121731 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-176599301 / 125000000) (-282558881 / 200000000) (Real.log (121731 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (17655721 / 31250000) ≤ -Real.log (500000 / 879709) ∧
    -Real.log (500000 / 879709) ≤ (564983073 / 1000000000) := by
  have h := checkLog_sound (w := (379709 / 1379709)) (n := 12)
    (lo := (17655721 / 31250000)) (hi := (564983073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((879709 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(879709 / 500000) = 1/(500000 / 879709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (17655721 / 31250000) (564983073 / 1000000000) (Real.log (879709 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (879709 / 500000) = -Real.log (500000 / 879709) := by
    rw [show ((879709 / 500000) : ℝ) = ((500000 / 879709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (142469429 / 100000000) ≤ -Real.log (120291 / 500000) ∧
    -Real.log (120291 / 500000) ≤ (1424694293 / 1000000000) := by
  have h := checkLog_sound (w := (4709 / 245291)) (n := 12)
    (lo := (3839993 / 100000000)) (hi := (38399931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 120291) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 120291) = 1/(120291 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1424694293 / 1000000000) (-142469429 / 100000000) (Real.log (120291 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (490404117 / 1000000000) ≤ -Real.log (62500 / 102061) ∧
    -Real.log (62500 / 102061) ≤ (245202059 / 500000000) := by
  have h := checkLog_sound (w := (39561 / 164561)) (n := 12)
    (lo := (490404117 / 1000000000)) (hi := (245202059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102061 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102061 / 62500) = 1/(62500 / 102061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (490404117 / 1000000000) (245202059 / 500000000) (Real.log (102061 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (102061 / 62500) = -Real.log (62500 / 102061) := by
    rw [show ((102061 / 62500) : ℝ) = ((62500 / 102061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1002328037 / 1000000000) ≤ -Real.log (22939 / 62500) ∧
    -Real.log (22939 / 62500) ≤ (1002328039 / 1000000000) := by
  have h := checkLog_sound (w := (8311 / 54189)) (n := 12)
    (lo := (309180857 / 1000000000)) (hi := (154590429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22939) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 22939) = 1/(22939 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1002328039 / 1000000000) (-1002328037 / 1000000000) (Real.log (22939 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (246184267 / 500000000) ≤ -Real.log (1000000 / 1636187) ∧
    -Real.log (1000000 / 1636187) ≤ (98473707 / 200000000) := by
  have h := checkLog_sound (w := (636187 / 2636187)) (n := 12)
    (lo := (246184267 / 500000000)) (hi := (98473707 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1636187 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1636187 / 1000000) = 1/(1000000 / 1636187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (246184267 / 500000000) (98473707 / 200000000) (Real.log (1636187 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1636187 / 1000000) = -Real.log (1000000 / 1636187) := by
    rw [show ((1636187 / 1000000) : ℝ) = ((1000000 / 1636187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1011115279 / 1000000000) ≤ -Real.log (363813 / 1000000) ∧
    -Real.log (363813 / 1000000) ≤ (1011115281 / 1000000000) := by
  have h := checkLog_sound (w := (136187 / 863813)) (n := 12)
    (lo := (317968099 / 1000000000)) (hi := (3179681 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 363813) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 363813) = 1/(363813 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1011115281 / 1000000000) (-1011115279 / 1000000000) (Real.log (363813 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1976139231 / 1000000000) ≤ -Real.log (125000000000 / 901854293483) ∧
    -Real.log (125000000000 / 901854293483) ≤ (988069617 / 500000000) := by
  have h := checkLog_sound (w := (401854293483 / 1401854293483)) (n := 12)
    (lo := (589844871 / 1000000000)) (hi := (73730609 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((901854293483 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(901854293483 / 500000000000) = 1/(125000000000 / 901854293483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1976139231 / 1000000000) (988069617 / 500000000) (Real.log (901854293483 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (901854293483 / 125000000000) = -Real.log (125000000000 / 901854293483) := by
    rw [show ((901854293483 / 125000000000) : ℝ) = ((125000000000 / 901854293483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (994838681 / 500000000) ≤ -Real.log (50000000000 / 365658694333) ∧
    -Real.log (50000000000 / 365658694333) ≤ (397935473 / 200000000) := by
  have h := checkLog_sound (w := (165658694333 / 565658694333)) (n := 12)
    (lo := (301691501 / 500000000)) (hi := (603383003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((365658694333 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(365658694333 / 200000000000) = 1/(50000000000 / 365658694333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (994838681 / 500000000) (397935473 / 200000000) (Real.log (365658694333 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (365658694333 / 50000000000) = -Real.log (50000000000 / 365658694333) := by
    rw [show ((365658694333 / 50000000000) : ℝ) = ((50000000000 / 365658694333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1492732153 / 1000000000) ≤ -Real.log (125000000000 / 556154365927) ∧
    -Real.log (125000000000 / 556154365927) ≤ (373183039 / 250000000) := by
  have h := checkLog_sound (w := (56154365927 / 1056154365927)) (n := 12)
    (lo := (106437793 / 1000000000)) (hi := (53218897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((556154365927 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(556154365927 / 500000000000) = 1/(125000000000 / 556154365927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1492732153 / 1000000000) (373183039 / 250000000) (Real.log (556154365927 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (556154365927 / 125000000000) = -Real.log (125000000000 / 556154365927) := by
    rw [show ((556154365927 / 125000000000) : ℝ) = ((125000000000 / 556154365927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1503483813 / 1000000000) ≤ -Real.log (62500000000 / 281083104507) ∧
    -Real.log (62500000000 / 281083104507) ≤ (187935477 / 125000000) := by
  have h := checkLog_sound (w := (31083104507 / 531083104507)) (n := 12)
    (lo := (117189453 / 1000000000)) (hi := (58594727 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((281083104507 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(281083104507 / 250000000000) = 1/(62500000000 / 281083104507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1503483813 / 1000000000) (187935477 / 125000000) (Real.log (281083104507 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (281083104507 / 62500000000) = -Real.log (62500000000 / 281083104507) := by
    rw [show ((281083104507 / 62500000000) : ℝ) = ((62500000000 / 281083104507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0017

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0018Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0018
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

theorem reflection_log_1_neg : (399981349 / 1000000000) ≤ -Real.log (2560 / 3819) ∧
    -Real.log (2560 / 3819) ≤ (7999627 / 20000000) := by
  have h := checkLog_sound (w := (1259 / 6379)) (n := 12)
    (lo := (399981349 / 1000000000)) (hi := (7999627 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3819 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3819 / 2560) = 1/(2560 / 3819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (399981349 / 1000000000) (7999627 / 20000000) (Real.log (3819 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3819 / 2560) = -Real.log (2560 / 3819) := by
    rw [show ((3819 / 2560) : ℝ) = ((2560 / 3819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (338437029 / 500000000) ≤ -Real.log (1301 / 2560) ∧
    -Real.log (1301 / 2560) ≤ (676874059 / 1000000000) := by
  have h := checkLog_sound (w := (1259 / 3861)) (n := 12)
    (lo := (338437029 / 500000000)) (hi := (676874059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1301) = 1/(1301 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-676874059 / 1000000000) (-338437029 / 500000000) (Real.log (1301 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (79839099 / 200000000) ≤ -Real.log (320 / 477) ∧
    -Real.log (320 / 477) ≤ (49899437 / 125000000) := by
  have h := checkLog_sound (w := (157 / 797)) (n := 12)
    (lo := (79839099 / 200000000)) (hi := (49899437 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((477 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(477 / 320) = 1/(320 / 477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (79839099 / 200000000) (49899437 / 125000000) (Real.log (477 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (477 / 320) = -Real.log (320 / 477) := by
    rw [show ((477 / 320) : ℝ) = ((320 / 477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (337285397 / 500000000) ≤ -Real.log (163 / 320) ∧
    -Real.log (163 / 320) ≤ (134914159 / 200000000) := by
  have h := checkLog_sound (w := (157 / 483)) (n := 12)
    (lo := (337285397 / 500000000)) (hi := (134914159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 163) = 1/(163 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-134914159 / 200000000) (-337285397 / 500000000) (Real.log (163 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (42806889 / 62500000) ≤ -Real.log (1280 / 2539) ∧
    -Real.log (1280 / 2539) ≤ (27396409 / 40000000) := by
  have h := checkLog_sound (w := (1259 / 3819)) (n := 12)
    (lo := (42806889 / 62500000)) (hi := (27396409 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2539 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2539 / 1280) = 1/(1280 / 2539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (42806889 / 62500000) (27396409 / 40000000) (Real.log (2539 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2539 / 1280) = -Real.log (1280 / 2539) := by
    rw [show ((2539 / 1280) : ℝ) = ((1280 / 2539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1027523229 / 250000000) ≤ -Real.log (21 / 1280) ∧
    -Real.log (21 / 1280) ≤ (2055046461 / 500000000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(40 / 21) = 1/(21 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2055046461 / 500000000) (-1027523229 / 250000000) (Real.log (21 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (341863979 / 500000000) ≤ -Real.log (160 / 317) ∧
    -Real.log (160 / 317) ≤ (683727959 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 477)) (n := 12)
    (lo := (341863979 / 500000000)) (hi := (683727959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(317 / 160) = 1/(160 / 317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (341863979 / 500000000) (683727959 / 1000000000) (Real.log (317 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (317 / 160) = -Real.log (160 / 317) := by
    rw [show ((317 / 160) : ℝ) = ((160 / 317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3976561523 / 1000000000) ≤ -Real.log (3 / 160) ∧
    -Real.log (3 / 160) ≤ (3976561529 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5 / 3) = 1/(3 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3976561529 / 1000000000) (-3976561523 / 1000000000) (Real.log (3 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (561742667 / 1000000000) ≤ -Real.log (500000 / 876863) ∧
    -Real.log (500000 / 876863) ≤ (140435667 / 250000000) := by
  have h := checkLog_sound (w := (376863 / 1376863)) (n := 12)
    (lo := (561742667 / 1000000000)) (hi := (140435667 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((876863 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(876863 / 500000) = 1/(500000 / 876863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (561742667 / 1000000000) (140435667 / 250000000) (Real.log (876863 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (876863 / 500000) = -Real.log (500000 / 876863) := by
    rw [show ((876863 / 500000) : ℝ) = ((500000 / 876863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (70065527 / 50000000) ≤ -Real.log (123137 / 500000) ∧
    -Real.log (123137 / 500000) ≤ (1401310543 / 1000000000) := by
  have h := checkLog_sound (w := (1863 / 248137)) (n := 12)
    (lo := (750809 / 50000000)) (hi := (15016181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 123137) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 123137) = 1/(123137 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1401310543 / 1000000000) (-70065527 / 50000000) (Real.log (123137 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (112669079 / 200000000) ≤ -Real.log (1000000 / 1756539) ∧
    -Real.log (1000000 / 1756539) ≤ (140836349 / 250000000) := by
  have h := checkLog_sound (w := (756539 / 2756539)) (n := 12)
    (lo := (112669079 / 200000000)) (hi := (140836349 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1756539 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1756539 / 1000000) = 1/(1000000 / 1756539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (112669079 / 200000000) (140836349 / 250000000) (Real.log (1756539 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1756539 / 1000000) = -Real.log (1000000 / 1756539) := by
    rw [show ((1756539 / 1000000) : ℝ) = ((1000000 / 1756539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (88299907 / 62500000) ≤ -Real.log (243461 / 1000000) ∧
    -Real.log (243461 / 1000000) ≤ (282559703 / 200000000) := by
  have h := checkLog_sound (w := (6539 / 493461)) (n := 12)
    (lo := (3313019 / 125000000)) (hi := (26504153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 243461) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 243461) = 1/(243461 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-282559703 / 200000000) (-88299907 / 62500000) (Real.log (243461 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (30530269 / 62500000) ≤ -Real.log (250000 / 407461) ∧
    -Real.log (250000 / 407461) ≤ (97696861 / 200000000) := by
  have h := checkLog_sound (w := (157461 / 657461)) (n := 12)
    (lo := (30530269 / 62500000)) (hi := (97696861 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((407461 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(407461 / 250000) = 1/(250000 / 407461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (30530269 / 62500000) (97696861 / 200000000) (Real.log (407461 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (407461 / 250000) = -Real.log (250000 / 407461) := by
    rw [show ((407461 / 250000) : ℝ) = ((250000 / 407461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (49691537 / 50000000) ≤ -Real.log (92539 / 250000) ∧
    -Real.log (92539 / 250000) ≤ (496915371 / 500000000) := by
  have h := checkLog_sound (w := (32461 / 217539)) (n := 12)
    (lo := (7517089 / 25000000)) (hi := (300683561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 92539) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 92539) = 1/(92539 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-496915371 / 500000000) (-49691537 / 50000000) (Real.log (92539 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (490404729 / 1000000000) ≤ -Real.log (1000000 / 1632977) ∧
    -Real.log (1000000 / 1632977) ≤ (49040473 / 100000000) := by
  have h := checkLog_sound (w := (632977 / 2632977)) (n := 12)
    (lo := (490404729 / 1000000000)) (hi := (49040473 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1632977 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1632977 / 1000000) = 1/(1000000 / 1632977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (490404729 / 1000000000) (49040473 / 100000000) (Real.log (1632977 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1632977 / 1000000) = -Real.log (1000000 / 1632977) := by
    rw [show ((1632977 / 1000000) : ℝ) = ((1000000 / 1632977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (501165381 / 500000000) ≤ -Real.log (367023 / 1000000) ∧
    -Real.log (367023 / 1000000) ≤ (250582691 / 250000000) := by
  have h := checkLog_sound (w := (132977 / 867023)) (n := 12)
    (lo := (154591791 / 500000000)) (hi := (309183583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 367023) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 367023) = 1/(367023 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-250582691 / 250000000) (-501165381 / 500000000) (Real.log (367023 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (245381651 / 125000000) ≤ -Real.log (50000000000 / 356051795967) ∧
    -Real.log (50000000000 / 356051795967) ≤ (1963053211 / 1000000000) := by
  have h := checkLog_sound (w := (156051795967 / 556051795967)) (n := 12)
    (lo := (9011857 / 15625000)) (hi := (576758849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((356051795967 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(356051795967 / 200000000000) = 1/(50000000000 / 356051795967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (245381651 / 125000000) (1963053211 / 1000000000) (Real.log (356051795967 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (356051795967 / 50000000000) = -Real.log (50000000000 / 356051795967) := by
    rw [show ((356051795967 / 50000000000) : ℝ) = ((50000000000 / 356051795967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (494035977 / 250000000) ≤ -Real.log (250000000000 / 1803717022439) ∧
    -Real.log (250000000000 / 1803717022439) ≤ (1976143911 / 1000000000) := by
  have h := checkLog_sound (w := (803717022439 / 2803717022439)) (n := 12)
    (lo := (147462387 / 250000000)) (hi := (589849549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1803717022439 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1803717022439 / 1000000000000) = 1/(250000000000 / 1803717022439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (494035977 / 250000000) (1976143911 / 1000000000) (Real.log (1803717022439 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1803717022439 / 250000000000) = -Real.log (250000000000 / 1803717022439) := by
    rw [show ((1803717022439 / 250000000000) : ℝ) = ((250000000000 / 1803717022439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (370578761 / 250000000) ≤ -Real.log (500000000000 / 2201563665049) ∧
    -Real.log (500000000000 / 2201563665049) ≤ (1482315047 / 1000000000) := by
  have h := checkLog_sound (w := (201563665049 / 4201563665049)) (n := 12)
    (lo := (24005171 / 250000000)) (hi := (19204137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2201563665049 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2201563665049 / 2000000000000) = 1/(500000000000 / 2201563665049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (370578761 / 250000000) (1482315047 / 1000000000) (Real.log (2201563665049 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2201563665049 / 500000000000) = -Real.log (500000000000 / 2201563665049) := by
    rw [show ((2201563665049 / 500000000000) : ℝ) = ((500000000000 / 2201563665049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (149273549 / 100000000) ≤ -Real.log (500000000000 / 2224624887269) ∧
    -Real.log (500000000000 / 2224624887269) ≤ (1492735493 / 1000000000) := by
  have h := checkLog_sound (w := (224624887269 / 4224624887269)) (n := 12)
    (lo := (10644113 / 100000000)) (hi := (106441131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2224624887269 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2224624887269 / 2000000000000) = 1/(500000000000 / 2224624887269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (149273549 / 100000000) (1492735493 / 1000000000) (Real.log (2224624887269 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2224624887269 / 500000000000) = -Real.log (500000000000 / 2224624887269) := by
    rw [show ((2224624887269 / 500000000000) : ℝ) = ((500000000000 / 2224624887269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0018

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0019Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0019
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

theorem reflection_log_1_neg : (79839099 / 200000000) ≤ -Real.log (320 / 477) ∧
    -Real.log (320 / 477) ≤ (49899437 / 125000000) := by
  have h := checkLog_sound (w := (157 / 797)) (n := 12)
    (lo := (79839099 / 200000000)) (hi := (49899437 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((477 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(477 / 320) = 1/(320 / 477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (79839099 / 200000000) (49899437 / 125000000) (Real.log (477 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (477 / 320) = -Real.log (320 / 477) := by
    rw [show ((477 / 320) : ℝ) = ((320 / 477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (337285397 / 500000000) ≤ -Real.log (163 / 320) ∧
    -Real.log (163 / 320) ≤ (134914159 / 200000000) := by
  have h := checkLog_sound (w := (157 / 483)) (n := 12)
    (lo := (337285397 / 500000000)) (hi := (134914159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 163) = 1/(163 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-134914159 / 200000000) (-337285397 / 500000000) (Real.log (163 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (199204511 / 500000000) ≤ -Real.log (2560 / 3813) ∧
    -Real.log (2560 / 3813) ≤ (398409023 / 1000000000) := by
  have h := checkLog_sound (w := (1253 / 6373)) (n := 12)
    (lo := (199204511 / 500000000)) (hi := (398409023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3813 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3813 / 2560) = 1/(2560 / 3813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (199204511 / 500000000) (398409023 / 1000000000) (Real.log (3813 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3813 / 2560) = -Real.log (2560 / 3813) := by
    rw [show ((3813 / 2560) : ℝ) = ((2560 / 3813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (672272823 / 1000000000) ≤ -Real.log (1307 / 2560) ∧
    -Real.log (1307 / 2560) ≤ (84034103 / 125000000) := by
  have h := checkLog_sound (w := (1253 / 3867)) (n := 12)
    (lo := (672272823 / 1000000000)) (hi := (84034103 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1307) = 1/(1307 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-84034103 / 125000000) (-672272823 / 1000000000) (Real.log (1307 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (341863979 / 500000000) ≤ -Real.log (160 / 317) ∧
    -Real.log (160 / 317) ≤ (683727959 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 477)) (n := 12)
    (lo := (341863979 / 500000000)) (hi := (683727959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(317 / 160) = 1/(160 / 317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (341863979 / 500000000) (683727959 / 1000000000) (Real.log (317 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (317 / 160) = -Real.log (160 / 317) := by
    rw [show ((317 / 160) : ℝ) = ((160 / 317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3976561523 / 1000000000) ≤ -Real.log (3 / 160) ∧
    -Real.log (3 / 160) ≤ (3976561529 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5 / 3) = 1/(3 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3976561529 / 1000000000) (-3976561523 / 1000000000) (Real.log (3 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (682544293 / 1000000000) ≤ -Real.log (1280 / 2533) ∧
    -Real.log (1280 / 2533) ≤ (341272147 / 500000000) := by
  have h := checkLog_sound (w := (1253 / 3813)) (n := 12)
    (lo := (682544293 / 1000000000)) (hi := (341272147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2533 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2533 / 1280) = 1/(1280 / 2533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (682544293 / 1000000000) (341272147 / 500000000) (Real.log (2533 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2533 / 1280) = -Real.log (1280 / 2533) := by
    rw [show ((2533 / 1280) : ℝ) = ((1280 / 2533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (482347311 / 125000000) ≤ -Real.log (27 / 1280) ∧
    -Real.log (27 / 1280) ≤ (1929389247 / 500000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(40 / 27) = 1/(27 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1929389247 / 500000000) (-482347311 / 125000000) (Real.log (27 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (560170491 / 1000000000) ≤ -Real.log (1000000 / 1750971) ∧
    -Real.log (1000000 / 1750971) ≤ (140042623 / 250000000) := by
  have h := checkLog_sound (w := (750971 / 2750971)) (n := 12)
    (lo := (560170491 / 1000000000)) (hi := (140042623 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1750971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1750971 / 1000000) = 1/(1000000 / 1750971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (560170491 / 1000000000) (140042623 / 250000000) (Real.log (1750971 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1750971 / 1000000) = -Real.log (1000000 / 1750971) := by
    rw [show ((1750971 / 1000000) : ℝ) = ((1000000 / 1750971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (695092961 / 500000000) ≤ -Real.log (249029 / 1000000) ∧
    -Real.log (249029 / 1000000) ≤ (55607437 / 40000000) := by
  have h := checkLog_sound (w := (971 / 499029)) (n := 12)
    (lo := (1945781 / 500000000)) (hi := (3891563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249029) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 249029) = 1/(249029 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-55607437 / 40000000) (-695092961 / 500000000) (Real.log (249029 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (561743237 / 1000000000) ≤ -Real.log (1000000 / 1753727) ∧
    -Real.log (1000000 / 1753727) ≤ (280871619 / 500000000) := by
  have h := checkLog_sound (w := (753727 / 2753727)) (n := 12)
    (lo := (561743237 / 1000000000)) (hi := (280871619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1753727 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1753727 / 1000000) = 1/(1000000 / 1753727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (561743237 / 1000000000) (280871619 / 500000000) (Real.log (1753727 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1753727 / 1000000) = -Real.log (1000000 / 1753727) := by
    rw [show ((1753727 / 1000000) : ℝ) = ((1000000 / 1753727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1401314601 / 1000000000) ≤ -Real.log (246273 / 1000000) ∧
    -Real.log (246273 / 1000000) ≤ (350328651 / 250000000) := by
  have h := checkLog_sound (w := (3727 / 496273)) (n := 12)
    (lo := (15020241 / 1000000000)) (hi := (7510121 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 246273) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 246273) = 1/(246273 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-350328651 / 250000000) (-1401314601 / 1000000000) (Real.log (246273 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (2433013 / 5000000) ≤ -Real.log (50000 / 81339) ∧
    -Real.log (50000 / 81339) ≤ (486602601 / 1000000000) := by
  have h := checkLog_sound (w := (31339 / 131339)) (n := 12)
    (lo := (2433013 / 5000000)) (hi := (486602601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81339 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81339 / 50000) = 1/(50000 / 81339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (2433013 / 5000000) (486602601 / 1000000000) (Real.log (81339 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (81339 / 50000) = -Real.log (50000 / 81339) := by
    rw [show ((81339 / 50000) : ℝ) = ((50000 / 81339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (49279361 / 50000000) ≤ -Real.log (18661 / 50000) ∧
    -Real.log (18661 / 50000) ≤ (492793611 / 500000000) := by
  have h := checkLog_sound (w := (6339 / 43661)) (n := 12)
    (lo := (7311001 / 25000000)) (hi := (292440041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 18661) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25000 / 18661) = 1/(18661 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-492793611 / 500000000) (-49279361 / 50000000) (Real.log (18661 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (244242459 / 500000000) ≤ -Real.log (200000 / 325969) ∧
    -Real.log (200000 / 325969) ≤ (488484919 / 1000000000) := by
  have h := checkLog_sound (w := (125969 / 525969)) (n := 12)
    (lo := (244242459 / 500000000)) (hi := (488484919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((325969 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(325969 / 200000) = 1/(200000 / 325969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (244242459 / 500000000) (488484919 / 1000000000) (Real.log (325969 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (325969 / 200000) = -Real.log (200000 / 325969) := by
    rw [show ((325969 / 200000) : ℝ) = ((200000 / 325969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (993833441 / 1000000000) ≤ -Real.log (74031 / 200000) ∧
    -Real.log (74031 / 200000) ≤ (993833443 / 1000000000) := by
  have h := checkLog_sound (w := (25969 / 174031)) (n := 12)
    (lo := (300686261 / 1000000000)) (hi := (150343131 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 74031) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 74031) = 1/(74031 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-993833443 / 1000000000) (-993833441 / 1000000000) (Real.log (74031 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1950356413 / 1000000000) ≤ -Real.log (100000000000 / 703119315421) ∧
    -Real.log (100000000000 / 703119315421) ≤ (30474319 / 15625000) := by
  have h := checkLog_sound (w := (303119315421 / 1103119315421)) (n := 12)
    (lo := (564062053 / 1000000000)) (hi := (282031027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703119315421 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(703119315421 / 400000000000) = 1/(100000000000 / 703119315421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1950356413 / 1000000000) (30474319 / 15625000) (Real.log (703119315421 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (703119315421 / 100000000000) = -Real.log (100000000000 / 703119315421) := by
    rw [show ((703119315421 / 100000000000) : ℝ) = ((100000000000 / 703119315421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (981528919 / 500000000) ≤ -Real.log (62500000000 / 445066805943) ∧
    -Real.log (62500000000 / 445066805943) ≤ (1963057841 / 1000000000) := by
  have h := checkLog_sound (w := (195066805943 / 695066805943)) (n := 12)
    (lo := (288381739 / 500000000)) (hi := (576763479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((445066805943 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(445066805943 / 250000000000) = 1/(62500000000 / 445066805943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (981528919 / 500000000) (1963057841 / 1000000000) (Real.log (445066805943 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (445066805943 / 62500000000) = -Real.log (62500000000 / 445066805943) := by
    rw [show ((445066805943 / 62500000000) : ℝ) = ((62500000000 / 445066805943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (73609491 / 50000000) ≤ -Real.log (250000000000 / 1089692406623) ∧
    -Real.log (250000000000 / 1089692406623) ≤ (1472189823 / 1000000000) := by
  have h := checkLog_sound (w := (89692406623 / 2089692406623)) (n := 12)
    (lo := (4294773 / 50000000)) (hi := (85895461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089692406623 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1089692406623 / 1000000000000) = 1/(250000000000 / 1089692406623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (73609491 / 50000000) (1472189823 / 1000000000) (Real.log (1089692406623 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1089692406623 / 250000000000) = -Real.log (250000000000 / 1089692406623) := by
    rw [show ((1089692406623 / 250000000000) : ℝ) = ((250000000000 / 1089692406623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1482318359 / 1000000000) ≤ -Real.log (125000000000 / 550392740879) ∧
    -Real.log (125000000000 / 550392740879) ≤ (741159181 / 500000000) := by
  have h := checkLog_sound (w := (50392740879 / 1050392740879)) (n := 12)
    (lo := (96023999 / 1000000000)) (hi := (12003 / 125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((550392740879 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(550392740879 / 500000000000) = 1/(125000000000 / 550392740879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1482318359 / 1000000000) (741159181 / 500000000) (Real.log (550392740879 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (550392740879 / 125000000000) = -Real.log (125000000000 / 550392740879) := by
    rw [show ((550392740879 / 125000000000) : ℝ) = ((125000000000 / 550392740879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0019

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0020Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0020
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

theorem reflection_log_1_neg : (199204511 / 500000000) ≤ -Real.log (2560 / 3813) ∧
    -Real.log (2560 / 3813) ≤ (398409023 / 1000000000) := by
  have h := checkLog_sound (w := (1253 / 6373)) (n := 12)
    (lo := (199204511 / 500000000)) (hi := (398409023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3813 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3813 / 2560) = 1/(2560 / 3813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (199204511 / 500000000) (398409023 / 1000000000) (Real.log (3813 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3813 / 2560) = -Real.log (2560 / 3813) := by
    rw [show ((3813 / 2560) : ℝ) = ((2560 / 3813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (672272823 / 1000000000) ≤ -Real.log (1307 / 2560) ∧
    -Real.log (1307 / 2560) ≤ (84034103 / 125000000) := by
  have h := checkLog_sound (w := (1253 / 3867)) (n := 12)
    (lo := (672272823 / 1000000000)) (hi := (84034103 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1307) = 1/(1307 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-84034103 / 125000000) (-672272823 / 1000000000) (Real.log (1307 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (39762193 / 100000000) ≤ -Real.log (256 / 381) ∧
    -Real.log (256 / 381) ≤ (397621931 / 1000000000) := by
  have h := checkLog_sound (w := (125 / 637)) (n := 12)
    (lo := (39762193 / 100000000)) (hi := (397621931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381 / 256) = 1/(256 / 381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (39762193 / 100000000) (397621931 / 1000000000) (Real.log (381 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (381 / 256) = -Real.log (256 / 381) := by
    rw [show ((381 / 256) : ℝ) = ((256 / 381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (669980121 / 1000000000) ≤ -Real.log (131 / 256) ∧
    -Real.log (131 / 256) ≤ (334990061 / 500000000) := by
  have h := checkLog_sound (w := (125 / 387)) (n := 12)
    (lo := (669980121 / 1000000000)) (hi := (334990061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 131) = 1/(131 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-334990061 / 500000000) (-669980121 / 1000000000) (Real.log (131 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (682544293 / 1000000000) ≤ -Real.log (1280 / 2533) ∧
    -Real.log (1280 / 2533) ≤ (341272147 / 500000000) := by
  have h := checkLog_sound (w := (1253 / 3813)) (n := 12)
    (lo := (682544293 / 1000000000)) (hi := (341272147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2533 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2533 / 1280) = 1/(1280 / 2533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (682544293 / 1000000000) (341272147 / 500000000) (Real.log (2533 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2533 / 1280) = -Real.log (1280 / 2533) := by
    rw [show ((2533 / 1280) : ℝ) = ((1280 / 2533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (482347311 / 125000000) ≤ -Real.log (27 / 1280) ∧
    -Real.log (27 / 1280) ≤ (1929389247 / 500000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(40 / 27) = 1/(27 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1929389247 / 500000000) (-482347311 / 125000000) (Real.log (27 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (85169903 / 125000000) ≤ -Real.log (128 / 253) ∧
    -Real.log (128 / 253) ≤ (27254369 / 40000000) := by
  have h := checkLog_sound (w := (125 / 381)) (n := 12)
    (lo := (85169903 / 125000000)) (hi := (27254369 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((253 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(253 / 128) = 1/(128 / 253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (85169903 / 125000000) (27254369 / 40000000) (Real.log (253 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (253 / 128) = -Real.log (128 / 253) := by
    rw [show ((253 / 128) : ℝ) = ((128 / 253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (938354493 / 250000000) ≤ -Real.log (3 / 128) ∧
    -Real.log (3 / 128) ≤ (1876708989 / 500000000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4 / 3) = 1/(3 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1876708989 / 500000000) (-938354493 / 250000000) (Real.log (3 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (558625011 / 1000000000) ≤ -Real.log (1000000 / 1748267) ∧
    -Real.log (1000000 / 1748267) ≤ (139656253 / 250000000) := by
  have h := checkLog_sound (w := (748267 / 2748267)) (n := 12)
    (lo := (558625011 / 1000000000)) (hi := (139656253 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1748267 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1748267 / 1000000) = 1/(1000000 / 1748267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (558625011 / 1000000000) (139656253 / 250000000) (Real.log (1748267 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1748267 / 1000000) = -Real.log (1000000 / 1748267) := by
    rw [show ((1748267 / 1000000) : ℝ) = ((1000000 / 1748267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (344846569 / 250000000) ≤ -Real.log (251733 / 1000000) ∧
    -Real.log (251733 / 1000000) ≤ (689693139 / 500000000) := by
  have h := checkLog_sound (w := (248267 / 751733)) (n := 12)
    (lo := (85779887 / 125000000)) (hi := (686239097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 251733) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 251733) = 1/(251733 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-689693139 / 500000000) (-344846569 / 250000000) (Real.log (251733 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (280085531 / 500000000) ≤ -Real.log (250000 / 437743) ∧
    -Real.log (250000 / 437743) ≤ (560171063 / 1000000000) := by
  have h := checkLog_sound (w := (187743 / 687743)) (n := 12)
    (lo := (280085531 / 500000000)) (hi := (560171063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((437743 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(437743 / 250000) = 1/(250000 / 437743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (280085531 / 500000000) (560171063 / 1000000000) (Real.log (437743 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (437743 / 250000) = -Real.log (250000 / 437743) := by
    rw [show ((437743 / 250000) : ℝ) = ((250000 / 437743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1390189937 / 1000000000) ≤ -Real.log (62257 / 250000) ∧
    -Real.log (62257 / 250000) ≤ (69509497 / 50000000) := by
  have h := checkLog_sound (w := (243 / 124757)) (n := 12)
    (lo := (3895577 / 1000000000)) (hi := (1947789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62257) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(62500 / 62257) = 1/(62257 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-69509497 / 50000000) (-1390189937 / 1000000000) (Real.log (62257 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (121188883 / 250000000) ≤ -Real.log (500000 / 811889) ∧
    -Real.log (500000 / 811889) ≤ (484755533 / 1000000000) := by
  have h := checkLog_sound (w := (311889 / 1311889)) (n := 12)
    (lo := (121188883 / 250000000)) (hi := (484755533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((811889 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(811889 / 500000) = 1/(500000 / 811889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (121188883 / 250000000) (484755533 / 1000000000) (Real.log (811889 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (811889 / 500000) = -Real.log (500000 / 811889) := by
    rw [show ((811889 / 500000) : ℝ) = ((500000 / 811889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (977575883 / 1000000000) ≤ -Real.log (188111 / 500000) ∧
    -Real.log (188111 / 500000) ≤ (195515177 / 200000000) := by
  have h := checkLog_sound (w := (61889 / 438111)) (n := 12)
    (lo := (284428703 / 1000000000)) (hi := (8888397 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 188111) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 188111) = 1/(188111 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-195515177 / 200000000) (-977575883 / 1000000000) (Real.log (188111 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (97320643 / 200000000) ≤ -Real.log (1000000 / 1626781) ∧
    -Real.log (1000000 / 1626781) ≤ (30412701 / 62500000) := by
  have h := checkLog_sound (w := (626781 / 2626781)) (n := 12)
    (lo := (97320643 / 200000000)) (hi := (30412701 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1626781 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1626781 / 1000000) = 1/(1000000 / 1626781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (97320643 / 200000000) (30412701 / 62500000) (Real.log (1626781 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1626781 / 1000000) = -Real.log (1000000 / 1626781) := by
    rw [show ((1626781 / 1000000) : ℝ) = ((1000000 / 1626781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (985589899 / 1000000000) ≤ -Real.log (373219 / 1000000) ∧
    -Real.log (373219 / 1000000) ≤ (985589901 / 1000000000) := by
  have h := checkLog_sound (w := (126781 / 873219)) (n := 12)
    (lo := (292442719 / 1000000000)) (hi := (1827767 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 373219) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 373219) = 1/(373219 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-985589901 / 1000000000) (-985589899 / 1000000000) (Real.log (373219 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1938011287 / 1000000000) ≤ -Real.log (100000000000 / 694492577453) ∧
    -Real.log (100000000000 / 694492577453) ≤ (193801129 / 100000000) := by
  have h := checkLog_sound (w := (294492577453 / 1094492577453)) (n := 12)
    (lo := (551716927 / 1000000000)) (hi := (8620577 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694492577453 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(694492577453 / 400000000000) = 1/(100000000000 / 694492577453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1938011287 / 1000000000) (193801129 / 100000000) (Real.log (694492577453 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (694492577453 / 100000000000) = -Real.log (100000000000 / 694492577453) := by
    rw [show ((694492577453 / 100000000000) : ℝ) = ((100000000000 / 694492577453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1950361 / 1000000) ≤ -Real.log (500000000000 / 3515612702187) ∧
    -Real.log (500000000000 / 3515612702187) ≤ (1950361003 / 1000000000) := by
  have h := checkLog_sound (w := (1515612702187 / 5515612702187)) (n := 12)
    (lo := (7050833 / 12500000)) (hi := (564066641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3515612702187 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3515612702187 / 2000000000000) = 1/(500000000000 / 3515612702187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1950361 / 1000000) (1950361003 / 1000000000) (Real.log (3515612702187 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3515612702187 / 500000000000) = -Real.log (500000000000 / 3515612702187) := by
    rw [show ((3515612702187 / 500000000000) : ℝ) = ((500000000000 / 3515612702187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (182791427 / 125000000) ≤ -Real.log (500000000000 / 2158005114001) ∧
    -Real.log (500000000000 / 2158005114001) ≤ (1462331419 / 1000000000) := by
  have h := checkLog_sound (w := (158005114001 / 4158005114001)) (n := 12)
    (lo := (1188079 / 15625000)) (hi := (76037057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2158005114001 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2158005114001 / 2000000000000) = 1/(500000000000 / 2158005114001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (182791427 / 125000000) (1462331419 / 1000000000) (Real.log (2158005114001 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2158005114001 / 500000000000) = -Real.log (500000000000 / 2158005114001) := by
    rw [show ((2158005114001 / 500000000000) : ℝ) = ((500000000000 / 2158005114001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (736096557 / 500000000) ≤ -Real.log (50000000000 / 217939199237) ∧
    -Real.log (50000000000 / 217939199237) ≤ (1472193117 / 1000000000) := by
  have h := checkLog_sound (w := (17939199237 / 417939199237)) (n := 12)
    (lo := (42949377 / 500000000)) (hi := (17179751 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217939199237 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(217939199237 / 200000000000) = 1/(50000000000 / 217939199237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (736096557 / 500000000) (1472193117 / 1000000000) (Real.log (217939199237 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (217939199237 / 50000000000) = -Real.log (50000000000 / 217939199237) := by
    rw [show ((217939199237 / 50000000000) : ℝ) = ((50000000000 / 217939199237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0020

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0021Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0021
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

theorem reflection_log_1_neg : (39762193 / 100000000) ≤ -Real.log (256 / 381) ∧
    -Real.log (256 / 381) ≤ (397621931 / 1000000000) := by
  have h := checkLog_sound (w := (125 / 637)) (n := 12)
    (lo := (39762193 / 100000000)) (hi := (397621931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381 / 256) = 1/(256 / 381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (39762193 / 100000000) (397621931 / 1000000000) (Real.log (381 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (381 / 256) = -Real.log (256 / 381) := by
    rw [show ((381 / 256) : ℝ) = ((256 / 381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (669980121 / 1000000000) ≤ -Real.log (131 / 256) ∧
    -Real.log (131 / 256) ≤ (334990061 / 500000000) := by
  have h := checkLog_sound (w := (125 / 387)) (n := 12)
    (lo := (669980121 / 1000000000)) (hi := (334990061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 131) = 1/(131 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-334990061 / 500000000) (-669980121 / 1000000000) (Real.log (131 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (198417109 / 500000000) ≤ -Real.log (2560 / 3807) ∧
    -Real.log (2560 / 3807) ≤ (396834219 / 1000000000) := by
  have h := checkLog_sound (w := (1247 / 6367)) (n := 12)
    (lo := (198417109 / 500000000)) (hi := (396834219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3807 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3807 / 2560) = 1/(2560 / 3807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (198417109 / 500000000) (396834219 / 1000000000) (Real.log (3807 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3807 / 2560) = -Real.log (2560 / 3807) := by
    rw [show ((3807 / 2560) : ℝ) = ((2560 / 3807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (667692663 / 1000000000) ≤ -Real.log (1313 / 2560) ∧
    -Real.log (1313 / 2560) ≤ (83461583 / 125000000) := by
  have h := checkLog_sound (w := (1247 / 3873)) (n := 12)
    (lo := (667692663 / 1000000000)) (hi := (83461583 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1313) = 1/(1313 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-83461583 / 125000000) (-667692663 / 1000000000) (Real.log (1313 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (85169903 / 125000000) ≤ -Real.log (128 / 253) ∧
    -Real.log (128 / 253) ≤ (27254369 / 40000000) := by
  have h := checkLog_sound (w := (125 / 381)) (n := 12)
    (lo := (85169903 / 125000000)) (hi := (27254369 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((253 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(253 / 128) = 1/(128 / 253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (85169903 / 125000000) (27254369 / 40000000) (Real.log (253 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (253 / 128) = -Real.log (128 / 253) := by
    rw [show ((253 / 128) : ℝ) = ((128 / 253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (938354493 / 250000000) ≤ -Real.log (3 / 128) ∧
    -Real.log (3 / 128) ≤ (1876708989 / 500000000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4 / 3) = 1/(3 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1876708989 / 500000000) (-938354493 / 250000000) (Real.log (3 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (2720691 / 4000000) ≤ -Real.log (1280 / 2527) ∧
    -Real.log (1280 / 2527) ≤ (680172751 / 1000000000) := by
  have h := checkLog_sound (w := (1247 / 3807)) (n := 12)
    (lo := (2720691 / 4000000)) (hi := (680172751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2527 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2527 / 1280) = 1/(1280 / 2527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (2720691 / 4000000) (680172751 / 1000000000) (Real.log (2527 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2527 / 1280) = -Real.log (1280 / 2527) := by
    rw [show ((2527 / 1280) : ℝ) = ((1280 / 2527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (228631737 / 62500000) ≤ -Real.log (33 / 1280) ∧
    -Real.log (33 / 1280) ≤ (1829053899 / 500000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(40 / 33) = 1/(33 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1829053899 / 500000000) (-228631737 / 62500000) (Real.log (33 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (278551173 / 500000000) ≤ -Real.log (1000000 / 1745607) ∧
    -Real.log (1000000 / 1745607) ≤ (557102347 / 1000000000) := by
  have h := checkLog_sound (w := (745607 / 2745607)) (n := 12)
    (lo := (278551173 / 500000000)) (hi := (557102347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1745607 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1745607 / 1000000) = 1/(1000000 / 1745607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (278551173 / 500000000) (557102347 / 1000000000) (Real.log (1745607 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1745607 / 1000000) = -Real.log (1000000 / 1745607) := by
    rw [show ((1745607 / 1000000) : ℝ) = ((1000000 / 1745607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1368874963 / 1000000000) ≤ -Real.log (254393 / 1000000) ∧
    -Real.log (254393 / 1000000) ≤ (273774993 / 200000000) := by
  have h := checkLog_sound (w := (245607 / 754393)) (n := 12)
    (lo := (675727783 / 1000000000)) (hi := (84465973 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 254393) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 254393) = 1/(254393 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-273774993 / 200000000) (-1368874963 / 1000000000) (Real.log (254393 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (558625583 / 1000000000) ≤ -Real.log (250000 / 437067) ∧
    -Real.log (250000 / 437067) ≤ (34914099 / 62500000) := by
  have h := checkLog_sound (w := (187067 / 687067)) (n := 12)
    (lo := (558625583 / 1000000000)) (hi := (34914099 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((437067 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(437067 / 250000) = 1/(250000 / 437067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (558625583 / 1000000000) (34914099 / 62500000) (Real.log (437067 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (437067 / 250000) = -Real.log (250000 / 437067) := by
    rw [show ((437067 / 250000) : ℝ) = ((250000 / 437067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (172423781 / 125000000) ≤ -Real.log (62933 / 250000) ∧
    -Real.log (62933 / 250000) ≤ (5517561 / 4000000) := by
  have h := checkLog_sound (w := (62067 / 187933)) (n := 12)
    (lo := (171560767 / 250000000)) (hi := (686243069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 62933) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 62933) = 1/(62933 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-5517561 / 4000000) (-172423781 / 125000000) (Real.log (62933 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (482938363 / 1000000000) ≤ -Real.log (100000 / 162083) ∧
    -Real.log (100000 / 162083) ≤ (120734591 / 250000000) := by
  have h := checkLog_sound (w := (62083 / 262083)) (n := 12)
    (lo := (482938363 / 1000000000)) (hi := (120734591 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162083 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162083 / 100000) = 1/(100000 / 162083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (482938363 / 1000000000) (120734591 / 250000000) (Real.log (162083 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (162083 / 100000) = -Real.log (100000 / 162083) := by
    rw [show ((162083 / 100000) : ℝ) = ((100000 / 162083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1551633 / 1600000) ≤ -Real.log (37917 / 100000) ∧
    -Real.log (37917 / 100000) ≤ (969770627 / 1000000000) := by
  have h := checkLog_sound (w := (12083 / 87917)) (n := 12)
    (lo := (55324689 / 200000000)) (hi := (138311723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 37917) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 37917) = 1/(37917 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-969770627 / 1000000000) (-1551633 / 1600000) (Real.log (37917 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (121189037 / 250000000) ≤ -Real.log (1000000 / 1623779) ∧
    -Real.log (1000000 / 1623779) ≤ (484756149 / 1000000000) := by
  have h := checkLog_sound (w := (623779 / 2623779)) (n := 12)
    (lo := (121189037 / 250000000)) (hi := (484756149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1623779 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1623779 / 1000000) = 1/(1000000 / 1623779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (121189037 / 250000000) (484756149 / 1000000000) (Real.log (1623779 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1623779 / 1000000) = -Real.log (1000000 / 1623779) := by
    rw [show ((1623779 / 1000000) : ℝ) = ((1000000 / 1623779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (977578541 / 1000000000) ≤ -Real.log (376221 / 1000000) ∧
    -Real.log (376221 / 1000000) ≤ (977578543 / 1000000000) := by
  have h := checkLog_sound (w := (123779 / 876221)) (n := 12)
    (lo := (284431361 / 1000000000)) (hi := (142215681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 376221) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 376221) = 1/(376221 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-977578543 / 1000000000) (-977578541 / 1000000000) (Real.log (376221 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (481494327 / 250000000) ≤ -Real.log (62500000000 / 428865721541) ∧
    -Real.log (62500000000 / 428865721541) ≤ (1925977311 / 1000000000) := by
  have h := checkLog_sound (w := (178865721541 / 678865721541)) (n := 12)
    (lo := (134920737 / 250000000)) (hi := (539682949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((428865721541 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(428865721541 / 250000000000) = 1/(62500000000 / 428865721541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (481494327 / 250000000) (1925977311 / 1000000000) (Real.log (428865721541 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (428865721541 / 62500000000) = -Real.log (62500000000 / 428865721541) := by
    rw [show ((428865721541 / 62500000000) : ℝ) = ((62500000000 / 428865721541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1938015831 / 1000000000) ≤ -Real.log (50000000000 / 347247866779) ∧
    -Real.log (50000000000 / 347247866779) ≤ (969007917 / 500000000) := by
  have h := checkLog_sound (w := (147247866779 / 547247866779)) (n := 12)
    (lo := (551721471 / 1000000000)) (hi := (1077581 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347247866779 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(347247866779 / 200000000000) = 1/(50000000000 / 347247866779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1938015831 / 1000000000) (969007917 / 500000000) (Real.log (347247866779 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (347247866779 / 50000000000) = -Real.log (50000000000 / 347247866779) := by
    rw [show ((347247866779 / 50000000000) : ℝ) = ((50000000000 / 347247866779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (363177247 / 250000000) ≤ -Real.log (12500000000 / 53433486299) ∧
    -Real.log (12500000000 / 53433486299) ≤ (1452708991 / 1000000000) := by
  have h := checkLog_sound (w := (3433486299 / 103433486299)) (n := 12)
    (lo := (16603657 / 250000000)) (hi := (66414629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53433486299 / 50000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(53433486299 / 50000000000) = 1/(12500000000 / 53433486299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (363177247 / 250000000) (1452708991 / 1000000000) (Real.log (53433486299 / 12500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (53433486299 / 12500000000) = -Real.log (12500000000 / 53433486299) := by
    rw [show ((53433486299 / 12500000000) : ℝ) = ((12500000000 / 53433486299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1462334689 / 1000000000) ≤ -Real.log (125000000000 / 539503044753) ∧
    -Real.log (125000000000 / 539503044753) ≤ (365583673 / 250000000) := by
  have h := checkLog_sound (w := (39503044753 / 1039503044753)) (n := 12)
    (lo := (76040329 / 1000000000)) (hi := (7604033 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539503044753 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(539503044753 / 500000000000) = 1/(125000000000 / 539503044753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1462334689 / 1000000000) (365583673 / 250000000) (Real.log (539503044753 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (539503044753 / 125000000000) = -Real.log (125000000000 / 539503044753) := by
    rw [show ((539503044753 / 125000000000) : ℝ) = ((125000000000 / 539503044753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0021

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0022Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0022
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

theorem reflection_log_1_neg : (198417109 / 500000000) ≤ -Real.log (2560 / 3807) ∧
    -Real.log (2560 / 3807) ≤ (396834219 / 1000000000) := by
  have h := checkLog_sound (w := (1247 / 6367)) (n := 12)
    (lo := (198417109 / 500000000)) (hi := (396834219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3807 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3807 / 2560) = 1/(2560 / 3807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (198417109 / 500000000) (396834219 / 1000000000) (Real.log (3807 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3807 / 2560) = -Real.log (2560 / 3807) := by
    rw [show ((3807 / 2560) : ℝ) = ((2560 / 3807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (667692663 / 1000000000) ≤ -Real.log (1313 / 2560) ∧
    -Real.log (1313 / 2560) ≤ (83461583 / 125000000) := by
  have h := checkLog_sound (w := (1247 / 3873)) (n := 12)
    (lo := (667692663 / 1000000000)) (hi := (83461583 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1313) = 1/(1313 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-83461583 / 125000000) (-667692663 / 1000000000) (Real.log (1313 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (198022943 / 500000000) ≤ -Real.log (640 / 951) ∧
    -Real.log (640 / 951) ≤ (396045887 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 1591)) (n := 12)
    (lo := (198022943 / 500000000)) (hi := (396045887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((951 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(951 / 640) = 1/(640 / 951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (198022943 / 500000000) (396045887 / 1000000000) (Real.log (951 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (951 / 640) = -Real.log (640 / 951) := by
    rw [show ((951 / 640) : ℝ) = ((640 / 951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (26616417 / 40000000) ≤ -Real.log (329 / 640) ∧
    -Real.log (329 / 640) ≤ (332705213 / 500000000) := by
  have h := checkLog_sound (w := (311 / 969)) (n := 12)
    (lo := (26616417 / 40000000)) (hi := (332705213 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 329) = 1/(329 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-332705213 / 500000000) (-26616417 / 40000000) (Real.log (329 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (2720691 / 4000000) ≤ -Real.log (1280 / 2527) ∧
    -Real.log (1280 / 2527) ≤ (680172751 / 1000000000) := by
  have h := checkLog_sound (w := (1247 / 3807)) (n := 12)
    (lo := (2720691 / 4000000)) (hi := (680172751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2527 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2527 / 1280) = 1/(1280 / 2527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (2720691 / 4000000) (680172751 / 1000000000) (Real.log (2527 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2527 / 1280) = -Real.log (1280 / 2527) := by
    rw [show ((2527 / 1280) : ℝ) = ((1280 / 2527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (228631737 / 62500000) ≤ -Real.log (33 / 1280) ∧
    -Real.log (33 / 1280) ≤ (1829053899 / 500000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(40 / 33) = 1/(33 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1829053899 / 500000000) (-228631737 / 62500000) (Real.log (33 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (339492433 / 500000000) ≤ -Real.log (320 / 631) ∧
    -Real.log (320 / 631) ≤ (678984867 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 951)) (n := 12)
    (lo := (339492433 / 500000000)) (hi := (678984867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((631 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(631 / 320) = 1/(320 / 631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (339492433 / 500000000) (678984867 / 1000000000) (Real.log (631 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (631 / 320) = -Real.log (320 / 631) := by
    rw [show ((631 / 320) : ℝ) = ((320 / 631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (714219283 / 200000000) ≤ -Real.log (9 / 320) ∧
    -Real.log (9 / 320) ≤ (3571096421 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(10 / 9) = 1/(9 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3571096421 / 1000000000) (-714219283 / 200000000) (Real.log (9 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (277799867 / 500000000) ≤ -Real.log (500000 / 871493) ∧
    -Real.log (500000 / 871493) ≤ (111119947 / 200000000) := by
  have h := checkLog_sound (w := (371493 / 1371493)) (n := 12)
    (lo := (277799867 / 500000000)) (hi := (111119947 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((871493 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(871493 / 500000) = 1/(500000 / 871493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (277799867 / 500000000) (111119947 / 200000000) (Real.log (871493 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (871493 / 500000) = -Real.log (500000 / 871493) := by
    rw [show ((871493 / 500000) : ℝ) = ((500000 / 871493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (16982809 / 12500000) ≤ -Real.log (128507 / 500000) ∧
    -Real.log (128507 / 500000) ≤ (679312361 / 500000000) := by
  have h := checkLog_sound (w := (121493 / 378507)) (n := 12)
    (lo := (33273877 / 50000000)) (hi := (665477541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 128507) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 128507) = 1/(128507 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-679312361 / 500000000) (-16982809 / 12500000) (Real.log (128507 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (557102919 / 1000000000) ≤ -Real.log (125000 / 218201) ∧
    -Real.log (125000 / 218201) ≤ (13927573 / 25000000) := by
  have h := checkLog_sound (w := (93201 / 343201)) (n := 12)
    (lo := (557102919 / 1000000000)) (hi := (13927573 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218201 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218201 / 125000) = 1/(125000 / 218201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (557102919 / 1000000000) (13927573 / 25000000) (Real.log (218201 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (218201 / 125000) = -Real.log (125000 / 218201) := by
    rw [show ((218201 / 125000) : ℝ) = ((125000 / 218201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1368878893 / 1000000000) ≤ -Real.log (31799 / 125000) ∧
    -Real.log (31799 / 125000) ≤ (273775779 / 200000000) := by
  have h := checkLog_sound (w := (30701 / 94299)) (n := 12)
    (lo := (675731713 / 1000000000)) (hi := (337865857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 31799) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 31799) = 1/(31799 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-273775779 / 200000000) (-1368878893 / 1000000000) (Real.log (31799 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (48114879 / 100000000) ≤ -Real.log (250000 / 404483) ∧
    -Real.log (250000 / 404483) ≤ (481148791 / 1000000000) := by
  have h := checkLog_sound (w := (154483 / 654483)) (n := 12)
    (lo := (48114879 / 100000000)) (hi := (481148791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((404483 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(404483 / 250000) = 1/(250000 / 404483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (48114879 / 100000000) (481148791 / 1000000000) (Real.log (404483 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (404483 / 250000) = -Real.log (250000 / 404483) := by
    rw [show ((404483 / 250000) : ℝ) = ((250000 / 404483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (38486267 / 40000000) ≤ -Real.log (95517 / 250000) ∧
    -Real.log (95517 / 250000) ≤ (962156677 / 1000000000) := by
  have h := checkLog_sound (w := (29483 / 220517)) (n := 12)
    (lo := (53801899 / 200000000)) (hi := (33626187 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 95517) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 95517) = 1/(95517 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-962156677 / 1000000000) (-38486267 / 40000000) (Real.log (95517 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (24146949 / 50000000) ≤ -Real.log (1000000 / 1620831) ∧
    -Real.log (1000000 / 1620831) ≤ (482938981 / 1000000000) := by
  have h := checkLog_sound (w := (620831 / 2620831)) (n := 12)
    (lo := (24146949 / 50000000)) (hi := (482938981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1620831 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1620831 / 1000000) = 1/(1000000 / 1620831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (24146949 / 50000000) (482938981 / 1000000000) (Real.log (1620831 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1620831 / 1000000) = -Real.log (1000000 / 1620831) := by
    rw [show ((1620831 / 1000000) : ℝ) = ((1000000 / 1620831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (484886631 / 500000000) ≤ -Real.log (379169 / 1000000) ∧
    -Real.log (379169 / 1000000) ≤ (60610829 / 62500000) := by
  have h := checkLog_sound (w := (120831 / 879169)) (n := 12)
    (lo := (138313041 / 500000000)) (hi := (276626083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 379169) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 379169) = 1/(379169 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-60610829 / 62500000) (-484886631 / 500000000) (Real.log (379169 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (957112227 / 500000000) ≤ -Real.log (250000000000 / 1695419315679) ∧
    -Real.log (250000000000 / 1695419315679) ≤ (1914224457 / 1000000000) := by
  have h := checkLog_sound (w := (695419315679 / 2695419315679)) (n := 12)
    (lo := (263965047 / 500000000)) (hi := (105586019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1695419315679 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1695419315679 / 1000000000000) = 1/(250000000000 / 1695419315679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (957112227 / 500000000) (1914224457 / 1000000000) (Real.log (1695419315679 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1695419315679 / 250000000000) = -Real.log (250000000000 / 1695419315679) := by
    rw [show ((1695419315679 / 250000000000) : ℝ) = ((250000000000 / 1695419315679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (481495453 / 250000000) ≤ -Real.log (500000000000 / 3430941224567) ∧
    -Real.log (500000000000 / 3430941224567) ≤ (385196363 / 200000000) := by
  have h := checkLog_sound (w := (1430941224567 / 5430941224567)) (n := 12)
    (lo := (134921863 / 250000000)) (hi := (539687453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3430941224567 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3430941224567 / 2000000000000) = 1/(500000000000 / 3430941224567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (481495453 / 250000000) (385196363 / 200000000) (Real.log (3430941224567 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3430941224567 / 500000000000) = -Real.log (500000000000 / 3430941224567) := by
    rw [show ((3430941224567 / 500000000000) : ℝ) = ((500000000000 / 3430941224567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (288661093 / 200000000) ≤ -Real.log (500000000000 / 2117335134059) ∧
    -Real.log (500000000000 / 2117335134059) ≤ (360826367 / 250000000) := by
  have h := checkLog_sound (w := (117335134059 / 4117335134059)) (n := 12)
    (lo := (11402221 / 200000000)) (hi := (28505553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2117335134059 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2117335134059 / 2000000000000) = 1/(500000000000 / 2117335134059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (288661093 / 200000000) (360826367 / 250000000) (Real.log (2117335134059 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2117335134059 / 500000000000) = -Real.log (500000000000 / 2117335134059) := by
    rw [show ((2117335134059 / 500000000000) : ℝ) = ((500000000000 / 2117335134059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (726356121 / 500000000) ≤ -Real.log (500000000000 / 2137346407539) ∧
    -Real.log (500000000000 / 2137346407539) ≤ (290542449 / 200000000) := by
  have h := checkLog_sound (w := (137346407539 / 4137346407539)) (n := 12)
    (lo := (33208941 / 500000000)) (hi := (66417883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2137346407539 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2137346407539 / 2000000000000) = 1/(500000000000 / 2137346407539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (726356121 / 500000000) (290542449 / 200000000) (Real.log (2137346407539 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2137346407539 / 500000000000) = -Real.log (500000000000 / 2137346407539) := by
    rw [show ((2137346407539 / 500000000000) : ℝ) = ((500000000000 / 2137346407539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0022

end


