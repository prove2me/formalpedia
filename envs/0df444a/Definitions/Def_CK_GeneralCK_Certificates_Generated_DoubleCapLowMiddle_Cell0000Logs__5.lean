-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0000Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0000Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:54:20.758418+00:00
-- url     : https://prove2.me/theorems/8490db31-087f-4f4a-80be-1efac82abba9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0000Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0001Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0000Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0001Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0002Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0003Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0004Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0000Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0001Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0002Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0003Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0004Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0000Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0001Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0002Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0003Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0004Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0000Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0001Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0002Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0003Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0004Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0000Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0000
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

theorem reflection_log_1_neg : (170774211 / 250000000) ≤ -Real.log (50 / 99) ∧
    -Real.log (50 / 99) ≤ (136619369 / 200000000) := by
  have h := checkLog_sound (w := (49 / 149)) (n := 12)
    (lo := (170774211 / 250000000)) (hi := (136619369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99 / 50) = 1/(50 / 99) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (170774211 / 250000000) (136619369 / 200000000) (Real.log (99 / 50)) := by
  have h := reflection_log_1_neg
  have he : Real.log (99 / 50) = -Real.log (50 / 99) := by
    rw [show ((99 / 50) : ℝ) = ((50 / 99) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1956011501 / 500000000) ≤ -Real.log (1 / 50) ∧
    -Real.log (1 / 50) ≤ (122250719 / 31250000) := by
  have h := checkLog_sound (w := (9 / 41)) (n := 12)
    (lo := (223143551 / 500000000)) (hi := (446287103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 16) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(25 / 16) = 1/(1 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-122250719 / 31250000) (-1956011501 / 500000000) (Real.log (1 / 50)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (170762497 / 250000000) ≤ -Real.log (500000000000 / 989953613281) ∧
    -Real.log (500000000000 / 989953613281) ≤ (683049989 / 1000000000) := by
  have h := checkLog_sound (w := (489953613281 / 1489953613281)) (n := 12)
    (lo := (170762497 / 250000000)) (hi := (683049989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989953613281 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989953613281 / 500000000000) = 1/(500000000000 / 989953613281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (170762497 / 250000000) (683049989 / 1000000000) (Real.log (989953613281 / 500000000000)) := by
  have h := reflection_log_3_neg
  have he : Real.log (989953613281 / 500000000000) = -Real.log (500000000000 / 989953613281) := by
    rw [show ((989953613281 / 500000000000) : ℝ) = ((500000000000 / 989953613281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (244212191 / 62500000) ≤ -Real.log (10046386719 / 500000000000) ∧
    -Real.log (10046386719 / 500000000000) ≤ (1953697531 / 500000000) := by
  have h := checkLog_sound (w := (5578613281 / 25671386719)) (n := 12)
    (lo := (110414789 / 250000000)) (hi := (441659157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 10046386719) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625000000 / 10046386719) = 1/(10046386719 / 500000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1953697531 / 500000000) (-244212191 / 62500000) (Real.log (10046386719 / 500000000000)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (672944473 / 1000000000) ≤ -Real.log (25 / 49) ∧
    -Real.log (25 / 49) ≤ (336472237 / 500000000) := by
  have h := checkLog_sound (w := (12 / 37)) (n := 12)
    (lo := (672944473 / 1000000000)) (hi := (336472237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49 / 25) = 1/(25 / 49) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (672944473 / 1000000000) (336472237 / 500000000) (Real.log (49 / 25)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49 / 25) = -Real.log (25 / 49) := by
    rw [show ((49 / 25) : ℝ) = ((25 / 49) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1609437911 / 500000000) ≤ -Real.log (1 / 25) ∧
    -Real.log (1 / 25) ≤ (3218875827 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 41)) (n := 12)
    (lo := (223143551 / 500000000)) (hi := (446287103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 16) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(25 / 16) = 1/(1 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3218875827 / 1000000000) (-1609437911 / 500000000) (Real.log (1 / 25)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (672849801 / 1000000000) ≤ -Real.log (20480 / 40137) ∧
    -Real.log (20480 / 40137) ≤ (336424901 / 500000000) := by
  have h := checkLog_sound (w := (19657 / 60617)) (n := 12)
    (lo := (672849801 / 1000000000)) (hi := (336424901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40137 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40137 / 20480) = 1/(20480 / 40137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (672849801 / 1000000000) (336424901 / 500000000) (Real.log (40137 / 20480)) := by
  have h := reflection_log_7_neg
  have he : Real.log (40137 / 20480) = -Real.log (20480 / 40137) := by
    rw [show ((40137 / 20480) : ℝ) = ((20480 / 40137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (803561969 / 250000000) ≤ -Real.log (823 / 20480) ∧
    -Real.log (823 / 20480) ≤ (3214247881 / 1000000000) := by
  have h := checkLog_sound (w := (457 / 2103)) (n := 12)
    (lo := (110414789 / 250000000)) (hi := (441659157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 823) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1280 / 823) = 1/(823 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3214247881 / 1000000000) (-803561969 / 250000000) (Real.log (823 / 20480)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (684565967 / 1000000000) ≤ -Real.log (1000000 / 1982911) ∧
    -Real.log (1000000 / 1982911) ≤ (42785373 / 62500000) := by
  have h := checkLog_sound (w := (982911 / 2982911)) (n := 12)
    (lo := (684565967 / 1000000000)) (hi := (42785373 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982911 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982911 / 1000000) = 1/(1000000 / 1982911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (684565967 / 1000000000) (42785373 / 62500000) (Real.log (1982911 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1982911 / 1000000) = -Real.log (1000000 / 1982911) := by
    rw [show ((1982911 / 1000000) : ℝ) = ((1000000 / 1982911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2034660147 / 500000000) ≤ -Real.log (17089 / 1000000) ∧
    -Real.log (17089 / 1000000) ≤ (40693203 / 10000000) := by
  have h := checkLog_sound (w := (14161 / 48339)) (n := 12)
    (lo := (301792197 / 500000000)) (hi := (120716879 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17089) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17089) = 1/(17089 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-40693203 / 10000000) (-2034660147 / 500000000) (Real.log (17089 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (342302399 / 500000000) ≤ -Real.log (250000 / 495747) ∧
    -Real.log (250000 / 495747) ≤ (684604799 / 1000000000) := by
  have h := checkLog_sound (w := (245747 / 745747)) (n := 12)
    (lo := (342302399 / 500000000)) (hi := (684604799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((495747 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(495747 / 250000) = 1/(250000 / 495747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (342302399 / 500000000) (684604799 / 1000000000) (Real.log (495747 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (495747 / 250000) = -Real.log (250000 / 495747) := by
    rw [show ((495747 / 250000) : ℝ) = ((250000 / 495747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2036918149 / 500000000) ≤ -Real.log (4253 / 250000) ∧
    -Real.log (4253 / 250000) ≤ (254614769 / 62500000) := by
  have h := checkLog_sound (w := (7119 / 24131)) (n := 12)
    (lo := (304050199 / 500000000)) (hi := (608100399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8506) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8506) = 1/(4253 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-254614769 / 62500000) (-2036918149 / 500000000) (Real.log (4253 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (684534699 / 1000000000) ≤ -Real.log (1000000 / 1982849) ∧
    -Real.log (1000000 / 1982849) ≤ (6845347 / 10000000) := by
  have h := checkLog_sound (w := (982849 / 2982849)) (n := 12)
    (lo := (684534699 / 1000000000)) (hi := (6845347 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982849 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982849 / 1000000) = 1/(1000000 / 1982849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (684534699 / 1000000000) (6845347 / 10000000) (Real.log (1982849 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1982849 / 1000000) = -Real.log (1000000 / 1982849) := by
    rw [show ((1982849 / 1000000) : ℝ) = ((1000000 / 1982849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (813139759 / 200000000) ≤ -Real.log (17151 / 1000000) ∧
    -Real.log (17151 / 1000000) ≤ (4065698801 / 1000000000) := by
  have h := checkLog_sound (w := (14099 / 48401)) (n := 12)
    (lo := (119992579 / 200000000)) (hi := (37497681 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17151) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17151) = 1/(17151 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-4065698801 / 1000000000) (-813139759 / 200000000) (Real.log (17151 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (684573531 / 1000000000) ≤ -Real.log (500000 / 991463) ∧
    -Real.log (500000 / 991463) ≤ (171143383 / 250000000) := by
  have h := checkLog_sound (w := (491463 / 1491463)) (n := 12)
    (lo := (684573531 / 1000000000)) (hi := (171143383 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991463 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991463 / 500000) = 1/(500000 / 991463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (684573531 / 1000000000) (171143383 / 250000000) (Real.log (991463 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (991463 / 500000) = -Real.log (500000 / 991463) := by
    rw [show ((991463 / 500000) : ℝ) = ((500000 / 991463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (4070198437 / 1000000000) ≤ -Real.log (8537 / 500000) ∧
    -Real.log (8537 / 500000) ≤ (4070198443 / 1000000000) := by
  have h := checkLog_sound (w := (3544 / 12081)) (n := 12)
    (lo := (604462537 / 1000000000)) (hi := (302231269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8537) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8537) = 1/(8537 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-4070198443 / 1000000000) (-4070198437 / 1000000000) (Real.log (8537 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (237694313 / 50000000) ≤ -Real.log (500000000000 / 58017174790801) ∧
    -Real.log (500000000000 / 58017174790801) ≤ (4753886267 / 1000000000) := by
  have h := checkLog_sound (w := (26017174790801 / 90017174790801)) (n := 12)
    (lo := (29750159 / 50000000)) (hi := (595003181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58017174790801 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(58017174790801 / 32000000000000) = 1/(500000000000 / 58017174790801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (237694313 / 50000000) (4753886267 / 1000000000) (Real.log (58017174790801 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (58017174790801 / 500000000000) = -Real.log (500000000000 / 58017174790801) := by
    rw [show ((58017174790801 / 500000000000) : ℝ) = ((500000000000 / 58017174790801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (594805137 / 125000000) ≤ -Real.log (100000000000 / 11656407241947) ∧
    -Real.log (100000000000 / 11656407241947) ≤ (4758441103 / 1000000000) := by
  have h := checkLog_sound (w := (5256407241947 / 18056407241947)) (n := 12)
    (lo := (4684047 / 7812500)) (hi := (599558017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11656407241947 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(11656407241947 / 6400000000000) = 1/(100000000000 / 11656407241947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (594805137 / 125000000) (4758441103 / 1000000000) (Real.log (11656407241947 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (11656407241947 / 100000000000) = -Real.log (100000000000 / 11656407241947) := by
    rw [show ((11656407241947 / 100000000000) : ℝ) = ((100000000000 / 11656407241947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2375116747 / 500000000) ≤ -Real.log (500000000000 / 57805638155209) ∧
    -Real.log (500000000000 / 57805638155209) ≤ (4750233501 / 1000000000) := by
  have h := checkLog_sound (w := (25805638155209 / 89805638155209)) (n := 12)
    (lo := (295675207 / 500000000)) (hi := (118270083 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57805638155209 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(57805638155209 / 32000000000000) = 1/(500000000000 / 57805638155209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2375116747 / 500000000) (4750233501 / 1000000000) (Real.log (57805638155209 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (57805638155209 / 500000000000) = -Real.log (500000000000 / 57805638155209) := by
    rw [show ((57805638155209 / 500000000000) : ℝ) = ((500000000000 / 57805638155209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (9286664 / 1953125) ≤ -Real.log (125000000000 / 14517145952911) ∧
    -Real.log (125000000000 / 14517145952911) ≤ (190190879 / 40000000) := by
  have h := checkLog_sound (w := (6517145952911 / 22517145952911)) (n := 12)
    (lo := (74486111 / 125000000)) (hi := (595888889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14517145952911 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(14517145952911 / 8000000000000) = 1/(125000000000 / 14517145952911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (9286664 / 1953125) (190190879 / 40000000) (Real.log (14517145952911 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (14517145952911 / 125000000000) = -Real.log (125000000000 / 14517145952911) := by
    rw [show ((14517145952911 / 125000000000) : ℝ) = ((125000000000 / 14517145952911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0000

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0001Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0001
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

theorem reflection_log_1_neg : (170762497 / 250000000) ≤ -Real.log (1000000000000 / 1979907226563) ∧
    -Real.log (1000000000000 / 1979907226563) ≤ (683049989 / 1000000000) := by
  have h := checkLog_sound (w := (979907226563 / 2979907226563)) (n := 12)
    (lo := (170762497 / 250000000)) (hi := (683049989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979907226563 / 1000000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979907226563 / 1000000000000) = 1/(1000000000000 / 1979907226563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (170762497 / 250000000) (683049989 / 1000000000) (Real.log (1979907226563 / 1000000000000)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1979907226563 / 1000000000000) = -Real.log (1000000000000 / 1979907226563) := by
    rw [show ((1979907226563 / 1000000000000) : ℝ) = ((1000000000000 / 1979907226563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (244212191 / 62500000) ≤ -Real.log (20092773437 / 1000000000000) ∧
    -Real.log (20092773437 / 1000000000000) ≤ (1953697531 / 500000000) := by
  have h := checkLog_sound (w := (11157226563 / 51342773437)) (n := 12)
    (lo := (110414789 / 250000000)) (hi := (441659157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250000000 / 20092773437) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250000000 / 20092773437) = 1/(20092773437 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1953697531 / 500000000) (-244212191 / 62500000) (Real.log (20092773437 / 1000000000000)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (683003129 / 1000000000) ≤ -Real.log (102400 / 202733) ∧
    -Real.log (102400 / 202733) ≤ (68300313 / 100000000) := by
  have h := checkLog_sound (w := (100333 / 305133)) (n := 12)
    (lo := (683003129 / 1000000000)) (hi := (68300313 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202733 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202733 / 102400) = 1/(102400 / 202733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (683003129 / 1000000000) (68300313 / 100000000) (Real.log (202733 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202733 / 102400) = -Real.log (102400 / 202733) := by
    rw [show ((202733 / 102400) : ℝ) = ((102400 / 202733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3902788429 / 1000000000) ≤ -Real.log (2067 / 102400) ∧
    -Real.log (2067 / 102400) ≤ (780557687 / 200000000) := by
  have h := checkLog_sound (w := (1133 / 5267)) (n := 12)
    (lo := (437052529 / 1000000000)) (hi := (43705253 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2067) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2067) = 1/(2067 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-780557687 / 200000000) (-3902788429 / 1000000000) (Real.log (2067 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (672849801 / 1000000000) ≤ -Real.log (20480 / 40137) ∧
    -Real.log (20480 / 40137) ≤ (336424901 / 500000000) := by
  have h := checkLog_sound (w := (19657 / 60617)) (n := 12)
    (lo := (672849801 / 1000000000)) (hi := (336424901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40137 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40137 / 20480) = 1/(20480 / 40137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (672849801 / 1000000000) (336424901 / 500000000) (Real.log (40137 / 20480)) := by
  have h := reflection_log_5_neg
  have he : Real.log (40137 / 20480) = -Real.log (20480 / 40137) := by
    rw [show ((40137 / 20480) : ℝ) = ((20480 / 40137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (803561969 / 250000000) ≤ -Real.log (823 / 20480) ∧
    -Real.log (823 / 20480) ≤ (3214247881 / 1000000000) := by
  have h := checkLog_sound (w := (457 / 2103)) (n := 12)
    (lo := (110414789 / 250000000)) (hi := (441659157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 823) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1280 / 823) = 1/(823 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3214247881 / 1000000000) (-803561969 / 250000000) (Real.log (823 / 20480)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (672755121 / 1000000000) ≤ -Real.log (51200 / 100333) ∧
    -Real.log (51200 / 100333) ≤ (336377561 / 500000000) := by
  have h := checkLog_sound (w := (49133 / 151533)) (n := 12)
    (lo := (672755121 / 1000000000)) (hi := (336377561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100333 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100333 / 51200) = 1/(51200 / 100333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (672755121 / 1000000000) (336377561 / 500000000) (Real.log (100333 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (100333 / 51200) = -Real.log (51200 / 100333) := by
    rw [show ((100333 / 51200) : ℝ) = ((51200 / 100333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3209641249 / 1000000000) ≤ -Real.log (2067 / 51200) ∧
    -Real.log (2067 / 51200) ≤ (1604820627 / 500000000) := by
  have h := checkLog_sound (w := (1133 / 5267)) (n := 12)
    (lo := (437052529 / 1000000000)) (hi := (43705253 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2067) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2067) = 1/(2067 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1604820627 / 500000000) (-3209641249 / 1000000000) (Real.log (2067 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (342263819 / 500000000) ≤ -Real.log (200000 / 396567) ∧
    -Real.log (200000 / 396567) ≤ (684527639 / 1000000000) := by
  have h := checkLog_sound (w := (196567 / 596567)) (n := 12)
    (lo := (342263819 / 500000000)) (hi := (684527639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((396567 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(396567 / 200000) = 1/(200000 / 396567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (342263819 / 500000000) (684527639 / 1000000000) (Real.log (396567 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (396567 / 200000) = -Real.log (200000 / 396567) := by
    rw [show ((396567 / 200000) : ℝ) = ((200000 / 396567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (4064882849 / 1000000000) ≤ -Real.log (3433 / 200000) ∧
    -Real.log (3433 / 200000) ≤ (812976571 / 200000000) := by
  have h := checkLog_sound (w := (2817 / 9683)) (n := 12)
    (lo := (599146949 / 1000000000)) (hi := (11982939 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3433) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 3433) = 1/(3433 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-812976571 / 200000000) (-4064882849 / 1000000000) (Real.log (3433 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (684566471 / 1000000000) ≤ -Real.log (15625 / 30983) ∧
    -Real.log (15625 / 30983) ≤ (85570809 / 125000000) := by
  have h := checkLog_sound (w := (7679 / 23304)) (n := 12)
    (lo := (684566471 / 1000000000)) (hi := (85570809 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30983 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30983 / 15625) = 1/(15625 / 30983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (684566471 / 1000000000) (85570809 / 125000000) (Real.log (30983 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (30983 / 15625) = -Real.log (15625 / 30983) := by
    rw [show ((30983 / 15625) : ℝ) = ((15625 / 30983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (4069378813 / 1000000000) ≤ -Real.log (267 / 15625) ∧
    -Real.log (267 / 15625) ≤ (4069378819 / 1000000000) := by
  have h := checkLog_sound (w := (7081 / 24169)) (n := 12)
    (lo := (603642913 / 1000000000)) (hi := (301821457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8544) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8544) = 1/(267 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-4069378819 / 1000000000) (-4069378813 / 1000000000) (Real.log (267 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (136899173 / 200000000) ≤ -Real.log (250000 / 495693) ∧
    -Real.log (250000 / 495693) ≤ (342247933 / 500000000) := by
  have h := checkLog_sound (w := (245693 / 745693)) (n := 12)
    (lo := (136899173 / 200000000)) (hi := (342247933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((495693 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(495693 / 250000) = 1/(250000 / 495693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (136899173 / 200000000) (342247933 / 500000000) (Real.log (495693 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (495693 / 250000) = -Real.log (250000 / 495693) := by
    rw [show ((495693 / 250000) : ℝ) = ((250000 / 495693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1015304827 / 250000000) ≤ -Real.log (4307 / 250000) ∧
    -Real.log (4307 / 250000) ≤ (2030609657 / 500000000) := by
  have h := checkLog_sound (w := (7011 / 24239)) (n := 12)
    (lo := (37217713 / 62500000)) (hi := (595483409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8614) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8614) = 1/(4307 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2030609657 / 500000000) (-1015304827 / 250000000) (Real.log (4307 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (684535203 / 1000000000) ≤ -Real.log (20000 / 39657) ∧
    -Real.log (20000 / 39657) ≤ (171133801 / 250000000) := by
  have h := checkLog_sound (w := (19657 / 59657)) (n := 12)
    (lo := (684535203 / 1000000000)) (hi := (171133801 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39657 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39657 / 20000) = 1/(20000 / 39657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (684535203 / 1000000000) (171133801 / 250000000) (Real.log (39657 / 20000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (39657 / 20000) = -Real.log (20000 / 39657) := by
    rw [show ((39657 / 20000) : ℝ) = ((20000 / 39657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2032878551 / 500000000) ≤ -Real.log (343 / 20000) ∧
    -Real.log (343 / 20000) ≤ (1016439277 / 250000000) := by
  have h := checkLog_sound (w := (141 / 484)) (n := 12)
    (lo := (300010601 / 500000000)) (hi := (600021203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 343) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(625 / 343) = 1/(343 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1016439277 / 250000000) (-2032878551 / 500000000) (Real.log (343 / 20000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4749410487 / 1000000000) ≤ -Real.log (500000000000 / 57758083309059) ∧
    -Real.log (500000000000 / 57758083309059) ≤ (2374705247 / 500000000) := by
  have h := checkLog_sound (w := (25758083309059 / 89758083309059)) (n := 12)
    (lo := (590527407 / 1000000000)) (hi := (36907963 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57758083309059 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(57758083309059 / 32000000000000) = 1/(500000000000 / 57758083309059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4749410487 / 1000000000) (2374705247 / 500000000) (Real.log (57758083309059 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (57758083309059 / 500000000000) = -Real.log (500000000000 / 57758083309059) := by
    rw [show ((57758083309059 / 500000000000) : ℝ) = ((500000000000 / 57758083309059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1188486321 / 250000000) ≤ -Real.log (500000000000 / 58020599250937) ∧
    -Real.log (500000000000 / 58020599250937) ≤ (4753945291 / 1000000000) := by
  have h := checkLog_sound (w := (26020599250937 / 90020599250937)) (n := 12)
    (lo := (148765551 / 250000000)) (hi := (119012441 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58020599250937 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(58020599250937 / 32000000000000) = 1/(500000000000 / 58020599250937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1188486321 / 250000000) (4753945291 / 1000000000) (Real.log (58020599250937 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (58020599250937 / 500000000000) = -Real.log (500000000000 / 58020599250937) := by
    rw [show ((58020599250937 / 500000000000) : ℝ) = ((500000000000 / 58020599250937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2372857587 / 500000000) ≤ -Real.log (500000000000 / 57545042953331) ∧
    -Real.log (500000000000 / 57545042953331) ≤ (4745715181 / 1000000000) := by
  have h := checkLog_sound (w := (25545042953331 / 89545042953331)) (n := 12)
    (lo := (293416047 / 500000000)) (hi := (117366419 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57545042953331 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(57545042953331 / 32000000000000) = 1/(500000000000 / 57545042953331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2372857587 / 500000000) (4745715181 / 1000000000) (Real.log (57545042953331 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (57545042953331 / 500000000000) = -Real.log (500000000000 / 57545042953331) := by
    rw [show ((57545042953331 / 500000000000) : ℝ) = ((500000000000 / 57545042953331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (950058461 / 200000000) ≤ -Real.log (4000000000 / 462472303207) ∧
    -Real.log (4000000000 / 462472303207) ≤ (593786539 / 125000000) := by
  have h := checkLog_sound (w := (206472303207 / 718472303207)) (n := 12)
    (lo := (23656369 / 40000000)) (hi := (295704613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((462472303207 / 256000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(462472303207 / 256000000000) = 1/(4000000000 / 462472303207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (950058461 / 200000000) (593786539 / 125000000) (Real.log (462472303207 / 4000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (462472303207 / 4000000000) = -Real.log (4000000000 / 462472303207) := by
    rw [show ((462472303207 / 4000000000) : ℝ) = ((4000000000 / 462472303207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0001

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0002Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0002
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

theorem reflection_log_1_neg : (683003129 / 1000000000) ≤ -Real.log (102400 / 202733) ∧
    -Real.log (102400 / 202733) ≤ (68300313 / 100000000) := by
  have h := checkLog_sound (w := (100333 / 305133)) (n := 12)
    (lo := (683003129 / 1000000000)) (hi := (68300313 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202733 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202733 / 102400) = 1/(102400 / 202733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (683003129 / 1000000000) (68300313 / 100000000) (Real.log (202733 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202733 / 102400) = -Real.log (102400 / 202733) := by
    rw [show ((202733 / 102400) : ℝ) = ((102400 / 202733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3902788429 / 1000000000) ≤ -Real.log (2067 / 102400) ∧
    -Real.log (2067 / 102400) ≤ (780557687 / 200000000) := by
  have h := checkLog_sound (w := (1133 / 5267)) (n := 12)
    (lo := (437052529 / 1000000000)) (hi := (43705253 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2067) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2067) = 1/(2067 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-780557687 / 200000000) (-3902788429 / 1000000000) (Real.log (2067 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (682956269 / 1000000000) ≤ -Real.log (1000000000000 / 1979721679687) ∧
    -Real.log (1000000000000 / 1979721679687) ≤ (68295627 / 100000000) := by
  have h := checkLog_sound (w := (979721679687 / 2979721679687)) (n := 12)
    (lo := (682956269 / 1000000000)) (hi := (68295627 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979721679687 / 1000000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979721679687 / 1000000000000) = 1/(1000000000000 / 1979721679687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (682956269 / 1000000000) (68295627 / 100000000) (Real.log (1979721679687 / 1000000000000)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1979721679687 / 1000000000000) = -Real.log (1000000000000 / 1979721679687) := by
    rw [show ((1979721679687 / 1000000000000) : ℝ) = ((1000000000000 / 1979721679687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (155928117 / 40000000) ≤ -Real.log (20278320313 / 1000000000000) ∧
    -Real.log (20278320313 / 1000000000000) ≤ (3898202931 / 1000000000) := by
  have h := checkLog_sound (w := (10971679687 / 51528320313)) (n := 12)
    (lo := (17298681 / 40000000)) (hi := (216233513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250000000 / 20278320313) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250000000 / 20278320313) = 1/(20278320313 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3898202931 / 1000000000) (-155928117 / 40000000) (Real.log (20278320313 / 1000000000000)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (672755121 / 1000000000) ≤ -Real.log (51200 / 100333) ∧
    -Real.log (51200 / 100333) ≤ (336377561 / 500000000) := by
  have h := checkLog_sound (w := (49133 / 151533)) (n := 12)
    (lo := (672755121 / 1000000000)) (hi := (336377561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100333 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100333 / 51200) = 1/(51200 / 100333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (672755121 / 1000000000) (336377561 / 500000000) (Real.log (100333 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (100333 / 51200) = -Real.log (51200 / 100333) := by
    rw [show ((100333 / 51200) : ℝ) = ((51200 / 100333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3209641249 / 1000000000) ≤ -Real.log (2067 / 51200) ∧
    -Real.log (2067 / 51200) ≤ (1604820627 / 500000000) := by
  have h := checkLog_sound (w := (1133 / 5267)) (n := 12)
    (lo := (437052529 / 1000000000)) (hi := (43705253 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2067) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2067) = 1/(2067 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1604820627 / 500000000) (-3209641249 / 1000000000) (Real.log (2067 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (42041277 / 62500000) ≤ -Real.log (102400 / 200647) ∧
    -Real.log (102400 / 200647) ≤ (672660433 / 1000000000) := by
  have h := checkLog_sound (w := (98247 / 303047)) (n := 12)
    (lo := (42041277 / 62500000)) (hi := (672660433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200647 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200647 / 102400) = 1/(102400 / 200647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (42041277 / 62500000) (672660433 / 1000000000) (Real.log (200647 / 102400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (200647 / 102400) = -Real.log (102400 / 200647) := by
    rw [show ((200647 / 102400) : ℝ) = ((102400 / 200647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (641011149 / 200000000) ≤ -Real.log (4153 / 102400) ∧
    -Real.log (4153 / 102400) ≤ (12820223 / 4000000) := by
  have h := checkLog_sound (w := (2247 / 10553)) (n := 12)
    (lo := (17298681 / 40000000)) (hi := (216233513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4153) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 4153) = 1/(4153 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-12820223 / 4000000) (-641011149 / 200000000) (Real.log (4153 / 102400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (684489309 / 1000000000) ≤ -Real.log (1000000 / 1982759) ∧
    -Real.log (1000000 / 1982759) ≤ (68448931 / 100000000) := by
  have h := checkLog_sound (w := (982759 / 2982759)) (n := 12)
    (lo := (684489309 / 1000000000)) (hi := (68448931 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982759 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982759 / 1000000) = 1/(1000000 / 1982759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (684489309 / 1000000000) (68448931 / 100000000) (Real.log (1982759 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1982759 / 1000000) = -Real.log (1000000 / 1982759) := by
    rw [show ((1982759 / 1000000) : ℝ) = ((1000000 / 1982759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (4060465007 / 1000000000) ≤ -Real.log (17241 / 1000000) ∧
    -Real.log (17241 / 1000000) ≤ (4060465013 / 1000000000) := by
  have h := checkLog_sound (w := (14009 / 48491)) (n := 12)
    (lo := (594729107 / 1000000000)) (hi := (148682277 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17241) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17241) = 1/(17241 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4060465013 / 1000000000) (-4060465007 / 1000000000) (Real.log (17241 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (684528143 / 1000000000) ≤ -Real.log (250000 / 495709) ∧
    -Real.log (250000 / 495709) ≤ (42783009 / 62500000) := by
  have h := checkLog_sound (w := (245709 / 745709)) (n := 12)
    (lo := (684528143 / 1000000000)) (hi := (42783009 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((495709 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(495709 / 250000) = 1/(250000 / 495709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (684528143 / 1000000000) (42783009 / 62500000) (Real.log (495709 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (495709 / 250000) = -Real.log (250000 / 495709) := by
    rw [show ((495709 / 250000) : ℝ) = ((250000 / 495709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (4064941109 / 1000000000) ≤ -Real.log (4291 / 250000) ∧
    -Real.log (4291 / 250000) ≤ (812988223 / 200000000) := by
  have h := checkLog_sound (w := (7043 / 24207)) (n := 12)
    (lo := (599205209 / 1000000000)) (hi := (59920521 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8582) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8582) = 1/(4291 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-812988223 / 200000000) (-4064941109 / 1000000000) (Real.log (4291 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (342228767 / 500000000) ≤ -Real.log (125000 / 247837) ∧
    -Real.log (125000 / 247837) ≤ (136891507 / 200000000) := by
  have h := checkLog_sound (w := (122837 / 372837)) (n := 12)
    (lo := (342228767 / 500000000)) (hi := (136891507 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247837 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247837 / 125000) = 1/(125000 / 247837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (342228767 / 500000000) (136891507 / 200000000) (Real.log (247837 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (247837 / 125000) = -Real.log (125000 / 247837) := by
    rw [show ((247837 / 125000) : ℝ) = ((125000 / 247837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (4056817587 / 1000000000) ≤ -Real.log (2163 / 125000) ∧
    -Real.log (2163 / 125000) ≤ (4056817593 / 1000000000) := by
  have h := checkLog_sound (w := (6973 / 24277)) (n := 12)
    (lo := (591081687 / 1000000000)) (hi := (73885211 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8652) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8652) = 1/(2163 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-4056817593 / 1000000000) (-4056817587 / 1000000000) (Real.log (2163 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (684496369 / 1000000000) ≤ -Real.log (1000000 / 1982773) ∧
    -Real.log (1000000 / 1982773) ≤ (68449637 / 100000000) := by
  have h := checkLog_sound (w := (982773 / 2982773)) (n := 12)
    (lo := (684496369 / 1000000000)) (hi := (68449637 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982773 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982773 / 1000000) = 1/(1000000 / 1982773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (684496369 / 1000000000) (68449637 / 100000000) (Real.log (1982773 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1982773 / 1000000) = -Real.log (1000000 / 1982773) := by
    rw [show ((1982773 / 1000000) : ℝ) = ((1000000 / 1982773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (812255471 / 200000000) ≤ -Real.log (17227 / 1000000) ∧
    -Real.log (17227 / 1000000) ≤ (4061277361 / 1000000000) := by
  have h := checkLog_sound (w := (14023 / 48477)) (n := 12)
    (lo := (119108291 / 200000000)) (hi := (37221341 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17227) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17227) = 1/(17227 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-4061277361 / 1000000000) (-812255471 / 200000000) (Real.log (17227 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1186238579 / 250000000) ≤ -Real.log (62500000000 / 7187659503509) ∧
    -Real.log (62500000000 / 7187659503509) ≤ (4744954323 / 1000000000) := by
  have h := checkLog_sound (w := (3187659503509 / 11187659503509)) (n := 12)
    (lo := (146517809 / 250000000)) (hi := (586071237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7187659503509 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7187659503509 / 4000000000000) = 1/(62500000000 / 7187659503509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1186238579 / 250000000) (4744954323 / 1000000000) (Real.log (7187659503509 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7187659503509 / 62500000000) = -Real.log (62500000000 / 7187659503509) := by
    rw [show ((7187659503509 / 62500000000) : ℝ) = ((62500000000 / 7187659503509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4749469251 / 1000000000) ≤ -Real.log (50000000000 / 5776147751107) ∧
    -Real.log (50000000000 / 5776147751107) ≤ (2374734629 / 500000000) := by
  have h := checkLog_sound (w := (2576147751107 / 8976147751107)) (n := 12)
    (lo := (590586171 / 1000000000)) (hi := (147646543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5776147751107 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5776147751107 / 3200000000000) = 1/(50000000000 / 5776147751107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4749469251 / 1000000000) (2374734629 / 500000000) (Real.log (5776147751107 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5776147751107 / 50000000000) = -Real.log (50000000000 / 5776147751107) := by
    rw [show ((5776147751107 / 50000000000) : ℝ) = ((50000000000 / 5776147751107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4741275121 / 1000000000) ≤ -Real.log (100000000000 / 11458021266759) ∧
    -Real.log (100000000000 / 11458021266759) ≤ (592659391 / 125000000) := by
  have h := checkLog_sound (w := (5058021266759 / 17858021266759)) (n := 12)
    (lo := (582392041 / 1000000000)) (hi := (291196021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11458021266759 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(11458021266759 / 6400000000000) = 1/(100000000000 / 11458021266759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4741275121 / 1000000000) (592659391 / 125000000) (Real.log (11458021266759 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (11458021266759 / 100000000000) = -Real.log (100000000000 / 11458021266759) := by
    rw [show ((11458021266759 / 100000000000) : ℝ) = ((100000000000 / 11458021266759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (189830949 / 40000000) ≤ -Real.log (250000000000 / 28774206187961) ∧
    -Real.log (250000000000 / 28774206187961) ≤ (1186443433 / 250000000) := by
  have h := checkLog_sound (w := (12774206187961 / 44774206187961)) (n := 12)
    (lo := (117378129 / 200000000)) (hi := (293445323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28774206187961 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(28774206187961 / 16000000000000) = 1/(250000000000 / 28774206187961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (189830949 / 40000000) (1186443433 / 250000000) (Real.log (28774206187961 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (28774206187961 / 250000000000) = -Real.log (250000000000 / 28774206187961) := by
    rw [show ((28774206187961 / 250000000000) : ℝ) = ((250000000000 / 28774206187961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0002

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0003Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0003
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

theorem reflection_log_1_neg : (682956269 / 1000000000) ≤ -Real.log (125000000000 / 247465209961) ∧
    -Real.log (125000000000 / 247465209961) ≤ (68295627 / 100000000) := by
  have h := checkLog_sound (w := (122465209961 / 372465209961)) (n := 12)
    (lo := (682956269 / 1000000000)) (hi := (68295627 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247465209961 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247465209961 / 125000000000) = 1/(125000000000 / 247465209961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (682956269 / 1000000000) (68295627 / 100000000) (Real.log (247465209961 / 125000000000)) := by
  have h := reflection_log_1_neg
  have he : Real.log (247465209961 / 125000000000) = -Real.log (125000000000 / 247465209961) := by
    rw [show ((247465209961 / 125000000000) : ℝ) = ((125000000000 / 247465209961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (155928117 / 40000000) ≤ -Real.log (2534790039 / 125000000000) ∧
    -Real.log (2534790039 / 125000000000) ≤ (3898202931 / 1000000000) := by
  have h := checkLog_sound (w := (1371459961 / 6441040039)) (n := 12)
    (lo := (17298681 / 40000000)) (hi := (216233513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 2534790039) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3906250000 / 2534790039) = 1/(2534790039 / 125000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3898202931 / 1000000000) (-155928117 / 40000000) (Real.log (2534790039 / 125000000000)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (341454703 / 500000000) ≤ -Real.log (51200 / 101357) ∧
    -Real.log (51200 / 101357) ≤ (682909407 / 1000000000) := by
  have h := checkLog_sound (w := (50157 / 152557)) (n := 12)
    (lo := (341454703 / 500000000)) (hi := (682909407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101357 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101357 / 51200) = 1/(51200 / 101357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (341454703 / 500000000) (682909407 / 1000000000) (Real.log (101357 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (101357 / 51200) = -Real.log (51200 / 101357) := by
    rw [show ((101357 / 51200) : ℝ) = ((51200 / 101357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3893638353 / 1000000000) ≤ -Real.log (1043 / 51200) ∧
    -Real.log (1043 / 51200) ≤ (3893638359 / 1000000000) := by
  have h := checkLog_sound (w := (557 / 2643)) (n := 12)
    (lo := (427902453 / 1000000000)) (hi := (213951227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1043) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1043) = 1/(1043 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3893638359 / 1000000000) (-3893638353 / 1000000000) (Real.log (1043 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (42041277 / 62500000) ≤ -Real.log (102400 / 200647) ∧
    -Real.log (102400 / 200647) ≤ (672660433 / 1000000000) := by
  have h := checkLog_sound (w := (98247 / 303047)) (n := 12)
    (lo := (42041277 / 62500000)) (hi := (672660433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200647 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200647 / 102400) = 1/(102400 / 200647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (42041277 / 62500000) (672660433 / 1000000000) (Real.log (200647 / 102400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (200647 / 102400) = -Real.log (102400 / 200647) := by
    rw [show ((200647 / 102400) : ℝ) = ((102400 / 200647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (641011149 / 200000000) ≤ -Real.log (4153 / 102400) ∧
    -Real.log (4153 / 102400) ≤ (12820223 / 4000000) := by
  have h := checkLog_sound (w := (2247 / 10553)) (n := 12)
    (lo := (17298681 / 40000000)) (hi := (216233513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4153) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 4153) = 1/(4153 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-12820223 / 4000000) (-641011149 / 200000000) (Real.log (4153 / 102400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (336282867 / 500000000) ≤ -Real.log (25600 / 50157) ∧
    -Real.log (25600 / 50157) ≤ (134513147 / 200000000) := by
  have h := checkLog_sound (w := (24557 / 75757)) (n := 12)
    (lo := (336282867 / 500000000)) (hi := (134513147 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50157 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50157 / 25600) = 1/(25600 / 50157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (336282867 / 500000000) (134513147 / 200000000) (Real.log (50157 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (50157 / 25600) = -Real.log (25600 / 50157) := by
    rw [show ((50157 / 25600) : ℝ) = ((25600 / 50157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3200491173 / 1000000000) ≤ -Real.log (1043 / 25600) ∧
    -Real.log (1043 / 25600) ≤ (1600245589 / 500000000) := by
  have h := checkLog_sound (w := (557 / 2643)) (n := 12)
    (lo := (427902453 / 1000000000)) (hi := (213951227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1043) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1043) = 1/(1043 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1600245589 / 500000000) (-3200491173 / 1000000000) (Real.log (1043 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (684450977 / 1000000000) ≤ -Real.log (1000000 / 1982683) ∧
    -Real.log (1000000 / 1982683) ≤ (342225489 / 500000000) := by
  have h := checkLog_sound (w := (982683 / 2982683)) (n := 12)
    (lo := (684450977 / 1000000000)) (hi := (342225489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982683 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982683 / 1000000) = 1/(1000000 / 1982683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (684450977 / 1000000000) (342225489 / 500000000) (Real.log (1982683 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1982683 / 1000000) = -Real.log (1000000 / 1982683) := by
    rw [show ((1982683 / 1000000) : ℝ) = ((1000000 / 1982683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2028033299 / 500000000) ≤ -Real.log (17317 / 1000000) ∧
    -Real.log (17317 / 1000000) ≤ (1014016651 / 250000000) := by
  have h := checkLog_sound (w := (13933 / 48567)) (n := 12)
    (lo := (295165349 / 500000000)) (hi := (590330699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17317) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17317) = 1/(17317 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1014016651 / 250000000) (-2028033299 / 500000000) (Real.log (17317 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (684489813 / 1000000000) ≤ -Real.log (25000 / 49569) ∧
    -Real.log (25000 / 49569) ≤ (342244907 / 500000000) := by
  have h := checkLog_sound (w := (24569 / 74569)) (n := 12)
    (lo := (684489813 / 1000000000)) (hi := (342244907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49569 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49569 / 25000) = 1/(25000 / 49569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (684489813 / 1000000000) (342244907 / 500000000) (Real.log (49569 / 25000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (49569 / 25000) = -Real.log (25000 / 49569) := by
    rw [show ((49569 / 25000) : ℝ) = ((25000 / 49569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (406052301 / 100000000) ≤ -Real.log (431 / 25000) ∧
    -Real.log (431 / 25000) ≤ (507565377 / 125000000) := by
  have h := checkLog_sound (w := (1401 / 4849)) (n := 12)
    (lo := (59478711 / 100000000)) (hi := (594787111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1724) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 1724) = 1/(431 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-507565377 / 125000000) (-406052301 / 100000000) (Real.log (431 / 25000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (684418697 / 1000000000) ≤ -Real.log (1000000 / 1982619) ∧
    -Real.log (1000000 / 1982619) ≤ (342209349 / 500000000) := by
  have h := checkLog_sound (w := (982619 / 2982619)) (n := 12)
    (lo := (684418697 / 1000000000)) (hi := (342209349 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982619 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982619 / 1000000) = 1/(1000000 / 1982619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (684418697 / 1000000000) (342209349 / 500000000) (Real.log (1982619 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1982619 / 1000000) = -Real.log (1000000 / 1982619) := by
    rw [show ((1982619 / 1000000) : ℝ) = ((1000000 / 1982619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (202618881 / 50000000) ≤ -Real.log (17381 / 1000000) ∧
    -Real.log (17381 / 1000000) ≤ (2026188813 / 500000000) := by
  have h := checkLog_sound (w := (13869 / 48631)) (n := 12)
    (lo := (14666043 / 25000000)) (hi := (586641721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17381) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17381) = 1/(17381 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2026188813 / 500000000) (-202618881 / 50000000) (Real.log (17381 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (684458039 / 1000000000) ≤ -Real.log (1000000 / 1982697) ∧
    -Real.log (1000000 / 1982697) ≤ (17111451 / 25000000) := by
  have h := checkLog_sound (w := (982697 / 2982697)) (n := 12)
    (lo := (684458039 / 1000000000)) (hi := (17111451 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982697 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982697 / 1000000) = 1/(1000000 / 1982697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (684458039 / 1000000000) (17111451 / 25000000) (Real.log (1982697 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1982697 / 1000000) = -Real.log (1000000 / 1982697) := by
    rw [show ((1982697 / 1000000) : ℝ) = ((1000000 / 1982697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (4056875379 / 1000000000) ≤ -Real.log (17303 / 1000000) ∧
    -Real.log (17303 / 1000000) ≤ (811375077 / 200000000) := by
  have h := checkLog_sound (w := (13947 / 48553)) (n := 12)
    (lo := (591139479 / 1000000000)) (hi := (14778487 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17303) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17303) = 1/(17303 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-811375077 / 200000000) (-4056875379 / 1000000000) (Real.log (17303 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (189620703 / 40000000) ≤ -Real.log (125000000000 / 14311680718369) ∧
    -Real.log (125000000000 / 14311680718369) ≤ (2370258791 / 500000000) := by
  have h := checkLog_sound (w := (6311680718369 / 22311680718369)) (n := 12)
    (lo := (116326899 / 200000000)) (hi := (9088039 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14311680718369 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(14311680718369 / 8000000000000) = 1/(125000000000 / 14311680718369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (189620703 / 40000000) (2370258791 / 500000000) (Real.log (14311680718369 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (14311680718369 / 125000000000) = -Real.log (125000000000 / 14311680718369) := by
    rw [show ((14311680718369 / 125000000000) : ℝ) = ((125000000000 / 14311680718369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4745012823 / 1000000000) ≤ -Real.log (50000000000 / 5750464037123) ∧
    -Real.log (50000000000 / 5750464037123) ≤ (474501283 / 100000000) := by
  have h := checkLog_sound (w := (2550464037123 / 8950464037123)) (n := 12)
    (lo := (586129743 / 1000000000)) (hi := (36633109 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5750464037123 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5750464037123 / 3200000000000) = 1/(50000000000 / 5750464037123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4745012823 / 1000000000) (474501283 / 100000000) (Real.log (5750464037123 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5750464037123 / 50000000000) = -Real.log (50000000000 / 5750464037123) := by
    rw [show ((5750464037123 / 50000000000) : ℝ) = ((50000000000 / 5750464037123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4736796317 / 1000000000) ≤ -Real.log (500000000000 / 57034088947701) ∧
    -Real.log (500000000000 / 57034088947701) ≤ (1184199081 / 250000000) := by
  have h := checkLog_sound (w := (25034088947701 / 89034088947701)) (n := 12)
    (lo := (577913237 / 1000000000)) (hi := (288956619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57034088947701 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(57034088947701 / 32000000000000) = 1/(500000000000 / 57034088947701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4736796317 / 1000000000) (1184199081 / 250000000) (Real.log (57034088947701 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (57034088947701 / 500000000000) = -Real.log (500000000000 / 57034088947701) := by
    rw [show ((57034088947701 / 500000000000) : ℝ) = ((500000000000 / 57034088947701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4741333417 / 1000000000) ≤ -Real.log (500000000000 / 57293446223199) ∧
    -Real.log (500000000000 / 57293446223199) ≤ (296333339 / 62500000) := by
  have h := checkLog_sound (w := (25293446223199 / 89293446223199)) (n := 12)
    (lo := (582450337 / 1000000000)) (hi := (291225169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57293446223199 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(57293446223199 / 32000000000000) = 1/(500000000000 / 57293446223199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4741333417 / 1000000000) (296333339 / 62500000) (Real.log (57293446223199 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (57293446223199 / 500000000000) = -Real.log (500000000000 / 57293446223199) := by
    rw [show ((57293446223199 / 500000000000) : ℝ) = ((500000000000 / 57293446223199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0003

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0004Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0004
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

theorem reflection_log_1_neg : (341454703 / 500000000) ≤ -Real.log (51200 / 101357) ∧
    -Real.log (51200 / 101357) ≤ (682909407 / 1000000000) := by
  have h := checkLog_sound (w := (50157 / 152557)) (n := 12)
    (lo := (341454703 / 500000000)) (hi := (682909407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101357 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101357 / 51200) = 1/(51200 / 101357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (341454703 / 500000000) (682909407 / 1000000000) (Real.log (101357 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (101357 / 51200) = -Real.log (51200 / 101357) := by
    rw [show ((101357 / 51200) : ℝ) = ((51200 / 101357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3893638353 / 1000000000) ≤ -Real.log (1043 / 51200) ∧
    -Real.log (1043 / 51200) ≤ (3893638359 / 1000000000) := by
  have h := checkLog_sound (w := (557 / 2643)) (n := 12)
    (lo := (427902453 / 1000000000)) (hi := (213951227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1043) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1043) = 1/(1043 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3893638359 / 1000000000) (-3893638353 / 1000000000) (Real.log (1043 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (34143127 / 50000000) ≤ -Real.log (250000000000 / 494884033203) ∧
    -Real.log (250000000000 / 494884033203) ≤ (682862541 / 1000000000) := by
  have h := checkLog_sound (w := (244884033203 / 744884033203)) (n := 12)
    (lo := (34143127 / 50000000)) (hi := (682862541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494884033203 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494884033203 / 250000000000) = 1/(250000000000 / 494884033203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (34143127 / 50000000) (682862541 / 1000000000) (Real.log (494884033203 / 250000000000)) := by
  have h := reflection_log_3_neg
  have he : Real.log (494884033203 / 250000000000) = -Real.log (250000000000 / 494884033203) := by
    rw [show ((494884033203 / 250000000000) : ℝ) = ((250000000000 / 494884033203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3889094521 / 1000000000) ≤ -Real.log (5115966797 / 250000000000) ∧
    -Real.log (5115966797 / 250000000000) ≤ (3889094527 / 1000000000) := by
  have h := checkLog_sound (w := (2696533203 / 12928466797)) (n := 12)
    (lo := (423358621 / 1000000000)) (hi := (211679311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7812500000 / 5115966797) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(7812500000 / 5115966797) = 1/(5115966797 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3889094527 / 1000000000) (-3889094521 / 1000000000) (Real.log (5115966797 / 250000000000)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (336282867 / 500000000) ≤ -Real.log (25600 / 50157) ∧
    -Real.log (25600 / 50157) ≤ (134513147 / 200000000) := by
  have h := checkLog_sound (w := (24557 / 75757)) (n := 12)
    (lo := (336282867 / 500000000)) (hi := (134513147 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50157 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50157 / 25600) = 1/(25600 / 50157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (336282867 / 500000000) (134513147 / 200000000) (Real.log (50157 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (50157 / 25600) = -Real.log (25600 / 50157) := by
    rw [show ((50157 / 25600) : ℝ) = ((25600 / 50157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3200491173 / 1000000000) ≤ -Real.log (1043 / 25600) ∧
    -Real.log (1043 / 25600) ≤ (1600245589 / 500000000) := by
  have h := checkLog_sound (w := (557 / 2643)) (n := 12)
    (lo := (427902453 / 1000000000)) (hi := (213951227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1043) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1043) = 1/(1043 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1600245589 / 500000000) (-3200491173 / 1000000000) (Real.log (1043 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (672471027 / 1000000000) ≤ -Real.log (102400 / 200609) ∧
    -Real.log (102400 / 200609) ≤ (168117757 / 250000000) := by
  have h := checkLog_sound (w := (98209 / 303009)) (n := 12)
    (lo := (672471027 / 1000000000)) (hi := (168117757 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200609 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200609 / 102400) = 1/(102400 / 200609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (672471027 / 1000000000) (168117757 / 250000000) (Real.log (200609 / 102400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (200609 / 102400) = -Real.log (102400 / 200609) := by
    rw [show ((200609 / 102400) : ℝ) = ((102400 / 200609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3195947341 / 1000000000) ≤ -Real.log (4191 / 102400) ∧
    -Real.log (4191 / 102400) ≤ (1597973673 / 500000000) := by
  have h := checkLog_sound (w := (2209 / 10591)) (n := 12)
    (lo := (423358621 / 1000000000)) (hi := (211679311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4191) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 4191) = 1/(4191 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1597973673 / 500000000) (-3195947341 / 1000000000) (Real.log (4191 / 102400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (684413149 / 1000000000) ≤ -Real.log (62500 / 123913) ∧
    -Real.log (62500 / 123913) ≤ (13688263 / 20000000) := by
  have h := checkLog_sound (w := (61413 / 186413)) (n := 12)
    (lo := (684413149 / 1000000000)) (hi := (13688263 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123913 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123913 / 62500) = 1/(62500 / 123913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (684413149 / 1000000000) (13688263 / 20000000) (Real.log (123913 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (123913 / 62500) = -Real.log (62500 / 123913) := by
    rw [show ((123913 / 62500) : ℝ) = ((62500 / 123913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (810348989 / 200000000) ≤ -Real.log (1087 / 62500) ∧
    -Real.log (1087 / 62500) ≤ (4051744951 / 1000000000) := by
  have h := checkLog_sound (w := (6929 / 24321)) (n := 12)
    (lo := (117201809 / 200000000)) (hi := (293004523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8696) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8696) = 1/(1087 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4051744951 / 1000000000) (-810348989 / 200000000) (Real.log (1087 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (342225741 / 500000000) ≤ -Real.log (250000 / 495671) ∧
    -Real.log (250000 / 495671) ≤ (684451483 / 1000000000) := by
  have h := checkLog_sound (w := (245671 / 745671)) (n := 12)
    (lo := (342225741 / 500000000)) (hi := (684451483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((495671 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(495671 / 250000) = 1/(250000 / 495671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (342225741 / 500000000) (684451483 / 1000000000) (Real.log (495671 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (495671 / 250000) = -Real.log (250000 / 495671) := by
    rw [show ((495671 / 250000) : ℝ) = ((250000 / 495671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2028062173 / 500000000) ≤ -Real.log (4329 / 250000) ∧
    -Real.log (4329 / 250000) ≤ (63376943 / 15625000) := by
  have h := checkLog_sound (w := (6967 / 24283)) (n := 12)
    (lo := (295194223 / 500000000)) (hi := (590388447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8658) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8658) = 1/(4329 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-63376943 / 15625000) (-2028062173 / 500000000) (Real.log (4329 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (171095091 / 250000000) ≤ -Real.log (1000000 / 1982543) ∧
    -Real.log (1000000 / 1982543) ≤ (136876073 / 200000000) := by
  have h := checkLog_sound (w := (982543 / 2982543)) (n := 12)
    (lo := (171095091 / 250000000)) (hi := (136876073 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982543 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982543 / 1000000) = 1/(1000000 / 1982543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (171095091 / 250000000) (136876073 / 200000000) (Real.log (1982543 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1982543 / 1000000) = -Real.log (1000000 / 1982543) := by
    rw [show ((1982543 / 1000000) : ℝ) = ((1000000 / 1982543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (4048014561 / 1000000000) ≤ -Real.log (17457 / 1000000) ∧
    -Real.log (17457 / 1000000) ≤ (4048014567 / 1000000000) := by
  have h := checkLog_sound (w := (13793 / 48707)) (n := 12)
    (lo := (582278661 / 1000000000)) (hi := (291139331 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17457) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17457) = 1/(17457 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-4048014567 / 1000000000) (-4048014561 / 1000000000) (Real.log (17457 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (342209601 / 500000000) ≤ -Real.log (50000 / 99131) ∧
    -Real.log (50000 / 99131) ≤ (684419203 / 1000000000) := by
  have h := checkLog_sound (w := (49131 / 149131)) (n := 12)
    (lo := (342209601 / 500000000)) (hi := (684419203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99131 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99131 / 50000) = 1/(50000 / 99131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (342209601 / 500000000) (684419203 / 1000000000) (Real.log (99131 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (99131 / 50000) = -Real.log (50000 / 99131) := by
    rw [show ((99131 / 50000) : ℝ) = ((50000 / 99131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1013108789 / 250000000) ≤ -Real.log (869 / 50000) ∧
    -Real.log (869 / 50000) ≤ (2026217581 / 500000000) := by
  have h := checkLog_sound (w := (1387 / 4863)) (n := 12)
    (lo := (73337407 / 125000000)) (hi := (586699257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1738) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 1738) = 1/(869 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2026217581 / 500000000) (-1013108789 / 250000000) (Real.log (869 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2368079047 / 500000000) ≤ -Real.log (125000000000 / 14249425022999) ∧
    -Real.log (125000000000 / 14249425022999) ≤ (4736158101 / 1000000000) := by
  have h := checkLog_sound (w := (6249425022999 / 22249425022999)) (n := 12)
    (lo := (288637507 / 500000000)) (hi := (115455003 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14249425022999 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(14249425022999 / 8000000000000) = 1/(125000000000 / 14249425022999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2368079047 / 500000000) (4736158101 / 1000000000) (Real.log (14249425022999 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (14249425022999 / 125000000000) = -Real.log (125000000000 / 14249425022999) := by
    rw [show ((14249425022999 / 125000000000) : ℝ) = ((125000000000 / 14249425022999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1185143957 / 250000000) ≤ -Real.log (250000000000 / 28625028875029) ∧
    -Real.log (250000000000 / 28625028875029) ≤ (948115167 / 200000000) := by
  have h := checkLog_sound (w := (12625028875029 / 44625028875029)) (n := 12)
    (lo := (145423187 / 250000000)) (hi := (581692749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28625028875029 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(28625028875029 / 16000000000000) = 1/(250000000000 / 28625028875029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1185143957 / 250000000) (948115167 / 200000000) (Real.log (28625028875029 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (28625028875029 / 250000000000) = -Real.log (250000000000 / 28625028875029) := by
    rw [show ((28625028875029 / 250000000000) : ℝ) = ((250000000000 / 28625028875029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (189295797 / 40000000) ≤ -Real.log (500000000000 / 56783611158847) ∧
    -Real.log (500000000000 / 56783611158847) ≤ (1183098733 / 250000000) := by
  have h := checkLog_sound (w := (24783611158847 / 88783611158847)) (n := 12)
    (lo := (114702369 / 200000000)) (hi := (286755923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56783611158847 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(56783611158847 / 32000000000000) = 1/(500000000000 / 56783611158847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (189295797 / 40000000) (1183098733 / 250000000) (Real.log (56783611158847 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (56783611158847 / 500000000000) = -Real.log (500000000000 / 56783611158847) := by
    rw [show ((56783611158847 / 500000000000) : ℝ) = ((500000000000 / 56783611158847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2368427179 / 500000000) ≤ -Real.log (31250000000 / 3564837456847) ∧
    -Real.log (31250000000 / 3564837456847) ≤ (947370873 / 200000000) := by
  have h := checkLog_sound (w := (1564837456847 / 5564837456847)) (n := 12)
    (lo := (288985639 / 500000000)) (hi := (577971279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3564837456847 / 2000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(3564837456847 / 2000000000000) = 1/(31250000000 / 3564837456847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2368427179 / 500000000) (947370873 / 200000000) (Real.log (3564837456847 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3564837456847 / 31250000000) = -Real.log (31250000000 / 3564837456847) := by
    rw [show ((3564837456847 / 31250000000) : ℝ) = ((31250000000 / 3564837456847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0004

end


