-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0047Logs__8
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0047Logs__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:18:04.763322+00:00
-- url     : https://prove2.me/theorems/2c233f11-4ba3-4180-9d08-d0b5775232ba
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0047Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0048Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0047Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0048Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0049Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0050Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0051Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0052Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0053Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0054Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0047Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0048Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0049Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0050Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0051Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0052Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0053Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0054Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0047Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0048Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0049Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0050Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0051Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0052Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0053Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0054Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0047Logs (+7 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0048Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0049Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0050Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0051Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0052Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0053Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0054Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0047Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0047
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

theorem reflection_log_1_neg : (5889641 / 15625000) ≤ -Real.log (640 / 933) ∧
    -Real.log (640 / 933) ≤ (15077481 / 40000000) := by
  have h := checkLog_sound (w := (293 / 1573)) (n := 12)
    (lo := (5889641 / 15625000)) (hi := (15077481 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((933 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(933 / 640) = 1/(640 / 933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (5889641 / 15625000) (15077481 / 40000000) (Real.log (933 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (933 / 640) = -Real.log (640 / 933) := by
    rw [show ((933 / 640) : ℝ) = ((640 / 933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (153035849 / 250000000) ≤ -Real.log (347 / 640) ∧
    -Real.log (347 / 640) ≤ (612143397 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 987)) (n := 12)
    (lo := (153035849 / 250000000)) (hi := (612143397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 347) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 347) = 1/(347 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-612143397 / 1000000000) (-153035849 / 250000000) (Real.log (347 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (188066421 / 500000000) ≤ -Real.log (2560 / 3729) ∧
    -Real.log (2560 / 3729) ≤ (376132843 / 1000000000) := by
  have h := checkLog_sound (w := (1169 / 6289)) (n := 12)
    (lo := (188066421 / 500000000)) (hi := (376132843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3729 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3729 / 2560) = 1/(2560 / 3729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (188066421 / 500000000) (376132843 / 1000000000) (Real.log (3729 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3729 / 2560) = -Real.log (2560 / 3729) := by
    rw [show ((3729 / 2560) : ℝ) = ((2560 / 3729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (121996869 / 200000000) ≤ -Real.log (1391 / 2560) ∧
    -Real.log (1391 / 2560) ≤ (304992173 / 500000000) := by
  have h := checkLog_sound (w := (1169 / 3951)) (n := 12)
    (lo := (121996869 / 200000000)) (hi := (304992173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1391) = 1/(1391 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-304992173 / 500000000) (-121996869 / 200000000) (Real.log (1391 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (32502197 / 50000000) ≤ -Real.log (320 / 613) ∧
    -Real.log (320 / 613) ≤ (650043941 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 933)) (n := 12)
    (lo := (32502197 / 50000000)) (hi := (650043941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613 / 320) = 1/(320 / 613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (32502197 / 50000000) (650043941 / 1000000000) (Real.log (613 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (613 / 320) = -Real.log (320 / 613) := by
    rw [show ((613 / 320) : ℝ) = ((320 / 613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (77265129 / 31250000) ≤ -Real.log (27 / 320) ∧
    -Real.log (27 / 320) ≤ (618121033 / 250000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(40 / 27) = 1/(27 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-618121033 / 250000000) (-77265129 / 31250000) (Real.log (27 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (6488197 / 10000000) ≤ -Real.log (1280 / 2449) ∧
    -Real.log (1280 / 2449) ≤ (648819701 / 1000000000) := by
  have h := checkLog_sound (w := (1169 / 3729)) (n := 12)
    (lo := (6488197 / 10000000)) (hi := (648819701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2449 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2449 / 1280) = 1/(1280 / 2449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (6488197 / 10000000) (648819701 / 1000000000) (Real.log (2449 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2449 / 1280) = -Real.log (1280 / 2449) := by
    rw [show ((2449 / 1280) : ℝ) = ((1280 / 2449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2445085153 / 1000000000) ≤ -Real.log (111 / 1280) ∧
    -Real.log (111 / 1280) ≤ (2445085157 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 271)) (n := 12)
    (lo := (365643613 / 1000000000)) (hi := (182821807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 111) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 111) = 1/(111 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2445085157 / 1000000000) (-2445085153 / 1000000000) (Real.log (111 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (521544767 / 1000000000) ≤ -Real.log (250000 / 421157) ∧
    -Real.log (250000 / 421157) ≤ (8149137 / 15625000) := by
  have h := checkLog_sound (w := (171157 / 671157)) (n := 12)
    (lo := (521544767 / 1000000000)) (hi := (8149137 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((421157 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(421157 / 250000) = 1/(250000 / 421157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (521544767 / 1000000000) (8149137 / 15625000) (Real.log (421157 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (421157 / 250000) = -Real.log (250000 / 421157) := by
    rw [show ((421157 / 250000) : ℝ) = ((250000 / 421157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1154002383 / 1000000000) ≤ -Real.log (78843 / 250000) ∧
    -Real.log (78843 / 250000) ≤ (230800477 / 200000000) := by
  have h := checkLog_sound (w := (46157 / 203843)) (n := 12)
    (lo := (460855203 / 1000000000)) (hi := (115213801 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 78843) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 78843) = 1/(78843 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-230800477 / 200000000) (-1154002383 / 1000000000) (Real.log (78843 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (522832057 / 1000000000) ≤ -Real.log (500000 / 843399) ∧
    -Real.log (500000 / 843399) ≤ (261416029 / 500000000) := by
  have h := checkLog_sound (w := (343399 / 1343399)) (n := 12)
    (lo := (522832057 / 1000000000)) (hi := (261416029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((843399 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(843399 / 500000) = 1/(500000 / 843399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (522832057 / 1000000000) (261416029 / 500000000) (Real.log (843399 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (843399 / 500000) = -Real.log (500000 / 843399) := by
    rw [show ((843399 / 500000) : ℝ) = ((500000 / 843399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (72556683 / 62500000) ≤ -Real.log (156601 / 500000) ∧
    -Real.log (156601 / 500000) ≤ (116090693 / 100000000) := by
  have h := checkLog_sound (w := (93399 / 406601)) (n := 12)
    (lo := (116939937 / 250000000)) (hi := (467759749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 156601) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 156601) = 1/(156601 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-116090693 / 100000000) (-72556683 / 62500000) (Real.log (156601 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (441625373 / 1000000000) ≤ -Real.log (1000000 / 1555233) ∧
    -Real.log (1000000 / 1555233) ≤ (220812687 / 500000000) := by
  have h := checkLog_sound (w := (555233 / 2555233)) (n := 12)
    (lo := (441625373 / 1000000000)) (hi := (220812687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1555233 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1555233 / 1000000) = 1/(1000000 / 1555233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (441625373 / 1000000000) (220812687 / 500000000) (Real.log (1555233 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1555233 / 1000000) = -Real.log (1000000 / 1555233) := by
    rw [show ((1555233 / 1000000) : ℝ) = ((1000000 / 1555233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (101275591 / 125000000) ≤ -Real.log (444767 / 1000000) ∧
    -Real.log (444767 / 1000000) ≤ (81020473 / 100000000) := by
  have h := checkLog_sound (w := (55233 / 944767)) (n := 12)
    (lo := (29264387 / 250000000)) (hi := (117057549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 444767) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 444767) = 1/(444767 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-81020473 / 100000000) (-101275591 / 125000000) (Real.log (444767 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (88616009 / 200000000) ≤ -Real.log (1000000 / 1557497) ∧
    -Real.log (1000000 / 1557497) ≤ (221540023 / 500000000) := by
  have h := checkLog_sound (w := (557497 / 2557497)) (n := 12)
    (lo := (88616009 / 200000000)) (hi := (221540023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1557497 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1557497 / 1000000) = 1/(1000000 / 1557497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (88616009 / 200000000) (221540023 / 500000000) (Real.log (1557497 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1557497 / 1000000) = -Real.log (1000000 / 1557497) := by
    rw [show ((1557497 / 1000000) : ℝ) = ((1000000 / 1557497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (407654017 / 500000000) ≤ -Real.log (442503 / 1000000) ∧
    -Real.log (442503 / 1000000) ≤ (203827009 / 250000000) := by
  have h := checkLog_sound (w := (57497 / 942503)) (n := 12)
    (lo := (61080427 / 500000000)) (hi := (24432171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 442503) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 442503) = 1/(442503 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-203827009 / 250000000) (-407654017 / 500000000) (Real.log (442503 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1675547151 / 1000000000) ≤ -Real.log (250000000000 / 1335429270829) ∧
    -Real.log (250000000000 / 1335429270829) ≤ (837773577 / 500000000) := by
  have h := checkLog_sound (w := (335429270829 / 2335429270829)) (n := 12)
    (lo := (289252791 / 1000000000)) (hi := (36156599 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1335429270829 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1335429270829 / 1000000000000) = 1/(250000000000 / 1335429270829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1675547151 / 1000000000) (837773577 / 500000000) (Real.log (1335429270829 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1335429270829 / 250000000000) = -Real.log (250000000000 / 1335429270829) := by
    rw [show ((1335429270829 / 250000000000) : ℝ) = ((250000000000 / 1335429270829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (336747797 / 200000000) ≤ -Real.log (62500000000 / 336603454001) ∧
    -Real.log (62500000000 / 336603454001) ≤ (420934747 / 250000000) := by
  have h := checkLog_sound (w := (86603454001 / 586603454001)) (n := 12)
    (lo := (2379557 / 8000000)) (hi := (148722313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336603454001 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(336603454001 / 250000000000) = 1/(62500000000 / 336603454001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (336747797 / 200000000) (420934747 / 250000000) (Real.log (336603454001 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (336603454001 / 62500000000) = -Real.log (62500000000 / 336603454001) := by
    rw [show ((336603454001 / 62500000000) : ℝ) = ((62500000000 / 336603454001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (625915051 / 500000000) ≤ -Real.log (62500000000 / 218546030843) ∧
    -Real.log (62500000000 / 218546030843) ≤ (156478763 / 125000000) := by
  have h := checkLog_sound (w := (93546030843 / 343546030843)) (n := 12)
    (lo := (279341461 / 500000000)) (hi := (558682923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218546030843 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(218546030843 / 125000000000) = 1/(62500000000 / 218546030843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (625915051 / 500000000) (156478763 / 125000000) (Real.log (218546030843 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (218546030843 / 62500000000) = -Real.log (62500000000 / 218546030843) := by
    rw [show ((218546030843 / 62500000000) : ℝ) = ((62500000000 / 218546030843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1258388079 / 1000000000) ≤ -Real.log (250000000000 / 879935842243) ∧
    -Real.log (250000000000 / 879935842243) ≤ (1258388081 / 1000000000) := by
  have h := checkLog_sound (w := (379935842243 / 1379935842243)) (n := 12)
    (lo := (565240899 / 1000000000)) (hi := (5652409 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((879935842243 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(879935842243 / 500000000000) = 1/(250000000000 / 879935842243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1258388079 / 1000000000) (1258388081 / 1000000000) (Real.log (879935842243 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (879935842243 / 250000000000) = -Real.log (250000000000 / 879935842243) := by
    rw [show ((879935842243 / 250000000000) : ℝ) = ((250000000000 / 879935842243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0047

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0048Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0048
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

theorem reflection_log_1_neg : (188066421 / 500000000) ≤ -Real.log (2560 / 3729) ∧
    -Real.log (2560 / 3729) ≤ (376132843 / 1000000000) := by
  have h := checkLog_sound (w := (1169 / 6289)) (n := 12)
    (lo := (188066421 / 500000000)) (hi := (376132843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3729 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3729 / 2560) = 1/(2560 / 3729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (188066421 / 500000000) (376132843 / 1000000000) (Real.log (3729 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3729 / 2560) = -Real.log (2560 / 3729) := by
    rw [show ((3729 / 2560) : ℝ) = ((2560 / 3729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (121996869 / 200000000) ≤ -Real.log (1391 / 2560) ∧
    -Real.log (1391 / 2560) ≤ (304992173 / 500000000) := by
  have h := checkLog_sound (w := (1169 / 3951)) (n := 12)
    (lo := (121996869 / 200000000)) (hi := (304992173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1391) = 1/(1391 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-304992173 / 500000000) (-121996869 / 200000000) (Real.log (1391 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (375328013 / 1000000000) ≤ -Real.log (1280 / 1863) ∧
    -Real.log (1280 / 1863) ≤ (187664007 / 500000000) := by
  have h := checkLog_sound (w := (583 / 3143)) (n := 12)
    (lo := (375328013 / 1000000000)) (hi := (187664007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1863 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1863 / 1280) = 1/(1280 / 1863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (375328013 / 1000000000) (187664007 / 500000000) (Real.log (1863 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1863 / 1280) = -Real.log (1280 / 1863) := by
    rw [show ((1863 / 1280) : ℝ) = ((1280 / 1863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (303914973 / 500000000) ≤ -Real.log (697 / 1280) ∧
    -Real.log (697 / 1280) ≤ (607829947 / 1000000000) := by
  have h := checkLog_sound (w := (583 / 1977)) (n := 12)
    (lo := (303914973 / 500000000)) (hi := (607829947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 697) = 1/(697 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-607829947 / 1000000000) (-303914973 / 500000000) (Real.log (697 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (6488197 / 10000000) ≤ -Real.log (1280 / 2449) ∧
    -Real.log (1280 / 2449) ≤ (648819701 / 1000000000) := by
  have h := checkLog_sound (w := (1169 / 3729)) (n := 12)
    (lo := (6488197 / 10000000)) (hi := (648819701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2449 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2449 / 1280) = 1/(1280 / 2449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (6488197 / 10000000) (648819701 / 1000000000) (Real.log (2449 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2449 / 1280) = -Real.log (1280 / 2449) := by
    rw [show ((2449 / 1280) : ℝ) = ((1280 / 2449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2445085153 / 1000000000) ≤ -Real.log (111 / 1280) ∧
    -Real.log (111 / 1280) ≤ (2445085157 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 271)) (n := 12)
    (lo := (365643613 / 1000000000)) (hi := (182821807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 111) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 111) = 1/(111 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2445085157 / 1000000000) (-2445085153 / 1000000000) (Real.log (111 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (647593959 / 1000000000) ≤ -Real.log (640 / 1223) ∧
    -Real.log (640 / 1223) ≤ (16189849 / 25000000) := by
  have h := checkLog_sound (w := (583 / 1863)) (n := 12)
    (lo := (647593959 / 1000000000)) (hi := (16189849 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1223 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1223 / 640) = 1/(640 / 1223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (647593959 / 1000000000) (16189849 / 25000000) (Real.log (1223 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1223 / 640) = -Real.log (640 / 1223) := by
    rw [show ((1223 / 640) : ℝ) = ((640 / 1223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1209208453 / 500000000) ≤ -Real.log (57 / 640) ∧
    -Real.log (57 / 640) ≤ (241841691 / 100000000) := by
  have h := checkLog_sound (w := (23 / 137)) (n := 12)
    (lo := (169487683 / 500000000)) (hi := (338975367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 57) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(80 / 57) = 1/(57 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-241841691 / 100000000) (-1209208453 / 500000000) (Real.log (57 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (520262357 / 1000000000) ≤ -Real.log (1000000 / 1682469) ∧
    -Real.log (1000000 / 1682469) ≤ (260131179 / 500000000) := by
  have h := checkLog_sound (w := (682469 / 2682469)) (n := 12)
    (lo := (520262357 / 1000000000)) (hi := (260131179 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1682469 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1682469 / 1000000) = 1/(1000000 / 1682469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (520262357 / 1000000000) (260131179 / 500000000) (Real.log (1682469 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1682469 / 1000000) = -Real.log (1000000 / 1682469) := by
    rw [show ((1682469 / 1000000) : ℝ) = ((1000000 / 1682469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1147179827 / 1000000000) ≤ -Real.log (317531 / 1000000) ∧
    -Real.log (317531 / 1000000) ≤ (1147179829 / 1000000000) := by
  have h := checkLog_sound (w := (182469 / 817531)) (n := 12)
    (lo := (454032647 / 1000000000)) (hi := (56754081 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 317531) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 317531) = 1/(317531 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1147179829 / 1000000000) (-1147179827 / 1000000000) (Real.log (317531 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (521545361 / 1000000000) ≤ -Real.log (1000000 / 1684629) ∧
    -Real.log (1000000 / 1684629) ≤ (260772681 / 500000000) := by
  have h := checkLog_sound (w := (684629 / 2684629)) (n := 12)
    (lo := (521545361 / 1000000000)) (hi := (260772681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1684629 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1684629 / 1000000) = 1/(1000000 / 1684629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (521545361 / 1000000000) (260772681 / 500000000) (Real.log (1684629 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1684629 / 1000000) = -Real.log (1000000 / 1684629) := by
    rw [show ((1684629 / 1000000) : ℝ) = ((1000000 / 1684629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (577002777 / 500000000) ≤ -Real.log (315371 / 1000000) ∧
    -Real.log (315371 / 1000000) ≤ (288501389 / 250000000) := by
  have h := checkLog_sound (w := (184629 / 815371)) (n := 12)
    (lo := (230429187 / 500000000)) (hi := (3686867 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 315371) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 315371) = 1/(315371 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-288501389 / 250000000) (-577002777 / 500000000) (Real.log (315371 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (88035777 / 200000000) ≤ -Real.log (200000 / 310597) ∧
    -Real.log (200000 / 310597) ≤ (220089443 / 500000000) := by
  have h := checkLog_sound (w := (110597 / 510597)) (n := 12)
    (lo := (88035777 / 200000000)) (hi := (220089443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((310597 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(310597 / 200000) = 1/(200000 / 310597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (88035777 / 200000000) (220089443 / 500000000) (Real.log (310597 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (310597 / 200000) = -Real.log (200000 / 310597) := by
    rw [show ((310597 / 200000) : ℝ) = ((200000 / 310597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (805163127 / 1000000000) ≤ -Real.log (89403 / 200000) ∧
    -Real.log (89403 / 200000) ≤ (805163129 / 1000000000) := by
  have h := checkLog_sound (w := (10597 / 189403)) (n := 12)
    (lo := (112015947 / 1000000000)) (hi := (28003987 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 89403) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 89403) = 1/(89403 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-805163129 / 1000000000) (-805163127 / 1000000000) (Real.log (89403 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (13800813 / 31250000) ≤ -Real.log (500000 / 777617) ∧
    -Real.log (500000 / 777617) ≤ (441626017 / 1000000000) := by
  have h := checkLog_sound (w := (277617 / 1277617)) (n := 12)
    (lo := (13800813 / 31250000)) (hi := (441626017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((777617 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(777617 / 500000) = 1/(500000 / 777617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (13800813 / 31250000) (441626017 / 1000000000) (Real.log (777617 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (777617 / 500000) = -Real.log (500000 / 777617) := by
    rw [show ((777617 / 500000) : ℝ) = ((500000 / 777617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (810206977 / 1000000000) ≤ -Real.log (222383 / 500000) ∧
    -Real.log (222383 / 500000) ≤ (810206979 / 1000000000) := by
  have h := checkLog_sound (w := (27617 / 472383)) (n := 12)
    (lo := (117059797 / 1000000000)) (hi := (58529899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 222383) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 222383) = 1/(222383 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-810206979 / 1000000000) (-810206977 / 1000000000) (Real.log (222383 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1667442183 / 1000000000) ≤ -Real.log (25000000000 / 132464940431) ∧
    -Real.log (25000000000 / 132464940431) ≤ (833721093 / 500000000) := by
  have h := checkLog_sound (w := (32464940431 / 232464940431)) (n := 12)
    (lo := (281147823 / 1000000000)) (hi := (17571739 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((132464940431 / 100000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(132464940431 / 100000000000) = 1/(25000000000 / 132464940431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1667442183 / 1000000000) (833721093 / 500000000) (Real.log (132464940431 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (132464940431 / 25000000000) = -Real.log (25000000000 / 132464940431) := by
    rw [show ((132464940431 / 25000000000) : ℝ) = ((25000000000 / 132464940431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (335110183 / 200000000) ≤ -Real.log (100000000000 / 534173719207) ∧
    -Real.log (100000000000 / 534173719207) ≤ (837775459 / 500000000) := by
  have h := checkLog_sound (w := (134173719207 / 934173719207)) (n := 12)
    (lo := (57851311 / 200000000)) (hi := (72314139 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((534173719207 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(534173719207 / 400000000000) = 1/(100000000000 / 534173719207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (335110183 / 200000000) (837775459 / 500000000) (Real.log (534173719207 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (534173719207 / 100000000000) = -Real.log (100000000000 / 534173719207) := by
    rw [show ((534173719207 / 100000000000) : ℝ) = ((100000000000 / 534173719207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (311335503 / 250000000) ≤ -Real.log (10000000000 / 34741227923) ∧
    -Real.log (10000000000 / 34741227923) ≤ (622671007 / 500000000) := by
  have h := checkLog_sound (w := (14741227923 / 54741227923)) (n := 12)
    (lo := (34512177 / 62500000)) (hi := (552194833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34741227923 / 20000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(34741227923 / 20000000000) = 1/(10000000000 / 34741227923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (311335503 / 250000000) (622671007 / 500000000) (Real.log (34741227923 / 10000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (34741227923 / 10000000000) = -Real.log (10000000000 / 34741227923) := by
    rw [show ((34741227923 / 10000000000) : ℝ) = ((10000000000 / 34741227923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1251832993 / 1000000000) ≤ -Real.log (500000000000 / 1748373301917) ∧
    -Real.log (500000000000 / 1748373301917) ≤ (250366599 / 200000000) := by
  have h := checkLog_sound (w := (748373301917 / 2748373301917)) (n := 12)
    (lo := (558685813 / 1000000000)) (hi := (279342907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1748373301917 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1748373301917 / 1000000000000) = 1/(500000000000 / 1748373301917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1251832993 / 1000000000) (250366599 / 200000000) (Real.log (1748373301917 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1748373301917 / 500000000000) = -Real.log (500000000000 / 1748373301917) := by
    rw [show ((1748373301917 / 500000000000) : ℝ) = ((500000000000 / 1748373301917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0048

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0049Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0049
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

theorem reflection_log_1_neg : (375328013 / 1000000000) ≤ -Real.log (1280 / 1863) ∧
    -Real.log (1280 / 1863) ≤ (187664007 / 500000000) := by
  have h := checkLog_sound (w := (583 / 3143)) (n := 12)
    (lo := (375328013 / 1000000000)) (hi := (187664007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1863 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1863 / 1280) = 1/(1280 / 1863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (375328013 / 1000000000) (187664007 / 500000000) (Real.log (1863 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1863 / 1280) = -Real.log (1280 / 1863) := by
    rw [show ((1863 / 1280) : ℝ) = ((1280 / 1863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (303914973 / 500000000) ≤ -Real.log (697 / 1280) ∧
    -Real.log (697 / 1280) ≤ (607829947 / 1000000000) := by
  have h := checkLog_sound (w := (583 / 1977)) (n := 12)
    (lo := (303914973 / 500000000)) (hi := (607829947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 697) = 1/(697 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-607829947 / 1000000000) (-303914973 / 500000000) (Real.log (697 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (46815317 / 125000000) ≤ -Real.log (2560 / 3723) ∧
    -Real.log (2560 / 3723) ≤ (374522537 / 1000000000) := by
  have h := checkLog_sound (w := (1163 / 6283)) (n := 12)
    (lo := (46815317 / 125000000)) (hi := (374522537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3723 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3723 / 2560) = 1/(2560 / 3723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (46815317 / 125000000) (374522537 / 1000000000) (Real.log (3723 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3723 / 2560) = -Real.log (2560 / 3723) := by
    rw [show ((3723 / 2560) : ℝ) = ((2560 / 3723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (302840089 / 500000000) ≤ -Real.log (1397 / 2560) ∧
    -Real.log (1397 / 2560) ≤ (605680179 / 1000000000) := by
  have h := checkLog_sound (w := (1163 / 3957)) (n := 12)
    (lo := (302840089 / 500000000)) (hi := (605680179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1397) = 1/(1397 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-605680179 / 1000000000) (-302840089 / 500000000) (Real.log (1397 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (647593959 / 1000000000) ≤ -Real.log (640 / 1223) ∧
    -Real.log (640 / 1223) ≤ (16189849 / 25000000) := by
  have h := checkLog_sound (w := (583 / 1863)) (n := 12)
    (lo := (647593959 / 1000000000)) (hi := (16189849 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1223 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1223 / 640) = 1/(640 / 1223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (647593959 / 1000000000) (16189849 / 25000000) (Real.log (1223 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1223 / 640) = -Real.log (640 / 1223) := by
    rw [show ((1223 / 640) : ℝ) = ((640 / 1223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1209208453 / 500000000) ≤ -Real.log (57 / 640) ∧
    -Real.log (57 / 640) ≤ (241841691 / 100000000) := by
  have h := checkLog_sound (w := (23 / 137)) (n := 12)
    (lo := (169487683 / 500000000)) (hi := (338975367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 57) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(80 / 57) = 1/(57 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-241841691 / 100000000) (-1209208453 / 500000000) (Real.log (57 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (323183357 / 500000000) ≤ -Real.log (1280 / 2443) ∧
    -Real.log (1280 / 2443) ≤ (129273343 / 200000000) := by
  have h := checkLog_sound (w := (1163 / 3723)) (n := 12)
    (lo := (323183357 / 500000000)) (hi := (129273343 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2443 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2443 / 1280) = 1/(1280 / 2443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (323183357 / 500000000) (129273343 / 200000000) (Real.log (2443 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2443 / 1280) = -Real.log (1280 / 2443) := by
    rw [show ((2443 / 1280) : ℝ) = ((1280 / 2443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (119622071 / 50000000) ≤ -Real.log (117 / 1280) ∧
    -Real.log (117 / 1280) ≤ (149527589 / 62500000) := by
  have h := checkLog_sound (w := (43 / 277)) (n := 12)
    (lo := (7824997 / 25000000)) (hi := (312999881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 117) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 117) = 1/(117 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-149527589 / 62500000) (-119622071 / 50000000) (Real.log (117 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (518983061 / 1000000000) ≤ -Real.log (500000 / 840159) ∧
    -Real.log (500000 / 840159) ≤ (259491531 / 500000000) := by
  have h := checkLog_sound (w := (340159 / 1340159)) (n := 12)
    (lo := (518983061 / 1000000000)) (hi := (259491531 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((840159 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(840159 / 500000) = 1/(500000 / 840159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (518983061 / 1000000000) (259491531 / 500000000) (Real.log (840159 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (840159 / 500000) = -Real.log (500000 / 840159) := by
    rw [show ((840159 / 500000) : ℝ) = ((500000 / 840159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (570214263 / 500000000) ≤ -Real.log (159841 / 500000) ∧
    -Real.log (159841 / 500000) ≤ (71276783 / 62500000) := by
  have h := checkLog_sound (w := (90159 / 409841)) (n := 12)
    (lo := (223640673 / 500000000)) (hi := (447281347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 159841) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 159841) = 1/(159841 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-71276783 / 62500000) (-570214263 / 500000000) (Real.log (159841 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (520262951 / 1000000000) ≤ -Real.log (100000 / 168247) ∧
    -Real.log (100000 / 168247) ≤ (65032869 / 125000000) := by
  have h := checkLog_sound (w := (68247 / 268247)) (n := 12)
    (lo := (520262951 / 1000000000)) (hi := (65032869 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168247 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168247 / 100000) = 1/(100000 / 168247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (520262951 / 1000000000) (65032869 / 125000000) (Real.log (168247 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (168247 / 100000) = -Real.log (100000 / 168247) := by
    rw [show ((168247 / 100000) : ℝ) = ((100000 / 168247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (8962367 / 7812500) ≤ -Real.log (31753 / 100000) ∧
    -Real.log (31753 / 100000) ≤ (573591489 / 500000000) := by
  have h := checkLog_sound (w := (18247 / 81753)) (n := 12)
    (lo := (113508949 / 250000000)) (hi := (454035797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 31753) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 31753) = 1/(31753 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-573591489 / 500000000) (-8962367 / 7812500) (Real.log (31753 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (438739329 / 1000000000) ≤ -Real.log (1000000 / 1550751) ∧
    -Real.log (1000000 / 1550751) ≤ (43873933 / 100000000) := by
  have h := checkLog_sound (w := (550751 / 2550751)) (n := 12)
    (lo := (438739329 / 1000000000)) (hi := (43873933 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1550751 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1550751 / 1000000) = 1/(1000000 / 1550751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (438739329 / 1000000000) (43873933 / 100000000) (Real.log (1550751 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1550751 / 1000000) = -Real.log (1000000 / 1550751) := by
    rw [show ((1550751 / 1000000) : ℝ) = ((1000000 / 1550751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (400088989 / 500000000) ≤ -Real.log (449249 / 1000000) ∧
    -Real.log (449249 / 1000000) ≤ (40008899 / 50000000) := by
  have h := checkLog_sound (w := (50751 / 949249)) (n := 12)
    (lo := (53515399 / 500000000)) (hi := (107030799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 449249) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 449249) = 1/(449249 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-40008899 / 50000000) (-400088989 / 500000000) (Real.log (449249 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (440179529 / 1000000000) ≤ -Real.log (500000 / 776493) ∧
    -Real.log (500000 / 776493) ≤ (44017953 / 100000000) := by
  have h := checkLog_sound (w := (276493 / 1276493)) (n := 12)
    (lo := (440179529 / 1000000000)) (hi := (44017953 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((776493 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(776493 / 500000) = 1/(500000 / 776493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (440179529 / 1000000000) (44017953 / 100000000) (Real.log (776493 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (776493 / 500000) = -Real.log (500000 / 776493) := by
    rw [show ((776493 / 500000) : ℝ) = ((500000 / 776493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (201291341 / 250000000) ≤ -Real.log (223507 / 500000) ∧
    -Real.log (223507 / 500000) ≤ (402582683 / 500000000) := by
  have h := checkLog_sound (w := (26493 / 473507)) (n := 12)
    (lo := (14002273 / 125000000)) (hi := (22403637 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 223507) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 223507) = 1/(223507 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-402582683 / 500000000) (-201291341 / 250000000) (Real.log (223507 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1659411587 / 1000000000) ≤ -Real.log (500000000000 / 2628108557879) ∧
    -Real.log (500000000000 / 2628108557879) ≤ (165941159 / 100000000) := by
  have h := checkLog_sound (w := (628108557879 / 4628108557879)) (n := 12)
    (lo := (273117227 / 1000000000)) (hi := (68279307 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2628108557879 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2628108557879 / 2000000000000) = 1/(500000000000 / 2628108557879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1659411587 / 1000000000) (165941159 / 100000000) (Real.log (2628108557879 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2628108557879 / 500000000000) = -Real.log (500000000000 / 2628108557879) := by
    rw [show ((2628108557879 / 500000000000) : ℝ) = ((500000000000 / 2628108557879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1667445927 / 1000000000) ≤ -Real.log (100000000000 / 529861745347) ∧
    -Real.log (100000000000 / 529861745347) ≤ (166744593 / 100000000) := by
  have h := checkLog_sound (w := (129861745347 / 929861745347)) (n := 12)
    (lo := (281151567 / 1000000000)) (hi := (17571973 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((529861745347 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(529861745347 / 400000000000) = 1/(100000000000 / 529861745347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1667445927 / 1000000000) (166744593 / 100000000) (Real.log (529861745347 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (529861745347 / 100000000000) = -Real.log (100000000000 / 529861745347) := by
    rw [show ((529861745347 / 100000000000) : ℝ) = ((100000000000 / 529861745347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (309729327 / 250000000) ≤ -Real.log (100000000000 / 345187412771) ∧
    -Real.log (100000000000 / 345187412771) ≤ (123891731 / 100000000) := by
  have h := checkLog_sound (w := (145187412771 / 545187412771)) (n := 12)
    (lo := (34110633 / 62500000)) (hi := (545770129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((345187412771 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(345187412771 / 200000000000) = 1/(100000000000 / 345187412771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (309729327 / 250000000) (123891731 / 100000000) (Real.log (345187412771 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (345187412771 / 100000000000) = -Real.log (100000000000 / 345187412771) := by
    rw [show ((345187412771 / 100000000000) : ℝ) = ((100000000000 / 345187412771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1245344893 / 1000000000) ≤ -Real.log (100000000000 / 347413280121) ∧
    -Real.log (100000000000 / 347413280121) ≤ (249068979 / 200000000) := by
  have h := checkLog_sound (w := (147413280121 / 547413280121)) (n := 12)
    (lo := (552197713 / 1000000000)) (hi := (276098857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347413280121 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(347413280121 / 200000000000) = 1/(100000000000 / 347413280121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1245344893 / 1000000000) (249068979 / 200000000) (Real.log (347413280121 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (347413280121 / 100000000000) = -Real.log (100000000000 / 347413280121) := by
    rw [show ((347413280121 / 100000000000) : ℝ) = ((100000000000 / 347413280121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0049

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0050Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0050
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

theorem reflection_log_1_neg : (46815317 / 125000000) ≤ -Real.log (2560 / 3723) ∧
    -Real.log (2560 / 3723) ≤ (374522537 / 1000000000) := by
  have h := checkLog_sound (w := (1163 / 6283)) (n := 12)
    (lo := (46815317 / 125000000)) (hi := (374522537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3723 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3723 / 2560) = 1/(2560 / 3723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (46815317 / 125000000) (374522537 / 1000000000) (Real.log (3723 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3723 / 2560) = -Real.log (2560 / 3723) := by
    rw [show ((3723 / 2560) : ℝ) = ((2560 / 3723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (302840089 / 500000000) ≤ -Real.log (1397 / 2560) ∧
    -Real.log (1397 / 2560) ≤ (605680179 / 1000000000) := by
  have h := checkLog_sound (w := (1163 / 3957)) (n := 12)
    (lo := (302840089 / 500000000)) (hi := (605680179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1397) = 1/(1397 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-605680179 / 1000000000) (-302840089 / 500000000) (Real.log (1397 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (373716409 / 1000000000) ≤ -Real.log (64 / 93) ∧
    -Real.log (64 / 93) ≤ (37371641 / 100000000) := by
  have h := checkLog_sound (w := (29 / 157)) (n := 12)
    (lo := (373716409 / 1000000000)) (hi := (37371641 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93 / 64) = 1/(64 / 93) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (373716409 / 1000000000) (37371641 / 100000000) (Real.log (93 / 64)) := by
  have h := reflection_log_3_neg
  have he : Real.log (93 / 64) = -Real.log (64 / 93) := by
    rw [show ((93 / 64) : ℝ) = ((64 / 93) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (603535021 / 1000000000) ≤ -Real.log (35 / 64) ∧
    -Real.log (35 / 64) ≤ (301767511 / 500000000) := by
  have h := checkLog_sound (w := (29 / 99)) (n := 12)
    (lo := (603535021 / 1000000000)) (hi := (301767511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 35) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 35) = 1/(35 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-301767511 / 500000000) (-603535021 / 1000000000) (Real.log (35 / 64)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (323183357 / 500000000) ≤ -Real.log (1280 / 2443) ∧
    -Real.log (1280 / 2443) ≤ (129273343 / 200000000) := by
  have h := checkLog_sound (w := (1163 / 3723)) (n := 12)
    (lo := (323183357 / 500000000)) (hi := (129273343 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2443 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2443 / 1280) = 1/(1280 / 2443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (323183357 / 500000000) (129273343 / 200000000) (Real.log (2443 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2443 / 1280) = -Real.log (1280 / 2443) := by
    rw [show ((2443 / 1280) : ℝ) = ((1280 / 2443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (119622071 / 50000000) ≤ -Real.log (117 / 1280) ∧
    -Real.log (117 / 1280) ≤ (149527589 / 62500000) := by
  have h := checkLog_sound (w := (43 / 277)) (n := 12)
    (lo := (7824997 / 25000000)) (hi := (312999881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 117) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 117) = 1/(117 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-149527589 / 62500000) (-119622071 / 50000000) (Real.log (117 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (645137961 / 1000000000) ≤ -Real.log (32 / 61) ∧
    -Real.log (32 / 61) ≤ (322568981 / 500000000) := by
  have h := checkLog_sound (w := (29 / 93)) (n := 12)
    (lo := (645137961 / 1000000000)) (hi := (322568981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61 / 32) = 1/(32 / 61) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (645137961 / 1000000000) (322568981 / 500000000) (Real.log (61 / 32)) := by
  have h := reflection_log_7_neg
  have he : Real.log (61 / 32) = -Real.log (32 / 61) := by
    rw [show ((61 / 32) : ℝ) = ((32 / 61) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (591780903 / 250000000) ≤ -Real.log (3 / 32) ∧
    -Real.log (3 / 32) ≤ (73972613 / 31250000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4 / 3) = 1/(3 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-73972613 / 31250000) (-591780903 / 250000000) (Real.log (3 / 32)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (103541617 / 200000000) ≤ -Real.log (1000000 / 1678177) ∧
    -Real.log (1000000 / 1678177) ≤ (258854043 / 500000000) := by
  have h := checkLog_sound (w := (678177 / 2678177)) (n := 12)
    (lo := (103541617 / 200000000)) (hi := (258854043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1678177 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1678177 / 1000000) = 1/(1000000 / 1678177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (103541617 / 200000000) (258854043 / 500000000) (Real.log (1678177 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1678177 / 1000000) = -Real.log (1000000 / 1678177) := by
    rw [show ((1678177 / 1000000) : ℝ) = ((1000000 / 1678177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1133753573 / 1000000000) ≤ -Real.log (321823 / 1000000) ∧
    -Real.log (321823 / 1000000) ≤ (45350143 / 40000000) := by
  have h := checkLog_sound (w := (178177 / 821823)) (n := 12)
    (lo := (440606393 / 1000000000)) (hi := (220303197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 321823) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 321823) = 1/(321823 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-45350143 / 40000000) (-1133753573 / 1000000000) (Real.log (321823 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (518984251 / 1000000000) ≤ -Real.log (3125 / 5251) ∧
    -Real.log (3125 / 5251) ≤ (129746063 / 250000000) := by
  have h := checkLog_sound (w := (1063 / 4188)) (n := 12)
    (lo := (518984251 / 1000000000)) (hi := (129746063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5251 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5251 / 3125) = 1/(3125 / 5251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (518984251 / 1000000000) (129746063 / 250000000) (Real.log (5251 / 3125)) := by
  have h := reflection_log_11_neg
  have he : Real.log (5251 / 3125) = -Real.log (3125 / 5251) := by
    rw [show ((5251 / 3125) : ℝ) = ((3125 / 5251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (570217391 / 500000000) ≤ -Real.log (999 / 3125) ∧
    -Real.log (999 / 3125) ≤ (35638587 / 31250000) := by
  have h := checkLog_sound (w := (1127 / 5123)) (n := 12)
    (lo := (223643801 / 500000000)) (hi := (447287603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1998) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(3125 / 1998) = 1/(999 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-35638587 / 31250000) (-570217391 / 500000000) (Real.log (999 / 3125)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (87461477 / 200000000) ≤ -Real.log (250000 / 387133) ∧
    -Real.log (250000 / 387133) ≤ (218653693 / 500000000) := by
  have h := checkLog_sound (w := (137133 / 637133)) (n := 12)
    (lo := (87461477 / 200000000)) (hi := (218653693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387133 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387133 / 250000) = 1/(250000 / 387133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (87461477 / 200000000) (218653693 / 500000000) (Real.log (387133 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (387133 / 250000) = -Real.log (250000 / 387133) := by
    rw [show ((387133 / 250000) : ℝ) = ((250000 / 387133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (397625391 / 500000000) ≤ -Real.log (112867 / 250000) ∧
    -Real.log (112867 / 250000) ≤ (24851587 / 31250000) := by
  have h := checkLog_sound (w := (12133 / 237867)) (n := 12)
    (lo := (51051801 / 500000000)) (hi := (102103603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112867) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 112867) = 1/(112867 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-24851587 / 31250000) (-397625391 / 500000000) (Real.log (112867 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (219369987 / 500000000) ≤ -Real.log (31250 / 48461) ∧
    -Real.log (31250 / 48461) ≤ (17549599 / 40000000) := by
  have h := checkLog_sound (w := (17211 / 79711)) (n := 12)
    (lo := (219369987 / 500000000)) (hi := (17549599 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48461 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48461 / 31250) = 1/(31250 / 48461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (219369987 / 500000000) (17549599 / 40000000) (Real.log (48461 / 31250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (48461 / 31250) = -Real.log (31250 / 48461) := by
    rw [show ((48461 / 31250) : ℝ) = ((31250 / 48461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (200045051 / 250000000) ≤ -Real.log (14039 / 31250) ∧
    -Real.log (14039 / 31250) ≤ (400090103 / 500000000) := by
  have h := checkLog_sound (w := (793 / 14832)) (n := 12)
    (lo := (1672391 / 15625000)) (hi := (4281321 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14039) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15625 / 14039) = 1/(14039 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-400090103 / 500000000) (-200045051 / 250000000) (Real.log (14039 / 31250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (825730829 / 500000000) ≤ -Real.log (500000000000 / 2607298111073) ∧
    -Real.log (500000000000 / 2607298111073) ≤ (1651461661 / 1000000000) := by
  have h := checkLog_sound (w := (607298111073 / 4607298111073)) (n := 12)
    (lo := (132583649 / 500000000)) (hi := (265167299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2607298111073 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2607298111073 / 2000000000000) = 1/(500000000000 / 2607298111073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (825730829 / 500000000) (1651461661 / 1000000000) (Real.log (2607298111073 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2607298111073 / 500000000000) = -Real.log (500000000000 / 2607298111073) := by
    rw [show ((2607298111073 / 500000000000) : ℝ) = ((500000000000 / 2607298111073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1659419033 / 1000000000) ≤ -Real.log (500000000000 / 2628128128129) ∧
    -Real.log (500000000000 / 2628128128129) ≤ (414854759 / 250000000) := by
  have h := checkLog_sound (w := (628128128129 / 4628128128129)) (n := 12)
    (lo := (273124673 / 1000000000)) (hi := (136562337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2628128128129 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2628128128129 / 2000000000000) = 1/(500000000000 / 2628128128129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1659419033 / 1000000000) (414854759 / 250000000) (Real.log (2628128128129 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2628128128129 / 500000000000) = -Real.log (500000000000 / 2628128128129) := by
    rw [show ((2628128128129 / 500000000000) : ℝ) = ((500000000000 / 2628128128129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (154069771 / 125000000) ≤ -Real.log (100000000000 / 342999282341) ∧
    -Real.log (100000000000 / 342999282341) ≤ (123255817 / 100000000) := by
  have h := checkLog_sound (w := (142999282341 / 542999282341)) (n := 12)
    (lo := (134852747 / 250000000)) (hi := (539410989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342999282341 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(342999282341 / 200000000000) = 1/(100000000000 / 342999282341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (154069771 / 125000000) (123255817 / 100000000) (Real.log (342999282341 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (342999282341 / 100000000000) = -Real.log (100000000000 / 342999282341) := by
    rw [show ((342999282341 / 100000000000) : ℝ) = ((100000000000 / 342999282341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1238920179 / 1000000000) ≤ -Real.log (500000000000 / 1725942018663) ∧
    -Real.log (500000000000 / 1725942018663) ≤ (1238920181 / 1000000000) := by
  have h := checkLog_sound (w := (725942018663 / 2725942018663)) (n := 12)
    (lo := (545772999 / 1000000000)) (hi := (545773 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1725942018663 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1725942018663 / 1000000000000) = 1/(500000000000 / 1725942018663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1238920179 / 1000000000) (1238920181 / 1000000000) (Real.log (1725942018663 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1725942018663 / 500000000000) = -Real.log (500000000000 / 1725942018663) := by
    rw [show ((1725942018663 / 500000000000) : ℝ) = ((500000000000 / 1725942018663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0050

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0051Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0051
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

theorem reflection_log_1_neg : (373716409 / 1000000000) ≤ -Real.log (64 / 93) ∧
    -Real.log (64 / 93) ≤ (37371641 / 100000000) := by
  have h := checkLog_sound (w := (29 / 157)) (n := 12)
    (lo := (373716409 / 1000000000)) (hi := (37371641 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93 / 64) = 1/(64 / 93) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (373716409 / 1000000000) (37371641 / 100000000) (Real.log (93 / 64)) := by
  have h := reflection_log_1_neg
  have he : Real.log (93 / 64) = -Real.log (64 / 93) := by
    rw [show ((93 / 64) : ℝ) = ((64 / 93) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (603535021 / 1000000000) ≤ -Real.log (35 / 64) ∧
    -Real.log (35 / 64) ≤ (301767511 / 500000000) := by
  have h := checkLog_sound (w := (29 / 99)) (n := 12)
    (lo := (603535021 / 1000000000)) (hi := (301767511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 35) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 35) = 1/(35 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-301767511 / 500000000) (-603535021 / 1000000000) (Real.log (35 / 64)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (5826713 / 15625000) ≤ -Real.log (2560 / 3717) ∧
    -Real.log (2560 / 3717) ≤ (372909633 / 1000000000) := by
  have h := checkLog_sound (w := (1157 / 6277)) (n := 12)
    (lo := (5826713 / 15625000)) (hi := (372909633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3717 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3717 / 2560) = 1/(2560 / 3717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (5826713 / 15625000) (372909633 / 1000000000) (Real.log (3717 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3717 / 2560) = -Real.log (2560 / 3717) := by
    rw [show ((3717 / 2560) : ℝ) = ((2560 / 3717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (601394457 / 1000000000) ≤ -Real.log (1403 / 2560) ∧
    -Real.log (1403 / 2560) ≤ (300697229 / 500000000) := by
  have h := checkLog_sound (w := (1157 / 3963)) (n := 12)
    (lo := (601394457 / 1000000000)) (hi := (300697229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1403) = 1/(1403 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-300697229 / 500000000) (-601394457 / 1000000000) (Real.log (1403 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (645137961 / 1000000000) ≤ -Real.log (32 / 61) ∧
    -Real.log (32 / 61) ≤ (322568981 / 500000000) := by
  have h := checkLog_sound (w := (29 / 93)) (n := 12)
    (lo := (645137961 / 1000000000)) (hi := (322568981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61 / 32) = 1/(32 / 61) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (645137961 / 1000000000) (322568981 / 500000000) (Real.log (61 / 32)) := by
  have h := reflection_log_5_neg
  have he : Real.log (61 / 32) = -Real.log (32 / 61) := by
    rw [show ((61 / 32) : ℝ) = ((32 / 61) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (591780903 / 250000000) ≤ -Real.log (3 / 32) ∧
    -Real.log (3 / 32) ≤ (73972613 / 31250000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4 / 3) = 1/(3 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-73972613 / 31250000) (-591780903 / 250000000) (Real.log (3 / 32)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (40244231 / 62500000) ≤ -Real.log (1280 / 2437) ∧
    -Real.log (1280 / 2437) ≤ (643907697 / 1000000000) := by
  have h := checkLog_sound (w := (1157 / 3717)) (n := 12)
    (lo := (40244231 / 62500000)) (hi := (643907697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2437 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2437 / 1280) = 1/(1280 / 2437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (40244231 / 62500000) (643907697 / 1000000000) (Real.log (2437 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2437 / 1280) = -Real.log (1280 / 2437) := by
    rw [show ((2437 / 1280) : ℝ) = ((1280 / 2437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2342430999 / 1000000000) ≤ -Real.log (123 / 1280) ∧
    -Real.log (123 / 1280) ≤ (2342431003 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 283)) (n := 12)
    (lo := (262989459 / 1000000000)) (hi := (13149473 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 123) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 123) = 1/(123 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2342431003 / 1000000000) (-2342430999 / 1000000000) (Real.log (123 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (258217829 / 500000000) ≤ -Real.log (1000000 / 1676043) ∧
    -Real.log (1000000 / 1676043) ≤ (516435659 / 1000000000) := by
  have h := checkLog_sound (w := (676043 / 2676043)) (n := 12)
    (lo := (258217829 / 500000000)) (hi := (516435659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1676043 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1676043 / 1000000) = 1/(1000000 / 1676043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (258217829 / 500000000) (516435659 / 1000000000) (Real.log (1676043 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1676043 / 1000000) = -Real.log (1000000 / 1676043) := by
    rw [show ((1676043 / 1000000) : ℝ) = ((1000000 / 1676043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1127144487 / 1000000000) ≤ -Real.log (323957 / 1000000) ∧
    -Real.log (323957 / 1000000) ≤ (1127144489 / 1000000000) := by
  have h := checkLog_sound (w := (176043 / 823957)) (n := 12)
    (lo := (433997307 / 1000000000)) (hi := (108499327 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 323957) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 323957) = 1/(323957 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1127144489 / 1000000000) (-1127144487 / 1000000000) (Real.log (323957 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (517708681 / 1000000000) ≤ -Real.log (500000 / 839089) ∧
    -Real.log (500000 / 839089) ≤ (258854341 / 500000000) := by
  have h := checkLog_sound (w := (339089 / 1339089)) (n := 12)
    (lo := (517708681 / 1000000000)) (hi := (258854341 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((839089 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(839089 / 500000) = 1/(500000 / 839089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (517708681 / 1000000000) (258854341 / 500000000) (Real.log (839089 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (839089 / 500000) = -Real.log (500000 / 839089) := by
    rw [show ((839089 / 500000) : ℝ) = ((500000 / 839089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (28343917 / 25000000) ≤ -Real.log (160911 / 500000) ∧
    -Real.log (160911 / 500000) ≤ (566878341 / 500000000) := by
  have h := checkLog_sound (w := (89089 / 410911)) (n := 12)
    (lo := (881219 / 2000000)) (hi := (440609501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 160911) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 160911) = 1/(160911 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-566878341 / 500000000) (-28343917 / 25000000) (Real.log (160911 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (217940897 / 500000000) ≤ -Real.log (500000 / 773163) ∧
    -Real.log (500000 / 773163) ≤ (87176359 / 200000000) := by
  have h := checkLog_sound (w := (273163 / 1273163)) (n := 12)
    (lo := (217940897 / 500000000)) (hi := (87176359 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((773163 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(773163 / 500000) = 1/(500000 / 773163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (217940897 / 500000000) (87176359 / 200000000) (Real.log (773163 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (773163 / 500000) = -Real.log (500000 / 773163) := by
    rw [show ((773163 / 500000) : ℝ) = ((500000 / 773163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (790376399 / 1000000000) ≤ -Real.log (226837 / 500000) ∧
    -Real.log (226837 / 500000) ≤ (790376401 / 1000000000) := by
  have h := checkLog_sound (w := (23163 / 476837)) (n := 12)
    (lo := (97229219 / 1000000000)) (hi := (4861461 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226837) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 226837) = 1/(226837 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-790376401 / 1000000000) (-790376399 / 1000000000) (Real.log (226837 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (437308031 / 1000000000) ≤ -Real.log (1000000 / 1548533) ∧
    -Real.log (1000000 / 1548533) ≤ (3416469 / 7812500) := by
  have h := checkLog_sound (w := (548533 / 2548533)) (n := 12)
    (lo := (437308031 / 1000000000)) (hi := (3416469 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1548533 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1548533 / 1000000) = 1/(1000000 / 1548533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (437308031 / 1000000000) (3416469 / 7812500) (Real.log (1548533 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1548533 / 1000000) = -Real.log (1000000 / 1548533) := by
    rw [show ((1548533 / 1000000) : ℝ) = ((1000000 / 1548533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (795252997 / 1000000000) ≤ -Real.log (451467 / 1000000) ∧
    -Real.log (451467 / 1000000) ≤ (795252999 / 1000000000) := by
  have h := checkLog_sound (w := (48533 / 951467)) (n := 12)
    (lo := (102105817 / 1000000000)) (hi := (51052909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451467) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 451467) = 1/(451467 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-795252999 / 1000000000) (-795252997 / 1000000000) (Real.log (451467 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (102723759 / 62500000) ≤ -Real.log (125000000000 / 646707356223) ∧
    -Real.log (125000000000 / 646707356223) ≤ (1643580147 / 1000000000) := by
  have h := checkLog_sound (w := (146707356223 / 1146707356223)) (n := 12)
    (lo := (32160723 / 125000000)) (hi := (51457157 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((646707356223 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(646707356223 / 500000000000) = 1/(125000000000 / 646707356223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (102723759 / 62500000) (1643580147 / 1000000000) (Real.log (646707356223 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (646707356223 / 125000000000) = -Real.log (125000000000 / 646707356223) := by
    rw [show ((646707356223 / 125000000000) : ℝ) = ((125000000000 / 646707356223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1651465361 / 1000000000) ≤ -Real.log (250000000000 / 1303653883203) ∧
    -Real.log (250000000000 / 1303653883203) ≤ (412866341 / 250000000) := by
  have h := checkLog_sound (w := (303653883203 / 2303653883203)) (n := 12)
    (lo := (265171001 / 1000000000)) (hi := (132585501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1303653883203 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1303653883203 / 1000000000000) = 1/(250000000000 / 1303653883203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1651465361 / 1000000000) (412866341 / 250000000) (Real.log (1303653883203 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1303653883203 / 250000000000) = -Real.log (250000000000 / 1303653883203) := by
    rw [show ((1303653883203 / 250000000000) : ℝ) = ((250000000000 / 1303653883203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (613129097 / 500000000) ≤ -Real.log (20000000000 / 68169037679) ∧
    -Real.log (20000000000 / 68169037679) ≤ (306564549 / 250000000) := by
  have h := checkLog_sound (w := (28169037679 / 108169037679)) (n := 12)
    (lo := (266555507 / 500000000)) (hi := (106622203 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68169037679 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(68169037679 / 40000000000) = 1/(20000000000 / 68169037679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (613129097 / 500000000) (306564549 / 250000000) (Real.log (68169037679 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (68169037679 / 20000000000) = -Real.log (20000000000 / 68169037679) := by
    rw [show ((68169037679 / 20000000000) : ℝ) = ((20000000000 / 68169037679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1232561029 / 1000000000) ≤ -Real.log (250000000000 / 857500658963) ∧
    -Real.log (250000000000 / 857500658963) ≤ (1232561031 / 1000000000) := by
  have h := checkLog_sound (w := (357500658963 / 1357500658963)) (n := 12)
    (lo := (539413849 / 1000000000)) (hi := (10788277 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((857500658963 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(857500658963 / 500000000000) = 1/(250000000000 / 857500658963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1232561029 / 1000000000) (1232561031 / 1000000000) (Real.log (857500658963 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (857500658963 / 250000000000) = -Real.log (250000000000 / 857500658963) := by
    rw [show ((857500658963 / 250000000000) : ℝ) = ((250000000000 / 857500658963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0051

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0052Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0052
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

theorem reflection_log_1_neg : (5826713 / 15625000) ≤ -Real.log (2560 / 3717) ∧
    -Real.log (2560 / 3717) ≤ (372909633 / 1000000000) := by
  have h := checkLog_sound (w := (1157 / 6277)) (n := 12)
    (lo := (5826713 / 15625000)) (hi := (372909633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3717 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3717 / 2560) = 1/(2560 / 3717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (5826713 / 15625000) (372909633 / 1000000000) (Real.log (3717 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3717 / 2560) = -Real.log (2560 / 3717) := by
    rw [show ((3717 / 2560) : ℝ) = ((2560 / 3717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (601394457 / 1000000000) ≤ -Real.log (1403 / 2560) ∧
    -Real.log (1403 / 2560) ≤ (300697229 / 500000000) := by
  have h := checkLog_sound (w := (1157 / 3963)) (n := 12)
    (lo := (601394457 / 1000000000)) (hi := (300697229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1403) = 1/(1403 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-300697229 / 500000000) (-601394457 / 1000000000) (Real.log (1403 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (93025551 / 250000000) ≤ -Real.log (1280 / 1857) ∧
    -Real.log (1280 / 1857) ≤ (74420441 / 200000000) := by
  have h := checkLog_sound (w := (577 / 3137)) (n := 12)
    (lo := (93025551 / 250000000)) (hi := (74420441 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1857 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1857 / 1280) = 1/(1280 / 1857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (93025551 / 250000000) (74420441 / 200000000) (Real.log (1857 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1857 / 1280) = -Real.log (1280 / 1857) := by
    rw [show ((1857 / 1280) : ℝ) = ((1280 / 1857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (119851693 / 200000000) ≤ -Real.log (703 / 1280) ∧
    -Real.log (703 / 1280) ≤ (299629233 / 500000000) := by
  have h := checkLog_sound (w := (577 / 1983)) (n := 12)
    (lo := (119851693 / 200000000)) (hi := (299629233 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 703) = 1/(703 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-299629233 / 500000000) (-119851693 / 200000000) (Real.log (703 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (40244231 / 62500000) ≤ -Real.log (1280 / 2437) ∧
    -Real.log (1280 / 2437) ≤ (643907697 / 1000000000) := by
  have h := checkLog_sound (w := (1157 / 3717)) (n := 12)
    (lo := (40244231 / 62500000)) (hi := (643907697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2437 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2437 / 1280) = 1/(1280 / 2437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (40244231 / 62500000) (643907697 / 1000000000) (Real.log (2437 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2437 / 1280) = -Real.log (1280 / 2437) := by
    rw [show ((2437 / 1280) : ℝ) = ((1280 / 2437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2342430999 / 1000000000) ≤ -Real.log (123 / 1280) ∧
    -Real.log (123 / 1280) ≤ (2342431003 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 283)) (n := 12)
    (lo := (262989459 / 1000000000)) (hi := (13149473 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 123) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 123) = 1/(123 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2342431003 / 1000000000) (-2342430999 / 1000000000) (Real.log (123 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (160668979 / 250000000) ≤ -Real.log (640 / 1217) ∧
    -Real.log (640 / 1217) ≤ (642675917 / 1000000000) := by
  have h := checkLog_sound (w := (577 / 1857)) (n := 12)
    (lo := (160668979 / 250000000)) (hi := (642675917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1217 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1217 / 640) = 1/(640 / 1217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (160668979 / 250000000) (642675917 / 1000000000) (Real.log (1217 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1217 / 640) = -Real.log (640 / 1217) := by
    rw [show ((1217 / 640) : ℝ) = ((640 / 1217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (289791681 / 125000000) ≤ -Real.log (63 / 640) ∧
    -Real.log (63 / 640) ≤ (579583363 / 250000000) := by
  have h := checkLog_sound (w := (17 / 143)) (n := 12)
    (lo := (59722977 / 250000000)) (hi := (238891909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 63) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(80 / 63) = 1/(63 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-579583363 / 250000000) (-289791681 / 125000000) (Real.log (63 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (257583493 / 500000000) ≤ -Real.log (500000 / 836959) ∧
    -Real.log (500000 / 836959) ≤ (515166987 / 1000000000) := by
  have h := checkLog_sound (w := (336959 / 1336959)) (n := 12)
    (lo := (257583493 / 500000000)) (hi := (515166987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((836959 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(836959 / 500000) = 1/(500000 / 836959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (257583493 / 500000000) (515166987 / 1000000000) (Real.log (836959 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (836959 / 500000) = -Real.log (500000 / 836959) := by
    rw [show ((836959 / 500000) : ℝ) = ((500000 / 836959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (560303197 / 500000000) ≤ -Real.log (163041 / 500000) ∧
    -Real.log (163041 / 500000) ≤ (280151599 / 250000000) := by
  have h := checkLog_sound (w := (86959 / 413041)) (n := 12)
    (lo := (213729607 / 500000000)) (hi := (85491843 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 163041) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 163041) = 1/(163041 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-280151599 / 250000000) (-560303197 / 500000000) (Real.log (163041 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (258218127 / 500000000) ≤ -Real.log (250000 / 419011) ∧
    -Real.log (250000 / 419011) ≤ (103287251 / 200000000) := by
  have h := checkLog_sound (w := (169011 / 669011)) (n := 12)
    (lo := (258218127 / 500000000)) (hi := (103287251 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((419011 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(419011 / 250000) = 1/(250000 / 419011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (258218127 / 500000000) (103287251 / 200000000) (Real.log (419011 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (419011 / 250000) = -Real.log (250000 / 419011) := by
    rw [show ((419011 / 250000) : ℝ) = ((250000 / 419011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (563573787 / 500000000) ≤ -Real.log (80989 / 250000) ∧
    -Real.log (80989 / 250000) ≤ (140893447 / 125000000) := by
  have h := checkLog_sound (w := (44011 / 205989)) (n := 12)
    (lo := (217000197 / 500000000)) (hi := (86800079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 80989) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 80989) = 1/(80989 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-140893447 / 125000000) (-563573787 / 500000000) (Real.log (80989 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (86892647 / 200000000) ≤ -Real.log (500000 / 772067) ∧
    -Real.log (500000 / 772067) ≤ (108615809 / 250000000) := by
  have h := checkLog_sound (w := (272067 / 1272067)) (n := 12)
    (lo := (86892647 / 200000000)) (hi := (108615809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((772067 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(772067 / 500000) = 1/(500000 / 772067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (86892647 / 200000000) (108615809 / 250000000) (Real.log (772067 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (772067 / 500000) = -Real.log (500000 / 772067) := by
    rw [show ((772067 / 500000) : ℝ) = ((500000 / 772067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (785556371 / 1000000000) ≤ -Real.log (227933 / 500000) ∧
    -Real.log (227933 / 500000) ≤ (785556373 / 1000000000) := by
  have h := checkLog_sound (w := (22067 / 477933)) (n := 12)
    (lo := (92409191 / 1000000000)) (hi := (11551149 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227933) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 227933) = 1/(227933 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-785556373 / 1000000000) (-785556371 / 1000000000) (Real.log (227933 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (435882441 / 1000000000) ≤ -Real.log (1000000 / 1546327) ∧
    -Real.log (1000000 / 1546327) ≤ (217941221 / 500000000) := by
  have h := checkLog_sound (w := (546327 / 2546327)) (n := 12)
    (lo := (435882441 / 1000000000)) (hi := (217941221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1546327 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1546327 / 1000000) = 1/(1000000 / 1546327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (435882441 / 1000000000) (217941221 / 500000000) (Real.log (1546327 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1546327 / 1000000) = -Real.log (1000000 / 1546327) := by
    rw [show ((1546327 / 1000000) : ℝ) = ((1000000 / 1546327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (197594651 / 250000000) ≤ -Real.log (453673 / 1000000) ∧
    -Real.log (453673 / 1000000) ≤ (395189303 / 500000000) := by
  have h := checkLog_sound (w := (46327 / 953673)) (n := 12)
    (lo := (1519241 / 15625000)) (hi := (3889257 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453673) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 453673) = 1/(453673 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-395189303 / 500000000) (-197594651 / 250000000) (Real.log (453673 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (81788669 / 50000000) ≤ -Real.log (125000000000 / 641678320177) ∧
    -Real.log (125000000000 / 641678320177) ≤ (1635773383 / 1000000000) := by
  have h := checkLog_sound (w := (141678320177 / 1141678320177)) (n := 12)
    (lo := (12473951 / 50000000)) (hi := (249479021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((641678320177 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(641678320177 / 500000000000) = 1/(125000000000 / 641678320177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (81788669 / 50000000) (1635773383 / 1000000000) (Real.log (641678320177 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (641678320177 / 125000000000) = -Real.log (125000000000 / 641678320177) := by
    rw [show ((641678320177 / 125000000000) : ℝ) = ((125000000000 / 641678320177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (410895957 / 250000000) ≤ -Real.log (500000000000 / 2586838953439) ∧
    -Real.log (500000000000 / 2586838953439) ≤ (1643583831 / 1000000000) := by
  have h := checkLog_sound (w := (586838953439 / 4586838953439)) (n := 12)
    (lo := (64322367 / 250000000)) (hi := (257289469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2586838953439 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2586838953439 / 2000000000000) = 1/(500000000000 / 2586838953439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (410895957 / 250000000) (1643583831 / 1000000000) (Real.log (2586838953439 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2586838953439 / 500000000000) = -Real.log (500000000000 / 2586838953439) := by
    rw [show ((2586838953439 / 500000000000) : ℝ) = ((500000000000 / 2586838953439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1220019607 / 1000000000) ≤ -Real.log (250000000000 / 846813537311) ∧
    -Real.log (250000000000 / 846813537311) ≤ (1220019609 / 1000000000) := by
  have h := checkLog_sound (w := (346813537311 / 1346813537311)) (n := 12)
    (lo := (526872427 / 1000000000)) (hi := (131718107 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((846813537311 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(846813537311 / 500000000000) = 1/(250000000000 / 846813537311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1220019607 / 1000000000) (1220019609 / 1000000000) (Real.log (846813537311 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (846813537311 / 250000000000) = -Real.log (250000000000 / 846813537311) := by
    rw [show ((846813537311 / 250000000000) : ℝ) = ((250000000000 / 846813537311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (245252209 / 200000000) ≤ -Real.log (500000000000 / 1704230800599) ∧
    -Real.log (500000000000 / 1704230800599) ≤ (1226261047 / 1000000000) := by
  have h := checkLog_sound (w := (704230800599 / 2704230800599)) (n := 12)
    (lo := (106622773 / 200000000)) (hi := (266556933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1704230800599 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1704230800599 / 1000000000000) = 1/(500000000000 / 1704230800599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (245252209 / 200000000) (1226261047 / 1000000000) (Real.log (1704230800599 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1704230800599 / 500000000000) = -Real.log (500000000000 / 1704230800599) := by
    rw [show ((1704230800599 / 500000000000) : ℝ) = ((500000000000 / 1704230800599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0052

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0053Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0053
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

theorem reflection_log_1_neg : (93025551 / 250000000) ≤ -Real.log (1280 / 1857) ∧
    -Real.log (1280 / 1857) ≤ (74420441 / 200000000) := by
  have h := checkLog_sound (w := (577 / 3137)) (n := 12)
    (lo := (93025551 / 250000000)) (hi := (74420441 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1857 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1857 / 1280) = 1/(1280 / 1857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (93025551 / 250000000) (74420441 / 200000000) (Real.log (1857 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1857 / 1280) = -Real.log (1280 / 1857) := by
    rw [show ((1857 / 1280) : ℝ) = ((1280 / 1857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (119851693 / 200000000) ≤ -Real.log (703 / 1280) ∧
    -Real.log (703 / 1280) ≤ (299629233 / 500000000) := by
  have h := checkLog_sound (w := (577 / 1983)) (n := 12)
    (lo := (119851693 / 200000000)) (hi := (299629233 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 703) = 1/(703 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-299629233 / 500000000) (-119851693 / 200000000) (Real.log (703 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (371294123 / 1000000000) ≤ -Real.log (2560 / 3711) ∧
    -Real.log (2560 / 3711) ≤ (92823531 / 250000000) := by
  have h := checkLog_sound (w := (1151 / 6271)) (n := 12)
    (lo := (371294123 / 1000000000)) (hi := (92823531 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3711 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3711 / 2560) = 1/(2560 / 3711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (371294123 / 1000000000) (92823531 / 250000000) (Real.log (3711 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3711 / 2560) = -Real.log (2560 / 3711) := by
    rw [show ((3711 / 2560) : ℝ) = ((2560 / 3711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (23885081 / 40000000) ≤ -Real.log (1409 / 2560) ∧
    -Real.log (1409 / 2560) ≤ (298563513 / 500000000) := by
  have h := checkLog_sound (w := (1151 / 3969)) (n := 12)
    (lo := (23885081 / 40000000)) (hi := (298563513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1409) = 1/(1409 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-298563513 / 500000000) (-23885081 / 40000000) (Real.log (1409 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (160668979 / 250000000) ≤ -Real.log (640 / 1217) ∧
    -Real.log (640 / 1217) ≤ (642675917 / 1000000000) := by
  have h := checkLog_sound (w := (577 / 1857)) (n := 12)
    (lo := (160668979 / 250000000)) (hi := (642675917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1217 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1217 / 640) = 1/(640 / 1217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (160668979 / 250000000) (642675917 / 1000000000) (Real.log (1217 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1217 / 640) = -Real.log (640 / 1217) := by
    rw [show ((1217 / 640) : ℝ) = ((640 / 1217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (289791681 / 125000000) ≤ -Real.log (63 / 640) ∧
    -Real.log (63 / 640) ≤ (579583363 / 250000000) := by
  have h := checkLog_sound (w := (17 / 143)) (n := 12)
    (lo := (59722977 / 250000000)) (hi := (238891909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 63) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(80 / 63) = 1/(63 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-579583363 / 250000000) (-289791681 / 125000000) (Real.log (63 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (641442617 / 1000000000) ≤ -Real.log (1280 / 2431) ∧
    -Real.log (1280 / 2431) ≤ (320721309 / 500000000) := by
  have h := checkLog_sound (w := (1151 / 3711)) (n := 12)
    (lo := (641442617 / 1000000000)) (hi := (320721309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2431 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2431 / 1280) = 1/(1280 / 2431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (641442617 / 1000000000) (320721309 / 500000000) (Real.log (2431 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2431 / 1280) = -Real.log (1280 / 2431) := by
    rw [show ((2431 / 1280) : ℝ) = ((1280 / 2431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (45896059 / 20000000) ≤ -Real.log (129 / 1280) ∧
    -Real.log (129 / 1280) ≤ (1147401477 / 500000000) := by
  have h := checkLog_sound (w := (31 / 289)) (n := 12)
    (lo := (21536141 / 100000000)) (hi := (215361411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 129) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 129) = 1/(129 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1147401477 / 500000000) (-45896059 / 20000000) (Real.log (129 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (32118843 / 62500000) ≤ -Real.log (1000000 / 1671801) ∧
    -Real.log (1000000 / 1671801) ≤ (513901489 / 1000000000) := by
  have h := checkLog_sound (w := (671801 / 2671801)) (n := 12)
    (lo := (32118843 / 62500000)) (hi := (513901489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1671801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1671801 / 1000000) = 1/(1000000 / 1671801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (32118843 / 62500000) (513901489 / 1000000000) (Real.log (1671801 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1671801 / 1000000) = -Real.log (1000000 / 1671801) := by
    rw [show ((1671801 / 1000000) : ℝ) = ((1000000 / 1671801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (557067573 / 500000000) ≤ -Real.log (328199 / 1000000) ∧
    -Real.log (328199 / 1000000) ≤ (278533787 / 250000000) := by
  have h := checkLog_sound (w := (171801 / 828199)) (n := 12)
    (lo := (210493983 / 500000000)) (hi := (420987967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 328199) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 328199) = 1/(328199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-278533787 / 250000000) (-557067573 / 500000000) (Real.log (328199 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (515167583 / 1000000000) ≤ -Real.log (1000000 / 1673919) ∧
    -Real.log (1000000 / 1673919) ≤ (16098987 / 31250000) := by
  have h := checkLog_sound (w := (673919 / 2673919)) (n := 12)
    (lo := (515167583 / 1000000000)) (hi := (16098987 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1673919 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1673919 / 1000000) = 1/(1000000 / 1673919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (515167583 / 1000000000) (16098987 / 31250000) (Real.log (1673919 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1673919 / 1000000) = -Real.log (1000000 / 1673919) := by
    rw [show ((1673919 / 1000000) : ℝ) = ((1000000 / 1673919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1120609461 / 1000000000) ≤ -Real.log (326081 / 1000000) ∧
    -Real.log (326081 / 1000000) ≤ (1120609463 / 1000000000) := by
  have h := checkLog_sound (w := (173919 / 826081)) (n := 12)
    (lo := (427462281 / 1000000000)) (hi := (213731141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 326081) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 326081) = 1/(326081 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1120609463 / 1000000000) (-1120609461 / 1000000000) (Real.log (326081 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (433050443 / 1000000000) ≤ -Real.log (500000 / 770977) ∧
    -Real.log (500000 / 770977) ≤ (108262611 / 250000000) := by
  have h := checkLog_sound (w := (270977 / 1270977)) (n := 12)
    (lo := (433050443 / 1000000000)) (hi := (108262611 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((770977 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(770977 / 500000) = 1/(500000 / 770977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (433050443 / 1000000000) (108262611 / 250000000) (Real.log (770977 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (770977 / 500000) = -Real.log (500000 / 770977) := by
    rw [show ((770977 / 500000) : ℝ) = ((500000 / 770977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (390392831 / 500000000) ≤ -Real.log (229023 / 500000) ∧
    -Real.log (229023 / 500000) ≤ (1524972 / 1953125) := by
  have h := checkLog_sound (w := (20977 / 479023)) (n := 12)
    (lo := (43819241 / 500000000)) (hi := (87638483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229023) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 229023) = 1/(229023 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1524972 / 1953125) (-390392831 / 500000000) (Real.log (229023 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (434463883 / 1000000000) ≤ -Real.log (200000 / 308827) ∧
    -Real.log (200000 / 308827) ≤ (108615971 / 250000000) := by
  have h := checkLog_sound (w := (108827 / 508827)) (n := 12)
    (lo := (434463883 / 1000000000)) (hi := (108615971 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308827 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(308827 / 200000) = 1/(200000 / 308827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (434463883 / 1000000000) (108615971 / 250000000) (Real.log (308827 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (308827 / 200000) = -Real.log (200000 / 308827) := by
    rw [show ((308827 / 200000) : ℝ) = ((200000 / 308827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (157111713 / 200000000) ≤ -Real.log (91173 / 200000) ∧
    -Real.log (91173 / 200000) ≤ (785558567 / 1000000000) := by
  have h := checkLog_sound (w := (8827 / 191173)) (n := 12)
    (lo := (18482277 / 200000000)) (hi := (46205693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 91173) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 91173) = 1/(91173 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-785558567 / 1000000000) (-157111713 / 200000000) (Real.log (91173 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (814018317 / 500000000) ≤ -Real.log (500000000000 / 2546931891931) ∧
    -Real.log (500000000000 / 2546931891931) ≤ (1628036637 / 1000000000) := by
  have h := checkLog_sound (w := (546931891931 / 4546931891931)) (n := 12)
    (lo := (120871137 / 500000000)) (hi := (9669691 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2546931891931 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2546931891931 / 2000000000000) = 1/(500000000000 / 2546931891931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (814018317 / 500000000) (1628036637 / 1000000000) (Real.log (2546931891931 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2546931891931 / 500000000000) = -Real.log (500000000000 / 2546931891931) := by
    rw [show ((2546931891931 / 500000000000) : ℝ) = ((500000000000 / 2546931891931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (408944261 / 250000000) ≤ -Real.log (125000000000 / 641680671367) ∧
    -Real.log (125000000000 / 641680671367) ≤ (1635777047 / 1000000000) := by
  have h := checkLog_sound (w := (141680671367 / 1141680671367)) (n := 12)
    (lo := (62370671 / 250000000)) (hi := (49896537 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((641680671367 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(641680671367 / 500000000000) = 1/(125000000000 / 641680671367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (408944261 / 250000000) (1635777047 / 1000000000) (Real.log (641680671367 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (641680671367 / 125000000000) = -Real.log (125000000000 / 641680671367) := by
    rw [show ((641680671367 / 125000000000) : ℝ) = ((125000000000 / 641680671367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (242767221 / 200000000) ≤ -Real.log (62500000000 / 210398355187) ∧
    -Real.log (62500000000 / 210398355187) ≤ (1213836107 / 1000000000) := by
  have h := checkLog_sound (w := (85398355187 / 335398355187)) (n := 12)
    (lo := (20827557 / 40000000)) (hi := (260344463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((210398355187 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(210398355187 / 125000000000) = 1/(62500000000 / 210398355187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (242767221 / 200000000) (1213836107 / 1000000000) (Real.log (210398355187 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (210398355187 / 62500000000) = -Real.log (62500000000 / 210398355187) := by
    rw [show ((210398355187 / 62500000000) : ℝ) = ((62500000000 / 210398355187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (76251403 / 62500000) ≤ -Real.log (250000000000 / 846815943317) ∧
    -Real.log (250000000000 / 846815943317) ≤ (24400449 / 20000000) := by
  have h := checkLog_sound (w := (346815943317 / 1346815943317)) (n := 12)
    (lo := (131718817 / 250000000)) (hi := (526875269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((846815943317 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(846815943317 / 500000000000) = 1/(250000000000 / 846815943317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (76251403 / 62500000) (24400449 / 20000000) (Real.log (846815943317 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (846815943317 / 250000000000) = -Real.log (250000000000 / 846815943317) := by
    rw [show ((846815943317 / 250000000000) : ℝ) = ((250000000000 / 846815943317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0053

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0054Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0054
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

theorem reflection_log_1_neg : (371294123 / 1000000000) ≤ -Real.log (2560 / 3711) ∧
    -Real.log (2560 / 3711) ≤ (92823531 / 250000000) := by
  have h := checkLog_sound (w := (1151 / 6271)) (n := 12)
    (lo := (371294123 / 1000000000)) (hi := (92823531 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3711 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3711 / 2560) = 1/(2560 / 3711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (371294123 / 1000000000) (92823531 / 250000000) (Real.log (3711 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3711 / 2560) = -Real.log (2560 / 3711) := by
    rw [show ((3711 / 2560) : ℝ) = ((2560 / 3711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (23885081 / 40000000) ≤ -Real.log (1409 / 2560) ∧
    -Real.log (1409 / 2560) ≤ (298563513 / 500000000) := by
  have h := checkLog_sound (w := (1151 / 3969)) (n := 12)
    (lo := (23885081 / 40000000)) (hi := (298563513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1409) = 1/(1409 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-298563513 / 500000000) (-23885081 / 40000000) (Real.log (1409 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (370485389 / 1000000000) ≤ -Real.log (640 / 927) ∧
    -Real.log (640 / 927) ≤ (37048539 / 100000000) := by
  have h := checkLog_sound (w := (287 / 1567)) (n := 12)
    (lo := (370485389 / 1000000000)) (hi := (37048539 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((927 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(927 / 640) = 1/(640 / 927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (370485389 / 1000000000) (37048539 / 100000000) (Real.log (927 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (927 / 640) = -Real.log (640 / 927) := by
    rw [show ((927 / 640) : ℝ) = ((640 / 927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (595000119 / 1000000000) ≤ -Real.log (353 / 640) ∧
    -Real.log (353 / 640) ≤ (14875003 / 25000000) := by
  have h := checkLog_sound (w := (287 / 993)) (n := 12)
    (lo := (595000119 / 1000000000)) (hi := (14875003 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 353) = 1/(353 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-14875003 / 25000000) (-595000119 / 1000000000) (Real.log (353 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (641442617 / 1000000000) ≤ -Real.log (1280 / 2431) ∧
    -Real.log (1280 / 2431) ≤ (320721309 / 500000000) := by
  have h := checkLog_sound (w := (1151 / 3711)) (n := 12)
    (lo := (641442617 / 1000000000)) (hi := (320721309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2431 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2431 / 1280) = 1/(1280 / 2431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (641442617 / 1000000000) (320721309 / 500000000) (Real.log (2431 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2431 / 1280) = -Real.log (1280 / 2431) := by
    rw [show ((2431 / 1280) : ℝ) = ((1280 / 2431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (45896059 / 20000000) ≤ -Real.log (129 / 1280) ∧
    -Real.log (129 / 1280) ≤ (1147401477 / 500000000) := by
  have h := checkLog_sound (w := (31 / 289)) (n := 12)
    (lo := (21536141 / 100000000)) (hi := (215361411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 129) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 129) = 1/(129 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1147401477 / 500000000) (-45896059 / 20000000) (Real.log (129 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (128041559 / 200000000) ≤ -Real.log (320 / 607) ∧
    -Real.log (320 / 607) ≤ (160051949 / 250000000) := by
  have h := checkLog_sound (w := (287 / 927)) (n := 12)
    (lo := (128041559 / 200000000)) (hi := (160051949 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607 / 320) = 1/(320 / 607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (128041559 / 200000000) (160051949 / 250000000) (Real.log (607 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (607 / 320) = -Real.log (320 / 607) := by
    rw [show ((607 / 320) : ℝ) = ((320 / 607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (283976679 / 125000000) ≤ -Real.log (33 / 320) ∧
    -Real.log (33 / 320) ≤ (567953359 / 250000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(40 / 33) = 1/(33 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-567953359 / 250000000) (-283976679 / 125000000) (Real.log (33 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (512638579 / 1000000000) ≤ -Real.log (1000000 / 1669691) ∧
    -Real.log (1000000 / 1669691) ≤ (25631929 / 50000000) := by
  have h := checkLog_sound (w := (669691 / 2669691)) (n := 12)
    (lo := (512638579 / 1000000000)) (hi := (25631929 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1669691 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1669691 / 1000000) = 1/(1000000 / 1669691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (512638579 / 1000000000) (25631929 / 50000000) (Real.log (1669691 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1669691 / 1000000) = -Real.log (1000000 / 1669691) := by
    rw [show ((1669691 / 1000000) : ℝ) = ((1000000 / 1669691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (553863349 / 500000000) ≤ -Real.log (330309 / 1000000) ∧
    -Real.log (330309 / 1000000) ≤ (11077267 / 10000000) := by
  have h := checkLog_sound (w := (169691 / 830309)) (n := 12)
    (lo := (207289759 / 500000000)) (hi := (414579519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 330309) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 330309) = 1/(330309 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-11077267 / 10000000) (-553863349 / 500000000) (Real.log (330309 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (256951043 / 500000000) ≤ -Real.log (500000 / 835901) ∧
    -Real.log (500000 / 835901) ≤ (513902087 / 1000000000) := by
  have h := checkLog_sound (w := (335901 / 1335901)) (n := 12)
    (lo := (256951043 / 500000000)) (hi := (513902087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((835901 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(835901 / 500000) = 1/(500000 / 835901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (256951043 / 500000000) (513902087 / 1000000000) (Real.log (835901 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (835901 / 500000) = -Real.log (500000 / 835901) := by
    rw [show ((835901 / 500000) : ℝ) = ((500000 / 835901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1114138193 / 1000000000) ≤ -Real.log (164099 / 500000) ∧
    -Real.log (164099 / 500000) ≤ (222827639 / 200000000) := by
  have h := checkLog_sound (w := (85901 / 414099)) (n := 12)
    (lo := (420991013 / 1000000000)) (hi := (210495507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 164099) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 164099) = 1/(164099 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-222827639 / 200000000) (-1114138193 / 1000000000) (Real.log (164099 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (86328819 / 200000000) ≤ -Real.log (1000000 / 1539787) ∧
    -Real.log (1000000 / 1539787) ≤ (6744439 / 15625000) := by
  have h := checkLog_sound (w := (539787 / 2539787)) (n := 12)
    (lo := (86328819 / 200000000)) (hi := (6744439 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1539787 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1539787 / 1000000) = 1/(1000000 / 1539787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (86328819 / 200000000) (6744439 / 15625000) (Real.log (1539787 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1539787 / 1000000) = -Real.log (1000000 / 1539787) := by
    rw [show ((1539787 / 1000000) : ℝ) = ((1000000 / 1539787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (194016463 / 250000000) ≤ -Real.log (460213 / 1000000) ∧
    -Real.log (460213 / 1000000) ≤ (388032927 / 500000000) := by
  have h := checkLog_sound (w := (39787 / 960213)) (n := 12)
    (lo := (5182417 / 62500000)) (hi := (82918673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460213) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 460213) = 1/(460213 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-388032927 / 500000000) (-194016463 / 250000000) (Real.log (460213 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (433051091 / 1000000000) ≤ -Real.log (200000 / 308391) ∧
    -Real.log (200000 / 308391) ≤ (108262773 / 250000000) := by
  have h := checkLog_sound (w := (108391 / 508391)) (n := 12)
    (lo := (433051091 / 1000000000)) (hi := (108262773 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308391 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(308391 / 200000) = 1/(200000 / 308391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (433051091 / 1000000000) (108262773 / 250000000) (Real.log (308391 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (308391 / 200000) = -Real.log (200000 / 308391) := by
    rw [show ((308391 / 200000) : ℝ) = ((200000 / 308391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (156157569 / 200000000) ≤ -Real.log (91609 / 200000) ∧
    -Real.log (91609 / 200000) ≤ (780787847 / 1000000000) := by
  have h := checkLog_sound (w := (8391 / 191609)) (n := 12)
    (lo := (17528133 / 200000000)) (hi := (43820333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 91609) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 91609) = 1/(91609 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-780787847 / 1000000000) (-156157569 / 200000000) (Real.log (91609 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1620365277 / 1000000000) ≤ -Real.log (31250000000 / 157966763697) ∧
    -Real.log (31250000000 / 157966763697) ≤ (10127283 / 6250000) := by
  have h := checkLog_sound (w := (32966763697 / 282966763697)) (n := 12)
    (lo := (234070917 / 1000000000)) (hi := (117035459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157966763697 / 125000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(157966763697 / 125000000000) = 1/(31250000000 / 157966763697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1620365277 / 1000000000) (10127283 / 6250000) (Real.log (157966763697 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (157966763697 / 31250000000) = -Real.log (31250000000 / 157966763697) := by
    rw [show ((157966763697 / 31250000000) : ℝ) = ((31250000000 / 157966763697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1628040279 / 1000000000) ≤ -Real.log (250000000000 / 1273470587877) ∧
    -Real.log (250000000000 / 1273470587877) ≤ (814020141 / 500000000) := by
  have h := checkLog_sound (w := (273470587877 / 2273470587877)) (n := 12)
    (lo := (241745919 / 1000000000)) (hi := (94432 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1273470587877 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1273470587877 / 1000000000000) = 1/(250000000000 / 1273470587877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1628040279 / 1000000000) (814020141 / 500000000) (Real.log (1273470587877 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1273470587877 / 250000000000) = -Real.log (250000000000 / 1273470587877) := by
    rw [show ((1273470587877 / 250000000000) : ℝ) = ((250000000000 / 1273470587877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1207709947 / 1000000000) ≤ -Real.log (62500000000 / 209113361639) ∧
    -Real.log (62500000000 / 209113361639) ≤ (1207709949 / 1000000000) := by
  have h := checkLog_sound (w := (84113361639 / 334113361639)) (n := 12)
    (lo := (514562767 / 1000000000)) (hi := (32160173 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((209113361639 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(209113361639 / 125000000000) = 1/(62500000000 / 209113361639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1207709947 / 1000000000) (1207709949 / 1000000000) (Real.log (209113361639 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (209113361639 / 62500000000) = -Real.log (62500000000 / 209113361639) := by
    rw [show ((209113361639 / 62500000000) : ℝ) = ((62500000000 / 209113361639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1213838937 / 1000000000) ≤ -Real.log (125000000000 / 420797901953) ∧
    -Real.log (125000000000 / 420797901953) ≤ (1213838939 / 1000000000) := by
  have h := checkLog_sound (w := (170797901953 / 670797901953)) (n := 12)
    (lo := (520691757 / 1000000000)) (hi := (260345879 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((420797901953 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(420797901953 / 250000000000) = 1/(125000000000 / 420797901953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1213838937 / 1000000000) (1213838939 / 1000000000) (Real.log (420797901953 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (420797901953 / 125000000000) = -Real.log (125000000000 / 420797901953) := by
    rw [show ((420797901953 / 125000000000) : ℝ) = ((125000000000 / 420797901953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0054

end


