-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0072Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0072Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:15:45.688243+00:00
-- url     : https://prove2.me/theorems/0c1875b0-72fa-4e46-99a3-bf4bbed789e2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0072Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0073Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0072Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0073Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0074Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0075Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0076Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0077Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0078Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0072Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0073Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0074Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0075Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0076Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0077Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0078Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0072Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0073Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0074Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0075Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0076Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0077Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0078Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0072Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0073Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0074Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0075Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0076Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0077Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0078Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0072Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0072
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

theorem reflection_log_1_neg : (8915897 / 25000000) ≤ -Real.log (2560 / 3657) ∧
    -Real.log (2560 / 3657) ≤ (356635881 / 1000000000) := by
  have h := checkLog_sound (w := (1097 / 6217)) (n := 12)
    (lo := (8915897 / 25000000)) (hi := (356635881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3657 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3657 / 2560) = 1/(2560 / 3657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (8915897 / 25000000) (356635881 / 1000000000) (Real.log (3657 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3657 / 2560) = -Real.log (2560 / 3657) := by
    rw [show ((3657 / 2560) : ℝ) = ((2560 / 3657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (69939767 / 125000000) ≤ -Real.log (1463 / 2560) ∧
    -Real.log (1463 / 2560) ≤ (559518137 / 1000000000) := by
  have h := checkLog_sound (w := (1097 / 4023)) (n := 12)
    (lo := (69939767 / 125000000)) (hi := (559518137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1463) = 1/(1463 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-559518137 / 1000000000) (-69939767 / 125000000) (Real.log (1463 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (355815199 / 1000000000) ≤ -Real.log (1280 / 1827) ∧
    -Real.log (1280 / 1827) ≤ (444769 / 1250000) := by
  have h := checkLog_sound (w := (547 / 3107)) (n := 12)
    (lo := (355815199 / 1000000000)) (hi := (444769 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1827 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1827 / 1280) = 1/(1280 / 1827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (355815199 / 1000000000) (444769 / 1250000) (Real.log (1827 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1827 / 1280) = -Real.log (1280 / 1827) := by
    rw [show ((1827 / 1280) : ℝ) = ((1280 / 1827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (111493931 / 200000000) ≤ -Real.log (733 / 1280) ∧
    -Real.log (733 / 1280) ≤ (69683707 / 125000000) := by
  have h := checkLog_sound (w := (547 / 2013)) (n := 12)
    (lo := (111493931 / 200000000)) (hi := (69683707 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 733) = 1/(733 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-69683707 / 125000000) (-111493931 / 200000000) (Real.log (733 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (61897911 / 100000000) ≤ -Real.log (1280 / 2377) ∧
    -Real.log (1280 / 2377) ≤ (618979111 / 1000000000) := by
  have h := checkLog_sound (w := (1097 / 3657)) (n := 12)
    (lo := (61897911 / 100000000)) (hi := (618979111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2377 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2377 / 1280) = 1/(1280 / 2377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (61897911 / 100000000) (618979111 / 1000000000) (Real.log (2377 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2377 / 1280) = -Real.log (1280 / 2377) := by
    rw [show ((2377 / 1280) : ℝ) = ((1280 / 2377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (972564601 / 500000000) ≤ -Real.log (183 / 1280) ∧
    -Real.log (183 / 1280) ≤ (389025841 / 200000000) := by
  have h := checkLog_sound (w := (137 / 503)) (n := 12)
    (lo := (279417421 / 500000000)) (hi := (558834843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 183) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 183) = 1/(183 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-389025841 / 200000000) (-972564601 / 500000000) (Real.log (183 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (308858109 / 500000000) ≤ -Real.log (640 / 1187) ∧
    -Real.log (640 / 1187) ≤ (617716219 / 1000000000) := by
  have h := checkLog_sound (w := (547 / 1827)) (n := 12)
    (lo := (308858109 / 500000000)) (hi := (617716219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1187 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1187 / 640) = 1/(640 / 1187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (308858109 / 500000000) (617716219 / 1000000000) (Real.log (1187 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1187 / 640) = -Real.log (640 / 1187) := by
    rw [show ((1187 / 640) : ℝ) = ((640 / 1187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (964434341 / 500000000) ≤ -Real.log (93 / 640) ∧
    -Real.log (93 / 640) ≤ (385773737 / 200000000) := by
  have h := checkLog_sound (w := (67 / 253)) (n := 12)
    (lo := (271287161 / 500000000)) (hi := (542574323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 93) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 93) = 1/(93 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-385773737 / 200000000) (-964434341 / 500000000) (Real.log (93 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (122575461 / 250000000) ≤ -Real.log (1000000 / 1632809) ∧
    -Real.log (1000000 / 1632809) ≤ (98060369 / 200000000) := by
  have h := checkLog_sound (w := (632809 / 2632809)) (n := 12)
    (lo := (122575461 / 250000000)) (hi := (98060369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1632809 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1632809 / 1000000) = 1/(1000000 / 1632809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (122575461 / 250000000) (98060369 / 200000000) (Real.log (1632809 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1632809 / 1000000) = -Real.log (1000000 / 1632809) := by
    rw [show ((1632809 / 1000000) : ℝ) = ((1000000 / 1632809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1001873129 / 1000000000) ≤ -Real.log (367191 / 1000000) ∧
    -Real.log (367191 / 1000000) ≤ (1001873131 / 1000000000) := by
  have h := checkLog_sound (w := (132809 / 867191)) (n := 12)
    (lo := (308725949 / 1000000000)) (hi := (6174519 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 367191) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 367191) = 1/(367191 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1001873131 / 1000000000) (-1001873129 / 1000000000) (Real.log (367191 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (491527813 / 1000000000) ≤ -Real.log (250000 / 408703) ∧
    -Real.log (250000 / 408703) ≤ (245763907 / 500000000) := by
  have h := checkLog_sound (w := (158703 / 658703)) (n := 12)
    (lo := (491527813 / 1000000000)) (hi := (245763907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((408703 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(408703 / 250000) = 1/(250000 / 408703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (491527813 / 1000000000) (245763907 / 500000000) (Real.log (408703 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (408703 / 250000) = -Real.log (250000 / 408703) := by
    rw [show ((408703 / 250000) : ℝ) = ((250000 / 408703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (251835747 / 250000000) ≤ -Real.log (91297 / 250000) ∧
    -Real.log (91297 / 250000) ≤ (100734299 / 100000000) := by
  have h := checkLog_sound (w := (33703 / 216297)) (n := 12)
    (lo := (9818619 / 31250000)) (hi := (314195809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 91297) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 91297) = 1/(91297 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-100734299 / 100000000) (-251835747 / 250000000) (Real.log (91297 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (20362509 / 50000000) ≤ -Real.log (25000 / 37567) ∧
    -Real.log (25000 / 37567) ≤ (407250181 / 1000000000) := by
  have h := checkLog_sound (w := (12567 / 62567)) (n := 12)
    (lo := (20362509 / 50000000)) (hi := (407250181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37567 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37567 / 25000) = 1/(25000 / 37567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (20362509 / 50000000) (407250181 / 1000000000) (Real.log (37567 / 25000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (37567 / 25000) = -Real.log (25000 / 37567) := by
    rw [show ((37567 / 25000) : ℝ) = ((25000 / 37567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (174630399 / 250000000) ≤ -Real.log (12433 / 25000) ∧
    -Real.log (12433 / 25000) ≤ (349260799 / 500000000) := by
  have h := checkLog_sound (w := (67 / 24933)) (n := 12)
    (lo := (335901 / 62500000)) (hi := (5374417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 12433) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(12500 / 12433) = 1/(12433 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-349260799 / 500000000) (-174630399 / 250000000) (Real.log (12433 / 25000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (204283147 / 500000000) ≤ -Real.log (1000000 / 1504659) ∧
    -Real.log (1000000 / 1504659) ≤ (81713259 / 200000000) := by
  have h := checkLog_sound (w := (504659 / 2504659)) (n := 12)
    (lo := (204283147 / 500000000)) (hi := (81713259 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1504659 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1504659 / 1000000) = 1/(1000000 / 1504659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (204283147 / 500000000) (81713259 / 200000000) (Real.log (1504659 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1504659 / 1000000) = -Real.log (1000000 / 1504659) := by
    rw [show ((1504659 / 1000000) : ℝ) = ((1000000 / 1504659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (10976701 / 15625000) ≤ -Real.log (495341 / 1000000) ∧
    -Real.log (495341 / 1000000) ≤ (351254433 / 500000000) := by
  have h := checkLog_sound (w := (4659 / 995341)) (n := 12)
    (lo := (2340421 / 250000000)) (hi := (1872337 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 495341) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 495341) = 1/(495341 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-351254433 / 500000000) (-10976701 / 15625000) (Real.log (495341 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1492174973 / 1000000000) ≤ -Real.log (500000000000 / 2223378296309) ∧
    -Real.log (500000000000 / 2223378296309) ≤ (11657617 / 7812500) := by
  have h := checkLog_sound (w := (223378296309 / 4223378296309)) (n := 12)
    (lo := (105880613 / 1000000000)) (hi := (52940307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2223378296309 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2223378296309 / 2000000000000) = 1/(500000000000 / 2223378296309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1492174973 / 1000000000) (11657617 / 7812500) (Real.log (2223378296309 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2223378296309 / 500000000000) = -Real.log (500000000000 / 2223378296309) := by
    rw [show ((2223378296309 / 500000000000) : ℝ) = ((500000000000 / 2223378296309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1498870801 / 1000000000) ≤ -Real.log (62500000000 / 279789450913) ∧
    -Real.log (62500000000 / 279789450913) ≤ (374717701 / 250000000) := by
  have h := checkLog_sound (w := (29789450913 / 529789450913)) (n := 12)
    (lo := (112576441 / 1000000000)) (hi := (56288221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279789450913 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(279789450913 / 250000000000) = 1/(62500000000 / 279789450913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1498870801 / 1000000000) (374717701 / 250000000) (Real.log (279789450913 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (279789450913 / 62500000000) = -Real.log (62500000000 / 279789450913) := by
    rw [show ((279789450913 / 62500000000) : ℝ) = ((62500000000 / 279789450913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4319421 / 3906250) ≤ -Real.log (12500000000 / 37769444221) ∧
    -Real.log (12500000000 / 37769444221) ≤ (552885889 / 500000000) := by
  have h := checkLog_sound (w := (12769444221 / 62769444221)) (n := 12)
    (lo := (103156149 / 250000000)) (hi := (412624597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37769444221 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(37769444221 / 25000000000) = 1/(12500000000 / 37769444221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4319421 / 3906250) (552885889 / 500000000) (Real.log (37769444221 / 12500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (37769444221 / 12500000000) = -Real.log (12500000000 / 37769444221) := by
    rw [show ((37769444221 / 12500000000) : ℝ) = ((12500000000 / 37769444221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (555537579 / 500000000) ≤ -Real.log (500000000000 / 1518811283541) ∧
    -Real.log (500000000000 / 1518811283541) ≤ (27776879 / 25000000) := by
  have h := checkLog_sound (w := (518811283541 / 2518811283541)) (n := 12)
    (lo := (208963989 / 500000000)) (hi := (417927979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1518811283541 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1518811283541 / 1000000000000) = 1/(500000000000 / 1518811283541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (555537579 / 500000000) (27776879 / 25000000) (Real.log (1518811283541 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1518811283541 / 500000000000) = -Real.log (500000000000 / 1518811283541) := by
    rw [show ((1518811283541 / 500000000000) : ℝ) = ((500000000000 / 1518811283541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0072

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0073Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0073
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

theorem reflection_log_1_neg : (355815199 / 1000000000) ≤ -Real.log (1280 / 1827) ∧
    -Real.log (1280 / 1827) ≤ (444769 / 1250000) := by
  have h := checkLog_sound (w := (547 / 3107)) (n := 12)
    (lo := (355815199 / 1000000000)) (hi := (444769 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1827 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1827 / 1280) = 1/(1280 / 1827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (355815199 / 1000000000) (444769 / 1250000) (Real.log (1827 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1827 / 1280) = -Real.log (1280 / 1827) := by
    rw [show ((1827 / 1280) : ℝ) = ((1280 / 1827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (111493931 / 200000000) ≤ -Real.log (733 / 1280) ∧
    -Real.log (733 / 1280) ≤ (69683707 / 125000000) := by
  have h := checkLog_sound (w := (547 / 2013)) (n := 12)
    (lo := (111493931 / 200000000)) (hi := (69683707 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 733) = 1/(733 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-69683707 / 125000000) (-111493931 / 200000000) (Real.log (733 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (88748461 / 250000000) ≤ -Real.log (2560 / 3651) ∧
    -Real.log (2560 / 3651) ≤ (70998769 / 200000000) := by
  have h := checkLog_sound (w := (1091 / 6211)) (n := 12)
    (lo := (88748461 / 250000000)) (hi := (70998769 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3651 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3651 / 2560) = 1/(2560 / 3651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (88748461 / 250000000) (70998769 / 200000000) (Real.log (3651 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3651 / 2560) = -Real.log (2560 / 3651) := by
    rw [show ((3651 / 2560) : ℝ) = ((2560 / 3651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (555425361 / 1000000000) ≤ -Real.log (1469 / 2560) ∧
    -Real.log (1469 / 2560) ≤ (277712681 / 500000000) := by
  have h := checkLog_sound (w := (1091 / 4029)) (n := 12)
    (lo := (555425361 / 1000000000)) (hi := (277712681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1469) = 1/(1469 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-277712681 / 500000000) (-555425361 / 1000000000) (Real.log (1469 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (308858109 / 500000000) ≤ -Real.log (640 / 1187) ∧
    -Real.log (640 / 1187) ≤ (617716219 / 1000000000) := by
  have h := checkLog_sound (w := (547 / 1827)) (n := 12)
    (lo := (308858109 / 500000000)) (hi := (617716219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1187 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1187 / 640) = 1/(640 / 1187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (308858109 / 500000000) (617716219 / 1000000000) (Real.log (1187 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1187 / 640) = -Real.log (640 / 1187) := by
    rw [show ((1187 / 640) : ℝ) = ((640 / 1187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (964434341 / 500000000) ≤ -Real.log (93 / 640) ∧
    -Real.log (93 / 640) ≤ (385773737 / 200000000) := by
  have h := checkLog_sound (w := (67 / 253)) (n := 12)
    (lo := (271287161 / 500000000)) (hi := (542574323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 93) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 93) = 1/(93 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-385773737 / 200000000) (-964434341 / 500000000) (Real.log (93 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (616451729 / 1000000000) ≤ -Real.log (1280 / 2371) ∧
    -Real.log (1280 / 2371) ≤ (61645173 / 100000000) := by
  have h := checkLog_sound (w := (1091 / 3651)) (n := 12)
    (lo := (616451729 / 1000000000)) (hi := (61645173 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2371 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2371 / 1280) = 1/(1280 / 2371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (616451729 / 1000000000) (61645173 / 100000000) (Real.log (2371 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2371 / 1280) = -Real.log (1280 / 2371) := by
    rw [show ((2371 / 1280) : ℝ) = ((1280 / 2371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (95643417 / 50000000) ≤ -Real.log (189 / 1280) ∧
    -Real.log (189 / 1280) ≤ (1912868343 / 1000000000) := by
  have h := checkLog_sound (w := (131 / 509)) (n := 12)
    (lo := (26328699 / 50000000)) (hi := (526573981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 189) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 189) = 1/(189 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1912868343 / 1000000000) (-95643417 / 50000000) (Real.log (189 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (489077437 / 1000000000) ≤ -Real.log (1000000 / 1630811) ∧
    -Real.log (1000000 / 1630811) ≤ (244538719 / 500000000) := by
  have h := checkLog_sound (w := (630811 / 2630811)) (n := 12)
    (lo := (489077437 / 1000000000)) (hi := (244538719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1630811 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1630811 / 1000000) = 1/(1000000 / 1630811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (489077437 / 1000000000) (244538719 / 500000000) (Real.log (1630811 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1630811 / 1000000) = -Real.log (1000000 / 1630811) := by
    rw [show ((1630811 / 1000000) : ℝ) = ((1000000 / 1630811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (99644657 / 100000000) ≤ -Real.log (369189 / 1000000) ∧
    -Real.log (369189 / 1000000) ≤ (249111643 / 250000000) := by
  have h := checkLog_sound (w := (130811 / 869189)) (n := 12)
    (lo := (30329939 / 100000000)) (hi := (303299391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 369189) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 369189) = 1/(369189 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-249111643 / 250000000) (-99644657 / 100000000) (Real.log (369189 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (61287807 / 125000000) ≤ -Real.log (100000 / 163281) ∧
    -Real.log (100000 / 163281) ≤ (490302457 / 1000000000) := by
  have h := checkLog_sound (w := (63281 / 263281)) (n := 12)
    (lo := (61287807 / 125000000)) (hi := (490302457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163281 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163281 / 100000) = 1/(100000 / 163281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (61287807 / 125000000) (490302457 / 1000000000) (Real.log (163281 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (163281 / 100000) = -Real.log (100000 / 163281) := by
    rw [show ((163281 / 100000) : ℝ) = ((100000 / 163281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1001875853 / 1000000000) ≤ -Real.log (36719 / 100000) ∧
    -Real.log (36719 / 100000) ≤ (200375171 / 200000000) := by
  have h := checkLog_sound (w := (13281 / 86719)) (n := 12)
    (lo := (308728673 / 1000000000)) (hi := (154364337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 36719) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 36719) = 1/(36719 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-200375171 / 200000000) (-1001875853 / 1000000000) (Real.log (36719 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (81187799 / 200000000) ≤ -Real.log (1000000 / 1500711) ∧
    -Real.log (1000000 / 1500711) ≤ (101484749 / 250000000) := by
  have h := checkLog_sound (w := (500711 / 2500711)) (n := 12)
    (lo := (81187799 / 200000000)) (hi := (101484749 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1500711 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1500711 / 1000000) = 1/(1000000 / 1500711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (81187799 / 200000000) (101484749 / 250000000) (Real.log (1500711 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1500711 / 1000000) = -Real.log (1000000 / 1500711) := by
    rw [show ((1500711 / 1000000) : ℝ) = ((1000000 / 1500711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (43410637 / 62500000) ≤ -Real.log (499289 / 1000000) ∧
    -Real.log (499289 / 1000000) ≤ (347285097 / 500000000) := by
  have h := checkLog_sound (w := (711 / 999289)) (n := 12)
    (lo := (355753 / 250000000)) (hi := (1423013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499289) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 499289) = 1/(499289 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-347285097 / 500000000) (-43410637 / 62500000) (Real.log (499289 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (203625423 / 500000000) ≤ -Real.log (1000000 / 1502681) ∧
    -Real.log (1000000 / 1502681) ≤ (407250847 / 1000000000) := by
  have h := checkLog_sound (w := (502681 / 2502681)) (n := 12)
    (lo := (203625423 / 500000000)) (hi := (407250847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1502681 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1502681 / 1000000) = 1/(1000000 / 1502681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (203625423 / 500000000) (407250847 / 1000000000) (Real.log (1502681 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1502681 / 1000000) = -Real.log (1000000 / 1502681) := by
    rw [show ((1502681 / 1000000) : ℝ) = ((1000000 / 1502681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (698523607 / 1000000000) ≤ -Real.log (497319 / 1000000) ∧
    -Real.log (497319 / 1000000) ≤ (698523609 / 1000000000) := by
  have h := checkLog_sound (w := (2681 / 997319)) (n := 12)
    (lo := (5376427 / 1000000000)) (hi := (1344107 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 497319) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 497319) = 1/(497319 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-698523609 / 1000000000) (-698523607 / 1000000000) (Real.log (497319 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (742762003 / 500000000) ≤ -Real.log (125000000000 / 552159937051) ∧
    -Real.log (125000000000 / 552159937051) ≤ (1485524009 / 1000000000) := by
  have h := checkLog_sound (w := (52159937051 / 1052159937051)) (n := 12)
    (lo := (49614823 / 500000000)) (hi := (99229647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((552159937051 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(552159937051 / 500000000000) = 1/(125000000000 / 552159937051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (742762003 / 500000000) (1485524009 / 1000000000) (Real.log (552159937051 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (552159937051 / 125000000000) = -Real.log (125000000000 / 552159937051) := by
    rw [show ((552159937051 / 125000000000) : ℝ) = ((125000000000 / 552159937051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1492178309 / 1000000000) ≤ -Real.log (500000000000 / 2223385713119) ∧
    -Real.log (500000000000 / 2223385713119) ≤ (186522289 / 125000000) := by
  have h := checkLog_sound (w := (223385713119 / 4223385713119)) (n := 12)
    (lo := (105883949 / 1000000000)) (hi := (2117679 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2223385713119 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2223385713119 / 2000000000000) = 1/(500000000000 / 2223385713119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1492178309 / 1000000000) (186522289 / 125000000) (Real.log (2223385713119 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2223385713119 / 500000000000) = -Real.log (500000000000 / 2223385713119) := by
    rw [show ((2223385713119 / 500000000000) : ℝ) = ((500000000000 / 2223385713119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1100509187 / 1000000000) ≤ -Real.log (250000000000 / 751424024963) ∧
    -Real.log (250000000000 / 751424024963) ≤ (1100509189 / 1000000000) := by
  have h := checkLog_sound (w := (251424024963 / 1251424024963)) (n := 12)
    (lo := (407362007 / 1000000000)) (hi := (50920251 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((751424024963 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(751424024963 / 500000000000) = 1/(250000000000 / 751424024963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1100509187 / 1000000000) (1100509189 / 1000000000) (Real.log (751424024963 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (751424024963 / 250000000000) = -Real.log (250000000000 / 751424024963) := by
    rw [show ((751424024963 / 250000000000) : ℝ) = ((250000000000 / 751424024963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1105774453 / 1000000000) ≤ -Real.log (500000000000 / 1510781812077) ∧
    -Real.log (500000000000 / 1510781812077) ≤ (221154891 / 200000000) := by
  have h := checkLog_sound (w := (510781812077 / 2510781812077)) (n := 12)
    (lo := (412627273 / 1000000000)) (hi := (206313637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1510781812077 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1510781812077 / 1000000000000) = 1/(500000000000 / 1510781812077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1105774453 / 1000000000) (221154891 / 200000000) (Real.log (1510781812077 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1510781812077 / 500000000000) = -Real.log (500000000000 / 1510781812077) := by
    rw [show ((1510781812077 / 500000000000) : ℝ) = ((500000000000 / 1510781812077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0073

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0074Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0074
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

theorem reflection_log_1_neg : (88748461 / 250000000) ≤ -Real.log (2560 / 3651) ∧
    -Real.log (2560 / 3651) ≤ (70998769 / 200000000) := by
  have h := checkLog_sound (w := (1091 / 6211)) (n := 12)
    (lo := (88748461 / 250000000)) (hi := (70998769 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3651 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3651 / 2560) = 1/(2560 / 3651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (88748461 / 250000000) (70998769 / 200000000) (Real.log (3651 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3651 / 2560) = -Real.log (2560 / 3651) := by
    rw [show ((3651 / 2560) : ℝ) = ((2560 / 3651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (555425361 / 1000000000) ≤ -Real.log (1469 / 2560) ∧
    -Real.log (1469 / 2560) ≤ (277712681 / 500000000) := by
  have h := checkLog_sound (w := (1091 / 4029)) (n := 12)
    (lo := (555425361 / 1000000000)) (hi := (277712681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1469) = 1/(1469 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-277712681 / 500000000) (-555425361 / 1000000000) (Real.log (1469 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (354171813 / 1000000000) ≤ -Real.log (40 / 57) ∧
    -Real.log (40 / 57) ≤ (177085907 / 500000000) := by
  have h := checkLog_sound (w := (17 / 97)) (n := 12)
    (lo := (354171813 / 1000000000)) (hi := (177085907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57 / 40) = 1/(40 / 57) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (354171813 / 1000000000) (177085907 / 500000000) (Real.log (57 / 40)) := by
  have h := reflection_log_3_neg
  have he : Real.log (57 / 40) = -Real.log (40 / 57) := by
    rw [show ((57 / 40) : ℝ) = ((40 / 57) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (276692619 / 500000000) ≤ -Real.log (23 / 40) ∧
    -Real.log (23 / 40) ≤ (553385239 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 63)) (n := 12)
    (lo := (276692619 / 500000000)) (hi := (553385239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 23) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 23) = 1/(23 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-553385239 / 1000000000) (-276692619 / 500000000) (Real.log (23 / 40)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (616451729 / 1000000000) ≤ -Real.log (1280 / 2371) ∧
    -Real.log (1280 / 2371) ≤ (61645173 / 100000000) := by
  have h := checkLog_sound (w := (1091 / 3651)) (n := 12)
    (lo := (616451729 / 1000000000)) (hi := (61645173 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2371 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2371 / 1280) = 1/(1280 / 2371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (616451729 / 1000000000) (61645173 / 100000000) (Real.log (2371 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2371 / 1280) = -Real.log (1280 / 2371) := by
    rw [show ((2371 / 1280) : ℝ) = ((1280 / 2371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (95643417 / 50000000) ≤ -Real.log (189 / 1280) ∧
    -Real.log (189 / 1280) ≤ (1912868343 / 1000000000) := by
  have h := checkLog_sound (w := (131 / 509)) (n := 12)
    (lo := (26328699 / 50000000)) (hi := (526573981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 189) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 189) = 1/(189 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1912868343 / 1000000000) (-95643417 / 50000000) (Real.log (189 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (615185639 / 1000000000) ≤ -Real.log (20 / 37) ∧
    -Real.log (20 / 37) ≤ (15379641 / 25000000) := by
  have h := checkLog_sound (w := (17 / 57)) (n := 12)
    (lo := (615185639 / 1000000000)) (hi := (15379641 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37 / 20) = 1/(20 / 37) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (615185639 / 1000000000) (15379641 / 25000000) (Real.log (37 / 20)) := by
  have h := reflection_log_7_neg
  have he : Real.log (37 / 20) = -Real.log (20 / 37) := by
    rw [show ((37 / 20) : ℝ) = ((20 / 37) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1897119983 / 1000000000) ≤ -Real.log (3 / 20) ∧
    -Real.log (3 / 20) ≤ (948559993 / 500000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(5 / 3) = 1/(3 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-948559993 / 500000000) (-1897119983 / 1000000000) (Real.log (3 / 20)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (243927299 / 500000000) ≤ -Real.log (500000 / 814409) ∧
    -Real.log (500000 / 814409) ≤ (487854599 / 1000000000) := by
  have h := checkLog_sound (w := (314409 / 1314409)) (n := 12)
    (lo := (243927299 / 500000000)) (hi := (487854599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((814409 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(814409 / 500000) = 1/(500000 / 814409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (243927299 / 500000000) (487854599 / 1000000000) (Real.log (814409 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (814409 / 500000) = -Real.log (500000 / 814409) := by
    rw [show ((814409 / 500000) : ℝ) = ((500000 / 814409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (99106277 / 100000000) ≤ -Real.log (185591 / 500000) ∧
    -Real.log (185591 / 500000) ≤ (247765693 / 250000000) := by
  have h := checkLog_sound (w := (64409 / 435591)) (n := 12)
    (lo := (29791559 / 100000000)) (hi := (297915591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 185591) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 185591) = 1/(185591 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-247765693 / 250000000) (-99106277 / 100000000) (Real.log (185591 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (9781561 / 20000000) ≤ -Real.log (250000 / 407703) ∧
    -Real.log (250000 / 407703) ≤ (489078051 / 1000000000) := by
  have h := checkLog_sound (w := (157703 / 657703)) (n := 12)
    (lo := (9781561 / 20000000)) (hi := (489078051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((407703 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(407703 / 250000) = 1/(250000 / 407703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (9781561 / 20000000) (489078051 / 1000000000) (Real.log (407703 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (407703 / 250000) = -Real.log (250000 / 407703) := by
    rw [show ((407703 / 250000) : ℝ) = ((250000 / 407703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (996449279 / 1000000000) ≤ -Real.log (92297 / 250000) ∧
    -Real.log (92297 / 250000) ≤ (996449281 / 1000000000) := by
  have h := checkLog_sound (w := (32703 / 217297)) (n := 12)
    (lo := (303302099 / 1000000000)) (hi := (3033021 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 92297) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 92297) = 1/(92297 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-996449281 / 1000000000) (-996449279 / 1000000000) (Real.log (92297 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (404631427 / 1000000000) ≤ -Real.log (800 / 1199) ∧
    -Real.log (800 / 1199) ≤ (101157857 / 250000000) := by
  have h := checkLog_sound (w := (399 / 1999)) (n := 12)
    (lo := (404631427 / 1000000000)) (hi := (101157857 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1199 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1199 / 800) = 1/(800 / 1199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (404631427 / 1000000000) (101157857 / 250000000) (Real.log (1199 / 800)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1199 / 800) = -Real.log (800 / 1199) := by
    rw [show ((1199 / 800) : ℝ) = ((800 / 1199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (6906503 / 10000000) ≤ -Real.log (401 / 800) ∧
    -Real.log (401 / 800) ≤ (690650301 / 1000000000) := by
  have h := checkLog_sound (w := (399 / 1201)) (n := 12)
    (lo := (6906503 / 10000000)) (hi := (690650301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800 / 401) = 1/(401 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-690650301 / 1000000000) (-6906503 / 10000000) (Real.log (401 / 800)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (202969831 / 500000000) ≤ -Real.log (125000 / 187589) ∧
    -Real.log (125000 / 187589) ≤ (405939663 / 1000000000) := by
  have h := checkLog_sound (w := (62589 / 312589)) (n := 12)
    (lo := (202969831 / 500000000)) (hi := (405939663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187589 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187589 / 125000) = 1/(125000 / 187589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (202969831 / 500000000) (405939663 / 1000000000) (Real.log (187589 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (187589 / 125000) = -Real.log (125000 / 187589) := by
    rw [show ((187589 / 125000) : ℝ) = ((125000 / 187589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (347286097 / 500000000) ≤ -Real.log (62411 / 125000) ∧
    -Real.log (62411 / 125000) ≤ (173643049 / 250000000) := by
  have h := checkLog_sound (w := (89 / 124911)) (n := 12)
    (lo := (712507 / 500000000)) (hi := (285003 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62411) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 62411) = 1/(62411 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-173643049 / 250000000) (-347286097 / 500000000) (Real.log (62411 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1478917367 / 1000000000) ≤ -Real.log (6250000000 / 27426201971) ∧
    -Real.log (6250000000 / 27426201971) ≤ (147891737 / 100000000) := by
  have h := checkLog_sound (w := (2426201971 / 52426201971)) (n := 12)
    (lo := (92623007 / 1000000000)) (hi := (2894469 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27426201971 / 25000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(27426201971 / 25000000000) = 1/(6250000000 / 27426201971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1478917367 / 1000000000) (147891737 / 100000000) (Real.log (27426201971 / 6250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (27426201971 / 6250000000) = -Real.log (6250000000 / 27426201971) := by
    rw [show ((27426201971 / 6250000000) : ℝ) = ((6250000000 / 27426201971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (46422729 / 31250000) ≤ -Real.log (100000000000 / 441729416991) ∧
    -Real.log (100000000000 / 441729416991) ≤ (1485527331 / 1000000000) := by
  have h := checkLog_sound (w := (41729416991 / 841729416991)) (n := 12)
    (lo := (12404121 / 125000000)) (hi := (99232969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((441729416991 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(441729416991 / 400000000000) = 1/(100000000000 / 441729416991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (46422729 / 31250000) (1485527331 / 1000000000) (Real.log (441729416991 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (441729416991 / 100000000000) = -Real.log (100000000000 / 441729416991) := by
    rw [show ((441729416991 / 100000000000) : ℝ) = ((100000000000 / 441729416991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1095281727 / 1000000000) ≤ -Real.log (500000000000 / 1495012468827) ∧
    -Real.log (500000000000 / 1495012468827) ≤ (1095281729 / 1000000000) := by
  have h := checkLog_sound (w := (495012468827 / 2495012468827)) (n := 12)
    (lo := (402134547 / 1000000000)) (hi := (100533637 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1495012468827 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1495012468827 / 1000000000000) = 1/(500000000000 / 1495012468827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1095281727 / 1000000000) (1095281729 / 1000000000) (Real.log (1495012468827 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1495012468827 / 500000000000) = -Real.log (500000000000 / 1495012468827) := by
    rw [show ((1495012468827 / 500000000000) : ℝ) = ((500000000000 / 1495012468827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1100511857 / 1000000000) ≤ -Real.log (62500000000 / 187856507667) ∧
    -Real.log (62500000000 / 187856507667) ≤ (1100511859 / 1000000000) := by
  have h := checkLog_sound (w := (62856507667 / 312856507667)) (n := 12)
    (lo := (407364677 / 1000000000)) (hi := (203682339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187856507667 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(187856507667 / 125000000000) = 1/(62500000000 / 187856507667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1100511857 / 1000000000) (1100511859 / 1000000000) (Real.log (187856507667 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (187856507667 / 62500000000) = -Real.log (62500000000 / 187856507667) := by
    rw [show ((187856507667 / 62500000000) : ℝ) = ((62500000000 / 187856507667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0074

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0075Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0075
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

theorem reflection_log_1_neg : (354171813 / 1000000000) ≤ -Real.log (40 / 57) ∧
    -Real.log (40 / 57) ≤ (177085907 / 500000000) := by
  have h := checkLog_sound (w := (17 / 97)) (n := 12)
    (lo := (354171813 / 1000000000)) (hi := (177085907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57 / 40) = 1/(40 / 57) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (354171813 / 1000000000) (177085907 / 500000000) (Real.log (57 / 40)) := by
  have h := reflection_log_1_neg
  have he : Real.log (57 / 40) = -Real.log (40 / 57) := by
    rw [show ((57 / 40) : ℝ) = ((40 / 57) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (276692619 / 500000000) ≤ -Real.log (23 / 40) ∧
    -Real.log (23 / 40) ≤ (553385239 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 63)) (n := 12)
    (lo := (276692619 / 500000000)) (hi := (553385239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 23) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 23) = 1/(23 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-553385239 / 1000000000) (-276692619 / 500000000) (Real.log (23 / 40)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (176674553 / 500000000) ≤ -Real.log (512 / 729) ∧
    -Real.log (512 / 729) ≤ (353349107 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 1241)) (n := 12)
    (lo := (176674553 / 500000000)) (hi := (353349107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729 / 512) = 1/(512 / 729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (176674553 / 500000000) (353349107 / 1000000000) (Real.log (729 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (729 / 512) = -Real.log (512 / 729) := by
    rw [show ((729 / 512) : ℝ) = ((512 / 729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (137837317 / 250000000) ≤ -Real.log (295 / 512) ∧
    -Real.log (295 / 512) ≤ (551349269 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 807)) (n := 12)
    (lo := (137837317 / 250000000)) (hi := (551349269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 295) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 295) = 1/(295 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-551349269 / 1000000000) (-137837317 / 250000000) (Real.log (295 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (615185639 / 1000000000) ≤ -Real.log (20 / 37) ∧
    -Real.log (20 / 37) ≤ (15379641 / 25000000) := by
  have h := checkLog_sound (w := (17 / 57)) (n := 12)
    (lo := (615185639 / 1000000000)) (hi := (15379641 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37 / 20) = 1/(20 / 37) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (615185639 / 1000000000) (15379641 / 25000000) (Real.log (37 / 20)) := by
  have h := reflection_log_5_neg
  have he : Real.log (37 / 20) = -Real.log (20 / 37) := by
    rw [show ((37 / 20) : ℝ) = ((20 / 37) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1897119983 / 1000000000) ≤ -Real.log (3 / 20) ∧
    -Real.log (3 / 20) ≤ (948559993 / 500000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(5 / 3) = 1/(3 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-948559993 / 500000000) (-1897119983 / 1000000000) (Real.log (3 / 20)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (76739743 / 125000000) ≤ -Real.log (256 / 473) ∧
    -Real.log (256 / 473) ≤ (122783589 / 200000000) := by
  have h := checkLog_sound (w := (217 / 729)) (n := 12)
    (lo := (76739743 / 125000000)) (hi := (122783589 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((473 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(473 / 256) = 1/(256 / 473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (76739743 / 125000000) (122783589 / 200000000) (Real.log (473 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (473 / 256) = -Real.log (256 / 473) := by
    rw [show ((473 / 256) : ℝ) = ((256 / 473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1881615797 / 1000000000) ≤ -Real.log (39 / 256) ∧
    -Real.log (39 / 256) ≤ (9408079 / 5000000) := by
  have h := checkLog_sound (w := (25 / 103)) (n := 12)
    (lo := (495321437 / 1000000000)) (hi := (247660719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 39) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 39) = 1/(39 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-9408079 / 5000000) (-1881615797 / 1000000000) (Real.log (39 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (97326667 / 200000000) ≤ -Real.log (100000 / 162683) ∧
    -Real.log (100000 / 162683) ≤ (60829167 / 125000000) := by
  have h := checkLog_sound (w := (62683 / 262683)) (n := 12)
    (lo := (97326667 / 200000000)) (hi := (60829167 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162683 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162683 / 100000) = 1/(100000 / 162683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (97326667 / 200000000) (60829167 / 125000000) (Real.log (162683 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (162683 / 100000) = -Real.log (100000 / 162683) := by
    rw [show ((162683 / 100000) : ℝ) = ((100000 / 162683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (492860599 / 500000000) ≤ -Real.log (37317 / 100000) ∧
    -Real.log (37317 / 100000) ≤ (2464303 / 2500000) := by
  have h := checkLog_sound (w := (12683 / 87317)) (n := 12)
    (lo := (146287009 / 500000000)) (hi := (292574019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 37317) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 37317) = 1/(37317 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2464303 / 2500000) (-492860599 / 500000000) (Real.log (37317 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (121963803 / 250000000) ≤ -Real.log (1000000 / 1628819) ∧
    -Real.log (1000000 / 1628819) ≤ (487855213 / 1000000000) := by
  have h := checkLog_sound (w := (628819 / 2628819)) (n := 12)
    (lo := (121963803 / 250000000)) (hi := (487855213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1628819 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1628819 / 1000000) = 1/(1000000 / 1628819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (121963803 / 250000000) (487855213 / 1000000000) (Real.log (1628819 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1628819 / 1000000) = -Real.log (1000000 / 1628819) := by
    rw [show ((1628819 / 1000000) : ℝ) = ((1000000 / 1628819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (123883183 / 125000000) ≤ -Real.log (371181 / 1000000) ∧
    -Real.log (371181 / 1000000) ≤ (495532733 / 500000000) := by
  have h := checkLog_sound (w := (128819 / 871181)) (n := 12)
    (lo := (74479571 / 250000000)) (hi := (59583657 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 371181) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 371181) = 1/(371181 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-495532733 / 500000000) (-123883183 / 125000000) (Real.log (371181 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (403328159 / 1000000000) ≤ -Real.log (500000 / 748399) ∧
    -Real.log (500000 / 748399) ≤ (2520801 / 6250000) := by
  have h := checkLog_sound (w := (248399 / 1248399)) (n := 12)
    (lo := (403328159 / 1000000000)) (hi := (2520801 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((748399 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(748399 / 500000) = 1/(500000 / 748399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (403328159 / 1000000000) (2520801 / 6250000) (Real.log (748399 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (748399 / 500000) = -Real.log (500000 / 748399) := by
    rw [show ((748399 / 500000) : ℝ) = ((500000 / 748399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (686763599 / 1000000000) ≤ -Real.log (251601 / 500000) ∧
    -Real.log (251601 / 500000) ≤ (1716909 / 2500000) := by
  have h := checkLog_sound (w := (248399 / 751601)) (n := 12)
    (lo := (686763599 / 1000000000)) (hi := (1716909 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 251601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 251601) = 1/(251601 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1716909 / 2500000) (-686763599 / 1000000000) (Real.log (251601 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (202316047 / 500000000) ≤ -Real.log (1000000 / 1498751) ∧
    -Real.log (1000000 / 1498751) ≤ (80926419 / 200000000) := by
  have h := checkLog_sound (w := (498751 / 2498751)) (n := 12)
    (lo := (202316047 / 500000000)) (hi := (80926419 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1498751 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1498751 / 1000000) = 1/(1000000 / 1498751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (202316047 / 500000000) (80926419 / 200000000) (Real.log (1498751 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1498751 / 1000000) = -Real.log (1000000 / 1498751) := by
    rw [show ((1498751 / 1000000) : ℝ) = ((1000000 / 1498751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (138130459 / 200000000) ≤ -Real.log (501249 / 1000000) ∧
    -Real.log (501249 / 1000000) ≤ (86331537 / 125000000) := by
  have h := checkLog_sound (w := (498751 / 1501249)) (n := 12)
    (lo := (138130459 / 200000000)) (hi := (86331537 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 501249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 501249) = 1/(501249 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-86331537 / 125000000) (-138130459 / 200000000) (Real.log (501249 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1472354533 / 1000000000) ≤ -Real.log (500000000000 / 2179743816491) ∧
    -Real.log (500000000000 / 2179743816491) ≤ (184044317 / 125000000) := by
  have h := checkLog_sound (w := (179743816491 / 4179743816491)) (n := 12)
    (lo := (86060173 / 1000000000)) (hi := (43030087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2179743816491 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2179743816491 / 2000000000000) = 1/(500000000000 / 2179743816491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1472354533 / 1000000000) (184044317 / 125000000) (Real.log (2179743816491 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2179743816491 / 500000000000) = -Real.log (500000000000 / 2179743816491) := by
    rw [show ((2179743816491 / 500000000000) : ℝ) = ((500000000000 / 2179743816491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (59156827 / 40000000) ≤ -Real.log (250000000000 / 1097051707927) ∧
    -Real.log (250000000000 / 1097051707927) ≤ (739460339 / 500000000) := by
  have h := checkLog_sound (w := (97051707927 / 2097051707927)) (n := 12)
    (lo := (18525263 / 200000000)) (hi := (23156579 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097051707927 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1097051707927 / 1000000000000) = 1/(250000000000 / 1097051707927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (59156827 / 40000000) (739460339 / 500000000) (Real.log (1097051707927 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1097051707927 / 250000000000) = -Real.log (250000000000 / 1097051707927) := by
    rw [show ((1097051707927 / 250000000000) : ℝ) = ((250000000000 / 1097051707927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (545045879 / 500000000) ≤ -Real.log (250000000000 / 743636750251) ∧
    -Real.log (250000000000 / 743636750251) ≤ (13626147 / 12500000) := by
  have h := checkLog_sound (w := (243636750251 / 1243636750251)) (n := 12)
    (lo := (198472289 / 500000000)) (hi := (396944579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743636750251 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(743636750251 / 500000000000) = 1/(250000000000 / 743636750251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (545045879 / 500000000) (13626147 / 12500000) (Real.log (743636750251 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (743636750251 / 250000000000) = -Real.log (250000000000 / 743636750251) := by
    rw [show ((743636750251 / 250000000000) : ℝ) = ((250000000000 / 743636750251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1095284389 / 1000000000) ≤ -Real.log (500000000000 / 1495016448911) ∧
    -Real.log (500000000000 / 1495016448911) ≤ (1095284391 / 1000000000) := by
  have h := checkLog_sound (w := (495016448911 / 2495016448911)) (n := 12)
    (lo := (402137209 / 1000000000)) (hi := (40213721 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1495016448911 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1495016448911 / 1000000000000) = 1/(500000000000 / 1495016448911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1095284389 / 1000000000) (1095284391 / 1000000000) (Real.log (1495016448911 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1495016448911 / 500000000000) = -Real.log (500000000000 / 1495016448911) := by
    rw [show ((1495016448911 / 500000000000) : ℝ) = ((500000000000 / 1495016448911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0075

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0076Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0076
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

theorem reflection_log_1_neg : (176674553 / 500000000) ≤ -Real.log (512 / 729) ∧
    -Real.log (512 / 729) ≤ (353349107 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 1241)) (n := 12)
    (lo := (176674553 / 500000000)) (hi := (353349107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729 / 512) = 1/(512 / 729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (176674553 / 500000000) (353349107 / 1000000000) (Real.log (729 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (729 / 512) = -Real.log (512 / 729) := by
    rw [show ((729 / 512) : ℝ) = ((512 / 729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (137837317 / 250000000) ≤ -Real.log (295 / 512) ∧
    -Real.log (295 / 512) ≤ (551349269 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 807)) (n := 12)
    (lo := (137837317 / 250000000)) (hi := (551349269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 295) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 295) = 1/(295 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-551349269 / 1000000000) (-137837317 / 250000000) (Real.log (295 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (176262861 / 500000000) ≤ -Real.log (1280 / 1821) ∧
    -Real.log (1280 / 1821) ≤ (352525723 / 1000000000) := by
  have h := checkLog_sound (w := (541 / 3101)) (n := 12)
    (lo := (176262861 / 500000000)) (hi := (352525723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1821 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1821 / 1280) = 1/(1280 / 1821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (176262861 / 500000000) (352525723 / 1000000000) (Real.log (1821 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1821 / 1280) = -Real.log (1280 / 1821) := by
    rw [show ((1821 / 1280) : ℝ) = ((1280 / 1821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (109863487 / 200000000) ≤ -Real.log (739 / 1280) ∧
    -Real.log (739 / 1280) ≤ (137329359 / 250000000) := by
  have h := checkLog_sound (w := (541 / 2019)) (n := 12)
    (lo := (109863487 / 200000000)) (hi := (137329359 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 739) = 1/(739 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-137329359 / 250000000) (-109863487 / 200000000) (Real.log (739 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (76739743 / 125000000) ≤ -Real.log (256 / 473) ∧
    -Real.log (256 / 473) ≤ (122783589 / 200000000) := by
  have h := checkLog_sound (w := (217 / 729)) (n := 12)
    (lo := (76739743 / 125000000)) (hi := (122783589 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((473 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(473 / 256) = 1/(256 / 473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (76739743 / 125000000) (122783589 / 200000000) (Real.log (473 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (473 / 256) = -Real.log (256 / 473) := by
    rw [show ((473 / 256) : ℝ) = ((256 / 473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1881615797 / 1000000000) ≤ -Real.log (39 / 256) ∧
    -Real.log (39 / 256) ≤ (9408079 / 5000000) := by
  have h := checkLog_sound (w := (25 / 103)) (n := 12)
    (lo := (495321437 / 1000000000)) (hi := (247660719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 39) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 39) = 1/(39 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-9408079 / 5000000) (-1881615797 / 1000000000) (Real.log (39 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (612648639 / 1000000000) ≤ -Real.log (640 / 1181) ∧
    -Real.log (640 / 1181) ≤ (1914527 / 3125000) := by
  have h := checkLog_sound (w := (541 / 1821)) (n := 12)
    (lo := (612648639 / 1000000000)) (hi := (1914527 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1181 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1181 / 640) = 1/(640 / 1181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (612648639 / 1000000000) (1914527 / 3125000) (Real.log (1181 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1181 / 640) = -Real.log (640 / 1181) := by
    rw [show ((1181 / 640) : ℝ) = ((640 / 1181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (74653933 / 40000000) ≤ -Real.log (99 / 640) ∧
    -Real.log (99 / 640) ≤ (233293541 / 125000000) := by
  have h := checkLog_sound (w := (61 / 259)) (n := 12)
    (lo := (96010793 / 200000000)) (hi := (240026983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 99) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 99) = 1/(99 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-233293541 / 125000000) (-74653933 / 40000000) (Real.log (99 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (242706521 / 500000000) ≤ -Real.log (500000 / 812423) ∧
    -Real.log (500000 / 812423) ≤ (485413043 / 1000000000) := by
  have h := checkLog_sound (w := (312423 / 1312423)) (n := 12)
    (lo := (242706521 / 500000000)) (hi := (485413043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((812423 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(812423 / 500000) = 1/(500000 / 812423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (242706521 / 500000000) (485413043 / 1000000000) (Real.log (812423 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (812423 / 500000) = -Real.log (500000 / 812423) := by
    rw [show ((812423 / 500000) : ℝ) = ((500000 / 812423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (98041867 / 100000000) ≤ -Real.log (187577 / 500000) ∧
    -Real.log (187577 / 500000) ≤ (61276167 / 62500000) := by
  have h := checkLog_sound (w := (62423 / 437577)) (n := 12)
    (lo := (28727149 / 100000000)) (hi := (287271491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 187577) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 187577) = 1/(187577 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-61276167 / 62500000) (-98041867 / 100000000) (Real.log (187577 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (9732679 / 20000000) ≤ -Real.log (1000000 / 1626831) ∧
    -Real.log (1000000 / 1626831) ≤ (486633951 / 1000000000) := by
  have h := checkLog_sound (w := (626831 / 2626831)) (n := 12)
    (lo := (9732679 / 20000000)) (hi := (486633951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1626831 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1626831 / 1000000) = 1/(1000000 / 1626831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (9732679 / 20000000) (486633951 / 1000000000) (Real.log (1626831 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1626831 / 1000000) = -Real.log (1000000 / 1626831) := by
    rw [show ((1626831 / 1000000) : ℝ) = ((1000000 / 1626831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (492861939 / 500000000) ≤ -Real.log (373169 / 1000000) ∧
    -Real.log (373169 / 1000000) ≤ (24643097 / 25000000) := by
  have h := checkLog_sound (w := (126831 / 873169)) (n := 12)
    (lo := (146288349 / 500000000)) (hi := (292576699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 373169) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 373169) = 1/(373169 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-24643097 / 25000000) (-492861939 / 500000000) (Real.log (373169 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (402028543 / 1000000000) ≤ -Real.log (500000 / 747427) ∧
    -Real.log (500000 / 747427) ≤ (785212 / 1953125) := by
  have h := checkLog_sound (w := (247427 / 1247427)) (n := 12)
    (lo := (402028543 / 1000000000)) (hi := (785212 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747427 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747427 / 500000) = 1/(500000 / 747427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (402028543 / 1000000000) (785212 / 1953125) (Real.log (747427 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (747427 / 500000) = -Real.log (500000 / 747427) := by
    rw [show ((747427 / 500000) : ℝ) = ((500000 / 747427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (341453891 / 500000000) ≤ -Real.log (252573 / 500000) ∧
    -Real.log (252573 / 500000) ≤ (682907783 / 1000000000) := by
  have h := checkLog_sound (w := (247427 / 752573)) (n := 12)
    (lo := (341453891 / 500000000)) (hi := (682907783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 252573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 252573) = 1/(252573 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-682907783 / 1000000000) (-341453891 / 500000000) (Real.log (252573 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (403328827 / 1000000000) ≤ -Real.log (1000000 / 1496799) ∧
    -Real.log (1000000 / 1496799) ≤ (100832207 / 250000000) := by
  have h := checkLog_sound (w := (496799 / 2496799)) (n := 12)
    (lo := (403328827 / 1000000000)) (hi := (100832207 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1496799 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1496799 / 1000000) = 1/(1000000 / 1496799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (403328827 / 1000000000) (100832207 / 250000000) (Real.log (1496799 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1496799 / 1000000) = -Real.log (1000000 / 1496799) := by
    rw [show ((1496799 / 1000000) : ℝ) = ((1000000 / 1496799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (343382793 / 500000000) ≤ -Real.log (503201 / 1000000) ∧
    -Real.log (503201 / 1000000) ≤ (686765587 / 1000000000) := by
  have h := checkLog_sound (w := (496799 / 1503201)) (n := 12)
    (lo := (343382793 / 500000000)) (hi := (686765587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 503201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 503201) = 1/(503201 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-686765587 / 1000000000) (-343382793 / 500000000) (Real.log (503201 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1465831711 / 1000000000) ≤ -Real.log (62500000000 / 270696500637) ∧
    -Real.log (62500000000 / 270696500637) ≤ (732915857 / 500000000) := by
  have h := checkLog_sound (w := (20696500637 / 520696500637)) (n := 12)
    (lo := (79537351 / 1000000000)) (hi := (9942169 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270696500637 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(270696500637 / 250000000000) = 1/(62500000000 / 270696500637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1465831711 / 1000000000) (732915857 / 500000000) (Real.log (270696500637 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (270696500637 / 62500000000) = -Real.log (62500000000 / 270696500637) := by
    rw [show ((270696500637 / 62500000000) : ℝ) = ((62500000000 / 270696500637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (368089457 / 250000000) ≤ -Real.log (250000000000 / 1089875498769) ∧
    -Real.log (250000000000 / 1089875498769) ≤ (1472357831 / 1000000000) := by
  have h := checkLog_sound (w := (89875498769 / 2089875498769)) (n := 12)
    (lo := (21515867 / 250000000)) (hi := (86063469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089875498769 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1089875498769 / 1000000000000) = 1/(250000000000 / 1089875498769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (368089457 / 250000000) (1472357831 / 1000000000) (Real.log (1089875498769 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1089875498769 / 250000000000) = -Real.log (250000000000 / 1089875498769) := by
    rw [show ((1089875498769 / 250000000000) : ℝ) = ((250000000000 / 1089875498769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (43397453 / 40000000) ≤ -Real.log (250000000000 / 739812846187) ∧
    -Real.log (250000000000 / 739812846187) ≤ (1084936327 / 1000000000) := by
  have h := checkLog_sound (w := (239812846187 / 1239812846187)) (n := 12)
    (lo := (78357829 / 200000000)) (hi := (195894573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739812846187 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(739812846187 / 500000000000) = 1/(250000000000 / 739812846187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (43397453 / 40000000) (1084936327 / 1000000000) (Real.log (739812846187 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (739812846187 / 250000000000) = -Real.log (250000000000 / 739812846187) := by
    rw [show ((739812846187 / 250000000000) : ℝ) = ((250000000000 / 739812846187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1090094413 / 1000000000) ≤ -Real.log (500000000000 / 1487277449767) ∧
    -Real.log (500000000000 / 1487277449767) ≤ (218018883 / 200000000) := by
  have h := checkLog_sound (w := (487277449767 / 2487277449767)) (n := 12)
    (lo := (396947233 / 1000000000)) (hi := (198473617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1487277449767 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1487277449767 / 1000000000000) = 1/(500000000000 / 1487277449767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1090094413 / 1000000000) (218018883 / 200000000) (Real.log (1487277449767 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1487277449767 / 500000000000) = -Real.log (500000000000 / 1487277449767) := by
    rw [show ((1487277449767 / 500000000000) : ℝ) = ((500000000000 / 1487277449767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0076

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0077Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0077
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

theorem reflection_log_1_neg : (176262861 / 500000000) ≤ -Real.log (1280 / 1821) ∧
    -Real.log (1280 / 1821) ≤ (352525723 / 1000000000) := by
  have h := checkLog_sound (w := (541 / 3101)) (n := 12)
    (lo := (176262861 / 500000000)) (hi := (352525723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1821 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1821 / 1280) = 1/(1280 / 1821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (176262861 / 500000000) (352525723 / 1000000000) (Real.log (1821 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1821 / 1280) = -Real.log (1280 / 1821) := by
    rw [show ((1821 / 1280) : ℝ) = ((1280 / 1821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (109863487 / 200000000) ≤ -Real.log (739 / 1280) ∧
    -Real.log (739 / 1280) ≤ (137329359 / 250000000) := by
  have h := checkLog_sound (w := (541 / 2019)) (n := 12)
    (lo := (109863487 / 200000000)) (hi := (137329359 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 739) = 1/(739 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-137329359 / 250000000) (-109863487 / 200000000) (Real.log (739 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (17585083 / 50000000) ≤ -Real.log (2560 / 3639) ∧
    -Real.log (2560 / 3639) ≤ (351701661 / 1000000000) := by
  have h := checkLog_sound (w := (1079 / 6199)) (n := 12)
    (lo := (17585083 / 50000000)) (hi := (351701661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3639 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3639 / 2560) = 1/(2560 / 3639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (17585083 / 50000000) (351701661 / 1000000000) (Real.log (3639 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3639 / 2560) = -Real.log (2560 / 3639) := by
    rw [show ((3639 / 2560) : ℝ) = ((2560 / 3639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (547289723 / 1000000000) ≤ -Real.log (1481 / 2560) ∧
    -Real.log (1481 / 2560) ≤ (136822431 / 250000000) := by
  have h := checkLog_sound (w := (1079 / 4041)) (n := 12)
    (lo := (547289723 / 1000000000)) (hi := (136822431 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1481) = 1/(1481 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-136822431 / 250000000) (-547289723 / 1000000000) (Real.log (1481 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (612648639 / 1000000000) ≤ -Real.log (640 / 1181) ∧
    -Real.log (640 / 1181) ≤ (1914527 / 3125000) := by
  have h := checkLog_sound (w := (541 / 1821)) (n := 12)
    (lo := (612648639 / 1000000000)) (hi := (1914527 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1181 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1181 / 640) = 1/(640 / 1181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (612648639 / 1000000000) (1914527 / 3125000) (Real.log (1181 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1181 / 640) = -Real.log (640 / 1181) := by
    rw [show ((1181 / 640) : ℝ) = ((640 / 1181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (74653933 / 40000000) ≤ -Real.log (99 / 640) ∧
    -Real.log (99 / 640) ≤ (233293541 / 125000000) := by
  have h := checkLog_sound (w := (61 / 259)) (n := 12)
    (lo := (96010793 / 200000000)) (hi := (240026983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 99) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 99) = 1/(99 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-233293541 / 125000000) (-74653933 / 40000000) (Real.log (99 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (305688861 / 500000000) ≤ -Real.log (1280 / 2359) ∧
    -Real.log (1280 / 2359) ≤ (611377723 / 1000000000) := by
  have h := checkLog_sound (w := (1079 / 3639)) (n := 12)
    (lo := (305688861 / 500000000)) (hi := (611377723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2359 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2359 / 1280) = 1/(1280 / 2359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (305688861 / 500000000) (611377723 / 1000000000) (Real.log (2359 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2359 / 1280) = -Real.log (1280 / 2359) := by
    rw [show ((2359 / 1280) : ℝ) = ((1280 / 2359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1851310447 / 1000000000) ≤ -Real.log (201 / 1280) ∧
    -Real.log (201 / 1280) ≤ (37026209 / 20000000) := by
  have h := checkLog_sound (w := (119 / 521)) (n := 12)
    (lo := (465016087 / 1000000000)) (hi := (58127011 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 201) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 201) = 1/(201 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-37026209 / 20000000) (-1851310447 / 1000000000) (Real.log (201 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (484193721 / 1000000000) ≤ -Real.log (500000 / 811433) ∧
    -Real.log (500000 / 811433) ≤ (242096861 / 500000000) := by
  have h := checkLog_sound (w := (311433 / 1311433)) (n := 12)
    (lo := (484193721 / 1000000000)) (hi := (242096861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((811433 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(811433 / 500000) = 1/(500000 / 811433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (484193721 / 1000000000) (242096861 / 500000000) (Real.log (811433 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (811433 / 500000) = -Real.log (500000 / 811433) := by
    rw [show ((811433 / 500000) : ℝ) = ((500000 / 811433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (243788679 / 250000000) ≤ -Real.log (188567 / 500000) ∧
    -Real.log (188567 / 500000) ≤ (487577359 / 500000000) := by
  have h := checkLog_sound (w := (61433 / 438567)) (n := 12)
    (lo := (17625471 / 62500000)) (hi := (282007537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 188567) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 188567) = 1/(188567 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-487577359 / 500000000) (-243788679 / 250000000) (Real.log (188567 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (485413657 / 1000000000) ≤ -Real.log (1000000 / 1624847) ∧
    -Real.log (1000000 / 1624847) ≤ (242706829 / 500000000) := by
  have h := checkLog_sound (w := (624847 / 2624847)) (n := 12)
    (lo := (485413657 / 1000000000)) (hi := (242706829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1624847 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1624847 / 1000000) = 1/(1000000 / 1624847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (485413657 / 1000000000) (242706829 / 500000000) (Real.log (1624847 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1624847 / 1000000) = -Real.log (1000000 / 1624847) := by
    rw [show ((1624847 / 1000000) : ℝ) = ((1000000 / 1624847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (196084267 / 200000000) ≤ -Real.log (375153 / 1000000) ∧
    -Real.log (375153 / 1000000) ≤ (980421337 / 1000000000) := by
  have h := checkLog_sound (w := (124847 / 875153)) (n := 12)
    (lo := (57454831 / 200000000)) (hi := (71818539 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 375153) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 375153) = 1/(375153 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-980421337 / 1000000000) (-196084267 / 200000000) (Real.log (375153 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (200366297 / 500000000) ≤ -Real.log (500000 / 746459) ∧
    -Real.log (500000 / 746459) ≤ (80146519 / 200000000) := by
  have h := checkLog_sound (w := (246459 / 1246459)) (n := 12)
    (lo := (200366297 / 500000000)) (hi := (80146519 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746459 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746459 / 500000) = 1/(500000 / 746459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (200366297 / 500000000) (80146519 / 200000000) (Real.log (746459 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (746459 / 500000) = -Real.log (500000 / 746459) := by
    rw [show ((746459 / 500000) : ℝ) = ((500000 / 746459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (84885319 / 125000000) ≤ -Real.log (253541 / 500000) ∧
    -Real.log (253541 / 500000) ≤ (679082553 / 1000000000) := by
  have h := checkLog_sound (w := (246459 / 753541)) (n := 12)
    (lo := (84885319 / 125000000)) (hi := (679082553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 253541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 253541) = 1/(253541 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-679082553 / 1000000000) (-84885319 / 125000000) (Real.log (253541 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (100507303 / 250000000) ≤ -Real.log (200000 / 298971) ∧
    -Real.log (200000 / 298971) ≤ (402029213 / 1000000000) := by
  have h := checkLog_sound (w := (98971 / 498971)) (n := 12)
    (lo := (100507303 / 250000000)) (hi := (402029213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298971 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298971 / 200000) = 1/(200000 / 298971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (100507303 / 250000000) (402029213 / 1000000000) (Real.log (298971 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (298971 / 200000) = -Real.log (200000 / 298971) := by
    rw [show ((298971 / 200000) : ℝ) = ((200000 / 298971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (341454881 / 500000000) ≤ -Real.log (101029 / 200000) ∧
    -Real.log (101029 / 200000) ≤ (682909763 / 1000000000) := by
  have h := checkLog_sound (w := (98971 / 301029)) (n := 12)
    (lo := (341454881 / 500000000)) (hi := (682909763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 101029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 101029) = 1/(101029 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-682909763 / 1000000000) (-341454881 / 500000000) (Real.log (101029 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1459348437 / 1000000000) ≤ -Real.log (500000000000 / 2151577423409) ∧
    -Real.log (500000000000 / 2151577423409) ≤ (36483711 / 25000000) := by
  have h := checkLog_sound (w := (151577423409 / 4151577423409)) (n := 12)
    (lo := (73054077 / 1000000000)) (hi := (36527039 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2151577423409 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2151577423409 / 2000000000000) = 1/(500000000000 / 2151577423409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1459348437 / 1000000000) (36483711 / 25000000) (Real.log (2151577423409 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2151577423409 / 500000000000) = -Real.log (500000000000 / 2151577423409) := by
    rw [show ((2151577423409 / 500000000000) : ℝ) = ((500000000000 / 2151577423409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (91614687 / 62500000) ≤ -Real.log (50000000000 / 216557911039) ∧
    -Real.log (50000000000 / 216557911039) ≤ (293166999 / 200000000) := by
  have h := checkLog_sound (w := (16557911039 / 416557911039)) (n := 12)
    (lo := (9942579 / 125000000)) (hi := (79540633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216557911039 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(216557911039 / 200000000000) = 1/(50000000000 / 216557911039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (91614687 / 62500000) (293166999 / 200000000) (Real.log (216557911039 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (216557911039 / 50000000000) = -Real.log (50000000000 / 216557911039) := by
    rw [show ((216557911039 / 50000000000) : ℝ) = ((50000000000 / 216557911039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (539907573 / 500000000) ≤ -Real.log (500000000000 / 1472067634031) ∧
    -Real.log (500000000000 / 1472067634031) ≤ (269953787 / 250000000) := by
  have h := checkLog_sound (w := (472067634031 / 2472067634031)) (n := 12)
    (lo := (193333983 / 500000000)) (hi := (386667967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1472067634031 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1472067634031 / 1000000000000) = 1/(500000000000 / 1472067634031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (539907573 / 500000000) (269953787 / 250000000) (Real.log (1472067634031 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1472067634031 / 500000000000) = -Real.log (500000000000 / 1472067634031) := by
    rw [show ((1472067634031 / 500000000000) : ℝ) = ((500000000000 / 1472067634031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1084938973 / 1000000000) ≤ -Real.log (5000000000 / 14796296113) ∧
    -Real.log (5000000000 / 14796296113) ≤ (43397559 / 40000000) := by
  have h := checkLog_sound (w := (4796296113 / 24796296113)) (n := 12)
    (lo := (391791793 / 1000000000)) (hi := (195895897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14796296113 / 10000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(14796296113 / 10000000000) = 1/(5000000000 / 14796296113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1084938973 / 1000000000) (43397559 / 40000000) (Real.log (14796296113 / 5000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (14796296113 / 5000000000) = -Real.log (5000000000 / 14796296113) := by
    rw [show ((14796296113 / 5000000000) : ℝ) = ((5000000000 / 14796296113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0077

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0078Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0078
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

theorem reflection_log_1_neg : (17585083 / 50000000) ≤ -Real.log (2560 / 3639) ∧
    -Real.log (2560 / 3639) ≤ (351701661 / 1000000000) := by
  have h := checkLog_sound (w := (1079 / 6199)) (n := 12)
    (lo := (17585083 / 50000000)) (hi := (351701661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3639 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3639 / 2560) = 1/(2560 / 3639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (17585083 / 50000000) (351701661 / 1000000000) (Real.log (3639 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3639 / 2560) = -Real.log (2560 / 3639) := by
    rw [show ((3639 / 2560) : ℝ) = ((2560 / 3639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (547289723 / 1000000000) ≤ -Real.log (1481 / 2560) ∧
    -Real.log (1481 / 2560) ≤ (136822431 / 250000000) := by
  have h := checkLog_sound (w := (1079 / 4041)) (n := 12)
    (lo := (547289723 / 1000000000)) (hi := (136822431 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1481) = 1/(1481 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-136822431 / 250000000) (-547289723 / 1000000000) (Real.log (1481 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (350876917 / 1000000000) ≤ -Real.log (640 / 909) ∧
    -Real.log (640 / 909) ≤ (175438459 / 500000000) := by
  have h := checkLog_sound (w := (269 / 1549)) (n := 12)
    (lo := (350876917 / 1000000000)) (hi := (175438459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((909 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(909 / 640) = 1/(640 / 909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (350876917 / 1000000000) (175438459 / 500000000) (Real.log (909 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (909 / 640) = -Real.log (640 / 909) := by
    rw [show ((909 / 640) : ℝ) = ((640 / 909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (545266113 / 1000000000) ≤ -Real.log (371 / 640) ∧
    -Real.log (371 / 640) ≤ (272633057 / 500000000) := by
  have h := checkLog_sound (w := (269 / 1011)) (n := 12)
    (lo := (545266113 / 1000000000)) (hi := (272633057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 371) = 1/(371 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-272633057 / 500000000) (-545266113 / 1000000000) (Real.log (371 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (305688861 / 500000000) ≤ -Real.log (1280 / 2359) ∧
    -Real.log (1280 / 2359) ≤ (611377723 / 1000000000) := by
  have h := checkLog_sound (w := (1079 / 3639)) (n := 12)
    (lo := (305688861 / 500000000)) (hi := (611377723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2359 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2359 / 1280) = 1/(1280 / 2359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (305688861 / 500000000) (611377723 / 1000000000) (Real.log (2359 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2359 / 1280) = -Real.log (1280 / 2359) := by
    rw [show ((2359 / 1280) : ℝ) = ((1280 / 2359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1851310447 / 1000000000) ≤ -Real.log (201 / 1280) ∧
    -Real.log (201 / 1280) ≤ (37026209 / 20000000) := by
  have h := checkLog_sound (w := (119 / 521)) (n := 12)
    (lo := (465016087 / 1000000000)) (hi := (58127011 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 201) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 201) = 1/(201 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-37026209 / 20000000) (-1851310447 / 1000000000) (Real.log (201 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (610105187 / 1000000000) ≤ -Real.log (320 / 589) ∧
    -Real.log (320 / 589) ≤ (152526297 / 250000000) := by
  have h := checkLog_sound (w := (269 / 909)) (n := 12)
    (lo := (610105187 / 1000000000)) (hi := (152526297 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589 / 320) = 1/(320 / 589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (610105187 / 1000000000) (152526297 / 250000000) (Real.log (589 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (589 / 320) = -Real.log (320 / 589) := by
    rw [show ((589 / 320) : ℝ) = ((320 / 589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1836495361 / 1000000000) ≤ -Real.log (51 / 320) ∧
    -Real.log (51 / 320) ≤ (459123841 / 250000000) := by
  have h := checkLog_sound (w := (29 / 131)) (n := 12)
    (lo := (450201001 / 1000000000)) (hi := (225100501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 51) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 51) = 1/(51 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-459123841 / 250000000) (-1836495361 / 1000000000) (Real.log (51 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (241487999 / 500000000) ≤ -Real.log (1000000 / 1620891) ∧
    -Real.log (1000000 / 1620891) ≤ (482975999 / 1000000000) := by
  have h := checkLog_sound (w := (620891 / 2620891)) (n := 12)
    (lo := (241487999 / 500000000)) (hi := (482975999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1620891 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1620891 / 1000000) = 1/(1000000 / 1620891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (241487999 / 500000000) (482975999 / 1000000000) (Real.log (1620891 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1620891 / 1000000) = -Real.log (1000000 / 1620891) := by
    rw [show ((1620891 / 1000000) : ℝ) = ((1000000 / 1620891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (193986303 / 200000000) ≤ -Real.log (379109 / 1000000) ∧
    -Real.log (379109 / 1000000) ≤ (969931517 / 1000000000) := by
  have h := checkLog_sound (w := (120891 / 879109)) (n := 12)
    (lo := (55356867 / 200000000)) (hi := (17299021 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 379109) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 379109) = 1/(379109 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-969931517 / 1000000000) (-193986303 / 200000000) (Real.log (379109 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (242097169 / 500000000) ≤ -Real.log (1000000 / 1622867) ∧
    -Real.log (1000000 / 1622867) ≤ (484194339 / 1000000000) := by
  have h := checkLog_sound (w := (622867 / 2622867)) (n := 12)
    (lo := (242097169 / 500000000)) (hi := (484194339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1622867 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1622867 / 1000000) = 1/(1000000 / 1622867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (242097169 / 500000000) (484194339 / 1000000000) (Real.log (1622867 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1622867 / 1000000) = -Real.log (1000000 / 1622867) := by
    rw [show ((1622867 / 1000000) : ℝ) = ((1000000 / 1622867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (121894671 / 125000000) ≤ -Real.log (377133 / 1000000) ∧
    -Real.log (377133 / 1000000) ≤ (97515737 / 100000000) := by
  have h := checkLog_sound (w := (122867 / 877133)) (n := 12)
    (lo := (70502547 / 250000000)) (hi := (282010189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 377133) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 377133) = 1/(377133 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-97515737 / 100000000) (-121894671 / 125000000) (Real.log (377133 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (399440999 / 1000000000) ≤ -Real.log (1000000 / 1490991) ∧
    -Real.log (1000000 / 1490991) ≤ (399441 / 1000000) := by
  have h := checkLog_sound (w := (490991 / 2490991)) (n := 12)
    (lo := (399440999 / 1000000000)) (hi := (399441 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1490991 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1490991 / 1000000) = 1/(1000000 / 1490991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (399440999 / 1000000000) (399441 / 1000000) (Real.log (1490991 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1490991 / 1000000) = -Real.log (1000000 / 1490991) := by
    rw [show ((1490991 / 1000000) : ℝ) = ((1000000 / 1490991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (33764479 / 50000000) ≤ -Real.log (509009 / 1000000) ∧
    -Real.log (509009 / 1000000) ≤ (675289581 / 1000000000) := by
  have h := checkLog_sound (w := (490991 / 1509009)) (n := 12)
    (lo := (33764479 / 50000000)) (hi := (675289581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 509009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 509009) = 1/(509009 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-675289581 / 1000000000) (-33764479 / 50000000) (Real.log (509009 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (400733933 / 1000000000) ≤ -Real.log (25000 / 37323) ∧
    -Real.log (25000 / 37323) ≤ (200366967 / 500000000) := by
  have h := checkLog_sound (w := (12323 / 62323)) (n := 12)
    (lo := (400733933 / 1000000000)) (hi := (200366967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37323 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37323 / 25000) = 1/(25000 / 37323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (400733933 / 1000000000) (200366967 / 500000000) (Real.log (37323 / 25000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (37323 / 25000) = -Real.log (25000 / 37323) := by
    rw [show ((37323 / 25000) : ℝ) = ((25000 / 37323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (21221453 / 31250000) ≤ -Real.log (12677 / 25000) ∧
    -Real.log (12677 / 25000) ≤ (679086497 / 1000000000) := by
  have h := checkLog_sound (w := (12323 / 37677)) (n := 12)
    (lo := (21221453 / 31250000)) (hi := (679086497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 12677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 12677) = 1/(12677 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-679086497 / 1000000000) (-21221453 / 31250000) (Real.log (12677 / 25000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1452907513 / 1000000000) ≤ -Real.log (62500000000 / 267220476169) ∧
    -Real.log (62500000000 / 267220476169) ≤ (363226879 / 250000000) := by
  have h := checkLog_sound (w := (17220476169 / 517220476169)) (n := 12)
    (lo := (66613153 / 1000000000)) (hi := (33306577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((267220476169 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(267220476169 / 250000000000) = 1/(62500000000 / 267220476169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1452907513 / 1000000000) (363226879 / 250000000) (Real.log (267220476169 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (267220476169 / 62500000000) = -Real.log (62500000000 / 267220476169) := by
    rw [show ((267220476169 / 62500000000) : ℝ) = ((62500000000 / 267220476169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (291870341 / 200000000) ≤ -Real.log (500000000000 / 2151584454291) ∧
    -Real.log (500000000000 / 2151584454291) ≤ (364837927 / 250000000) := by
  have h := checkLog_sound (w := (151584454291 / 4151584454291)) (n := 12)
    (lo := (14611469 / 200000000)) (hi := (36528673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2151584454291 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2151584454291 / 2000000000000) = 1/(500000000000 / 2151584454291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (291870341 / 200000000) (364837927 / 250000000) (Real.log (2151584454291 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2151584454291 / 500000000000) = -Real.log (500000000000 / 2151584454291) := by
    rw [show ((2151584454291 / 500000000000) : ℝ) = ((500000000000 / 2151584454291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1074730579 / 1000000000) ≤ -Real.log (500000000000 / 1464601804683) ∧
    -Real.log (500000000000 / 1464601804683) ≤ (1074730581 / 1000000000) := by
  have h := checkLog_sound (w := (464601804683 / 2464601804683)) (n := 12)
    (lo := (381583399 / 1000000000)) (hi := (1907917 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1464601804683 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1464601804683 / 1000000000000) = 1/(500000000000 / 1464601804683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1074730579 / 1000000000) (1074730581 / 1000000000) (Real.log (1464601804683 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1464601804683 / 500000000000) = -Real.log (500000000000 / 1464601804683) := by
    rw [show ((1464601804683 / 500000000000) : ℝ) = ((500000000000 / 1464601804683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (107982043 / 100000000) ≤ -Real.log (125000000000 / 368018853041) ∧
    -Real.log (125000000000 / 368018853041) ≤ (67488777 / 62500000) := by
  have h := checkLog_sound (w := (118018853041 / 618018853041)) (n := 12)
    (lo := (1546693 / 4000000)) (hi := (386673251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((368018853041 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(368018853041 / 250000000000) = 1/(125000000000 / 368018853041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (107982043 / 100000000) (67488777 / 62500000) (Real.log (368018853041 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (368018853041 / 125000000000) = -Real.log (125000000000 / 368018853041) := by
    rw [show ((368018853041 / 125000000000) : ℝ) = ((125000000000 / 368018853041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0078

end


