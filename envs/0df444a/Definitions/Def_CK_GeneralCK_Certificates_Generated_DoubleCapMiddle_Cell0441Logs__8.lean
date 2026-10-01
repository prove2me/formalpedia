-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0441Logs__8
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0441Logs__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:07:03.90393+00:00
-- url     : https://prove2.me/theorems/78f6b4c2-b653-4a6a-a60c-36d2c892b614
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0441Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0442Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0441Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0442Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0443Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0444Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0445Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0446Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0447Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0448Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0441Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0442Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0443Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0444Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0445Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0446Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0447Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0448Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0441Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0442Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0443Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0444Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0445Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0446Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0447Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0448Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0441Logs (+7 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0442Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0443Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0444Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0445Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0446Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0447Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0448Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0441Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0441
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

theorem reflection_log_1_neg : (38069183 / 200000000) ≤ -Real.log (10240 / 12387) ∧
    -Real.log (10240 / 12387) ≤ (47586479 / 250000000) := by
  have h := checkLog_sound (w := (2147 / 22627)) (n := 12)
    (lo := (38069183 / 200000000)) (hi := (47586479 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12387 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12387 / 10240) = 1/(10240 / 12387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (38069183 / 200000000) (47586479 / 250000000) (Real.log (12387 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12387 / 10240) = -Real.log (10240 / 12387) := by
    rw [show ((12387 / 10240) : ℝ) = ((10240 / 12387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (235302129 / 1000000000) ≤ -Real.log (8093 / 10240) ∧
    -Real.log (8093 / 10240) ≤ (23530213 / 100000000) := by
  have h := checkLog_sound (w := (2147 / 18333)) (n := 12)
    (lo := (235302129 / 1000000000)) (hi := (23530213 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8093) = 1/(8093 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-23530213 / 100000000) (-235302129 / 1000000000) (Real.log (8093 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (190103697 / 1000000000) ≤ -Real.log (320 / 387) ∧
    -Real.log (320 / 387) ≤ (95051849 / 500000000) := by
  have h := checkLog_sound (w := (67 / 707)) (n := 12)
    (lo := (190103697 / 1000000000)) (hi := (95051849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387 / 320) = 1/(320 / 387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (190103697 / 1000000000) (95051849 / 500000000) (Real.log (387 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (387 / 320) = -Real.log (320 / 387) := by
    rw [show ((387 / 320) : ℝ) = ((320 / 387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (234931507 / 1000000000) ≤ -Real.log (253 / 320) ∧
    -Real.log (253 / 320) ≤ (58732877 / 250000000) := by
  have h := checkLog_sound (w := (67 / 573)) (n := 12)
    (lo := (234931507 / 1000000000)) (hi := (58732877 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 253) = 1/(253 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-58732877 / 250000000) (-234931507 / 1000000000) (Real.log (253 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (43773639 / 125000000) ≤ -Real.log (5120 / 7267) ∧
    -Real.log (5120 / 7267) ≤ (350189113 / 1000000000) := by
  have h := checkLog_sound (w := (2147 / 12387)) (n := 12)
    (lo := (43773639 / 125000000)) (hi := (350189113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7267 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7267 / 5120) = 1/(5120 / 7267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (43773639 / 125000000) (350189113 / 1000000000) (Real.log (7267 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7267 / 5120) = -Real.log (5120 / 7267) := by
    rw [show ((7267 / 5120) : ℝ) = ((5120 / 7267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (108716579 / 200000000) ≤ -Real.log (2973 / 5120) ∧
    -Real.log (2973 / 5120) ≤ (33973931 / 62500000) := by
  have h := checkLog_sound (w := (2147 / 8093)) (n := 12)
    (lo := (108716579 / 200000000)) (hi := (33973931 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2973) = 1/(2973 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-33973931 / 62500000) (-108716579 / 200000000) (Real.log (2973 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (174888101 / 500000000) ≤ -Real.log (160 / 227) ∧
    -Real.log (160 / 227) ≤ (349776203 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 387)) (n := 12)
    (lo := (174888101 / 500000000)) (hi := (349776203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((227 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(227 / 160) = 1/(160 / 227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (174888101 / 500000000) (349776203 / 1000000000) (Real.log (227 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (227 / 160) = -Real.log (160 / 227) := by
    rw [show ((227 / 160) : ℝ) = ((160 / 227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (271287161 / 500000000) ≤ -Real.log (93 / 160) ∧
    -Real.log (93 / 160) ≤ (542574323 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 253)) (n := 12)
    (lo := (271287161 / 500000000)) (hi := (542574323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 93) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 93) = 1/(93 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-542574323 / 1000000000) (-271287161 / 500000000) (Real.log (93 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (261162003 / 1000000000) ≤ -Real.log (500000 / 649219) ∧
    -Real.log (500000 / 649219) ≤ (65290501 / 250000000) := by
  have h := checkLog_sound (w := (149219 / 1149219)) (n := 12)
    (lo := (261162003 / 1000000000)) (hi := (65290501 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((649219 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(649219 / 500000) = 1/(500000 / 649219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (261162003 / 1000000000) (65290501 / 250000000) (Real.log (649219 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (649219 / 500000) = -Real.log (500000 / 649219) := by
    rw [show ((649219 / 500000) : ℝ) = ((500000 / 649219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (354446001 / 1000000000) ≤ -Real.log (350781 / 500000) ∧
    -Real.log (350781 / 500000) ≤ (177223001 / 500000000) := by
  have h := checkLog_sound (w := (149219 / 850781)) (n := 12)
    (lo := (354446001 / 1000000000)) (hi := (177223001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 350781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 350781) = 1/(350781 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-177223001 / 500000000) (-354446001 / 1000000000) (Real.log (350781 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (130744633 / 500000000) ≤ -Real.log (1000000 / 1298863) ∧
    -Real.log (1000000 / 1298863) ≤ (261489267 / 1000000000) := by
  have h := checkLog_sound (w := (298863 / 2298863)) (n := 12)
    (lo := (130744633 / 500000000)) (hi := (261489267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1298863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1298863 / 1000000) = 1/(1000000 / 1298863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (130744633 / 500000000) (261489267 / 1000000000) (Real.log (1298863 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1298863 / 1000000) = -Real.log (1000000 / 1298863) := by
    rw [show ((1298863 / 1000000) : ℝ) = ((1000000 / 1298863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (14202079 / 40000000) ≤ -Real.log (701137 / 1000000) ∧
    -Real.log (701137 / 1000000) ≤ (44381497 / 125000000) := by
  have h := checkLog_sound (w := (298863 / 1701137)) (n := 12)
    (lo := (14202079 / 40000000)) (hi := (44381497 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 701137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 701137) = 1/(701137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-44381497 / 125000000) (-14202079 / 40000000) (Real.log (701137 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (97932629 / 500000000) ≤ -Real.log (1000000 / 1216363) ∧
    -Real.log (1000000 / 1216363) ≤ (195865259 / 1000000000) := by
  have h := checkLog_sound (w := (216363 / 2216363)) (n := 12)
    (lo := (97932629 / 500000000)) (hi := (195865259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1216363 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1216363 / 1000000) = 1/(1000000 / 1216363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (97932629 / 500000000) (195865259 / 1000000000) (Real.log (1216363 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1216363 / 1000000) = -Real.log (1000000 / 1216363) := by
    rw [show ((1216363 / 1000000) : ℝ) = ((1000000 / 1216363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (7619043 / 31250000) ≤ -Real.log (783637 / 1000000) ∧
    -Real.log (783637 / 1000000) ≤ (243809377 / 1000000000) := by
  have h := checkLog_sound (w := (216363 / 1783637)) (n := 12)
    (lo := (7619043 / 31250000)) (hi := (243809377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 783637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 783637) = 1/(783637 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-243809377 / 1000000000) (-7619043 / 31250000) (Real.log (783637 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (196132413 / 1000000000) ≤ -Real.log (62500 / 76043) ∧
    -Real.log (62500 / 76043) ≤ (98066207 / 500000000) := by
  have h := checkLog_sound (w := (13543 / 138543)) (n := 12)
    (lo := (196132413 / 1000000000)) (hi := (98066207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76043 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76043 / 62500) = 1/(62500 / 76043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (196132413 / 1000000000) (98066207 / 500000000) (Real.log (76043 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (76043 / 62500) = -Real.log (62500 / 76043) := by
    rw [show ((76043 / 62500) : ℝ) = ((62500 / 76043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (122112097 / 500000000) ≤ -Real.log (48957 / 62500) ∧
    -Real.log (48957 / 62500) ≤ (48844839 / 200000000) := by
  have h := checkLog_sound (w := (13543 / 111457)) (n := 12)
    (lo := (122112097 / 500000000)) (hi := (48844839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 48957) = 1/(48957 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-48844839 / 200000000) (-122112097 / 500000000) (Real.log (48957 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (153902001 / 250000000) ≤ -Real.log (500000000000 / 925390770879) ∧
    -Real.log (500000000000 / 925390770879) ≤ (123121601 / 200000000) := by
  have h := checkLog_sound (w := (425390770879 / 1425390770879)) (n := 12)
    (lo := (153902001 / 250000000)) (hi := (123121601 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((925390770879 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(925390770879 / 500000000000) = 1/(500000000000 / 925390770879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (153902001 / 250000000) (123121601 / 200000000) (Real.log (925390770879 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (925390770879 / 500000000000) = -Real.log (500000000000 / 925390770879) := by
    rw [show ((925390770879 / 500000000000) : ℝ) = ((500000000000 / 925390770879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (308270621 / 500000000) ≤ -Real.log (250000000000 / 463127391651) ∧
    -Real.log (250000000000 / 463127391651) ≤ (616541243 / 1000000000) := by
  have h := checkLog_sound (w := (213127391651 / 713127391651)) (n := 12)
    (lo := (308270621 / 500000000)) (hi := (616541243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((463127391651 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(463127391651 / 250000000000) = 1/(250000000000 / 463127391651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (308270621 / 500000000) (616541243 / 1000000000) (Real.log (463127391651 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (463127391651 / 250000000000) = -Real.log (250000000000 / 463127391651) := by
    rw [show ((463127391651 / 250000000000) : ℝ) = ((250000000000 / 463127391651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (219837317 / 500000000) ≤ -Real.log (50000000000 / 77610105189) ∧
    -Real.log (50000000000 / 77610105189) ≤ (87934927 / 200000000) := by
  have h := checkLog_sound (w := (27610105189 / 127610105189)) (n := 12)
    (lo := (219837317 / 500000000)) (hi := (87934927 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77610105189 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77610105189 / 50000000000) = 1/(50000000000 / 77610105189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (219837317 / 500000000) (87934927 / 200000000) (Real.log (77610105189 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (77610105189 / 50000000000) = -Real.log (50000000000 / 77610105189) := by
    rw [show ((77610105189 / 50000000000) : ℝ) = ((50000000000 / 77610105189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (440356607 / 1000000000) ≤ -Real.log (500000000000 / 776630512491) ∧
    -Real.log (500000000000 / 776630512491) ≤ (1720143 / 3906250) := by
  have h := checkLog_sound (w := (276630512491 / 1276630512491)) (n := 12)
    (lo := (440356607 / 1000000000)) (hi := (1720143 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((776630512491 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(776630512491 / 500000000000) = 1/(500000000000 / 776630512491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (440356607 / 1000000000) (1720143 / 3906250) (Real.log (776630512491 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (776630512491 / 500000000000) = -Real.log (500000000000 / 776630512491) := by
    rw [show ((776630512491 / 500000000000) : ℝ) = ((500000000000 / 776630512491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0441

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0442Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0442
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

theorem reflection_log_1_neg : (190103697 / 1000000000) ≤ -Real.log (320 / 387) ∧
    -Real.log (320 / 387) ≤ (95051849 / 500000000) := by
  have h := checkLog_sound (w := (67 / 707)) (n := 12)
    (lo := (190103697 / 1000000000)) (hi := (95051849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387 / 320) = 1/(320 / 387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (190103697 / 1000000000) (95051849 / 500000000) (Real.log (387 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (387 / 320) = -Real.log (320 / 387) := by
    rw [show ((387 / 320) : ℝ) = ((320 / 387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (234931507 / 1000000000) ≤ -Real.log (253 / 320) ∧
    -Real.log (253 / 320) ≤ (58732877 / 250000000) := by
  have h := checkLog_sound (w := (67 / 573)) (n := 12)
    (lo := (234931507 / 1000000000)) (hi := (58732877 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 253) = 1/(253 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-58732877 / 250000000) (-234931507 / 1000000000) (Real.log (253 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (189861419 / 1000000000) ≤ -Real.log (10240 / 12381) ∧
    -Real.log (10240 / 12381) ≤ (9493071 / 50000000) := by
  have h := checkLog_sound (w := (2141 / 22621)) (n := 12)
    (lo := (189861419 / 1000000000)) (hi := (9493071 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12381 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12381 / 10240) = 1/(10240 / 12381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (189861419 / 1000000000) (9493071 / 50000000) (Real.log (12381 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12381 / 10240) = -Real.log (10240 / 12381) := by
    rw [show ((12381 / 10240) : ℝ) = ((10240 / 12381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (117280511 / 500000000) ≤ -Real.log (8099 / 10240) ∧
    -Real.log (8099 / 10240) ≤ (234561023 / 1000000000) := by
  have h := checkLog_sound (w := (2141 / 18339)) (n := 12)
    (lo := (117280511 / 500000000)) (hi := (234561023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8099) = 1/(8099 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-234561023 / 1000000000) (-117280511 / 500000000) (Real.log (8099 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (174888101 / 500000000) ≤ -Real.log (160 / 227) ∧
    -Real.log (160 / 227) ≤ (349776203 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 387)) (n := 12)
    (lo := (174888101 / 500000000)) (hi := (349776203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((227 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(227 / 160) = 1/(160 / 227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (174888101 / 500000000) (349776203 / 1000000000) (Real.log (227 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (227 / 160) = -Real.log (160 / 227) := by
    rw [show ((227 / 160) : ℝ) = ((160 / 227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (271287161 / 500000000) ≤ -Real.log (93 / 160) ∧
    -Real.log (93 / 160) ≤ (542574323 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 253)) (n := 12)
    (lo := (271287161 / 500000000)) (hi := (542574323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 93) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 93) = 1/(93 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-542574323 / 1000000000) (-271287161 / 500000000) (Real.log (93 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (349363121 / 1000000000) ≤ -Real.log (5120 / 7261) ∧
    -Real.log (5120 / 7261) ≤ (174681561 / 500000000) := by
  have h := checkLog_sound (w := (2141 / 12381)) (n := 12)
    (lo := (349363121 / 1000000000)) (hi := (174681561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7261 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7261 / 5120) = 1/(5120 / 7261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (349363121 / 1000000000) (174681561 / 500000000) (Real.log (7261 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7261 / 5120) = -Real.log (5120 / 7261) := by
    rw [show ((7261 / 5120) : ℝ) = ((5120 / 7261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (108313353 / 200000000) ≤ -Real.log (2979 / 5120) ∧
    -Real.log (2979 / 5120) ≤ (270783383 / 500000000) := by
  have h := checkLog_sound (w := (2141 / 8099)) (n := 12)
    (lo := (108313353 / 200000000)) (hi := (270783383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2979) = 1/(2979 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-270783383 / 500000000) (-108313353 / 200000000) (Real.log (2979 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (260834633 / 1000000000) ≤ -Real.log (1000000 / 1298013) ∧
    -Real.log (1000000 / 1298013) ≤ (130417317 / 500000000) := by
  have h := checkLog_sound (w := (298013 / 2298013)) (n := 12)
    (lo := (260834633 / 1000000000)) (hi := (130417317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1298013 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1298013 / 1000000) = 1/(1000000 / 1298013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (260834633 / 1000000000) (130417317 / 500000000) (Real.log (1298013 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1298013 / 1000000) = -Real.log (1000000 / 1298013) := by
    rw [show ((1298013 / 1000000) : ℝ) = ((1000000 / 1298013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (353840393 / 1000000000) ≤ -Real.log (701987 / 1000000) ∧
    -Real.log (701987 / 1000000) ≤ (176920197 / 500000000) := by
  have h := checkLog_sound (w := (298013 / 1701987)) (n := 12)
    (lo := (353840393 / 1000000000)) (hi := (176920197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 701987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 701987) = 1/(701987 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-176920197 / 500000000) (-353840393 / 1000000000) (Real.log (701987 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (261162773 / 1000000000) ≤ -Real.log (1000000 / 1298439) ∧
    -Real.log (1000000 / 1298439) ≤ (130581387 / 500000000) := by
  have h := checkLog_sound (w := (298439 / 2298439)) (n := 12)
    (lo := (261162773 / 1000000000)) (hi := (130581387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1298439 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1298439 / 1000000) = 1/(1000000 / 1298439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (261162773 / 1000000000) (130581387 / 500000000) (Real.log (1298439 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1298439 / 1000000) = -Real.log (1000000 / 1298439) := by
    rw [show ((1298439 / 1000000) : ℝ) = ((1000000 / 1298439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (177223713 / 500000000) ≤ -Real.log (701561 / 1000000) ∧
    -Real.log (701561 / 1000000) ≤ (354447427 / 1000000000) := by
  have h := checkLog_sound (w := (298439 / 1701561)) (n := 12)
    (lo := (177223713 / 500000000)) (hi := (354447427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 701561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 701561) = 1/(701561 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-354447427 / 1000000000) (-177223713 / 500000000) (Real.log (701561 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (39119771 / 200000000) ≤ -Real.log (1000000 / 1216039) ∧
    -Real.log (1000000 / 1216039) ≤ (24449857 / 125000000) := by
  have h := checkLog_sound (w := (216039 / 2216039)) (n := 12)
    (lo := (39119771 / 200000000)) (hi := (24449857 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1216039 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1216039 / 1000000) = 1/(1000000 / 1216039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (39119771 / 200000000) (24449857 / 125000000) (Real.log (1216039 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1216039 / 1000000) = -Real.log (1000000 / 1216039) := by
    rw [show ((1216039 / 1000000) : ℝ) = ((1000000 / 1216039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (60849001 / 250000000) ≤ -Real.log (783961 / 1000000) ∧
    -Real.log (783961 / 1000000) ≤ (48679201 / 200000000) := by
  have h := checkLog_sound (w := (216039 / 1783961)) (n := 12)
    (lo := (60849001 / 250000000)) (hi := (48679201 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 783961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 783961) = 1/(783961 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-48679201 / 200000000) (-60849001 / 250000000) (Real.log (783961 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (1224163 / 6250000) ≤ -Real.log (250000 / 304091) ∧
    -Real.log (250000 / 304091) ≤ (195866081 / 1000000000) := by
  have h := checkLog_sound (w := (54091 / 554091)) (n := 12)
    (lo := (1224163 / 6250000)) (hi := (195866081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304091 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304091 / 250000) = 1/(250000 / 304091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (1224163 / 6250000) (195866081 / 1000000000) (Real.log (304091 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (304091 / 250000) = -Real.log (250000 / 304091) := by
    rw [show ((304091 / 250000) : ℝ) = ((250000 / 304091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (60952663 / 250000000) ≤ -Real.log (195909 / 250000) ∧
    -Real.log (195909 / 250000) ≤ (243810653 / 1000000000) := by
  have h := checkLog_sound (w := (54091 / 445909)) (n := 12)
    (lo := (60952663 / 250000000)) (hi := (243810653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 195909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 195909) = 1/(195909 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-243810653 / 1000000000) (-60952663 / 250000000) (Real.log (195909 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (614675027 / 1000000000) ≤ -Real.log (100000000000 / 184905560929) ∧
    -Real.log (100000000000 / 184905560929) ≤ (153668757 / 250000000) := by
  have h := checkLog_sound (w := (84905560929 / 284905560929)) (n := 12)
    (lo := (614675027 / 1000000000)) (hi := (153668757 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184905560929 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184905560929 / 100000000000) = 1/(100000000000 / 184905560929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (614675027 / 1000000000) (153668757 / 250000000) (Real.log (184905560929 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (184905560929 / 100000000000) = -Real.log (100000000000 / 184905560929) := by
    rw [show ((184905560929 / 100000000000) : ℝ) = ((100000000000 / 184905560929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3078051 / 5000000) ≤ -Real.log (250000000000 / 462696401311) ∧
    -Real.log (250000000000 / 462696401311) ≤ (615610201 / 1000000000) := by
  have h := checkLog_sound (w := (212696401311 / 712696401311)) (n := 12)
    (lo := (3078051 / 5000000)) (hi := (615610201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((462696401311 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(462696401311 / 250000000000) = 1/(250000000000 / 462696401311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3078051 / 5000000) (615610201 / 1000000000) (Real.log (462696401311 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (462696401311 / 250000000000) = -Real.log (250000000000 / 462696401311) := by
    rw [show ((462696401311 / 250000000000) : ℝ) = ((250000000000 / 462696401311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (21949743 / 50000000) ≤ -Real.log (500000000000 / 775573657363) ∧
    -Real.log (500000000000 / 775573657363) ≤ (438994861 / 1000000000) := by
  have h := checkLog_sound (w := (275573657363 / 1275573657363)) (n := 12)
    (lo := (21949743 / 50000000)) (hi := (438994861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((775573657363 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(775573657363 / 500000000000) = 1/(500000000000 / 775573657363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (21949743 / 50000000) (438994861 / 1000000000) (Real.log (775573657363 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (775573657363 / 500000000000) = -Real.log (500000000000 / 775573657363) := by
    rw [show ((775573657363 / 500000000000) : ℝ) = ((500000000000 / 775573657363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (439676733 / 1000000000) ≤ -Real.log (500000000000 / 776102680327) ∧
    -Real.log (500000000000 / 776102680327) ≤ (219838367 / 500000000) := by
  have h := checkLog_sound (w := (276102680327 / 1276102680327)) (n := 12)
    (lo := (439676733 / 1000000000)) (hi := (219838367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((776102680327 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(776102680327 / 500000000000) = 1/(500000000000 / 776102680327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (439676733 / 1000000000) (219838367 / 500000000) (Real.log (776102680327 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (776102680327 / 500000000000) = -Real.log (500000000000 / 776102680327) := by
    rw [show ((776102680327 / 500000000000) : ℝ) = ((500000000000 / 776102680327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0442

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0443Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0443
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

theorem reflection_log_1_neg : (189861419 / 1000000000) ≤ -Real.log (10240 / 12381) ∧
    -Real.log (10240 / 12381) ≤ (9493071 / 50000000) := by
  have h := checkLog_sound (w := (2141 / 22621)) (n := 12)
    (lo := (189861419 / 1000000000)) (hi := (9493071 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12381 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12381 / 10240) = 1/(10240 / 12381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (189861419 / 1000000000) (9493071 / 50000000) (Real.log (12381 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12381 / 10240) = -Real.log (10240 / 12381) := by
    rw [show ((12381 / 10240) : ℝ) = ((10240 / 12381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (117280511 / 500000000) ≤ -Real.log (8099 / 10240) ∧
    -Real.log (8099 / 10240) ≤ (234561023 / 1000000000) := by
  have h := checkLog_sound (w := (2141 / 18339)) (n := 12)
    (lo := (117280511 / 500000000)) (hi := (234561023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8099) = 1/(8099 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-234561023 / 1000000000) (-117280511 / 500000000) (Real.log (8099 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (189619083 / 1000000000) ≤ -Real.log (5120 / 6189) ∧
    -Real.log (5120 / 6189) ≤ (47404771 / 250000000) := by
  have h := checkLog_sound (w := (1069 / 11309)) (n := 12)
    (lo := (189619083 / 1000000000)) (hi := (47404771 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6189 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6189 / 5120) = 1/(5120 / 6189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (189619083 / 1000000000) (47404771 / 250000000) (Real.log (6189 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6189 / 5120) = -Real.log (5120 / 6189) := by
    rw [show ((6189 / 5120) : ℝ) = ((5120 / 6189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (117095337 / 500000000) ≤ -Real.log (4051 / 5120) ∧
    -Real.log (4051 / 5120) ≤ (9367627 / 40000000) := by
  have h := checkLog_sound (w := (1069 / 9171)) (n := 12)
    (lo := (117095337 / 500000000)) (hi := (9367627 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4051) = 1/(4051 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-9367627 / 40000000) (-117095337 / 500000000) (Real.log (4051 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (349363121 / 1000000000) ≤ -Real.log (5120 / 7261) ∧
    -Real.log (5120 / 7261) ≤ (174681561 / 500000000) := by
  have h := checkLog_sound (w := (2141 / 12381)) (n := 12)
    (lo := (349363121 / 1000000000)) (hi := (174681561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7261 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7261 / 5120) = 1/(5120 / 7261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (349363121 / 1000000000) (174681561 / 500000000) (Real.log (7261 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7261 / 5120) = -Real.log (5120 / 7261) := by
    rw [show ((7261 / 5120) : ℝ) = ((5120 / 7261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (108313353 / 200000000) ≤ -Real.log (2979 / 5120) ∧
    -Real.log (2979 / 5120) ≤ (270783383 / 500000000) := by
  have h := checkLog_sound (w := (2141 / 8099)) (n := 12)
    (lo := (108313353 / 200000000)) (hi := (270783383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2979) = 1/(2979 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-270783383 / 500000000) (-108313353 / 200000000) (Real.log (2979 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (348949869 / 1000000000) ≤ -Real.log (2560 / 3629) ∧
    -Real.log (2560 / 3629) ≤ (34894987 / 100000000) := by
  have h := checkLog_sound (w := (1069 / 6189)) (n := 12)
    (lo := (348949869 / 1000000000)) (hi := (34894987 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3629 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3629 / 2560) = 1/(2560 / 3629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (348949869 / 1000000000) (34894987 / 100000000) (Real.log (3629 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3629 / 2560) = -Real.log (2560 / 3629) := by
    rw [show ((3629 / 2560) : ℝ) = ((2560 / 3629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (270280111 / 500000000) ≤ -Real.log (1491 / 2560) ∧
    -Real.log (1491 / 2560) ≤ (540560223 / 1000000000) := by
  have h := checkLog_sound (w := (1069 / 4051)) (n := 12)
    (lo := (270280111 / 500000000)) (hi := (540560223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1491) = 1/(1491 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-540560223 / 1000000000) (-270280111 / 500000000) (Real.log (1491 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (65126789 / 250000000) ≤ -Real.log (250000 / 324397) ∧
    -Real.log (250000 / 324397) ≤ (260507157 / 1000000000) := by
  have h := checkLog_sound (w := (74397 / 574397)) (n := 12)
    (lo := (65126789 / 250000000)) (hi := (260507157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((324397 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(324397 / 250000) = 1/(250000 / 324397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (65126789 / 250000000) (260507157 / 1000000000) (Real.log (324397 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (324397 / 250000) = -Real.log (250000 / 324397) := by
    rw [show ((324397 / 250000) : ℝ) = ((250000 / 324397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (22077197 / 62500000) ≤ -Real.log (175603 / 250000) ∧
    -Real.log (175603 / 250000) ≤ (353235153 / 1000000000) := by
  have h := checkLog_sound (w := (74397 / 425603)) (n := 12)
    (lo := (22077197 / 62500000)) (hi := (353235153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 175603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 175603) = 1/(175603 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-353235153 / 1000000000) (-22077197 / 62500000) (Real.log (175603 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (65208851 / 250000000) ≤ -Real.log (500000 / 649007) ∧
    -Real.log (500000 / 649007) ≤ (52167081 / 200000000) := by
  have h := checkLog_sound (w := (149007 / 1149007)) (n := 12)
    (lo := (65208851 / 250000000)) (hi := (52167081 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((649007 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(649007 / 500000) = 1/(500000 / 649007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (65208851 / 250000000) (52167081 / 200000000) (Real.log (649007 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (649007 / 500000) = -Real.log (500000 / 649007) := by
    rw [show ((649007 / 500000) : ℝ) = ((500000 / 649007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (176920909 / 500000000) ≤ -Real.log (350993 / 500000) ∧
    -Real.log (350993 / 500000) ≤ (353841819 / 1000000000) := by
  have h := checkLog_sound (w := (149007 / 850993)) (n := 12)
    (lo := (176920909 / 500000000)) (hi := (353841819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 350993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 350993) = 1/(350993 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-353841819 / 1000000000) (-176920909 / 500000000) (Real.log (350993 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (195333203 / 1000000000) ≤ -Real.log (250000 / 303929) ∧
    -Real.log (250000 / 303929) ≤ (48833301 / 250000000) := by
  have h := checkLog_sound (w := (53929 / 553929)) (n := 12)
    (lo := (195333203 / 1000000000)) (hi := (48833301 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303929 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303929 / 250000) = 1/(250000 / 303929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (195333203 / 1000000000) (48833301 / 250000000) (Real.log (303929 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (303929 / 250000) = -Real.log (250000 / 303929) := by
    rw [show ((303929 / 250000) : ℝ) = ((250000 / 303929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (242984079 / 1000000000) ≤ -Real.log (196071 / 250000) ∧
    -Real.log (196071 / 250000) ≤ (3037301 / 12500000) := by
  have h := checkLog_sound (w := (53929 / 446071)) (n := 12)
    (lo := (242984079 / 1000000000)) (hi := (3037301 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 196071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 196071) = 1/(196071 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3037301 / 12500000) (-242984079 / 1000000000) (Real.log (196071 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (195599677 / 1000000000) ≤ -Real.log (25000 / 30401) ∧
    -Real.log (25000 / 30401) ≤ (97799839 / 500000000) := by
  have h := checkLog_sound (w := (5401 / 55401)) (n := 12)
    (lo := (195599677 / 1000000000)) (hi := (97799839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30401 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30401 / 25000) = 1/(25000 / 30401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (195599677 / 1000000000) (97799839 / 500000000) (Real.log (30401 / 25000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (30401 / 25000) = -Real.log (25000 / 30401) := by
    rw [show ((30401 / 25000) : ℝ) = ((25000 / 30401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1521233 / 6250000) ≤ -Real.log (19599 / 25000) ∧
    -Real.log (19599 / 25000) ≤ (243397281 / 1000000000) := by
  have h := checkLog_sound (w := (5401 / 44599)) (n := 12)
    (lo := (1521233 / 6250000)) (hi := (243397281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 19599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 19599) = 1/(19599 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-243397281 / 1000000000) (-1521233 / 6250000) (Real.log (19599 / 25000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (613742309 / 1000000000) ≤ -Real.log (500000000000 / 923665882701) ∧
    -Real.log (500000000000 / 923665882701) ≤ (61374231 / 100000000) := by
  have h := checkLog_sound (w := (423665882701 / 1423665882701)) (n := 12)
    (lo := (613742309 / 1000000000)) (hi := (61374231 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((923665882701 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(923665882701 / 500000000000) = 1/(500000000000 / 923665882701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (613742309 / 1000000000) (61374231 / 100000000) (Real.log (923665882701 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (923665882701 / 500000000000) = -Real.log (500000000000 / 923665882701) := by
    rw [show ((923665882701 / 500000000000) : ℝ) = ((500000000000 / 923665882701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (307338611 / 500000000) ≤ -Real.log (500000000000 / 924529833929) ∧
    -Real.log (500000000000 / 924529833929) ≤ (614677223 / 1000000000) := by
  have h := checkLog_sound (w := (424529833929 / 1424529833929)) (n := 12)
    (lo := (307338611 / 500000000)) (hi := (614677223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((924529833929 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(924529833929 / 500000000000) = 1/(500000000000 / 924529833929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (307338611 / 500000000) (614677223 / 1000000000) (Real.log (924529833929 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (924529833929 / 500000000000) = -Real.log (500000000000 / 924529833929) := by
    rw [show ((924529833929 / 500000000000) : ℝ) = ((500000000000 / 924529833929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (219158641 / 500000000) ≤ -Real.log (500000000000 / 775048324331) ∧
    -Real.log (500000000000 / 775048324331) ≤ (438317283 / 1000000000) := by
  have h := checkLog_sound (w := (275048324331 / 1275048324331)) (n := 12)
    (lo := (219158641 / 500000000)) (hi := (438317283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((775048324331 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(775048324331 / 500000000000) = 1/(500000000000 / 775048324331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (219158641 / 500000000) (438317283 / 1000000000) (Real.log (775048324331 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (775048324331 / 500000000000) = -Real.log (500000000000 / 775048324331) := by
    rw [show ((775048324331 / 500000000000) : ℝ) = ((500000000000 / 775048324331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (219498479 / 500000000) ≤ -Real.log (250000000000 / 387787642227) ∧
    -Real.log (250000000000 / 387787642227) ≤ (438996959 / 1000000000) := by
  have h := checkLog_sound (w := (137787642227 / 637787642227)) (n := 12)
    (lo := (219498479 / 500000000)) (hi := (438996959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387787642227 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387787642227 / 250000000000) = 1/(250000000000 / 387787642227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (219498479 / 500000000) (438996959 / 1000000000) (Real.log (387787642227 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (387787642227 / 250000000000) = -Real.log (250000000000 / 387787642227) := by
    rw [show ((387787642227 / 250000000000) : ℝ) = ((250000000000 / 387787642227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0443

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0444Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0444
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

theorem reflection_log_1_neg : (189619083 / 1000000000) ≤ -Real.log (5120 / 6189) ∧
    -Real.log (5120 / 6189) ≤ (47404771 / 250000000) := by
  have h := checkLog_sound (w := (1069 / 11309)) (n := 12)
    (lo := (189619083 / 1000000000)) (hi := (47404771 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6189 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6189 / 5120) = 1/(5120 / 6189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (189619083 / 1000000000) (47404771 / 250000000) (Real.log (6189 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6189 / 5120) = -Real.log (5120 / 6189) := by
    rw [show ((6189 / 5120) : ℝ) = ((5120 / 6189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (117095337 / 500000000) ≤ -Real.log (4051 / 5120) ∧
    -Real.log (4051 / 5120) ≤ (9367627 / 40000000) := by
  have h := checkLog_sound (w := (1069 / 9171)) (n := 12)
    (lo := (117095337 / 500000000)) (hi := (9367627 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4051) = 1/(4051 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-9367627 / 40000000) (-117095337 / 500000000) (Real.log (4051 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11836043 / 62500000) ≤ -Real.log (2048 / 2475) ∧
    -Real.log (2048 / 2475) ≤ (189376689 / 1000000000) := by
  have h := checkLog_sound (w := (427 / 4523)) (n := 12)
    (lo := (11836043 / 62500000)) (hi := (189376689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2475 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2475 / 2048) = 1/(2048 / 2475) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11836043 / 62500000) (189376689 / 1000000000) (Real.log (2475 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2475 / 2048) = -Real.log (2048 / 2475) := by
    rw [show ((2475 / 2048) : ℝ) = ((2048 / 2475) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (14613779 / 62500000) ≤ -Real.log (1621 / 2048) ∧
    -Real.log (1621 / 2048) ≤ (46764093 / 200000000) := by
  have h := checkLog_sound (w := (427 / 3669)) (n := 12)
    (lo := (14613779 / 62500000)) (hi := (46764093 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1621) = 1/(1621 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-46764093 / 200000000) (-14613779 / 62500000) (Real.log (1621 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (348949869 / 1000000000) ≤ -Real.log (2560 / 3629) ∧
    -Real.log (2560 / 3629) ≤ (34894987 / 100000000) := by
  have h := checkLog_sound (w := (1069 / 6189)) (n := 12)
    (lo := (348949869 / 1000000000)) (hi := (34894987 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3629 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3629 / 2560) = 1/(2560 / 3629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (348949869 / 1000000000) (34894987 / 100000000) (Real.log (3629 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3629 / 2560) = -Real.log (2560 / 3629) := by
    rw [show ((3629 / 2560) : ℝ) = ((2560 / 3629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (270280111 / 500000000) ≤ -Real.log (1491 / 2560) ∧
    -Real.log (1491 / 2560) ≤ (540560223 / 1000000000) := by
  have h := checkLog_sound (w := (1069 / 4051)) (n := 12)
    (lo := (270280111 / 500000000)) (hi := (540560223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1491) = 1/(1491 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-540560223 / 1000000000) (-270280111 / 500000000) (Real.log (1491 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (348536447 / 1000000000) ≤ -Real.log (1024 / 1451) ∧
    -Real.log (1024 / 1451) ≤ (2722941 / 7812500) := by
  have h := checkLog_sound (w := (427 / 2475)) (n := 12)
    (lo := (348536447 / 1000000000)) (hi := (2722941 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1451 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1451 / 1024) = 1/(1024 / 1451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (348536447 / 1000000000) (2722941 / 7812500) (Real.log (1451 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1451 / 1024) = -Real.log (1024 / 1451) := by
    rw [show ((1451 / 1024) : ℝ) = ((1024 / 1451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (134888673 / 250000000) ≤ -Real.log (597 / 1024) ∧
    -Real.log (597 / 1024) ≤ (539554693 / 1000000000) := by
  have h := checkLog_sound (w := (427 / 1621)) (n := 12)
    (lo := (134888673 / 250000000)) (hi := (539554693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 597) = 1/(597 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-539554693 / 1000000000) (-134888673 / 250000000) (Real.log (597 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (130090171 / 500000000) ≤ -Real.log (250000 / 324291) ∧
    -Real.log (250000 / 324291) ≤ (260180343 / 1000000000) := by
  have h := checkLog_sound (w := (74291 / 574291)) (n := 12)
    (lo := (130090171 / 500000000)) (hi := (260180343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((324291 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(324291 / 250000) = 1/(250000 / 324291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (130090171 / 500000000) (260180343 / 1000000000) (Real.log (324291 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (324291 / 250000) = -Real.log (250000 / 324291) := by
    rw [show ((324291 / 250000) : ℝ) = ((250000 / 324291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3526317 / 10000000) ≤ -Real.log (175709 / 250000) ∧
    -Real.log (175709 / 250000) ≤ (352631701 / 1000000000) := by
  have h := checkLog_sound (w := (74291 / 425709)) (n := 12)
    (lo := (3526317 / 10000000)) (hi := (352631701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 175709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 175709) = 1/(175709 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-352631701 / 1000000000) (-3526317 / 10000000) (Real.log (175709 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (260507927 / 1000000000) ≤ -Real.log (1000000 / 1297589) ∧
    -Real.log (1000000 / 1297589) ≤ (32563491 / 125000000) := by
  have h := checkLog_sound (w := (297589 / 2297589)) (n := 12)
    (lo := (260507927 / 1000000000)) (hi := (32563491 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1297589 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1297589 / 1000000) = 1/(1000000 / 1297589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (260507927 / 1000000000) (32563491 / 125000000) (Real.log (1297589 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1297589 / 1000000) = -Real.log (1000000 / 1297589) := by
    rw [show ((1297589 / 1000000) : ℝ) = ((1000000 / 1297589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (11038643 / 31250000) ≤ -Real.log (702411 / 1000000) ∧
    -Real.log (702411 / 1000000) ≤ (353236577 / 1000000000) := by
  have h := checkLog_sound (w := (297589 / 1702411)) (n := 12)
    (lo := (11038643 / 31250000)) (hi := (353236577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 702411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 702411) = 1/(702411 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-353236577 / 1000000000) (-11038643 / 31250000) (Real.log (702411 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (195067481 / 1000000000) ≤ -Real.log (1000000 / 1215393) ∧
    -Real.log (1000000 / 1215393) ≤ (97533741 / 500000000) := by
  have h := checkLog_sound (w := (215393 / 2215393)) (n := 12)
    (lo := (195067481 / 1000000000)) (hi := (97533741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1215393 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1215393 / 1000000) = 1/(1000000 / 1215393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (195067481 / 1000000000) (97533741 / 500000000) (Real.log (1215393 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1215393 / 1000000) = -Real.log (1000000 / 1215393) := by
    rw [show ((1215393 / 1000000) : ℝ) = ((1000000 / 1215393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (242572323 / 1000000000) ≤ -Real.log (784607 / 1000000) ∧
    -Real.log (784607 / 1000000) ≤ (60643081 / 250000000) := by
  have h := checkLog_sound (w := (215393 / 1784607)) (n := 12)
    (lo := (242572323 / 1000000000)) (hi := (60643081 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 784607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 784607) = 1/(784607 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-60643081 / 250000000) (-242572323 / 1000000000) (Real.log (784607 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (97667013 / 500000000) ≤ -Real.log (1000000 / 1215717) ∧
    -Real.log (1000000 / 1215717) ≤ (195334027 / 1000000000) := by
  have h := checkLog_sound (w := (215717 / 2215717)) (n := 12)
    (lo := (97667013 / 500000000)) (hi := (195334027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1215717 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1215717 / 1000000) = 1/(1000000 / 1215717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (97667013 / 500000000) (195334027 / 1000000000) (Real.log (1215717 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1215717 / 1000000) = -Real.log (1000000 / 1215717) := by
    rw [show ((1215717 / 1000000) : ℝ) = ((1000000 / 1215717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (121492677 / 500000000) ≤ -Real.log (784283 / 1000000) ∧
    -Real.log (784283 / 1000000) ≤ (48597071 / 200000000) := by
  have h := checkLog_sound (w := (215717 / 1784283)) (n := 12)
    (lo := (121492677 / 500000000)) (hi := (48597071 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 784283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 784283) = 1/(784283 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-48597071 / 200000000) (-121492677 / 500000000) (Real.log (784283 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (612812043 / 1000000000) ≤ -Real.log (62500000000 / 115350878441) ∧
    -Real.log (62500000000 / 115350878441) ≤ (153203011 / 250000000) := by
  have h := checkLog_sound (w := (52850878441 / 177850878441)) (n := 12)
    (lo := (612812043 / 1000000000)) (hi := (153203011 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((115350878441 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(115350878441 / 62500000000) = 1/(62500000000 / 115350878441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (612812043 / 1000000000) (153203011 / 250000000) (Real.log (115350878441 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (115350878441 / 62500000000) = -Real.log (62500000000 / 115350878441) := by
    rw [show ((115350878441 / 62500000000) : ℝ) = ((62500000000 / 115350878441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (613744503 / 1000000000) ≤ -Real.log (500000000000 / 923667909529) ∧
    -Real.log (500000000000 / 923667909529) ≤ (76718063 / 125000000) := by
  have h := checkLog_sound (w := (423667909529 / 1423667909529)) (n := 12)
    (lo := (613744503 / 1000000000)) (hi := (76718063 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((923667909529 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(923667909529 / 500000000000) = 1/(500000000000 / 923667909529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (613744503 / 1000000000) (76718063 / 125000000) (Real.log (923667909529 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (923667909529 / 500000000000) = -Real.log (500000000000 / 923667909529) := by
    rw [show ((923667909529 / 500000000000) : ℝ) = ((500000000000 / 923667909529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (109409951 / 250000000) ≤ -Real.log (125000000000 / 193630855957) ∧
    -Real.log (125000000000 / 193630855957) ≤ (87527961 / 200000000) := by
  have h := checkLog_sound (w := (68630855957 / 318630855957)) (n := 12)
    (lo := (109409951 / 250000000)) (hi := (87527961 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((193630855957 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(193630855957 / 125000000000) = 1/(125000000000 / 193630855957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (109409951 / 250000000) (87527961 / 200000000) (Real.log (193630855957 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (193630855957 / 125000000000) = -Real.log (125000000000 / 193630855957) := by
    rw [show ((193630855957 / 125000000000) : ℝ) = ((125000000000 / 193630855957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (21915969 / 50000000) ≤ -Real.log (250000000000 / 387524975041) ∧
    -Real.log (250000000000 / 387524975041) ≤ (438319381 / 1000000000) := by
  have h := checkLog_sound (w := (137524975041 / 637524975041)) (n := 12)
    (lo := (21915969 / 50000000)) (hi := (438319381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387524975041 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387524975041 / 250000000000) = 1/(250000000000 / 387524975041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (21915969 / 50000000) (438319381 / 1000000000) (Real.log (387524975041 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (387524975041 / 250000000000) = -Real.log (250000000000 / 387524975041) := by
    rw [show ((387524975041 / 250000000000) : ℝ) = ((250000000000 / 387524975041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0444

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0445Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0445
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

theorem reflection_log_1_neg : (11836043 / 62500000) ≤ -Real.log (2048 / 2475) ∧
    -Real.log (2048 / 2475) ≤ (189376689 / 1000000000) := by
  have h := checkLog_sound (w := (427 / 4523)) (n := 12)
    (lo := (11836043 / 62500000)) (hi := (189376689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2475 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2475 / 2048) = 1/(2048 / 2475) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11836043 / 62500000) (189376689 / 1000000000) (Real.log (2475 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2475 / 2048) = -Real.log (2048 / 2475) := by
    rw [show ((2475 / 2048) : ℝ) = ((2048 / 2475) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (14613779 / 62500000) ≤ -Real.log (1621 / 2048) ∧
    -Real.log (1621 / 2048) ≤ (46764093 / 200000000) := by
  have h := checkLog_sound (w := (427 / 3669)) (n := 12)
    (lo := (14613779 / 62500000)) (hi := (46764093 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1621) = 1/(1621 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-46764093 / 200000000) (-14613779 / 62500000) (Real.log (1621 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (37826847 / 200000000) ≤ -Real.log (2560 / 3093) ∧
    -Real.log (2560 / 3093) ≤ (47283559 / 250000000) := by
  have h := checkLog_sound (w := (533 / 5653)) (n := 12)
    (lo := (37826847 / 200000000)) (hi := (47283559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3093 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3093 / 2560) = 1/(2560 / 3093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (37826847 / 200000000) (47283559 / 250000000) (Real.log (3093 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3093 / 2560) = -Real.log (2560 / 3093) := by
    rw [show ((3093 / 2560) : ℝ) = ((2560 / 3093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (233450391 / 1000000000) ≤ -Real.log (2027 / 2560) ∧
    -Real.log (2027 / 2560) ≤ (29181299 / 125000000) := by
  have h := checkLog_sound (w := (533 / 4587)) (n := 12)
    (lo := (233450391 / 1000000000)) (hi := (29181299 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 2027) = 1/(2027 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-29181299 / 125000000) (-233450391 / 1000000000) (Real.log (2027 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (348536447 / 1000000000) ≤ -Real.log (1024 / 1451) ∧
    -Real.log (1024 / 1451) ≤ (2722941 / 7812500) := by
  have h := checkLog_sound (w := (427 / 2475)) (n := 12)
    (lo := (348536447 / 1000000000)) (hi := (2722941 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1451 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1451 / 1024) = 1/(1024 / 1451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (348536447 / 1000000000) (2722941 / 7812500) (Real.log (1451 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1451 / 1024) = -Real.log (1024 / 1451) := by
    rw [show ((1451 / 1024) : ℝ) = ((1024 / 1451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (134888673 / 250000000) ≤ -Real.log (597 / 1024) ∧
    -Real.log (597 / 1024) ≤ (539554693 / 1000000000) := by
  have h := checkLog_sound (w := (427 / 1621)) (n := 12)
    (lo := (134888673 / 250000000)) (hi := (539554693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 597) = 1/(597 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-539554693 / 1000000000) (-134888673 / 250000000) (Real.log (597 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (348122853 / 1000000000) ≤ -Real.log (1280 / 1813) ∧
    -Real.log (1280 / 1813) ≤ (174061427 / 500000000) := by
  have h := checkLog_sound (w := (533 / 3093)) (n := 12)
    (lo := (348122853 / 1000000000)) (hi := (174061427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1813 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1813 / 1280) = 1/(1280 / 1813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (348122853 / 1000000000) (174061427 / 500000000) (Real.log (1813 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1813 / 1280) = -Real.log (1280 / 1813) := by
    rw [show ((1813 / 1280) : ℝ) = ((1280 / 1813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (538550171 / 1000000000) ≤ -Real.log (747 / 1280) ∧
    -Real.log (747 / 1280) ≤ (134637543 / 250000000) := by
  have h := checkLog_sound (w := (533 / 2027)) (n := 12)
    (lo := (538550171 / 1000000000)) (hi := (134637543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 747) = 1/(747 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-134637543 / 250000000) (-538550171 / 1000000000) (Real.log (747 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (259852651 / 1000000000) ≤ -Real.log (1000000 / 1296739) ∧
    -Real.log (1000000 / 1296739) ≤ (64963163 / 250000000) := by
  have h := checkLog_sound (w := (296739 / 2296739)) (n := 12)
    (lo := (259852651 / 1000000000)) (hi := (64963163 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1296739 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1296739 / 1000000) = 1/(1000000 / 1296739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (259852651 / 1000000000) (64963163 / 250000000) (Real.log (1296739 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1296739 / 1000000) = -Real.log (1000000 / 1296739) := by
    rw [show ((1296739 / 1000000) : ℝ) = ((1000000 / 1296739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (35202719 / 100000000) ≤ -Real.log (703261 / 1000000) ∧
    -Real.log (703261 / 1000000) ≤ (352027191 / 1000000000) := by
  have h := checkLog_sound (w := (296739 / 1703261)) (n := 12)
    (lo := (35202719 / 100000000)) (hi := (352027191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 703261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 703261) = 1/(703261 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-352027191 / 1000000000) (-35202719 / 100000000) (Real.log (703261 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (260181113 / 1000000000) ≤ -Real.log (200000 / 259433) ∧
    -Real.log (200000 / 259433) ≤ (130090557 / 500000000) := by
  have h := checkLog_sound (w := (59433 / 459433)) (n := 12)
    (lo := (260181113 / 1000000000)) (hi := (130090557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259433 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(259433 / 200000) = 1/(200000 / 259433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (260181113 / 1000000000) (130090557 / 500000000) (Real.log (259433 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (259433 / 200000) = -Real.log (200000 / 259433) := by
    rw [show ((259433 / 200000) : ℝ) = ((200000 / 259433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (352633123 / 1000000000) ≤ -Real.log (140567 / 200000) ∧
    -Real.log (140567 / 200000) ≤ (88158281 / 250000000) := by
  have h := checkLog_sound (w := (59433 / 340567)) (n := 12)
    (lo := (352633123 / 1000000000)) (hi := (88158281 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 140567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 140567) = 1/(140567 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-88158281 / 250000000) (-352633123 / 1000000000) (Real.log (140567 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (24350211 / 125000000) ≤ -Real.log (100000 / 121507) ∧
    -Real.log (100000 / 121507) ≤ (194801689 / 1000000000) := by
  have h := checkLog_sound (w := (21507 / 221507)) (n := 12)
    (lo := (24350211 / 125000000)) (hi := (194801689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121507 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121507 / 100000) = 1/(100000 / 121507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (24350211 / 125000000) (194801689 / 1000000000) (Real.log (121507 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (121507 / 100000) = -Real.log (100000 / 121507) := by
    rw [show ((121507 / 100000) : ℝ) = ((100000 / 121507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (242160737 / 1000000000) ≤ -Real.log (78493 / 100000) ∧
    -Real.log (78493 / 100000) ≤ (121080369 / 500000000) := by
  have h := checkLog_sound (w := (21507 / 178493)) (n := 12)
    (lo := (242160737 / 1000000000)) (hi := (121080369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 78493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 78493) = 1/(78493 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-121080369 / 500000000) (-242160737 / 1000000000) (Real.log (78493 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (12191769 / 62500000) ≤ -Real.log (500000 / 607697) ∧
    -Real.log (500000 / 607697) ≤ (39013661 / 200000000) := by
  have h := checkLog_sound (w := (107697 / 1107697)) (n := 12)
    (lo := (12191769 / 62500000)) (hi := (39013661 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607697 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607697 / 500000) = 1/(500000 / 607697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (12191769 / 62500000) (39013661 / 200000000) (Real.log (607697 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (607697 / 500000) = -Real.log (500000 / 607697) := by
    rw [show ((607697 / 500000) : ℝ) = ((500000 / 607697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (121286799 / 500000000) ≤ -Real.log (392303 / 500000) ∧
    -Real.log (392303 / 500000) ≤ (242573599 / 1000000000) := by
  have h := checkLog_sound (w := (107697 / 892303)) (n := 12)
    (lo := (121286799 / 500000000)) (hi := (242573599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 392303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 392303) = 1/(392303 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-242573599 / 1000000000) (-121286799 / 500000000) (Real.log (392303 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (611879841 / 1000000000) ≤ -Real.log (500000000000 / 921947186037) ∧
    -Real.log (500000000000 / 921947186037) ≤ (305939921 / 500000000) := by
  have h := checkLog_sound (w := (421947186037 / 1421947186037)) (n := 12)
    (lo := (611879841 / 1000000000)) (hi := (305939921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((921947186037 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(921947186037 / 500000000000) = 1/(500000000000 / 921947186037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (611879841 / 1000000000) (305939921 / 500000000) (Real.log (921947186037 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (921947186037 / 500000000000) = -Real.log (500000000000 / 921947186037) := by
    rw [show ((921947186037 / 500000000000) : ℝ) = ((500000000000 / 921947186037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (612814237 / 1000000000) ≤ -Real.log (62500000000 / 115351131489) ∧
    -Real.log (62500000000 / 115351131489) ≤ (306407119 / 500000000) := by
  have h := checkLog_sound (w := (52851131489 / 177851131489)) (n := 12)
    (lo := (612814237 / 1000000000)) (hi := (306407119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((115351131489 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(115351131489 / 62500000000) = 1/(62500000000 / 115351131489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (612814237 / 1000000000) (306407119 / 500000000) (Real.log (115351131489 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (115351131489 / 62500000000) = -Real.log (62500000000 / 115351131489) := by
    rw [show ((115351131489 / 62500000000) : ℝ) = ((62500000000 / 115351131489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (17478497 / 40000000) ≤ -Real.log (12500000000 / 19349973883) ∧
    -Real.log (12500000000 / 19349973883) ≤ (218481213 / 500000000) := by
  have h := checkLog_sound (w := (6849973883 / 31849973883)) (n := 12)
    (lo := (17478497 / 40000000)) (hi := (218481213 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19349973883 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19349973883 / 12500000000) = 1/(12500000000 / 19349973883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (17478497 / 40000000) (218481213 / 500000000) (Real.log (19349973883 / 12500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (19349973883 / 12500000000) = -Real.log (12500000000 / 19349973883) := by
    rw [show ((19349973883 / 12500000000) : ℝ) = ((12500000000 / 19349973883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (218820951 / 500000000) ≤ -Real.log (500000000000 / 774525048241) ∧
    -Real.log (500000000000 / 774525048241) ≤ (437641903 / 1000000000) := by
  have h := checkLog_sound (w := (274525048241 / 1274525048241)) (n := 12)
    (lo := (218820951 / 500000000)) (hi := (437641903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((774525048241 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(774525048241 / 500000000000) = 1/(500000000000 / 774525048241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (218820951 / 500000000) (437641903 / 1000000000) (Real.log (774525048241 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (774525048241 / 500000000000) = -Real.log (500000000000 / 774525048241) := by
    rw [show ((774525048241 / 500000000000) : ℝ) = ((500000000000 / 774525048241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0445

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0446Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0446
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

theorem reflection_log_1_neg : (37826847 / 200000000) ≤ -Real.log (2560 / 3093) ∧
    -Real.log (2560 / 3093) ≤ (47283559 / 250000000) := by
  have h := checkLog_sound (w := (533 / 5653)) (n := 12)
    (lo := (37826847 / 200000000)) (hi := (47283559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3093 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3093 / 2560) = 1/(2560 / 3093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (37826847 / 200000000) (47283559 / 250000000) (Real.log (3093 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3093 / 2560) = -Real.log (2560 / 3093) := by
    rw [show ((3093 / 2560) : ℝ) = ((2560 / 3093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (233450391 / 1000000000) ≤ -Real.log (2027 / 2560) ∧
    -Real.log (2027 / 2560) ≤ (29181299 / 125000000) := by
  have h := checkLog_sound (w := (533 / 4587)) (n := 12)
    (lo := (233450391 / 1000000000)) (hi := (29181299 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 2027) = 1/(2027 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-29181299 / 125000000) (-233450391 / 1000000000) (Real.log (2027 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (94445861 / 500000000) ≤ -Real.log (10240 / 12369) ∧
    -Real.log (10240 / 12369) ≤ (188891723 / 1000000000) := by
  have h := checkLog_sound (w := (2129 / 22609)) (n := 12)
    (lo := (94445861 / 500000000)) (hi := (188891723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12369 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12369 / 10240) = 1/(10240 / 12369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (94445861 / 500000000) (188891723 / 1000000000) (Real.log (12369 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12369 / 10240) = -Real.log (10240 / 12369) := by
    rw [show ((12369 / 10240) : ℝ) = ((10240 / 12369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (116540227 / 500000000) ≤ -Real.log (8111 / 10240) ∧
    -Real.log (8111 / 10240) ≤ (46616091 / 200000000) := by
  have h := checkLog_sound (w := (2129 / 18351)) (n := 12)
    (lo := (116540227 / 500000000)) (hi := (46616091 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8111) = 1/(8111 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-46616091 / 200000000) (-116540227 / 500000000) (Real.log (8111 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (348122853 / 1000000000) ≤ -Real.log (1280 / 1813) ∧
    -Real.log (1280 / 1813) ≤ (174061427 / 500000000) := by
  have h := checkLog_sound (w := (533 / 3093)) (n := 12)
    (lo := (348122853 / 1000000000)) (hi := (174061427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1813 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1813 / 1280) = 1/(1280 / 1813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (348122853 / 1000000000) (174061427 / 500000000) (Real.log (1813 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1813 / 1280) = -Real.log (1280 / 1813) := by
    rw [show ((1813 / 1280) : ℝ) = ((1280 / 1813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (538550171 / 1000000000) ≤ -Real.log (747 / 1280) ∧
    -Real.log (747 / 1280) ≤ (134637543 / 250000000) := by
  have h := checkLog_sound (w := (533 / 2027)) (n := 12)
    (lo := (538550171 / 1000000000)) (hi := (134637543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 747) = 1/(747 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-134637543 / 250000000) (-538550171 / 1000000000) (Real.log (747 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (347709089 / 1000000000) ≤ -Real.log (5120 / 7249) ∧
    -Real.log (5120 / 7249) ≤ (34770909 / 100000000) := by
  have h := checkLog_sound (w := (2129 / 12369)) (n := 12)
    (lo := (347709089 / 1000000000)) (hi := (34770909 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7249 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7249 / 5120) = 1/(5120 / 7249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (347709089 / 1000000000) (34770909 / 100000000) (Real.log (7249 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7249 / 5120) = -Real.log (5120 / 7249) := by
    rw [show ((7249 / 5120) : ℝ) = ((5120 / 7249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (537546659 / 1000000000) ≤ -Real.log (2991 / 5120) ∧
    -Real.log (2991 / 5120) ≤ (26877333 / 50000000) := by
  have h := checkLog_sound (w := (2129 / 8111)) (n := 12)
    (lo := (537546659 / 1000000000)) (hi := (26877333 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2991) = 1/(2991 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-26877333 / 50000000) (-537546659 / 1000000000) (Real.log (2991 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (259525623 / 1000000000) ≤ -Real.log (200000 / 259263) ∧
    -Real.log (200000 / 259263) ≤ (32440703 / 125000000) := by
  have h := checkLog_sound (w := (59263 / 459263)) (n := 12)
    (lo := (259525623 / 1000000000)) (hi := (32440703 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259263 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(259263 / 200000) = 1/(200000 / 259263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (259525623 / 1000000000) (32440703 / 125000000) (Real.log (259263 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (259263 / 200000) = -Real.log (200000 / 259263) := by
    rw [show ((259263 / 200000) : ℝ) = ((200000 / 259263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (175712233 / 500000000) ≤ -Real.log (140737 / 200000) ∧
    -Real.log (140737 / 200000) ≤ (351424467 / 1000000000) := by
  have h := checkLog_sound (w := (59263 / 340737)) (n := 12)
    (lo := (175712233 / 500000000)) (hi := (351424467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 140737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 140737) = 1/(140737 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-351424467 / 1000000000) (-175712233 / 500000000) (Real.log (140737 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (129926711 / 500000000) ≤ -Real.log (50000 / 64837) ∧
    -Real.log (50000 / 64837) ≤ (259853423 / 1000000000) := by
  have h := checkLog_sound (w := (14837 / 114837)) (n := 12)
    (lo := (129926711 / 500000000)) (hi := (259853423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64837 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64837 / 50000) = 1/(50000 / 64837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (129926711 / 500000000) (259853423 / 1000000000) (Real.log (64837 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (64837 / 50000) = -Real.log (50000 / 64837) := by
    rw [show ((64837 / 50000) : ℝ) = ((50000 / 64837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (88007153 / 250000000) ≤ -Real.log (35163 / 50000) ∧
    -Real.log (35163 / 50000) ≤ (352028613 / 1000000000) := by
  have h := checkLog_sound (w := (14837 / 85163)) (n := 12)
    (lo := (88007153 / 250000000)) (hi := (352028613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 35163) = 1/(35163 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-352028613 / 1000000000) (-88007153 / 250000000) (Real.log (35163 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (12158489 / 62500000) ≤ -Real.log (1000000 / 1214747) ∧
    -Real.log (1000000 / 1214747) ≤ (7781433 / 40000000) := by
  have h := checkLog_sound (w := (214747 / 2214747)) (n := 12)
    (lo := (12158489 / 62500000)) (hi := (7781433 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1214747 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1214747 / 1000000) = 1/(1000000 / 1214747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (12158489 / 62500000) (7781433 / 40000000) (Real.log (1214747 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1214747 / 1000000) = -Real.log (1000000 / 1214747) := by
    rw [show ((1214747 / 1000000) : ℝ) = ((1000000 / 1214747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (6043733 / 25000000) ≤ -Real.log (785253 / 1000000) ∧
    -Real.log (785253 / 1000000) ≤ (241749321 / 1000000000) := by
  have h := checkLog_sound (w := (214747 / 1785253)) (n := 12)
    (lo := (6043733 / 25000000)) (hi := (241749321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 785253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 785253) = 1/(785253 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-241749321 / 1000000000) (-6043733 / 25000000) (Real.log (785253 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (194802511 / 1000000000) ≤ -Real.log (1000000 / 1215071) ∧
    -Real.log (1000000 / 1215071) ≤ (12175157 / 62500000) := by
  have h := checkLog_sound (w := (215071 / 2215071)) (n := 12)
    (lo := (194802511 / 1000000000)) (hi := (12175157 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1215071 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1215071 / 1000000) = 1/(1000000 / 1215071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (194802511 / 1000000000) (12175157 / 62500000) (Real.log (1215071 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1215071 / 1000000) = -Real.log (1000000 / 1215071) := by
    rw [show ((1215071 / 1000000) : ℝ) = ((1000000 / 1215071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (242162011 / 1000000000) ≤ -Real.log (784929 / 1000000) ∧
    -Real.log (784929 / 1000000) ≤ (60540503 / 250000000) := by
  have h := checkLog_sound (w := (215071 / 1784929)) (n := 12)
    (lo := (242162011 / 1000000000)) (hi := (60540503 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 784929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 784929) = 1/(784929 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-60540503 / 250000000) (-242162011 / 1000000000) (Real.log (784929 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (61095009 / 100000000) ≤ -Real.log (100000000000 / 184218080533) ∧
    -Real.log (100000000000 / 184218080533) ≤ (610950091 / 1000000000) := by
  have h := checkLog_sound (w := (84218080533 / 284218080533)) (n := 12)
    (lo := (61095009 / 100000000)) (hi := (610950091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184218080533 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184218080533 / 100000000000) = 1/(100000000000 / 184218080533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (61095009 / 100000000) (610950091 / 1000000000) (Real.log (184218080533 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (184218080533 / 100000000000) = -Real.log (100000000000 / 184218080533) := by
    rw [show ((184218080533 / 100000000000) : ℝ) = ((100000000000 / 184218080533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (305941017 / 500000000) ≤ -Real.log (20000000000 / 36877968319) ∧
    -Real.log (20000000000 / 36877968319) ≤ (122376407 / 200000000) := by
  have h := checkLog_sound (w := (16877968319 / 56877968319)) (n := 12)
    (lo := (305941017 / 500000000)) (hi := (122376407 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36877968319 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36877968319 / 20000000000) = 1/(20000000000 / 36877968319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (305941017 / 500000000) (122376407 / 200000000) (Real.log (36877968319 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (36877968319 / 20000000000) = -Real.log (20000000000 / 36877968319) := by
    rw [show ((36877968319 / 20000000000) : ℝ) = ((20000000000 / 36877968319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (54535643 / 125000000) ≤ -Real.log (250000000000 / 386737459137) ∧
    -Real.log (250000000000 / 386737459137) ≤ (87257029 / 200000000) := by
  have h := checkLog_sound (w := (136737459137 / 636737459137)) (n := 12)
    (lo := (54535643 / 125000000)) (hi := (87257029 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((386737459137 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(386737459137 / 250000000000) = 1/(250000000000 / 386737459137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (54535643 / 125000000) (87257029 / 200000000) (Real.log (386737459137 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (386737459137 / 250000000000) = -Real.log (250000000000 / 386737459137) := by
    rw [show ((386737459137 / 250000000000) : ℝ) = ((250000000000 / 386737459137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (218482261 / 500000000) ≤ -Real.log (500000000000 / 774000578397) ∧
    -Real.log (500000000000 / 774000578397) ≤ (436964523 / 1000000000) := by
  have h := checkLog_sound (w := (274000578397 / 1274000578397)) (n := 12)
    (lo := (218482261 / 500000000)) (hi := (436964523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((774000578397 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(774000578397 / 500000000000) = 1/(500000000000 / 774000578397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (218482261 / 500000000) (436964523 / 1000000000) (Real.log (774000578397 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (774000578397 / 500000000000) = -Real.log (500000000000 / 774000578397) := by
    rw [show ((774000578397 / 500000000000) : ℝ) = ((500000000000 / 774000578397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0446

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0447Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0447
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

theorem reflection_log_1_neg : (94445861 / 500000000) ≤ -Real.log (10240 / 12369) ∧
    -Real.log (10240 / 12369) ≤ (188891723 / 1000000000) := by
  have h := checkLog_sound (w := (2129 / 22609)) (n := 12)
    (lo := (94445861 / 500000000)) (hi := (188891723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12369 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12369 / 10240) = 1/(10240 / 12369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (94445861 / 500000000) (188891723 / 1000000000) (Real.log (12369 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12369 / 10240) = -Real.log (10240 / 12369) := by
    rw [show ((12369 / 10240) : ℝ) = ((10240 / 12369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (116540227 / 500000000) ≤ -Real.log (8111 / 10240) ∧
    -Real.log (8111 / 10240) ≤ (46616091 / 200000000) := by
  have h := checkLog_sound (w := (2129 / 18351)) (n := 12)
    (lo := (116540227 / 500000000)) (hi := (46616091 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8111) = 1/(8111 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-46616091 / 200000000) (-116540227 / 500000000) (Real.log (8111 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (188649151 / 1000000000) ≤ -Real.log (5120 / 6183) ∧
    -Real.log (5120 / 6183) ≤ (2947643 / 15625000) := by
  have h := checkLog_sound (w := (1063 / 11303)) (n := 12)
    (lo := (188649151 / 1000000000)) (hi := (2947643 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6183 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6183 / 5120) = 1/(5120 / 6183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (188649151 / 1000000000) (2947643 / 15625000) (Real.log (6183 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6183 / 5120) = -Real.log (5120 / 6183) := by
    rw [show ((6183 / 5120) : ℝ) = ((5120 / 6183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (116355327 / 500000000) ≤ -Real.log (4057 / 5120) ∧
    -Real.log (4057 / 5120) ≤ (46542131 / 200000000) := by
  have h := checkLog_sound (w := (1063 / 9177)) (n := 12)
    (lo := (116355327 / 500000000)) (hi := (46542131 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4057) = 1/(4057 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-46542131 / 200000000) (-116355327 / 500000000) (Real.log (4057 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (347709089 / 1000000000) ≤ -Real.log (5120 / 7249) ∧
    -Real.log (5120 / 7249) ≤ (34770909 / 100000000) := by
  have h := checkLog_sound (w := (2129 / 12369)) (n := 12)
    (lo := (347709089 / 1000000000)) (hi := (34770909 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7249 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7249 / 5120) = 1/(5120 / 7249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (347709089 / 1000000000) (34770909 / 100000000) (Real.log (7249 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7249 / 5120) = -Real.log (5120 / 7249) := by
    rw [show ((7249 / 5120) : ℝ) = ((5120 / 7249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (537546659 / 1000000000) ≤ -Real.log (2991 / 5120) ∧
    -Real.log (2991 / 5120) ≤ (26877333 / 50000000) := by
  have h := checkLog_sound (w := (2129 / 8111)) (n := 12)
    (lo := (537546659 / 1000000000)) (hi := (26877333 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2991) = 1/(2991 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-26877333 / 50000000) (-537546659 / 1000000000) (Real.log (2991 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (347295153 / 1000000000) ≤ -Real.log (2560 / 3623) ∧
    -Real.log (2560 / 3623) ≤ (173647577 / 500000000) := by
  have h := checkLog_sound (w := (1063 / 6183)) (n := 12)
    (lo := (347295153 / 1000000000)) (hi := (173647577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3623 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3623 / 2560) = 1/(2560 / 3623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (347295153 / 1000000000) (173647577 / 500000000) (Real.log (3623 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3623 / 2560) = -Real.log (2560 / 3623) := by
    rw [show ((3623 / 2560) : ℝ) = ((2560 / 3623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (536544153 / 1000000000) ≤ -Real.log (1497 / 2560) ∧
    -Real.log (1497 / 2560) ≤ (268272077 / 500000000) := by
  have h := checkLog_sound (w := (1063 / 4057)) (n := 12)
    (lo := (536544153 / 1000000000)) (hi := (268272077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1497) = 1/(1497 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-268272077 / 500000000) (-536544153 / 1000000000) (Real.log (1497 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (259197717 / 1000000000) ≤ -Real.log (100000 / 129589) ∧
    -Real.log (100000 / 129589) ≤ (129598859 / 500000000) := by
  have h := checkLog_sound (w := (29589 / 229589)) (n := 12)
    (lo := (259197717 / 1000000000)) (hi := (129598859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((129589 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(129589 / 100000) = 1/(100000 / 129589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (259197717 / 1000000000) (129598859 / 500000000) (Real.log (129589 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (129589 / 100000) = -Real.log (100000 / 129589) := by
    rw [show ((129589 / 100000) : ℝ) = ((100000 / 129589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (70164137 / 200000000) ≤ -Real.log (70411 / 100000) ∧
    -Real.log (70411 / 100000) ≤ (175410343 / 500000000) := by
  have h := checkLog_sound (w := (29589 / 170411)) (n := 12)
    (lo := (70164137 / 200000000)) (hi := (175410343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 70411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 70411) = 1/(70411 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-175410343 / 500000000) (-70164137 / 200000000) (Real.log (70411 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (51905279 / 200000000) ≤ -Real.log (250000 / 324079) ∧
    -Real.log (250000 / 324079) ≤ (64881599 / 250000000) := by
  have h := checkLog_sound (w := (74079 / 574079)) (n := 12)
    (lo := (51905279 / 200000000)) (hi := (64881599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((324079 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(324079 / 250000) = 1/(250000 / 324079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (51905279 / 200000000) (64881599 / 250000000) (Real.log (324079 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (324079 / 250000) = -Real.log (250000 / 324079) := by
    rw [show ((324079 / 250000) : ℝ) = ((250000 / 324079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (351425887 / 1000000000) ≤ -Real.log (175921 / 250000) ∧
    -Real.log (175921 / 250000) ≤ (10982059 / 31250000) := by
  have h := checkLog_sound (w := (74079 / 425921)) (n := 12)
    (lo := (351425887 / 1000000000)) (hi := (10982059 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 175921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 175921) = 1/(175921 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-10982059 / 31250000) (-351425887 / 1000000000) (Real.log (175921 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (19426989 / 100000000) ≤ -Real.log (125000 / 151803) ∧
    -Real.log (125000 / 151803) ≤ (194269891 / 1000000000) := by
  have h := checkLog_sound (w := (26803 / 276803)) (n := 12)
    (lo := (19426989 / 100000000)) (hi := (194269891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151803 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151803 / 125000) = 1/(125000 / 151803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (19426989 / 100000000) (194269891 / 1000000000) (Real.log (151803 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (151803 / 125000) = -Real.log (125000 / 151803) := by
    rw [show ((151803 / 125000) : ℝ) = ((125000 / 151803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (30167259 / 125000000) ≤ -Real.log (98197 / 125000) ∧
    -Real.log (98197 / 125000) ≤ (241338073 / 1000000000) := by
  have h := checkLog_sound (w := (26803 / 223197)) (n := 12)
    (lo := (30167259 / 125000000)) (hi := (241338073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 98197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 98197) = 1/(98197 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-241338073 / 1000000000) (-30167259 / 125000000) (Real.log (98197 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (194536647 / 1000000000) ≤ -Real.log (250000 / 303687) ∧
    -Real.log (250000 / 303687) ≤ (24317081 / 125000000) := by
  have h := checkLog_sound (w := (53687 / 553687)) (n := 12)
    (lo := (194536647 / 1000000000)) (hi := (24317081 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303687 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303687 / 250000) = 1/(250000 / 303687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (194536647 / 1000000000) (24317081 / 125000000) (Real.log (303687 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (303687 / 250000) = -Real.log (250000 / 303687) := by
    rw [show ((303687 / 250000) : ℝ) = ((250000 / 303687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (241750593 / 1000000000) ≤ -Real.log (196313 / 250000) ∧
    -Real.log (196313 / 250000) ≤ (120875297 / 500000000) := by
  have h := checkLog_sound (w := (53687 / 446313)) (n := 12)
    (lo := (241750593 / 1000000000)) (hi := (120875297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 196313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 196313) = 1/(196313 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-120875297 / 500000000) (-241750593 / 1000000000) (Real.log (196313 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (305009201 / 500000000) ≤ -Real.log (100000000000 / 184046526821) ∧
    -Real.log (100000000000 / 184046526821) ≤ (610018403 / 1000000000) := by
  have h := checkLog_sound (w := (84046526821 / 284046526821)) (n := 12)
    (lo := (305009201 / 500000000)) (hi := (610018403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184046526821 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184046526821 / 100000000000) = 1/(100000000000 / 184046526821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (305009201 / 500000000) (610018403 / 1000000000) (Real.log (184046526821 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (184046526821 / 100000000000) = -Real.log (100000000000 / 184046526821) := by
    rw [show ((184046526821 / 100000000000) : ℝ) = ((100000000000 / 184046526821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (305476141 / 500000000) ≤ -Real.log (500000000000 / 921092422167) ∧
    -Real.log (500000000000 / 921092422167) ≤ (610952283 / 1000000000) := by
  have h := checkLog_sound (w := (421092422167 / 1421092422167)) (n := 12)
    (lo := (305476141 / 500000000)) (hi := (610952283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((921092422167 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(921092422167 / 500000000000) = 1/(500000000000 / 921092422167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (305476141 / 500000000) (610952283 / 1000000000) (Real.log (921092422167 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (921092422167 / 500000000000) = -Real.log (500000000000 / 921092422167) := by
    rw [show ((921092422167 / 500000000000) : ℝ) = ((500000000000 / 921092422167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (217803981 / 500000000) ≤ -Real.log (250000000000 / 386475656079) ∧
    -Real.log (250000000000 / 386475656079) ≤ (435607963 / 1000000000) := by
  have h := checkLog_sound (w := (136475656079 / 636475656079)) (n := 12)
    (lo := (217803981 / 500000000)) (hi := (435607963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((386475656079 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(386475656079 / 250000000000) = 1/(250000000000 / 386475656079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (217803981 / 500000000) (435607963 / 1000000000) (Real.log (386475656079 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (386475656079 / 250000000000) = -Real.log (250000000000 / 386475656079) := by
    rw [show ((386475656079 / 250000000000) : ℝ) = ((250000000000 / 386475656079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (436287241 / 1000000000) ≤ -Real.log (31250000000 / 48342283751) ∧
    -Real.log (31250000000 / 48342283751) ≤ (218143621 / 500000000) := by
  have h := checkLog_sound (w := (17092283751 / 79592283751)) (n := 12)
    (lo := (436287241 / 1000000000)) (hi := (218143621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48342283751 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48342283751 / 31250000000) = 1/(31250000000 / 48342283751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (436287241 / 1000000000) (218143621 / 500000000) (Real.log (48342283751 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (48342283751 / 31250000000) = -Real.log (31250000000 / 48342283751) := by
    rw [show ((48342283751 / 31250000000) : ℝ) = ((31250000000 / 48342283751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0447

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0448Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0448
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

theorem reflection_log_1_neg : (188649151 / 1000000000) ≤ -Real.log (5120 / 6183) ∧
    -Real.log (5120 / 6183) ≤ (2947643 / 15625000) := by
  have h := checkLog_sound (w := (1063 / 11303)) (n := 12)
    (lo := (188649151 / 1000000000)) (hi := (2947643 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6183 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6183 / 5120) = 1/(5120 / 6183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (188649151 / 1000000000) (2947643 / 15625000) (Real.log (6183 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6183 / 5120) = -Real.log (5120 / 6183) := by
    rw [show ((6183 / 5120) : ℝ) = ((5120 / 6183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (116355327 / 500000000) ≤ -Real.log (4057 / 5120) ∧
    -Real.log (4057 / 5120) ≤ (46542131 / 200000000) := by
  have h := checkLog_sound (w := (1063 / 9177)) (n := 12)
    (lo := (116355327 / 500000000)) (hi := (46542131 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4057) = 1/(4057 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-46542131 / 200000000) (-116355327 / 500000000) (Real.log (4057 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (188406521 / 1000000000) ≤ -Real.log (10240 / 12363) ∧
    -Real.log (10240 / 12363) ≤ (94203261 / 500000000) := by
  have h := checkLog_sound (w := (2123 / 22603)) (n := 12)
    (lo := (188406521 / 1000000000)) (hi := (94203261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12363 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12363 / 10240) = 1/(10240 / 12363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (188406521 / 1000000000) (94203261 / 500000000) (Real.log (12363 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12363 / 10240) = -Real.log (10240 / 12363) := by
    rw [show ((12363 / 10240) : ℝ) = ((10240 / 12363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (232340991 / 1000000000) ≤ -Real.log (8117 / 10240) ∧
    -Real.log (8117 / 10240) ≤ (453791 / 1953125) := by
  have h := checkLog_sound (w := (2123 / 18357)) (n := 12)
    (lo := (232340991 / 1000000000)) (hi := (453791 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8117) = 1/(8117 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-453791 / 1953125) (-232340991 / 1000000000) (Real.log (8117 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (347295153 / 1000000000) ≤ -Real.log (2560 / 3623) ∧
    -Real.log (2560 / 3623) ≤ (173647577 / 500000000) := by
  have h := checkLog_sound (w := (1063 / 6183)) (n := 12)
    (lo := (347295153 / 1000000000)) (hi := (173647577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3623 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3623 / 2560) = 1/(2560 / 3623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (347295153 / 1000000000) (173647577 / 500000000) (Real.log (3623 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3623 / 2560) = -Real.log (2560 / 3623) := by
    rw [show ((3623 / 2560) : ℝ) = ((2560 / 3623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (536544153 / 1000000000) ≤ -Real.log (1497 / 2560) ∧
    -Real.log (1497 / 2560) ≤ (268272077 / 500000000) := by
  have h := checkLog_sound (w := (1063 / 4057)) (n := 12)
    (lo := (536544153 / 1000000000)) (hi := (268272077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1497) = 1/(1497 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-268272077 / 500000000) (-536544153 / 1000000000) (Real.log (1497 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (173440523 / 500000000) ≤ -Real.log (5120 / 7243) ∧
    -Real.log (5120 / 7243) ≤ (346881047 / 1000000000) := by
  have h := checkLog_sound (w := (2123 / 12363)) (n := 12)
    (lo := (173440523 / 500000000)) (hi := (346881047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7243 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7243 / 5120) = 1/(5120 / 7243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (173440523 / 500000000) (346881047 / 1000000000) (Real.log (7243 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7243 / 5120) = -Real.log (5120 / 7243) := by
    rw [show ((7243 / 5120) : ℝ) = ((5120 / 7243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (10710853 / 20000000) ≤ -Real.log (2997 / 5120) ∧
    -Real.log (2997 / 5120) ≤ (535542651 / 1000000000) := by
  have h := checkLog_sound (w := (2123 / 8117)) (n := 12)
    (lo := (10710853 / 20000000)) (hi := (535542651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2997) = 1/(2997 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-535542651 / 1000000000) (-10710853 / 20000000) (Real.log (2997 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (10354819 / 40000000) ≤ -Real.log (500000 / 647733) ∧
    -Real.log (500000 / 647733) ≤ (64717619 / 250000000) := by
  have h := checkLog_sound (w := (147733 / 1147733)) (n := 12)
    (lo := (10354819 / 40000000)) (hi := (64717619 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((647733 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(647733 / 500000) = 1/(500000 / 647733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (10354819 / 40000000) (64717619 / 250000000) (Real.log (647733 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (647733 / 500000) = -Real.log (500000 / 647733) := by
    rw [show ((647733 / 500000) : ℝ) = ((500000 / 647733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (350218687 / 1000000000) ≤ -Real.log (352267 / 500000) ∧
    -Real.log (352267 / 500000) ≤ (5472167 / 15625000) := by
  have h := checkLog_sound (w := (147733 / 852267)) (n := 12)
    (lo := (350218687 / 1000000000)) (hi := (5472167 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 352267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 352267) = 1/(352267 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-5472167 / 15625000) (-350218687 / 1000000000) (Real.log (352267 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (259198489 / 1000000000) ≤ -Real.log (1000000 / 1295891) ∧
    -Real.log (1000000 / 1295891) ≤ (25919849 / 100000000) := by
  have h := checkLog_sound (w := (295891 / 2295891)) (n := 12)
    (lo := (259198489 / 1000000000)) (hi := (25919849 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1295891 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1295891 / 1000000) = 1/(1000000 / 1295891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (259198489 / 1000000000) (25919849 / 100000000) (Real.log (1295891 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1295891 / 1000000) = -Real.log (1000000 / 1295891) := by
    rw [show ((1295891 / 1000000) : ℝ) = ((1000000 / 1295891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (70164421 / 200000000) ≤ -Real.log (704109 / 1000000) ∧
    -Real.log (704109 / 1000000) ≤ (175411053 / 500000000) := by
  have h := checkLog_sound (w := (295891 / 1704109)) (n := 12)
    (lo := (70164421 / 200000000)) (hi := (175411053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 704109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 704109) = 1/(704109 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-175411053 / 500000000) (-70164421 / 200000000) (Real.log (704109 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (38800777 / 200000000) ≤ -Real.log (1000000 / 1214101) ∧
    -Real.log (1000000 / 1214101) ≤ (97001943 / 500000000) := by
  have h := checkLog_sound (w := (214101 / 2214101)) (n := 12)
    (lo := (38800777 / 200000000)) (hi := (97001943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1214101 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1214101 / 1000000) = 1/(1000000 / 1214101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (38800777 / 200000000) (97001943 / 500000000) (Real.log (1214101 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1214101 / 1000000) = -Real.log (1000000 / 1214101) := by
    rw [show ((1214101 / 1000000) : ℝ) = ((1000000 / 1214101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (240926993 / 1000000000) ≤ -Real.log (785899 / 1000000) ∧
    -Real.log (785899 / 1000000) ≤ (120463497 / 500000000) := by
  have h := checkLog_sound (w := (214101 / 1785899)) (n := 12)
    (lo := (240926993 / 1000000000)) (hi := (120463497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 785899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 785899) = 1/(785899 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-120463497 / 500000000) (-240926993 / 1000000000) (Real.log (785899 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (194270713 / 1000000000) ≤ -Real.log (40000 / 48577) ∧
    -Real.log (40000 / 48577) ≤ (97135357 / 500000000) := by
  have h := checkLog_sound (w := (8577 / 88577)) (n := 12)
    (lo := (194270713 / 1000000000)) (hi := (97135357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48577 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48577 / 40000) = 1/(40000 / 48577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (194270713 / 1000000000) (97135357 / 500000000) (Real.log (48577 / 40000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (48577 / 40000) = -Real.log (40000 / 48577) := by
    rw [show ((48577 / 40000) : ℝ) = ((40000 / 48577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (48267869 / 200000000) ≤ -Real.log (31423 / 40000) ∧
    -Real.log (31423 / 40000) ≤ (120669673 / 500000000) := by
  have h := checkLog_sound (w := (8577 / 71423)) (n := 12)
    (lo := (48267869 / 200000000)) (hi := (120669673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 31423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 31423) = 1/(31423 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-120669673 / 500000000) (-48267869 / 200000000) (Real.log (31423 / 40000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (609089163 / 1000000000) ≤ -Real.log (500000000000 / 919377915047) ∧
    -Real.log (500000000000 / 919377915047) ≤ (152272291 / 250000000) := by
  have h := checkLog_sound (w := (419377915047 / 1419377915047)) (n := 12)
    (lo := (609089163 / 1000000000)) (hi := (152272291 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((919377915047 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(919377915047 / 500000000000) = 1/(500000000000 / 919377915047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (609089163 / 1000000000) (152272291 / 250000000) (Real.log (919377915047 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (919377915047 / 500000000000) = -Real.log (500000000000 / 919377915047) := by
    rw [show ((919377915047 / 500000000000) : ℝ) = ((500000000000 / 919377915047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (305010297 / 500000000) ≤ -Real.log (50000000000 / 92023465117) ∧
    -Real.log (50000000000 / 92023465117) ≤ (122004119 / 200000000) := by
  have h := checkLog_sound (w := (42023465117 / 142023465117)) (n := 12)
    (lo := (305010297 / 500000000)) (hi := (122004119 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92023465117 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92023465117 / 50000000000) = 1/(50000000000 / 92023465117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (305010297 / 500000000) (122004119 / 200000000) (Real.log (92023465117 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (92023465117 / 50000000000) = -Real.log (50000000000 / 92023465117) := by
    rw [show ((92023465117 / 50000000000) : ℝ) = ((50000000000 / 92023465117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (217465439 / 500000000) ≤ -Real.log (500000000000 / 772428136439) ∧
    -Real.log (500000000000 / 772428136439) ≤ (434930879 / 1000000000) := by
  have h := checkLog_sound (w := (272428136439 / 1272428136439)) (n := 12)
    (lo := (217465439 / 500000000)) (hi := (434930879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((772428136439 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(772428136439 / 500000000000) = 1/(500000000000 / 772428136439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (217465439 / 500000000) (434930879 / 1000000000) (Real.log (772428136439 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (772428136439 / 500000000000) = -Real.log (500000000000 / 772428136439) := by
    rw [show ((772428136439 / 500000000000) : ℝ) = ((500000000000 / 772428136439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (435610059 / 1000000000) ≤ -Real.log (250000000000 / 386476466283) ∧
    -Real.log (250000000000 / 386476466283) ≤ (21780503 / 50000000) := by
  have h := checkLog_sound (w := (136476466283 / 636476466283)) (n := 12)
    (lo := (435610059 / 1000000000)) (hi := (21780503 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((386476466283 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(386476466283 / 250000000000) = 1/(250000000000 / 386476466283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (435610059 / 1000000000) (21780503 / 50000000) (Real.log (386476466283 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (386476466283 / 250000000000) = -Real.log (250000000000 / 386476466283) := by
    rw [show ((386476466283 / 250000000000) : ℝ) = ((250000000000 / 386476466283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0448

end


