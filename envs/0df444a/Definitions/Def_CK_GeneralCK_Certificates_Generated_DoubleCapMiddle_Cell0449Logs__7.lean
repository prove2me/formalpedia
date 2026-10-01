-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0449Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0449Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:07:19.256987+00:00
-- url     : https://prove2.me/theorems/38b50e89-29c8-4b6d-96fe-d6c9bfdcadf4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0449Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0450Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0449Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0450Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0451Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0452Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0453Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0454Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0455Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0449Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0450Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0451Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0452Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0453Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0454Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0455Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0449Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0450Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0451Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0452Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0453Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0454Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0455Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0449Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0450Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0451Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0452Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0453Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0454Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0455Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0449Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0449
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

theorem reflection_log_1_neg : (188406521 / 1000000000) ≤ -Real.log (10240 / 12363) ∧
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


theorem reflection_log_1 : Bounds (188406521 / 1000000000) (94203261 / 500000000) (Real.log (12363 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12363 / 10240) = -Real.log (10240 / 12363) := by
    rw [show ((12363 / 10240) : ℝ) = ((10240 / 12363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (232340991 / 1000000000) ≤ -Real.log (8117 / 10240) ∧
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


theorem reflection_log_2 : Bounds (-453791 / 1953125) (-232340991 / 1000000000) (Real.log (8117 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (23520479 / 125000000) ≤ -Real.log (256 / 309) ∧
    -Real.log (256 / 309) ≤ (188163833 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 565)) (n := 12)
    (lo := (23520479 / 125000000)) (hi := (188163833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((309 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(309 / 256) = 1/(256 / 309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (23520479 / 125000000) (188163833 / 1000000000) (Real.log (309 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (309 / 256) = -Real.log (256 / 309) := by
    rw [show ((309 / 256) : ℝ) = ((256 / 309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (46394293 / 200000000) ≤ -Real.log (203 / 256) ∧
    -Real.log (203 / 256) ≤ (115985733 / 500000000) := by
  have h := checkLog_sound (w := (53 / 459)) (n := 12)
    (lo := (46394293 / 200000000)) (hi := (115985733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 203) = 1/(203 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-115985733 / 500000000) (-46394293 / 200000000) (Real.log (203 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (173440523 / 500000000) ≤ -Real.log (5120 / 7243) ∧
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


theorem reflection_log_5 : Bounds (173440523 / 500000000) (346881047 / 1000000000) (Real.log (7243 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7243 / 5120) = -Real.log (5120 / 7243) := by
    rw [show ((7243 / 5120) : ℝ) = ((5120 / 7243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (10710853 / 20000000) ≤ -Real.log (2997 / 5120) ∧
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


theorem reflection_log_6 : Bounds (-535542651 / 1000000000) (-10710853 / 20000000) (Real.log (2997 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (346466767 / 1000000000) ≤ -Real.log (128 / 181) ∧
    -Real.log (128 / 181) ≤ (21654173 / 62500000) := by
  have h := checkLog_sound (w := (53 / 309)) (n := 12)
    (lo := (346466767 / 1000000000)) (hi := (21654173 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181 / 128) = 1/(128 / 181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (346466767 / 1000000000) (21654173 / 62500000) (Real.log (181 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (181 / 128) = -Real.log (128 / 181) := by
    rw [show ((181 / 128) : ℝ) = ((128 / 181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (10690843 / 20000000) ≤ -Real.log (75 / 128) ∧
    -Real.log (75 / 128) ≤ (534542151 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 203)) (n := 12)
    (lo := (10690843 / 20000000)) (hi := (534542151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 75) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 75) = 1/(75 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-534542151 / 1000000000) (-10690843 / 20000000) (Real.log (75 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (129271177 / 500000000) ≤ -Real.log (1000000 / 1295041) ∧
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


theorem reflection_log_9 : Bounds (129271177 / 500000000) (51708471 / 200000000) (Real.log (1295041 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1295041 / 1000000) = -Real.log (1000000 / 1295041) := by
    rw [show ((1295041 / 1000000) : ℝ) = ((1000000 / 1295041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (349615633 / 1000000000) ≤ -Real.log (704959 / 1000000) ∧
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


theorem reflection_log_10 : Bounds (-174807817 / 500000000) (-349615633 / 1000000000) (Real.log (704959 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (258871247 / 1000000000) ≤ -Real.log (1000000 / 1295467) ∧
    -Real.log (1000000 / 1295467) ≤ (16179453 / 62500000) := by
  have h := checkLog_sound (w := (295467 / 2295467)) (n := 12)
    (lo := (258871247 / 1000000000)) (hi := (16179453 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1295467 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1295467 / 1000000) = 1/(1000000 / 1295467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (258871247 / 1000000000) (16179453 / 62500000) (Real.log (1295467 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1295467 / 1000000) = -Real.log (1000000 / 1295467) := by
    rw [show ((1295467 / 1000000) : ℝ) = ((1000000 / 1295467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (350220107 / 1000000000) ≤ -Real.log (704533 / 1000000) ∧
    -Real.log (704533 / 1000000) ≤ (87555027 / 250000000) := by
  have h := checkLog_sound (w := (295467 / 1704533)) (n := 12)
    (lo := (350220107 / 1000000000)) (hi := (87555027 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 704533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 704533) = 1/(704533 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-87555027 / 250000000) (-350220107 / 1000000000) (Real.log (704533 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (193737809 / 1000000000) ≤ -Real.log (500000 / 606889) ∧
    -Real.log (500000 / 606889) ≤ (19373781 / 100000000) := by
  have h := checkLog_sound (w := (106889 / 1106889)) (n := 12)
    (lo := (193737809 / 1000000000)) (hi := (19373781 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606889 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606889 / 500000) = 1/(500000 / 606889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (193737809 / 1000000000) (19373781 / 100000000) (Real.log (606889 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (606889 / 500000) = -Real.log (500000 / 606889) := by
    rw [show ((606889 / 500000) : ℝ) = ((500000 / 606889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (240516083 / 1000000000) ≤ -Real.log (393111 / 500000) ∧
    -Real.log (393111 / 500000) ≤ (60129021 / 250000000) := by
  have h := checkLog_sound (w := (106889 / 893111)) (n := 12)
    (lo := (240516083 / 1000000000)) (hi := (60129021 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 393111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 393111) = 1/(393111 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-60129021 / 250000000) (-240516083 / 1000000000) (Real.log (393111 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (48501177 / 250000000) ≤ -Real.log (500000 / 607051) ∧
    -Real.log (500000 / 607051) ≤ (194004709 / 1000000000) := by
  have h := checkLog_sound (w := (107051 / 1107051)) (n := 12)
    (lo := (48501177 / 250000000)) (hi := (194004709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607051 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607051 / 500000) = 1/(500000 / 607051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (48501177 / 250000000) (194004709 / 1000000000) (Real.log (607051 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (607051 / 500000) = -Real.log (500000 / 607051) := by
    rw [show ((607051 / 500000) : ℝ) = ((500000 / 607051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (48185653 / 200000000) ≤ -Real.log (392949 / 500000) ∧
    -Real.log (392949 / 500000) ≤ (120464133 / 500000000) := by
  have h := checkLog_sound (w := (107051 / 892949)) (n := 12)
    (lo := (48185653 / 200000000)) (hi := (120464133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 392949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 392949) = 1/(392949 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-120464133 / 500000000) (-48185653 / 200000000) (Real.log (392949 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (152039497 / 250000000) ≤ -Real.log (50000000000 / 91852221193) ∧
    -Real.log (50000000000 / 91852221193) ≤ (608157989 / 1000000000) := by
  have h := checkLog_sound (w := (41852221193 / 141852221193)) (n := 12)
    (lo := (152039497 / 250000000)) (hi := (608157989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91852221193 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91852221193 / 50000000000) = 1/(50000000000 / 91852221193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (152039497 / 250000000) (608157989 / 1000000000) (Real.log (91852221193 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (91852221193 / 50000000000) = -Real.log (50000000000 / 91852221193) := by
    rw [show ((91852221193 / 50000000000) : ℝ) = ((50000000000 / 91852221193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (304545677 / 500000000) ≤ -Real.log (125000000000 / 229844982421) ∧
    -Real.log (125000000000 / 229844982421) ≤ (121818271 / 200000000) := by
  have h := checkLog_sound (w := (104844982421 / 354844982421)) (n := 12)
    (lo := (304545677 / 500000000)) (hi := (121818271 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229844982421 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(229844982421 / 125000000000) = 1/(125000000000 / 229844982421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (304545677 / 500000000) (121818271 / 200000000) (Real.log (229844982421 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (229844982421 / 125000000000) = -Real.log (125000000000 / 229844982421) := by
    rw [show ((229844982421 / 125000000000) : ℝ) = ((125000000000 / 229844982421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (434253893 / 1000000000) ≤ -Real.log (500000000000 / 771905390589) ∧
    -Real.log (500000000000 / 771905390589) ≤ (217126947 / 500000000) := by
  have h := checkLog_sound (w := (271905390589 / 1271905390589)) (n := 12)
    (lo := (434253893 / 1000000000)) (hi := (217126947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((771905390589 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(771905390589 / 500000000000) = 1/(500000000000 / 771905390589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (434253893 / 1000000000) (217126947 / 500000000) (Real.log (771905390589 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (771905390589 / 500000000000) = -Real.log (500000000000 / 771905390589) := by
    rw [show ((771905390589 / 500000000000) : ℝ) = ((500000000000 / 771905390589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (217466487 / 500000000) ≤ -Real.log (125000000000 / 193107438879) ∧
    -Real.log (125000000000 / 193107438879) ≤ (17397319 / 40000000) := by
  have h := checkLog_sound (w := (68107438879 / 318107438879)) (n := 12)
    (lo := (217466487 / 500000000)) (hi := (17397319 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((193107438879 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(193107438879 / 125000000000) = 1/(125000000000 / 193107438879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (217466487 / 500000000) (17397319 / 40000000) (Real.log (193107438879 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (193107438879 / 125000000000) = -Real.log (125000000000 / 193107438879) := by
    rw [show ((193107438879 / 125000000000) : ℝ) = ((125000000000 / 193107438879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0449

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0450Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0450
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

theorem reflection_log_1_neg : (23520479 / 125000000) ≤ -Real.log (256 / 309) ∧
    -Real.log (256 / 309) ≤ (188163833 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 565)) (n := 12)
    (lo := (23520479 / 125000000)) (hi := (188163833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((309 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(309 / 256) = 1/(256 / 309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (23520479 / 125000000) (188163833 / 1000000000) (Real.log (309 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (309 / 256) = -Real.log (256 / 309) := by
    rw [show ((309 / 256) : ℝ) = ((256 / 309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (46394293 / 200000000) ≤ -Real.log (203 / 256) ∧
    -Real.log (203 / 256) ≤ (115985733 / 500000000) := by
  have h := checkLog_sound (w := (53 / 459)) (n := 12)
    (lo := (46394293 / 200000000)) (hi := (115985733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 203) = 1/(203 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-115985733 / 500000000) (-46394293 / 200000000) (Real.log (203 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (46980271 / 250000000) ≤ -Real.log (10240 / 12357) ∧
    -Real.log (10240 / 12357) ≤ (37584217 / 200000000) := by
  have h := checkLog_sound (w := (2117 / 22597)) (n := 12)
    (lo := (46980271 / 250000000)) (hi := (37584217 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12357 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12357 / 10240) = 1/(10240 / 12357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (46980271 / 250000000) (37584217 / 200000000) (Real.log (12357 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12357 / 10240) = -Real.log (10240 / 12357) := by
    rw [show ((12357 / 10240) : ℝ) = ((10240 / 12357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (9264083 / 40000000) ≤ -Real.log (8123 / 10240) ∧
    -Real.log (8123 / 10240) ≤ (57900519 / 250000000) := by
  have h := checkLog_sound (w := (2117 / 18363)) (n := 12)
    (lo := (9264083 / 40000000)) (hi := (57900519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8123) = 1/(8123 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-57900519 / 250000000) (-9264083 / 40000000) (Real.log (8123 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (346466767 / 1000000000) ≤ -Real.log (128 / 181) ∧
    -Real.log (128 / 181) ≤ (21654173 / 62500000) := by
  have h := checkLog_sound (w := (53 / 309)) (n := 12)
    (lo := (346466767 / 1000000000)) (hi := (21654173 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181 / 128) = 1/(128 / 181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (346466767 / 1000000000) (21654173 / 62500000) (Real.log (181 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (181 / 128) = -Real.log (128 / 181) := by
    rw [show ((181 / 128) : ℝ) = ((128 / 181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (10690843 / 20000000) ≤ -Real.log (75 / 128) ∧
    -Real.log (75 / 128) ≤ (534542151 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 203)) (n := 12)
    (lo := (10690843 / 20000000)) (hi := (534542151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 75) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 75) = 1/(75 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-534542151 / 1000000000) (-10690843 / 20000000) (Real.log (75 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (86513079 / 250000000) ≤ -Real.log (5120 / 7237) ∧
    -Real.log (5120 / 7237) ≤ (346052317 / 1000000000) := by
  have h := checkLog_sound (w := (2117 / 12357)) (n := 12)
    (lo := (86513079 / 250000000)) (hi := (346052317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7237 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7237 / 5120) = 1/(5120 / 7237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (86513079 / 250000000) (346052317 / 1000000000) (Real.log (7237 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7237 / 5120) = -Real.log (5120 / 7237) := by
    rw [show ((7237 / 5120) : ℝ) = ((5120 / 7237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (10670853 / 20000000) ≤ -Real.log (3003 / 5120) ∧
    -Real.log (3003 / 5120) ≤ (533542651 / 1000000000) := by
  have h := checkLog_sound (w := (2117 / 8123)) (n := 12)
    (lo := (10670853 / 20000000)) (hi := (533542651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3003) = 1/(3003 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-533542651 / 1000000000) (-10670853 / 20000000) (Real.log (3003 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (129107449 / 500000000) ≤ -Real.log (1000000 / 1294617) ∧
    -Real.log (1000000 / 1294617) ≤ (258214899 / 1000000000) := by
  have h := checkLog_sound (w := (294617 / 2294617)) (n := 12)
    (lo := (129107449 / 500000000)) (hi := (258214899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1294617 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1294617 / 1000000) = 1/(1000000 / 1294617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (129107449 / 500000000) (258214899 / 1000000000) (Real.log (1294617 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1294617 / 1000000) = -Real.log (1000000 / 1294617) := by
    rw [show ((1294617 / 1000000) : ℝ) = ((1000000 / 1294617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (349014361 / 1000000000) ≤ -Real.log (705383 / 1000000) ∧
    -Real.log (705383 / 1000000) ≤ (174507181 / 500000000) := by
  have h := checkLog_sound (w := (294617 / 1705383)) (n := 12)
    (lo := (349014361 / 1000000000)) (hi := (174507181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 705383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 705383) = 1/(705383 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-174507181 / 500000000) (-349014361 / 1000000000) (Real.log (705383 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (258543127 / 1000000000) ≤ -Real.log (500000 / 647521) ∧
    -Real.log (500000 / 647521) ≤ (32317891 / 125000000) := by
  have h := checkLog_sound (w := (147521 / 1147521)) (n := 12)
    (lo := (258543127 / 1000000000)) (hi := (32317891 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((647521 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(647521 / 500000) = 1/(500000 / 647521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (258543127 / 1000000000) (32317891 / 125000000) (Real.log (647521 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (647521 / 500000) = -Real.log (500000 / 647521) := by
    rw [show ((647521 / 500000) : ℝ) = ((500000 / 647521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (87404263 / 250000000) ≤ -Real.log (352479 / 500000) ∧
    -Real.log (352479 / 500000) ≤ (349617053 / 1000000000) := by
  have h := checkLog_sound (w := (147521 / 852479)) (n := 12)
    (lo := (87404263 / 250000000)) (hi := (349617053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 352479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 352479) = 1/(352479 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-349617053 / 1000000000) (-87404263 / 250000000) (Real.log (352479 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (96736243 / 500000000) ≤ -Real.log (62500 / 75841) ∧
    -Real.log (62500 / 75841) ≤ (193472487 / 1000000000) := by
  have h := checkLog_sound (w := (13341 / 138341)) (n := 12)
    (lo := (96736243 / 500000000)) (hi := (193472487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75841 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75841 / 62500) = 1/(62500 / 75841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (96736243 / 500000000) (193472487 / 1000000000) (Real.log (75841 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (75841 / 62500) = -Real.log (62500 / 75841) := by
    rw [show ((75841 / 62500) : ℝ) = ((62500 / 75841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (240106613 / 1000000000) ≤ -Real.log (49159 / 62500) ∧
    -Real.log (49159 / 62500) ≤ (120053307 / 500000000) := by
  have h := checkLog_sound (w := (13341 / 111659)) (n := 12)
    (lo := (240106613 / 1000000000)) (hi := (120053307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 49159) = 1/(49159 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-120053307 / 500000000) (-240106613 / 1000000000) (Real.log (49159 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (193738633 / 1000000000) ≤ -Real.log (1000000 / 1213779) ∧
    -Real.log (1000000 / 1213779) ≤ (96869317 / 500000000) := by
  have h := checkLog_sound (w := (213779 / 2213779)) (n := 12)
    (lo := (193738633 / 1000000000)) (hi := (96869317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1213779 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1213779 / 1000000) = 1/(1000000 / 1213779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (193738633 / 1000000000) (96869317 / 500000000) (Real.log (1213779 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1213779 / 1000000) = -Real.log (1000000 / 1213779) := by
    rw [show ((1213779 / 1000000) : ℝ) = ((1000000 / 1213779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (48103471 / 200000000) ≤ -Real.log (786221 / 1000000) ∧
    -Real.log (786221 / 1000000) ≤ (60129339 / 250000000) := by
  have h := checkLog_sound (w := (213779 / 1786221)) (n := 12)
    (lo := (48103471 / 200000000)) (hi := (60129339 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 786221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 786221) = 1/(786221 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-60129339 / 250000000) (-48103471 / 200000000) (Real.log (786221 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (607229259 / 1000000000) ≤ -Real.log (500000000000 / 917669549733) ∧
    -Real.log (500000000000 / 917669549733) ≤ (30361463 / 50000000) := by
  have h := checkLog_sound (w := (417669549733 / 1417669549733)) (n := 12)
    (lo := (607229259 / 1000000000)) (hi := (30361463 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((917669549733 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(917669549733 / 500000000000) = 1/(500000000000 / 917669549733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (607229259 / 1000000000) (30361463 / 50000000) (Real.log (917669549733 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (917669549733 / 500000000000) = -Real.log (500000000000 / 917669549733) := by
    rw [show ((917669549733 / 500000000000) : ℝ) = ((500000000000 / 917669549733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (608160179 / 1000000000) ≤ -Real.log (500000000000 / 918524224139) ∧
    -Real.log (500000000000 / 918524224139) ≤ (30408009 / 50000000) := by
  have h := checkLog_sound (w := (418524224139 / 1418524224139)) (n := 12)
    (lo := (608160179 / 1000000000)) (hi := (30408009 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((918524224139 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(918524224139 / 500000000000) = 1/(500000000000 / 918524224139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (608160179 / 1000000000) (30408009 / 50000000) (Real.log (918524224139 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (918524224139 / 500000000000) = -Real.log (500000000000 / 918524224139) := by
    rw [show ((918524224139 / 500000000000) : ℝ) = ((500000000000 / 918524224139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4335791 / 10000000) ≤ -Real.log (250000000000 / 385692345247) ∧
    -Real.log (250000000000 / 385692345247) ≤ (433579101 / 1000000000) := by
  have h := checkLog_sound (w := (135692345247 / 635692345247)) (n := 12)
    (lo := (4335791 / 10000000)) (hi := (433579101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((385692345247 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(385692345247 / 250000000000) = 1/(250000000000 / 385692345247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4335791 / 10000000) (433579101 / 1000000000) (Real.log (385692345247 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (385692345247 / 250000000000) = -Real.log (250000000000 / 385692345247) := by
    rw [show ((385692345247 / 250000000000) : ℝ) = ((250000000000 / 385692345247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (108563997 / 250000000) ≤ -Real.log (100000000000 / 154381401667) ∧
    -Real.log (100000000000 / 154381401667) ≤ (434255989 / 1000000000) := by
  have h := checkLog_sound (w := (54381401667 / 254381401667)) (n := 12)
    (lo := (108563997 / 250000000)) (hi := (434255989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154381401667 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154381401667 / 100000000000) = 1/(100000000000 / 154381401667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (108563997 / 250000000) (434255989 / 1000000000) (Real.log (154381401667 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (154381401667 / 100000000000) = -Real.log (100000000000 / 154381401667) := by
    rw [show ((154381401667 / 100000000000) : ℝ) = ((100000000000 / 154381401667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0450

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0451Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0451
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

theorem reflection_log_1_neg : (46980271 / 250000000) ≤ -Real.log (10240 / 12357) ∧
    -Real.log (10240 / 12357) ≤ (37584217 / 200000000) := by
  have h := checkLog_sound (w := (2117 / 22597)) (n := 12)
    (lo := (46980271 / 250000000)) (hi := (37584217 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12357 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12357 / 10240) = 1/(10240 / 12357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (46980271 / 250000000) (37584217 / 200000000) (Real.log (12357 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12357 / 10240) = -Real.log (10240 / 12357) := by
    rw [show ((12357 / 10240) : ℝ) = ((10240 / 12357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (9264083 / 40000000) ≤ -Real.log (8123 / 10240) ∧
    -Real.log (8123 / 10240) ≤ (57900519 / 250000000) := by
  have h := checkLog_sound (w := (2117 / 18363)) (n := 12)
    (lo := (9264083 / 40000000)) (hi := (57900519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8123) = 1/(8123 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-57900519 / 250000000) (-9264083 / 40000000) (Real.log (8123 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (187678277 / 1000000000) ≤ -Real.log (5120 / 6177) ∧
    -Real.log (5120 / 6177) ≤ (93839139 / 500000000) := by
  have h := checkLog_sound (w := (1057 / 11297)) (n := 12)
    (lo := (187678277 / 1000000000)) (hi := (93839139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6177 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6177 / 5120) = 1/(5120 / 6177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (187678277 / 1000000000) (93839139 / 500000000) (Real.log (6177 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6177 / 5120) = -Real.log (5120 / 6177) := by
    rw [show ((6177 / 5120) : ℝ) = ((5120 / 6177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (115616411 / 500000000) ≤ -Real.log (4063 / 5120) ∧
    -Real.log (4063 / 5120) ≤ (231232823 / 1000000000) := by
  have h := checkLog_sound (w := (1057 / 9183)) (n := 12)
    (lo := (115616411 / 500000000)) (hi := (231232823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4063) = 1/(4063 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-231232823 / 1000000000) (-115616411 / 500000000) (Real.log (4063 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (86513079 / 250000000) ≤ -Real.log (5120 / 7237) ∧
    -Real.log (5120 / 7237) ≤ (346052317 / 1000000000) := by
  have h := checkLog_sound (w := (2117 / 12357)) (n := 12)
    (lo := (86513079 / 250000000)) (hi := (346052317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7237 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7237 / 5120) = 1/(5120 / 7237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (86513079 / 250000000) (346052317 / 1000000000) (Real.log (7237 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7237 / 5120) = -Real.log (5120 / 7237) := by
    rw [show ((7237 / 5120) : ℝ) = ((5120 / 7237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (10670853 / 20000000) ≤ -Real.log (3003 / 5120) ∧
    -Real.log (3003 / 5120) ≤ (533542651 / 1000000000) := by
  have h := checkLog_sound (w := (2117 / 8123)) (n := 12)
    (lo := (10670853 / 20000000)) (hi := (533542651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3003) = 1/(3003 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-533542651 / 1000000000) (-10670853 / 20000000) (Real.log (3003 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (172818847 / 500000000) ≤ -Real.log (2560 / 3617) ∧
    -Real.log (2560 / 3617) ≤ (69127539 / 200000000) := by
  have h := checkLog_sound (w := (1057 / 6177)) (n := 12)
    (lo := (172818847 / 500000000)) (hi := (69127539 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3617 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3617 / 2560) = 1/(2560 / 3617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (172818847 / 500000000) (69127539 / 200000000) (Real.log (3617 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3617 / 2560) = -Real.log (2560 / 3617) := by
    rw [show ((3617 / 2560) : ℝ) = ((2560 / 3617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (532544147 / 1000000000) ≤ -Real.log (1503 / 2560) ∧
    -Real.log (1503 / 2560) ≤ (133136037 / 250000000) := by
  have h := checkLog_sound (w := (1057 / 4063)) (n := 12)
    (lo := (532544147 / 1000000000)) (hi := (133136037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1503) = 1/(1503 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-133136037 / 250000000) (-532544147 / 1000000000) (Real.log (1503 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (128943281 / 500000000) ≤ -Real.log (62500 / 80887) ∧
    -Real.log (62500 / 80887) ≤ (257886563 / 1000000000) := by
  have h := checkLog_sound (w := (18387 / 143387)) (n := 12)
    (lo := (128943281 / 500000000)) (hi := (257886563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80887 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80887 / 62500) = 1/(62500 / 80887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (128943281 / 500000000) (257886563 / 1000000000) (Real.log (80887 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (80887 / 62500) = -Real.log (62500 / 80887) := by
    rw [show ((80887 / 62500) : ℝ) = ((62500 / 80887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (348412033 / 1000000000) ≤ -Real.log (44113 / 62500) ∧
    -Real.log (44113 / 62500) ≤ (174206017 / 500000000) := by
  have h := checkLog_sound (w := (18387 / 106613)) (n := 12)
    (lo := (348412033 / 1000000000)) (hi := (174206017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 44113) = 1/(44113 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-174206017 / 500000000) (-348412033 / 1000000000) (Real.log (44113 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (25821567 / 100000000) ≤ -Real.log (500000 / 647309) ∧
    -Real.log (500000 / 647309) ≤ (258215671 / 1000000000) := by
  have h := checkLog_sound (w := (147309 / 1147309)) (n := 12)
    (lo := (25821567 / 100000000)) (hi := (258215671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((647309 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(647309 / 500000) = 1/(500000 / 647309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (25821567 / 100000000) (258215671 / 1000000000) (Real.log (647309 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (647309 / 500000) = -Real.log (500000 / 647309) := by
    rw [show ((647309 / 500000) : ℝ) = ((500000 / 647309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (174507889 / 500000000) ≤ -Real.log (352691 / 500000) ∧
    -Real.log (352691 / 500000) ≤ (349015779 / 1000000000) := by
  have h := checkLog_sound (w := (147309 / 852691)) (n := 12)
    (lo := (174507889 / 500000000)) (hi := (349015779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 352691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 352691) = 1/(352691 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-349015779 / 1000000000) (-174507889 / 500000000) (Real.log (352691 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (193206269 / 1000000000) ≤ -Real.log (1000000 / 1213133) ∧
    -Real.log (1000000 / 1213133) ≤ (19320627 / 100000000) := by
  have h := checkLog_sound (w := (213133 / 2213133)) (n := 12)
    (lo := (193206269 / 1000000000)) (hi := (19320627 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1213133 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1213133 / 1000000) = 1/(1000000 / 1213133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (193206269 / 1000000000) (19320627 / 100000000) (Real.log (1213133 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1213133 / 1000000) = -Real.log (1000000 / 1213133) := by
    rw [show ((1213133 / 1000000) : ℝ) = ((1000000 / 1213133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (239696041 / 1000000000) ≤ -Real.log (786867 / 1000000) ∧
    -Real.log (786867 / 1000000) ≤ (119848021 / 500000000) := by
  have h := checkLog_sound (w := (213133 / 1786867)) (n := 12)
    (lo := (239696041 / 1000000000)) (hi := (119848021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 786867) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 786867) = 1/(786867 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-119848021 / 500000000) (-239696041 / 1000000000) (Real.log (786867 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (19347331 / 100000000) ≤ -Real.log (1000000 / 1213457) ∧
    -Real.log (1000000 / 1213457) ≤ (193473311 / 1000000000) := by
  have h := checkLog_sound (w := (213457 / 2213457)) (n := 12)
    (lo := (19347331 / 100000000)) (hi := (193473311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1213457 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1213457 / 1000000) = 1/(1000000 / 1213457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (19347331 / 100000000) (193473311 / 1000000000) (Real.log (1213457 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1213457 / 1000000) = -Real.log (1000000 / 1213457) := by
    rw [show ((1213457 / 1000000) : ℝ) = ((1000000 / 1213457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (48021577 / 200000000) ≤ -Real.log (786543 / 1000000) ∧
    -Real.log (786543 / 1000000) ≤ (120053943 / 500000000) := by
  have h := checkLog_sound (w := (213457 / 1786543)) (n := 12)
    (lo := (48021577 / 200000000)) (hi := (120053943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 786543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 786543) = 1/(786543 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-120053943 / 500000000) (-48021577 / 200000000) (Real.log (786543 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (121259719 / 200000000) ≤ -Real.log (15625000000 / 28650497019) ∧
    -Real.log (15625000000 / 28650497019) ≤ (151574649 / 250000000) := by
  have h := checkLog_sound (w := (13025497019 / 44275497019)) (n := 12)
    (lo := (121259719 / 200000000)) (hi := (151574649 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28650497019 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28650497019 / 15625000000) = 1/(15625000000 / 28650497019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (121259719 / 200000000) (151574649 / 250000000) (Real.log (28650497019 / 15625000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (28650497019 / 15625000000) = -Real.log (15625000000 / 28650497019) := by
    rw [show ((28650497019 / 15625000000) : ℝ) = ((15625000000 / 28650497019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (607231449 / 1000000000) ≤ -Real.log (125000000000 / 229417889881) ∧
    -Real.log (125000000000 / 229417889881) ≤ (12144629 / 20000000) := by
  have h := checkLog_sound (w := (104417889881 / 354417889881)) (n := 12)
    (lo := (607231449 / 1000000000)) (hi := (12144629 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229417889881 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(229417889881 / 125000000000) = 1/(125000000000 / 229417889881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (607231449 / 1000000000) (12144629 / 20000000) (Real.log (229417889881 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (229417889881 / 125000000000) = -Real.log (125000000000 / 229417889881) := by
    rw [show ((229417889881 / 125000000000) : ℝ) = ((125000000000 / 229417889881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (43290231 / 100000000) ≤ -Real.log (62500000000 / 96357850183) ∧
    -Real.log (62500000000 / 96357850183) ≤ (432902311 / 1000000000) := by
  have h := checkLog_sound (w := (33857850183 / 158857850183)) (n := 12)
    (lo := (43290231 / 100000000)) (hi := (432902311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96357850183 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96357850183 / 62500000000) = 1/(62500000000 / 96357850183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (43290231 / 100000000) (432902311 / 1000000000) (Real.log (96357850183 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (96357850183 / 62500000000) = -Real.log (62500000000 / 96357850183) := by
    rw [show ((96357850183 / 62500000000) : ℝ) = ((62500000000 / 96357850183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (108395299 / 250000000) ≤ -Real.log (125000000000 / 192846576729) ∧
    -Real.log (125000000000 / 192846576729) ≤ (433581197 / 1000000000) := by
  have h := checkLog_sound (w := (67846576729 / 317846576729)) (n := 12)
    (lo := (108395299 / 250000000)) (hi := (433581197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((192846576729 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(192846576729 / 125000000000) = 1/(125000000000 / 192846576729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (108395299 / 250000000) (433581197 / 1000000000) (Real.log (192846576729 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (192846576729 / 125000000000) = -Real.log (125000000000 / 192846576729) := by
    rw [show ((192846576729 / 125000000000) : ℝ) = ((125000000000 / 192846576729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0451

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0452Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0452
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

theorem reflection_log_1_neg : (187678277 / 1000000000) ≤ -Real.log (5120 / 6177) ∧
    -Real.log (5120 / 6177) ≤ (93839139 / 500000000) := by
  have h := checkLog_sound (w := (1057 / 11297)) (n := 12)
    (lo := (187678277 / 1000000000)) (hi := (93839139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6177 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6177 / 5120) = 1/(5120 / 6177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (187678277 / 1000000000) (93839139 / 500000000) (Real.log (6177 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6177 / 5120) = -Real.log (5120 / 6177) := by
    rw [show ((6177 / 5120) : ℝ) = ((5120 / 6177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (115616411 / 500000000) ≤ -Real.log (4063 / 5120) ∧
    -Real.log (4063 / 5120) ≤ (231232823 / 1000000000) := by
  have h := checkLog_sound (w := (1057 / 9183)) (n := 12)
    (lo := (115616411 / 500000000)) (hi := (231232823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4063) = 1/(4063 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-231232823 / 1000000000) (-115616411 / 500000000) (Real.log (4063 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (187435411 / 1000000000) ≤ -Real.log (10240 / 12351) ∧
    -Real.log (10240 / 12351) ≤ (46858853 / 250000000) := by
  have h := checkLog_sound (w := (2111 / 22591)) (n := 12)
    (lo := (187435411 / 1000000000)) (hi := (46858853 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12351 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12351 / 10240) = 1/(10240 / 12351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (187435411 / 1000000000) (46858853 / 250000000) (Real.log (12351 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12351 / 10240) = -Real.log (10240 / 12351) := by
    rw [show ((12351 / 10240) : ℝ) = ((10240 / 12351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (28857963 / 125000000) ≤ -Real.log (8129 / 10240) ∧
    -Real.log (8129 / 10240) ≤ (46172741 / 200000000) := by
  have h := checkLog_sound (w := (2111 / 18369)) (n := 12)
    (lo := (28857963 / 125000000)) (hi := (46172741 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8129) = 1/(8129 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-46172741 / 200000000) (-28857963 / 125000000) (Real.log (8129 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (172818847 / 500000000) ≤ -Real.log (2560 / 3617) ∧
    -Real.log (2560 / 3617) ≤ (69127539 / 200000000) := by
  have h := checkLog_sound (w := (1057 / 6177)) (n := 12)
    (lo := (172818847 / 500000000)) (hi := (69127539 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3617 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3617 / 2560) = 1/(2560 / 3617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (172818847 / 500000000) (69127539 / 200000000) (Real.log (3617 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3617 / 2560) = -Real.log (2560 / 3617) := by
    rw [show ((3617 / 2560) : ℝ) = ((2560 / 3617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (532544147 / 1000000000) ≤ -Real.log (1503 / 2560) ∧
    -Real.log (1503 / 2560) ≤ (133136037 / 250000000) := by
  have h := checkLog_sound (w := (1057 / 4063)) (n := 12)
    (lo := (532544147 / 1000000000)) (hi := (133136037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1503) = 1/(1503 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-133136037 / 250000000) (-532544147 / 1000000000) (Real.log (1503 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (3452229 / 10000000) ≤ -Real.log (5120 / 7231) ∧
    -Real.log (5120 / 7231) ≤ (345222901 / 1000000000) := by
  have h := checkLog_sound (w := (2111 / 12351)) (n := 12)
    (lo := (3452229 / 10000000)) (hi := (345222901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7231 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7231 / 5120) = 1/(5120 / 7231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (3452229 / 10000000) (345222901 / 1000000000) (Real.log (7231 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7231 / 5120) = -Real.log (5120 / 7231) := by
    rw [show ((7231 / 5120) : ℝ) = ((5120 / 7231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (531546641 / 1000000000) ≤ -Real.log (3009 / 5120) ∧
    -Real.log (3009 / 5120) ≤ (265773321 / 500000000) := by
  have h := checkLog_sound (w := (2111 / 8129)) (n := 12)
    (lo := (531546641 / 1000000000)) (hi := (265773321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3009) = 1/(3009 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-265773321 / 500000000) (-531546641 / 1000000000) (Real.log (3009 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (25755889 / 100000000) ≤ -Real.log (125000 / 161721) ∧
    -Real.log (125000 / 161721) ≤ (257558891 / 1000000000) := by
  have h := checkLog_sound (w := (36721 / 286721)) (n := 12)
    (lo := (25755889 / 100000000)) (hi := (257558891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161721 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161721 / 125000) = 1/(125000 / 161721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (25755889 / 100000000) (257558891 / 1000000000) (Real.log (161721 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (161721 / 125000) = -Real.log (125000 / 161721) := by
    rw [show ((161721 / 125000) : ℝ) = ((125000 / 161721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (347811483 / 1000000000) ≤ -Real.log (88279 / 125000) ∧
    -Real.log (88279 / 125000) ≤ (86952871 / 250000000) := by
  have h := checkLog_sound (w := (36721 / 213279)) (n := 12)
    (lo := (347811483 / 1000000000)) (hi := (86952871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 88279) = 1/(88279 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-86952871 / 250000000) (-347811483 / 1000000000) (Real.log (88279 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (128943667 / 500000000) ≤ -Real.log (1000000 / 1294193) ∧
    -Real.log (1000000 / 1294193) ≤ (51577467 / 200000000) := by
  have h := checkLog_sound (w := (294193 / 2294193)) (n := 12)
    (lo := (128943667 / 500000000)) (hi := (51577467 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1294193 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1294193 / 1000000) = 1/(1000000 / 1294193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (128943667 / 500000000) (51577467 / 200000000) (Real.log (1294193 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1294193 / 1000000) = -Real.log (1000000 / 1294193) := by
    rw [show ((1294193 / 1000000) : ℝ) = ((1000000 / 1294193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (348413449 / 1000000000) ≤ -Real.log (705807 / 1000000) ∧
    -Real.log (705807 / 1000000) ≤ (6968269 / 20000000) := by
  have h := checkLog_sound (w := (294193 / 1705807)) (n := 12)
    (lo := (348413449 / 1000000000)) (hi := (6968269 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 705807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 705807) = 1/(705807 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-6968269 / 20000000) (-348413449 / 1000000000) (Real.log (705807 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (38588161 / 200000000) ≤ -Real.log (1000000 / 1212811) ∧
    -Real.log (1000000 / 1212811) ≤ (96470403 / 500000000) := by
  have h := checkLog_sound (w := (212811 / 2212811)) (n := 12)
    (lo := (38588161 / 200000000)) (hi := (96470403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1212811 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1212811 / 1000000) = 1/(1000000 / 1212811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (38588161 / 200000000) (96470403 / 500000000) (Real.log (1212811 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1212811 / 1000000) = -Real.log (1000000 / 1212811) := by
    rw [show ((1212811 / 1000000) : ℝ) = ((1000000 / 1212811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (119643453 / 500000000) ≤ -Real.log (787189 / 1000000) ∧
    -Real.log (787189 / 1000000) ≤ (239286907 / 1000000000) := by
  have h := checkLog_sound (w := (212811 / 1787189)) (n := 12)
    (lo := (119643453 / 500000000)) (hi := (239286907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 787189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 787189) = 1/(787189 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-239286907 / 1000000000) (-119643453 / 500000000) (Real.log (787189 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (193207093 / 1000000000) ≤ -Real.log (500000 / 606567) ∧
    -Real.log (500000 / 606567) ≤ (96603547 / 500000000) := by
  have h := checkLog_sound (w := (106567 / 1106567)) (n := 12)
    (lo := (193207093 / 1000000000)) (hi := (96603547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606567 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606567 / 500000) = 1/(500000 / 606567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (193207093 / 1000000000) (96603547 / 500000000) (Real.log (606567 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (606567 / 500000) = -Real.log (500000 / 606567) := by
    rw [show ((606567 / 500000) : ℝ) = ((500000 / 606567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (239697311 / 1000000000) ≤ -Real.log (393433 / 500000) ∧
    -Real.log (393433 / 500000) ≤ (7490541 / 31250000) := by
  have h := checkLog_sound (w := (106567 / 893433)) (n := 12)
    (lo := (239697311 / 1000000000)) (hi := (7490541 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 393433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 393433) = 1/(393433 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-7490541 / 31250000) (-239697311 / 1000000000) (Real.log (393433 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (302685187 / 500000000) ≤ -Real.log (250000000000 / 457982645929) ∧
    -Real.log (250000000000 / 457982645929) ≤ (4842963 / 8000000) := by
  have h := checkLog_sound (w := (207982645929 / 707982645929)) (n := 12)
    (lo := (302685187 / 500000000)) (hi := (4842963 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((457982645929 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(457982645929 / 250000000000) = 1/(250000000000 / 457982645929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (302685187 / 500000000) (4842963 / 8000000) (Real.log (457982645929 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (457982645929 / 250000000000) = -Real.log (250000000000 / 457982645929) := by
    rw [show ((457982645929 / 250000000000) : ℝ) = ((250000000000 / 457982645929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (37893799 / 62500000) ≤ -Real.log (500000000000 / 916817911979) ∧
    -Real.log (500000000000 / 916817911979) ≤ (121260157 / 200000000) := by
  have h := checkLog_sound (w := (416817911979 / 1416817911979)) (n := 12)
    (lo := (37893799 / 62500000)) (hi := (121260157 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((916817911979 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(916817911979 / 500000000000) = 1/(500000000000 / 916817911979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (37893799 / 62500000) (121260157 / 200000000) (Real.log (916817911979 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (916817911979 / 500000000000) = -Real.log (500000000000 / 916817911979) := by
    rw [show ((916817911979 / 500000000000) : ℝ) = ((500000000000 / 916817911979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3376779 / 7812500) ≤ -Real.log (500000000000 / 770342954487) ∧
    -Real.log (500000000000 / 770342954487) ≤ (432227713 / 1000000000) := by
  have h := checkLog_sound (w := (270342954487 / 1270342954487)) (n := 12)
    (lo := (3376779 / 7812500)) (hi := (432227713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((770342954487 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(770342954487 / 500000000000) = 1/(500000000000 / 770342954487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3376779 / 7812500) (432227713 / 1000000000) (Real.log (770342954487 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (770342954487 / 500000000000) = -Real.log (500000000000 / 770342954487) := by
    rw [show ((770342954487 / 500000000000) : ℝ) = ((500000000000 / 770342954487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (86580881 / 200000000) ≤ -Real.log (500000000000 / 770864416559) ∧
    -Real.log (500000000000 / 770864416559) ≤ (216452203 / 500000000) := by
  have h := checkLog_sound (w := (270864416559 / 1270864416559)) (n := 12)
    (lo := (86580881 / 200000000)) (hi := (216452203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((770864416559 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(770864416559 / 500000000000) = 1/(500000000000 / 770864416559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (86580881 / 200000000) (216452203 / 500000000) (Real.log (770864416559 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (770864416559 / 500000000000) = -Real.log (500000000000 / 770864416559) := by
    rw [show ((770864416559 / 500000000000) : ℝ) = ((500000000000 / 770864416559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0452

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0453Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0453
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

theorem reflection_log_1_neg : (187435411 / 1000000000) ≤ -Real.log (10240 / 12351) ∧
    -Real.log (10240 / 12351) ≤ (46858853 / 250000000) := by
  have h := checkLog_sound (w := (2111 / 22591)) (n := 12)
    (lo := (187435411 / 1000000000)) (hi := (46858853 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12351 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12351 / 10240) = 1/(10240 / 12351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (187435411 / 1000000000) (46858853 / 250000000) (Real.log (12351 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12351 / 10240) = -Real.log (10240 / 12351) := by
    rw [show ((12351 / 10240) : ℝ) = ((10240 / 12351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (28857963 / 125000000) ≤ -Real.log (8129 / 10240) ∧
    -Real.log (8129 / 10240) ≤ (46172741 / 200000000) := by
  have h := checkLog_sound (w := (2111 / 18369)) (n := 12)
    (lo := (28857963 / 125000000)) (hi := (46172741 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8129) = 1/(8129 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-46172741 / 200000000) (-28857963 / 125000000) (Real.log (8129 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (187192487 / 1000000000) ≤ -Real.log (2560 / 3087) ∧
    -Real.log (2560 / 3087) ≤ (23399061 / 125000000) := by
  have h := checkLog_sound (w := (527 / 5647)) (n := 12)
    (lo := (187192487 / 1000000000)) (hi := (23399061 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3087 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3087 / 2560) = 1/(2560 / 3087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (187192487 / 1000000000) (23399061 / 125000000) (Real.log (3087 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3087 / 2560) = -Real.log (2560 / 3087) := by
    rw [show ((3087 / 2560) : ℝ) = ((2560 / 3087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (230494723 / 1000000000) ≤ -Real.log (2033 / 2560) ∧
    -Real.log (2033 / 2560) ≤ (57623681 / 250000000) := by
  have h := checkLog_sound (w := (527 / 4593)) (n := 12)
    (lo := (230494723 / 1000000000)) (hi := (57623681 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 2033) = 1/(2033 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-57623681 / 250000000) (-230494723 / 1000000000) (Real.log (2033 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (3452229 / 10000000) ≤ -Real.log (5120 / 7231) ∧
    -Real.log (5120 / 7231) ≤ (345222901 / 1000000000) := by
  have h := checkLog_sound (w := (2111 / 12351)) (n := 12)
    (lo := (3452229 / 10000000)) (hi := (345222901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7231 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7231 / 5120) = 1/(5120 / 7231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (3452229 / 10000000) (345222901 / 1000000000) (Real.log (7231 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7231 / 5120) = -Real.log (5120 / 7231) := by
    rw [show ((7231 / 5120) : ℝ) = ((5120 / 7231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (531546641 / 1000000000) ≤ -Real.log (3009 / 5120) ∧
    -Real.log (3009 / 5120) ≤ (265773321 / 500000000) := by
  have h := checkLog_sound (w := (2111 / 8129)) (n := 12)
    (lo := (531546641 / 1000000000)) (hi := (265773321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3009) = 1/(3009 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-265773321 / 500000000) (-531546641 / 1000000000) (Real.log (3009 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (344807933 / 1000000000) ≤ -Real.log (1280 / 1807) ∧
    -Real.log (1280 / 1807) ≤ (172403967 / 500000000) := by
  have h := checkLog_sound (w := (527 / 3087)) (n := 12)
    (lo := (344807933 / 1000000000)) (hi := (172403967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1807 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1807 / 1280) = 1/(1280 / 1807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (344807933 / 1000000000) (172403967 / 500000000) (Real.log (1807 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1807 / 1280) = -Real.log (1280 / 1807) := by
    rw [show ((1807 / 1280) : ℝ) = ((1280 / 1807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (530550129 / 1000000000) ≤ -Real.log (753 / 1280) ∧
    -Real.log (753 / 1280) ≤ (53055013 / 100000000) := by
  have h := checkLog_sound (w := (527 / 2033)) (n := 12)
    (lo := (530550129 / 1000000000)) (hi := (53055013 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 753) = 1/(753 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-53055013 / 100000000) (-530550129 / 1000000000) (Real.log (753 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (32153889 / 125000000) ≤ -Real.log (31250 / 40417) ∧
    -Real.log (31250 / 40417) ≤ (257231113 / 1000000000) := by
  have h := checkLog_sound (w := (9167 / 71667)) (n := 12)
    (lo := (32153889 / 125000000)) (hi := (257231113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40417 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40417 / 31250) = 1/(31250 / 40417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (32153889 / 125000000) (257231113 / 1000000000) (Real.log (40417 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (40417 / 31250) = -Real.log (31250 / 40417) := by
    rw [show ((40417 / 31250) : ℝ) = ((31250 / 40417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (173605647 / 500000000) ≤ -Real.log (22083 / 31250) ∧
    -Real.log (22083 / 31250) ≤ (69442259 / 200000000) := by
  have h := checkLog_sound (w := (9167 / 53333)) (n := 12)
    (lo := (173605647 / 500000000)) (hi := (69442259 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 22083) = 1/(22083 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-69442259 / 200000000) (-173605647 / 500000000) (Real.log (22083 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (257559663 / 1000000000) ≤ -Real.log (1000000 / 1293769) ∧
    -Real.log (1000000 / 1293769) ≤ (16097479 / 62500000) := by
  have h := checkLog_sound (w := (293769 / 2293769)) (n := 12)
    (lo := (257559663 / 1000000000)) (hi := (16097479 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1293769 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1293769 / 1000000) = 1/(1000000 / 1293769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (257559663 / 1000000000) (16097479 / 62500000) (Real.log (1293769 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1293769 / 1000000) = -Real.log (1000000 / 1293769) := by
    rw [show ((1293769 / 1000000) : ℝ) = ((1000000 / 1293769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (347812899 / 1000000000) ≤ -Real.log (706231 / 1000000) ∧
    -Real.log (706231 / 1000000) ≤ (3478129 / 10000000) := by
  have h := checkLog_sound (w := (293769 / 1706231)) (n := 12)
    (lo := (347812899 / 1000000000)) (hi := (3478129 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 706231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 706231) = 1/(706231 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3478129 / 10000000) (-347812899 / 1000000000) (Real.log (706231 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (96337223 / 500000000) ≤ -Real.log (125000 / 151561) ∧
    -Real.log (125000 / 151561) ≤ (192674447 / 1000000000) := by
  have h := checkLog_sound (w := (26561 / 276561)) (n := 12)
    (lo := (96337223 / 500000000)) (hi := (192674447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151561 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151561 / 125000) = 1/(125000 / 151561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (96337223 / 500000000) (192674447 / 1000000000) (Real.log (151561 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (151561 / 125000) = -Real.log (125000 / 151561) := by
    rw [show ((151561 / 125000) : ℝ) = ((125000 / 151561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (23887667 / 100000000) ≤ -Real.log (98439 / 125000) ∧
    -Real.log (98439 / 125000) ≤ (238876671 / 1000000000) := by
  have h := checkLog_sound (w := (26561 / 223439)) (n := 12)
    (lo := (23887667 / 100000000)) (hi := (238876671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 98439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 98439) = 1/(98439 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-238876671 / 1000000000) (-23887667 / 100000000) (Real.log (98439 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (19294163 / 100000000) ≤ -Real.log (250000 / 303203) ∧
    -Real.log (250000 / 303203) ≤ (192941631 / 1000000000) := by
  have h := checkLog_sound (w := (53203 / 553203)) (n := 12)
    (lo := (19294163 / 100000000)) (hi := (192941631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303203 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303203 / 250000) = 1/(250000 / 303203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (19294163 / 100000000) (192941631 / 1000000000) (Real.log (303203 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (303203 / 250000) = -Real.log (250000 / 303203) := by
    rw [show ((303203 / 250000) : ℝ) = ((250000 / 303203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (239288177 / 1000000000) ≤ -Real.log (196797 / 250000) ∧
    -Real.log (196797 / 250000) ≤ (119644089 / 500000000) := by
  have h := checkLog_sound (w := (53203 / 446797)) (n := 12)
    (lo := (239288177 / 1000000000)) (hi := (119644089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 196797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 196797) = 1/(196797 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-119644089 / 500000000) (-239288177 / 1000000000) (Real.log (196797 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (302221203 / 500000000) ≤ -Real.log (500000000000 / 915115699859) ∧
    -Real.log (500000000000 / 915115699859) ≤ (604442407 / 1000000000) := by
  have h := checkLog_sound (w := (415115699859 / 1415115699859)) (n := 12)
    (lo := (302221203 / 500000000)) (hi := (604442407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((915115699859 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(915115699859 / 500000000000) = 1/(500000000000 / 915115699859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (302221203 / 500000000) (604442407 / 1000000000) (Real.log (915115699859 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (915115699859 / 500000000000) = -Real.log (500000000000 / 915115699859) := by
    rw [show ((915115699859 / 500000000000) : ℝ) = ((500000000000 / 915115699859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (605372563 / 1000000000) ≤ -Real.log (25000000000 / 45798364841) ∧
    -Real.log (25000000000 / 45798364841) ≤ (151343141 / 250000000) := by
  have h := checkLog_sound (w := (20798364841 / 70798364841)) (n := 12)
    (lo := (605372563 / 1000000000)) (hi := (151343141 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45798364841 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45798364841 / 25000000000) = 1/(25000000000 / 45798364841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (605372563 / 1000000000) (151343141 / 250000000) (Real.log (45798364841 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (45798364841 / 25000000000) = -Real.log (25000000000 / 45798364841) := by
    rw [show ((45798364841 / 25000000000) : ℝ) = ((25000000000 / 45798364841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (431551117 / 1000000000) ≤ -Real.log (500000000000 / 769821920173) ∧
    -Real.log (500000000000 / 769821920173) ≤ (215775559 / 500000000) := by
  have h := checkLog_sound (w := (269821920173 / 1269821920173)) (n := 12)
    (lo := (431551117 / 1000000000)) (hi := (215775559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((769821920173 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(769821920173 / 500000000000) = 1/(500000000000 / 769821920173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (431551117 / 1000000000) (215775559 / 500000000) (Real.log (769821920173 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (769821920173 / 500000000000) = -Real.log (500000000000 / 769821920173) := by
    rw [show ((769821920173 / 500000000000) : ℝ) = ((500000000000 / 769821920173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (432229807 / 1000000000) ≤ -Real.log (500000000000 / 770344568261) ∧
    -Real.log (500000000000 / 770344568261) ≤ (27014363 / 62500000) := by
  have h := checkLog_sound (w := (270344568261 / 1270344568261)) (n := 12)
    (lo := (432229807 / 1000000000)) (hi := (27014363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((770344568261 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(770344568261 / 500000000000) = 1/(500000000000 / 770344568261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (432229807 / 1000000000) (27014363 / 62500000) (Real.log (770344568261 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (770344568261 / 500000000000) = -Real.log (500000000000 / 770344568261) := by
    rw [show ((770344568261 / 500000000000) : ℝ) = ((500000000000 / 770344568261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0453

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0454Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0454
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

theorem reflection_log_1_neg : (187192487 / 1000000000) ≤ -Real.log (2560 / 3087) ∧
    -Real.log (2560 / 3087) ≤ (23399061 / 125000000) := by
  have h := checkLog_sound (w := (527 / 5647)) (n := 12)
    (lo := (187192487 / 1000000000)) (hi := (23399061 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3087 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3087 / 2560) = 1/(2560 / 3087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (187192487 / 1000000000) (23399061 / 125000000) (Real.log (3087 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3087 / 2560) = -Real.log (2560 / 3087) := by
    rw [show ((3087 / 2560) : ℝ) = ((2560 / 3087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (230494723 / 1000000000) ≤ -Real.log (2033 / 2560) ∧
    -Real.log (2033 / 2560) ≤ (57623681 / 250000000) := by
  have h := checkLog_sound (w := (527 / 4593)) (n := 12)
    (lo := (230494723 / 1000000000)) (hi := (57623681 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 2033) = 1/(2033 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-57623681 / 250000000) (-230494723 / 1000000000) (Real.log (2033 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (186949503 / 1000000000) ≤ -Real.log (2048 / 2469) ∧
    -Real.log (2048 / 2469) ≤ (1460543 / 7812500) := by
  have h := checkLog_sound (w := (421 / 4517)) (n := 12)
    (lo := (186949503 / 1000000000)) (hi := (1460543 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2469 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2469 / 2048) = 1/(2048 / 2469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (186949503 / 1000000000) (1460543 / 7812500) (Real.log (2469 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2469 / 2048) = -Real.log (2048 / 2469) := by
    rw [show ((2469 / 2048) : ℝ) = ((2048 / 2469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (115062939 / 500000000) ≤ -Real.log (1627 / 2048) ∧
    -Real.log (1627 / 2048) ≤ (230125879 / 1000000000) := by
  have h := checkLog_sound (w := (421 / 3675)) (n := 12)
    (lo := (115062939 / 500000000)) (hi := (230125879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1627) = 1/(1627 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-230125879 / 1000000000) (-115062939 / 500000000) (Real.log (1627 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (344807933 / 1000000000) ≤ -Real.log (1280 / 1807) ∧
    -Real.log (1280 / 1807) ≤ (172403967 / 500000000) := by
  have h := checkLog_sound (w := (527 / 3087)) (n := 12)
    (lo := (344807933 / 1000000000)) (hi := (172403967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1807 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1807 / 1280) = 1/(1280 / 1807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (344807933 / 1000000000) (172403967 / 500000000) (Real.log (1807 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1807 / 1280) = -Real.log (1280 / 1807) := by
    rw [show ((1807 / 1280) : ℝ) = ((1280 / 1807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (530550129 / 1000000000) ≤ -Real.log (753 / 1280) ∧
    -Real.log (753 / 1280) ≤ (53055013 / 100000000) := by
  have h := checkLog_sound (w := (527 / 2033)) (n := 12)
    (lo := (530550129 / 1000000000)) (hi := (53055013 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 753) = 1/(753 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-53055013 / 100000000) (-530550129 / 1000000000) (Real.log (753 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (172196397 / 500000000) ≤ -Real.log (1024 / 1445) ∧
    -Real.log (1024 / 1445) ≤ (68878559 / 200000000) := by
  have h := checkLog_sound (w := (421 / 2469)) (n := 12)
    (lo := (172196397 / 500000000)) (hi := (68878559 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1445 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1445 / 1024) = 1/(1024 / 1445) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (172196397 / 500000000) (68878559 / 200000000) (Real.log (1445 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1445 / 1024) = -Real.log (1024 / 1445) := by
    rw [show ((1445 / 1024) : ℝ) = ((1024 / 1445) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (33097163 / 62500000) ≤ -Real.log (603 / 1024) ∧
    -Real.log (603 / 1024) ≤ (529554609 / 1000000000) := by
  have h := checkLog_sound (w := (421 / 1627)) (n := 12)
    (lo := (33097163 / 62500000)) (hi := (529554609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 603) = 1/(603 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-529554609 / 1000000000) (-33097163 / 62500000) (Real.log (603 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (64225613 / 250000000) ≤ -Real.log (1000000 / 1292919) ∧
    -Real.log (1000000 / 1292919) ≤ (256902453 / 1000000000) := by
  have h := checkLog_sound (w := (292919 / 2292919)) (n := 12)
    (lo := (64225613 / 250000000)) (hi := (256902453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1292919 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1292919 / 1000000) = 1/(1000000 / 1292919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (64225613 / 250000000) (256902453 / 1000000000) (Real.log (1292919 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1292919 / 1000000) = -Real.log (1000000 / 1292919) := by
    rw [show ((1292919 / 1000000) : ℝ) = ((1000000 / 1292919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (346610051 / 1000000000) ≤ -Real.log (707081 / 1000000) ∧
    -Real.log (707081 / 1000000) ≤ (86652513 / 250000000) := by
  have h := checkLog_sound (w := (292919 / 1707081)) (n := 12)
    (lo := (346610051 / 1000000000)) (hi := (86652513 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 707081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 707081) = 1/(707081 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-86652513 / 250000000) (-346610051 / 1000000000) (Real.log (707081 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (51446377 / 200000000) ≤ -Real.log (200000 / 258669) ∧
    -Real.log (200000 / 258669) ≤ (128615943 / 500000000) := by
  have h := checkLog_sound (w := (58669 / 458669)) (n := 12)
    (lo := (51446377 / 200000000)) (hi := (128615943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((258669 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(258669 / 200000) = 1/(200000 / 258669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (51446377 / 200000000) (128615943 / 500000000) (Real.log (258669 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (258669 / 200000) = -Real.log (200000 / 258669) := by
    rw [show ((258669 / 200000) : ℝ) = ((200000 / 258669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (347212709 / 1000000000) ≤ -Real.log (141331 / 200000) ∧
    -Real.log (141331 / 200000) ≤ (34721271 / 100000000) := by
  have h := checkLog_sound (w := (58669 / 341331)) (n := 12)
    (lo := (347212709 / 1000000000)) (hi := (34721271 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 141331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 141331) = 1/(141331 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-34721271 / 100000000) (-347212709 / 1000000000) (Real.log (141331 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (192408841 / 1000000000) ≤ -Real.log (500000 / 606083) ∧
    -Real.log (500000 / 606083) ≤ (96204421 / 500000000) := by
  have h := checkLog_sound (w := (106083 / 1106083)) (n := 12)
    (lo := (192408841 / 1000000000)) (hi := (96204421 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606083 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606083 / 500000) = 1/(500000 / 606083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (192408841 / 1000000000) (96204421 / 500000000) (Real.log (606083 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (606083 / 500000) = -Real.log (500000 / 606083) := by
    rw [show ((606083 / 500000) : ℝ) = ((500000 / 606083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (238467871 / 1000000000) ≤ -Real.log (393917 / 500000) ∧
    -Real.log (393917 / 500000) ≤ (7452121 / 31250000) := by
  have h := checkLog_sound (w := (106083 / 893917)) (n := 12)
    (lo := (238467871 / 1000000000)) (hi := (7452121 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 393917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 393917) = 1/(393917 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-7452121 / 31250000) (-238467871 / 1000000000) (Real.log (393917 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (192675271 / 1000000000) ≤ -Real.log (1000000 / 1212489) ∧
    -Real.log (1000000 / 1212489) ≤ (24084409 / 125000000) := by
  have h := checkLog_sound (w := (212489 / 2212489)) (n := 12)
    (lo := (192675271 / 1000000000)) (hi := (24084409 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1212489 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1212489 / 1000000) = 1/(1000000 / 1212489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (192675271 / 1000000000) (24084409 / 125000000) (Real.log (1212489 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1212489 / 1000000) = -Real.log (1000000 / 1212489) := by
    rw [show ((1212489 / 1000000) : ℝ) = ((1000000 / 1212489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (11943897 / 50000000) ≤ -Real.log (787511 / 1000000) ∧
    -Real.log (787511 / 1000000) ≤ (238877941 / 1000000000) := by
  have h := checkLog_sound (w := (212489 / 1787511)) (n := 12)
    (lo := (11943897 / 50000000)) (hi := (238877941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 787511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 787511) = 1/(787511 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-238877941 / 1000000000) (-11943897 / 50000000) (Real.log (787511 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (603512503 / 1000000000) ≤ -Real.log (250000000000 / 457132563313) ∧
    -Real.log (250000000000 / 457132563313) ≤ (75439063 / 125000000) := by
  have h := checkLog_sound (w := (207132563313 / 707132563313)) (n := 12)
    (lo := (603512503 / 1000000000)) (hi := (75439063 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((457132563313 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(457132563313 / 250000000000) = 1/(250000000000 / 457132563313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (603512503 / 1000000000) (75439063 / 125000000) (Real.log (457132563313 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (457132563313 / 250000000000) = -Real.log (250000000000 / 457132563313) := by
    rw [show ((457132563313 / 250000000000) : ℝ) = ((250000000000 / 457132563313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (120888919 / 200000000) ≤ -Real.log (100000000000 / 183023540483) ∧
    -Real.log (100000000000 / 183023540483) ≤ (151111149 / 250000000) := by
  have h := checkLog_sound (w := (83023540483 / 283023540483)) (n := 12)
    (lo := (120888919 / 200000000)) (hi := (151111149 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183023540483 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183023540483 / 100000000000) = 1/(100000000000 / 183023540483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (120888919 / 200000000) (151111149 / 250000000) (Real.log (183023540483 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (183023540483 / 100000000000) = -Real.log (100000000000 / 183023540483) := by
    rw [show ((183023540483 / 100000000000) : ℝ) = ((100000000000 / 183023540483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (430876713 / 1000000000) ≤ -Real.log (25000000000 / 38465146211) ∧
    -Real.log (25000000000 / 38465146211) ≤ (215438357 / 500000000) := by
  have h := checkLog_sound (w := (13465146211 / 63465146211)) (n := 12)
    (lo := (430876713 / 1000000000)) (hi := (215438357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38465146211 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38465146211 / 25000000000) = 1/(25000000000 / 38465146211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (430876713 / 1000000000) (215438357 / 500000000) (Real.log (38465146211 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (38465146211 / 25000000000) = -Real.log (25000000000 / 38465146211) := by
    rw [show ((38465146211 / 25000000000) : ℝ) = ((25000000000 / 38465146211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (431553211 / 1000000000) ≤ -Real.log (31250000000 / 48113970789) ∧
    -Real.log (31250000000 / 48113970789) ≤ (107888303 / 250000000) := by
  have h := checkLog_sound (w := (16863970789 / 79363970789)) (n := 12)
    (lo := (431553211 / 1000000000)) (hi := (107888303 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48113970789 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48113970789 / 31250000000) = 1/(31250000000 / 48113970789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (431553211 / 1000000000) (107888303 / 250000000) (Real.log (48113970789 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (48113970789 / 31250000000) = -Real.log (31250000000 / 48113970789) := by
    rw [show ((48113970789 / 31250000000) : ℝ) = ((31250000000 / 48113970789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0454

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0455Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0455
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

theorem reflection_log_1_neg : (186949503 / 1000000000) ≤ -Real.log (2048 / 2469) ∧
    -Real.log (2048 / 2469) ≤ (1460543 / 7812500) := by
  have h := checkLog_sound (w := (421 / 4517)) (n := 12)
    (lo := (186949503 / 1000000000)) (hi := (1460543 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2469 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2469 / 2048) = 1/(2048 / 2469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (186949503 / 1000000000) (1460543 / 7812500) (Real.log (2469 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2469 / 2048) = -Real.log (2048 / 2469) := by
    rw [show ((2469 / 2048) : ℝ) = ((2048 / 2469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (115062939 / 500000000) ≤ -Real.log (1627 / 2048) ∧
    -Real.log (1627 / 2048) ≤ (230125879 / 1000000000) := by
  have h := checkLog_sound (w := (421 / 3675)) (n := 12)
    (lo := (115062939 / 500000000)) (hi := (230125879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1627) = 1/(1627 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-230125879 / 1000000000) (-115062939 / 500000000) (Real.log (1627 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (9335323 / 50000000) ≤ -Real.log (5120 / 6171) ∧
    -Real.log (5120 / 6171) ≤ (186706461 / 1000000000) := by
  have h := checkLog_sound (w := (1051 / 11291)) (n := 12)
    (lo := (9335323 / 50000000)) (hi := (186706461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6171 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6171 / 5120) = 1/(5120 / 6171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (9335323 / 50000000) (186706461 / 1000000000) (Real.log (6171 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6171 / 5120) = -Real.log (5120 / 6171) := by
    rw [show ((6171 / 5120) : ℝ) = ((5120 / 6171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (22975717 / 100000000) ≤ -Real.log (4069 / 5120) ∧
    -Real.log (4069 / 5120) ≤ (229757171 / 1000000000) := by
  have h := checkLog_sound (w := (1051 / 9189)) (n := 12)
    (lo := (22975717 / 100000000)) (hi := (229757171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4069) = 1/(4069 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-229757171 / 1000000000) (-22975717 / 100000000) (Real.log (4069 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (172196397 / 500000000) ≤ -Real.log (1024 / 1445) ∧
    -Real.log (1024 / 1445) ≤ (68878559 / 200000000) := by
  have h := checkLog_sound (w := (421 / 2469)) (n := 12)
    (lo := (172196397 / 500000000)) (hi := (68878559 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1445 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1445 / 1024) = 1/(1024 / 1445) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (172196397 / 500000000) (68878559 / 200000000) (Real.log (1445 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1445 / 1024) = -Real.log (1024 / 1445) := by
    rw [show ((1445 / 1024) : ℝ) = ((1024 / 1445) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (33097163 / 62500000) ≤ -Real.log (603 / 1024) ∧
    -Real.log (603 / 1024) ≤ (529554609 / 1000000000) := by
  have h := checkLog_sound (w := (421 / 1627)) (n := 12)
    (lo := (33097163 / 62500000)) (hi := (529554609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 603) = 1/(603 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-529554609 / 1000000000) (-33097163 / 62500000) (Real.log (603 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (343977483 / 1000000000) ≤ -Real.log (2560 / 3611) ∧
    -Real.log (2560 / 3611) ≤ (85994371 / 250000000) := by
  have h := checkLog_sound (w := (1051 / 6171)) (n := 12)
    (lo := (343977483 / 1000000000)) (hi := (85994371 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3611 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3611 / 2560) = 1/(2560 / 3611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (343977483 / 1000000000) (85994371 / 250000000) (Real.log (3611 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3611 / 2560) = -Real.log (2560 / 3611) := by
    rw [show ((3611 / 2560) : ℝ) = ((2560 / 3611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (264280039 / 500000000) ≤ -Real.log (1509 / 2560) ∧
    -Real.log (1509 / 2560) ≤ (528560079 / 1000000000) := by
  have h := checkLog_sound (w := (1051 / 4069)) (n := 12)
    (lo := (264280039 / 500000000)) (hi := (528560079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1509) = 1/(1509 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-528560079 / 1000000000) (-264280039 / 500000000) (Real.log (1509 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (128287229 / 500000000) ≤ -Real.log (200000 / 258499) ∧
    -Real.log (200000 / 258499) ≤ (256574459 / 1000000000) := by
  have h := checkLog_sound (w := (58499 / 458499)) (n := 12)
    (lo := (128287229 / 500000000)) (hi := (256574459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((258499 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(258499 / 200000) = 1/(200000 / 258499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (128287229 / 500000000) (256574459 / 1000000000) (Real.log (258499 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (258499 / 200000) = -Real.log (200000 / 258499) := by
    rw [show ((258499 / 200000) : ℝ) = ((200000 / 258499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (173005291 / 500000000) ≤ -Real.log (141501 / 200000) ∧
    -Real.log (141501 / 200000) ≤ (346010583 / 1000000000) := by
  have h := checkLog_sound (w := (58499 / 341501)) (n := 12)
    (lo := (173005291 / 500000000)) (hi := (346010583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 141501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 141501) = 1/(141501 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-346010583 / 1000000000) (-173005291 / 500000000) (Real.log (141501 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (256903999 / 1000000000) ≤ -Real.log (1000000 / 1292921) ∧
    -Real.log (1000000 / 1292921) ≤ (32113 / 125000) := by
  have h := checkLog_sound (w := (292921 / 2292921)) (n := 12)
    (lo := (256903999 / 1000000000)) (hi := (32113 / 125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1292921 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1292921 / 1000000) = 1/(1000000 / 1292921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (256903999 / 1000000000) (32113 / 125000) (Real.log (1292921 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1292921 / 1000000) = -Real.log (1000000 / 1292921) := by
    rw [show ((1292921 / 1000000) : ℝ) = ((1000000 / 1292921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (346612879 / 1000000000) ≤ -Real.log (707079 / 1000000) ∧
    -Real.log (707079 / 1000000) ≤ (4332661 / 12500000) := by
  have h := checkLog_sound (w := (292921 / 1707079)) (n := 12)
    (lo := (346612879 / 1000000000)) (hi := (4332661 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 707079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 707079) = 1/(707079 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-4332661 / 12500000) (-346612879 / 1000000000) (Real.log (707079 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (96071583 / 500000000) ≤ -Real.log (250000 / 302961) ∧
    -Real.log (250000 / 302961) ≤ (192143167 / 1000000000) := by
  have h := checkLog_sound (w := (52961 / 552961)) (n := 12)
    (lo := (96071583 / 500000000)) (hi := (192143167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302961 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302961 / 250000) = 1/(250000 / 302961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (96071583 / 500000000) (192143167 / 1000000000) (Real.log (302961 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (302961 / 250000) = -Real.log (250000 / 302961) := by
    rw [show ((302961 / 250000) : ℝ) = ((250000 / 302961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (238059239 / 1000000000) ≤ -Real.log (197039 / 250000) ∧
    -Real.log (197039 / 250000) ≤ (5951481 / 25000000) := by
  have h := checkLog_sound (w := (52961 / 447039)) (n := 12)
    (lo := (238059239 / 1000000000)) (hi := (5951481 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 197039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 197039) = 1/(197039 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-5951481 / 25000000) (-238059239 / 1000000000) (Real.log (197039 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (96204833 / 500000000) ≤ -Real.log (1000000 / 1212167) ∧
    -Real.log (1000000 / 1212167) ≤ (192409667 / 1000000000) := by
  have h := checkLog_sound (w := (212167 / 2212167)) (n := 12)
    (lo := (96204833 / 500000000)) (hi := (192409667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1212167 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1212167 / 1000000) = 1/(1000000 / 1212167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (96204833 / 500000000) (192409667 / 1000000000) (Real.log (1212167 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1212167 / 1000000) = -Real.log (1000000 / 1212167) := by
    rw [show ((1212167 / 1000000) : ℝ) = ((1000000 / 1212167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (11923457 / 50000000) ≤ -Real.log (787833 / 1000000) ∧
    -Real.log (787833 / 1000000) ≤ (238469141 / 1000000000) := by
  have h := checkLog_sound (w := (212167 / 1787833)) (n := 12)
    (lo := (11923457 / 50000000)) (hi := (238469141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 787833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 787833) = 1/(787833 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-238469141 / 1000000000) (-11923457 / 50000000) (Real.log (787833 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (602585041 / 1000000000) ≤ -Real.log (25000000000 / 45670878651) ∧
    -Real.log (25000000000 / 45670878651) ≤ (301292521 / 500000000) := by
  have h := checkLog_sound (w := (20670878651 / 70670878651)) (n := 12)
    (lo := (602585041 / 1000000000)) (hi := (301292521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45670878651 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45670878651 / 25000000000) = 1/(25000000000 / 45670878651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (602585041 / 1000000000) (301292521 / 500000000) (Real.log (45670878651 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (45670878651 / 25000000000) = -Real.log (25000000000 / 45670878651) := by
    rw [show ((45670878651 / 25000000000) : ℝ) = ((25000000000 / 45670878651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (603516879 / 1000000000) ≤ -Real.log (50000000000 / 91426912693) ∧
    -Real.log (50000000000 / 91426912693) ≤ (7543961 / 12500000) := by
  have h := checkLog_sound (w := (41426912693 / 141426912693)) (n := 12)
    (lo := (603516879 / 1000000000)) (hi := (7543961 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91426912693 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91426912693 / 50000000000) = 1/(50000000000 / 91426912693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (603516879 / 1000000000) (7543961 / 12500000) (Real.log (91426912693 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (91426912693 / 50000000000) = -Real.log (50000000000 / 91426912693) := by
    rw [show ((91426912693 / 50000000000) : ℝ) = ((50000000000 / 91426912693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (86040481 / 200000000) ≤ -Real.log (31250000000 / 48049022021) ∧
    -Real.log (31250000000 / 48049022021) ≤ (215101203 / 500000000) := by
  have h := checkLog_sound (w := (16799022021 / 79299022021)) (n := 12)
    (lo := (86040481 / 200000000)) (hi := (215101203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48049022021 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48049022021 / 31250000000) = 1/(31250000000 / 48049022021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (86040481 / 200000000) (215101203 / 500000000) (Real.log (48049022021 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (48049022021 / 31250000000) = -Real.log (31250000000 / 48049022021) := by
    rw [show ((48049022021 / 31250000000) : ℝ) = ((31250000000 / 48049022021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (430878807 / 1000000000) ≤ -Real.log (500000000000 / 769304535353) ∧
    -Real.log (500000000000 / 769304535353) ≤ (53859851 / 125000000) := by
  have h := checkLog_sound (w := (269304535353 / 1269304535353)) (n := 12)
    (lo := (430878807 / 1000000000)) (hi := (53859851 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((769304535353 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(769304535353 / 500000000000) = 1/(500000000000 / 769304535353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (430878807 / 1000000000) (53859851 / 125000000) (Real.log (769304535353 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (769304535353 / 500000000000) = -Real.log (500000000000 / 769304535353) := by
    rw [show ((769304535353 / 500000000000) : ℝ) = ((500000000000 / 769304535353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0455

end


