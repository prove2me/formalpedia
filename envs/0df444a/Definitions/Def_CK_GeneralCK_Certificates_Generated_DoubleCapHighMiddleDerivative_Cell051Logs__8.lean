-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell051Logs__8
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell051Logs__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T16:37:07.191972+00:00
-- url     : https://prove2.me/theorems/91b8bd29-4afa-40de-a276-36980edcce95
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell051Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell052…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell051Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell052Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell053Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell054Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell055Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell056Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell057Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell058Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell051Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell052Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell053Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell054Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell055Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell056Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell057Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell058Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell051Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell052Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell053Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell054Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell055Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell056Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell057Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell058Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell051Logs (+7 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell052Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell053Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell054Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell055Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell056Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell057Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell058Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell051Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell051
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (247226221 / 1000000000) ≤ -Real.log (1280 / 1639) ∧
    -Real.log (1280 / 1639) ≤ (123613111 / 500000000) := by
  have h := checkLog_sound (w := (359 / 2919)) (n := 12)
    (lo := (247226221 / 1000000000)) (hi := (123613111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1639 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1639 / 1280) = 1/(1280 / 1639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (247226221 / 1000000000) (123613111 / 500000000) (Real.log (1639 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1639 / 1280) = -Real.log (1280 / 1639) := by
    rw [show ((1639 / 1280) : ℝ) = ((1280 / 1639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (8228883 / 25000000) ≤ -Real.log (921 / 1280) ∧
    -Real.log (921 / 1280) ≤ (329155321 / 1000000000) := by
  have h := checkLog_sound (w := (359 / 2201)) (n := 12)
    (lo := (8228883 / 25000000)) (hi := (329155321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 921) = 1/(921 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-329155321 / 1000000000) (-8228883 / 25000000) (Real.log (921 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (246768521 / 1000000000) ≤ -Real.log (5120 / 6553) ∧
    -Real.log (5120 / 6553) ≤ (123384261 / 500000000) := by
  have h := checkLog_sound (w := (1433 / 11673)) (n := 12)
    (lo := (246768521 / 1000000000)) (hi := (123384261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6553 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6553 / 5120) = 1/(5120 / 6553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (246768521 / 1000000000) (123384261 / 500000000) (Real.log (6553 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6553 / 5120) = -Real.log (5120 / 6553) := by
    rw [show ((6553 / 5120) : ℝ) = ((5120 / 6553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (328341319 / 1000000000) ≤ -Real.log (3687 / 5120) ∧
    -Real.log (3687 / 5120) ≤ (8208533 / 25000000) := by
  have h := checkLog_sound (w := (1433 / 8807)) (n := 12)
    (lo := (328341319 / 1000000000)) (hi := (8208533 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3687) = 1/(3687 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-8208533 / 25000000) (-328341319 / 1000000000) (Real.log (3687 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (45283129 / 250000000) ≤ -Real.log (500000 / 599287) ∧
    -Real.log (500000 / 599287) ≤ (181132517 / 1000000000) := by
  have h := checkLog_sound (w := (99287 / 1099287)) (n := 12)
    (lo := (45283129 / 250000000)) (hi := (181132517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599287 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599287 / 500000) = 1/(500000 / 599287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (45283129 / 250000000) (181132517 / 1000000000) (Real.log (599287 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (599287 / 500000) = -Real.log (500000 / 599287) := by
    rw [show ((599287 / 500000) : ℝ) = ((500000 / 599287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (110681319 / 500000000) ≤ -Real.log (400713 / 500000) ∧
    -Real.log (400713 / 500000) ≤ (221362639 / 1000000000) := by
  have h := checkLog_sound (w := (99287 / 900713)) (n := 12)
    (lo := (110681319 / 500000000)) (hi := (221362639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 400713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 400713) = 1/(400713 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-221362639 / 1000000000) (-110681319 / 500000000) (Real.log (400713 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (181482871 / 1000000000) ≤ -Real.log (500000 / 599497) ∧
    -Real.log (500000 / 599497) ≤ (22685359 / 125000000) := by
  have h := checkLog_sound (w := (99497 / 1099497)) (n := 12)
    (lo := (181482871 / 1000000000)) (hi := (22685359 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599497 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599497 / 500000) = 1/(500000 / 599497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (181482871 / 1000000000) (22685359 / 125000000) (Real.log (599497 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (599497 / 500000) = -Real.log (500000 / 599497) := by
    rw [show ((599497 / 500000) : ℝ) = ((500000 / 599497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (221886841 / 1000000000) ≤ -Real.log (400503 / 500000) ∧
    -Real.log (400503 / 500000) ≤ (110943421 / 500000000) := by
  have h := checkLog_sound (w := (99497 / 900503)) (n := 12)
    (lo := (221886841 / 1000000000)) (hi := (110943421 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 400503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 400503) = 1/(400503 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-110943421 / 500000000) (-221886841 / 1000000000) (Real.log (400503 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (66375231 / 500000000) ≤ -Real.log (200000 / 228393) ∧
    -Real.log (200000 / 228393) ≤ (132750463 / 1000000000) := by
  have h := checkLog_sound (w := (28393 / 428393)) (n := 12)
    (lo := (66375231 / 500000000)) (hi := (132750463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((228393 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(228393 / 200000) = 1/(200000 / 228393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (66375231 / 500000000) (132750463 / 1000000000) (Real.log (228393 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (228393 / 200000) = -Real.log (200000 / 228393) := by
    rw [show ((228393 / 200000) : ℝ) = ((200000 / 228393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (153110387 / 1000000000) ≤ -Real.log (171607 / 200000) ∧
    -Real.log (171607 / 200000) ≤ (38277597 / 250000000) := by
  have h := checkLog_sound (w := (28393 / 371607)) (n := 12)
    (lo := (153110387 / 1000000000)) (hi := (38277597 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 171607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 171607) = 1/(171607 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-38277597 / 250000000) (-153110387 / 1000000000) (Real.log (171607 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (66509193 / 500000000) ≤ -Real.log (1000000 / 1142271) ∧
    -Real.log (1000000 / 1142271) ≤ (133018387 / 1000000000) := by
  have h := checkLog_sound (w := (142271 / 2142271)) (n := 12)
    (lo := (66509193 / 500000000)) (hi := (133018387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1142271 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1142271 / 1000000) = 1/(1000000 / 1142271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (66509193 / 500000000) (133018387 / 1000000000) (Real.log (1142271 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1142271 / 1000000) = -Real.log (1000000 / 1142271) := by
    rw [show ((1142271 / 1000000) : ℝ) = ((1000000 / 1142271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3836677 / 25000000) ≤ -Real.log (857729 / 1000000) ∧
    -Real.log (857729 / 1000000) ≤ (153467081 / 1000000000) := by
  have h := checkLog_sound (w := (142271 / 1857729)) (n := 12)
    (lo := (3836677 / 25000000)) (hi := (153467081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 857729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 857729) = 1/(857729 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-153467081 / 1000000000) (-3836677 / 25000000) (Real.log (857729 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (7188873 / 12500000) ≤ -Real.log (500000000000 / 888662869541) ∧
    -Real.log (500000000000 / 888662869541) ≤ (575109841 / 1000000000) := by
  have h := checkLog_sound (w := (388662869541 / 1388662869541)) (n := 12)
    (lo := (7188873 / 12500000)) (hi := (575109841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((888662869541 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(888662869541 / 500000000000) = 1/(500000000000 / 888662869541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (7188873 / 12500000) (575109841 / 1000000000) (Real.log (888662869541 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (888662869541 / 500000000000) = -Real.log (500000000000 / 888662869541) := by
    rw [show ((888662869541 / 500000000000) : ℝ) = ((500000000000 / 888662869541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (288190771 / 500000000) ≤ -Real.log (250000000000 / 444896851249) ∧
    -Real.log (250000000000 / 444896851249) ≤ (576381543 / 1000000000) := by
  have h := checkLog_sound (w := (194896851249 / 694896851249)) (n := 12)
    (lo := (288190771 / 500000000)) (hi := (576381543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((444896851249 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(444896851249 / 250000000000) = 1/(250000000000 / 444896851249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (288190771 / 500000000) (576381543 / 1000000000) (Real.log (444896851249 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (444896851249 / 250000000000) = -Real.log (250000000000 / 444896851249) := by
    rw [show ((444896851249 / 250000000000) : ℝ) = ((250000000000 / 444896851249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (201247577 / 500000000) ≤ -Real.log (100000000000 / 149555167913) ∧
    -Real.log (100000000000 / 149555167913) ≤ (80499031 / 200000000) := by
  have h := checkLog_sound (w := (49555167913 / 249555167913)) (n := 12)
    (lo := (201247577 / 500000000)) (hi := (80499031 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149555167913 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149555167913 / 100000000000) = 1/(100000000000 / 149555167913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (201247577 / 500000000) (80499031 / 200000000) (Real.log (149555167913 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (149555167913 / 100000000000) = -Real.log (100000000000 / 149555167913) := by
    rw [show ((149555167913 / 100000000000) : ℝ) = ((100000000000 / 149555167913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (403369713 / 1000000000) ≤ -Real.log (500000000000 / 748430099151) ∧
    -Real.log (500000000000 / 748430099151) ≤ (201684857 / 500000000) := by
  have h := checkLog_sound (w := (248430099151 / 1248430099151)) (n := 12)
    (lo := (403369713 / 1000000000)) (hi := (201684857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((748430099151 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(748430099151 / 500000000000) = 1/(500000000000 / 748430099151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (403369713 / 1000000000) (201684857 / 500000000) (Real.log (748430099151 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (748430099151 / 500000000000) = -Real.log (500000000000 / 748430099151) := by
    rw [show ((748430099151 / 500000000000) : ℝ) = ((500000000000 / 748430099151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (5717217 / 20000000) ≤ -Real.log (250000000000 / 332726811843) ∧
    -Real.log (250000000000 / 332726811843) ≤ (285860851 / 1000000000) := by
  have h := checkLog_sound (w := (82726811843 / 582726811843)) (n := 12)
    (lo := (5717217 / 20000000)) (hi := (285860851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((332726811843 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(332726811843 / 250000000000) = 1/(250000000000 / 332726811843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (5717217 / 20000000) (285860851 / 1000000000) (Real.log (332726811843 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (332726811843 / 250000000000) = -Real.log (250000000000 / 332726811843) := by
    rw [show ((332726811843 / 250000000000) : ℝ) = ((250000000000 / 332726811843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (143242733 / 500000000) ≤ -Real.log (100000000000 / 133173881261) ∧
    -Real.log (100000000000 / 133173881261) ≤ (286485467 / 1000000000) := by
  have h := checkLog_sound (w := (33173881261 / 233173881261)) (n := 12)
    (lo := (143242733 / 500000000)) (hi := (286485467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133173881261 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133173881261 / 100000000000) = 1/(100000000000 / 133173881261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (143242733 / 500000000) (286485467 / 1000000000) (Real.log (133173881261 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (133173881261 / 100000000000) = -Real.log (100000000000 / 133173881261) := by
    rw [show ((133173881261 / 100000000000) : ℝ) = ((100000000000 / 133173881261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (10224347 / 500000000) ≤ -Real.log (979758962559 / 1000000000000) ∧
    -Real.log (979758962559 / 1000000000000) ≤ (4089739 / 200000000) := by
  have h := checkLog_sound (w := (20241037441 / 1979758962559)) (n := 12)
    (lo := (10224347 / 500000000)) (hi := (4089739 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979758962559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979758962559) = 1/(979758962559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4089739 / 200000000) (-10224347 / 500000000) (Real.log (979758962559 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (814397 / 40000000) ≤ -Real.log (39193837551 / 40000000000) ∧
    -Real.log (39193837551 / 40000000000) ≤ (10179963 / 500000000) := by
  have h := checkLog_sound (w := (806162449 / 79193837551)) (n := 12)
    (lo := (814397 / 40000000)) (hi := (10179963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39193837551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39193837551) = 1/(39193837551 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-10179963 / 500000000) (-814397 / 40000000) (Real.log (39193837551 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell051

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell052Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell052
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (247683713 / 1000000000) ≤ -Real.log (5120 / 6559) ∧
    -Real.log (5120 / 6559) ≤ (123841857 / 500000000) := by
  have h := checkLog_sound (w := (1439 / 11679)) (n := 12)
    (lo := (247683713 / 1000000000)) (hi := (123841857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6559 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6559 / 5120) = 1/(5120 / 6559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (247683713 / 1000000000) (123841857 / 500000000) (Real.log (6559 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6559 / 5120) = -Real.log (5120 / 6559) := by
    rw [show ((6559 / 5120) : ℝ) = ((5120 / 6559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (5155781 / 15625000) ≤ -Real.log (3681 / 5120) ∧
    -Real.log (3681 / 5120) ≤ (65993997 / 200000000) := by
  have h := checkLog_sound (w := (1439 / 8801)) (n := 12)
    (lo := (5155781 / 15625000)) (hi := (65993997 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3681) = 1/(3681 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-65993997 / 200000000) (-5155781 / 15625000) (Real.log (3681 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (247226221 / 1000000000) ≤ -Real.log (1280 / 1639) ∧
    -Real.log (1280 / 1639) ≤ (123613111 / 500000000) := by
  have h := checkLog_sound (w := (359 / 2919)) (n := 12)
    (lo := (247226221 / 1000000000)) (hi := (123613111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1639 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1639 / 1280) = 1/(1280 / 1639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (247226221 / 1000000000) (123613111 / 500000000) (Real.log (1639 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1639 / 1280) = -Real.log (1280 / 1639) := by
    rw [show ((1639 / 1280) : ℝ) = ((1280 / 1639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (8228883 / 25000000) ≤ -Real.log (921 / 1280) ∧
    -Real.log (921 / 1280) ≤ (329155321 / 1000000000) := by
  have h := checkLog_sound (w := (359 / 2201)) (n := 12)
    (lo := (8228883 / 25000000)) (hi := (329155321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 921) = 1/(921 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-329155321 / 1000000000) (-8228883 / 25000000) (Real.log (921 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (181482037 / 1000000000) ≤ -Real.log (1000000 / 1198993) ∧
    -Real.log (1000000 / 1198993) ≤ (90741019 / 500000000) := by
  have h := checkLog_sound (w := (198993 / 2198993)) (n := 12)
    (lo := (181482037 / 1000000000)) (hi := (90741019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1198993 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1198993 / 1000000) = 1/(1000000 / 1198993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (181482037 / 1000000000) (90741019 / 500000000) (Real.log (1198993 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1198993 / 1000000) = -Real.log (1000000 / 1198993) := by
    rw [show ((1198993 / 1000000) : ℝ) = ((1000000 / 1198993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (27735699 / 125000000) ≤ -Real.log (801007 / 1000000) ∧
    -Real.log (801007 / 1000000) ≤ (221885593 / 1000000000) := by
  have h := checkLog_sound (w := (198993 / 1801007)) (n := 12)
    (lo := (27735699 / 125000000)) (hi := (221885593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 801007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 801007) = 1/(801007 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-221885593 / 1000000000) (-27735699 / 125000000) (Real.log (801007 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (18183227 / 100000000) ≤ -Real.log (1000000 / 1199413) ∧
    -Real.log (1000000 / 1199413) ≤ (181832271 / 1000000000) := by
  have h := checkLog_sound (w := (199413 / 2199413)) (n := 12)
    (lo := (18183227 / 100000000)) (hi := (181832271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1199413 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1199413 / 1000000) = 1/(1000000 / 1199413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (18183227 / 100000000) (181832271 / 1000000000) (Real.log (1199413 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1199413 / 1000000) = -Real.log (1000000 / 1199413) := by
    rw [show ((1199413 / 1000000) : ℝ) = ((1000000 / 1199413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (22241007 / 100000000) ≤ -Real.log (800587 / 1000000) ∧
    -Real.log (800587 / 1000000) ≤ (222410071 / 1000000000) := by
  have h := checkLog_sound (w := (199413 / 1800587)) (n := 12)
    (lo := (22241007 / 100000000)) (hi := (222410071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 800587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 800587) = 1/(800587 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-222410071 / 1000000000) (-22241007 / 100000000) (Real.log (800587 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (13301751 / 100000000) ≤ -Real.log (100000 / 114227) ∧
    -Real.log (100000 / 114227) ≤ (133017511 / 1000000000) := by
  have h := checkLog_sound (w := (14227 / 214227)) (n := 12)
    (lo := (13301751 / 100000000)) (hi := (133017511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114227 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(114227 / 100000) = 1/(100000 / 114227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (13301751 / 100000000) (133017511 / 1000000000) (Real.log (114227 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (114227 / 100000) = -Real.log (100000 / 114227) := by
    rw [show ((114227 / 100000) : ℝ) = ((100000 / 114227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (76732957 / 500000000) ≤ -Real.log (85773 / 100000) ∧
    -Real.log (85773 / 100000) ≤ (30693183 / 200000000) := by
  have h := checkLog_sound (w := (14227 / 185773)) (n := 12)
    (lo := (76732957 / 500000000)) (hi := (30693183 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 85773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 85773) = 1/(85773 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-30693183 / 200000000) (-76732957 / 500000000) (Real.log (85773 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (133286237 / 1000000000) ≤ -Real.log (1000000 / 1142577) ∧
    -Real.log (1000000 / 1142577) ≤ (66643119 / 500000000) := by
  have h := checkLog_sound (w := (142577 / 2142577)) (n := 12)
    (lo := (133286237 / 1000000000)) (hi := (66643119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1142577 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1142577 / 1000000) = 1/(1000000 / 1142577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (133286237 / 1000000000) (66643119 / 500000000) (Real.log (1142577 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1142577 / 1000000) = -Real.log (1000000 / 1142577) := by
    rw [show ((1142577 / 1000000) : ℝ) = ((1000000 / 1142577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (153823899 / 1000000000) ≤ -Real.log (857423 / 1000000) ∧
    -Real.log (857423 / 1000000) ≤ (1538239 / 10000000) := by
  have h := checkLog_sound (w := (142577 / 1857423)) (n := 12)
    (lo := (153823899 / 1000000000)) (hi := (1538239 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 857423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 857423) = 1/(857423 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1538239 / 10000000) (-153823899 / 1000000000) (Real.log (857423 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (288190771 / 500000000) ≤ -Real.log (500000000000 / 889793702497) ∧
    -Real.log (500000000000 / 889793702497) ≤ (576381543 / 1000000000) := by
  have h := checkLog_sound (w := (389793702497 / 1389793702497)) (n := 12)
    (lo := (288190771 / 500000000)) (hi := (576381543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((889793702497 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(889793702497 / 500000000000) = 1/(500000000000 / 889793702497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (288190771 / 500000000) (576381543 / 1000000000) (Real.log (889793702497 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (889793702497 / 500000000000) = -Real.log (500000000000 / 889793702497) := by
    rw [show ((889793702497 / 500000000000) : ℝ) = ((500000000000 / 889793702497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (577653697 / 1000000000) ≤ -Real.log (250000000000 / 445463189351) ∧
    -Real.log (250000000000 / 445463189351) ≤ (288826849 / 500000000) := by
  have h := checkLog_sound (w := (195463189351 / 695463189351)) (n := 12)
    (lo := (577653697 / 1000000000)) (hi := (288826849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((445463189351 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(445463189351 / 250000000000) = 1/(250000000000 / 445463189351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (577653697 / 1000000000) (288826849 / 500000000) (Real.log (445463189351 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (445463189351 / 250000000000) = -Real.log (250000000000 / 445463189351) := by
    rw [show ((445463189351 / 250000000000) : ℝ) = ((250000000000 / 445463189351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (40336763 / 100000000) ≤ -Real.log (250000000000 / 374214270287) ∧
    -Real.log (250000000000 / 374214270287) ≤ (403367631 / 1000000000) := by
  have h := checkLog_sound (w := (124214270287 / 624214270287)) (n := 12)
    (lo := (40336763 / 100000000)) (hi := (403367631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374214270287 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374214270287 / 250000000000) = 1/(250000000000 / 374214270287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (40336763 / 100000000) (403367631 / 1000000000) (Real.log (374214270287 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (374214270287 / 250000000000) = -Real.log (250000000000 / 374214270287) := by
    rw [show ((374214270287 / 250000000000) : ℝ) = ((250000000000 / 374214270287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (20212117 / 50000000) ≤ -Real.log (500000000000 / 749083484993) ∧
    -Real.log (500000000000 / 749083484993) ≤ (404242341 / 1000000000) := by
  have h := checkLog_sound (w := (249083484993 / 1249083484993)) (n := 12)
    (lo := (20212117 / 50000000)) (hi := (404242341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((749083484993 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(749083484993 / 500000000000) = 1/(500000000000 / 749083484993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (20212117 / 50000000) (404242341 / 1000000000) (Real.log (749083484993 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (749083484993 / 500000000000) = -Real.log (500000000000 / 749083484993) := by
    rw [show ((749083484993 / 500000000000) : ℝ) = ((500000000000 / 749083484993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (8952607 / 31250000) ≤ -Real.log (250000000000 / 332934023527) ∧
    -Real.log (250000000000 / 332934023527) ≤ (11459337 / 40000000) := by
  have h := checkLog_sound (w := (82934023527 / 582934023527)) (n := 12)
    (lo := (8952607 / 31250000)) (hi := (11459337 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((332934023527 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(332934023527 / 250000000000) = 1/(250000000000 / 332934023527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (8952607 / 31250000) (11459337 / 40000000) (Real.log (332934023527 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (332934023527 / 250000000000) = -Real.log (250000000000 / 332934023527) := by
    rw [show ((332934023527 / 250000000000) : ℝ) = ((250000000000 / 332934023527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (287110137 / 1000000000) ≤ -Real.log (250000000000 / 333142742847) ∧
    -Real.log (250000000000 / 333142742847) ≤ (143555069 / 500000000) := by
  have h := checkLog_sound (w := (83142742847 / 583142742847)) (n := 12)
    (lo := (287110137 / 1000000000)) (hi := (143555069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((333142742847 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(333142742847 / 250000000000) = 1/(250000000000 / 333142742847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (287110137 / 1000000000) (143555069 / 500000000) (Real.log (333142742847 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (333142742847 / 250000000000) = -Real.log (250000000000 / 333142742847) := by
    rw [show ((333142742847 / 250000000000) : ℝ) = ((250000000000 / 333142742847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (10268831 / 500000000) ≤ -Real.log (979671799071 / 1000000000000) ∧
    -Real.log (979671799071 / 1000000000000) ≤ (20537663 / 1000000000) := by
  have h := checkLog_sound (w := (20328200929 / 1979671799071)) (n := 12)
    (lo := (10268831 / 500000000)) (hi := (20537663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979671799071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979671799071) = 1/(979671799071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-20537663 / 1000000000) (-10268831 / 500000000) (Real.log (979671799071 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (20448403 / 1000000000) ≤ -Real.log (9797592471 / 10000000000) ∧
    -Real.log (9797592471 / 10000000000) ≤ (5112101 / 250000000) := by
  have h := checkLog_sound (w := (202407529 / 19797592471)) (n := 12)
    (lo := (20448403 / 1000000000)) (hi := (5112101 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9797592471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9797592471) = 1/(9797592471 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5112101 / 250000000) (-20448403 / 1000000000) (Real.log (9797592471 / 10000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell052

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell053Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell053
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (49628199 / 200000000) ≤ -Real.log (2560 / 3281) ∧
    -Real.log (2560 / 3281) ≤ (62035249 / 250000000) := by
  have h := checkLog_sound (w := (721 / 5841)) (n := 12)
    (lo := (49628199 / 200000000)) (hi := (62035249 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3281 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3281 / 2560) = 1/(2560 / 3281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (49628199 / 200000000) (62035249 / 250000000) (Real.log (3281 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3281 / 2560) = -Real.log (2560 / 3281) := by
    rw [show ((3281 / 2560) : ℝ) = ((2560 / 3281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (10337041 / 31250000) ≤ -Real.log (1839 / 2560) ∧
    -Real.log (1839 / 2560) ≤ (330785313 / 1000000000) := by
  have h := checkLog_sound (w := (721 / 4399)) (n := 12)
    (lo := (10337041 / 31250000)) (hi := (330785313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1839) = 1/(1839 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-330785313 / 1000000000) (-10337041 / 31250000) (Real.log (1839 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (247683713 / 1000000000) ≤ -Real.log (5120 / 6559) ∧
    -Real.log (5120 / 6559) ≤ (123841857 / 500000000) := by
  have h := checkLog_sound (w := (1439 / 11679)) (n := 12)
    (lo := (247683713 / 1000000000)) (hi := (123841857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6559 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6559 / 5120) = 1/(5120 / 6559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (247683713 / 1000000000) (123841857 / 500000000) (Real.log (6559 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6559 / 5120) = -Real.log (5120 / 6559) := by
    rw [show ((6559 / 5120) : ℝ) = ((5120 / 6559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (5155781 / 15625000) ≤ -Real.log (3681 / 5120) ∧
    -Real.log (3681 / 5120) ≤ (65993997 / 200000000) := by
  have h := checkLog_sound (w := (1439 / 8801)) (n := 12)
    (lo := (5155781 / 15625000)) (hi := (65993997 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3681) = 1/(3681 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-65993997 / 200000000) (-5155781 / 15625000) (Real.log (3681 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (45457859 / 250000000) ≤ -Real.log (250000 / 299853) ∧
    -Real.log (250000 / 299853) ≤ (181831437 / 1000000000) := by
  have h := checkLog_sound (w := (49853 / 549853)) (n := 12)
    (lo := (45457859 / 250000000)) (hi := (181831437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299853 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299853 / 250000) = 1/(250000 / 299853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (45457859 / 250000000) (181831437 / 1000000000) (Real.log (299853 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (299853 / 250000) = -Real.log (250000 / 299853) := by
    rw [show ((299853 / 250000) : ℝ) = ((250000 / 299853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (222408821 / 1000000000) ≤ -Real.log (200147 / 250000) ∧
    -Real.log (200147 / 250000) ≤ (111204411 / 500000000) := by
  have h := checkLog_sound (w := (49853 / 450147)) (n := 12)
    (lo := (222408821 / 1000000000)) (hi := (111204411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 200147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 200147) = 1/(200147 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-111204411 / 500000000) (-222408821 / 1000000000) (Real.log (200147 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (182180713 / 1000000000) ≤ -Real.log (1000000 / 1199831) ∧
    -Real.log (1000000 / 1199831) ≤ (91090357 / 500000000) := by
  have h := checkLog_sound (w := (199831 / 2199831)) (n := 12)
    (lo := (182180713 / 1000000000)) (hi := (91090357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1199831 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1199831 / 1000000) = 1/(1000000 / 1199831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (182180713 / 1000000000) (91090357 / 500000000) (Real.log (1199831 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1199831 / 1000000) = -Real.log (1000000 / 1199831) := by
    rw [show ((1199831 / 1000000) : ℝ) = ((1000000 / 1199831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (222932323 / 1000000000) ≤ -Real.log (800169 / 1000000) ∧
    -Real.log (800169 / 1000000) ≤ (55733081 / 250000000) := by
  have h := checkLog_sound (w := (199831 / 1800169)) (n := 12)
    (lo := (222932323 / 1000000000)) (hi := (55733081 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 800169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 800169) = 1/(800169 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-55733081 / 250000000) (-222932323 / 1000000000) (Real.log (800169 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (66642681 / 500000000) ≤ -Real.log (62500 / 71411) ∧
    -Real.log (62500 / 71411) ≤ (133285363 / 1000000000) := by
  have h := checkLog_sound (w := (8911 / 133911)) (n := 12)
    (lo := (66642681 / 500000000)) (hi := (133285363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71411 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71411 / 62500) = 1/(62500 / 71411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (66642681 / 500000000) (133285363 / 1000000000) (Real.log (71411 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (71411 / 62500) = -Real.log (62500 / 71411) := by
    rw [show ((71411 / 62500) : ℝ) = ((62500 / 71411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (153822733 / 1000000000) ≤ -Real.log (53589 / 62500) ∧
    -Real.log (53589 / 62500) ≤ (76911367 / 500000000) := by
  have h := checkLog_sound (w := (8911 / 116089)) (n := 12)
    (lo := (153822733 / 1000000000)) (hi := (76911367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 53589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 53589) = 1/(53589 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-76911367 / 500000000) (-153822733 / 1000000000) (Real.log (53589 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (133554017 / 1000000000) ≤ -Real.log (1000000 / 1142883) ∧
    -Real.log (1000000 / 1142883) ≤ (66777009 / 500000000) := by
  have h := checkLog_sound (w := (142883 / 2142883)) (n := 12)
    (lo := (133554017 / 1000000000)) (hi := (66777009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1142883 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1142883 / 1000000) = 1/(1000000 / 1142883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (133554017 / 1000000000) (66777009 / 500000000) (Real.log (1142883 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1142883 / 1000000) = -Real.log (1000000 / 1142883) := by
    rw [show ((1142883 / 1000000) : ℝ) = ((1000000 / 1142883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (77090423 / 500000000) ≤ -Real.log (857117 / 1000000) ∧
    -Real.log (857117 / 1000000) ≤ (154180847 / 1000000000) := by
  have h := checkLog_sound (w := (142883 / 1857117)) (n := 12)
    (lo := (77090423 / 500000000)) (hi := (154180847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 857117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 857117) = 1/(857117 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-154180847 / 1000000000) (-77090423 / 500000000) (Real.log (857117 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (577653697 / 1000000000) ≤ -Real.log (500000000000 / 890926378701) ∧
    -Real.log (500000000000 / 890926378701) ≤ (288826849 / 500000000) := by
  have h := checkLog_sound (w := (390926378701 / 1390926378701)) (n := 12)
    (lo := (577653697 / 1000000000)) (hi := (288826849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((890926378701 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(890926378701 / 500000000000) = 1/(500000000000 / 890926378701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (577653697 / 1000000000) (288826849 / 500000000) (Real.log (890926378701 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (890926378701 / 500000000000) = -Real.log (500000000000 / 890926378701) := by
    rw [show ((890926378701 / 500000000000) : ℝ) = ((500000000000 / 890926378701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (144731577 / 250000000) ≤ -Real.log (100000000000 / 178412180533) ∧
    -Real.log (100000000000 / 178412180533) ≤ (578926309 / 1000000000) := by
  have h := checkLog_sound (w := (78412180533 / 278412180533)) (n := 12)
    (lo := (144731577 / 250000000)) (hi := (578926309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178412180533 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178412180533 / 100000000000) = 1/(100000000000 / 178412180533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (144731577 / 250000000) (578926309 / 1000000000) (Real.log (178412180533 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (178412180533 / 100000000000) = -Real.log (100000000000 / 178412180533) := by
    rw [show ((178412180533 / 100000000000) : ℝ) = ((100000000000 / 178412180533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (404240257 / 1000000000) ≤ -Real.log (100000000000 / 149816384957) ∧
    -Real.log (100000000000 / 149816384957) ≤ (202120129 / 500000000) := by
  have h := checkLog_sound (w := (49816384957 / 249816384957)) (n := 12)
    (lo := (404240257 / 1000000000)) (hi := (202120129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149816384957 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149816384957 / 100000000000) = 1/(100000000000 / 149816384957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (404240257 / 1000000000) (202120129 / 500000000) (Real.log (149816384957 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (149816384957 / 100000000000) = -Real.log (100000000000 / 149816384957) := by
    rw [show ((149816384957 / 100000000000) : ℝ) = ((100000000000 / 149816384957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (405113037 / 1000000000) ≤ -Real.log (62500000000 / 93716999159) ∧
    -Real.log (62500000000 / 93716999159) ≤ (202556519 / 500000000) := by
  have h := checkLog_sound (w := (31216999159 / 156216999159)) (n := 12)
    (lo := (405113037 / 1000000000)) (hi := (202556519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93716999159 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93716999159 / 62500000000) = 1/(62500000000 / 93716999159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (405113037 / 1000000000) (202556519 / 500000000) (Real.log (93716999159 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (93716999159 / 62500000000) = -Real.log (62500000000 / 93716999159) := by
    rw [show ((93716999159 / 62500000000) : ℝ) = ((62500000000 / 93716999159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (57421619 / 200000000) ≤ -Real.log (500000000000 / 666284125473) ∧
    -Real.log (500000000000 / 666284125473) ≤ (560758 / 1953125) := by
  have h := checkLog_sound (w := (166284125473 / 1166284125473)) (n := 12)
    (lo := (57421619 / 200000000)) (hi := (560758 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((666284125473 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(666284125473 / 500000000000) = 1/(500000000000 / 666284125473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (57421619 / 200000000) (560758 / 1953125) (Real.log (666284125473 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (666284125473 / 500000000000) = -Real.log (500000000000 / 666284125473) := by
    rw [show ((666284125473 / 500000000000) : ℝ) = ((500000000000 / 666284125473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (17983429 / 62500000) ≤ -Real.log (500000000000 / 666701862173) ∧
    -Real.log (500000000000 / 666701862173) ≤ (57546973 / 200000000) := by
  have h := checkLog_sound (w := (166701862173 / 1166701862173)) (n := 12)
    (lo := (17983429 / 62500000)) (hi := (57546973 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((666701862173 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(666701862173 / 500000000000) = 1/(500000000000 / 666701862173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (17983429 / 62500000) (57546973 / 200000000) (Real.log (666701862173 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (666701862173 / 500000000000) = -Real.log (500000000000 / 666701862173) := by
    rw [show ((666701862173 / 500000000000) : ℝ) = ((500000000000 / 666701862173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (20626829 / 1000000000) ≤ -Real.log (979584448311 / 1000000000000) ∧
    -Real.log (979584448311 / 1000000000000) ≤ (2062683 / 100000000) := by
  have h := checkLog_sound (w := (20415551689 / 1979584448311)) (n := 12)
    (lo := (20626829 / 1000000000)) (hi := (2062683 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979584448311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979584448311) = 1/(979584448311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-2062683 / 100000000) (-20626829 / 1000000000) (Real.log (979584448311 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (20537371 / 1000000000) ≤ -Real.log (3826844079 / 3906250000) ∧
    -Real.log (3826844079 / 3906250000) ≤ (5134343 / 250000000) := by
  have h := checkLog_sound (w := (79405921 / 7733094079)) (n := 12)
    (lo := (20537371 / 1000000000)) (hi := (5134343 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3826844079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3826844079) = 1/(3826844079 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5134343 / 250000000) (-20537371 / 1000000000) (Real.log (3826844079 / 3906250000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell053

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell054Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell054
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (62149517 / 250000000) ≤ -Real.log (1024 / 1313) ∧
    -Real.log (1024 / 1313) ≤ (248598069 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 2337)) (n := 12)
    (lo := (62149517 / 250000000)) (hi := (248598069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1313 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1313 / 1024) = 1/(1024 / 1313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (62149517 / 250000000) (248598069 / 1000000000) (Real.log (1313 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1313 / 1024) = -Real.log (1024 / 1313) := by
    rw [show ((1313 / 1024) : ℝ) = ((1024 / 1313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (165800653 / 500000000) ≤ -Real.log (735 / 1024) ∧
    -Real.log (735 / 1024) ≤ (331601307 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 1759)) (n := 12)
    (lo := (165800653 / 500000000)) (hi := (331601307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 735) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 735) = 1/(735 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-331601307 / 1000000000) (-165800653 / 500000000) (Real.log (735 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (49628199 / 200000000) ≤ -Real.log (2560 / 3281) ∧
    -Real.log (2560 / 3281) ≤ (62035249 / 250000000) := by
  have h := checkLog_sound (w := (721 / 5841)) (n := 12)
    (lo := (49628199 / 200000000)) (hi := (62035249 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3281 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3281 / 2560) = 1/(2560 / 3281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (49628199 / 200000000) (62035249 / 250000000) (Real.log (3281 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3281 / 2560) = -Real.log (2560 / 3281) := by
    rw [show ((3281 / 2560) : ℝ) = ((2560 / 3281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (10337041 / 31250000) ≤ -Real.log (1839 / 2560) ∧
    -Real.log (1839 / 2560) ≤ (330785313 / 1000000000) := by
  have h := checkLog_sound (w := (721 / 4399)) (n := 12)
    (lo := (10337041 / 31250000)) (hi := (330785313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1839) = 1/(1839 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-330785313 / 1000000000) (-10337041 / 31250000) (Real.log (1839 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (4554497 / 25000000) ≤ -Real.log (100000 / 119983) ∧
    -Real.log (100000 / 119983) ≤ (182179881 / 1000000000) := by
  have h := checkLog_sound (w := (19983 / 219983)) (n := 12)
    (lo := (4554497 / 25000000)) (hi := (182179881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119983 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119983 / 100000) = 1/(100000 / 119983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (4554497 / 25000000) (182179881 / 1000000000) (Real.log (119983 / 100000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (119983 / 100000) = -Real.log (100000 / 119983) := by
    rw [show ((119983 / 100000) : ℝ) = ((100000 / 119983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (222931073 / 1000000000) ≤ -Real.log (80017 / 100000) ∧
    -Real.log (80017 / 100000) ≤ (111465537 / 500000000) := by
  have h := checkLog_sound (w := (19983 / 180017)) (n := 12)
    (lo := (222931073 / 1000000000)) (hi := (111465537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 80017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 80017) = 1/(80017 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-111465537 / 500000000) (-222931073 / 1000000000) (Real.log (80017 / 100000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (45632467 / 250000000) ≤ -Real.log (4000 / 4801) ∧
    -Real.log (4000 / 4801) ≤ (182529869 / 1000000000) := by
  have h := checkLog_sound (w := (801 / 8801)) (n := 12)
    (lo := (45632467 / 250000000)) (hi := (182529869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4801 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4801 / 4000) = 1/(4000 / 4801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (45632467 / 250000000) (182529869 / 1000000000) (Real.log (4801 / 4000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4801 / 4000) = -Real.log (4000 / 4801) := by
    rw [show ((4801 / 4000) : ℝ) = ((4000 / 4801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2234561 / 10000000) ≤ -Real.log (3199 / 4000) ∧
    -Real.log (3199 / 4000) ≤ (223456101 / 1000000000) := by
  have h := checkLog_sound (w := (801 / 7199)) (n := 12)
    (lo := (2234561 / 10000000)) (hi := (223456101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 3199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000 / 3199) = 1/(3199 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-223456101 / 1000000000) (-2234561 / 10000000) (Real.log (3199 / 4000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (66776571 / 500000000) ≤ -Real.log (500000 / 571441) ∧
    -Real.log (500000 / 571441) ≤ (133553143 / 1000000000) := by
  have h := checkLog_sound (w := (71441 / 1071441)) (n := 12)
    (lo := (66776571 / 500000000)) (hi := (133553143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((571441 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(571441 / 500000) = 1/(500000 / 571441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (66776571 / 500000000) (133553143 / 1000000000) (Real.log (571441 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (571441 / 500000) = -Real.log (500000 / 571441) := by
    rw [show ((571441 / 500000) : ℝ) = ((500000 / 571441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (963623 / 6250000) ≤ -Real.log (428559 / 500000) ∧
    -Real.log (428559 / 500000) ≤ (154179681 / 1000000000) := by
  have h := checkLog_sound (w := (71441 / 928559)) (n := 12)
    (lo := (963623 / 6250000)) (hi := (154179681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 428559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 428559) = 1/(428559 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-154179681 / 1000000000) (-963623 / 6250000) (Real.log (428559 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (669113 / 5000000) ≤ -Real.log (100000 / 114319) ∧
    -Real.log (100000 / 114319) ≤ (133822601 / 1000000000) := by
  have h := checkLog_sound (w := (14319 / 214319)) (n := 12)
    (lo := (669113 / 5000000)) (hi := (133822601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114319 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(114319 / 100000) = 1/(100000 / 114319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (669113 / 5000000) (133822601 / 1000000000) (Real.log (114319 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (114319 / 100000) = -Real.log (100000 / 114319) := by
    rw [show ((114319 / 100000) : ℝ) = ((100000 / 114319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (9658693 / 62500000) ≤ -Real.log (85681 / 100000) ∧
    -Real.log (85681 / 100000) ≤ (154539089 / 1000000000) := by
  have h := checkLog_sound (w := (14319 / 185681)) (n := 12)
    (lo := (9658693 / 62500000)) (hi := (154539089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 85681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 85681) = 1/(85681 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-154539089 / 1000000000) (-9658693 / 62500000) (Real.log (85681 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (144731577 / 250000000) ≤ -Real.log (62500000000 / 111507612833) ∧
    -Real.log (62500000000 / 111507612833) ≤ (578926309 / 1000000000) := by
  have h := checkLog_sound (w := (49007612833 / 174007612833)) (n := 12)
    (lo := (144731577 / 250000000)) (hi := (578926309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111507612833 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111507612833 / 62500000000) = 1/(62500000000 / 111507612833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (144731577 / 250000000) (578926309 / 1000000000) (Real.log (111507612833 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (111507612833 / 62500000000) = -Real.log (62500000000 / 111507612833) := by
    rw [show ((111507612833 / 62500000000) : ℝ) = ((62500000000 / 111507612833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (928319 / 1600000) ≤ -Real.log (7812500000 / 13956207483) ∧
    -Real.log (7812500000 / 13956207483) ≤ (36262461 / 62500000) := by
  have h := checkLog_sound (w := (6143707483 / 21768707483)) (n := 12)
    (lo := (928319 / 1600000)) (hi := (36262461 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13956207483 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13956207483 / 7812500000) = 1/(7812500000 / 13956207483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (928319 / 1600000) (36262461 / 62500000) (Real.log (13956207483 / 7812500000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (13956207483 / 7812500000) = -Real.log (7812500000 / 13956207483) := by
    rw [show ((13956207483 / 7812500000) : ℝ) = ((7812500000 / 13956207483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (405110953 / 1000000000) ≤ -Real.log (500000000000 / 749734431433) ∧
    -Real.log (500000000000 / 749734431433) ≤ (202555477 / 500000000) := by
  have h := checkLog_sound (w := (249734431433 / 1249734431433)) (n := 12)
    (lo := (405110953 / 1000000000)) (hi := (202555477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((749734431433 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(749734431433 / 500000000000) = 1/(500000000000 / 749734431433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (405110953 / 1000000000) (202555477 / 500000000) (Real.log (749734431433 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (749734431433 / 500000000000) = -Real.log (500000000000 / 749734431433) := by
    rw [show ((749734431433 / 500000000000) : ℝ) = ((500000000000 / 749734431433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (25374123 / 62500000) ≤ -Real.log (500000000000 / 750390747109) ∧
    -Real.log (500000000000 / 750390747109) ≤ (405985969 / 1000000000) := by
  have h := checkLog_sound (w := (250390747109 / 1250390747109)) (n := 12)
    (lo := (25374123 / 62500000)) (hi := (405985969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((750390747109 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(750390747109 / 500000000000) = 1/(500000000000 / 750390747109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (25374123 / 62500000) (405985969 / 1000000000) (Real.log (750390747109 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (750390747109 / 500000000000) = -Real.log (500000000000 / 750390747109) := by
    rw [show ((750390747109 / 500000000000) : ℝ) = ((500000000000 / 750390747109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (143866411 / 500000000) ≤ -Real.log (500000000000 / 666700500981) ∧
    -Real.log (500000000000 / 666700500981) ≤ (287732823 / 1000000000) := by
  have h := checkLog_sound (w := (166700500981 / 1166700500981)) (n := 12)
    (lo := (143866411 / 500000000)) (hi := (287732823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((666700500981 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(666700500981 / 500000000000) = 1/(500000000000 / 666700500981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (143866411 / 500000000) (287732823 / 1000000000) (Real.log (666700500981 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (666700500981 / 500000000000) = -Real.log (500000000000 / 666700500981) := by
    rw [show ((666700500981 / 500000000000) : ℝ) = ((500000000000 / 666700500981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (36045211 / 125000000) ≤ -Real.log (125000000000 / 166779974557) ∧
    -Real.log (125000000000 / 166779974557) ≤ (288361689 / 1000000000) := by
  have h := checkLog_sound (w := (41779974557 / 291779974557)) (n := 12)
    (lo := (36045211 / 125000000)) (hi := (288361689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166779974557 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(166779974557 / 125000000000) = 1/(125000000000 / 166779974557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (36045211 / 125000000) (288361689 / 1000000000) (Real.log (166779974557 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (166779974557 / 125000000000) = -Real.log (125000000000 / 166779974557) := by
    rw [show ((166779974557 / 125000000000) : ℝ) = ((125000000000 / 166779974557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2589561 / 125000000) ≤ -Real.log (9794966239 / 10000000000) ∧
    -Real.log (9794966239 / 10000000000) ≤ (20716489 / 1000000000) := by
  have h := checkLog_sound (w := (205033761 / 19794966239)) (n := 12)
    (lo := (2589561 / 125000000)) (hi := (20716489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9794966239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9794966239) = 1/(9794966239 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-20716489 / 1000000000) (-2589561 / 125000000) (Real.log (9794966239 / 10000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (20626537 / 1000000000) ≤ -Real.log (244896183519 / 250000000000) ∧
    -Real.log (244896183519 / 250000000000) ≤ (10313269 / 500000000) := by
  have h := checkLog_sound (w := (5103816481 / 494896183519)) (n := 12)
    (lo := (20626537 / 1000000000)) (hi := (10313269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244896183519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244896183519) = 1/(244896183519 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-10313269 / 500000000) (-20626537 / 1000000000) (Real.log (244896183519 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell054

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell055Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell055
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (249054933 / 1000000000) ≤ -Real.log (640 / 821) ∧
    -Real.log (640 / 821) ≤ (124527467 / 500000000) := by
  have h := checkLog_sound (w := (181 / 1461)) (n := 12)
    (lo := (249054933 / 1000000000)) (hi := (124527467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(821 / 640) = 1/(640 / 821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (249054933 / 1000000000) (124527467 / 500000000) (Real.log (821 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (821 / 640) = -Real.log (640 / 821) := by
    rw [show ((821 / 640) : ℝ) = ((640 / 821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (166208983 / 500000000) ≤ -Real.log (459 / 640) ∧
    -Real.log (459 / 640) ≤ (332417967 / 1000000000) := by
  have h := checkLog_sound (w := (181 / 1099)) (n := 12)
    (lo := (166208983 / 500000000)) (hi := (332417967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 459) = 1/(459 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-332417967 / 1000000000) (-166208983 / 500000000) (Real.log (459 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (62149517 / 250000000) ≤ -Real.log (1024 / 1313) ∧
    -Real.log (1024 / 1313) ≤ (248598069 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 2337)) (n := 12)
    (lo := (62149517 / 250000000)) (hi := (248598069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1313 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1313 / 1024) = 1/(1024 / 1313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (62149517 / 250000000) (248598069 / 1000000000) (Real.log (1313 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1313 / 1024) = -Real.log (1024 / 1313) := by
    rw [show ((1313 / 1024) : ℝ) = ((1024 / 1313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (165800653 / 500000000) ≤ -Real.log (735 / 1024) ∧
    -Real.log (735 / 1024) ≤ (331601307 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 1759)) (n := 12)
    (lo := (165800653 / 500000000)) (hi := (331601307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 735) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 735) = 1/(735 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-331601307 / 1000000000) (-165800653 / 500000000) (Real.log (735 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (36505807 / 200000000) ≤ -Real.log (1000000 / 1200249) ∧
    -Real.log (1000000 / 1200249) ≤ (45632259 / 250000000) := by
  have h := checkLog_sound (w := (200249 / 2200249)) (n := 12)
    (lo := (36505807 / 200000000)) (hi := (45632259 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1200249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1200249 / 1000000) = 1/(1000000 / 1200249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (36505807 / 200000000) (45632259 / 250000000) (Real.log (1200249 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1200249 / 1000000) = -Real.log (1000000 / 1200249) := by
    rw [show ((1200249 / 1000000) : ℝ) = ((1000000 / 1200249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (223454849 / 1000000000) ≤ -Real.log (799751 / 1000000) ∧
    -Real.log (799751 / 1000000) ≤ (4469097 / 20000000) := by
  have h := checkLog_sound (w := (200249 / 1799751)) (n := 12)
    (lo := (223454849 / 1000000000)) (hi := (4469097 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 799751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 799751) = 1/(799751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-4469097 / 20000000) (-223454849 / 1000000000) (Real.log (799751 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (182878901 / 1000000000) ≤ -Real.log (1000000 / 1200669) ∧
    -Real.log (1000000 / 1200669) ≤ (91439451 / 500000000) := by
  have h := checkLog_sound (w := (200669 / 2200669)) (n := 12)
    (lo := (182878901 / 1000000000)) (hi := (91439451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1200669 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1200669 / 1000000) = 1/(1000000 / 1200669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (182878901 / 1000000000) (91439451 / 500000000) (Real.log (1200669 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1200669 / 1000000) = -Real.log (1000000 / 1200669) := by
    rw [show ((1200669 / 1000000) : ℝ) = ((1000000 / 1200669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (223980151 / 1000000000) ≤ -Real.log (799331 / 1000000) ∧
    -Real.log (799331 / 1000000) ≤ (27997519 / 125000000) := by
  have h := checkLog_sound (w := (200669 / 1799331)) (n := 12)
    (lo := (223980151 / 1000000000)) (hi := (27997519 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 799331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 799331) = 1/(799331 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-27997519 / 125000000) (-223980151 / 1000000000) (Real.log (799331 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (5352869 / 40000000) ≤ -Real.log (1000000 / 1143189) ∧
    -Real.log (1000000 / 1143189) ≤ (66910863 / 500000000) := by
  have h := checkLog_sound (w := (143189 / 2143189)) (n := 12)
    (lo := (5352869 / 40000000)) (hi := (66910863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1143189 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1143189 / 1000000) = 1/(1000000 / 1143189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (5352869 / 40000000) (66910863 / 500000000) (Real.log (1143189 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1143189 / 1000000) = -Real.log (1000000 / 1143189) := by
    rw [show ((1143189 / 1000000) : ℝ) = ((1000000 / 1143189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (154537921 / 1000000000) ≤ -Real.log (856811 / 1000000) ∧
    -Real.log (856811 / 1000000) ≤ (77268961 / 500000000) := by
  have h := checkLog_sound (w := (143189 / 1856811)) (n := 12)
    (lo := (154537921 / 1000000000)) (hi := (77268961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 856811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 856811) = 1/(856811 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-77268961 / 500000000) (-154537921 / 1000000000) (Real.log (856811 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (33522559 / 250000000) ≤ -Real.log (125000 / 142937) ∧
    -Real.log (125000 / 142937) ≤ (134090237 / 1000000000) := by
  have h := checkLog_sound (w := (17937 / 267937)) (n := 12)
    (lo := (33522559 / 250000000)) (hi := (134090237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142937 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142937 / 125000) = 1/(125000 / 142937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (33522559 / 250000000) (134090237 / 1000000000) (Real.log (142937 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (142937 / 125000) = -Real.log (125000 / 142937) := by
    rw [show ((142937 / 125000) : ℝ) = ((125000 / 142937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (154896291 / 1000000000) ≤ -Real.log (107063 / 125000) ∧
    -Real.log (107063 / 125000) ≤ (38724073 / 250000000) := by
  have h := checkLog_sound (w := (17937 / 232063)) (n := 12)
    (lo := (154896291 / 1000000000)) (hi := (38724073 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 107063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 107063) = 1/(107063 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-38724073 / 250000000) (-154896291 / 1000000000) (Real.log (107063 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (928319 / 1600000) ≤ -Real.log (500000000000 / 893197278911) ∧
    -Real.log (500000000000 / 893197278911) ≤ (36262461 / 62500000) := by
  have h := checkLog_sound (w := (393197278911 / 1393197278911)) (n := 12)
    (lo := (928319 / 1600000)) (hi := (36262461 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((893197278911 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(893197278911 / 500000000000) = 1/(500000000000 / 893197278911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (928319 / 1600000) (36262461 / 62500000) (Real.log (893197278911 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (893197278911 / 500000000000) = -Real.log (500000000000 / 893197278911) := by
    rw [show ((893197278911 / 500000000000) : ℝ) = ((500000000000 / 893197278911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (581472899 / 1000000000) ≤ -Real.log (500000000000 / 894335511983) ∧
    -Real.log (500000000000 / 894335511983) ≤ (5814729 / 10000000) := by
  have h := checkLog_sound (w := (394335511983 / 1394335511983)) (n := 12)
    (lo := (581472899 / 1000000000)) (hi := (5814729 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((894335511983 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(894335511983 / 500000000000) = 1/(500000000000 / 894335511983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (581472899 / 1000000000) (5814729 / 10000000) (Real.log (894335511983 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (894335511983 / 500000000000) = -Real.log (500000000000 / 894335511983) := by
    rw [show ((894335511983 / 500000000000) : ℝ) = ((500000000000 / 894335511983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (81196777 / 200000000) ≤ -Real.log (500000000000 / 750389183633) ∧
    -Real.log (500000000000 / 750389183633) ≤ (202991943 / 500000000) := by
  have h := checkLog_sound (w := (250389183633 / 1250389183633)) (n := 12)
    (lo := (81196777 / 200000000)) (hi := (202991943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((750389183633 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(750389183633 / 500000000000) = 1/(500000000000 / 750389183633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (81196777 / 200000000) (202991943 / 500000000) (Real.log (750389183633 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (750389183633 / 500000000000) = -Real.log (500000000000 / 750389183633) := by
    rw [show ((750389183633 / 500000000000) : ℝ) = ((500000000000 / 750389183633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (101714763 / 250000000) ≤ -Real.log (4000000000 / 6008369499) ∧
    -Real.log (4000000000 / 6008369499) ≤ (406859053 / 1000000000) := by
  have h := checkLog_sound (w := (2008369499 / 10008369499)) (n := 12)
    (lo := (101714763 / 250000000)) (hi := (406859053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6008369499 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6008369499 / 4000000000) = 1/(4000000000 / 6008369499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (101714763 / 250000000) (406859053 / 1000000000) (Real.log (6008369499 / 4000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (6008369499 / 4000000000) = -Real.log (4000000000 / 6008369499) := by
    rw [show ((6008369499 / 4000000000) : ℝ) = ((4000000000 / 6008369499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (144179823 / 500000000) ≤ -Real.log (500000000000 / 667118536059) ∧
    -Real.log (500000000000 / 667118536059) ≤ (288359647 / 1000000000) := by
  have h := checkLog_sound (w := (167118536059 / 1167118536059)) (n := 12)
    (lo := (144179823 / 500000000)) (hi := (288359647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667118536059 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667118536059 / 500000000000) = 1/(500000000000 / 667118536059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (144179823 / 500000000) (288359647 / 1000000000) (Real.log (667118536059 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (667118536059 / 500000000000) = -Real.log (500000000000 / 667118536059) := by
    rw [show ((667118536059 / 500000000000) : ℝ) = ((500000000000 / 667118536059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (288986527 / 1000000000) ≤ -Real.log (100000000000 / 133507374163) ∧
    -Real.log (100000000000 / 133507374163) ≤ (9030829 / 31250000) := by
  have h := checkLog_sound (w := (33507374163 / 233507374163)) (n := 12)
    (lo := (288986527 / 1000000000)) (hi := (9030829 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133507374163 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133507374163 / 100000000000) = 1/(100000000000 / 133507374163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (288986527 / 1000000000) (9030829 / 31250000) (Real.log (133507374163 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (133507374163 / 100000000000) = -Real.log (100000000000 / 133507374163) := by
    rw [show ((133507374163 / 100000000000) : ℝ) = ((100000000000 / 133507374163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (10403027 / 500000000) ≤ -Real.log (15303264031 / 15625000000) ∧
    -Real.log (15303264031 / 15625000000) ≤ (4161211 / 200000000) := by
  have h := checkLog_sound (w := (321735969 / 30928264031)) (n := 12)
    (lo := (10403027 / 500000000)) (hi := (4161211 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15303264031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15303264031) = 1/(15303264031 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4161211 / 200000000) (-10403027 / 500000000) (Real.log (15303264031 / 15625000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (4143239 / 200000000) ≤ -Real.log (979496910279 / 1000000000000) ∧
    -Real.log (979496910279 / 1000000000000) ≤ (5179049 / 250000000) := by
  have h := checkLog_sound (w := (20503089721 / 1979496910279)) (n := 12)
    (lo := (4143239 / 200000000)) (hi := (5179049 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979496910279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979496910279) = 1/(979496910279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5179049 / 250000000) (-4143239 / 200000000) (Real.log (979496910279 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell055

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell056Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell056
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (62377897 / 250000000) ≤ -Real.log (5120 / 6571) ∧
    -Real.log (5120 / 6571) ≤ (249511589 / 1000000000) := by
  have h := checkLog_sound (w := (1451 / 11691)) (n := 12)
    (lo := (62377897 / 250000000)) (hi := (249511589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6571 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6571 / 5120) = 1/(5120 / 6571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (62377897 / 250000000) (249511589 / 1000000000) (Real.log (6571 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6571 / 5120) = -Real.log (5120 / 6571) := by
    rw [show ((6571 / 5120) : ℝ) = ((5120 / 6571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (333235293 / 1000000000) ≤ -Real.log (3669 / 5120) ∧
    -Real.log (3669 / 5120) ≤ (166617647 / 500000000) := by
  have h := checkLog_sound (w := (1451 / 8789)) (n := 12)
    (lo := (333235293 / 1000000000)) (hi := (166617647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3669) = 1/(3669 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-166617647 / 500000000) (-333235293 / 1000000000) (Real.log (3669 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (249054933 / 1000000000) ≤ -Real.log (640 / 821) ∧
    -Real.log (640 / 821) ≤ (124527467 / 500000000) := by
  have h := checkLog_sound (w := (181 / 1461)) (n := 12)
    (lo := (249054933 / 1000000000)) (hi := (124527467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(821 / 640) = 1/(640 / 821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (249054933 / 1000000000) (124527467 / 500000000) (Real.log (821 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (821 / 640) = -Real.log (640 / 821) := by
    rw [show ((821 / 640) : ℝ) = ((640 / 821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (166208983 / 500000000) ≤ -Real.log (459 / 640) ∧
    -Real.log (459 / 640) ≤ (332417967 / 1000000000) := by
  have h := checkLog_sound (w := (181 / 1099)) (n := 12)
    (lo := (166208983 / 500000000)) (hi := (332417967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 459) = 1/(459 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-332417967 / 1000000000) (-166208983 / 500000000) (Real.log (459 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (45719517 / 250000000) ≤ -Real.log (250000 / 300167) ∧
    -Real.log (250000 / 300167) ≤ (182878069 / 1000000000) := by
  have h := checkLog_sound (w := (50167 / 550167)) (n := 12)
    (lo := (45719517 / 250000000)) (hi := (182878069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300167 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300167 / 250000) = 1/(250000 / 300167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (45719517 / 250000000) (182878069 / 1000000000) (Real.log (300167 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (300167 / 250000) = -Real.log (250000 / 300167) := by
    rw [show ((300167 / 250000) : ℝ) = ((250000 / 300167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2239789 / 10000000) ≤ -Real.log (199833 / 250000) ∧
    -Real.log (199833 / 250000) ≤ (223978901 / 1000000000) := by
  have h := checkLog_sound (w := (50167 / 449833)) (n := 12)
    (lo := (2239789 / 10000000)) (hi := (223978901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 199833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 199833) = 1/(199833 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-223978901 / 1000000000) (-2239789 / 10000000) (Real.log (199833 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (9161349 / 50000000) ≤ -Real.log (1000000 / 1201087) ∧
    -Real.log (1000000 / 1201087) ≤ (183226981 / 1000000000) := by
  have h := checkLog_sound (w := (201087 / 2201087)) (n := 12)
    (lo := (9161349 / 50000000)) (hi := (183226981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1201087 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1201087 / 1000000) = 1/(1000000 / 1201087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (9161349 / 50000000) (183226981 / 1000000000) (Real.log (1201087 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1201087 / 1000000) = -Real.log (1000000 / 1201087) := by
    rw [show ((1201087 / 1000000) : ℝ) = ((1000000 / 1201087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (8980129 / 40000000) ≤ -Real.log (798913 / 1000000) ∧
    -Real.log (798913 / 1000000) ≤ (112251613 / 500000000) := by
  have h := checkLog_sound (w := (201087 / 1798913)) (n := 12)
    (lo := (8980129 / 40000000)) (hi := (112251613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 798913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 798913) = 1/(798913 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-112251613 / 500000000) (-8980129 / 40000000) (Real.log (798913 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (134089361 / 1000000000) ≤ -Real.log (200000 / 228699) ∧
    -Real.log (200000 / 228699) ≤ (67044681 / 500000000) := by
  have h := checkLog_sound (w := (28699 / 428699)) (n := 12)
    (lo := (134089361 / 1000000000)) (hi := (67044681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((228699 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(228699 / 200000) = 1/(200000 / 228699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (134089361 / 1000000000) (67044681 / 500000000) (Real.log (228699 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (228699 / 200000) = -Real.log (200000 / 228699) := by
    rw [show ((228699 / 200000) : ℝ) = ((200000 / 228699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (154895123 / 1000000000) ≤ -Real.log (171301 / 200000) ∧
    -Real.log (171301 / 200000) ≤ (38723781 / 250000000) := by
  have h := checkLog_sound (w := (28699 / 371301)) (n := 12)
    (lo := (154895123 / 1000000000)) (hi := (38723781 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 171301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 171301) = 1/(171301 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-38723781 / 250000000) (-154895123 / 1000000000) (Real.log (171301 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (134357801 / 1000000000) ≤ -Real.log (500000 / 571901) ∧
    -Real.log (500000 / 571901) ≤ (67178901 / 500000000) := by
  have h := checkLog_sound (w := (71901 / 1071901)) (n := 12)
    (lo := (134357801 / 1000000000)) (hi := (67178901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((571901 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(571901 / 500000) = 1/(500000 / 571901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (134357801 / 1000000000) (67178901 / 500000000) (Real.log (571901 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (571901 / 500000) = -Real.log (500000 / 571901) := by
    rw [show ((571901 / 500000) : ℝ) = ((500000 / 571901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (155253621 / 1000000000) ≤ -Real.log (428099 / 500000) ∧
    -Real.log (428099 / 500000) ≤ (77626811 / 500000000) := by
  have h := checkLog_sound (w := (71901 / 928099)) (n := 12)
    (lo := (155253621 / 1000000000)) (hi := (77626811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 428099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 428099) = 1/(428099 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-77626811 / 500000000) (-155253621 / 1000000000) (Real.log (428099 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (581472899 / 1000000000) ≤ -Real.log (250000000000 / 447167755991) ∧
    -Real.log (250000000000 / 447167755991) ≤ (5814729 / 10000000) := by
  have h := checkLog_sound (w := (197167755991 / 697167755991)) (n := 12)
    (lo := (581472899 / 1000000000)) (hi := (5814729 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((447167755991 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(447167755991 / 250000000000) = 1/(250000000000 / 447167755991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (581472899 / 1000000000) (5814729 / 10000000) (Real.log (447167755991 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (447167755991 / 250000000000) = -Real.log (250000000000 / 447167755991) := by
    rw [show ((447167755991 / 250000000000) : ℝ) = ((250000000000 / 447167755991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (291373441 / 500000000) ≤ -Real.log (500000000000 / 895475606433) ∧
    -Real.log (500000000000 / 895475606433) ≤ (582746883 / 1000000000) := by
  have h := checkLog_sound (w := (395475606433 / 1395475606433)) (n := 12)
    (lo := (291373441 / 500000000)) (hi := (582746883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((895475606433 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(895475606433 / 500000000000) = 1/(500000000000 / 895475606433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (291373441 / 500000000) (582746883 / 1000000000) (Real.log (895475606433 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (895475606433 / 500000000000) = -Real.log (500000000000 / 895475606433) := by
    rw [show ((895475606433 / 500000000000) : ℝ) = ((500000000000 / 895475606433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (50857121 / 125000000) ≤ -Real.log (500000000000 / 751044622259) ∧
    -Real.log (500000000000 / 751044622259) ≤ (406856969 / 1000000000) := by
  have h := checkLog_sound (w := (251044622259 / 1251044622259)) (n := 12)
    (lo := (50857121 / 125000000)) (hi := (406856969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((751044622259 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(751044622259 / 500000000000) = 1/(500000000000 / 751044622259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (50857121 / 125000000) (406856969 / 1000000000) (Real.log (751044622259 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (751044622259 / 500000000000) = -Real.log (500000000000 / 751044622259) := by
    rw [show ((751044622259 / 500000000000) : ℝ) = ((500000000000 / 751044622259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (81546041 / 200000000) ≤ -Real.log (62500000000 / 93962593549) ∧
    -Real.log (62500000000 / 93962593549) ≤ (203865103 / 500000000) := by
  have h := checkLog_sound (w := (31462593549 / 156462593549)) (n := 12)
    (lo := (81546041 / 200000000)) (hi := (203865103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93962593549 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93962593549 / 62500000000) = 1/(62500000000 / 93962593549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (81546041 / 200000000) (203865103 / 500000000) (Real.log (93962593549 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (93962593549 / 62500000000) = -Real.log (62500000000 / 93962593549) := by
    rw [show ((93962593549 / 62500000000) : ℝ) = ((62500000000 / 93962593549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (57796897 / 200000000) ≤ -Real.log (500000000000 / 667535507673) ∧
    -Real.log (500000000000 / 667535507673) ≤ (144492243 / 500000000) := by
  have h := checkLog_sound (w := (167535507673 / 1167535507673)) (n := 12)
    (lo := (57796897 / 200000000)) (hi := (144492243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667535507673 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667535507673 / 500000000000) = 1/(500000000000 / 667535507673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (57796897 / 200000000) (144492243 / 500000000) (Real.log (667535507673 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (667535507673 / 500000000000) = -Real.log (500000000000 / 667535507673) := by
    rw [show ((667535507673 / 500000000000) : ℝ) = ((500000000000 / 667535507673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (144805711 / 500000000) ≤ -Real.log (500000000000 / 667954141449) ∧
    -Real.log (500000000000 / 667954141449) ≤ (289611423 / 1000000000) := by
  have h := checkLog_sound (w := (167954141449 / 1167954141449)) (n := 12)
    (lo := (144805711 / 500000000)) (hi := (289611423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667954141449 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667954141449 / 500000000000) = 1/(500000000000 / 667954141449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (144805711 / 500000000) (289611423 / 1000000000) (Real.log (667954141449 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (667954141449 / 500000000000) = -Real.log (500000000000 / 667954141449) := by
    rw [show ((667954141449 / 500000000000) : ℝ) = ((500000000000 / 667954141449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1044791 / 50000000) ≤ -Real.log (244830246199 / 250000000000) ∧
    -Real.log (244830246199 / 250000000000) ≤ (20895821 / 1000000000) := by
  have h := checkLog_sound (w := (5169753801 / 494830246199)) (n := 12)
    (lo := (1044791 / 50000000)) (hi := (20895821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244830246199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244830246199) = 1/(244830246199 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-20895821 / 1000000000) (-1044791 / 50000000) (Real.log (244830246199 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (20805761 / 1000000000) ≤ -Real.log (39176367399 / 40000000000) ∧
    -Real.log (39176367399 / 40000000000) ≤ (10402881 / 500000000) := by
  have h := checkLog_sound (w := (823632601 / 79176367399)) (n := 12)
    (lo := (20805761 / 1000000000)) (hi := (10402881 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39176367399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39176367399) = 1/(39176367399 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-10402881 / 500000000) (-20805761 / 1000000000) (Real.log (39176367399 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell056

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell057Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell057
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (62492009 / 250000000) ≤ -Real.log (2560 / 3287) ∧
    -Real.log (2560 / 3287) ≤ (249968037 / 1000000000) := by
  have h := checkLog_sound (w := (727 / 5847)) (n := 12)
    (lo := (62492009 / 250000000)) (hi := (249968037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3287 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3287 / 2560) = 1/(2560 / 3287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (62492009 / 250000000) (249968037 / 1000000000) (Real.log (3287 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3287 / 2560) = -Real.log (2560 / 3287) := by
    rw [show ((3287 / 2560) : ℝ) = ((2560 / 3287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (334053289 / 1000000000) ≤ -Real.log (1833 / 2560) ∧
    -Real.log (1833 / 2560) ≤ (33405329 / 100000000) := by
  have h := checkLog_sound (w := (727 / 4393)) (n := 12)
    (lo := (334053289 / 1000000000)) (hi := (33405329 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1833) = 1/(1833 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-33405329 / 100000000) (-334053289 / 1000000000) (Real.log (1833 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (62377897 / 250000000) ≤ -Real.log (5120 / 6571) ∧
    -Real.log (5120 / 6571) ≤ (249511589 / 1000000000) := by
  have h := checkLog_sound (w := (1451 / 11691)) (n := 12)
    (lo := (62377897 / 250000000)) (hi := (249511589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6571 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6571 / 5120) = 1/(5120 / 6571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (62377897 / 250000000) (249511589 / 1000000000) (Real.log (6571 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6571 / 5120) = -Real.log (5120 / 6571) := by
    rw [show ((6571 / 5120) : ℝ) = ((5120 / 6571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (333235293 / 1000000000) ≤ -Real.log (3669 / 5120) ∧
    -Real.log (3669 / 5120) ≤ (166617647 / 500000000) := by
  have h := checkLog_sound (w := (1451 / 8789)) (n := 12)
    (lo := (333235293 / 1000000000)) (hi := (166617647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3669) = 1/(3669 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-166617647 / 500000000) (-333235293 / 1000000000) (Real.log (3669 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (183226147 / 1000000000) ≤ -Real.log (500000 / 600543) ∧
    -Real.log (500000 / 600543) ≤ (45806537 / 250000000) := by
  have h := checkLog_sound (w := (100543 / 1100543)) (n := 12)
    (lo := (183226147 / 1000000000)) (hi := (45806537 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600543 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600543 / 500000) = 1/(500000 / 600543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (183226147 / 1000000000) (45806537 / 250000000) (Real.log (600543 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (600543 / 500000) = -Real.log (500000 / 600543) := by
    rw [show ((600543 / 500000) : ℝ) = ((500000 / 600543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (224501973 / 1000000000) ≤ -Real.log (399457 / 500000) ∧
    -Real.log (399457 / 500000) ≤ (112250987 / 500000000) := by
  have h := checkLog_sound (w := (100543 / 899457)) (n := 12)
    (lo := (224501973 / 1000000000)) (hi := (112250987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 399457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 399457) = 1/(399457 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-112250987 / 500000000) (-224501973 / 1000000000) (Real.log (399457 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (183575769 / 1000000000) ≤ -Real.log (500000 / 600753) ∧
    -Real.log (500000 / 600753) ≤ (18357577 / 100000000) := by
  have h := checkLog_sound (w := (100753 / 1100753)) (n := 12)
    (lo := (183575769 / 1000000000)) (hi := (18357577 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600753 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600753 / 500000) = 1/(500000 / 600753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (183575769 / 1000000000) (18357577 / 100000000) (Real.log (600753 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (600753 / 500000) = -Real.log (500000 / 600753) := by
    rw [show ((600753 / 500000) : ℝ) = ((500000 / 600753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (9001113 / 40000000) ≤ -Real.log (399247 / 500000) ∧
    -Real.log (399247 / 500000) ≤ (112513913 / 500000000) := by
  have h := checkLog_sound (w := (100753 / 899247)) (n := 12)
    (lo := (9001113 / 40000000)) (hi := (112513913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 399247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 399247) = 1/(399247 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-112513913 / 500000000) (-9001113 / 40000000) (Real.log (399247 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (67178463 / 500000000) ≤ -Real.log (1000000 / 1143801) ∧
    -Real.log (1000000 / 1143801) ≤ (134356927 / 1000000000) := by
  have h := checkLog_sound (w := (143801 / 2143801)) (n := 12)
    (lo := (67178463 / 500000000)) (hi := (134356927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1143801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1143801 / 1000000) = 1/(1000000 / 1143801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (67178463 / 500000000) (134356927 / 1000000000) (Real.log (1143801 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1143801 / 1000000) = -Real.log (1000000 / 1143801) := by
    rw [show ((1143801 / 1000000) : ℝ) = ((1000000 / 1143801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (155252453 / 1000000000) ≤ -Real.log (856199 / 1000000) ∧
    -Real.log (856199 / 1000000) ≤ (77626227 / 500000000) := by
  have h := checkLog_sound (w := (143801 / 1856199)) (n := 12)
    (lo := (155252453 / 1000000000)) (hi := (77626227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 856199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 856199) = 1/(856199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-77626227 / 500000000) (-155252453 / 1000000000) (Real.log (856199 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (67312647 / 500000000) ≤ -Real.log (250000 / 286027) ∧
    -Real.log (250000 / 286027) ≤ (26925059 / 200000000) := by
  have h := checkLog_sound (w := (36027 / 536027)) (n := 12)
    (lo := (67312647 / 500000000)) (hi := (26925059 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((286027 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(286027 / 250000) = 1/(250000 / 286027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (67312647 / 500000000) (26925059 / 200000000) (Real.log (286027 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (286027 / 250000) = -Real.log (250000 / 286027) := by
    rw [show ((286027 / 250000) : ℝ) = ((250000 / 286027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (155611079 / 1000000000) ≤ -Real.log (213973 / 250000) ∧
    -Real.log (213973 / 250000) ≤ (3890277 / 25000000) := by
  have h := checkLog_sound (w := (36027 / 463973)) (n := 12)
    (lo := (155611079 / 1000000000)) (hi := (3890277 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 213973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 213973) = 1/(213973 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3890277 / 25000000) (-155611079 / 1000000000) (Real.log (213973 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (291373441 / 500000000) ≤ -Real.log (15625000000 / 27983612701) ∧
    -Real.log (15625000000 / 27983612701) ≤ (582746883 / 1000000000) := by
  have h := checkLog_sound (w := (12358612701 / 43608612701)) (n := 12)
    (lo := (291373441 / 500000000)) (hi := (582746883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27983612701 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27983612701 / 15625000000) = 1/(15625000000 / 27983612701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (291373441 / 500000000) (582746883 / 1000000000) (Real.log (27983612701 / 15625000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (27983612701 / 15625000000) = -Real.log (15625000000 / 27983612701) := by
    rw [show ((27983612701 / 15625000000) : ℝ) = ((15625000000 / 27983612701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (23360853 / 40000000) ≤ -Real.log (500000000000 / 896617566831) ∧
    -Real.log (500000000000 / 896617566831) ≤ (292010663 / 500000000) := by
  have h := checkLog_sound (w := (396617566831 / 1396617566831)) (n := 12)
    (lo := (23360853 / 40000000)) (hi := (292010663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((896617566831 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(896617566831 / 500000000000) = 1/(500000000000 / 896617566831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (23360853 / 40000000) (292010663 / 500000000) (Real.log (896617566831 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (896617566831 / 500000000000) = -Real.log (500000000000 / 896617566831) := by
    rw [show ((896617566831 / 500000000000) : ℝ) = ((500000000000 / 896617566831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (407728121 / 1000000000) ≤ -Real.log (500000000000 / 751699181639) ∧
    -Real.log (500000000000 / 751699181639) ≤ (203864061 / 500000000) := by
  have h := checkLog_sound (w := (251699181639 / 1251699181639)) (n := 12)
    (lo := (407728121 / 1000000000)) (hi := (203864061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((751699181639 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(751699181639 / 500000000000) = 1/(500000000000 / 751699181639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (407728121 / 1000000000) (203864061 / 500000000) (Real.log (751699181639 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (751699181639 / 500000000000) = -Real.log (500000000000 / 751699181639) := by
    rw [show ((751699181639 / 500000000000) : ℝ) = ((500000000000 / 751699181639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (81720719 / 200000000) ≤ -Real.log (500000000000 / 752357563113) ∧
    -Real.log (500000000000 / 752357563113) ≤ (102150899 / 250000000) := by
  have h := checkLog_sound (w := (252357563113 / 1252357563113)) (n := 12)
    (lo := (81720719 / 200000000)) (hi := (102150899 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((752357563113 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(752357563113 / 500000000000) = 1/(500000000000 / 752357563113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (81720719 / 200000000) (102150899 / 250000000) (Real.log (752357563113 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (752357563113 / 500000000000) = -Real.log (500000000000 / 752357563113) := by
    rw [show ((752357563113 / 500000000000) : ℝ) = ((500000000000 / 752357563113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (14480469 / 50000000) ≤ -Real.log (500000000000 / 667952777333) ∧
    -Real.log (500000000000 / 667952777333) ≤ (289609381 / 1000000000) := by
  have h := checkLog_sound (w := (167952777333 / 1167952777333)) (n := 12)
    (lo := (14480469 / 50000000)) (hi := (289609381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667952777333 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667952777333 / 500000000000) = 1/(500000000000 / 667952777333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (14480469 / 50000000) (289609381 / 1000000000) (Real.log (667952777333 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (667952777333 / 500000000000) = -Real.log (500000000000 / 667952777333) := by
    rw [show ((667952777333 / 500000000000) : ℝ) = ((500000000000 / 667952777333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (290236373 / 1000000000) ≤ -Real.log (10000000000 / 13367434209) ∧
    -Real.log (10000000000 / 13367434209) ≤ (145118187 / 500000000) := by
  have h := checkLog_sound (w := (3367434209 / 23367434209)) (n := 12)
    (lo := (290236373 / 1000000000)) (hi := (145118187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13367434209 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13367434209 / 10000000000) = 1/(10000000000 / 13367434209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (290236373 / 1000000000) (145118187 / 500000000) (Real.log (13367434209 / 10000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (13367434209 / 10000000000) = -Real.log (10000000000 / 13367434209) := by
    rw [show ((13367434209 / 10000000000) : ℝ) = ((10000000000 / 13367434209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2623223 / 125000000) ≤ -Real.log (61202055271 / 62500000000) ∧
    -Real.log (61202055271 / 62500000000) ≤ (4197157 / 200000000) := by
  have h := checkLog_sound (w := (1297944729 / 123702055271)) (n := 12)
    (lo := (2623223 / 125000000)) (hi := (4197157 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61202055271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61202055271) = 1/(61202055271 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4197157 / 200000000) (-2623223 / 125000000) (Real.log (61202055271 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (10447763 / 500000000) ≤ -Real.log (979321272399 / 1000000000000) ∧
    -Real.log (979321272399 / 1000000000000) ≤ (20895527 / 1000000000) := by
  have h := checkLog_sound (w := (20678727601 / 1979321272399)) (n := 12)
    (lo := (10447763 / 500000000)) (hi := (20895527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979321272399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979321272399) = 1/(979321272399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-20895527 / 1000000000) (-10447763 / 500000000) (Real.log (979321272399 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell057

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell058Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell058
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (10016971 / 40000000) ≤ -Real.log (5120 / 6577) ∧
    -Real.log (5120 / 6577) ≤ (62606069 / 250000000) := by
  have h := checkLog_sound (w := (1457 / 11697)) (n := 12)
    (lo := (10016971 / 40000000)) (hi := (62606069 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6577 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6577 / 5120) = 1/(5120 / 6577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (10016971 / 40000000) (62606069 / 250000000) (Real.log (6577 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6577 / 5120) = -Real.log (5120 / 6577) := by
    rw [show ((6577 / 5120) : ℝ) = ((5120 / 6577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (66974391 / 200000000) ≤ -Real.log (3663 / 5120) ∧
    -Real.log (3663 / 5120) ≤ (83717989 / 250000000) := by
  have h := checkLog_sound (w := (1457 / 8783)) (n := 12)
    (lo := (66974391 / 200000000)) (hi := (83717989 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3663) = 1/(3663 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-83717989 / 250000000) (-66974391 / 200000000) (Real.log (3663 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (62492009 / 250000000) ≤ -Real.log (2560 / 3287) ∧
    -Real.log (2560 / 3287) ≤ (249968037 / 1000000000) := by
  have h := checkLog_sound (w := (727 / 5847)) (n := 12)
    (lo := (62492009 / 250000000)) (hi := (249968037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3287 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3287 / 2560) = 1/(2560 / 3287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (62492009 / 250000000) (249968037 / 1000000000) (Real.log (3287 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3287 / 2560) = -Real.log (2560 / 3287) := by
    rw [show ((3287 / 2560) : ℝ) = ((2560 / 3287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (334053289 / 1000000000) ≤ -Real.log (1833 / 2560) ∧
    -Real.log (1833 / 2560) ≤ (33405329 / 100000000) := by
  have h := checkLog_sound (w := (727 / 4393)) (n := 12)
    (lo := (334053289 / 1000000000)) (hi := (33405329 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1833) = 1/(1833 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-33405329 / 100000000) (-334053289 / 1000000000) (Real.log (1833 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (183574937 / 1000000000) ≤ -Real.log (200000 / 240301) ∧
    -Real.log (200000 / 240301) ≤ (91787469 / 500000000) := by
  have h := checkLog_sound (w := (40301 / 440301)) (n := 12)
    (lo := (183574937 / 1000000000)) (hi := (91787469 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((240301 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(240301 / 200000) = 1/(200000 / 240301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (183574937 / 1000000000) (91787469 / 500000000) (Real.log (240301 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (240301 / 200000) = -Real.log (200000 / 240301) := by
    rw [show ((240301 / 200000) : ℝ) = ((200000 / 240301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (225026573 / 1000000000) ≤ -Real.log (159699 / 200000) ∧
    -Real.log (159699 / 200000) ≤ (112513287 / 500000000) := by
  have h := checkLog_sound (w := (40301 / 359699)) (n := 12)
    (lo := (225026573 / 1000000000)) (hi := (112513287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 159699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 159699) = 1/(159699 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-112513287 / 500000000) (-225026573 / 1000000000) (Real.log (159699 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (91962219 / 500000000) ≤ -Real.log (40000 / 48077) ∧
    -Real.log (40000 / 48077) ≤ (183924439 / 1000000000) := by
  have h := checkLog_sound (w := (8077 / 88077)) (n := 12)
    (lo := (91962219 / 500000000)) (hi := (183924439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48077 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48077 / 40000) = 1/(40000 / 48077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (91962219 / 500000000) (183924439 / 1000000000) (Real.log (48077 / 40000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (48077 / 40000) = -Real.log (40000 / 48077) := by
    rw [show ((48077 / 40000) : ℝ) = ((40000 / 48077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2255527 / 10000000) ≤ -Real.log (31923 / 40000) ∧
    -Real.log (31923 / 40000) ≤ (225552701 / 1000000000) := by
  have h := checkLog_sound (w := (8077 / 71923)) (n := 12)
    (lo := (2255527 / 10000000)) (hi := (225552701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 31923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 31923) = 1/(31923 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-225552701 / 1000000000) (-2255527 / 10000000) (Real.log (31923 / 40000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (6731221 / 50000000) ≤ -Real.log (1000000 / 1144107) ∧
    -Real.log (1000000 / 1144107) ≤ (134624421 / 1000000000) := by
  have h := checkLog_sound (w := (144107 / 2144107)) (n := 12)
    (lo := (6731221 / 50000000)) (hi := (134624421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1144107 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1144107 / 1000000) = 1/(1000000 / 1144107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (6731221 / 50000000) (134624421 / 1000000000) (Real.log (1144107 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1144107 / 1000000) = -Real.log (1000000 / 1144107) := by
    rw [show ((1144107 / 1000000) : ℝ) = ((1000000 / 1144107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (15560991 / 100000000) ≤ -Real.log (855893 / 1000000) ∧
    -Real.log (855893 / 1000000) ≤ (155609911 / 1000000000) := by
  have h := checkLog_sound (w := (144107 / 1855893)) (n := 12)
    (lo := (15560991 / 100000000)) (hi := (155609911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 855893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 855893) = 1/(855893 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-155609911 / 1000000000) (-15560991 / 100000000) (Real.log (855893 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (26978543 / 200000000) ≤ -Real.log (500000 / 572207) ∧
    -Real.log (500000 / 572207) ≤ (33723179 / 250000000) := by
  have h := checkLog_sound (w := (72207 / 1072207)) (n := 12)
    (lo := (26978543 / 200000000)) (hi := (33723179 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((572207 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(572207 / 500000) = 1/(500000 / 572207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (26978543 / 200000000) (33723179 / 250000000) (Real.log (572207 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (572207 / 500000) = -Real.log (500000 / 572207) := by
    rw [show ((572207 / 500000) : ℝ) = ((500000 / 572207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (19496083 / 125000000) ≤ -Real.log (427793 / 500000) ∧
    -Real.log (427793 / 500000) ≤ (31193733 / 200000000) := by
  have h := checkLog_sound (w := (72207 / 927793)) (n := 12)
    (lo := (19496083 / 125000000)) (hi := (31193733 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 427793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 427793) = 1/(427793 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-31193733 / 200000000) (-19496083 / 125000000) (Real.log (427793 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (23360853 / 40000000) ≤ -Real.log (50000000000 / 89661756683) ∧
    -Real.log (50000000000 / 89661756683) ≤ (292010663 / 500000000) := by
  have h := checkLog_sound (w := (39661756683 / 139661756683)) (n := 12)
    (lo := (23360853 / 40000000)) (hi := (292010663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89661756683 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89661756683 / 50000000000) = 1/(50000000000 / 89661756683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (23360853 / 40000000) (292010663 / 500000000) (Real.log (89661756683 / 50000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (89661756683 / 50000000000) = -Real.log (50000000000 / 89661756683) := by
    rw [show ((89661756683 / 50000000000) : ℝ) = ((50000000000 / 89661756683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (58529623 / 100000000) ≤ -Real.log (250000000000 / 448880698881) ∧
    -Real.log (250000000000 / 448880698881) ≤ (585296231 / 1000000000) := by
  have h := checkLog_sound (w := (198880698881 / 698880698881)) (n := 12)
    (lo := (58529623 / 100000000)) (hi := (585296231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((448880698881 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(448880698881 / 250000000000) = 1/(250000000000 / 448880698881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (58529623 / 100000000) (585296231 / 1000000000) (Real.log (448880698881 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (448880698881 / 250000000000) = -Real.log (250000000000 / 448880698881) := by
    rw [show ((448880698881 / 250000000000) : ℝ) = ((250000000000 / 448880698881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (40860151 / 100000000) ≤ -Real.log (100000000000 / 150471198943) ∧
    -Real.log (100000000000 / 150471198943) ≤ (408601511 / 1000000000) := by
  have h := checkLog_sound (w := (50471198943 / 250471198943)) (n := 12)
    (lo := (40860151 / 100000000)) (hi := (408601511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150471198943 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150471198943 / 100000000000) = 1/(100000000000 / 150471198943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (40860151 / 100000000) (408601511 / 1000000000) (Real.log (150471198943 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (150471198943 / 100000000000) = -Real.log (100000000000 / 150471198943) := by
    rw [show ((150471198943 / 100000000000) : ℝ) = ((100000000000 / 150471198943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (409477139 / 1000000000) ≤ -Real.log (500000000000 / 753015067507) ∧
    -Real.log (500000000000 / 753015067507) ≤ (20473857 / 50000000) := by
  have h := checkLog_sound (w := (253015067507 / 1253015067507)) (n := 12)
    (lo := (409477139 / 1000000000)) (hi := (20473857 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((753015067507 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(753015067507 / 500000000000) = 1/(500000000000 / 753015067507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (409477139 / 1000000000) (20473857 / 50000000) (Real.log (753015067507 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (753015067507 / 500000000000) = -Real.log (500000000000 / 753015067507) := by
    rw [show ((753015067507 / 500000000000) : ℝ) = ((500000000000 / 753015067507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (29023433 / 100000000) ≤ -Real.log (250000000000 / 334185172679) ∧
    -Real.log (250000000000 / 334185172679) ≤ (290234331 / 1000000000) := by
  have h := checkLog_sound (w := (84185172679 / 584185172679)) (n := 12)
    (lo := (29023433 / 100000000)) (hi := (290234331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((334185172679 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(334185172679 / 250000000000) = 1/(250000000000 / 334185172679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (29023433 / 100000000) (290234331 / 1000000000) (Real.log (334185172679 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (334185172679 / 250000000000) = -Real.log (250000000000 / 334185172679) := by
    rw [show ((334185172679 / 250000000000) : ℝ) = ((250000000000 / 334185172679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (14543069 / 50000000) ≤ -Real.log (250000000000 / 334394789069) ∧
    -Real.log (250000000000 / 334394789069) ≤ (290861381 / 1000000000) := by
  have h := checkLog_sound (w := (84394789069 / 584394789069)) (n := 12)
    (lo := (14543069 / 50000000)) (hi := (290861381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((334394789069 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(334394789069 / 250000000000) = 1/(250000000000 / 334394789069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (14543069 / 50000000) (290861381 / 1000000000) (Real.log (334394789069 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (334394789069 / 250000000000) = -Real.log (250000000000 / 334394789069) := by
    rw [show ((334394789069 / 250000000000) : ℝ) = ((250000000000 / 334394789069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (21075949 / 1000000000) ≤ -Real.log (244786149151 / 250000000000) ∧
    -Real.log (244786149151 / 250000000000) ≤ (421519 / 20000000) := by
  have h := checkLog_sound (w := (5213850849 / 494786149151)) (n := 12)
    (lo := (21075949 / 1000000000)) (hi := (421519 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244786149151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244786149151) = 1/(244786149151 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-421519 / 20000000) (-21075949 / 1000000000) (Real.log (244786149151 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (2098549 / 100000000) ≤ -Real.log (979233172551 / 1000000000000) ∧
    -Real.log (979233172551 / 1000000000000) ≤ (20985491 / 1000000000) := by
  have h := checkLog_sound (w := (20766827449 / 1979233172551)) (n := 12)
    (lo := (2098549 / 100000000)) (hi := (20985491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979233172551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979233172551) = 1/(979233172551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-20985491 / 1000000000) (-2098549 / 100000000) (Real.log (979233172551 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell058

end


