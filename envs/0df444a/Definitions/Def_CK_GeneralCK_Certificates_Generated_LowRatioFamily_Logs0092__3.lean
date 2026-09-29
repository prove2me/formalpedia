-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0092__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0092__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T06:06:51.46991+00:00
-- url     : https://prove2.me/theorems/fe280e31-e352-4218-adde-f8f2f51610fc
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0092 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0093, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0092 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0093, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0094)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0092 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0093, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0094)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0092 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0093, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0094) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0092 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0093, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0094).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0092 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5888_neg : (193907301 / 1000000000) ≤ -Real.log (250000000000 / 303495935679) ∧
    -Real.log (250000000000 / 303495935679) ≤ (96953651 / 500000000) := by
  have h := checkLog_sound (w := (53495935679 / 553495935679)) (n := 12)
    (lo := (193907301 / 1000000000)) (hi := (96953651 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303495935679 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303495935679 / 250000000000) = 1/(250000000000 / 303495935679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5888 : Bounds (193907301 / 1000000000) (96953651 / 500000000) (Real.log (303495935679 / 250000000000)) := by
  have h := reflection_log_5888_neg
  have he : Real.log (303495935679 / 250000000000) = -Real.log (250000000000 / 303495935679) := by
    rw [show ((303495935679 / 250000000000) : ℝ) = ((250000000000 / 303495935679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5889_neg : (38879579 / 200000000) ≤ -Real.log (500000000000 / 607289731217) ∧
    -Real.log (500000000000 / 607289731217) ≤ (24299737 / 125000000) := by
  have h := checkLog_sound (w := (107289731217 / 1107289731217)) (n := 12)
    (lo := (38879579 / 200000000)) (hi := (24299737 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607289731217 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607289731217 / 500000000000) = 1/(500000000000 / 607289731217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5889 : Bounds (38879579 / 200000000) (24299737 / 125000000) (Real.log (607289731217 / 500000000000)) := by
  have h := reflection_log_5889_neg
  have he : Real.log (607289731217 / 500000000000) = -Real.log (500000000000 / 607289731217) := by
    rw [show ((607289731217 / 500000000000) : ℝ) = ((500000000000 / 607289731217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5890_neg : (77848223 / 200000000) ≤ -Real.log (500000000000 / 737930180737) ∧
    -Real.log (500000000000 / 737930180737) ≤ (97310279 / 250000000) := by
  have h := checkLog_sound (w := (237930180737 / 1237930180737)) (n := 12)
    (lo := (77848223 / 200000000)) (hi := (97310279 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737930180737 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(737930180737 / 500000000000) = 1/(500000000000 / 737930180737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5890 : Bounds (77848223 / 200000000) (97310279 / 250000000) (Real.log (737930180737 / 500000000000)) := by
  have h := reflection_log_5890_neg
  have he : Real.log (737930180737 / 500000000000) = -Real.log (500000000000 / 737930180737) := by
    rw [show ((737930180737 / 500000000000) : ℝ) = ((500000000000 / 737930180737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5891_neg : (389448791 / 1000000000) ≤ -Real.log (20000000000 / 29523337873) ∧
    -Real.log (20000000000 / 29523337873) ≤ (48681099 / 125000000) := by
  have h := checkLog_sound (w := (9523337873 / 49523337873)) (n := 12)
    (lo := (389448791 / 1000000000)) (hi := (48681099 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29523337873 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29523337873 / 20000000000) = 1/(20000000000 / 29523337873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5891 : Bounds (389448791 / 1000000000) (48681099 / 125000000) (Real.log (29523337873 / 20000000000)) := by
  have h := reflection_log_5891_neg
  have he : Real.log (29523337873 / 20000000000) = -Real.log (20000000000 / 29523337873) := by
    rw [show ((29523337873 / 20000000000) : ℝ) = ((20000000000 / 29523337873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5892_neg : (87984041 / 500000000) ≤ -Real.log (2500 / 2981) ∧
    -Real.log (2500 / 2981) ≤ (175968083 / 1000000000) := by
  have h := checkLog_sound (w := (481 / 5481)) (n := 12)
    (lo := (87984041 / 500000000)) (hi := (175968083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2981 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2981 / 2500) = 1/(2500 / 2981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5892 : Bounds (87984041 / 500000000) (175968083 / 1000000000) (Real.log (2981 / 2500)) := by
  have h := reflection_log_5892_neg
  have he : Real.log (2981 / 2500) = -Real.log (2500 / 2981) := by
    rw [show ((2981 / 2500) : ℝ) = ((2500 / 2981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5893_neg : (26711049 / 125000000) ≤ -Real.log (2019 / 2500) ∧
    -Real.log (2019 / 2500) ≤ (213688393 / 1000000000) := by
  have h := checkLog_sound (w := (481 / 4519)) (n := 12)
    (lo := (26711049 / 125000000)) (hi := (213688393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2019) = 1/(2019 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5893 : Bounds (-213688393 / 1000000000) (-26711049 / 125000000) (Real.log (2019 / 2500)) := by
  have h := reflection_log_5893_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5894_neg : (192381 / 1000000000) ≤ -Real.log (2500000 / 2500481) ∧
    -Real.log (2500000 / 2500481) ≤ (96191 / 500000000) := by
  have h := checkLog_sound (w := (481 / 5000481)) (n := 12)
    (lo := (192381 / 1000000000)) (hi := (96191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500481 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500481 / 2500000) = 1/(2500000 / 2500481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5894 : Bounds (192381 / 1000000000) (96191 / 500000000) (Real.log (2500481 / 2500000)) := by
  have h := reflection_log_5894_neg
  have he : Real.log (2500481 / 2500000) = -Real.log (2500000 / 2500481) := by
    rw [show ((2500481 / 2500000) : ℝ) = ((2500000 / 2500481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5895_neg : (96209 / 500000000) ≤ -Real.log (2499519 / 2500000) ∧
    -Real.log (2499519 / 2500000) ≤ (192419 / 1000000000) := by
  have h := checkLog_sound (w := (481 / 4999519)) (n := 12)
    (lo := (96209 / 500000000)) (hi := (192419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499519) = 1/(2499519 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5895 : Bounds (-192419 / 1000000000) (-96209 / 500000000) (Real.log (2499519 / 2500000)) := by
  have h := reflection_log_5895_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5896_neg : (46153747 / 500000000) ≤ -Real.log (500000 / 548351) ∧
    -Real.log (500000 / 548351) ≤ (18461499 / 200000000) := by
  have h := checkLog_sound (w := (48351 / 1048351)) (n := 12)
    (lo := (46153747 / 500000000)) (hi := (18461499 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548351 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548351 / 500000) = 1/(500000 / 548351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5896 : Bounds (46153747 / 500000000) (18461499 / 200000000) (Real.log (548351 / 500000)) := by
  have h := reflection_log_5896_neg
  have he : Real.log (548351 / 500000) = -Real.log (500000 / 548351) := by
    rw [show ((548351 / 500000) : ℝ) = ((500000 / 548351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5897_neg : (6356423 / 62500000) ≤ -Real.log (451649 / 500000) ∧
    -Real.log (451649 / 500000) ≤ (101702769 / 1000000000) := by
  have h := checkLog_sound (w := (48351 / 951649)) (n := 12)
    (lo := (6356423 / 62500000)) (hi := (101702769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451649) = 1/(451649 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5897 : Bounds (-101702769 / 1000000000) (-6356423 / 62500000) (Real.log (451649 / 500000)) := by
  have h := reflection_log_5897_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5898_neg : (92529043 / 1000000000) ≤ -Real.log (200000 / 219389) ∧
    -Real.log (200000 / 219389) ≤ (23132261 / 250000000) := by
  have h := checkLog_sound (w := (19389 / 419389)) (n := 12)
    (lo := (92529043 / 1000000000)) (hi := (23132261 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219389 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219389 / 200000) = 1/(200000 / 219389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5898 : Bounds (92529043 / 1000000000) (23132261 / 250000000) (Real.log (219389 / 200000)) := by
  have h := reflection_log_5898_neg
  have he : Real.log (219389 / 200000) = -Real.log (200000 / 219389) := by
    rw [show ((219389 / 200000) : ℝ) = ((200000 / 219389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5899_neg : (101971819 / 1000000000) ≤ -Real.log (180611 / 200000) ∧
    -Real.log (180611 / 200000) ≤ (5098591 / 50000000) := by
  have h := checkLog_sound (w := (19389 / 380611)) (n := 12)
    (lo := (101971819 / 1000000000)) (hi := (5098591 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180611) = 1/(180611 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5899 : Bounds (-5098591 / 50000000) (-101971819 / 1000000000) (Real.log (180611 / 200000)) := by
  have h := reflection_log_5899_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5900_neg : (1180347 / 125000000) ≤ -Real.log (39624066679 / 40000000000) ∧
    -Real.log (39624066679 / 40000000000) ≤ (9442777 / 1000000000) := by
  have h := checkLog_sound (w := (375933321 / 79624066679)) (n := 12)
    (lo := (1180347 / 125000000)) (hi := (9442777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39624066679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39624066679) = 1/(39624066679 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5900 : Bounds (-9442777 / 1000000000) (-1180347 / 125000000) (Real.log (39624066679 / 40000000000)) := by
  have h := reflection_log_5900_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5901_neg : (4697637 / 500000000) ≤ -Real.log (247662180799 / 250000000000) ∧
    -Real.log (247662180799 / 250000000000) ≤ (375811 / 40000000) := by
  have h := checkLog_sound (w := (2337819201 / 497662180799)) (n := 12)
    (lo := (4697637 / 500000000)) (hi := (375811 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247662180799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247662180799) = 1/(247662180799 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5901 : Bounds (-375811 / 40000000) (-4697637 / 500000000) (Real.log (247662180799 / 250000000000)) := by
  have h := reflection_log_5901_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5902_neg : (194010263 / 1000000000) ≤ -Real.log (125000000000 / 151763592967) ∧
    -Real.log (125000000000 / 151763592967) ≤ (24251283 / 125000000) := by
  have h := checkLog_sound (w := (26763592967 / 276763592967)) (n := 12)
    (lo := (194010263 / 1000000000)) (hi := (24251283 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151763592967 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151763592967 / 125000000000) = 1/(125000000000 / 151763592967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5902 : Bounds (194010263 / 1000000000) (24251283 / 125000000) (Real.log (151763592967 / 125000000000)) := by
  have h := reflection_log_5902_neg
  have he : Real.log (151763592967 / 125000000000) = -Real.log (125000000000 / 151763592967) := by
    rw [show ((151763592967 / 125000000000) : ℝ) = ((125000000000 / 151763592967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5903_neg : (97250431 / 500000000) ≤ -Real.log (250000000000 / 303676132683) ∧
    -Real.log (250000000000 / 303676132683) ≤ (194500863 / 1000000000) := by
  have h := checkLog_sound (w := (53676132683 / 553676132683)) (n := 12)
    (lo := (97250431 / 500000000)) (hi := (194500863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303676132683 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303676132683 / 250000000000) = 1/(250000000000 / 303676132683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5903 : Bounds (97250431 / 500000000) (194500863 / 1000000000) (Real.log (303676132683 / 250000000000)) := by
  have h := reflection_log_5903_neg
  have he : Real.log (303676132683 / 250000000000) = -Real.log (250000000000 / 303676132683) := by
    rw [show ((303676132683 / 250000000000) : ℝ) = ((250000000000 / 303676132683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5904_neg : (389448791 / 1000000000) ≤ -Real.log (62500000000 / 92260430853) ∧
    -Real.log (62500000000 / 92260430853) ≤ (48681099 / 125000000) := by
  have h := checkLog_sound (w := (29760430853 / 154760430853)) (n := 12)
    (lo := (389448791 / 1000000000)) (hi := (48681099 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92260430853 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92260430853 / 62500000000) = 1/(62500000000 / 92260430853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5904 : Bounds (389448791 / 1000000000) (48681099 / 125000000) (Real.log (92260430853 / 62500000000)) := by
  have h := reflection_log_5904_neg
  have he : Real.log (92260430853 / 62500000000) = -Real.log (62500000000 / 92260430853) := by
    rw [show ((92260430853 / 62500000000) : ℝ) = ((62500000000 / 92260430853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5905_neg : (15586259 / 40000000) ≤ -Real.log (500000000000 / 738236750867) ∧
    -Real.log (500000000000 / 738236750867) ≤ (97414119 / 250000000) := by
  have h := checkLog_sound (w := (238236750867 / 1238236750867)) (n := 12)
    (lo := (15586259 / 40000000)) (hi := (97414119 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((738236750867 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(738236750867 / 500000000000) = 1/(500000000000 / 738236750867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5905 : Bounds (15586259 / 40000000) (97414119 / 250000000) (Real.log (738236750867 / 500000000000)) := by
  have h := reflection_log_5905_neg
  have he : Real.log (738236750867 / 500000000000) = -Real.log (500000000000 / 738236750867) := by
    rw [show ((738236750867 / 500000000000) : ℝ) = ((500000000000 / 738236750867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5906_neg : (176051943 / 1000000000) ≤ -Real.log (400 / 477) ∧
    -Real.log (400 / 477) ≤ (22006493 / 125000000) := by
  have h := checkLog_sound (w := (77 / 877)) (n := 12)
    (lo := (176051943 / 1000000000)) (hi := (22006493 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((477 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(477 / 400) = 1/(400 / 477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5906 : Bounds (176051943 / 1000000000) (22006493 / 125000000) (Real.log (477 / 400)) := by
  have h := reflection_log_5906_neg
  have he : Real.log (477 / 400) = -Real.log (400 / 477) := by
    rw [show ((477 / 400) : ℝ) = ((400 / 477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5907_neg : (213812223 / 1000000000) ≤ -Real.log (323 / 400) ∧
    -Real.log (323 / 400) ≤ (417602 / 1953125) := by
  have h := checkLog_sound (w := (77 / 723)) (n := 12)
    (lo := (213812223 / 1000000000)) (hi := (417602 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 323) = 1/(323 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5907 : Bounds (-417602 / 1953125) (-213812223 / 1000000000) (Real.log (323 / 400)) := by
  have h := reflection_log_5907_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5908_neg : (192481 / 1000000000) ≤ -Real.log (400000 / 400077) ∧
    -Real.log (400000 / 400077) ≤ (96241 / 500000000) := by
  have h := checkLog_sound (w := (77 / 800077)) (n := 12)
    (lo := (192481 / 1000000000)) (hi := (96241 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400077 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400077 / 400000) = 1/(400000 / 400077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5908 : Bounds (192481 / 1000000000) (96241 / 500000000) (Real.log (400077 / 400000)) := by
  have h := reflection_log_5908_neg
  have he : Real.log (400077 / 400000) = -Real.log (400000 / 400077) := by
    rw [show ((400077 / 400000) : ℝ) = ((400000 / 400077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5909_neg : (96259 / 500000000) ≤ -Real.log (399923 / 400000) ∧
    -Real.log (399923 / 400000) ≤ (192519 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 799923)) (n := 12)
    (lo := (96259 / 500000000)) (hi := (192519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399923) = 1/(399923 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5909 : Bounds (-192519 / 1000000000) (-96259 / 500000000) (Real.log (399923 / 400000)) := by
  have h := reflection_log_5909_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5910_neg : (23088499 / 250000000) ≤ -Real.log (1000000 / 1096753) ∧
    -Real.log (1000000 / 1096753) ≤ (92353997 / 1000000000) := by
  have h := checkLog_sound (w := (96753 / 2096753)) (n := 12)
    (lo := (23088499 / 250000000)) (hi := (92353997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096753 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096753 / 1000000) = 1/(1000000 / 1096753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5910 : Bounds (23088499 / 250000000) (92353997 / 1000000000) (Real.log (1096753 / 1000000)) := by
  have h := reflection_log_5910_neg
  have he : Real.log (1096753 / 1000000) = -Real.log (1000000 / 1096753) := by
    rw [show ((1096753 / 1000000) : ℝ) = ((1000000 / 1096753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5911_neg : (10175923 / 100000000) ≤ -Real.log (903247 / 1000000) ∧
    -Real.log (903247 / 1000000) ≤ (101759231 / 1000000000) := by
  have h := checkLog_sound (w := (96753 / 1903247)) (n := 12)
    (lo := (10175923 / 100000000)) (hi := (101759231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903247) = 1/(903247 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5911 : Bounds (-101759231 / 1000000000) (-10175923 / 100000000) (Real.log (903247 / 1000000)) := by
  have h := reflection_log_5911_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5912_neg : (46287767 / 500000000) ≤ -Real.log (250000 / 274249) ∧
    -Real.log (250000 / 274249) ≤ (18515107 / 200000000) := by
  have h := checkLog_sound (w := (24249 / 524249)) (n := 12)
    (lo := (46287767 / 500000000)) (hi := (18515107 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274249 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274249 / 250000) = 1/(250000 / 274249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5912 : Bounds (46287767 / 500000000) (18515107 / 200000000) (Real.log (274249 / 250000)) := by
  have h := reflection_log_5912_neg
  have he : Real.log (274249 / 250000) = -Real.log (250000 / 274249) := by
    rw [show ((274249 / 250000) : ℝ) = ((250000 / 274249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5913_neg : (20405659 / 200000000) ≤ -Real.log (225751 / 250000) ∧
    -Real.log (225751 / 250000) ≤ (12753537 / 125000000) := by
  have h := checkLog_sound (w := (24249 / 475751)) (n := 12)
    (lo := (20405659 / 200000000)) (hi := (12753537 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225751) = 1/(225751 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5913 : Bounds (-12753537 / 125000000) (-20405659 / 200000000) (Real.log (225751 / 250000)) := by
  have h := reflection_log_5913_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5914_neg : (236319 / 25000000) ≤ -Real.log (61911985999 / 62500000000) ∧
    -Real.log (61911985999 / 62500000000) ≤ (9452761 / 1000000000) := by
  have h := checkLog_sound (w := (588014001 / 124411985999)) (n := 12)
    (lo := (236319 / 25000000)) (hi := (9452761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61911985999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61911985999) = 1/(61911985999 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5914 : Bounds (-9452761 / 1000000000) (-236319 / 25000000) (Real.log (61911985999 / 62500000000)) := by
  have h := reflection_log_5914_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5915_neg : (9405233 / 1000000000) ≤ -Real.log (990638856991 / 1000000000000) ∧
    -Real.log (990638856991 / 1000000000000) ≤ (4702617 / 500000000) := by
  have h := checkLog_sound (w := (9361143009 / 1990638856991)) (n := 12)
    (lo := (9405233 / 1000000000)) (hi := (4702617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990638856991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990638856991) = 1/(990638856991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5915 : Bounds (-4702617 / 500000000) (-9405233 / 1000000000) (Real.log (990638856991 / 1000000000000)) := by
  have h := reflection_log_5915_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5916_neg : (97056613 / 500000000) ≤ -Real.log (125000000000 / 151779219859) ∧
    -Real.log (125000000000 / 151779219859) ≤ (194113227 / 1000000000) := by
  have h := checkLog_sound (w := (26779219859 / 276779219859)) (n := 12)
    (lo := (97056613 / 500000000)) (hi := (194113227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151779219859 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151779219859 / 125000000000) = 1/(125000000000 / 151779219859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5916 : Bounds (97056613 / 500000000) (194113227 / 1000000000) (Real.log (151779219859 / 125000000000)) := by
  have h := reflection_log_5916_neg
  have he : Real.log (151779219859 / 125000000000) = -Real.log (125000000000 / 151779219859) := by
    rw [show ((151779219859 / 125000000000) : ℝ) = ((125000000000 / 151779219859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5917_neg : (19460383 / 100000000) ≤ -Real.log (500000000000 / 607414806579) ∧
    -Real.log (500000000000 / 607414806579) ≤ (194603831 / 1000000000) := by
  have h := checkLog_sound (w := (107414806579 / 1107414806579)) (n := 12)
    (lo := (19460383 / 100000000)) (hi := (194603831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607414806579 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607414806579 / 500000000000) = 1/(500000000000 / 607414806579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5917 : Bounds (19460383 / 100000000) (194603831 / 1000000000) (Real.log (607414806579 / 500000000000)) := by
  have h := reflection_log_5917_neg
  have he : Real.log (607414806579 / 500000000000) = -Real.log (500000000000 / 607414806579) := by
    rw [show ((607414806579 / 500000000000) : ℝ) = ((500000000000 / 607414806579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5918_neg : (15586259 / 40000000) ≤ -Real.log (250000000000 / 369118375433) ∧
    -Real.log (250000000000 / 369118375433) ≤ (97414119 / 250000000) := by
  have h := checkLog_sound (w := (119118375433 / 619118375433)) (n := 12)
    (lo := (15586259 / 40000000)) (hi := (97414119 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369118375433 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369118375433 / 250000000000) = 1/(250000000000 / 369118375433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5918 : Bounds (15586259 / 40000000) (97414119 / 250000000) (Real.log (369118375433 / 250000000000)) := by
  have h := reflection_log_5918_neg
  have he : Real.log (369118375433 / 250000000000) = -Real.log (250000000000 / 369118375433) := by
    rw [show ((369118375433 / 250000000000) : ℝ) = ((250000000000 / 369118375433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5919_neg : (389864167 / 1000000000) ≤ -Real.log (6250000000 / 9229876161) ∧
    -Real.log (6250000000 / 9229876161) ≤ (48733021 / 125000000) := by
  have h := checkLog_sound (w := (2979876161 / 15479876161)) (n := 12)
    (lo := (389864167 / 1000000000)) (hi := (48733021 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9229876161 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9229876161 / 6250000000) = 1/(6250000000 / 9229876161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5919 : Bounds (389864167 / 1000000000) (48733021 / 125000000) (Real.log (9229876161 / 6250000000)) := by
  have h := reflection_log_5919_neg
  have he : Real.log (9229876161 / 6250000000) = -Real.log (6250000000 / 9229876161) := by
    rw [show ((9229876161 / 6250000000) : ℝ) = ((6250000000 / 9229876161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5920_neg : (176135797 / 1000000000) ≤ -Real.log (5000 / 5963) ∧
    -Real.log (5000 / 5963) ≤ (88067899 / 500000000) := by
  have h := checkLog_sound (w := (963 / 10963)) (n := 12)
    (lo := (176135797 / 1000000000)) (hi := (88067899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5963 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5963 / 5000) = 1/(5000 / 5963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5920 : Bounds (176135797 / 1000000000) (88067899 / 500000000) (Real.log (5963 / 5000)) := by
  have h := reflection_log_5920_neg
  have he : Real.log (5963 / 5000) = -Real.log (5000 / 5963) := by
    rw [show ((5963 / 5000) : ℝ) = ((5000 / 5963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5921_neg : (21393607 / 100000000) ≤ -Real.log (4037 / 5000) ∧
    -Real.log (4037 / 5000) ≤ (213936071 / 1000000000) := by
  have h := checkLog_sound (w := (963 / 9037)) (n := 12)
    (lo := (21393607 / 100000000)) (hi := (213936071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4037) = 1/(4037 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5921 : Bounds (-213936071 / 1000000000) (-21393607 / 100000000) (Real.log (4037 / 5000)) := by
  have h := reflection_log_5921_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5922_neg : (192581 / 1000000000) ≤ -Real.log (5000000 / 5000963) ∧
    -Real.log (5000000 / 5000963) ≤ (96291 / 500000000) := by
  have h := checkLog_sound (w := (963 / 10000963)) (n := 12)
    (lo := (192581 / 1000000000)) (hi := (96291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000963 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000963 / 5000000) = 1/(5000000 / 5000963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5922 : Bounds (192581 / 1000000000) (96291 / 500000000) (Real.log (5000963 / 5000000)) := by
  have h := reflection_log_5922_neg
  have he : Real.log (5000963 / 5000000) = -Real.log (5000000 / 5000963) := by
    rw [show ((5000963 / 5000000) : ℝ) = ((5000000 / 5000963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5923_neg : (96309 / 500000000) ≤ -Real.log (4999037 / 5000000) ∧
    -Real.log (4999037 / 5000000) ≤ (192619 / 1000000000) := by
  have h := checkLog_sound (w := (963 / 9999037)) (n := 12)
    (lo := (96309 / 500000000)) (hi := (192619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999037) = 1/(4999037 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5923 : Bounds (-192619 / 1000000000) (-96309 / 500000000) (Real.log (4999037 / 5000000)) := by
  have h := reflection_log_5923_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5924_neg : (5775031 / 62500000) ≤ -Real.log (250000 / 274201) ∧
    -Real.log (250000 / 274201) ≤ (92400497 / 1000000000) := by
  have h := checkLog_sound (w := (24201 / 524201)) (n := 12)
    (lo := (5775031 / 62500000)) (hi := (92400497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274201 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274201 / 250000) = 1/(250000 / 274201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5924 : Bounds (5775031 / 62500000) (92400497 / 1000000000) (Real.log (274201 / 250000)) := by
  have h := reflection_log_5924_neg
  have he : Real.log (274201 / 250000) = -Real.log (250000 / 274201) := by
    rw [show ((274201 / 250000) : ℝ) = ((250000 / 274201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5925_neg : (50907847 / 500000000) ≤ -Real.log (225799 / 250000) ∧
    -Real.log (225799 / 250000) ≤ (20363139 / 200000000) := by
  have h := checkLog_sound (w := (24201 / 475799)) (n := 12)
    (lo := (50907847 / 500000000)) (hi := (20363139 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225799) = 1/(225799 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5925 : Bounds (-20363139 / 200000000) (-50907847 / 500000000) (Real.log (225799 / 250000)) := by
  have h := reflection_log_5925_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5926_neg : (11577753 / 125000000) ≤ -Real.log (1000000 / 1097047) ∧
    -Real.log (1000000 / 1097047) ≤ (3704881 / 40000000) := by
  have h := checkLog_sound (w := (97047 / 2097047)) (n := 12)
    (lo := (11577753 / 125000000)) (hi := (3704881 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097047 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097047 / 1000000) = 1/(1000000 / 1097047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5926 : Bounds (11577753 / 125000000) (3704881 / 40000000) (Real.log (1097047 / 1000000)) := by
  have h := reflection_log_5926_neg
  have he : Real.log (1097047 / 1000000) = -Real.log (1000000 / 1097047) := by
    rw [show ((1097047 / 1000000) : ℝ) = ((1000000 / 1097047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5927_neg : (4083391 / 40000000) ≤ -Real.log (902953 / 1000000) ∧
    -Real.log (902953 / 1000000) ≤ (12760597 / 125000000) := by
  have h := checkLog_sound (w := (97047 / 1902953)) (n := 12)
    (lo := (4083391 / 40000000)) (hi := (12760597 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902953) = 1/(902953 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5927 : Bounds (-12760597 / 125000000) (-4083391 / 40000000) (Real.log (902953 / 1000000)) := by
  have h := reflection_log_5927_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5928_neg : (9462751 / 1000000000) ≤ -Real.log (990581879791 / 1000000000000) ∧
    -Real.log (990581879791 / 1000000000000) ≤ (295711 / 31250000) := by
  have h := checkLog_sound (w := (9418120209 / 1990581879791)) (n := 12)
    (lo := (9462751 / 1000000000)) (hi := (295711 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990581879791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990581879791) = 1/(990581879791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5928 : Bounds (-295711 / 31250000) (-9462751 / 1000000000) (Real.log (990581879791 / 1000000000000)) := by
  have h := reflection_log_5928_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5929_neg : (4707599 / 500000000) ≤ -Real.log (61914311599 / 62500000000) ∧
    -Real.log (61914311599 / 62500000000) ≤ (9415199 / 1000000000) := by
  have h := checkLog_sound (w := (585688401 / 124414311599)) (n := 12)
    (lo := (4707599 / 500000000)) (hi := (9415199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61914311599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61914311599) = 1/(61914311599 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5929 : Bounds (-9415199 / 1000000000) (-4707599 / 500000000) (Real.log (61914311599 / 62500000000)) := by
  have h := reflection_log_5929_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5930_neg : (194216191 / 1000000000) ≤ -Real.log (250000000000 / 303589697031) ∧
    -Real.log (250000000000 / 303589697031) ≤ (758657 / 3906250) := by
  have h := checkLog_sound (w := (53589697031 / 553589697031)) (n := 12)
    (lo := (194216191 / 1000000000)) (hi := (758657 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303589697031 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303589697031 / 250000000000) = 1/(250000000000 / 303589697031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5930 : Bounds (194216191 / 1000000000) (758657 / 3906250) (Real.log (303589697031 / 250000000000)) := by
  have h := reflection_log_5930_neg
  have he : Real.log (303589697031 / 250000000000) = -Real.log (250000000000 / 303589697031) := by
    rw [show ((303589697031 / 250000000000) : ℝ) = ((250000000000 / 303589697031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5931_neg : (486767 / 2500000) ≤ -Real.log (500000000000 / 607477354857) ∧
    -Real.log (500000000000 / 607477354857) ≤ (194706801 / 1000000000) := by
  have h := checkLog_sound (w := (107477354857 / 1107477354857)) (n := 12)
    (lo := (486767 / 2500000)) (hi := (194706801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607477354857 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607477354857 / 500000000000) = 1/(500000000000 / 607477354857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5931 : Bounds (486767 / 2500000) (194706801 / 1000000000) (Real.log (607477354857 / 500000000000)) := by
  have h := reflection_log_5931_neg
  have he : Real.log (607477354857 / 500000000000) = -Real.log (500000000000 / 607477354857) := by
    rw [show ((607477354857 / 500000000000) : ℝ) = ((500000000000 / 607477354857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5932_neg : (389864167 / 1000000000) ≤ -Real.log (500000000000 / 738390092879) ∧
    -Real.log (500000000000 / 738390092879) ≤ (48733021 / 125000000) := by
  have h := checkLog_sound (w := (238390092879 / 1238390092879)) (n := 12)
    (lo := (389864167 / 1000000000)) (hi := (48733021 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((738390092879 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(738390092879 / 500000000000) = 1/(500000000000 / 738390092879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5932 : Bounds (389864167 / 1000000000) (48733021 / 125000000) (Real.log (738390092879 / 500000000000)) := by
  have h := reflection_log_5932_neg
  have he : Real.log (738390092879 / 500000000000) = -Real.log (500000000000 / 738390092879) := by
    rw [show ((738390092879 / 500000000000) : ℝ) = ((500000000000 / 738390092879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5933_neg : (97517967 / 250000000) ≤ -Real.log (125000000000 / 184635868219) ∧
    -Real.log (125000000000 / 184635868219) ≤ (390071869 / 1000000000) := by
  have h := checkLog_sound (w := (59635868219 / 309635868219)) (n := 12)
    (lo := (97517967 / 250000000)) (hi := (390071869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184635868219 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184635868219 / 125000000000) = 1/(125000000000 / 184635868219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5933 : Bounds (97517967 / 250000000) (390071869 / 1000000000) (Real.log (184635868219 / 125000000000)) := by
  have h := reflection_log_5933_neg
  have he : Real.log (184635868219 / 125000000000) = -Real.log (125000000000 / 184635868219) := by
    rw [show ((184635868219 / 125000000000) : ℝ) = ((125000000000 / 184635868219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5934_neg : (44054911 / 250000000) ≤ -Real.log (10000 / 11927) ∧
    -Real.log (10000 / 11927) ≤ (35243929 / 200000000) := by
  have h := checkLog_sound (w := (1927 / 21927)) (n := 12)
    (lo := (44054911 / 250000000)) (hi := (35243929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11927 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11927 / 10000) = 1/(10000 / 11927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5934 : Bounds (44054911 / 250000000) (35243929 / 200000000) (Real.log (11927 / 10000)) := by
  have h := reflection_log_5934_neg
  have he : Real.log (11927 / 10000) = -Real.log (10000 / 11927) := by
    rw [show ((11927 / 10000) : ℝ) = ((10000 / 11927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5935_neg : (53514983 / 250000000) ≤ -Real.log (8073 / 10000) ∧
    -Real.log (8073 / 10000) ≤ (214059933 / 1000000000) := by
  have h := checkLog_sound (w := (1927 / 18073)) (n := 12)
    (lo := (53514983 / 250000000)) (hi := (214059933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8073) = 1/(8073 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5935 : Bounds (-214059933 / 1000000000) (-53514983 / 250000000) (Real.log (8073 / 10000)) := by
  have h := reflection_log_5935_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5936_neg : (192681 / 1000000000) ≤ -Real.log (10000000 / 10001927) ∧
    -Real.log (10000000 / 10001927) ≤ (96341 / 500000000) := by
  have h := checkLog_sound (w := (1927 / 20001927)) (n := 12)
    (lo := (192681 / 1000000000)) (hi := (96341 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001927 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001927 / 10000000) = 1/(10000000 / 10001927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5936 : Bounds (192681 / 1000000000) (96341 / 500000000) (Real.log (10001927 / 10000000)) := by
  have h := reflection_log_5936_neg
  have he : Real.log (10001927 / 10000000) = -Real.log (10000000 / 10001927) := by
    rw [show ((10001927 / 10000000) : ℝ) = ((10000000 / 10001927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5937_neg : (96359 / 500000000) ≤ -Real.log (9998073 / 10000000) ∧
    -Real.log (9998073 / 10000000) ≤ (192719 / 1000000000) := by
  have h := checkLog_sound (w := (1927 / 19998073)) (n := 12)
    (lo := (96359 / 500000000)) (hi := (192719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998073) = 1/(9998073 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5937 : Bounds (-192719 / 1000000000) (-96359 / 500000000) (Real.log (9998073 / 10000000)) := by
  have h := reflection_log_5937_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5938_neg : (92446993 / 1000000000) ≤ -Real.log (200000 / 219371) ∧
    -Real.log (200000 / 219371) ≤ (46223497 / 500000000) := by
  have h := checkLog_sound (w := (19371 / 419371)) (n := 12)
    (lo := (92446993 / 1000000000)) (hi := (46223497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219371 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219371 / 200000) = 1/(200000 / 219371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5938 : Bounds (92446993 / 1000000000) (46223497 / 500000000) (Real.log (219371 / 200000)) := by
  have h := reflection_log_5938_neg
  have he : Real.log (219371 / 200000) = -Real.log (200000 / 219371) := by
    rw [show ((219371 / 200000) : ℝ) = ((200000 / 219371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5939_neg : (50936081 / 500000000) ≤ -Real.log (180629 / 200000) ∧
    -Real.log (180629 / 200000) ≤ (101872163 / 1000000000) := by
  have h := checkLog_sound (w := (19371 / 380629)) (n := 12)
    (lo := (50936081 / 500000000)) (hi := (101872163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180629) = 1/(180629 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5939 : Bounds (-101872163 / 1000000000) (-50936081 / 500000000) (Real.log (180629 / 200000)) := by
  have h := reflection_log_5939_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5940_neg : (92669423 / 1000000000) ≤ -Real.log (1000000 / 1097099) ∧
    -Real.log (1000000 / 1097099) ≤ (5791839 / 62500000) := by
  have h := checkLog_sound (w := (97099 / 2097099)) (n := 12)
    (lo := (92669423 / 1000000000)) (hi := (5791839 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097099 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097099 / 1000000) = 1/(1000000 / 1097099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5940 : Bounds (92669423 / 1000000000) (5791839 / 62500000) (Real.log (1097099 / 1000000)) := by
  have h := reflection_log_5940_neg
  have he : Real.log (1097099 / 1000000) = -Real.log (1000000 / 1097099) := by
    rw [show ((1097099 / 1000000) : ℝ) = ((1000000 / 1097099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5941_neg : (51071183 / 500000000) ≤ -Real.log (902901 / 1000000) ∧
    -Real.log (902901 / 1000000) ≤ (102142367 / 1000000000) := by
  have h := checkLog_sound (w := (97099 / 1902901)) (n := 12)
    (lo := (51071183 / 500000000)) (hi := (102142367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902901) = 1/(902901 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5941 : Bounds (-102142367 / 1000000000) (-51071183 / 500000000) (Real.log (902901 / 1000000)) := by
  have h := reflection_log_5941_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5942_neg : (4736471 / 500000000) ≤ -Real.log (990571784199 / 1000000000000) ∧
    -Real.log (990571784199 / 1000000000000) ≤ (9472943 / 1000000000) := by
  have h := checkLog_sound (w := (9428215801 / 1990571784199)) (n := 12)
    (lo := (4736471 / 500000000)) (hi := (9472943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990571784199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990571784199) = 1/(990571784199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5942 : Bounds (-9472943 / 1000000000) (-4736471 / 500000000) (Real.log (990571784199 / 1000000000000)) := by
  have h := reflection_log_5942_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5943_neg : (589073 / 62500000) ≤ -Real.log (39624764359 / 40000000000) ∧
    -Real.log (39624764359 / 40000000000) ≤ (9425169 / 1000000000) := by
  have h := checkLog_sound (w := (375235641 / 79624764359)) (n := 12)
    (lo := (589073 / 62500000)) (hi := (9425169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39624764359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39624764359) = 1/(39624764359 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5943 : Bounds (-9425169 / 1000000000) (-589073 / 62500000) (Real.log (39624764359 / 40000000000)) := by
  have h := reflection_log_5943_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5944_neg : (48579789 / 250000000) ≤ -Real.log (500000000000 / 607241915749) ∧
    -Real.log (500000000000 / 607241915749) ≤ (194319157 / 1000000000) := by
  have h := checkLog_sound (w := (107241915749 / 1107241915749)) (n := 12)
    (lo := (48579789 / 250000000)) (hi := (194319157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607241915749 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607241915749 / 500000000000) = 1/(500000000000 / 607241915749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5944 : Bounds (48579789 / 250000000) (194319157 / 1000000000) (Real.log (607241915749 / 500000000000)) := by
  have h := reflection_log_5944_neg
  have he : Real.log (607241915749 / 500000000000) = -Real.log (500000000000 / 607241915749) := by
    rw [show ((607241915749 / 500000000000) : ℝ) = ((500000000000 / 607241915749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5945_neg : (194811789 / 1000000000) ≤ -Real.log (500000000000 / 607541136847) ∧
    -Real.log (500000000000 / 607541136847) ≤ (19481179 / 100000000) := by
  have h := checkLog_sound (w := (107541136847 / 1107541136847)) (n := 12)
    (lo := (194811789 / 1000000000)) (hi := (19481179 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607541136847 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607541136847 / 500000000000) = 1/(500000000000 / 607541136847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5945 : Bounds (194811789 / 1000000000) (19481179 / 100000000) (Real.log (607541136847 / 500000000000)) := by
  have h := reflection_log_5945_neg
  have he : Real.log (607541136847 / 500000000000) = -Real.log (500000000000 / 607541136847) := by
    rw [show ((607541136847 / 500000000000) : ℝ) = ((500000000000 / 607541136847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5946_neg : (97517967 / 250000000) ≤ -Real.log (4000000000 / 5908347783) ∧
    -Real.log (4000000000 / 5908347783) ≤ (390071869 / 1000000000) := by
  have h := checkLog_sound (w := (1908347783 / 9908347783)) (n := 12)
    (lo := (97517967 / 250000000)) (hi := (390071869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5908347783 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5908347783 / 4000000000) = 1/(4000000000 / 5908347783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5946 : Bounds (97517967 / 250000000) (390071869 / 1000000000) (Real.log (5908347783 / 4000000000)) := by
  have h := reflection_log_5946_neg
  have he : Real.log (5908347783 / 4000000000) = -Real.log (4000000000 / 5908347783) := by
    rw [show ((5908347783 / 4000000000) : ℝ) = ((4000000000 / 5908347783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5947_neg : (390279577 / 1000000000) ≤ -Real.log (500000000000 / 738696890871) ∧
    -Real.log (500000000000 / 738696890871) ≤ (195139789 / 500000000) := by
  have h := checkLog_sound (w := (238696890871 / 1238696890871)) (n := 12)
    (lo := (390279577 / 1000000000)) (hi := (195139789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((738696890871 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(738696890871 / 500000000000) = 1/(500000000000 / 738696890871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5947 : Bounds (390279577 / 1000000000) (195139789 / 500000000) (Real.log (738696890871 / 500000000000)) := by
  have h := reflection_log_5947_neg
  have he : Real.log (738696890871 / 500000000000) = -Real.log (500000000000 / 738696890871) := by
    rw [show ((738696890871 / 500000000000) : ℝ) = ((500000000000 / 738696890871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5948_neg : (44075871 / 250000000) ≤ -Real.log (1250 / 1491) ∧
    -Real.log (1250 / 1491) ≤ (35260697 / 200000000) := by
  have h := checkLog_sound (w := (241 / 2741)) (n := 12)
    (lo := (44075871 / 250000000)) (hi := (35260697 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1491 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1491 / 1250) = 1/(1250 / 1491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5948 : Bounds (44075871 / 250000000) (35260697 / 200000000) (Real.log (1491 / 1250)) := by
  have h := reflection_log_5948_neg
  have he : Real.log (1491 / 1250) = -Real.log (1250 / 1491) := by
    rw [show ((1491 / 1250) : ℝ) = ((1250 / 1491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5949_neg : (214183809 / 1000000000) ≤ -Real.log (1009 / 1250) ∧
    -Real.log (1009 / 1250) ≤ (21418381 / 100000000) := by
  have h := checkLog_sound (w := (241 / 2259)) (n := 12)
    (lo := (214183809 / 1000000000)) (hi := (21418381 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1009) = 1/(1009 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5949 : Bounds (-21418381 / 100000000) (-214183809 / 1000000000) (Real.log (1009 / 1250)) := by
  have h := reflection_log_5949_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5950_neg : (192781 / 1000000000) ≤ -Real.log (1250000 / 1250241) ∧
    -Real.log (1250000 / 1250241) ≤ (96391 / 500000000) := by
  have h := checkLog_sound (w := (241 / 2500241)) (n := 12)
    (lo := (192781 / 1000000000)) (hi := (96391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250241 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250241 / 1250000) = 1/(1250000 / 1250241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5950 : Bounds (192781 / 1000000000) (96391 / 500000000) (Real.log (1250241 / 1250000)) := by
  have h := reflection_log_5950_neg
  have he : Real.log (1250241 / 1250000) = -Real.log (1250000 / 1250241) := by
    rw [show ((1250241 / 1250000) : ℝ) = ((1250000 / 1250241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5951_neg : (96409 / 500000000) ≤ -Real.log (1249759 / 1250000) ∧
    -Real.log (1249759 / 1250000) ≤ (192819 / 1000000000) := by
  have h := checkLog_sound (w := (241 / 2499759)) (n := 12)
    (lo := (96409 / 500000000)) (hi := (192819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249759) = 1/(1249759 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5951 : Bounds (-192819 / 1000000000) (-96409 / 500000000) (Real.log (1249759 / 1250000)) := by
  have h := reflection_log_5951_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0093 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5952_neg : (92493489 / 1000000000) ≤ -Real.log (500000 / 548453) ∧
    -Real.log (500000 / 548453) ≤ (9249349 / 100000000) := by
  have h := checkLog_sound (w := (48453 / 1048453)) (n := 12)
    (lo := (92493489 / 1000000000)) (hi := (9249349 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548453 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548453 / 500000) = 1/(500000 / 548453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5952 : Bounds (92493489 / 1000000000) (9249349 / 100000000) (Real.log (548453 / 500000)) := by
  have h := reflection_log_5952_neg
  have he : Real.log (548453 / 500000) = -Real.log (500000 / 548453) := by
    rw [show ((548453 / 500000) : ℝ) = ((500000 / 548453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5953_neg : (101928633 / 1000000000) ≤ -Real.log (451547 / 500000) ∧
    -Real.log (451547 / 500000) ≤ (50964317 / 500000000) := by
  have h := checkLog_sound (w := (48453 / 951547)) (n := 12)
    (lo := (101928633 / 1000000000)) (hi := (50964317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451547) = 1/(451547 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5953 : Bounds (-50964317 / 500000000) (-101928633 / 1000000000) (Real.log (451547 / 500000)) := by
  have h := reflection_log_5953_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5954_neg : (23178977 / 250000000) ≤ -Real.log (20000 / 21943) ∧
    -Real.log (20000 / 21943) ≤ (92715909 / 1000000000) := by
  have h := checkLog_sound (w := (1943 / 41943)) (n := 12)
    (lo := (23178977 / 250000000)) (hi := (92715909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21943 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21943 / 20000) = 1/(20000 / 21943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5954 : Bounds (23178977 / 250000000) (92715909 / 1000000000) (Real.log (21943 / 20000)) := by
  have h := reflection_log_5954_neg
  have he : Real.log (21943 / 20000) = -Real.log (20000 / 21943) := by
    rw [show ((21943 / 20000) : ℝ) = ((20000 / 21943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5955_neg : (25549713 / 250000000) ≤ -Real.log (18057 / 20000) ∧
    -Real.log (18057 / 20000) ≤ (102198853 / 1000000000) := by
  have h := checkLog_sound (w := (1943 / 38057)) (n := 12)
    (lo := (25549713 / 250000000)) (hi := (102198853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 18057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 18057) = 1/(18057 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5955 : Bounds (-102198853 / 1000000000) (-25549713 / 250000000) (Real.log (18057 / 20000)) := by
  have h := reflection_log_5955_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5956_neg : (9482943 / 1000000000) ≤ -Real.log (396224751 / 400000000) ∧
    -Real.log (396224751 / 400000000) ≤ (148171 / 15625000) := by
  have h := checkLog_sound (w := (3775249 / 796224751)) (n := 12)
    (lo := (9482943 / 1000000000)) (hi := (148171 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 396224751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 396224751) = 1/(396224751 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5956 : Bounds (-148171 / 15625000) (-9482943 / 1000000000) (Real.log (396224751 / 400000000)) := by
  have h := reflection_log_5956_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5957_neg : (1179393 / 125000000) ≤ -Real.log (247652306791 / 250000000000) ∧
    -Real.log (247652306791 / 250000000000) ≤ (1887029 / 200000000) := by
  have h := checkLog_sound (w := (2347693209 / 497652306791)) (n := 12)
    (lo := (1179393 / 125000000)) (hi := (1887029 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247652306791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247652306791) = 1/(247652306791 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5957 : Bounds (-1887029 / 200000000) (-1179393 / 125000000) (Real.log (247652306791 / 250000000000)) := by
  have h := reflection_log_5957_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5958_neg : (97211061 / 500000000) ≤ -Real.log (250000000000 / 303652222249) ∧
    -Real.log (250000000000 / 303652222249) ≤ (194422123 / 1000000000) := by
  have h := checkLog_sound (w := (53652222249 / 553652222249)) (n := 12)
    (lo := (97211061 / 500000000)) (hi := (194422123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303652222249 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303652222249 / 250000000000) = 1/(250000000000 / 303652222249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5958 : Bounds (97211061 / 500000000) (194422123 / 1000000000) (Real.log (303652222249 / 250000000000)) := by
  have h := reflection_log_5958_neg
  have he : Real.log (303652222249 / 250000000000) = -Real.log (250000000000 / 303652222249) := by
    rw [show ((303652222249 / 250000000000) : ℝ) = ((250000000000 / 303652222249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5959_neg : (4872869 / 25000000) ≤ -Real.log (500000000000 / 607603699397) ∧
    -Real.log (500000000000 / 607603699397) ≤ (194914761 / 1000000000) := by
  have h := checkLog_sound (w := (107603699397 / 1107603699397)) (n := 12)
    (lo := (4872869 / 25000000)) (hi := (194914761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607603699397 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607603699397 / 500000000000) = 1/(500000000000 / 607603699397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5959 : Bounds (4872869 / 25000000) (194914761 / 1000000000) (Real.log (607603699397 / 500000000000)) := by
  have h := reflection_log_5959_neg
  have he : Real.log (607603699397 / 500000000000) = -Real.log (500000000000 / 607603699397) := by
    rw [show ((607603699397 / 500000000000) : ℝ) = ((500000000000 / 607603699397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5960_neg : (390279577 / 1000000000) ≤ -Real.log (50000000000 / 73869689087) ∧
    -Real.log (50000000000 / 73869689087) ≤ (195139789 / 500000000) := by
  have h := checkLog_sound (w := (23869689087 / 123869689087)) (n := 12)
    (lo := (390279577 / 1000000000)) (hi := (195139789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73869689087 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73869689087 / 50000000000) = 1/(50000000000 / 73869689087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5960 : Bounds (390279577 / 1000000000) (195139789 / 500000000) (Real.log (73869689087 / 50000000000)) := by
  have h := reflection_log_5960_neg
  have he : Real.log (73869689087 / 50000000000) = -Real.log (50000000000 / 73869689087) := by
    rw [show ((73869689087 / 50000000000) : ℝ) = ((50000000000 / 73869689087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5961_neg : (195243647 / 500000000) ≤ -Real.log (500000000000 / 738850346879) ∧
    -Real.log (500000000000 / 738850346879) ≤ (78097459 / 200000000) := by
  have h := checkLog_sound (w := (238850346879 / 1238850346879)) (n := 12)
    (lo := (195243647 / 500000000)) (hi := (78097459 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((738850346879 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(738850346879 / 500000000000) = 1/(500000000000 / 738850346879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5961 : Bounds (195243647 / 500000000) (78097459 / 200000000) (Real.log (738850346879 / 500000000000)) := by
  have h := reflection_log_5961_neg
  have he : Real.log (738850346879 / 500000000000) = -Real.log (500000000000 / 738850346879) := by
    rw [show ((738850346879 / 500000000000) : ℝ) = ((500000000000 / 738850346879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5962_neg : (176387317 / 1000000000) ≤ -Real.log (10000 / 11929) ∧
    -Real.log (10000 / 11929) ≤ (88193659 / 500000000) := by
  have h := checkLog_sound (w := (1929 / 21929)) (n := 12)
    (lo := (176387317 / 1000000000)) (hi := (88193659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11929 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11929 / 10000) = 1/(10000 / 11929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5962 : Bounds (176387317 / 1000000000) (88193659 / 500000000) (Real.log (11929 / 10000)) := by
  have h := reflection_log_5962_neg
  have he : Real.log (11929 / 10000) = -Real.log (10000 / 11929) := by
    rw [show ((11929 / 10000) : ℝ) = ((10000 / 11929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5963_neg : (107153851 / 500000000) ≤ -Real.log (8071 / 10000) ∧
    -Real.log (8071 / 10000) ≤ (214307703 / 1000000000) := by
  have h := checkLog_sound (w := (1929 / 18071)) (n := 12)
    (lo := (107153851 / 500000000)) (hi := (214307703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8071) = 1/(8071 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5963 : Bounds (-214307703 / 1000000000) (-107153851 / 500000000) (Real.log (8071 / 10000)) := by
  have h := reflection_log_5963_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5964_neg : (192881 / 1000000000) ≤ -Real.log (10000000 / 10001929) ∧
    -Real.log (10000000 / 10001929) ≤ (96441 / 500000000) := by
  have h := checkLog_sound (w := (1929 / 20001929)) (n := 12)
    (lo := (192881 / 1000000000)) (hi := (96441 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001929 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001929 / 10000000) = 1/(10000000 / 10001929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5964 : Bounds (192881 / 1000000000) (96441 / 500000000) (Real.log (10001929 / 10000000)) := by
  have h := reflection_log_5964_neg
  have he : Real.log (10001929 / 10000000) = -Real.log (10000000 / 10001929) := by
    rw [show ((10001929 / 10000000) : ℝ) = ((10000000 / 10001929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5965_neg : (96459 / 500000000) ≤ -Real.log (9998071 / 10000000) ∧
    -Real.log (9998071 / 10000000) ≤ (192919 / 1000000000) := by
  have h := checkLog_sound (w := (1929 / 19998071)) (n := 12)
    (lo := (96459 / 500000000)) (hi := (192919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998071) = 1/(9998071 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5965 : Bounds (-192919 / 1000000000) (-96459 / 500000000) (Real.log (9998071 / 10000000)) := by
  have h := reflection_log_5965_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5966_neg : (46269991 / 500000000) ≤ -Real.log (1000000 / 1096957) ∧
    -Real.log (1000000 / 1096957) ≤ (92539983 / 1000000000) := by
  have h := checkLog_sound (w := (96957 / 2096957)) (n := 12)
    (lo := (46269991 / 500000000)) (hi := (92539983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096957 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096957 / 1000000) = 1/(1000000 / 1096957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5966 : Bounds (46269991 / 500000000) (92539983 / 1000000000) (Real.log (1096957 / 1000000)) := by
  have h := reflection_log_5966_neg
  have he : Real.log (1096957 / 1000000) = -Real.log (1000000 / 1096957) := by
    rw [show ((1096957 / 1000000) : ℝ) = ((1000000 / 1096957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5967_neg : (101985107 / 1000000000) ≤ -Real.log (903043 / 1000000) ∧
    -Real.log (903043 / 1000000) ≤ (25496277 / 250000000) := by
  have h := checkLog_sound (w := (96957 / 1903043)) (n := 12)
    (lo := (101985107 / 1000000000)) (hi := (25496277 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903043) = 1/(903043 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5967 : Bounds (-25496277 / 250000000) (-101985107 / 1000000000) (Real.log (903043 / 1000000)) := by
  have h := reflection_log_5967_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5968_neg : (92762391 / 1000000000) ≤ -Real.log (1000000 / 1097201) ∧
    -Real.log (1000000 / 1097201) ≤ (11595299 / 125000000) := by
  have h := checkLog_sound (w := (97201 / 2097201)) (n := 12)
    (lo := (92762391 / 1000000000)) (hi := (11595299 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097201 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097201 / 1000000) = 1/(1000000 / 1097201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5968 : Bounds (92762391 / 1000000000) (11595299 / 125000000) (Real.log (1097201 / 1000000)) := by
  have h := reflection_log_5968_neg
  have he : Real.log (1097201 / 1000000) = -Real.log (1000000 / 1097201) := by
    rw [show ((1097201 / 1000000) : ℝ) = ((1000000 / 1097201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5969_neg : (102255341 / 1000000000) ≤ -Real.log (902799 / 1000000) ∧
    -Real.log (902799 / 1000000) ≤ (51127671 / 500000000) := by
  have h := checkLog_sound (w := (97201 / 1902799)) (n := 12)
    (lo := (102255341 / 1000000000)) (hi := (51127671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902799) = 1/(902799 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5969 : Bounds (-51127671 / 500000000) (-102255341 / 1000000000) (Real.log (902799 / 1000000)) := by
  have h := reflection_log_5969_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5970_neg : (189859 / 20000000) ≤ -Real.log (990551965599 / 1000000000000) ∧
    -Real.log (990551965599 / 1000000000000) ≤ (9492951 / 1000000000) := by
  have h := checkLog_sound (w := (9448034401 / 1990551965599)) (n := 12)
    (lo := (189859 / 20000000)) (hi := (9492951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990551965599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990551965599) = 1/(990551965599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5970 : Bounds (-9492951 / 1000000000) (-189859 / 20000000) (Real.log (990551965599 / 1000000000000)) := by
  have h := reflection_log_5970_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5971_neg : (2361281 / 250000000) ≤ -Real.log (990599340151 / 1000000000000) ∧
    -Real.log (990599340151 / 1000000000000) ≤ (75561 / 8000000) := by
  have h := checkLog_sound (w := (9400659849 / 1990599340151)) (n := 12)
    (lo := (2361281 / 250000000)) (hi := (75561 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990599340151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990599340151) = 1/(990599340151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5971 : Bounds (-75561 / 8000000) (-2361281 / 250000000) (Real.log (990599340151 / 1000000000000)) := by
  have h := reflection_log_5971_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5972_neg : (19452509 / 100000000) ≤ -Real.log (500000000000 / 607366980309) ∧
    -Real.log (500000000000 / 607366980309) ≤ (194525091 / 1000000000) := by
  have h := checkLog_sound (w := (107366980309 / 1107366980309)) (n := 12)
    (lo := (19452509 / 100000000)) (hi := (194525091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607366980309 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607366980309 / 500000000000) = 1/(500000000000 / 607366980309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5972 : Bounds (19452509 / 100000000) (194525091 / 1000000000) (Real.log (607366980309 / 500000000000)) := by
  have h := reflection_log_5972_neg
  have he : Real.log (607366980309 / 500000000000) = -Real.log (500000000000 / 607366980309) := by
    rw [show ((607366980309 / 500000000000) : ℝ) = ((500000000000 / 607366980309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5973_neg : (195017733 / 1000000000) ≤ -Real.log (100000000000 / 121533253803) ∧
    -Real.log (100000000000 / 121533253803) ≤ (97508867 / 500000000) := by
  have h := checkLog_sound (w := (21533253803 / 221533253803)) (n := 12)
    (lo := (195017733 / 1000000000)) (hi := (97508867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121533253803 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121533253803 / 100000000000) = 1/(100000000000 / 121533253803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5973 : Bounds (195017733 / 1000000000) (97508867 / 500000000) (Real.log (121533253803 / 100000000000)) := by
  have h := reflection_log_5973_neg
  have he : Real.log (121533253803 / 100000000000) = -Real.log (100000000000 / 121533253803) := by
    rw [show ((121533253803 / 100000000000) : ℝ) = ((100000000000 / 121533253803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5974_neg : (195243647 / 500000000) ≤ -Real.log (250000000000 / 369425173439) ∧
    -Real.log (250000000000 / 369425173439) ≤ (78097459 / 200000000) := by
  have h := checkLog_sound (w := (119425173439 / 619425173439)) (n := 12)
    (lo := (195243647 / 500000000)) (hi := (78097459 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369425173439 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369425173439 / 250000000000) = 1/(250000000000 / 369425173439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5974 : Bounds (195243647 / 500000000) (78097459 / 200000000) (Real.log (369425173439 / 250000000000)) := by
  have h := reflection_log_5974_neg
  have he : Real.log (369425173439 / 250000000000) = -Real.log (250000000000 / 369425173439) := by
    rw [show ((369425173439 / 250000000000) : ℝ) = ((250000000000 / 369425173439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5975_neg : (390695019 / 1000000000) ≤ -Real.log (31250000000 / 46187740057) ∧
    -Real.log (31250000000 / 46187740057) ≤ (19534751 / 50000000) := by
  have h := checkLog_sound (w := (14937740057 / 77437740057)) (n := 12)
    (lo := (390695019 / 1000000000)) (hi := (19534751 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46187740057 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46187740057 / 31250000000) = 1/(31250000000 / 46187740057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5975 : Bounds (390695019 / 1000000000) (19534751 / 50000000) (Real.log (46187740057 / 31250000000)) := by
  have h := reflection_log_5975_neg
  have he : Real.log (46187740057 / 31250000000) = -Real.log (31250000000 / 46187740057) := by
    rw [show ((46187740057 / 31250000000) : ℝ) = ((31250000000 / 46187740057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5976_neg : (176471143 / 1000000000) ≤ -Real.log (1000 / 1193) ∧
    -Real.log (1000 / 1193) ≤ (22058893 / 125000000) := by
  have h := checkLog_sound (w := (193 / 2193)) (n := 12)
    (lo := (176471143 / 1000000000)) (hi := (22058893 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1193 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1193 / 1000) = 1/(1000 / 1193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5976 : Bounds (176471143 / 1000000000) (22058893 / 125000000) (Real.log (1193 / 1000)) := by
  have h := reflection_log_5976_neg
  have he : Real.log (1193 / 1000) = -Real.log (1000 / 1193) := by
    rw [show ((1193 / 1000) : ℝ) = ((1000 / 1193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5977_neg : (21443161 / 100000000) ≤ -Real.log (807 / 1000) ∧
    -Real.log (807 / 1000) ≤ (214431611 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 1807)) (n := 12)
    (lo := (21443161 / 100000000)) (hi := (214431611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 807) = 1/(807 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5977 : Bounds (-214431611 / 1000000000) (-21443161 / 100000000) (Real.log (807 / 1000)) := by
  have h := reflection_log_5977_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5978_neg : (192981 / 1000000000) ≤ -Real.log (1000000 / 1000193) ∧
    -Real.log (1000000 / 1000193) ≤ (96491 / 500000000) := by
  have h := checkLog_sound (w := (193 / 2000193)) (n := 12)
    (lo := (192981 / 1000000000)) (hi := (96491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000193 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000193 / 1000000) = 1/(1000000 / 1000193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5978 : Bounds (192981 / 1000000000) (96491 / 500000000) (Real.log (1000193 / 1000000)) := by
  have h := reflection_log_5978_neg
  have he : Real.log (1000193 / 1000000) = -Real.log (1000000 / 1000193) := by
    rw [show ((1000193 / 1000000) : ℝ) = ((1000000 / 1000193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5979_neg : (96509 / 500000000) ≤ -Real.log (999807 / 1000000) ∧
    -Real.log (999807 / 1000000) ≤ (193019 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 1999807)) (n := 12)
    (lo := (96509 / 500000000)) (hi := (193019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999807) = 1/(999807 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5979 : Bounds (-193019 / 1000000000) (-96509 / 500000000) (Real.log (999807 / 1000000)) := by
  have h := reflection_log_5979_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5980_neg : (92586473 / 1000000000) ≤ -Real.log (62500 / 68563) ∧
    -Real.log (62500 / 68563) ≤ (46293237 / 500000000) := by
  have h := checkLog_sound (w := (6063 / 131063)) (n := 12)
    (lo := (92586473 / 1000000000)) (hi := (46293237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68563 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68563 / 62500) = 1/(62500 / 68563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5980 : Bounds (92586473 / 1000000000) (46293237 / 500000000) (Real.log (68563 / 62500)) := by
  have h := reflection_log_5980_neg
  have he : Real.log (68563 / 62500) = -Real.log (62500 / 68563) := by
    rw [show ((68563 / 62500) : ℝ) = ((62500 / 68563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5981_neg : (6377599 / 62500000) ≤ -Real.log (56437 / 62500) ∧
    -Real.log (56437 / 62500) ≤ (20408317 / 200000000) := by
  have h := checkLog_sound (w := (6063 / 118937)) (n := 12)
    (lo := (6377599 / 62500000)) (hi := (20408317 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56437) = 1/(56437 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5981 : Bounds (-20408317 / 200000000) (-6377599 / 62500000) (Real.log (56437 / 62500)) := by
  have h := reflection_log_5981_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5982_neg : (11601109 / 125000000) ≤ -Real.log (250000 / 274313) ∧
    -Real.log (250000 / 274313) ≤ (92808873 / 1000000000) := by
  have h := checkLog_sound (w := (24313 / 524313)) (n := 12)
    (lo := (11601109 / 125000000)) (hi := (92808873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274313 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274313 / 250000) = 1/(250000 / 274313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5982 : Bounds (11601109 / 125000000) (92808873 / 1000000000) (Real.log (274313 / 250000)) := by
  have h := reflection_log_5982_neg
  have he : Real.log (274313 / 250000) = -Real.log (250000 / 274313) := by
    rw [show ((274313 / 250000) : ℝ) = ((250000 / 274313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5983_neg : (51155917 / 500000000) ≤ -Real.log (225687 / 250000) ∧
    -Real.log (225687 / 250000) ≤ (20462367 / 200000000) := by
  have h := checkLog_sound (w := (24313 / 475687)) (n := 12)
    (lo := (51155917 / 500000000)) (hi := (20462367 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225687) = 1/(225687 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5983 : Bounds (-20462367 / 200000000) (-51155917 / 500000000) (Real.log (225687 / 250000)) := by
  have h := reflection_log_5983_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5984_neg : (9502961 / 1000000000) ≤ -Real.log (61908878031 / 62500000000) ∧
    -Real.log (61908878031 / 62500000000) ≤ (4751481 / 500000000) := by
  have h := checkLog_sound (w := (591121969 / 124408878031)) (n := 12)
    (lo := (9502961 / 1000000000)) (hi := (4751481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61908878031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61908878031) = 1/(61908878031 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5984 : Bounds (-4751481 / 500000000) (-9502961 / 1000000000) (Real.log (61908878031 / 62500000000)) := by
  have h := reflection_log_5984_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5985_neg : (9455111 / 1000000000) ≤ -Real.log (3869490031 / 3906250000) ∧
    -Real.log (3869490031 / 3906250000) ≤ (1181889 / 125000000) := by
  have h := checkLog_sound (w := (36759969 / 7775740031)) (n := 12)
    (lo := (9455111 / 1000000000)) (hi := (1181889 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3869490031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3869490031) = 1/(3869490031 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5985 : Bounds (-1181889 / 125000000) (-9455111 / 1000000000) (Real.log (3869490031 / 3906250000)) := by
  have h := reflection_log_5985_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5986_neg : (97314029 / 500000000) ≤ -Real.log (100000000000 / 121485904637) ∧
    -Real.log (100000000000 / 121485904637) ≤ (194628059 / 1000000000) := by
  have h := checkLog_sound (w := (21485904637 / 221485904637)) (n := 12)
    (lo := (97314029 / 500000000)) (hi := (194628059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121485904637 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121485904637 / 100000000000) = 1/(100000000000 / 121485904637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5986 : Bounds (97314029 / 500000000) (194628059 / 1000000000) (Real.log (121485904637 / 100000000000)) := by
  have h := reflection_log_5986_neg
  have he : Real.log (121485904637 / 100000000000) = -Real.log (100000000000 / 121485904637) := by
    rw [show ((121485904637 / 100000000000) : ℝ) = ((100000000000 / 121485904637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5987_neg : (97560353 / 500000000) ≤ -Real.log (500000000000 / 607728845703) ∧
    -Real.log (500000000000 / 607728845703) ≤ (195120707 / 1000000000) := by
  have h := checkLog_sound (w := (107728845703 / 1107728845703)) (n := 12)
    (lo := (97560353 / 500000000)) (hi := (195120707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607728845703 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607728845703 / 500000000000) = 1/(500000000000 / 607728845703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5987 : Bounds (97560353 / 500000000) (195120707 / 1000000000) (Real.log (607728845703 / 500000000000)) := by
  have h := reflection_log_5987_neg
  have he : Real.log (607728845703 / 500000000000) = -Real.log (500000000000 / 607728845703) := by
    rw [show ((607728845703 / 500000000000) : ℝ) = ((500000000000 / 607728845703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5988_neg : (390695019 / 1000000000) ≤ -Real.log (500000000000 / 739003840911) ∧
    -Real.log (500000000000 / 739003840911) ≤ (19534751 / 50000000) := by
  have h := checkLog_sound (w := (239003840911 / 1239003840911)) (n := 12)
    (lo := (390695019 / 1000000000)) (hi := (19534751 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739003840911 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739003840911 / 500000000000) = 1/(500000000000 / 739003840911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5988 : Bounds (390695019 / 1000000000) (19534751 / 50000000) (Real.log (739003840911 / 500000000000)) := by
  have h := reflection_log_5988_neg
  have he : Real.log (739003840911 / 500000000000) = -Real.log (500000000000 / 739003840911) := by
    rw [show ((739003840911 / 500000000000) : ℝ) = ((500000000000 / 739003840911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5989_neg : (390902753 / 1000000000) ≤ -Real.log (500000000000 / 739157372987) ∧
    -Real.log (500000000000 / 739157372987) ≤ (195451377 / 500000000) := by
  have h := checkLog_sound (w := (239157372987 / 1239157372987)) (n := 12)
    (lo := (390902753 / 1000000000)) (hi := (195451377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739157372987 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739157372987 / 500000000000) = 1/(500000000000 / 739157372987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5989 : Bounds (390902753 / 1000000000) (195451377 / 500000000) (Real.log (739157372987 / 500000000000)) := by
  have h := reflection_log_5989_neg
  have he : Real.log (739157372987 / 500000000000) = -Real.log (500000000000 / 739157372987) := by
    rw [show ((739157372987 / 500000000000) : ℝ) = ((500000000000 / 739157372987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5990_neg : (176554961 / 1000000000) ≤ -Real.log (10000 / 11931) ∧
    -Real.log (10000 / 11931) ≤ (88277481 / 500000000) := by
  have h := checkLog_sound (w := (1931 / 21931)) (n := 12)
    (lo := (176554961 / 1000000000)) (hi := (88277481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11931 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11931 / 10000) = 1/(10000 / 11931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5990 : Bounds (176554961 / 1000000000) (88277481 / 500000000) (Real.log (11931 / 10000)) := by
  have h := reflection_log_5990_neg
  have he : Real.log (11931 / 10000) = -Real.log (10000 / 11931) := by
    rw [show ((11931 / 10000) : ℝ) = ((10000 / 11931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5991_neg : (107277767 / 500000000) ≤ -Real.log (8069 / 10000) ∧
    -Real.log (8069 / 10000) ≤ (42911107 / 200000000) := by
  have h := checkLog_sound (w := (1931 / 18069)) (n := 12)
    (lo := (107277767 / 500000000)) (hi := (42911107 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8069) = 1/(8069 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5991 : Bounds (-42911107 / 200000000) (-107277767 / 500000000) (Real.log (8069 / 10000)) := by
  have h := reflection_log_5991_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5992_neg : (193081 / 1000000000) ≤ -Real.log (10000000 / 10001931) ∧
    -Real.log (10000000 / 10001931) ≤ (96541 / 500000000) := by
  have h := checkLog_sound (w := (1931 / 20001931)) (n := 12)
    (lo := (193081 / 1000000000)) (hi := (96541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001931 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001931 / 10000000) = 1/(10000000 / 10001931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5992 : Bounds (193081 / 1000000000) (96541 / 500000000) (Real.log (10001931 / 10000000)) := by
  have h := reflection_log_5992_neg
  have he : Real.log (10001931 / 10000000) = -Real.log (10000000 / 10001931) := by
    rw [show ((10001931 / 10000000) : ℝ) = ((10000000 / 10001931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5993_neg : (96559 / 500000000) ≤ -Real.log (9998069 / 10000000) ∧
    -Real.log (9998069 / 10000000) ≤ (193119 / 1000000000) := by
  have h := checkLog_sound (w := (1931 / 19998069)) (n := 12)
    (lo := (96559 / 500000000)) (hi := (193119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998069) = 1/(9998069 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5993 : Bounds (-193119 / 1000000000) (-96559 / 500000000) (Real.log (9998069 / 10000000)) := by
  have h := reflection_log_5993_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5994_neg : (46316481 / 500000000) ≤ -Real.log (1000000 / 1097059) ∧
    -Real.log (1000000 / 1097059) ≤ (92632963 / 1000000000) := by
  have h := checkLog_sound (w := (97059 / 2097059)) (n := 12)
    (lo := (46316481 / 500000000)) (hi := (92632963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097059 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097059 / 1000000) = 1/(1000000 / 1097059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5994 : Bounds (46316481 / 500000000) (92632963 / 1000000000) (Real.log (1097059 / 1000000)) := by
  have h := reflection_log_5994_neg
  have he : Real.log (1097059 / 1000000) = -Real.log (1000000 / 1097059) := by
    rw [show ((1097059 / 1000000) : ℝ) = ((1000000 / 1097059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5995_neg : (20419613 / 200000000) ≤ -Real.log (902941 / 1000000) ∧
    -Real.log (902941 / 1000000) ≤ (51049033 / 500000000) := by
  have h := checkLog_sound (w := (97059 / 1902941)) (n := 12)
    (lo := (20419613 / 200000000)) (hi := (51049033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902941) = 1/(902941 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5995 : Bounds (-51049033 / 500000000) (-20419613 / 200000000) (Real.log (902941 / 1000000)) := by
  have h := reflection_log_5995_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5996_neg : (1857107 / 20000000) ≤ -Real.log (1000000 / 1097303) ∧
    -Real.log (1000000 / 1097303) ≤ (92855351 / 1000000000) := by
  have h := checkLog_sound (w := (97303 / 2097303)) (n := 12)
    (lo := (1857107 / 20000000)) (hi := (92855351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097303 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097303 / 1000000) = 1/(1000000 / 1097303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5996 : Bounds (1857107 / 20000000) (92855351 / 1000000000) (Real.log (1097303 / 1000000)) := by
  have h := reflection_log_5996_neg
  have he : Real.log (1097303 / 1000000) = -Real.log (1000000 / 1097303) := by
    rw [show ((1097303 / 1000000) : ℝ) = ((1000000 / 1097303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5997_neg : (10236833 / 100000000) ≤ -Real.log (902697 / 1000000) ∧
    -Real.log (902697 / 1000000) ≤ (102368331 / 1000000000) := by
  have h := checkLog_sound (w := (97303 / 1902697)) (n := 12)
    (lo := (10236833 / 100000000)) (hi := (102368331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902697) = 1/(902697 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5997 : Bounds (-102368331 / 1000000000) (-10236833 / 100000000) (Real.log (902697 / 1000000)) := by
  have h := reflection_log_5997_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5998_neg : (9512979 / 1000000000) ≤ -Real.log (990532126191 / 1000000000000) ∧
    -Real.log (990532126191 / 1000000000000) ≤ (475649 / 50000000) := by
  have h := checkLog_sound (w := (9467873809 / 1990532126191)) (n := 12)
    (lo := (9512979 / 1000000000)) (hi := (475649 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990532126191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990532126191) = 1/(990532126191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5998 : Bounds (-475649 / 50000000) (-9512979 / 1000000000) (Real.log (990532126191 / 1000000000000)) := by
  have h := reflection_log_5998_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5999_neg : (4732551 / 500000000) ≤ -Real.log (990579550519 / 1000000000000) ∧
    -Real.log (990579550519 / 1000000000000) ≤ (9465103 / 1000000000) := by
  have h := checkLog_sound (w := (9420449481 / 1990579550519)) (n := 12)
    (lo := (4732551 / 500000000)) (hi := (9465103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990579550519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990579550519) = 1/(990579550519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5999 : Bounds (-9465103 / 1000000000) (-4732551 / 500000000) (Real.log (990579550519 / 1000000000000)) := by
  have h := reflection_log_5999_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6000_neg : (48682757 / 250000000) ≤ -Real.log (800000000 / 971987317) ∧
    -Real.log (800000000 / 971987317) ≤ (194731029 / 1000000000) := by
  have h := checkLog_sound (w := (171987317 / 1771987317)) (n := 12)
    (lo := (48682757 / 250000000)) (hi := (194731029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((971987317 / 800000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(971987317 / 800000000) = 1/(800000000 / 971987317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6000 : Bounds (48682757 / 250000000) (194731029 / 1000000000) (Real.log (971987317 / 800000000)) := by
  have h := reflection_log_6000_neg
  have he : Real.log (971987317 / 800000000) = -Real.log (800000000 / 971987317) := by
    rw [show ((971987317 / 800000000) : ℝ) = ((800000000 / 971987317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6001_neg : (195223681 / 1000000000) ≤ -Real.log (500000000000 / 607791429461) ∧
    -Real.log (500000000000 / 607791429461) ≤ (97611841 / 500000000) := by
  have h := checkLog_sound (w := (107791429461 / 1107791429461)) (n := 12)
    (lo := (195223681 / 1000000000)) (hi := (97611841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607791429461 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607791429461 / 500000000000) = 1/(500000000000 / 607791429461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6001 : Bounds (195223681 / 1000000000) (97611841 / 500000000) (Real.log (607791429461 / 500000000000)) := by
  have h := reflection_log_6001_neg
  have he : Real.log (607791429461 / 500000000000) = -Real.log (500000000000 / 607791429461) := by
    rw [show ((607791429461 / 500000000000) : ℝ) = ((500000000000 / 607791429461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6002_neg : (390902753 / 1000000000) ≤ -Real.log (250000000000 / 369578686493) ∧
    -Real.log (250000000000 / 369578686493) ≤ (195451377 / 500000000) := by
  have h := checkLog_sound (w := (119578686493 / 619578686493)) (n := 12)
    (lo := (390902753 / 1000000000)) (hi := (195451377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369578686493 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369578686493 / 250000000000) = 1/(250000000000 / 369578686493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6002 : Bounds (390902753 / 1000000000) (195451377 / 500000000) (Real.log (369578686493 / 250000000000)) := by
  have h := reflection_log_6002_neg
  have he : Real.log (369578686493 / 250000000000) = -Real.log (250000000000 / 369578686493) := by
    rw [show ((369578686493 / 250000000000) : ℝ) = ((250000000000 / 369578686493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6003_neg : (12222203 / 31250000) ≤ -Real.log (125000000000 / 184827735779) ∧
    -Real.log (125000000000 / 184827735779) ≤ (391110497 / 1000000000) := by
  have h := checkLog_sound (w := (59827735779 / 309827735779)) (n := 12)
    (lo := (12222203 / 31250000)) (hi := (391110497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184827735779 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184827735779 / 125000000000) = 1/(125000000000 / 184827735779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6003 : Bounds (12222203 / 31250000) (391110497 / 1000000000) (Real.log (184827735779 / 125000000000)) := by
  have h := reflection_log_6003_neg
  have he : Real.log (184827735779 / 125000000000) = -Real.log (125000000000 / 184827735779) := by
    rw [show ((184827735779 / 125000000000) : ℝ) = ((125000000000 / 184827735779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6004_neg : (176638773 / 1000000000) ≤ -Real.log (2500 / 2983) ∧
    -Real.log (2500 / 2983) ≤ (88319387 / 500000000) := by
  have h := checkLog_sound (w := (483 / 5483)) (n := 12)
    (lo := (176638773 / 1000000000)) (hi := (88319387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2983 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2983 / 2500) = 1/(2500 / 2983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6004 : Bounds (176638773 / 1000000000) (88319387 / 500000000) (Real.log (2983 / 2500)) := by
  have h := reflection_log_6004_neg
  have he : Real.log (2983 / 2500) = -Real.log (2500 / 2983) := by
    rw [show ((2983 / 2500) : ℝ) = ((2500 / 2983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6005_neg : (13417467 / 62500000) ≤ -Real.log (2017 / 2500) ∧
    -Real.log (2017 / 2500) ≤ (214679473 / 1000000000) := by
  have h := checkLog_sound (w := (483 / 4517)) (n := 12)
    (lo := (13417467 / 62500000)) (hi := (214679473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2017) = 1/(2017 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6005 : Bounds (-214679473 / 1000000000) (-13417467 / 62500000) (Real.log (2017 / 2500)) := by
  have h := reflection_log_6005_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6006_neg : (193181 / 1000000000) ≤ -Real.log (2500000 / 2500483) ∧
    -Real.log (2500000 / 2500483) ≤ (96591 / 500000000) := by
  have h := checkLog_sound (w := (483 / 5000483)) (n := 12)
    (lo := (193181 / 1000000000)) (hi := (96591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500483 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500483 / 2500000) = 1/(2500000 / 2500483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6006 : Bounds (193181 / 1000000000) (96591 / 500000000) (Real.log (2500483 / 2500000)) := by
  have h := reflection_log_6006_neg
  have he : Real.log (2500483 / 2500000) = -Real.log (2500000 / 2500483) := by
    rw [show ((2500483 / 2500000) : ℝ) = ((2500000 / 2500483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6007_neg : (96609 / 500000000) ≤ -Real.log (2499517 / 2500000) ∧
    -Real.log (2499517 / 2500000) ≤ (193219 / 1000000000) := by
  have h := checkLog_sound (w := (483 / 4999517)) (n := 12)
    (lo := (96609 / 500000000)) (hi := (193219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499517) = 1/(2499517 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6007 : Bounds (-193219 / 1000000000) (-96609 / 500000000) (Real.log (2499517 / 2500000)) := by
  have h := reflection_log_6007_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6008_neg : (92679449 / 1000000000) ≤ -Real.log (100000 / 109711) ∧
    -Real.log (100000 / 109711) ≤ (1853589 / 20000000) := by
  have h := checkLog_sound (w := (9711 / 209711)) (n := 12)
    (lo := (92679449 / 1000000000)) (hi := (1853589 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109711 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109711 / 100000) = 1/(100000 / 109711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6008 : Bounds (92679449 / 1000000000) (1853589 / 20000000) (Real.log (109711 / 100000)) := by
  have h := reflection_log_6008_neg
  have he : Real.log (109711 / 100000) = -Real.log (100000 / 109711) := by
    rw [show ((109711 / 100000) : ℝ) = ((100000 / 109711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6009_neg : (102154549 / 1000000000) ≤ -Real.log (90289 / 100000) ∧
    -Real.log (90289 / 100000) ≤ (2043091 / 20000000) := by
  have h := checkLog_sound (w := (9711 / 190289)) (n := 12)
    (lo := (102154549 / 1000000000)) (hi := (2043091 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90289) = 1/(90289 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6009 : Bounds (-2043091 / 20000000) (-102154549 / 1000000000) (Real.log (90289 / 100000)) := by
  have h := reflection_log_6009_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6010_neg : (92901827 / 1000000000) ≤ -Real.log (500000 / 548677) ∧
    -Real.log (500000 / 548677) ≤ (23225457 / 250000000) := by
  have h := checkLog_sound (w := (48677 / 1048677)) (n := 12)
    (lo := (92901827 / 1000000000)) (hi := (23225457 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548677 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548677 / 500000) = 1/(500000 / 548677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6010 : Bounds (92901827 / 1000000000) (23225457 / 250000000) (Real.log (548677 / 500000)) := by
  have h := reflection_log_6010_neg
  have he : Real.log (548677 / 500000) = -Real.log (500000 / 548677) := by
    rw [show ((548677 / 500000) : ℝ) = ((500000 / 548677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6011_neg : (102424829 / 1000000000) ≤ -Real.log (451323 / 500000) ∧
    -Real.log (451323 / 500000) ≤ (10242483 / 100000000) := by
  have h := checkLog_sound (w := (48677 / 951323)) (n := 12)
    (lo := (102424829 / 1000000000)) (hi := (10242483 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451323) = 1/(451323 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6011 : Bounds (-10242483 / 100000000) (-102424829 / 1000000000) (Real.log (451323 / 500000)) := by
  have h := reflection_log_6011_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6012_neg : (9523001 / 1000000000) ≤ -Real.log (247630549671 / 250000000000) ∧
    -Real.log (247630549671 / 250000000000) ≤ (4761501 / 500000000) := by
  have h := checkLog_sound (w := (2369450329 / 497630549671)) (n := 12)
    (lo := (9523001 / 1000000000)) (hi := (4761501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247630549671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247630549671) = 1/(247630549671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6012 : Bounds (-4761501 / 500000000) (-9523001 / 1000000000) (Real.log (247630549671 / 250000000000)) := by
  have h := reflection_log_6012_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6013_neg : (9475099 / 1000000000) ≤ -Real.log (9905696479 / 10000000000) ∧
    -Real.log (9905696479 / 10000000000) ≤ (94751 / 10000000) := by
  have h := checkLog_sound (w := (94303521 / 19905696479)) (n := 12)
    (lo := (9475099 / 1000000000)) (hi := (94751 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9905696479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9905696479) = 1/(9905696479 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6013 : Bounds (-94751 / 10000000) (-9475099 / 1000000000) (Real.log (9905696479 / 10000000000)) := by
  have h := reflection_log_6013_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6014_neg : (97416999 / 500000000) ≤ -Real.log (125000000000 / 151888657533) ∧
    -Real.log (125000000000 / 151888657533) ≤ (194833999 / 1000000000) := by
  have h := checkLog_sound (w := (26888657533 / 276888657533)) (n := 12)
    (lo := (97416999 / 500000000)) (hi := (194833999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151888657533 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151888657533 / 125000000000) = 1/(125000000000 / 151888657533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6014 : Bounds (97416999 / 500000000) (194833999 / 1000000000) (Real.log (151888657533 / 125000000000)) := by
  have h := reflection_log_6014_neg
  have he : Real.log (151888657533 / 125000000000) = -Real.log (125000000000 / 151888657533) := by
    rw [show ((151888657533 / 125000000000) : ℝ) = ((125000000000 / 151888657533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6015_neg : (3051979 / 15625000) ≤ -Real.log (125000000000 / 151963505073) ∧
    -Real.log (125000000000 / 151963505073) ≤ (195326657 / 1000000000) := by
  have h := checkLog_sound (w := (26963505073 / 276963505073)) (n := 12)
    (lo := (3051979 / 15625000)) (hi := (195326657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151963505073 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151963505073 / 125000000000) = 1/(125000000000 / 151963505073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6015 : Bounds (3051979 / 15625000) (195326657 / 1000000000) (Real.log (151963505073 / 125000000000)) := by
  have h := reflection_log_6015_neg
  have he : Real.log (151963505073 / 125000000000) = -Real.log (125000000000 / 151963505073) := by
    rw [show ((151963505073 / 125000000000) : ℝ) = ((125000000000 / 151963505073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0094 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6016_neg : (12222203 / 31250000) ≤ -Real.log (100000000000 / 147862188623) ∧
    -Real.log (100000000000 / 147862188623) ≤ (391110497 / 1000000000) := by
  have h := checkLog_sound (w := (47862188623 / 247862188623)) (n := 12)
    (lo := (12222203 / 31250000)) (hi := (391110497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147862188623 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147862188623 / 100000000000) = 1/(100000000000 / 147862188623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6016 : Bounds (12222203 / 31250000) (391110497 / 1000000000) (Real.log (147862188623 / 100000000000)) := by
  have h := reflection_log_6016_neg
  have he : Real.log (147862188623 / 100000000000) = -Real.log (100000000000 / 147862188623) := by
    rw [show ((147862188623 / 100000000000) : ℝ) = ((100000000000 / 147862188623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6017_neg : (195659123 / 500000000) ≤ -Real.log (250000000000 / 369732275657) ∧
    -Real.log (250000000000 / 369732275657) ≤ (391318247 / 1000000000) := by
  have h := checkLog_sound (w := (119732275657 / 619732275657)) (n := 12)
    (lo := (195659123 / 500000000)) (hi := (391318247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369732275657 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369732275657 / 250000000000) = 1/(250000000000 / 369732275657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6017 : Bounds (195659123 / 500000000) (391318247 / 1000000000) (Real.log (369732275657 / 250000000000)) := by
  have h := reflection_log_6017_neg
  have he : Real.log (369732275657 / 250000000000) = -Real.log (250000000000 / 369732275657) := by
    rw [show ((369732275657 / 250000000000) : ℝ) = ((250000000000 / 369732275657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6018_neg : (88361289 / 500000000) ≤ -Real.log (10000 / 11933) ∧
    -Real.log (10000 / 11933) ≤ (176722579 / 1000000000) := by
  have h := checkLog_sound (w := (1933 / 21933)) (n := 12)
    (lo := (88361289 / 500000000)) (hi := (176722579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11933 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11933 / 10000) = 1/(10000 / 11933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6018 : Bounds (88361289 / 500000000) (176722579 / 1000000000) (Real.log (11933 / 10000)) := by
  have h := reflection_log_6018_neg
  have he : Real.log (11933 / 10000) = -Real.log (10000 / 11933) := by
    rw [show ((11933 / 10000) : ℝ) = ((10000 / 11933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6019_neg : (214803427 / 1000000000) ≤ -Real.log (8067 / 10000) ∧
    -Real.log (8067 / 10000) ≤ (53700857 / 250000000) := by
  have h := checkLog_sound (w := (1933 / 18067)) (n := 12)
    (lo := (214803427 / 1000000000)) (hi := (53700857 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8067) = 1/(8067 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6019 : Bounds (-53700857 / 250000000) (-214803427 / 1000000000) (Real.log (8067 / 10000)) := by
  have h := reflection_log_6019_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6020_neg : (193281 / 1000000000) ≤ -Real.log (10000000 / 10001933) ∧
    -Real.log (10000000 / 10001933) ≤ (96641 / 500000000) := by
  have h := checkLog_sound (w := (1933 / 20001933)) (n := 12)
    (lo := (193281 / 1000000000)) (hi := (96641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001933 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001933 / 10000000) = 1/(10000000 / 10001933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6020 : Bounds (193281 / 1000000000) (96641 / 500000000) (Real.log (10001933 / 10000000)) := by
  have h := reflection_log_6020_neg
  have he : Real.log (10001933 / 10000000) = -Real.log (10000000 / 10001933) := by
    rw [show ((10001933 / 10000000) : ℝ) = ((10000000 / 10001933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6021_neg : (96659 / 500000000) ≤ -Real.log (9998067 / 10000000) ∧
    -Real.log (9998067 / 10000000) ≤ (193319 / 1000000000) := by
  have h := checkLog_sound (w := (1933 / 19998067)) (n := 12)
    (lo := (96659 / 500000000)) (hi := (193319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998067) = 1/(9998067 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6021 : Bounds (-193319 / 1000000000) (-96659 / 500000000) (Real.log (9998067 / 10000000)) := by
  have h := reflection_log_6021_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6022_neg : (46362967 / 500000000) ≤ -Real.log (1000000 / 1097161) ∧
    -Real.log (1000000 / 1097161) ≤ (18545187 / 200000000) := by
  have h := checkLog_sound (w := (97161 / 2097161)) (n := 12)
    (lo := (46362967 / 500000000)) (hi := (18545187 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097161 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097161 / 1000000) = 1/(1000000 / 1097161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6022 : Bounds (46362967 / 500000000) (18545187 / 200000000) (Real.log (1097161 / 1000000)) := by
  have h := reflection_log_6022_neg
  have he : Real.log (1097161 / 1000000) = -Real.log (1000000 / 1097161) := by
    rw [show ((1097161 / 1000000) : ℝ) = ((1000000 / 1097161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6023_neg : (25552759 / 250000000) ≤ -Real.log (902839 / 1000000) ∧
    -Real.log (902839 / 1000000) ≤ (102211037 / 1000000000) := by
  have h := checkLog_sound (w := (97161 / 1902839)) (n := 12)
    (lo := (25552759 / 250000000)) (hi := (102211037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902839) = 1/(902839 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6023 : Bounds (-102211037 / 1000000000) (-25552759 / 250000000) (Real.log (902839 / 1000000)) := by
  have h := reflection_log_6023_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6024_neg : (92948301 / 1000000000) ≤ -Real.log (200000 / 219481) ∧
    -Real.log (200000 / 219481) ≤ (46474151 / 500000000) := by
  have h := checkLog_sound (w := (19481 / 419481)) (n := 12)
    (lo := (92948301 / 1000000000)) (hi := (46474151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219481 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219481 / 200000) = 1/(200000 / 219481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6024 : Bounds (92948301 / 1000000000) (46474151 / 500000000) (Real.log (219481 / 200000)) := by
  have h := reflection_log_6024_neg
  have he : Real.log (219481 / 200000) = -Real.log (200000 / 219481) := by
    rw [show ((219481 / 200000) : ℝ) = ((200000 / 219481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6025_neg : (102481331 / 1000000000) ≤ -Real.log (180519 / 200000) ∧
    -Real.log (180519 / 200000) ≤ (25620333 / 250000000) := by
  have h := checkLog_sound (w := (19481 / 380519)) (n := 12)
    (lo := (102481331 / 1000000000)) (hi := (25620333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180519) = 1/(180519 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6025 : Bounds (-25620333 / 250000000) (-102481331 / 1000000000) (Real.log (180519 / 200000)) := by
  have h := reflection_log_6025_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6026_neg : (9533029 / 1000000000) ≤ -Real.log (39620490639 / 40000000000) ∧
    -Real.log (39620490639 / 40000000000) ≤ (953303 / 100000000) := by
  have h := checkLog_sound (w := (379509361 / 79620490639)) (n := 12)
    (lo := (9533029 / 1000000000)) (hi := (953303 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39620490639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39620490639) = 1/(39620490639 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6026 : Bounds (-953303 / 100000000) (-9533029 / 1000000000) (Real.log (39620490639 / 40000000000)) := by
  have h := reflection_log_6026_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6027_neg : (9485101 / 1000000000) ≤ -Real.log (990559740079 / 1000000000000) ∧
    -Real.log (990559740079 / 1000000000000) ≤ (4742551 / 500000000) := by
  have h := checkLog_sound (w := (9440259921 / 1990559740079)) (n := 12)
    (lo := (9485101 / 1000000000)) (hi := (4742551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990559740079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990559740079) = 1/(990559740079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6027 : Bounds (-4742551 / 500000000) (-9485101 / 1000000000) (Real.log (990559740079 / 1000000000000)) := by
  have h := reflection_log_6027_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6028_neg : (19493697 / 100000000) ≤ -Real.log (250000000000 / 303808597103) ∧
    -Real.log (250000000000 / 303808597103) ≤ (194936971 / 1000000000) := by
  have h := checkLog_sound (w := (53808597103 / 553808597103)) (n := 12)
    (lo := (19493697 / 100000000)) (hi := (194936971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303808597103 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303808597103 / 250000000000) = 1/(250000000000 / 303808597103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6028 : Bounds (19493697 / 100000000) (194936971 / 1000000000) (Real.log (303808597103 / 250000000000)) := by
  have h := reflection_log_6028_neg
  have he : Real.log (303808597103 / 250000000000) = -Real.log (250000000000 / 303808597103) := by
    rw [show ((303808597103 / 250000000000) : ℝ) = ((250000000000 / 303808597103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6029_neg : (195429633 / 1000000000) ≤ -Real.log (125000000000 / 151979154549) ∧
    -Real.log (125000000000 / 151979154549) ≤ (97714817 / 500000000) := by
  have h := checkLog_sound (w := (26979154549 / 276979154549)) (n := 12)
    (lo := (195429633 / 1000000000)) (hi := (97714817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151979154549 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151979154549 / 125000000000) = 1/(125000000000 / 151979154549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6029 : Bounds (195429633 / 1000000000) (97714817 / 500000000) (Real.log (151979154549 / 125000000000)) := by
  have h := reflection_log_6029_neg
  have he : Real.log (151979154549 / 125000000000) = -Real.log (125000000000 / 151979154549) := by
    rw [show ((151979154549 / 125000000000) : ℝ) = ((125000000000 / 151979154549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6030_neg : (195659123 / 500000000) ≤ -Real.log (500000000000 / 739464551313) ∧
    -Real.log (500000000000 / 739464551313) ≤ (391318247 / 1000000000) := by
  have h := checkLog_sound (w := (239464551313 / 1239464551313)) (n := 12)
    (lo := (195659123 / 500000000)) (hi := (391318247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739464551313 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739464551313 / 500000000000) = 1/(500000000000 / 739464551313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6030 : Bounds (195659123 / 500000000) (391318247 / 1000000000) (Real.log (739464551313 / 500000000000)) := by
  have h := reflection_log_6030_neg
  have he : Real.log (739464551313 / 500000000000) = -Real.log (500000000000 / 739464551313) := by
    rw [show ((739464551313 / 500000000000) : ℝ) = ((500000000000 / 739464551313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6031_neg : (78305201 / 200000000) ≤ -Real.log (125000000000 / 184904549399) ∧
    -Real.log (125000000000 / 184904549399) ≤ (195763003 / 500000000) := by
  have h := checkLog_sound (w := (59904549399 / 309904549399)) (n := 12)
    (lo := (78305201 / 200000000)) (hi := (195763003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184904549399 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184904549399 / 125000000000) = 1/(125000000000 / 184904549399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6031 : Bounds (78305201 / 200000000) (195763003 / 500000000) (Real.log (184904549399 / 125000000000)) := by
  have h := reflection_log_6031_neg
  have he : Real.log (184904549399 / 125000000000) = -Real.log (125000000000 / 184904549399) := by
    rw [show ((184904549399 / 125000000000) : ℝ) = ((125000000000 / 184904549399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6032_neg : (22100797 / 125000000) ≤ -Real.log (5000 / 5967) ∧
    -Real.log (5000 / 5967) ≤ (176806377 / 1000000000) := by
  have h := checkLog_sound (w := (967 / 10967)) (n := 12)
    (lo := (22100797 / 125000000)) (hi := (176806377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5967 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5967 / 5000) = 1/(5000 / 5967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6032 : Bounds (22100797 / 125000000) (176806377 / 1000000000) (Real.log (5967 / 5000)) := by
  have h := reflection_log_6032_neg
  have he : Real.log (5967 / 5000) = -Real.log (5000 / 5967) := by
    rw [show ((5967 / 5000) : ℝ) = ((5000 / 5967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6033_neg : (53731849 / 250000000) ≤ -Real.log (4033 / 5000) ∧
    -Real.log (4033 / 5000) ≤ (214927397 / 1000000000) := by
  have h := checkLog_sound (w := (967 / 9033)) (n := 12)
    (lo := (53731849 / 250000000)) (hi := (214927397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4033) = 1/(4033 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6033 : Bounds (-214927397 / 1000000000) (-53731849 / 250000000) (Real.log (4033 / 5000)) := by
  have h := reflection_log_6033_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6034_neg : (193381 / 1000000000) ≤ -Real.log (5000000 / 5000967) ∧
    -Real.log (5000000 / 5000967) ≤ (96691 / 500000000) := by
  have h := checkLog_sound (w := (967 / 10000967)) (n := 12)
    (lo := (193381 / 1000000000)) (hi := (96691 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000967 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000967 / 5000000) = 1/(5000000 / 5000967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6034 : Bounds (193381 / 1000000000) (96691 / 500000000) (Real.log (5000967 / 5000000)) := by
  have h := reflection_log_6034_neg
  have he : Real.log (5000967 / 5000000) = -Real.log (5000000 / 5000967) := by
    rw [show ((5000967 / 5000000) : ℝ) = ((5000000 / 5000967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6035_neg : (96709 / 500000000) ≤ -Real.log (4999033 / 5000000) ∧
    -Real.log (4999033 / 5000000) ≤ (193419 / 1000000000) := by
  have h := checkLog_sound (w := (967 / 9999033)) (n := 12)
    (lo := (96709 / 500000000)) (hi := (193419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999033) = 1/(4999033 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6035 : Bounds (-193419 / 1000000000) (-96709 / 500000000) (Real.log (4999033 / 5000000)) := by
  have h := reflection_log_6035_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6036_neg : (1449569 / 15625000) ≤ -Real.log (250000 / 274303) ∧
    -Real.log (250000 / 274303) ≤ (92772417 / 1000000000) := by
  have h := checkLog_sound (w := (24303 / 524303)) (n := 12)
    (lo := (1449569 / 15625000)) (hi := (92772417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274303 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274303 / 250000) = 1/(250000 / 274303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6036 : Bounds (1449569 / 15625000) (92772417 / 1000000000) (Real.log (274303 / 250000)) := by
  have h := reflection_log_6036_neg
  have he : Real.log (274303 / 250000) = -Real.log (250000 / 274303) := by
    rw [show ((274303 / 250000) : ℝ) = ((250000 / 274303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6037_neg : (51133763 / 500000000) ≤ -Real.log (225697 / 250000) ∧
    -Real.log (225697 / 250000) ≤ (102267527 / 1000000000) := by
  have h := checkLog_sound (w := (24303 / 475697)) (n := 12)
    (lo := (51133763 / 500000000)) (hi := (102267527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225697) = 1/(225697 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6037 : Bounds (-102267527 / 1000000000) (-51133763 / 500000000) (Real.log (225697 / 250000)) := by
  have h := reflection_log_6037_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6038_neg : (46497387 / 500000000) ≤ -Real.log (62500 / 68591) ∧
    -Real.log (62500 / 68591) ≤ (3719791 / 40000000) := by
  have h := checkLog_sound (w := (6091 / 131091)) (n := 12)
    (lo := (46497387 / 500000000)) (hi := (3719791 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68591 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68591 / 62500) = 1/(62500 / 68591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6038 : Bounds (46497387 / 500000000) (3719791 / 40000000) (Real.log (68591 / 62500)) := by
  have h := reflection_log_6038_neg
  have he : Real.log (68591 / 62500) = -Real.log (62500 / 68591) := by
    rw [show ((68591 / 62500) : ℝ) = ((62500 / 68591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6039_neg : (25634459 / 250000000) ≤ -Real.log (56409 / 62500) ∧
    -Real.log (56409 / 62500) ≤ (102537837 / 1000000000) := by
  have h := checkLog_sound (w := (6091 / 118909)) (n := 12)
    (lo := (25634459 / 250000000)) (hi := (102537837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56409) = 1/(56409 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6039 : Bounds (-102537837 / 1000000000) (-25634459 / 250000000) (Real.log (56409 / 62500)) := by
  have h := reflection_log_6039_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6040_neg : (4771531 / 500000000) ≤ -Real.log (3869149719 / 3906250000) ∧
    -Real.log (3869149719 / 3906250000) ≤ (9543063 / 1000000000) := by
  have h := checkLog_sound (w := (37100281 / 7775399719)) (n := 12)
    (lo := (4771531 / 500000000)) (hi := (9543063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3869149719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3869149719) = 1/(3869149719 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6040 : Bounds (-9543063 / 1000000000) (-4771531 / 500000000) (Real.log (3869149719 / 3906250000)) := by
  have h := reflection_log_6040_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6041_neg : (9495109 / 1000000000) ≤ -Real.log (61909364191 / 62500000000) ∧
    -Real.log (61909364191 / 62500000000) ≤ (949511 / 100000000) := by
  have h := checkLog_sound (w := (590635809 / 124409364191)) (n := 12)
    (lo := (9495109 / 1000000000)) (hi := (949511 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61909364191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61909364191) = 1/(61909364191 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6041 : Bounds (-949511 / 100000000) (-9495109 / 1000000000) (Real.log (61909364191 / 62500000000)) := by
  have h := reflection_log_6041_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6042_neg : (195039943 / 1000000000) ≤ -Real.log (500000000000 / 607679765349) ∧
    -Real.log (500000000000 / 607679765349) ≤ (24379993 / 125000000) := by
  have h := checkLog_sound (w := (107679765349 / 1107679765349)) (n := 12)
    (lo := (195039943 / 1000000000)) (hi := (24379993 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607679765349 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607679765349 / 500000000000) = 1/(500000000000 / 607679765349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6042 : Bounds (195039943 / 1000000000) (24379993 / 125000000) (Real.log (607679765349 / 500000000000)) := by
  have h := reflection_log_6042_neg
  have he : Real.log (607679765349 / 500000000000) = -Real.log (500000000000 / 607679765349) := by
    rw [show ((607679765349 / 500000000000) : ℝ) = ((500000000000 / 607679765349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6043_neg : (19553261 / 100000000) ≤ -Real.log (250000000000 / 303989611587) ∧
    -Real.log (250000000000 / 303989611587) ≤ (195532611 / 1000000000) := by
  have h := checkLog_sound (w := (53989611587 / 553989611587)) (n := 12)
    (lo := (19553261 / 100000000)) (hi := (195532611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303989611587 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303989611587 / 250000000000) = 1/(250000000000 / 303989611587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6043 : Bounds (19553261 / 100000000) (195532611 / 1000000000) (Real.log (303989611587 / 250000000000)) := by
  have h := reflection_log_6043_neg
  have he : Real.log (303989611587 / 250000000000) = -Real.log (250000000000 / 303989611587) := by
    rw [show ((303989611587 / 250000000000) : ℝ) = ((250000000000 / 303989611587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6044_neg : (78305201 / 200000000) ≤ -Real.log (100000000000 / 147923639519) ∧
    -Real.log (100000000000 / 147923639519) ≤ (195763003 / 500000000) := by
  have h := checkLog_sound (w := (47923639519 / 247923639519)) (n := 12)
    (lo := (78305201 / 200000000)) (hi := (195763003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147923639519 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147923639519 / 100000000000) = 1/(100000000000 / 147923639519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6044 : Bounds (78305201 / 200000000) (195763003 / 500000000) (Real.log (147923639519 / 100000000000)) := by
  have h := reflection_log_6044_neg
  have he : Real.log (147923639519 / 100000000000) = -Real.log (100000000000 / 147923639519) := by
    rw [show ((147923639519 / 100000000000) : ℝ) = ((100000000000 / 147923639519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6045_neg : (97933443 / 250000000) ≤ -Real.log (250000000000 / 369885940987) ∧
    -Real.log (250000000000 / 369885940987) ≤ (391733773 / 1000000000) := by
  have h := checkLog_sound (w := (119885940987 / 619885940987)) (n := 12)
    (lo := (97933443 / 250000000)) (hi := (391733773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369885940987 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369885940987 / 250000000000) = 1/(250000000000 / 369885940987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6045 : Bounds (97933443 / 250000000) (391733773 / 1000000000) (Real.log (369885940987 / 250000000000)) := by
  have h := reflection_log_6045_neg
  have he : Real.log (369885940987 / 250000000000) = -Real.log (250000000000 / 369885940987) := by
    rw [show ((369885940987 / 250000000000) : ℝ) = ((250000000000 / 369885940987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6046_neg : (88445083 / 500000000) ≤ -Real.log (2000 / 2387) ∧
    -Real.log (2000 / 2387) ≤ (176890167 / 1000000000) := by
  have h := checkLog_sound (w := (387 / 4387)) (n := 12)
    (lo := (88445083 / 500000000)) (hi := (176890167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2387 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2387 / 2000) = 1/(2000 / 2387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6046 : Bounds (88445083 / 500000000) (176890167 / 1000000000) (Real.log (2387 / 2000)) := by
  have h := reflection_log_6046_neg
  have he : Real.log (2387 / 2000) = -Real.log (2000 / 2387) := by
    rw [show ((2387 / 2000) : ℝ) = ((2000 / 2387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6047_neg : (215051381 / 1000000000) ≤ -Real.log (1613 / 2000) ∧
    -Real.log (1613 / 2000) ≤ (107525691 / 500000000) := by
  have h := checkLog_sound (w := (387 / 3613)) (n := 12)
    (lo := (215051381 / 1000000000)) (hi := (107525691 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1613) = 1/(1613 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6047 : Bounds (-107525691 / 500000000) (-215051381 / 1000000000) (Real.log (1613 / 2000)) := by
  have h := reflection_log_6047_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6048_neg : (193481 / 1000000000) ≤ -Real.log (2000000 / 2000387) ∧
    -Real.log (2000000 / 2000387) ≤ (96741 / 500000000) := by
  have h := checkLog_sound (w := (387 / 4000387)) (n := 12)
    (lo := (193481 / 1000000000)) (hi := (96741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000387 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000387 / 2000000) = 1/(2000000 / 2000387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6048 : Bounds (193481 / 1000000000) (96741 / 500000000) (Real.log (2000387 / 2000000)) := by
  have h := reflection_log_6048_neg
  have he : Real.log (2000387 / 2000000) = -Real.log (2000000 / 2000387) := by
    rw [show ((2000387 / 2000000) : ℝ) = ((2000000 / 2000387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6049_neg : (96759 / 500000000) ≤ -Real.log (1999613 / 2000000) ∧
    -Real.log (1999613 / 2000000) ≤ (193519 / 1000000000) := by
  have h := checkLog_sound (w := (387 / 3999613)) (n := 12)
    (lo := (96759 / 500000000)) (hi := (193519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999613) = 1/(1999613 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6049 : Bounds (-193519 / 1000000000) (-96759 / 500000000) (Real.log (1999613 / 2000000)) := by
  have h := reflection_log_6049_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6050_neg : (92818897 / 1000000000) ≤ -Real.log (1000000 / 1097263) ∧
    -Real.log (1000000 / 1097263) ≤ (46409449 / 500000000) := by
  have h := checkLog_sound (w := (97263 / 2097263)) (n := 12)
    (lo := (92818897 / 1000000000)) (hi := (46409449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097263 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097263 / 1000000) = 1/(1000000 / 1097263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6050 : Bounds (92818897 / 1000000000) (46409449 / 500000000) (Real.log (1097263 / 1000000)) := by
  have h := reflection_log_6050_neg
  have he : Real.log (1097263 / 1000000) = -Real.log (1000000 / 1097263) := by
    rw [show ((1097263 / 1000000) : ℝ) = ((1000000 / 1097263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6051_neg : (102324019 / 1000000000) ≤ -Real.log (902737 / 1000000) ∧
    -Real.log (902737 / 1000000) ≤ (5116201 / 50000000) := by
  have h := checkLog_sound (w := (97263 / 1902737)) (n := 12)
    (lo := (102324019 / 1000000000)) (hi := (5116201 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902737) = 1/(902737 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6051 : Bounds (-5116201 / 50000000) (-102324019 / 1000000000) (Real.log (902737 / 1000000)) := by
  have h := reflection_log_6051_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6052_neg : (23260311 / 250000000) ≤ -Real.log (1000000 / 1097507) ∧
    -Real.log (1000000 / 1097507) ≤ (18608249 / 200000000) := by
  have h := checkLog_sound (w := (97507 / 2097507)) (n := 12)
    (lo := (23260311 / 250000000)) (hi := (18608249 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097507 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097507 / 1000000) = 1/(1000000 / 1097507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6052 : Bounds (23260311 / 250000000) (18608249 / 200000000) (Real.log (1097507 / 1000000)) := by
  have h := reflection_log_6052_neg
  have he : Real.log (1097507 / 1000000) = -Real.log (1000000 / 1097507) := by
    rw [show ((1097507 / 1000000) : ℝ) = ((1000000 / 1097507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6053_neg : (20518869 / 200000000) ≤ -Real.log (902493 / 1000000) ∧
    -Real.log (902493 / 1000000) ≤ (51297173 / 500000000) := by
  have h := checkLog_sound (w := (97507 / 1902493)) (n := 12)
    (lo := (20518869 / 200000000)) (hi := (51297173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902493) = 1/(902493 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6053 : Bounds (-51297173 / 500000000) (-20518869 / 200000000) (Real.log (902493 / 1000000)) := by
  have h := reflection_log_6053_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6054_neg : (95531 / 10000000) ≤ -Real.log (990492384951 / 1000000000000) ∧
    -Real.log (990492384951 / 1000000000000) ≤ (9553101 / 1000000000) := by
  have h := checkLog_sound (w := (9507615049 / 1990492384951)) (n := 12)
    (lo := (95531 / 10000000)) (hi := (9553101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990492384951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990492384951) = 1/(990492384951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6054 : Bounds (-9553101 / 1000000000) (-95531 / 10000000) (Real.log (990492384951 / 1000000000000)) := by
  have h := reflection_log_6054_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6055_neg : (4752561 / 500000000) ≤ -Real.log (990539908831 / 1000000000000) ∧
    -Real.log (990539908831 / 1000000000000) ≤ (9505123 / 1000000000) := by
  have h := checkLog_sound (w := (9460091169 / 1990539908831)) (n := 12)
    (lo := (4752561 / 500000000)) (hi := (9505123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990539908831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990539908831) = 1/(990539908831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6055 : Bounds (-9505123 / 1000000000) (-4752561 / 500000000) (Real.log (990539908831 / 1000000000000)) := by
  have h := reflection_log_6055_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6056_neg : (48785729 / 250000000) ≤ -Real.log (500000000000 / 607742343561) ∧
    -Real.log (500000000000 / 607742343561) ≤ (195142917 / 1000000000) := by
  have h := checkLog_sound (w := (107742343561 / 1107742343561)) (n := 12)
    (lo := (48785729 / 250000000)) (hi := (195142917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607742343561 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607742343561 / 500000000000) = 1/(500000000000 / 607742343561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6056 : Bounds (48785729 / 250000000) (195142917 / 1000000000) (Real.log (607742343561 / 500000000000)) := by
  have h := reflection_log_6056_neg
  have he : Real.log (607742343561 / 500000000000) = -Real.log (500000000000 / 607742343561) := by
    rw [show ((607742343561 / 500000000000) : ℝ) = ((500000000000 / 607742343561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6057_neg : (195635589 / 1000000000) ≤ -Real.log (125000000000 / 152010458807) ∧
    -Real.log (125000000000 / 152010458807) ≤ (19563559 / 100000000) := by
  have h := checkLog_sound (w := (27010458807 / 277010458807)) (n := 12)
    (lo := (195635589 / 1000000000)) (hi := (19563559 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152010458807 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152010458807 / 125000000000) = 1/(125000000000 / 152010458807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6057 : Bounds (195635589 / 1000000000) (19563559 / 100000000) (Real.log (152010458807 / 125000000000)) := by
  have h := reflection_log_6057_neg
  have he : Real.log (152010458807 / 125000000000) = -Real.log (125000000000 / 152010458807) := by
    rw [show ((152010458807 / 125000000000) : ℝ) = ((125000000000 / 152010458807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6058_neg : (97933443 / 250000000) ≤ -Real.log (500000000000 / 739771881973) ∧
    -Real.log (500000000000 / 739771881973) ≤ (391733773 / 1000000000) := by
  have h := checkLog_sound (w := (239771881973 / 1239771881973)) (n := 12)
    (lo := (97933443 / 250000000)) (hi := (391733773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739771881973 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739771881973 / 500000000000) = 1/(500000000000 / 739771881973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6058 : Bounds (97933443 / 250000000) (391733773 / 1000000000) (Real.log (739771881973 / 500000000000)) := by
  have h := reflection_log_6058_neg
  have he : Real.log (739771881973 / 500000000000) = -Real.log (500000000000 / 739771881973) := by
    rw [show ((739771881973 / 500000000000) : ℝ) = ((500000000000 / 739771881973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6059_neg : (97985387 / 250000000) ≤ -Real.log (31250000000 / 46245350279) ∧
    -Real.log (31250000000 / 46245350279) ≤ (391941549 / 1000000000) := by
  have h := checkLog_sound (w := (14995350279 / 77495350279)) (n := 12)
    (lo := (97985387 / 250000000)) (hi := (391941549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46245350279 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46245350279 / 31250000000) = 1/(31250000000 / 46245350279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6059 : Bounds (97985387 / 250000000) (391941549 / 1000000000) (Real.log (46245350279 / 31250000000)) := by
  have h := reflection_log_6059_neg
  have he : Real.log (46245350279 / 31250000000) = -Real.log (31250000000 / 46245350279) := by
    rw [show ((46245350279 / 31250000000) : ℝ) = ((31250000000 / 46245350279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6060_neg : (3539479 / 20000000) ≤ -Real.log (625 / 746) ∧
    -Real.log (625 / 746) ≤ (176973951 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 1371)) (n := 12)
    (lo := (3539479 / 20000000)) (hi := (176973951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746 / 625) = 1/(625 / 746) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6060 : Bounds (3539479 / 20000000) (176973951 / 1000000000) (Real.log (746 / 625)) := by
  have h := reflection_log_6060_neg
  have he : Real.log (746 / 625) = -Real.log (625 / 746) := by
    rw [show ((746 / 625) : ℝ) = ((625 / 746) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6061_neg : (215175381 / 1000000000) ≤ -Real.log (504 / 625) ∧
    -Real.log (504 / 625) ≤ (107587691 / 500000000) := by
  have h := checkLog_sound (w := (121 / 1129)) (n := 12)
    (lo := (215175381 / 1000000000)) (hi := (107587691 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 504) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 504) = 1/(504 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6061 : Bounds (-107587691 / 500000000) (-215175381 / 1000000000) (Real.log (504 / 625)) := by
  have h := reflection_log_6061_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6062_neg : (193581 / 1000000000) ≤ -Real.log (625000 / 625121) ∧
    -Real.log (625000 / 625121) ≤ (96791 / 500000000) := by
  have h := checkLog_sound (w := (121 / 1250121)) (n := 12)
    (lo := (193581 / 1000000000)) (hi := (96791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625121 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625121 / 625000) = 1/(625000 / 625121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6062 : Bounds (193581 / 1000000000) (96791 / 500000000) (Real.log (625121 / 625000)) := by
  have h := reflection_log_6062_neg
  have he : Real.log (625121 / 625000) = -Real.log (625000 / 625121) := by
    rw [show ((625121 / 625000) : ℝ) = ((625000 / 625121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6063_neg : (96809 / 500000000) ≤ -Real.log (624879 / 625000) ∧
    -Real.log (624879 / 625000) ≤ (193619 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 1249879)) (n := 12)
    (lo := (96809 / 500000000)) (hi := (193619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624879) = 1/(624879 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6063 : Bounds (-193619 / 1000000000) (-96809 / 500000000) (Real.log (624879 / 625000)) := by
  have h := reflection_log_6063_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6064_neg : (742923 / 8000000) ≤ -Real.log (500000 / 548657) ∧
    -Real.log (500000 / 548657) ≤ (2902043 / 31250000) := by
  have h := checkLog_sound (w := (48657 / 1048657)) (n := 12)
    (lo := (742923 / 8000000)) (hi := (2902043 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548657 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548657 / 500000) = 1/(500000 / 548657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6064 : Bounds (742923 / 8000000) (2902043 / 31250000) (Real.log (548657 / 500000)) := by
  have h := reflection_log_6064_neg
  have he : Real.log (548657 / 500000) = -Real.log (500000 / 548657) := by
    rw [show ((548657 / 500000) : ℝ) = ((500000 / 548657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6065_neg : (20476103 / 200000000) ≤ -Real.log (451343 / 500000) ∧
    -Real.log (451343 / 500000) ≤ (25595129 / 250000000) := by
  have h := checkLog_sound (w := (48657 / 951343)) (n := 12)
    (lo := (20476103 / 200000000)) (hi := (25595129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451343) = 1/(451343 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6065 : Bounds (-25595129 / 250000000) (-20476103 / 200000000) (Real.log (451343 / 500000)) := by
  have h := reflection_log_6065_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6066_neg : (93087711 / 1000000000) ≤ -Real.log (500000 / 548779) ∧
    -Real.log (500000 / 548779) ≤ (2908991 / 31250000) := by
  have h := checkLog_sound (w := (48779 / 1048779)) (n := 12)
    (lo := (93087711 / 1000000000)) (hi := (2908991 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548779 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548779 / 500000) = 1/(500000 / 548779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6066 : Bounds (93087711 / 1000000000) (2908991 / 31250000) (Real.log (548779 / 500000)) := by
  have h := reflection_log_6066_neg
  have he : Real.log (548779 / 500000) = -Real.log (500000 / 548779) := by
    rw [show ((548779 / 500000) : ℝ) = ((500000 / 548779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6067_neg : (12831357 / 125000000) ≤ -Real.log (451221 / 500000) ∧
    -Real.log (451221 / 500000) ≤ (102650857 / 1000000000) := by
  have h := checkLog_sound (w := (48779 / 951221)) (n := 12)
    (lo := (12831357 / 125000000)) (hi := (102650857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451221) = 1/(451221 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6067 : Bounds (-102650857 / 1000000000) (-12831357 / 125000000) (Real.log (451221 / 500000)) := by
  have h := reflection_log_6067_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6068_neg : (1195393 / 125000000) ≤ -Real.log (247620609159 / 250000000000) ∧
    -Real.log (247620609159 / 250000000000) ≤ (1912629 / 200000000) := by
  have h := checkLog_sound (w := (2379390841 / 497620609159)) (n := 12)
    (lo := (1195393 / 125000000)) (hi := (1912629 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247620609159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247620609159) = 1/(247620609159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6068 : Bounds (-1912629 / 200000000) (-1195393 / 125000000) (Real.log (247620609159 / 250000000000)) := by
  have h := reflection_log_6068_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6069_neg : (475757 / 50000000) ≤ -Real.log (247632496351 / 250000000000) ∧
    -Real.log (247632496351 / 250000000000) ≤ (9515141 / 1000000000) := by
  have h := checkLog_sound (w := (2367503649 / 497632496351)) (n := 12)
    (lo := (475757 / 50000000)) (hi := (9515141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247632496351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247632496351) = 1/(247632496351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6069 : Bounds (-9515141 / 1000000000) (-475757 / 50000000) (Real.log (247632496351 / 250000000000)) := by
  have h := reflection_log_6069_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6070_neg : (195245891 / 1000000000) ≤ -Real.log (100000000000 / 121560985769) ∧
    -Real.log (100000000000 / 121560985769) ≤ (48811473 / 250000000) := by
  have h := checkLog_sound (w := (21560985769 / 221560985769)) (n := 12)
    (lo := (195245891 / 1000000000)) (hi := (48811473 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121560985769 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121560985769 / 100000000000) = 1/(100000000000 / 121560985769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6070 : Bounds (195245891 / 1000000000) (48811473 / 250000000) (Real.log (121560985769 / 100000000000)) := by
  have h := reflection_log_6070_neg
  have he : Real.log (121560985769 / 100000000000) = -Real.log (100000000000 / 121560985769) := by
    rw [show ((121560985769 / 100000000000) : ℝ) = ((100000000000 / 121560985769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6071_neg : (24467321 / 125000000) ≤ -Real.log (500000000000 / 608104454359) ∧
    -Real.log (500000000000 / 608104454359) ≤ (195738569 / 1000000000) := by
  have h := checkLog_sound (w := (108104454359 / 1108104454359)) (n := 12)
    (lo := (24467321 / 125000000)) (hi := (195738569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608104454359 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608104454359 / 500000000000) = 1/(500000000000 / 608104454359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6071 : Bounds (24467321 / 125000000) (195738569 / 1000000000) (Real.log (608104454359 / 500000000000)) := by
  have h := reflection_log_6071_neg
  have he : Real.log (608104454359 / 500000000000) = -Real.log (500000000000 / 608104454359) := by
    rw [show ((608104454359 / 500000000000) : ℝ) = ((500000000000 / 608104454359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6072_neg : (97985387 / 250000000) ≤ -Real.log (500000000000 / 739925604463) ∧
    -Real.log (500000000000 / 739925604463) ≤ (391941549 / 1000000000) := by
  have h := checkLog_sound (w := (239925604463 / 1239925604463)) (n := 12)
    (lo := (97985387 / 250000000)) (hi := (391941549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739925604463 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739925604463 / 500000000000) = 1/(500000000000 / 739925604463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6072 : Bounds (97985387 / 250000000) (391941549 / 1000000000) (Real.log (739925604463 / 500000000000)) := by
  have h := reflection_log_6072_neg
  have he : Real.log (739925604463 / 500000000000) = -Real.log (500000000000 / 739925604463) := by
    rw [show ((739925604463 / 500000000000) : ℝ) = ((500000000000 / 739925604463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6073_neg : (98037333 / 250000000) ≤ -Real.log (12500000000 / 18501984127) ∧
    -Real.log (12500000000 / 18501984127) ≤ (392149333 / 1000000000) := by
  have h := checkLog_sound (w := (6001984127 / 31001984127)) (n := 12)
    (lo := (98037333 / 250000000)) (hi := (392149333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18501984127 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18501984127 / 12500000000) = 1/(12500000000 / 18501984127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6073 : Bounds (98037333 / 250000000) (392149333 / 1000000000) (Real.log (18501984127 / 12500000000)) := by
  have h := reflection_log_6073_neg
  have he : Real.log (18501984127 / 12500000000) = -Real.log (12500000000 / 18501984127) := by
    rw [show ((18501984127 / 12500000000) : ℝ) = ((12500000000 / 18501984127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6074_neg : (177057727 / 1000000000) ≤ -Real.log (10000 / 11937) ∧
    -Real.log (10000 / 11937) ≤ (2766527 / 15625000) := by
  have h := checkLog_sound (w := (1937 / 21937)) (n := 12)
    (lo := (177057727 / 1000000000)) (hi := (2766527 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11937 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11937 / 10000) = 1/(10000 / 11937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6074 : Bounds (177057727 / 1000000000) (2766527 / 15625000) (Real.log (11937 / 10000)) := by
  have h := reflection_log_6074_neg
  have he : Real.log (11937 / 10000) = -Real.log (10000 / 11937) := by
    rw [show ((11937 / 10000) : ℝ) = ((10000 / 11937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6075_neg : (215299397 / 1000000000) ≤ -Real.log (8063 / 10000) ∧
    -Real.log (8063 / 10000) ≤ (107649699 / 500000000) := by
  have h := checkLog_sound (w := (1937 / 18063)) (n := 12)
    (lo := (215299397 / 1000000000)) (hi := (107649699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8063) = 1/(8063 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6075 : Bounds (-107649699 / 500000000) (-215299397 / 1000000000) (Real.log (8063 / 10000)) := by
  have h := reflection_log_6075_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6076_neg : (193681 / 1000000000) ≤ -Real.log (10000000 / 10001937) ∧
    -Real.log (10000000 / 10001937) ≤ (96841 / 500000000) := by
  have h := checkLog_sound (w := (1937 / 20001937)) (n := 12)
    (lo := (193681 / 1000000000)) (hi := (96841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001937 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001937 / 10000000) = 1/(10000000 / 10001937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6076 : Bounds (193681 / 1000000000) (96841 / 500000000) (Real.log (10001937 / 10000000)) := by
  have h := reflection_log_6076_neg
  have he : Real.log (10001937 / 10000000) = -Real.log (10000000 / 10001937) := by
    rw [show ((10001937 / 10000000) : ℝ) = ((10000000 / 10001937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6077_neg : (96859 / 500000000) ≤ -Real.log (9998063 / 10000000) ∧
    -Real.log (9998063 / 10000000) ≤ (193719 / 1000000000) := by
  have h := checkLog_sound (w := (1937 / 19998063)) (n := 12)
    (lo := (96859 / 500000000)) (hi := (193719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998063) = 1/(9998063 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6077 : Bounds (-193719 / 1000000000) (-96859 / 500000000) (Real.log (9998063 / 10000000)) := by
  have h := reflection_log_6077_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6078_neg : (92911851 / 1000000000) ≤ -Real.log (200000 / 219473) ∧
    -Real.log (200000 / 219473) ≤ (23227963 / 250000000) := by
  have h := checkLog_sound (w := (19473 / 419473)) (n := 12)
    (lo := (92911851 / 1000000000)) (hi := (23227963 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219473 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219473 / 200000) = 1/(200000 / 219473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6078 : Bounds (92911851 / 1000000000) (23227963 / 250000000) (Real.log (219473 / 200000)) := by
  have h := reflection_log_6078_neg
  have he : Real.log (219473 / 200000) = -Real.log (200000 / 219473) := by
    rw [show ((219473 / 200000) : ℝ) = ((200000 / 219473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6079_neg : (20487403 / 200000000) ≤ -Real.log (180527 / 200000) ∧
    -Real.log (180527 / 200000) ≤ (12804627 / 125000000) := by
  have h := checkLog_sound (w := (19473 / 380527)) (n := 12)
    (lo := (20487403 / 200000000)) (hi := (12804627 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180527) = 1/(180527 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6079 : Bounds (-12804627 / 125000000) (-20487403 / 200000000) (Real.log (180527 / 200000)) := by
  have h := reflection_log_6079_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


