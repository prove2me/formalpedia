-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0172__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0172__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T01:55:54.793207+00:00
-- url     : https://prove2.me/theorems/fb5a20fb-e70c-4372-be06-1b8e5f508bb7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0172 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0173, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0172 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0173, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0174)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0172 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0173, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0174)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0172 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0173, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0174) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0172 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0173, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0174).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0172 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11008_neg : (56033823 / 250000000) ≤ -Real.log (799207 / 1000000) ∧
    -Real.log (799207 / 1000000) ≤ (224135293 / 1000000000) := by
  have h := checkLog_sound (w := (200793 / 1799207)) (n := 12)
    (lo := (56033823 / 250000000)) (hi := (224135293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 799207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 799207) = 1/(799207 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11008 : Bounds (-224135293 / 1000000000) (-56033823 / 250000000) (Real.log (799207 / 1000000)) := by
  have h := reflection_log_11008_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11009_neg : (41153121 / 1000000000) ≤ -Real.log (959682171151 / 1000000000000) ∧
    -Real.log (959682171151 / 1000000000000) ≤ (20576561 / 500000000) := by
  have h := checkLog_sound (w := (40317828849 / 1959682171151)) (n := 12)
    (lo := (41153121 / 1000000000)) (hi := (20576561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 959682171151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 959682171151) = 1/(959682171151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11009 : Bounds (-20576561 / 500000000) (-41153121 / 1000000000) (Real.log (959682171151 / 1000000000000)) := by
  have h := reflection_log_11009_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11010_neg : (20383923 / 500000000) ≤ -Real.log (9600519831 / 10000000000) ∧
    -Real.log (9600519831 / 10000000000) ≤ (40767847 / 1000000000) := by
  have h := checkLog_sound (w := (399480169 / 19600519831)) (n := 12)
    (lo := (20383923 / 500000000)) (hi := (40767847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9600519831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9600519831) = 1/(9600519831 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11010 : Bounds (-40767847 / 1000000000) (-20383923 / 500000000) (Real.log (9600519831 / 10000000000)) := by
  have h := reflection_log_11010_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11011_neg : (202597141 / 500000000) ≤ -Real.log (250000000000 / 374898454001) ∧
    -Real.log (250000000000 / 374898454001) ≤ (405194283 / 1000000000) := by
  have h := checkLog_sound (w := (124898454001 / 624898454001)) (n := 12)
    (lo := (202597141 / 500000000)) (hi := (405194283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374898454001 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374898454001 / 250000000000) = 1/(250000000000 / 374898454001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11011 : Bounds (202597141 / 500000000) (405194283 / 1000000000) (Real.log (374898454001 / 250000000000)) := by
  have h := reflection_log_11011_neg
  have he : Real.log (374898454001 / 250000000000) = -Real.log (250000000000 / 374898454001) := by
    rw [show ((374898454001 / 250000000000) : ℝ) = ((250000000000 / 374898454001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11012_neg : (50889683 / 125000000) ≤ -Real.log (25000000000 / 37562014597) ∧
    -Real.log (25000000000 / 37562014597) ≤ (81423493 / 200000000) := by
  have h := checkLog_sound (w := (12562014597 / 62562014597)) (n := 12)
    (lo := (50889683 / 125000000)) (hi := (81423493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37562014597 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37562014597 / 25000000000) = 1/(25000000000 / 37562014597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11012 : Bounds (50889683 / 125000000) (81423493 / 200000000) (Real.log (37562014597 / 25000000000)) := by
  have h := reflection_log_11012_neg
  have he : Real.log (37562014597 / 25000000000) = -Real.log (25000000000 / 37562014597) := by
    rw [show ((37562014597 / 25000000000) : ℝ) = ((25000000000 / 37562014597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11013_neg : (821242383 / 1000000000) ≤ -Real.log (500000000000 / 1136661211129) ∧
    -Real.log (500000000000 / 1136661211129) ≤ (164248477 / 200000000) := by
  have h := checkLog_sound (w := (136661211129 / 2136661211129)) (n := 12)
    (lo := (128095203 / 1000000000)) (hi := (32023801 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1136661211129 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1136661211129 / 1000000000000) = 1/(500000000000 / 1136661211129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11013 : Bounds (821242383 / 1000000000) (164248477 / 200000000) (Real.log (1136661211129 / 500000000000)) := by
  have h := reflection_log_11013_neg
  have he : Real.log (1136661211129 / 500000000000) = -Real.log (500000000000 / 1136661211129) := by
    rw [show ((1136661211129 / 500000000000) : ℝ) = ((500000000000 / 1136661211129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11014_neg : (205900017 / 250000000) ≤ -Real.log (62500000000 / 142418032787) ∧
    -Real.log (62500000000 / 142418032787) ≤ (82360007 / 100000000) := by
  have h := checkLog_sound (w := (17418032787 / 267418032787)) (n := 12)
    (lo := (16306611 / 125000000)) (hi := (130452889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142418032787 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(142418032787 / 125000000000) = 1/(62500000000 / 142418032787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11014 : Bounds (205900017 / 250000000) (82360007 / 100000000) (Real.log (142418032787 / 62500000000)) := by
  have h := reflection_log_11014_neg
  have he : Real.log (142418032787 / 62500000000) = -Real.log (62500000000 / 142418032787) := by
    rw [show ((142418032787 / 62500000000) : ℝ) = ((62500000000 / 142418032787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11015_neg : (644576 / 1953125) ≤ -Real.log (1000 / 1391) ∧
    -Real.log (1000 / 1391) ≤ (330022913 / 1000000000) := by
  have h := checkLog_sound (w := (391 / 2391)) (n := 12)
    (lo := (644576 / 1953125)) (hi := (330022913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1391 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1391 / 1000) = 1/(1000 / 1391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11015 : Bounds (644576 / 1953125) (330022913 / 1000000000) (Real.log (1391 / 1000)) := by
  have h := reflection_log_11015_neg
  have he : Real.log (1391 / 1000) = -Real.log (1000 / 1391) := by
    rw [show ((1391 / 1000) : ℝ) = ((1000 / 1391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11016_neg : (495937011 / 1000000000) ≤ -Real.log (609 / 1000) ∧
    -Real.log (609 / 1000) ≤ (123984253 / 250000000) := by
  have h := checkLog_sound (w := (391 / 1609)) (n := 12)
    (lo := (495937011 / 1000000000)) (hi := (123984253 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 609) = 1/(609 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11016 : Bounds (-123984253 / 250000000) (-495937011 / 1000000000) (Real.log (609 / 1000)) := by
  have h := reflection_log_11016_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11017_neg : (390923 / 1000000000) ≤ -Real.log (1000000 / 1000391) ∧
    -Real.log (1000000 / 1000391) ≤ (97731 / 250000000) := by
  have h := checkLog_sound (w := (391 / 2000391)) (n := 12)
    (lo := (390923 / 1000000000)) (hi := (97731 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000391 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000391 / 1000000) = 1/(1000000 / 1000391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11017 : Bounds (390923 / 1000000000) (97731 / 250000000) (Real.log (1000391 / 1000000)) := by
  have h := reflection_log_11017_neg
  have he : Real.log (1000391 / 1000000) = -Real.log (1000000 / 1000391) := by
    rw [show ((1000391 / 1000000) : ℝ) = ((1000000 / 1000391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11018_neg : (97769 / 250000000) ≤ -Real.log (999609 / 1000000) ∧
    -Real.log (999609 / 1000000) ≤ (391077 / 1000000000) := by
  have h := checkLog_sound (w := (391 / 1999609)) (n := 12)
    (lo := (97769 / 250000000)) (hi := (391077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999609) = 1/(999609 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11018 : Bounds (-391077 / 1000000000) (-97769 / 250000000) (Real.log (999609 / 1000000)) := by
  have h := reflection_log_11018_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11019_neg : (182666497 / 1000000000) ≤ -Real.log (500000 / 600207) ∧
    -Real.log (500000 / 600207) ≤ (91333249 / 500000000) := by
  have h := checkLog_sound (w := (100207 / 1100207)) (n := 12)
    (lo := (182666497 / 1000000000)) (hi := (91333249 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600207 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600207 / 500000) = 1/(500000 / 600207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11019 : Bounds (182666497 / 1000000000) (91333249 / 500000000) (Real.log (600207 / 500000)) := by
  have h := reflection_log_11019_neg
  have he : Real.log (600207 / 500000) = -Real.log (500000 / 600207) := by
    rw [show ((600207 / 500000) : ℝ) = ((500000 / 600207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11020_neg : (44732237 / 200000000) ≤ -Real.log (399793 / 500000) ∧
    -Real.log (399793 / 500000) ≤ (111830593 / 500000000) := by
  have h := checkLog_sound (w := (100207 / 899793)) (n := 12)
    (lo := (44732237 / 200000000)) (hi := (111830593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 399793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 399793) = 1/(399793 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11020 : Bounds (-111830593 / 500000000) (-44732237 / 200000000) (Real.log (399793 / 500000)) := by
  have h := reflection_log_11020_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11021_neg : (36687187 / 200000000) ≤ -Real.log (500000 / 600669) ∧
    -Real.log (500000 / 600669) ≤ (5732373 / 31250000) := by
  have h := checkLog_sound (w := (100669 / 1100669)) (n := 12)
    (lo := (36687187 / 200000000)) (hi := (5732373 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600669 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600669 / 500000) = 1/(500000 / 600669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11021 : Bounds (36687187 / 200000000) (5732373 / 31250000) (Real.log (600669 / 500000)) := by
  have h := reflection_log_11021_neg
  have he : Real.log (600669 / 500000) = -Real.log (500000 / 600669) := by
    rw [show ((600669 / 500000) : ℝ) = ((500000 / 600669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11022_neg : (224817451 / 1000000000) ≤ -Real.log (399331 / 500000) ∧
    -Real.log (399331 / 500000) ≤ (56204363 / 250000000) := by
  have h := checkLog_sound (w := (100669 / 899331)) (n := 12)
    (lo := (224817451 / 1000000000)) (hi := (56204363 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 399331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 399331) = 1/(399331 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11022 : Bounds (-56204363 / 250000000) (-224817451 / 1000000000) (Real.log (399331 / 500000)) := by
  have h := reflection_log_11022_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11023_neg : (8276303 / 200000000) ≤ -Real.log (239865752439 / 250000000000) ∧
    -Real.log (239865752439 / 250000000000) ≤ (10345379 / 250000000) := by
  have h := checkLog_sound (w := (10134247561 / 489865752439)) (n := 12)
    (lo := (8276303 / 200000000)) (hi := (10345379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 239865752439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 239865752439) = 1/(239865752439 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11023 : Bounds (-10345379 / 250000000) (-8276303 / 200000000) (Real.log (239865752439 / 250000000000)) := by
  have h := reflection_log_11023_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11024_neg : (40994687 / 1000000000) ≤ -Real.log (239958557151 / 250000000000) ∧
    -Real.log (239958557151 / 250000000000) ≤ (320271 / 7812500) := by
  have h := checkLog_sound (w := (10041442849 / 489958557151)) (n := 12)
    (lo := (40994687 / 1000000000)) (hi := (320271 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 239958557151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 239958557151) = 1/(239958557151 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11024 : Bounds (-320271 / 7812500) (-40994687 / 1000000000) (Real.log (239958557151 / 250000000000)) := by
  have h := reflection_log_11024_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11025_neg : (203163841 / 500000000) ≤ -Real.log (500000000000 / 750647209931) ∧
    -Real.log (500000000000 / 750647209931) ≤ (406327683 / 1000000000) := by
  have h := checkLog_sound (w := (250647209931 / 1250647209931)) (n := 12)
    (lo := (203163841 / 500000000)) (hi := (406327683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((750647209931 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(750647209931 / 500000000000) = 1/(500000000000 / 750647209931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11025 : Bounds (203163841 / 500000000) (406327683 / 1000000000) (Real.log (750647209931 / 500000000000)) := by
  have h := reflection_log_11025_neg
  have he : Real.log (750647209931 / 500000000000) = -Real.log (500000000000 / 750647209931) := by
    rw [show ((750647209931 / 500000000000) : ℝ) = ((500000000000 / 750647209931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11026_neg : (408253387 / 1000000000) ≤ -Real.log (500000000000 / 752094127429) ∧
    -Real.log (500000000000 / 752094127429) ≤ (102063347 / 250000000) := by
  have h := checkLog_sound (w := (252094127429 / 1252094127429)) (n := 12)
    (lo := (408253387 / 1000000000)) (hi := (102063347 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((752094127429 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(752094127429 / 500000000000) = 1/(500000000000 / 752094127429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11026 : Bounds (408253387 / 1000000000) (102063347 / 250000000) (Real.log (752094127429 / 500000000000)) := by
  have h := reflection_log_11026_neg
  have he : Real.log (752094127429 / 500000000000) = -Real.log (500000000000 / 752094127429) := by
    rw [show ((752094127429 / 500000000000) : ℝ) = ((500000000000 / 752094127429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11027_neg : (205900017 / 250000000) ≤ -Real.log (100000000000 / 227868852459) ∧
    -Real.log (100000000000 / 227868852459) ≤ (82360007 / 100000000) := by
  have h := checkLog_sound (w := (27868852459 / 427868852459)) (n := 12)
    (lo := (16306611 / 125000000)) (hi := (130452889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((227868852459 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(227868852459 / 200000000000) = 1/(100000000000 / 227868852459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11027 : Bounds (205900017 / 250000000) (82360007 / 100000000) (Real.log (227868852459 / 100000000000)) := by
  have h := reflection_log_11027_neg
  have he : Real.log (227868852459 / 100000000000) = -Real.log (100000000000 / 227868852459) := by
    rw [show ((227868852459 / 100000000000) : ℝ) = ((100000000000 / 227868852459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11028_neg : (825959923 / 1000000000) ≤ -Real.log (100000000000 / 228407224959) ∧
    -Real.log (100000000000 / 228407224959) ≤ (33038397 / 40000000) := by
  have h := checkLog_sound (w := (28407224959 / 428407224959)) (n := 12)
    (lo := (132812743 / 1000000000)) (hi := (16601593 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((228407224959 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(228407224959 / 200000000000) = 1/(100000000000 / 228407224959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11028 : Bounds (825959923 / 1000000000) (33038397 / 40000000) (Real.log (228407224959 / 100000000000)) := by
  have h := reflection_log_11028_neg
  have he : Real.log (228407224959 / 100000000000) = -Real.log (100000000000 / 228407224959) := by
    rw [show ((228407224959 / 100000000000) : ℝ) = ((100000000000 / 228407224959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11029_neg : (330741561 / 1000000000) ≤ -Real.log (125 / 174) ∧
    -Real.log (125 / 174) ≤ (165370781 / 500000000) := by
  have h := checkLog_sound (w := (49 / 299)) (n := 12)
    (lo := (330741561 / 1000000000)) (hi := (165370781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(174 / 125) = 1/(125 / 174) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11029 : Bounds (330741561 / 1000000000) (165370781 / 500000000) (Real.log (174 / 125)) := by
  have h := reflection_log_11029_neg
  have he : Real.log (174 / 125) = -Real.log (125 / 174) := by
    rw [show ((174 / 125) : ℝ) = ((125 / 174) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11030_neg : (497580397 / 1000000000) ≤ -Real.log (76 / 125) ∧
    -Real.log (76 / 125) ≤ (248790199 / 500000000) := by
  have h := checkLog_sound (w := (49 / 201)) (n := 12)
    (lo := (497580397 / 1000000000)) (hi := (248790199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 76) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 76) = 1/(76 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11030 : Bounds (-248790199 / 500000000) (-497580397 / 1000000000) (Real.log (76 / 125)) := by
  have h := reflection_log_11030_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11031_neg : (391923 / 1000000000) ≤ -Real.log (125000 / 125049) ∧
    -Real.log (125000 / 125049) ≤ (97981 / 250000000) := by
  have h := checkLog_sound (w := (49 / 250049)) (n := 12)
    (lo := (391923 / 1000000000)) (hi := (97981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125049 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125049 / 125000) = 1/(125000 / 125049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11031 : Bounds (391923 / 1000000000) (97981 / 250000000) (Real.log (125049 / 125000)) := by
  have h := reflection_log_11031_neg
  have he : Real.log (125049 / 125000) = -Real.log (125000 / 125049) := by
    rw [show ((125049 / 125000) : ℝ) = ((125000 / 125049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11032_neg : (98019 / 250000000) ≤ -Real.log (124951 / 125000) ∧
    -Real.log (124951 / 125000) ≤ (392077 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 249951)) (n := 12)
    (lo := (98019 / 250000000)) (hi := (392077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124951) = 1/(124951 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11032 : Bounds (-392077 / 1000000000) (-98019 / 250000000) (Real.log (124951 / 125000)) := by
  have h := reflection_log_11032_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11033_neg : (183119571 / 1000000000) ≤ -Real.log (500000 / 600479) ∧
    -Real.log (500000 / 600479) ≤ (45779893 / 250000000) := by
  have h := checkLog_sound (w := (100479 / 1100479)) (n := 12)
    (lo := (183119571 / 1000000000)) (hi := (45779893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600479 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600479 / 500000) = 1/(500000 / 600479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11033 : Bounds (183119571 / 1000000000) (45779893 / 250000000) (Real.log (600479 / 500000)) := by
  have h := reflection_log_11033_neg
  have he : Real.log (600479 / 500000) = -Real.log (500000 / 600479) := by
    rw [show ((600479 / 500000) : ℝ) = ((500000 / 600479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11034_neg : (28042721 / 125000000) ≤ -Real.log (399521 / 500000) ∧
    -Real.log (399521 / 500000) ≤ (224341769 / 1000000000) := by
  have h := checkLog_sound (w := (100479 / 899521)) (n := 12)
    (lo := (28042721 / 125000000)) (hi := (224341769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 399521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 399521) = 1/(399521 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11034 : Bounds (-224341769 / 1000000000) (-28042721 / 125000000) (Real.log (399521 / 500000)) := by
  have h := reflection_log_11034_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11035_neg : (183889493 / 1000000000) ≤ -Real.log (1000000 / 1201883) ∧
    -Real.log (1000000 / 1201883) ≤ (91944747 / 500000000) := by
  have h := checkLog_sound (w := (201883 / 2201883)) (n := 12)
    (lo := (183889493 / 1000000000)) (hi := (91944747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1201883 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1201883 / 1000000) = 1/(1000000 / 1201883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11035 : Bounds (183889493 / 1000000000) (91944747 / 500000000) (Real.log (1201883 / 1000000)) := by
  have h := reflection_log_11035_neg
  have he : Real.log (1201883 / 1000000) = -Real.log (1000000 / 1201883) := by
    rw [show ((1201883 / 1000000) : ℝ) = ((1000000 / 1201883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11036_neg : (9020003 / 40000000) ≤ -Real.log (798117 / 1000000) ∧
    -Real.log (798117 / 1000000) ≤ (56375019 / 250000000) := by
  have h := checkLog_sound (w := (201883 / 1798117)) (n := 12)
    (lo := (9020003 / 40000000)) (hi := (56375019 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 798117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 798117) = 1/(798117 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11036 : Bounds (-56375019 / 250000000) (-9020003 / 40000000) (Real.log (798117 / 1000000)) := by
  have h := reflection_log_11036_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11037_neg : (20805291 / 500000000) ≤ -Real.log (959243254311 / 1000000000000) ∧
    -Real.log (959243254311 / 1000000000000) ≤ (41610583 / 1000000000) := by
  have h := checkLog_sound (w := (40756745689 / 1959243254311)) (n := 12)
    (lo := (20805291 / 500000000)) (hi := (41610583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 959243254311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 959243254311) = 1/(959243254311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11037 : Bounds (-41610583 / 1000000000) (-20805291 / 500000000) (Real.log (959243254311 / 1000000000000)) := by
  have h := reflection_log_11037_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11038_neg : (41222197 / 1000000000) ≤ -Real.log (239903970559 / 250000000000) ∧
    -Real.log (239903970559 / 250000000000) ≤ (20611099 / 500000000) := by
  have h := checkLog_sound (w := (10096029441 / 489903970559)) (n := 12)
    (lo := (41222197 / 1000000000)) (hi := (20611099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 239903970559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 239903970559) = 1/(239903970559 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11038 : Bounds (-20611099 / 500000000) (-41222197 / 1000000000) (Real.log (239903970559 / 250000000000)) := by
  have h := reflection_log_11038_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11039_neg : (20373067 / 50000000) ≤ -Real.log (62500000000 / 93937333707) ∧
    -Real.log (62500000000 / 93937333707) ≤ (407461341 / 1000000000) := by
  have h := checkLog_sound (w := (31437333707 / 156437333707)) (n := 12)
    (lo := (20373067 / 50000000)) (hi := (407461341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93937333707 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93937333707 / 62500000000) = 1/(62500000000 / 93937333707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11039 : Bounds (20373067 / 50000000) (407461341 / 1000000000) (Real.log (93937333707 / 62500000000)) := by
  have h := reflection_log_11039_neg
  have he : Real.log (93937333707 / 62500000000) = -Real.log (62500000000 / 93937333707) := by
    rw [show ((93937333707 / 62500000000) : ℝ) = ((62500000000 / 93937333707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11040_neg : (409389569 / 1000000000) ≤ -Real.log (500000000000 / 752949129013) ∧
    -Real.log (500000000000 / 752949129013) ≤ (40938957 / 100000000) := by
  have h := checkLog_sound (w := (252949129013 / 1252949129013)) (n := 12)
    (lo := (409389569 / 1000000000)) (hi := (40938957 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((752949129013 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(752949129013 / 500000000000) = 1/(500000000000 / 752949129013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11040 : Bounds (409389569 / 1000000000) (40938957 / 100000000) (Real.log (752949129013 / 500000000000)) := by
  have h := reflection_log_11040_neg
  have he : Real.log (752949129013 / 500000000000) = -Real.log (500000000000 / 752949129013) := by
    rw [show ((752949129013 / 500000000000) : ℝ) = ((500000000000 / 752949129013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11041_neg : (825959923 / 1000000000) ≤ -Real.log (250000000000 / 571018062397) ∧
    -Real.log (250000000000 / 571018062397) ≤ (33038397 / 40000000) := by
  have h := checkLog_sound (w := (71018062397 / 1071018062397)) (n := 12)
    (lo := (132812743 / 1000000000)) (hi := (16601593 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((571018062397 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(571018062397 / 500000000000) = 1/(250000000000 / 571018062397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11041 : Bounds (825959923 / 1000000000) (33038397 / 40000000) (Real.log (571018062397 / 250000000000)) := by
  have h := reflection_log_11041_neg
  have he : Real.log (571018062397 / 250000000000) = -Real.log (250000000000 / 571018062397) := by
    rw [show ((571018062397 / 250000000000) : ℝ) = ((250000000000 / 571018062397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11042_neg : (414160979 / 500000000) ≤ -Real.log (250000000000 / 572368421053) ∧
    -Real.log (250000000000 / 572368421053) ≤ (20708049 / 25000000) := by
  have h := checkLog_sound (w := (72368421053 / 1072368421053)) (n := 12)
    (lo := (67587389 / 500000000)) (hi := (135174779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((572368421053 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(572368421053 / 500000000000) = 1/(250000000000 / 572368421053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11042 : Bounds (414160979 / 500000000) (20708049 / 25000000) (Real.log (572368421053 / 250000000000)) := by
  have h := reflection_log_11042_neg
  have he : Real.log (572368421053 / 250000000000) = -Real.log (250000000000 / 572368421053) := by
    rw [show ((572368421053 / 250000000000) : ℝ) = ((250000000000 / 572368421053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11043_neg : (165729847 / 500000000) ≤ -Real.log (1000 / 1393) ∧
    -Real.log (1000 / 1393) ≤ (66291939 / 200000000) := by
  have h := checkLog_sound (w := (393 / 2393)) (n := 12)
    (lo := (165729847 / 500000000)) (hi := (66291939 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1393 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1393 / 1000) = 1/(1000 / 1393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11043 : Bounds (165729847 / 500000000) (66291939 / 200000000) (Real.log (1393 / 1000)) := by
  have h := reflection_log_11043_neg
  have he : Real.log (1393 / 1000) = -Real.log (1000 / 1393) := by
    rw [show ((1393 / 1000) : ℝ) = ((1000 / 1393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11044_neg : (499226487 / 1000000000) ≤ -Real.log (607 / 1000) ∧
    -Real.log (607 / 1000) ≤ (62403311 / 125000000) := by
  have h := checkLog_sound (w := (393 / 1607)) (n := 12)
    (lo := (499226487 / 1000000000)) (hi := (62403311 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 607) = 1/(607 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11044 : Bounds (-62403311 / 125000000) (-499226487 / 1000000000) (Real.log (607 / 1000)) := by
  have h := reflection_log_11044_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11045_neg : (196461 / 500000000) ≤ -Real.log (1000000 / 1000393) ∧
    -Real.log (1000000 / 1000393) ≤ (392923 / 1000000000) := by
  have h := checkLog_sound (w := (393 / 2000393)) (n := 12)
    (lo := (196461 / 500000000)) (hi := (392923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000393 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000393 / 1000000) = 1/(1000000 / 1000393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11045 : Bounds (196461 / 500000000) (392923 / 1000000000) (Real.log (1000393 / 1000000)) := by
  have h := reflection_log_11045_neg
  have he : Real.log (1000393 / 1000000) = -Real.log (1000000 / 1000393) := by
    rw [show ((1000393 / 1000000) : ℝ) = ((1000000 / 1000393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11046_neg : (393077 / 1000000000) ≤ -Real.log (999607 / 1000000) ∧
    -Real.log (999607 / 1000000) ≤ (196539 / 500000000) := by
  have h := checkLog_sound (w := (393 / 1999607)) (n := 12)
    (lo := (393077 / 1000000000)) (hi := (196539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999607) = 1/(999607 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11046 : Bounds (-196539 / 500000000) (-393077 / 1000000000) (Real.log (999607 / 1000000)) := by
  have h := reflection_log_11046_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11047_neg : (4589311 / 25000000) ≤ -Real.log (500000 / 600751) ∧
    -Real.log (500000 / 600751) ≤ (183572441 / 1000000000) := by
  have h := checkLog_sound (w := (100751 / 1100751)) (n := 12)
    (lo := (4589311 / 25000000)) (hi := (183572441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600751 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600751 / 500000) = 1/(500000 / 600751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11047 : Bounds (4589311 / 25000000) (183572441 / 1000000000) (Real.log (600751 / 500000)) := by
  have h := reflection_log_11047_neg
  have he : Real.log (600751 / 500000) = -Real.log (500000 / 600751) := by
    rw [show ((600751 / 500000) : ℝ) = ((500000 / 600751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11048_neg : (7031963 / 31250000) ≤ -Real.log (399249 / 500000) ∧
    -Real.log (399249 / 500000) ≤ (225022817 / 1000000000) := by
  have h := checkLog_sound (w := (100751 / 899249)) (n := 12)
    (lo := (7031963 / 31250000)) (hi := (225022817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 399249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 399249) = 1/(399249 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11048 : Bounds (-225022817 / 1000000000) (-7031963 / 31250000) (Real.log (399249 / 500000)) := by
  have h := reflection_log_11048_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11049_neg : (184343677 / 1000000000) ≤ -Real.log (1000000 / 1202429) ∧
    -Real.log (1000000 / 1202429) ≤ (92171839 / 500000000) := by
  have h := checkLog_sound (w := (202429 / 2202429)) (n := 12)
    (lo := (184343677 / 1000000000)) (hi := (92171839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1202429 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1202429 / 1000000) = 1/(1000000 / 1202429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11049 : Bounds (184343677 / 1000000000) (92171839 / 500000000) (Real.log (1202429 / 1000000)) := by
  have h := reflection_log_11049_neg
  have he : Real.log (1202429 / 1000000) = -Real.log (1000000 / 1202429) := by
    rw [show ((1202429 / 1000000) : ℝ) = ((1000000 / 1202429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11050_neg : (11309221 / 50000000) ≤ -Real.log (797571 / 1000000) ∧
    -Real.log (797571 / 1000000) ≤ (226184421 / 1000000000) := by
  have h := checkLog_sound (w := (202429 / 1797571)) (n := 12)
    (lo := (11309221 / 50000000)) (hi := (226184421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 797571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 797571) = 1/(797571 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11050 : Bounds (-226184421 / 1000000000) (-11309221 / 50000000) (Real.log (797571 / 1000000)) := by
  have h := reflection_log_11050_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11051_neg : (20920371 / 500000000) ≤ -Real.log (959022499959 / 1000000000000) ∧
    -Real.log (959022499959 / 1000000000000) ≤ (41840743 / 1000000000) := by
  have h := checkLog_sound (w := (40977500041 / 1959022499959)) (n := 12)
    (lo := (20920371 / 500000000)) (hi := (41840743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 959022499959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 959022499959) = 1/(959022499959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11051 : Bounds (-41840743 / 1000000000) (-20920371 / 500000000) (Real.log (959022499959 / 1000000000000)) := by
  have h := reflection_log_11051_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11052_neg : (331603 / 8000000) ≤ -Real.log (239849235999 / 250000000000) ∧
    -Real.log (239849235999 / 250000000000) ≤ (5181297 / 125000000) := by
  have h := checkLog_sound (w := (10150764001 / 489849235999)) (n := 12)
    (lo := (331603 / 8000000)) (hi := (5181297 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 239849235999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 239849235999) = 1/(239849235999 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11052 : Bounds (-5181297 / 125000000) (-331603 / 8000000) (Real.log (239849235999 / 250000000000)) := by
  have h := reflection_log_11052_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11053_neg : (51074407 / 125000000) ≤ -Real.log (250000000000 / 376175644773) ∧
    -Real.log (250000000000 / 376175644773) ≤ (408595257 / 1000000000) := by
  have h := checkLog_sound (w := (126175644773 / 626175644773)) (n := 12)
    (lo := (51074407 / 125000000)) (hi := (408595257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((376175644773 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(376175644773 / 250000000000) = 1/(250000000000 / 376175644773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11053 : Bounds (51074407 / 125000000) (408595257 / 1000000000) (Real.log (376175644773 / 250000000000)) := by
  have h := reflection_log_11053_neg
  have he : Real.log (376175644773 / 250000000000) = -Real.log (250000000000 / 376175644773) := by
    rw [show ((376175644773 / 250000000000) : ℝ) = ((250000000000 / 376175644773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11054_neg : (410528097 / 1000000000) ≤ -Real.log (500000000000 / 753806871113) ∧
    -Real.log (500000000000 / 753806871113) ≤ (205264049 / 500000000) := by
  have h := checkLog_sound (w := (253806871113 / 1253806871113)) (n := 12)
    (lo := (410528097 / 1000000000)) (hi := (205264049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((753806871113 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(753806871113 / 500000000000) = 1/(500000000000 / 753806871113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11054 : Bounds (410528097 / 1000000000) (205264049 / 500000000) (Real.log (753806871113 / 500000000000)) := by
  have h := reflection_log_11054_neg
  have he : Real.log (753806871113 / 500000000000) = -Real.log (500000000000 / 753806871113) := by
    rw [show ((753806871113 / 500000000000) : ℝ) = ((500000000000 / 753806871113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11055_neg : (414160979 / 500000000) ≤ -Real.log (100000000000 / 228947368421) ∧
    -Real.log (100000000000 / 228947368421) ≤ (20708049 / 25000000) := by
  have h := checkLog_sound (w := (28947368421 / 428947368421)) (n := 12)
    (lo := (67587389 / 500000000)) (hi := (135174779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((228947368421 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(228947368421 / 200000000000) = 1/(100000000000 / 228947368421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11055 : Bounds (414160979 / 500000000) (20708049 / 25000000) (Real.log (228947368421 / 100000000000)) := by
  have h := reflection_log_11055_neg
  have he : Real.log (228947368421 / 100000000000) = -Real.log (100000000000 / 228947368421) := by
    rw [show ((228947368421 / 100000000000) : ℝ) = ((100000000000 / 228947368421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11056_neg : (415343091 / 500000000) ≤ -Real.log (500000000000 / 1147446457991) ∧
    -Real.log (500000000000 / 1147446457991) ≤ (103835773 / 125000000) := by
  have h := checkLog_sound (w := (147446457991 / 2147446457991)) (n := 12)
    (lo := (68769501 / 500000000)) (hi := (137539003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1147446457991 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1147446457991 / 1000000000000) = 1/(500000000000 / 1147446457991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11056 : Bounds (415343091 / 500000000) (103835773 / 125000000) (Real.log (1147446457991 / 500000000000)) := by
  have h := reflection_log_11056_neg
  have he : Real.log (1147446457991 / 500000000000) = -Real.log (500000000000 / 1147446457991) := by
    rw [show ((1147446457991 / 500000000000) : ℝ) = ((500000000000 / 1147446457991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11057_neg : (10380541 / 31250000) ≤ -Real.log (500 / 697) ∧
    -Real.log (500 / 697) ≤ (332177313 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 1197)) (n := 12)
    (lo := (10380541 / 31250000)) (hi := (332177313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697 / 500) = 1/(500 / 697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11057 : Bounds (10380541 / 31250000) (332177313 / 1000000000) (Real.log (697 / 500)) := by
  have h := reflection_log_11057_neg
  have he : Real.log (697 / 500) = -Real.log (500 / 697) := by
    rw [show ((697 / 500) : ℝ) = ((500 / 697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11058_neg : (125218823 / 250000000) ≤ -Real.log (303 / 500) ∧
    -Real.log (303 / 500) ≤ (500875293 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 803)) (n := 12)
    (lo := (125218823 / 250000000)) (hi := (500875293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 303) = 1/(303 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11058 : Bounds (-500875293 / 1000000000) (-125218823 / 250000000) (Real.log (303 / 500)) := by
  have h := reflection_log_11058_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11059_neg : (196961 / 500000000) ≤ -Real.log (500000 / 500197) ∧
    -Real.log (500000 / 500197) ≤ (393923 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 1000197)) (n := 12)
    (lo := (196961 / 500000000)) (hi := (393923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500197 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500197 / 500000) = 1/(500000 / 500197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11059 : Bounds (196961 / 500000000) (393923 / 1000000000) (Real.log (500197 / 500000)) := by
  have h := reflection_log_11059_neg
  have he : Real.log (500197 / 500000) = -Real.log (500000 / 500197) := by
    rw [show ((500197 / 500000) : ℝ) = ((500000 / 500197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11060_neg : (394077 / 1000000000) ≤ -Real.log (499803 / 500000) ∧
    -Real.log (499803 / 500000) ≤ (197039 / 500000000) := by
  have h := checkLog_sound (w := (197 / 999803)) (n := 12)
    (lo := (394077 / 1000000000)) (hi := (197039 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499803) = 1/(499803 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11060 : Bounds (-197039 / 500000000) (-394077 / 1000000000) (Real.log (499803 / 500000)) := by
  have h := reflection_log_11060_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11061_neg : (11501621 / 62500000) ≤ -Real.log (1000000 / 1202047) ∧
    -Real.log (1000000 / 1202047) ≤ (184025937 / 1000000000) := by
  have h := checkLog_sound (w := (202047 / 2202047)) (n := 12)
    (lo := (11501621 / 62500000)) (hi := (184025937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1202047 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1202047 / 1000000) = 1/(1000000 / 1202047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11061 : Bounds (11501621 / 62500000) (184025937 / 1000000000) (Real.log (1202047 / 1000000)) := by
  have h := reflection_log_11061_neg
  have he : Real.log (1202047 / 1000000) = -Real.log (1000000 / 1202047) := by
    rw [show ((1202047 / 1000000) : ℝ) = ((1000000 / 1202047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11062_neg : (11285279 / 50000000) ≤ -Real.log (797953 / 1000000) ∧
    -Real.log (797953 / 1000000) ≤ (225705581 / 1000000000) := by
  have h := checkLog_sound (w := (202047 / 1797953)) (n := 12)
    (lo := (11285279 / 50000000)) (hi := (225705581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 797953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 797953) = 1/(797953 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11062 : Bounds (-225705581 / 1000000000) (-11285279 / 50000000) (Real.log (797953 / 1000000)) := by
  have h := reflection_log_11062_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11063_neg : (36959531 / 200000000) ≤ -Real.log (40000 / 48119) ∧
    -Real.log (40000 / 48119) ≤ (23099707 / 125000000) := by
  have h := checkLog_sound (w := (8119 / 88119)) (n := 12)
    (lo := (36959531 / 200000000)) (hi := (23099707 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48119 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48119 / 40000) = 1/(40000 / 48119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11063 : Bounds (36959531 / 200000000) (23099707 / 125000000) (Real.log (48119 / 40000)) := by
  have h := reflection_log_11063_neg
  have he : Real.log (48119 / 40000) = -Real.log (40000 / 48119) := by
    rw [show ((48119 / 40000) : ℝ) = ((40000 / 48119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11064_neg : (226869233 / 1000000000) ≤ -Real.log (31881 / 40000) ∧
    -Real.log (31881 / 40000) ≤ (113434617 / 500000000) := by
  have h := checkLog_sound (w := (8119 / 71881)) (n := 12)
    (lo := (226869233 / 1000000000)) (hi := (113434617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 31881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 31881) = 1/(31881 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11064 : Bounds (-113434617 / 500000000) (-226869233 / 1000000000) (Real.log (31881 / 40000)) := by
  have h := reflection_log_11064_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11065_neg : (42071577 / 1000000000) ≤ -Real.log (1534081839 / 1600000000) ∧
    -Real.log (1534081839 / 1600000000) ≤ (21035789 / 500000000) := by
  have h := checkLog_sound (w := (65918161 / 3134081839)) (n := 12)
    (lo := (42071577 / 1000000000)) (hi := (21035789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1534081839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1534081839) = 1/(1534081839 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11065 : Bounds (-21035789 / 500000000) (-42071577 / 1000000000) (Real.log (1534081839 / 1600000000)) := by
  have h := reflection_log_11065_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11066_neg : (41679643 / 1000000000) ≤ -Real.log (959177009791 / 1000000000000) ∧
    -Real.log (959177009791 / 1000000000000) ≤ (10419911 / 250000000) := by
  have h := checkLog_sound (w := (40822990209 / 1959177009791)) (n := 12)
    (lo := (41679643 / 1000000000)) (hi := (10419911 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 959177009791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 959177009791) = 1/(959177009791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11066 : Bounds (-10419911 / 250000000) (-41679643 / 1000000000) (Real.log (959177009791 / 1000000000000)) := by
  have h := reflection_log_11066_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11067_neg : (409731517 / 1000000000) ≤ -Real.log (7812500000 / 11768853789) ∧
    -Real.log (7812500000 / 11768853789) ≤ (204865759 / 500000000) := by
  have h := checkLog_sound (w := (3956353789 / 19581353789)) (n := 12)
    (lo := (409731517 / 1000000000)) (hi := (204865759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11768853789 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11768853789 / 7812500000) = 1/(7812500000 / 11768853789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11067 : Bounds (409731517 / 1000000000) (204865759 / 500000000) (Real.log (11768853789 / 7812500000)) := by
  have h := reflection_log_11067_neg
  have he : Real.log (11768853789 / 7812500000) = -Real.log (7812500000 / 11768853789) := by
    rw [show ((11768853789 / 7812500000) : ℝ) = ((7812500000 / 11768853789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11068_neg : (51458361 / 125000000) ≤ -Real.log (500000000000 / 754665788401) ∧
    -Real.log (500000000000 / 754665788401) ≤ (411666889 / 1000000000) := by
  have h := checkLog_sound (w := (254665788401 / 1254665788401)) (n := 12)
    (lo := (51458361 / 125000000)) (hi := (411666889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((754665788401 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(754665788401 / 500000000000) = 1/(500000000000 / 754665788401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11068 : Bounds (51458361 / 125000000) (411666889 / 1000000000) (Real.log (754665788401 / 500000000000)) := by
  have h := reflection_log_11068_neg
  have he : Real.log (754665788401 / 500000000000) = -Real.log (500000000000 / 754665788401) := by
    rw [show ((754665788401 / 500000000000) : ℝ) = ((500000000000 / 754665788401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11069_neg : (415343091 / 500000000) ≤ -Real.log (50000000000 / 114744645799) ∧
    -Real.log (50000000000 / 114744645799) ≤ (103835773 / 125000000) := by
  have h := checkLog_sound (w := (14744645799 / 214744645799)) (n := 12)
    (lo := (68769501 / 500000000)) (hi := (137539003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114744645799 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(114744645799 / 100000000000) = 1/(50000000000 / 114744645799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11069 : Bounds (415343091 / 500000000) (103835773 / 125000000) (Real.log (114744645799 / 50000000000)) := by
  have h := reflection_log_11069_neg
  have he : Real.log (114744645799 / 50000000000) = -Real.log (50000000000 / 114744645799) := by
    rw [show ((114744645799 / 50000000000) : ℝ) = ((50000000000 / 114744645799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11070_neg : (208263151 / 250000000) ≤ -Real.log (250000000000 / 575082508251) ∧
    -Real.log (250000000000 / 575082508251) ≤ (416526303 / 500000000) := by
  have h := checkLog_sound (w := (75082508251 / 1075082508251)) (n := 12)
    (lo := (8744089 / 62500000)) (hi := (5596217 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((575082508251 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(575082508251 / 500000000000) = 1/(250000000000 / 575082508251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11070 : Bounds (208263151 / 250000000) (416526303 / 500000000) (Real.log (575082508251 / 250000000000)) := by
  have h := reflection_log_11070_neg
  have he : Real.log (575082508251 / 250000000000) = -Real.log (250000000000 / 575082508251) := by
    rw [show ((575082508251 / 250000000000) : ℝ) = ((250000000000 / 575082508251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11071_neg : (66578883 / 200000000) ≤ -Real.log (200 / 279) ∧
    -Real.log (200 / 279) ≤ (20805901 / 62500000) := by
  have h := checkLog_sound (w := (79 / 479)) (n := 12)
    (lo := (66578883 / 200000000)) (hi := (20805901 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(279 / 200) = 1/(200 / 279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11071 : Bounds (66578883 / 200000000) (20805901 / 62500000) (Real.log (279 / 200)) := by
  have h := reflection_log_11071_neg
  have he : Real.log (279 / 200) = -Real.log (200 / 279) := by
    rw [show ((279 / 200) : ℝ) = ((200 / 279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0173 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11072_neg : (25126341 / 50000000) ≤ -Real.log (121 / 200) ∧
    -Real.log (121 / 200) ≤ (502526821 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 321)) (n := 12)
    (lo := (25126341 / 50000000)) (hi := (502526821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 121) = 1/(121 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11072 : Bounds (-502526821 / 1000000000) (-25126341 / 50000000) (Real.log (121 / 200)) := by
  have h := reflection_log_11072_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11073_neg : (197461 / 500000000) ≤ -Real.log (200000 / 200079) ∧
    -Real.log (200000 / 200079) ≤ (394923 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 400079)) (n := 12)
    (lo := (197461 / 500000000)) (hi := (394923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200079 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200079 / 200000) = 1/(200000 / 200079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11073 : Bounds (197461 / 500000000) (394923 / 1000000000) (Real.log (200079 / 200000)) := by
  have h := reflection_log_11073_neg
  have he : Real.log (200079 / 200000) = -Real.log (200000 / 200079) := by
    rw [show ((200079 / 200000) : ℝ) = ((200000 / 200079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11074_neg : (197539 / 500000000) ≤ -Real.log (199921 / 200000) ∧
    -Real.log (199921 / 200000) ≤ (395079 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 399921)) (n := 12)
    (lo := (197539 / 500000000)) (hi := (395079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199921) = 1/(199921 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11074 : Bounds (-395079 / 1000000000) (-197539 / 500000000) (Real.log (199921 / 200000)) := by
  have h := reflection_log_11074_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11075_neg : (184479227 / 1000000000) ≤ -Real.log (31250 / 37581) ∧
    -Real.log (31250 / 37581) ≤ (46119807 / 250000000) := by
  have h := checkLog_sound (w := (6331 / 68831)) (n := 12)
    (lo := (184479227 / 1000000000)) (hi := (46119807 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37581 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37581 / 31250) = 1/(31250 / 37581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11075 : Bounds (184479227 / 1000000000) (46119807 / 250000000) (Real.log (37581 / 31250)) := by
  have h := reflection_log_11075_neg
  have he : Real.log (37581 / 31250) = -Real.log (31250 / 37581) := by
    rw [show ((37581 / 31250) : ℝ) = ((31250 / 37581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11076_neg : (226388811 / 1000000000) ≤ -Real.log (24919 / 31250) ∧
    -Real.log (24919 / 31250) ≤ (56597203 / 250000000) := by
  have h := checkLog_sound (w := (6331 / 56169)) (n := 12)
    (lo := (226388811 / 1000000000)) (hi := (56597203 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 24919) = 1/(24919 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11076 : Bounds (-56597203 / 250000000) (-226388811 / 1000000000) (Real.log (24919 / 31250)) := by
  have h := reflection_log_11076_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11077_neg : (185251427 / 1000000000) ≤ -Real.log (1000000 / 1203521) ∧
    -Real.log (1000000 / 1203521) ≤ (46312857 / 250000000) := by
  have h := checkLog_sound (w := (203521 / 2203521)) (n := 12)
    (lo := (185251427 / 1000000000)) (hi := (46312857 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1203521 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1203521 / 1000000) = 1/(1000000 / 1203521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11077 : Bounds (185251427 / 1000000000) (46312857 / 250000000) (Real.log (1203521 / 1000000)) := by
  have h := reflection_log_11077_neg
  have he : Real.log (1203521 / 1000000) = -Real.log (1000000 / 1203521) := by
    rw [show ((1203521 / 1000000) : ℝ) = ((1000000 / 1203521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11078_neg : (45510903 / 200000000) ≤ -Real.log (796479 / 1000000) ∧
    -Real.log (796479 / 1000000) ≤ (56888629 / 250000000) := by
  have h := checkLog_sound (w := (203521 / 1796479)) (n := 12)
    (lo := (45510903 / 200000000)) (hi := (56888629 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 796479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 796479) = 1/(796479 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11078 : Bounds (-56888629 / 250000000) (-45510903 / 200000000) (Real.log (796479 / 1000000)) := by
  have h := reflection_log_11078_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11079_neg : (2643943 / 62500000) ≤ -Real.log (958579202559 / 1000000000000) ∧
    -Real.log (958579202559 / 1000000000000) ≤ (42303089 / 1000000000) := by
  have h := checkLog_sound (w := (41420797441 / 1958579202559)) (n := 12)
    (lo := (2643943 / 62500000)) (hi := (42303089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 958579202559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 958579202559) = 1/(958579202559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11079 : Bounds (-42303089 / 1000000000) (-2643943 / 62500000) (Real.log (958579202559 / 1000000000000)) := by
  have h := reflection_log_11079_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11080_neg : (2619349 / 62500000) ≤ -Real.log (936480939 / 976562500) ∧
    -Real.log (936480939 / 976562500) ≤ (8381917 / 200000000) := by
  have h := checkLog_sound (w := (40081561 / 1913043439)) (n := 12)
    (lo := (2619349 / 62500000)) (hi := (8381917 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 936480939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 936480939) = 1/(936480939 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11080 : Bounds (-8381917 / 200000000) (-2619349 / 62500000) (Real.log (936480939 / 976562500)) := by
  have h := reflection_log_11080_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11081_neg : (205434019 / 500000000) ≤ -Real.log (500000000000 / 754063164653) ∧
    -Real.log (500000000000 / 754063164653) ≤ (410868039 / 1000000000) := by
  have h := checkLog_sound (w := (254063164653 / 1254063164653)) (n := 12)
    (lo := (205434019 / 500000000)) (hi := (410868039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((754063164653 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(754063164653 / 500000000000) = 1/(500000000000 / 754063164653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11081 : Bounds (205434019 / 500000000) (410868039 / 1000000000) (Real.log (754063164653 / 500000000000)) := by
  have h := reflection_log_11081_neg
  have he : Real.log (754063164653 / 500000000000) = -Real.log (500000000000 / 754063164653) := by
    rw [show ((754063164653 / 500000000000) : ℝ) = ((500000000000 / 754063164653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11082_neg : (206402971 / 500000000) ≤ -Real.log (250000000000 / 377762941647) ∧
    -Real.log (250000000000 / 377762941647) ≤ (412805943 / 1000000000) := by
  have h := checkLog_sound (w := (127762941647 / 627762941647)) (n := 12)
    (lo := (206402971 / 500000000)) (hi := (412805943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((377762941647 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(377762941647 / 250000000000) = 1/(250000000000 / 377762941647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11082 : Bounds (206402971 / 500000000) (412805943 / 1000000000) (Real.log (377762941647 / 250000000000)) := by
  have h := reflection_log_11082_neg
  have he : Real.log (377762941647 / 250000000000) = -Real.log (250000000000 / 377762941647) := by
    rw [show ((377762941647 / 250000000000) : ℝ) = ((250000000000 / 377762941647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11083_neg : (208263151 / 250000000) ≤ -Real.log (500000000000 / 1150165016501) ∧
    -Real.log (500000000000 / 1150165016501) ≤ (416526303 / 500000000) := by
  have h := checkLog_sound (w := (150165016501 / 2150165016501)) (n := 12)
    (lo := (8744089 / 62500000)) (hi := (5596217 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1150165016501 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1150165016501 / 1000000000000) = 1/(500000000000 / 1150165016501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11083 : Bounds (208263151 / 250000000) (416526303 / 500000000) (Real.log (1150165016501 / 500000000000)) := by
  have h := reflection_log_11083_neg
  have he : Real.log (1150165016501 / 500000000000) = -Real.log (500000000000 / 1150165016501) := by
    rw [show ((1150165016501 / 500000000000) : ℝ) = ((500000000000 / 1150165016501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11084_neg : (167084247 / 200000000) ≤ -Real.log (7812500000 / 18013946281) ∧
    -Real.log (7812500000 / 18013946281) ≤ (835421237 / 1000000000) := by
  have h := checkLog_sound (w := (2388946281 / 33638946281)) (n := 12)
    (lo := (28454811 / 200000000)) (hi := (17784257 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18013946281 / 15625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(18013946281 / 15625000000) = 1/(7812500000 / 18013946281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11084 : Bounds (167084247 / 200000000) (835421237 / 1000000000) (Real.log (18013946281 / 7812500000)) := by
  have h := reflection_log_11084_neg
  have he : Real.log (18013946281 / 7812500000) = -Real.log (7812500000 / 18013946281) := by
    rw [show ((18013946281 / 7812500000) : ℝ) = ((7812500000 / 18013946281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11085_neg : (83402751 / 250000000) ≤ -Real.log (250 / 349) ∧
    -Real.log (250 / 349) ≤ (66722201 / 200000000) := by
  have h := checkLog_sound (w := (99 / 599)) (n := 12)
    (lo := (83402751 / 250000000)) (hi := (66722201 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349 / 250) = 1/(250 / 349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11085 : Bounds (83402751 / 250000000) (66722201 / 200000000) (Real.log (349 / 250)) := by
  have h := reflection_log_11085_neg
  have he : Real.log (349 / 250) = -Real.log (250 / 349) := by
    rw [show ((349 / 250) : ℝ) = ((250 / 349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11086_neg : (504181081 / 1000000000) ≤ -Real.log (151 / 250) ∧
    -Real.log (151 / 250) ≤ (252090541 / 500000000) := by
  have h := checkLog_sound (w := (99 / 401)) (n := 12)
    (lo := (504181081 / 1000000000)) (hi := (252090541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 151) = 1/(151 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11086 : Bounds (-252090541 / 500000000) (-504181081 / 1000000000) (Real.log (151 / 250)) := by
  have h := reflection_log_11086_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11087_neg : (395921 / 1000000000) ≤ -Real.log (250000 / 250099) ∧
    -Real.log (250000 / 250099) ≤ (197961 / 500000000) := by
  have h := checkLog_sound (w := (99 / 500099)) (n := 12)
    (lo := (395921 / 1000000000)) (hi := (197961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250099 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250099 / 250000) = 1/(250000 / 250099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11087 : Bounds (395921 / 1000000000) (197961 / 500000000) (Real.log (250099 / 250000)) := by
  have h := reflection_log_11087_neg
  have he : Real.log (250099 / 250000) = -Real.log (250000 / 250099) := by
    rw [show ((250099 / 250000) : ℝ) = ((250000 / 250099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11088_neg : (198039 / 500000000) ≤ -Real.log (249901 / 250000) ∧
    -Real.log (249901 / 250000) ≤ (396079 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 499901)) (n := 12)
    (lo := (198039 / 500000000)) (hi := (396079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249901) = 1/(249901 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11088 : Bounds (-396079 / 1000000000) (-198039 / 500000000) (Real.log (249901 / 250000)) := by
  have h := reflection_log_11088_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11089_neg : (23116539 / 125000000) ≤ -Real.log (1000000 / 1203137) ∧
    -Real.log (1000000 / 1203137) ≤ (184932313 / 1000000000) := by
  have h := checkLog_sound (w := (203137 / 2203137)) (n := 12)
    (lo := (23116539 / 125000000)) (hi := (184932313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1203137 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1203137 / 1000000) = 1/(1000000 / 1203137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11089 : Bounds (23116539 / 125000000) (184932313 / 1000000000) (Real.log (1203137 / 1000000)) := by
  have h := reflection_log_11089_neg
  have he : Real.log (1203137 / 1000000) = -Real.log (1000000 / 1203137) := by
    rw [show ((1203137 / 1000000) : ℝ) = ((1000000 / 1203137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11090_neg : (227072509 / 1000000000) ≤ -Real.log (796863 / 1000000) ∧
    -Real.log (796863 / 1000000) ≤ (22707251 / 100000000) := by
  have h := checkLog_sound (w := (203137 / 1796863)) (n := 12)
    (lo := (227072509 / 1000000000)) (hi := (22707251 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 796863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 796863) = 1/(796863 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11090 : Bounds (-22707251 / 100000000) (-227072509 / 1000000000) (Real.log (796863 / 1000000)) := by
  have h := reflection_log_11090_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11091_neg : (185704993 / 1000000000) ≤ -Real.log (1000000 / 1204067) ∧
    -Real.log (1000000 / 1204067) ≤ (92852497 / 500000000) := by
  have h := checkLog_sound (w := (204067 / 2204067)) (n := 12)
    (lo := (185704993 / 1000000000)) (hi := (92852497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1204067 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1204067 / 1000000) = 1/(1000000 / 1204067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11091 : Bounds (185704993 / 1000000000) (92852497 / 500000000) (Real.log (1204067 / 1000000)) := by
  have h := reflection_log_11091_neg
  have he : Real.log (1204067 / 1000000) = -Real.log (1000000 / 1204067) := by
    rw [show ((1204067 / 1000000) : ℝ) = ((1000000 / 1204067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11092_neg : (228240267 / 1000000000) ≤ -Real.log (795933 / 1000000) ∧
    -Real.log (795933 / 1000000) ≤ (57060067 / 250000000) := by
  have h := checkLog_sound (w := (204067 / 1795933)) (n := 12)
    (lo := (228240267 / 1000000000)) (hi := (57060067 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 795933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 795933) = 1/(795933 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11092 : Bounds (-57060067 / 250000000) (-228240267 / 1000000000) (Real.log (795933 / 1000000)) := by
  have h := reflection_log_11092_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11093_neg : (21267637 / 500000000) ≤ -Real.log (958356659511 / 1000000000000) ∧
    -Real.log (958356659511 / 1000000000000) ≤ (1701411 / 40000000) := by
  have h := checkLog_sound (w := (41643340489 / 1958356659511)) (n := 12)
    (lo := (21267637 / 500000000)) (hi := (1701411 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 958356659511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 958356659511) = 1/(958356659511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11093 : Bounds (-1701411 / 40000000) (-21267637 / 500000000) (Real.log (958356659511 / 1000000000000)) := by
  have h := reflection_log_11093_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11094_neg : (42140197 / 1000000000) ≤ -Real.log (958735359231 / 1000000000000) ∧
    -Real.log (958735359231 / 1000000000000) ≤ (21070099 / 500000000) := by
  have h := checkLog_sound (w := (41264640769 / 1958735359231)) (n := 12)
    (lo := (42140197 / 1000000000)) (hi := (21070099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 958735359231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 958735359231) = 1/(958735359231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11094 : Bounds (-21070099 / 500000000) (-42140197 / 1000000000) (Real.log (958735359231 / 1000000000000)) := by
  have h := reflection_log_11094_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11095_neg : (206002411 / 500000000) ≤ -Real.log (31250000000 / 47182553651) ∧
    -Real.log (31250000000 / 47182553651) ≤ (412004823 / 1000000000) := by
  have h := checkLog_sound (w := (15932553651 / 78432553651)) (n := 12)
    (lo := (206002411 / 500000000)) (hi := (412004823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47182553651 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47182553651 / 31250000000) = 1/(31250000000 / 47182553651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11095 : Bounds (206002411 / 500000000) (412004823 / 1000000000) (Real.log (47182553651 / 31250000000)) := by
  have h := reflection_log_11095_neg
  have he : Real.log (47182553651 / 31250000000) = -Real.log (31250000000 / 47182553651) := by
    rw [show ((47182553651 / 31250000000) : ℝ) = ((31250000000 / 47182553651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11096_neg : (20697263 / 50000000) ≤ -Real.log (62500000000 / 94548394777) ∧
    -Real.log (62500000000 / 94548394777) ≤ (413945261 / 1000000000) := by
  have h := checkLog_sound (w := (32048394777 / 157048394777)) (n := 12)
    (lo := (20697263 / 50000000)) (hi := (413945261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((94548394777 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(94548394777 / 62500000000) = 1/(62500000000 / 94548394777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11096 : Bounds (20697263 / 50000000) (413945261 / 1000000000) (Real.log (94548394777 / 62500000000)) := by
  have h := reflection_log_11096_neg
  have he : Real.log (94548394777 / 62500000000) = -Real.log (62500000000 / 94548394777) := by
    rw [show ((94548394777 / 62500000000) : ℝ) = ((62500000000 / 94548394777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11097_neg : (167084247 / 200000000) ≤ -Real.log (500000000000 / 1152892561983) ∧
    -Real.log (500000000000 / 1152892561983) ≤ (835421237 / 1000000000) := by
  have h := checkLog_sound (w := (152892561983 / 2152892561983)) (n := 12)
    (lo := (28454811 / 200000000)) (hi := (17784257 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1152892561983 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1152892561983 / 1000000000000) = 1/(500000000000 / 1152892561983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11097 : Bounds (167084247 / 200000000) (835421237 / 1000000000) (Real.log (1152892561983 / 500000000000)) := by
  have h := reflection_log_11097_neg
  have he : Real.log (1152892561983 / 500000000000) = -Real.log (500000000000 / 1152892561983) := by
    rw [show ((1152892561983 / 500000000000) : ℝ) = ((500000000000 / 1152892561983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11098_neg : (209448021 / 250000000) ≤ -Real.log (500000000000 / 1155629139073) ∧
    -Real.log (500000000000 / 1155629139073) ≤ (418896043 / 500000000) := by
  have h := checkLog_sound (w := (155629139073 / 2155629139073)) (n := 12)
    (lo := (18080613 / 125000000)) (hi := (28928981 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1155629139073 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1155629139073 / 1000000000000) = 1/(500000000000 / 1155629139073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11098 : Bounds (209448021 / 250000000) (418896043 / 500000000) (Real.log (1155629139073 / 500000000000)) := by
  have h := reflection_log_11098_neg
  have he : Real.log (1155629139073 / 500000000000) = -Real.log (500000000000 / 1155629139073) := by
    rw [show ((1155629139073 / 500000000000) : ℝ) = ((500000000000 / 1155629139073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11099_neg : (8358177 / 25000000) ≤ -Real.log (1000 / 1397) ∧
    -Real.log (1000 / 1397) ≤ (334327081 / 1000000000) := by
  have h := checkLog_sound (w := (397 / 2397)) (n := 12)
    (lo := (8358177 / 25000000)) (hi := (334327081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1397 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1397 / 1000) = 1/(1000 / 1397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11099 : Bounds (8358177 / 25000000) (334327081 / 1000000000) (Real.log (1397 / 1000)) := by
  have h := reflection_log_11099_neg
  have he : Real.log (1397 / 1000) = -Real.log (1000 / 1397) := by
    rw [show ((1397 / 1000) : ℝ) = ((1000 / 1397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11100_neg : (252919041 / 500000000) ≤ -Real.log (603 / 1000) ∧
    -Real.log (603 / 1000) ≤ (505838083 / 1000000000) := by
  have h := checkLog_sound (w := (397 / 1603)) (n := 12)
    (lo := (252919041 / 500000000)) (hi := (505838083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 603) = 1/(603 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11100 : Bounds (-505838083 / 1000000000) (-252919041 / 500000000) (Real.log (603 / 1000)) := by
  have h := reflection_log_11100_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11101_neg : (396921 / 1000000000) ≤ -Real.log (1000000 / 1000397) ∧
    -Real.log (1000000 / 1000397) ≤ (198461 / 500000000) := by
  have h := checkLog_sound (w := (397 / 2000397)) (n := 12)
    (lo := (396921 / 1000000000)) (hi := (198461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000397 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000397 / 1000000) = 1/(1000000 / 1000397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11101 : Bounds (396921 / 1000000000) (198461 / 500000000) (Real.log (1000397 / 1000000)) := by
  have h := reflection_log_11101_neg
  have he : Real.log (1000397 / 1000000) = -Real.log (1000000 / 1000397) := by
    rw [show ((1000397 / 1000000) : ℝ) = ((1000000 / 1000397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11102_neg : (198539 / 500000000) ≤ -Real.log (999603 / 1000000) ∧
    -Real.log (999603 / 1000000) ≤ (397079 / 1000000000) := by
  have h := checkLog_sound (w := (397 / 1999603)) (n := 12)
    (lo := (198539 / 500000000)) (hi := (397079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999603) = 1/(999603 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11102 : Bounds (-397079 / 1000000000) (-198539 / 500000000) (Real.log (999603 / 1000000)) := by
  have h := reflection_log_11102_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11103_neg : (23173149 / 125000000) ≤ -Real.log (500000 / 601841) ∧
    -Real.log (500000 / 601841) ≤ (185385193 / 1000000000) := by
  have h := checkLog_sound (w := (101841 / 1101841)) (n := 12)
    (lo := (23173149 / 125000000)) (hi := (185385193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601841 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(601841 / 500000) = 1/(500000 / 601841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11103 : Bounds (23173149 / 125000000) (185385193 / 1000000000) (Real.log (601841 / 500000)) := by
  have h := reflection_log_11103_neg
  have he : Real.log (601841 / 500000) = -Real.log (500000 / 601841) := by
    rw [show ((601841 / 500000) : ℝ) = ((500000 / 601841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11104_neg : (9110267 / 40000000) ≤ -Real.log (398159 / 500000) ∧
    -Real.log (398159 / 500000) ≤ (56939169 / 250000000) := by
  have h := checkLog_sound (w := (101841 / 898159)) (n := 12)
    (lo := (9110267 / 40000000)) (hi := (56939169 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 398159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 398159) = 1/(398159 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11104 : Bounds (-56939169 / 250000000) (-9110267 / 40000000) (Real.log (398159 / 500000)) := by
  have h := reflection_log_11104_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11105_neg : (186159183 / 1000000000) ≤ -Real.log (500000 / 602307) ∧
    -Real.log (500000 / 602307) ≤ (11634949 / 62500000) := by
  have h := checkLog_sound (w := (102307 / 1102307)) (n := 12)
    (lo := (186159183 / 1000000000)) (hi := (11634949 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602307 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602307 / 500000) = 1/(500000 / 602307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11105 : Bounds (186159183 / 1000000000) (11634949 / 62500000) (Real.log (602307 / 500000)) := by
  have h := reflection_log_11105_neg
  have he : Real.log (602307 / 500000) = -Real.log (500000 / 602307) := by
    rw [show ((602307 / 500000) : ℝ) = ((500000 / 602307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11106_neg : (228927747 / 1000000000) ≤ -Real.log (397693 / 500000) ∧
    -Real.log (397693 / 500000) ≤ (57231937 / 250000000) := by
  have h := checkLog_sound (w := (102307 / 897693)) (n := 12)
    (lo := (228927747 / 1000000000)) (hi := (57231937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 397693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 397693) = 1/(397693 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11106 : Bounds (-57231937 / 250000000) (-228927747 / 1000000000) (Real.log (397693 / 500000)) := by
  have h := reflection_log_11106_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11107_neg : (42768563 / 1000000000) ≤ -Real.log (239533277751 / 250000000000) ∧
    -Real.log (239533277751 / 250000000000) ≤ (10692141 / 250000000) := by
  have h := checkLog_sound (w := (10466722249 / 489533277751)) (n := 12)
    (lo := (42768563 / 1000000000)) (hi := (10692141 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 239533277751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 239533277751) = 1/(239533277751 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11107 : Bounds (-10692141 / 250000000) (-42768563 / 1000000000) (Real.log (239533277751 / 250000000000)) := by
  have h := reflection_log_11107_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11108_neg : (42371483 / 1000000000) ≤ -Real.log (239628410719 / 250000000000) ∧
    -Real.log (239628410719 / 250000000000) ≤ (10592871 / 250000000) := by
  have h := checkLog_sound (w := (10371589281 / 489628410719)) (n := 12)
    (lo := (42371483 / 1000000000)) (hi := (10592871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 239628410719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 239628410719) = 1/(239628410719 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11108 : Bounds (-10592871 / 250000000) (-42371483 / 1000000000) (Real.log (239628410719 / 250000000000)) := by
  have h := reflection_log_11108_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11109_neg : (413141867 / 1000000000) ≤ -Real.log (500000000000 / 755779726189) ∧
    -Real.log (500000000000 / 755779726189) ≤ (103285467 / 250000000) := by
  have h := checkLog_sound (w := (255779726189 / 1255779726189)) (n := 12)
    (lo := (413141867 / 1000000000)) (hi := (103285467 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((755779726189 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(755779726189 / 500000000000) = 1/(500000000000 / 755779726189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11109 : Bounds (413141867 / 1000000000) (103285467 / 250000000) (Real.log (755779726189 / 500000000000)) := by
  have h := reflection_log_11109_neg
  have he : Real.log (755779726189 / 500000000000) = -Real.log (500000000000 / 755779726189) := by
    rw [show ((755779726189 / 500000000000) : ℝ) = ((500000000000 / 755779726189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11110_neg : (415086931 / 1000000000) ≤ -Real.log (20000000000 / 30290047851) ∧
    -Real.log (20000000000 / 30290047851) ≤ (103771733 / 250000000) := by
  have h := checkLog_sound (w := (10290047851 / 50290047851)) (n := 12)
    (lo := (415086931 / 1000000000)) (hi := (103771733 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30290047851 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30290047851 / 20000000000) = 1/(20000000000 / 30290047851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11110 : Bounds (415086931 / 1000000000) (103771733 / 250000000) (Real.log (30290047851 / 20000000000)) := by
  have h := reflection_log_11110_neg
  have he : Real.log (30290047851 / 20000000000) = -Real.log (20000000000 / 30290047851) := by
    rw [show ((30290047851 / 20000000000) : ℝ) = ((20000000000 / 30290047851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11111_neg : (209448021 / 250000000) ≤ -Real.log (3906250000 / 9028352649) ∧
    -Real.log (3906250000 / 9028352649) ≤ (418896043 / 500000000) := by
  have h := checkLog_sound (w := (1215852649 / 16840852649)) (n := 12)
    (lo := (18080613 / 125000000)) (hi := (28928981 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9028352649 / 7812500000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(9028352649 / 7812500000) = 1/(3906250000 / 9028352649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11111 : Bounds (209448021 / 250000000) (418896043 / 500000000) (Real.log (9028352649 / 3906250000)) := by
  have h := reflection_log_11111_neg
  have he : Real.log (9028352649 / 3906250000) = -Real.log (3906250000 / 9028352649) := by
    rw [show ((9028352649 / 3906250000) : ℝ) = ((3906250000 / 9028352649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11112_neg : (840165161 / 1000000000) ≤ -Real.log (976562500 / 2262450767) ∧
    -Real.log (976562500 / 2262450767) ≤ (840165163 / 1000000000) := by
  have h := checkLog_sound (w := (309325767 / 4215575767)) (n := 12)
    (lo := (147017981 / 1000000000)) (hi := (73508991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2262450767 / 1953125000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2262450767 / 1953125000) = 1/(976562500 / 2262450767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11112 : Bounds (840165161 / 1000000000) (840165163 / 1000000000) (Real.log (2262450767 / 976562500)) := by
  have h := reflection_log_11112_neg
  have he : Real.log (2262450767 / 976562500) = -Real.log (976562500 / 2262450767) := by
    rw [show ((2262450767 / 976562500) : ℝ) = ((976562500 / 2262450767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11113_neg : (335042643 / 1000000000) ≤ -Real.log (500 / 699) ∧
    -Real.log (500 / 699) ≤ (83760661 / 250000000) := by
  have h := checkLog_sound (w := (199 / 1199)) (n := 12)
    (lo := (335042643 / 1000000000)) (hi := (83760661 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699 / 500) = 1/(500 / 699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11113 : Bounds (335042643 / 1000000000) (83760661 / 250000000) (Real.log (699 / 500)) := by
  have h := reflection_log_11113_neg
  have he : Real.log (699 / 500) = -Real.log (500 / 699) := by
    rw [show ((699 / 500) : ℝ) = ((500 / 699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11114_neg : (507497833 / 1000000000) ≤ -Real.log (301 / 500) ∧
    -Real.log (301 / 500) ≤ (253748917 / 500000000) := by
  have h := checkLog_sound (w := (199 / 801)) (n := 12)
    (lo := (507497833 / 1000000000)) (hi := (253748917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 301) = 1/(301 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11114 : Bounds (-253748917 / 500000000) (-507497833 / 1000000000) (Real.log (301 / 500)) := by
  have h := reflection_log_11114_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11115_neg : (2487 / 6250000) ≤ -Real.log (500000 / 500199) ∧
    -Real.log (500000 / 500199) ≤ (397921 / 1000000000) := by
  have h := checkLog_sound (w := (199 / 1000199)) (n := 12)
    (lo := (2487 / 6250000)) (hi := (397921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500199 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500199 / 500000) = 1/(500000 / 500199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11115 : Bounds (2487 / 6250000) (397921 / 1000000000) (Real.log (500199 / 500000)) := by
  have h := reflection_log_11115_neg
  have he : Real.log (500199 / 500000) = -Real.log (500000 / 500199) := by
    rw [show ((500199 / 500000) : ℝ) = ((500000 / 500199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11116_neg : (398079 / 1000000000) ≤ -Real.log (499801 / 500000) ∧
    -Real.log (499801 / 500000) ≤ (311 / 781250) := by
  have h := checkLog_sound (w := (199 / 999801)) (n := 12)
    (lo := (398079 / 1000000000)) (hi := (311 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499801) = 1/(499801 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11116 : Bounds (-311 / 781250) (-398079 / 1000000000) (Real.log (499801 / 500000)) := by
  have h := reflection_log_11116_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11117_neg : (185838697 / 1000000000) ≤ -Real.log (250000 / 301057) ∧
    -Real.log (250000 / 301057) ≤ (92919349 / 500000000) := by
  have h := checkLog_sound (w := (51057 / 551057)) (n := 12)
    (lo := (185838697 / 1000000000)) (hi := (92919349 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301057 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301057 / 250000) = 1/(250000 / 301057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11117 : Bounds (185838697 / 1000000000) (92919349 / 500000000) (Real.log (301057 / 250000)) := by
  have h := reflection_log_11117_neg
  have he : Real.log (301057 / 250000) = -Real.log (250000 / 301057) := by
    rw [show ((301057 / 250000) : ℝ) = ((250000 / 301057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11118_neg : (114221283 / 500000000) ≤ -Real.log (198943 / 250000) ∧
    -Real.log (198943 / 250000) ≤ (228442567 / 1000000000) := by
  have h := checkLog_sound (w := (51057 / 448943)) (n := 12)
    (lo := (114221283 / 500000000)) (hi := (228442567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 198943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 198943) = 1/(198943 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11118 : Bounds (-228442567 / 1000000000) (-114221283 / 500000000) (Real.log (198943 / 250000)) := by
  have h := reflection_log_11118_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11119_neg : (93306169 / 500000000) ≤ -Real.log (25000 / 30129) ∧
    -Real.log (25000 / 30129) ≤ (186612339 / 1000000000) := by
  have h := checkLog_sound (w := (5129 / 55129)) (n := 12)
    (lo := (93306169 / 500000000)) (hi := (186612339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30129 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30129 / 25000) = 1/(25000 / 30129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11119 : Bounds (93306169 / 500000000) (186612339 / 1000000000) (Real.log (30129 / 25000)) := by
  have h := reflection_log_11119_neg
  have he : Real.log (30129 / 25000) = -Real.log (25000 / 30129) := by
    rw [show ((30129 / 25000) : ℝ) = ((25000 / 30129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11120_neg : (114807221 / 500000000) ≤ -Real.log (19871 / 25000) ∧
    -Real.log (19871 / 25000) ≤ (229614443 / 1000000000) := by
  have h := checkLog_sound (w := (5129 / 44871)) (n := 12)
    (lo := (114807221 / 500000000)) (hi := (229614443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 19871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 19871) = 1/(19871 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11120 : Bounds (-229614443 / 1000000000) (-114807221 / 500000000) (Real.log (19871 / 25000)) := by
  have h := reflection_log_11120_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11121_neg : (5375263 / 125000000) ≤ -Real.log (598693359 / 625000000) ∧
    -Real.log (598693359 / 625000000) ≤ (8600421 / 200000000) := by
  have h := checkLog_sound (w := (26306641 / 1223693359)) (n := 12)
    (lo := (5375263 / 125000000)) (hi := (8600421 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 598693359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 598693359) = 1/(598693359 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11121 : Bounds (-8600421 / 200000000) (-5375263 / 125000000) (Real.log (598693359 / 625000000)) := by
  have h := reflection_log_11121_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11122_neg : (10650967 / 250000000) ≤ -Real.log (59893182751 / 62500000000) ∧
    -Real.log (59893182751 / 62500000000) ≤ (42603869 / 1000000000) := by
  have h := checkLog_sound (w := (2606817249 / 122393182751)) (n := 12)
    (lo := (10650967 / 250000000)) (hi := (42603869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59893182751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59893182751) = 1/(59893182751 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11122 : Bounds (-42603869 / 1000000000) (-10650967 / 250000000) (Real.log (59893182751 / 62500000000)) := by
  have h := reflection_log_11122_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11123_neg : (25892579 / 62500000) ≤ -Real.log (125000000000 / 189160337383) ∧
    -Real.log (125000000000 / 189160337383) ≤ (82856253 / 200000000) := by
  have h := checkLog_sound (w := (64160337383 / 314160337383)) (n := 12)
    (lo := (25892579 / 62500000)) (hi := (82856253 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189160337383 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189160337383 / 125000000000) = 1/(125000000000 / 189160337383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11123 : Bounds (25892579 / 62500000) (82856253 / 200000000) (Real.log (189160337383 / 125000000000)) := by
  have h := reflection_log_11123_neg
  have he : Real.log (189160337383 / 125000000000) = -Real.log (125000000000 / 189160337383) := by
    rw [show ((189160337383 / 125000000000) : ℝ) = ((125000000000 / 189160337383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11124_neg : (20811339 / 50000000) ≤ -Real.log (500000000000 / 758114840723) ∧
    -Real.log (500000000000 / 758114840723) ≤ (416226781 / 1000000000) := by
  have h := checkLog_sound (w := (258114840723 / 1258114840723)) (n := 12)
    (lo := (20811339 / 50000000)) (hi := (416226781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((758114840723 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(758114840723 / 500000000000) = 1/(500000000000 / 758114840723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11124 : Bounds (20811339 / 50000000) (416226781 / 1000000000) (Real.log (758114840723 / 500000000000)) := by
  have h := reflection_log_11124_neg
  have he : Real.log (758114840723 / 500000000000) = -Real.log (500000000000 / 758114840723) := by
    rw [show ((758114840723 / 500000000000) : ℝ) = ((500000000000 / 758114840723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11125_neg : (840165161 / 1000000000) ≤ -Real.log (500000000000 / 1158374792703) ∧
    -Real.log (500000000000 / 1158374792703) ≤ (840165163 / 1000000000) := by
  have h := checkLog_sound (w := (158374792703 / 2158374792703)) (n := 12)
    (lo := (147017981 / 1000000000)) (hi := (73508991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1158374792703 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1158374792703 / 1000000000000) = 1/(500000000000 / 1158374792703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11125 : Bounds (840165161 / 1000000000) (840165163 / 1000000000) (Real.log (1158374792703 / 500000000000)) := by
  have h := reflection_log_11125_neg
  have he : Real.log (1158374792703 / 500000000000) = -Real.log (500000000000 / 1158374792703) := by
    rw [show ((1158374792703 / 500000000000) : ℝ) = ((500000000000 / 1158374792703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11126_neg : (210635119 / 250000000) ≤ -Real.log (500000000000 / 1161129568107) ∧
    -Real.log (500000000000 / 1161129568107) ≤ (421270239 / 500000000) := by
  have h := checkLog_sound (w := (161129568107 / 2161129568107)) (n := 12)
    (lo := (9337081 / 62500000)) (hi := (149393297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161129568107 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1161129568107 / 1000000000000) = 1/(500000000000 / 1161129568107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11126 : Bounds (210635119 / 250000000) (421270239 / 500000000) (Real.log (1161129568107 / 500000000000)) := by
  have h := reflection_log_11126_neg
  have he : Real.log (1161129568107 / 500000000000) = -Real.log (500000000000 / 1161129568107) := by
    rw [show ((1161129568107 / 500000000000) : ℝ) = ((500000000000 / 1161129568107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11127_neg : (67151539 / 200000000) ≤ -Real.log (1000 / 1399) ∧
    -Real.log (1000 / 1399) ≤ (2623107 / 7812500) := by
  have h := checkLog_sound (w := (399 / 2399)) (n := 12)
    (lo := (67151539 / 200000000)) (hi := (2623107 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1399 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1399 / 1000) = 1/(1000 / 1399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11127 : Bounds (67151539 / 200000000) (2623107 / 7812500) (Real.log (1399 / 1000)) := by
  have h := reflection_log_11127_neg
  have he : Real.log (1399 / 1000) = -Real.log (1000 / 1399) := by
    rw [show ((1399 / 1000) : ℝ) = ((1000 / 1399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11128_neg : (63645043 / 125000000) ≤ -Real.log (601 / 1000) ∧
    -Real.log (601 / 1000) ≤ (101832069 / 200000000) := by
  have h := checkLog_sound (w := (399 / 1601)) (n := 12)
    (lo := (63645043 / 125000000)) (hi := (101832069 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 601) = 1/(601 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11128 : Bounds (-101832069 / 200000000) (-63645043 / 125000000) (Real.log (601 / 1000)) := by
  have h := reflection_log_11128_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11129_neg : (9973 / 25000000) ≤ -Real.log (1000000 / 1000399) ∧
    -Real.log (1000000 / 1000399) ≤ (398921 / 1000000000) := by
  have h := checkLog_sound (w := (399 / 2000399)) (n := 12)
    (lo := (9973 / 25000000)) (hi := (398921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000399 / 1000000) = 1/(1000000 / 1000399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11129 : Bounds (9973 / 25000000) (398921 / 1000000000) (Real.log (1000399 / 1000000)) := by
  have h := reflection_log_11129_neg
  have he : Real.log (1000399 / 1000000) = -Real.log (1000000 / 1000399) := by
    rw [show ((1000399 / 1000000) : ℝ) = ((1000000 / 1000399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11130_neg : (399079 / 1000000000) ≤ -Real.log (999601 / 1000000) ∧
    -Real.log (999601 / 1000000) ≤ (9977 / 25000000) := by
  have h := checkLog_sound (w := (399 / 1999601)) (n := 12)
    (lo := (399079 / 1000000000)) (hi := (9977 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999601) = 1/(999601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11130 : Bounds (-9977 / 25000000) (-399079 / 1000000000) (Real.log (999601 / 1000000)) := by
  have h := reflection_log_11130_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11131_neg : (186291997 / 1000000000) ≤ -Real.log (500000 / 602387) ∧
    -Real.log (500000 / 602387) ≤ (93145999 / 500000000) := by
  have h := checkLog_sound (w := (102387 / 1102387)) (n := 12)
    (lo := (186291997 / 1000000000)) (hi := (93145999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602387 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602387 / 500000) = 1/(500000 / 602387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11131 : Bounds (186291997 / 1000000000) (93145999 / 500000000) (Real.log (602387 / 500000)) := by
  have h := reflection_log_11131_neg
  have he : Real.log (602387 / 500000) = -Real.log (500000 / 602387) := by
    rw [show ((602387 / 500000) : ℝ) = ((500000 / 602387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11132_neg : (229128927 / 1000000000) ≤ -Real.log (397613 / 500000) ∧
    -Real.log (397613 / 500000) ≤ (7160279 / 31250000) := by
  have h := checkLog_sound (w := (102387 / 897613)) (n := 12)
    (lo := (229128927 / 1000000000)) (hi := (7160279 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 397613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 397613) = 1/(397613 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11132 : Bounds (-7160279 / 31250000) (-229128927 / 1000000000) (Real.log (397613 / 500000)) := by
  have h := reflection_log_11132_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11133_neg : (93533473 / 500000000) ≤ -Real.log (250000 / 301427) ∧
    -Real.log (250000 / 301427) ≤ (187066947 / 1000000000) := by
  have h := checkLog_sound (w := (51427 / 551427)) (n := 12)
    (lo := (93533473 / 500000000)) (hi := (187066947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301427 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301427 / 250000) = 1/(250000 / 301427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11133 : Bounds (93533473 / 500000000) (187066947 / 1000000000) (Real.log (301427 / 250000)) := by
  have h := reflection_log_11133_neg
  have he : Real.log (301427 / 250000) = -Real.log (250000 / 301427) := by
    rw [show ((301427 / 250000) : ℝ) = ((250000 / 301427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11134_neg : (230304127 / 1000000000) ≤ -Real.log (198573 / 250000) ∧
    -Real.log (198573 / 250000) ≤ (1799251 / 7812500) := by
  have h := checkLog_sound (w := (51427 / 448573)) (n := 12)
    (lo := (230304127 / 1000000000)) (hi := (1799251 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 198573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 198573) = 1/(198573 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11134 : Bounds (-1799251 / 7812500) (-230304127 / 1000000000) (Real.log (198573 / 250000)) := by
  have h := reflection_log_11134_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11135_neg : (2161859 / 50000000) ≤ -Real.log (59855263671 / 62500000000) ∧
    -Real.log (59855263671 / 62500000000) ≤ (43237181 / 1000000000) := by
  have h := checkLog_sound (w := (2644736329 / 122355263671)) (n := 12)
    (lo := (2161859 / 50000000)) (hi := (43237181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59855263671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59855263671) = 1/(59855263671 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11135 : Bounds (-43237181 / 1000000000) (-2161859 / 50000000) (Real.log (59855263671 / 62500000000)) := by
  have h := reflection_log_11135_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0174 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11136_neg : (4283693 / 100000000) ≤ -Real.log (239516902231 / 250000000000) ∧
    -Real.log (239516902231 / 250000000000) ≤ (42836931 / 1000000000) := by
  have h := checkLog_sound (w := (10483097769 / 489516902231)) (n := 12)
    (lo := (4283693 / 100000000)) (hi := (42836931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 239516902231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 239516902231) = 1/(239516902231 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11136 : Bounds (-42836931 / 1000000000) (-4283693 / 100000000) (Real.log (239516902231 / 250000000000)) := by
  have h := reflection_log_11136_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11137_neg : (16616837 / 40000000) ≤ -Real.log (500000000000 / 757504156051) ∧
    -Real.log (500000000000 / 757504156051) ≤ (207710463 / 500000000) := by
  have h := checkLog_sound (w := (257504156051 / 1257504156051)) (n := 12)
    (lo := (16616837 / 40000000)) (hi := (207710463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((757504156051 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(757504156051 / 500000000000) = 1/(500000000000 / 757504156051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11137 : Bounds (16616837 / 40000000) (207710463 / 500000000) (Real.log (757504156051 / 500000000000)) := by
  have h := reflection_log_11137_neg
  have he : Real.log (757504156051 / 500000000000) = -Real.log (500000000000 / 757504156051) := by
    rw [show ((757504156051 / 500000000000) : ℝ) = ((500000000000 / 757504156051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11138_neg : (417371073 / 1000000000) ≤ -Real.log (250000000000 / 379491421291) ∧
    -Real.log (250000000000 / 379491421291) ≤ (208685537 / 500000000) := by
  have h := checkLog_sound (w := (129491421291 / 629491421291)) (n := 12)
    (lo := (417371073 / 1000000000)) (hi := (208685537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((379491421291 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(379491421291 / 250000000000) = 1/(250000000000 / 379491421291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11138 : Bounds (417371073 / 1000000000) (208685537 / 500000000) (Real.log (379491421291 / 250000000000)) := by
  have h := reflection_log_11138_neg
  have he : Real.log (379491421291 / 250000000000) = -Real.log (250000000000 / 379491421291) := by
    rw [show ((379491421291 / 250000000000) : ℝ) = ((250000000000 / 379491421291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11139_neg : (210635119 / 250000000) ≤ -Real.log (250000000000 / 580564784053) ∧
    -Real.log (250000000000 / 580564784053) ≤ (421270239 / 500000000) := by
  have h := checkLog_sound (w := (80564784053 / 1080564784053)) (n := 12)
    (lo := (9337081 / 62500000)) (hi := (149393297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((580564784053 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(580564784053 / 500000000000) = 1/(250000000000 / 580564784053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11139 : Bounds (210635119 / 250000000) (421270239 / 500000000) (Real.log (580564784053 / 250000000000)) := by
  have h := reflection_log_11139_neg
  have he : Real.log (580564784053 / 250000000000) = -Real.log (250000000000 / 580564784053) := by
    rw [show ((580564784053 / 250000000000) : ℝ) = ((250000000000 / 580564784053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11140_neg : (844918039 / 1000000000) ≤ -Real.log (15625000000 / 36371672213) ∧
    -Real.log (15625000000 / 36371672213) ≤ (844918041 / 1000000000) := by
  have h := checkLog_sound (w := (5121672213 / 67621672213)) (n := 12)
    (lo := (151770859 / 1000000000)) (hi := (7588543 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36371672213 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(36371672213 / 31250000000) = 1/(15625000000 / 36371672213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11140 : Bounds (844918039 / 1000000000) (844918041 / 1000000000) (Real.log (36371672213 / 15625000000)) := by
  have h := reflection_log_11140_neg
  have he : Real.log (36371672213 / 15625000000) = -Real.log (15625000000 / 36371672213) := by
    rw [show ((36371672213 / 15625000000) : ℝ) = ((15625000000 / 36371672213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11141_neg : (84118059 / 250000000) ≤ -Real.log (5 / 7) ∧
    -Real.log (5 / 7) ≤ (336472237 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 6)) (n := 12)
    (lo := (84118059 / 250000000)) (hi := (336472237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7 / 5) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7 / 5) = 1/(5 / 7) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11141 : Bounds (84118059 / 250000000) (336472237 / 1000000000) (Real.log (7 / 5)) := by
  have h := reflection_log_11141_neg
  have he : Real.log (7 / 5) = -Real.log (5 / 7) := by
    rw [show ((7 / 5) : ℝ) = ((5 / 7) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11142_neg : (510825623 / 1000000000) ≤ -Real.log (3 / 5) ∧
    -Real.log (3 / 5) ≤ (63853203 / 125000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5 / 3) = 1/(3 / 5) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11142 : Bounds (-63853203 / 125000000) (-510825623 / 1000000000) (Real.log (3 / 5)) := by
  have h := reflection_log_11142_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11143_neg : (4999 / 12500000) ≤ -Real.log (2500 / 2501) ∧
    -Real.log (2500 / 2501) ≤ (399921 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 5001)) (n := 12)
    (lo := (4999 / 12500000)) (hi := (399921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2501 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2501 / 2500) = 1/(2500 / 2501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11143 : Bounds (4999 / 12500000) (399921 / 1000000000) (Real.log (2501 / 2500)) := by
  have h := reflection_log_11143_neg
  have he : Real.log (2501 / 2500) = -Real.log (2500 / 2501) := by
    rw [show ((2501 / 2500) : ℝ) = ((2500 / 2501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11144_neg : (5001 / 12500000) ≤ -Real.log (2499 / 2500) ∧
    -Real.log (2499 / 2500) ≤ (400081 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 4999)) (n := 12)
    (lo := (5001 / 12500000)) (hi := (400081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2499) = 1/(2499 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11144 : Bounds (-400081 / 1000000000) (-5001 / 12500000) (Real.log (2499 / 2500)) := by
  have h := reflection_log_11144_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11145_neg : (186745091 / 1000000000) ≤ -Real.log (25000 / 30133) ∧
    -Real.log (25000 / 30133) ≤ (46686273 / 250000000) := by
  have h := checkLog_sound (w := (5133 / 55133)) (n := 12)
    (lo := (186745091 / 1000000000)) (hi := (46686273 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30133 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30133 / 25000) = 1/(25000 / 30133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11145 : Bounds (186745091 / 1000000000) (46686273 / 250000000) (Real.log (30133 / 25000)) := by
  have h := reflection_log_11145_neg
  have he : Real.log (30133 / 25000) = -Real.log (25000 / 30133) := by
    rw [show ((30133 / 25000) : ℝ) = ((25000 / 30133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11146_neg : (229815761 / 1000000000) ≤ -Real.log (19867 / 25000) ∧
    -Real.log (19867 / 25000) ≤ (114907881 / 500000000) := by
  have h := checkLog_sound (w := (5133 / 44867)) (n := 12)
    (lo := (229815761 / 1000000000)) (hi := (114907881 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 19867) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 19867) = 1/(19867 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11146 : Bounds (-114907881 / 500000000) (-229815761 / 1000000000) (Real.log (19867 / 25000)) := by
  have h := reflection_log_11146_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11147_neg : (93760259 / 500000000) ≤ -Real.log (200000 / 241251) ∧
    -Real.log (200000 / 241251) ≤ (187520519 / 1000000000) := by
  have h := checkLog_sound (w := (41251 / 441251)) (n := 12)
    (lo := (93760259 / 500000000)) (hi := (187520519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241251 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241251 / 200000) = 1/(200000 / 241251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11147 : Bounds (93760259 / 500000000) (187520519 / 1000000000) (Real.log (241251 / 200000)) := by
  have h := reflection_log_11147_neg
  have he : Real.log (241251 / 200000) = -Real.log (200000 / 241251) := by
    rw [show ((241251 / 200000) : ℝ) = ((200000 / 241251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11148_neg : (57748257 / 250000000) ≤ -Real.log (158749 / 200000) ∧
    -Real.log (158749 / 200000) ≤ (230993029 / 1000000000) := by
  have h := checkLog_sound (w := (41251 / 358749)) (n := 12)
    (lo := (57748257 / 250000000)) (hi := (230993029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 158749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 158749) = 1/(158749 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11148 : Bounds (-230993029 / 1000000000) (-57748257 / 250000000) (Real.log (158749 / 200000)) := by
  have h := reflection_log_11148_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11149_neg : (43472509 / 1000000000) ≤ -Real.log (38298354999 / 40000000000) ∧
    -Real.log (38298354999 / 40000000000) ≤ (4347251 / 100000000) := by
  have h := checkLog_sound (w := (1701645001 / 78298354999)) (n := 12)
    (lo := (43472509 / 1000000000)) (hi := (4347251 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38298354999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38298354999) = 1/(38298354999 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11149 : Bounds (-4347251 / 100000000) (-43472509 / 1000000000) (Real.log (38298354999 / 40000000000)) := by
  have h := reflection_log_11149_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11150_neg : (43070669 / 1000000000) ≤ -Real.log (598652311 / 625000000) ∧
    -Real.log (598652311 / 625000000) ≤ (4307067 / 100000000) := by
  have h := checkLog_sound (w := (26347689 / 1223652311)) (n := 12)
    (lo := (43070669 / 1000000000)) (hi := (4307067 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 598652311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 598652311) = 1/(598652311 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11150 : Bounds (-4307067 / 100000000) (-43070669 / 1000000000) (Real.log (598652311 / 625000000)) := by
  have h := reflection_log_11150_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11151_neg : (104140213 / 250000000) ≤ -Real.log (100000000000 / 151673629637) ∧
    -Real.log (100000000000 / 151673629637) ≤ (416560853 / 1000000000) := by
  have h := checkLog_sound (w := (51673629637 / 251673629637)) (n := 12)
    (lo := (104140213 / 250000000)) (hi := (416560853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151673629637 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151673629637 / 100000000000) = 1/(100000000000 / 151673629637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11151 : Bounds (104140213 / 250000000) (416560853 / 1000000000) (Real.log (151673629637 / 100000000000)) := by
  have h := reflection_log_11151_neg
  have he : Real.log (151673629637 / 100000000000) = -Real.log (100000000000 / 151673629637) := by
    rw [show ((151673629637 / 100000000000) : ℝ) = ((100000000000 / 151673629637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11152_neg : (209256773 / 500000000) ≤ -Real.log (500000000000 / 759850455751) ∧
    -Real.log (500000000000 / 759850455751) ≤ (418513547 / 1000000000) := by
  have h := checkLog_sound (w := (259850455751 / 1259850455751)) (n := 12)
    (lo := (209256773 / 500000000)) (hi := (418513547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((759850455751 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(759850455751 / 500000000000) = 1/(500000000000 / 759850455751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11152 : Bounds (209256773 / 500000000) (418513547 / 1000000000) (Real.log (759850455751 / 500000000000)) := by
  have h := reflection_log_11152_neg
  have he : Real.log (759850455751 / 500000000000) = -Real.log (500000000000 / 759850455751) := by
    rw [show ((759850455751 / 500000000000) : ℝ) = ((500000000000 / 759850455751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11153_neg : (844918039 / 1000000000) ≤ -Real.log (100000000000 / 232778702163) ∧
    -Real.log (100000000000 / 232778702163) ≤ (844918041 / 1000000000) := by
  have h := checkLog_sound (w := (32778702163 / 432778702163)) (n := 12)
    (lo := (151770859 / 1000000000)) (hi := (7588543 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((232778702163 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(232778702163 / 200000000000) = 1/(100000000000 / 232778702163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11153 : Bounds (844918039 / 1000000000) (844918041 / 1000000000) (Real.log (232778702163 / 100000000000)) := by
  have h := reflection_log_11153_neg
  have he : Real.log (232778702163 / 100000000000) = -Real.log (100000000000 / 232778702163) := by
    rw [show ((232778702163 / 100000000000) : ℝ) = ((100000000000 / 232778702163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11154_neg : (847297859 / 1000000000) ≤ -Real.log (500000000000 / 1166666666667) ∧
    -Real.log (500000000000 / 1166666666667) ≤ (847297861 / 1000000000) := by
  have h := checkLog_sound (w := (166666666667 / 2166666666667)) (n := 12)
    (lo := (154150679 / 1000000000)) (hi := (3853767 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1166666666667 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1166666666667 / 1000000000000) = 1/(500000000000 / 1166666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11154 : Bounds (847297859 / 1000000000) (847297861 / 1000000000) (Real.log (1166666666667 / 500000000000)) := by
  have h := reflection_log_11154_neg
  have he : Real.log (1166666666667 / 500000000000) = -Real.log (500000000000 / 1166666666667) := by
    rw [show ((1166666666667 / 500000000000) : ℝ) = ((500000000000 / 1166666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11155_neg : (337186267 / 1000000000) ≤ -Real.log (1000 / 1401) ∧
    -Real.log (1000 / 1401) ≤ (84296567 / 250000000) := by
  have h := checkLog_sound (w := (401 / 2401)) (n := 12)
    (lo := (337186267 / 1000000000)) (hi := (84296567 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1401 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1401 / 1000) = 1/(1000 / 1401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11155 : Bounds (337186267 / 1000000000) (84296567 / 250000000) (Real.log (1401 / 1000)) := by
  have h := reflection_log_11155_neg
  have he : Real.log (1401 / 1000) = -Real.log (1000 / 1401) := by
    rw [show ((1401 / 1000) : ℝ) = ((1000 / 1401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11156_neg : (6406171 / 12500000) ≤ -Real.log (599 / 1000) ∧
    -Real.log (599 / 1000) ≤ (512493681 / 1000000000) := by
  have h := checkLog_sound (w := (401 / 1599)) (n := 12)
    (lo := (6406171 / 12500000)) (hi := (512493681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 599) = 1/(599 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11156 : Bounds (-512493681 / 1000000000) (-6406171 / 12500000) (Real.log (599 / 1000)) := by
  have h := reflection_log_11156_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11157_neg : (400919 / 1000000000) ≤ -Real.log (1000000 / 1000401) ∧
    -Real.log (1000000 / 1000401) ≤ (10023 / 25000000) := by
  have h := checkLog_sound (w := (401 / 2000401)) (n := 12)
    (lo := (400919 / 1000000000)) (hi := (10023 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000401 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000401 / 1000000) = 1/(1000000 / 1000401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11157 : Bounds (400919 / 1000000000) (10023 / 25000000) (Real.log (1000401 / 1000000)) := by
  have h := reflection_log_11157_neg
  have he : Real.log (1000401 / 1000000) = -Real.log (1000000 / 1000401) := by
    rw [show ((1000401 / 1000000) : ℝ) = ((1000000 / 1000401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11158_neg : (10027 / 25000000) ≤ -Real.log (999599 / 1000000) ∧
    -Real.log (999599 / 1000000) ≤ (401081 / 1000000000) := by
  have h := checkLog_sound (w := (401 / 1999599)) (n := 12)
    (lo := (10027 / 25000000)) (hi := (401081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999599) = 1/(999599 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11158 : Bounds (-401081 / 1000000000) (-10027 / 25000000) (Real.log (999599 / 1000000)) := by
  have h := reflection_log_11158_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11159_neg : (18719881 / 100000000) ≤ -Real.log (1000000 / 1205867) ∧
    -Real.log (1000000 / 1205867) ≤ (187198811 / 1000000000) := by
  have h := checkLog_sound (w := (205867 / 2205867)) (n := 12)
    (lo := (18719881 / 100000000)) (hi := (187198811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1205867 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1205867 / 1000000) = 1/(1000000 / 1205867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11159 : Bounds (18719881 / 100000000) (187198811 / 1000000000) (Real.log (1205867 / 1000000)) := by
  have h := reflection_log_11159_neg
  have he : Real.log (1205867 / 1000000) = -Real.log (1000000 / 1205867) := by
    rw [show ((1205867 / 1000000) : ℝ) = ((1000000 / 1205867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11160_neg : (9220173 / 40000000) ≤ -Real.log (794133 / 1000000) ∧
    -Real.log (794133 / 1000000) ≤ (115252163 / 500000000) := by
  have h := checkLog_sound (w := (205867 / 1794133)) (n := 12)
    (lo := (9220173 / 40000000)) (hi := (115252163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 794133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 794133) = 1/(794133 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11160 : Bounds (-115252163 / 500000000) (-9220173 / 40000000) (Real.log (794133 / 1000000)) := by
  have h := reflection_log_11160_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11161_neg : (37594777 / 200000000) ≤ -Real.log (500000 / 603401) ∧
    -Real.log (500000 / 603401) ≤ (93986943 / 500000000) := by
  have h := checkLog_sound (w := (103401 / 1103401)) (n := 12)
    (lo := (37594777 / 200000000)) (hi := (93986943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603401 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603401 / 500000) = 1/(500000 / 603401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11161 : Bounds (37594777 / 200000000) (93986943 / 500000000) (Real.log (603401 / 500000)) := by
  have h := reflection_log_11161_neg
  have he : Real.log (603401 / 500000) = -Real.log (500000 / 603401) := by
    rw [show ((603401 / 500000) : ℝ) = ((500000 / 603401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11162_neg : (231682403 / 1000000000) ≤ -Real.log (396599 / 500000) ∧
    -Real.log (396599 / 500000) ≤ (57920601 / 250000000) := by
  have h := checkLog_sound (w := (103401 / 896599)) (n := 12)
    (lo := (231682403 / 1000000000)) (hi := (57920601 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 396599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 396599) = 1/(396599 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11162 : Bounds (-57920601 / 250000000) (-231682403 / 1000000000) (Real.log (396599 / 500000)) := by
  have h := reflection_log_11162_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11163_neg : (21854259 / 500000000) ≤ -Real.log (239308233199 / 250000000000) ∧
    -Real.log (239308233199 / 250000000000) ≤ (43708519 / 1000000000) := by
  have h := checkLog_sound (w := (10691766801 / 489308233199)) (n := 12)
    (lo := (21854259 / 500000000)) (hi := (43708519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 239308233199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 239308233199) = 1/(239308233199 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11163 : Bounds (-43708519 / 1000000000) (-21854259 / 500000000) (Real.log (239308233199 / 250000000000)) := by
  have h := reflection_log_11163_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11164_neg : (8661103 / 200000000) ≤ -Real.log (957618778311 / 1000000000000) ∧
    -Real.log (957618778311 / 1000000000000) ≤ (10826379 / 250000000) := by
  have h := checkLog_sound (w := (42381221689 / 1957618778311)) (n := 12)
    (lo := (8661103 / 200000000)) (hi := (10826379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 957618778311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 957618778311) = 1/(957618778311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11164 : Bounds (-10826379 / 250000000) (-8661103 / 200000000) (Real.log (957618778311 / 1000000000000)) := by
  have h := reflection_log_11164_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11165_neg : (83540627 / 200000000) ≤ -Real.log (10000000000 / 15184698281) ∧
    -Real.log (10000000000 / 15184698281) ≤ (13053223 / 31250000) := by
  have h := checkLog_sound (w := (5184698281 / 25184698281)) (n := 12)
    (lo := (83540627 / 200000000)) (hi := (13053223 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15184698281 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15184698281 / 10000000000) = 1/(10000000000 / 15184698281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11165 : Bounds (83540627 / 200000000) (13053223 / 31250000) (Real.log (15184698281 / 10000000000)) := by
  have h := reflection_log_11165_neg
  have he : Real.log (15184698281 / 10000000000) = -Real.log (10000000000 / 15184698281) := by
    rw [show ((15184698281 / 10000000000) : ℝ) = ((10000000000 / 15184698281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11166_neg : (419656289 / 1000000000) ≤ -Real.log (125000000000 / 190179816389) ∧
    -Real.log (125000000000 / 190179816389) ≤ (41965629 / 100000000) := by
  have h := checkLog_sound (w := (65179816389 / 315179816389)) (n := 12)
    (lo := (419656289 / 1000000000)) (hi := (41965629 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190179816389 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(190179816389 / 125000000000) = 1/(125000000000 / 190179816389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11166 : Bounds (419656289 / 1000000000) (41965629 / 100000000) (Real.log (190179816389 / 125000000000)) := by
  have h := reflection_log_11166_neg
  have he : Real.log (190179816389 / 125000000000) = -Real.log (125000000000 / 190179816389) := by
    rw [show ((190179816389 / 125000000000) : ℝ) = ((125000000000 / 190179816389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11167_neg : (847297859 / 1000000000) ≤ -Real.log (250000000000 / 583333333333) ∧
    -Real.log (250000000000 / 583333333333) ≤ (847297861 / 1000000000) := by
  have h := checkLog_sound (w := (83333333333 / 1083333333333)) (n := 12)
    (lo := (154150679 / 1000000000)) (hi := (3853767 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583333333333 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(583333333333 / 500000000000) = 1/(250000000000 / 583333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11167 : Bounds (847297859 / 1000000000) (847297861 / 1000000000) (Real.log (583333333333 / 250000000000)) := by
  have h := reflection_log_11167_neg
  have he : Real.log (583333333333 / 250000000000) = -Real.log (250000000000 / 583333333333) := by
    rw [show ((583333333333 / 250000000000) : ℝ) = ((250000000000 / 583333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11168_neg : (849679947 / 1000000000) ≤ -Real.log (125000000000 / 292362270451) ∧
    -Real.log (125000000000 / 292362270451) ≤ (849679949 / 1000000000) := by
  have h := checkLog_sound (w := (42362270451 / 542362270451)) (n := 12)
    (lo := (156532767 / 1000000000)) (hi := (4891649 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292362270451 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(292362270451 / 250000000000) = 1/(125000000000 / 292362270451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11168 : Bounds (849679947 / 1000000000) (849679949 / 1000000000) (Real.log (292362270451 / 125000000000)) := by
  have h := reflection_log_11168_neg
  have he : Real.log (292362270451 / 125000000000) = -Real.log (125000000000 / 292362270451) := by
    rw [show ((292362270451 / 125000000000) : ℝ) = ((125000000000 / 292362270451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11169_neg : (84474947 / 250000000) ≤ -Real.log (500 / 701) ∧
    -Real.log (500 / 701) ≤ (337899789 / 1000000000) := by
  have h := checkLog_sound (w := (201 / 1201)) (n := 12)
    (lo := (84474947 / 250000000)) (hi := (337899789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((701 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(701 / 500) = 1/(500 / 701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11169 : Bounds (84474947 / 250000000) (337899789 / 1000000000) (Real.log (701 / 500)) := by
  have h := reflection_log_11169_neg
  have he : Real.log (701 / 500) = -Real.log (500 / 701) := by
    rw [show ((701 / 500) : ℝ) = ((500 / 701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11170_neg : (20566581 / 40000000) ≤ -Real.log (299 / 500) ∧
    -Real.log (299 / 500) ≤ (257082263 / 500000000) := by
  have h := checkLog_sound (w := (201 / 799)) (n := 12)
    (lo := (20566581 / 40000000)) (hi := (257082263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 299) = 1/(299 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11170 : Bounds (-257082263 / 500000000) (-20566581 / 40000000) (Real.log (299 / 500)) := by
  have h := reflection_log_11170_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11171_neg : (401919 / 1000000000) ≤ -Real.log (500000 / 500201) ∧
    -Real.log (500000 / 500201) ≤ (157 / 390625) := by
  have h := checkLog_sound (w := (201 / 1000201)) (n := 12)
    (lo := (401919 / 1000000000)) (hi := (157 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500201 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500201 / 500000) = 1/(500000 / 500201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11171 : Bounds (401919 / 1000000000) (157 / 390625) (Real.log (500201 / 500000)) := by
  have h := reflection_log_11171_neg
  have he : Real.log (500201 / 500000) = -Real.log (500000 / 500201) := by
    rw [show ((500201 / 500000) : ℝ) = ((500000 / 500201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11172_neg : (2513 / 6250000) ≤ -Real.log (499799 / 500000) ∧
    -Real.log (499799 / 500000) ≤ (402081 / 1000000000) := by
  have h := checkLog_sound (w := (201 / 999799)) (n := 12)
    (lo := (2513 / 6250000)) (hi := (402081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499799) = 1/(499799 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11172 : Bounds (-402081 / 1000000000) (-2513 / 6250000) (Real.log (499799 / 500000)) := by
  have h := reflection_log_11172_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11173_neg : (93825747 / 500000000) ≤ -Real.log (1000000 / 1206413) ∧
    -Real.log (1000000 / 1206413) ≤ (37530299 / 200000000) := by
  have h := checkLog_sound (w := (206413 / 2206413)) (n := 12)
    (lo := (93825747 / 500000000)) (hi := (37530299 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1206413 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1206413 / 1000000) = 1/(1000000 / 1206413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11173 : Bounds (93825747 / 500000000) (37530299 / 200000000) (Real.log (1206413 / 1000000)) := by
  have h := reflection_log_11173_neg
  have he : Real.log (1206413 / 1000000) = -Real.log (1000000 / 1206413) := by
    rw [show ((1206413 / 1000000) : ℝ) = ((1000000 / 1206413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11174_neg : (28899013 / 125000000) ≤ -Real.log (793587 / 1000000) ∧
    -Real.log (793587 / 1000000) ≤ (46238421 / 200000000) := by
  have h := checkLog_sound (w := (206413 / 1793587)) (n := 12)
    (lo := (28899013 / 125000000)) (hi := (46238421 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 793587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 793587) = 1/(793587 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11174 : Bounds (-46238421 / 200000000) (-28899013 / 125000000) (Real.log (793587 / 1000000)) := by
  have h := reflection_log_11174_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11175_neg : (1507423 / 8000000) ≤ -Real.log (20000 / 24147) ∧
    -Real.log (20000 / 24147) ≤ (47106969 / 250000000) := by
  have h := checkLog_sound (w := (4147 / 44147)) (n := 12)
    (lo := (1507423 / 8000000)) (hi := (47106969 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24147 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24147 / 20000) = 1/(20000 / 24147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11175 : Bounds (1507423 / 8000000) (47106969 / 250000000) (Real.log (24147 / 20000)) := by
  have h := reflection_log_11175_neg
  have he : Real.log (24147 / 20000) = -Real.log (20000 / 24147) := by
    rw [show ((24147 / 20000) : ℝ) = ((20000 / 24147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11176_neg : (58093379 / 250000000) ≤ -Real.log (15853 / 20000) ∧
    -Real.log (15853 / 20000) ≤ (232373517 / 1000000000) := by
  have h := checkLog_sound (w := (4147 / 35853)) (n := 12)
    (lo := (58093379 / 250000000)) (hi := (232373517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 15853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 15853) = 1/(15853 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11176 : Bounds (-232373517 / 1000000000) (-58093379 / 250000000) (Real.log (15853 / 20000)) := by
  have h := reflection_log_11176_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11177_neg : (43945641 / 1000000000) ≤ -Real.log (382802391 / 400000000) ∧
    -Real.log (382802391 / 400000000) ≤ (21972821 / 500000000) := by
  have h := checkLog_sound (w := (17197609 / 782802391)) (n := 12)
    (lo := (43945641 / 1000000000)) (hi := (21972821 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 382802391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 382802391) = 1/(382802391 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11177 : Bounds (-21972821 / 500000000) (-43945641 / 1000000000) (Real.log (382802391 / 400000000)) := by
  have h := reflection_log_11177_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11178_neg : (4354061 / 100000000) ≤ -Real.log (957393673431 / 1000000000000) ∧
    -Real.log (957393673431 / 1000000000000) ≤ (43540611 / 1000000000) := by
  have h := checkLog_sound (w := (42606326569 / 1957393673431)) (n := 12)
    (lo := (4354061 / 100000000)) (hi := (43540611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 957393673431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 957393673431) = 1/(957393673431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11178 : Bounds (-43540611 / 1000000000) (-4354061 / 100000000) (Real.log (957393673431 / 1000000000000)) := by
  have h := reflection_log_11178_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11179_neg : (209421799 / 500000000) ≤ -Real.log (500000000000 / 760101286941) ∧
    -Real.log (500000000000 / 760101286941) ≤ (418843599 / 1000000000) := by
  have h := checkLog_sound (w := (260101286941 / 1260101286941)) (n := 12)
    (lo := (209421799 / 500000000)) (hi := (418843599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((760101286941 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(760101286941 / 500000000000) = 1/(500000000000 / 760101286941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11179 : Bounds (209421799 / 500000000) (418843599 / 1000000000) (Real.log (760101286941 / 500000000000)) := by
  have h := reflection_log_11179_neg
  have he : Real.log (760101286941 / 500000000000) = -Real.log (500000000000 / 760101286941) := by
    rw [show ((760101286941 / 500000000000) : ℝ) = ((500000000000 / 760101286941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11180_neg : (420801391 / 1000000000) ≤ -Real.log (500000000000 / 761590866083) ∧
    -Real.log (500000000000 / 761590866083) ≤ (26300087 / 62500000) := by
  have h := checkLog_sound (w := (261590866083 / 1261590866083)) (n := 12)
    (lo := (420801391 / 1000000000)) (hi := (26300087 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((761590866083 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(761590866083 / 500000000000) = 1/(500000000000 / 761590866083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11180 : Bounds (420801391 / 1000000000) (26300087 / 62500000) (Real.log (761590866083 / 500000000000)) := by
  have h := reflection_log_11180_neg
  have he : Real.log (761590866083 / 500000000000) = -Real.log (500000000000 / 761590866083) := by
    rw [show ((761590866083 / 500000000000) : ℝ) = ((500000000000 / 761590866083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11181_neg : (849679947 / 1000000000) ≤ -Real.log (500000000000 / 1169449081803) ∧
    -Real.log (500000000000 / 1169449081803) ≤ (849679949 / 1000000000) := by
  have h := checkLog_sound (w := (169449081803 / 2169449081803)) (n := 12)
    (lo := (156532767 / 1000000000)) (hi := (4891649 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1169449081803 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1169449081803 / 1000000000000) = 1/(500000000000 / 1169449081803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11181 : Bounds (849679947 / 1000000000) (849679949 / 1000000000) (Real.log (1169449081803 / 500000000000)) := by
  have h := reflection_log_11181_neg
  have he : Real.log (1169449081803 / 500000000000) = -Real.log (500000000000 / 1169449081803) := by
    rw [show ((1169449081803 / 500000000000) : ℝ) = ((500000000000 / 1169449081803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11182_neg : (852064313 / 1000000000) ≤ -Real.log (125000000000 / 293060200669) ∧
    -Real.log (125000000000 / 293060200669) ≤ (170412863 / 200000000) := by
  have h := checkLog_sound (w := (43060200669 / 543060200669)) (n := 12)
    (lo := (158917133 / 1000000000)) (hi := (79458567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293060200669 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(293060200669 / 250000000000) = 1/(125000000000 / 293060200669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11182 : Bounds (852064313 / 1000000000) (170412863 / 200000000) (Real.log (293060200669 / 125000000000)) := by
  have h := reflection_log_11182_neg
  have he : Real.log (293060200669 / 125000000000) = -Real.log (125000000000 / 293060200669) := by
    rw [show ((293060200669 / 125000000000) : ℝ) = ((125000000000 / 293060200669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11183_neg : (338612801 / 1000000000) ≤ -Real.log (1000 / 1403) ∧
    -Real.log (1000 / 1403) ≤ (169306401 / 500000000) := by
  have h := checkLog_sound (w := (403 / 2403)) (n := 12)
    (lo := (338612801 / 1000000000)) (hi := (169306401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1403 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1403 / 1000) = 1/(1000 / 1403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11183 : Bounds (338612801 / 1000000000) (169306401 / 500000000) (Real.log (1403 / 1000)) := by
  have h := reflection_log_11183_neg
  have he : Real.log (1403 / 1000) = -Real.log (1000 / 1403) := by
    rw [show ((1403 / 1000) : ℝ) = ((1000 / 1403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11184_neg : (103167633 / 200000000) ≤ -Real.log (597 / 1000) ∧
    -Real.log (597 / 1000) ≤ (257919083 / 500000000) := by
  have h := checkLog_sound (w := (403 / 1597)) (n := 12)
    (lo := (103167633 / 200000000)) (hi := (257919083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 597) = 1/(597 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11184 : Bounds (-257919083 / 500000000) (-103167633 / 200000000) (Real.log (597 / 1000)) := by
  have h := reflection_log_11184_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11185_neg : (201459 / 500000000) ≤ -Real.log (1000000 / 1000403) ∧
    -Real.log (1000000 / 1000403) ≤ (402919 / 1000000000) := by
  have h := checkLog_sound (w := (403 / 2000403)) (n := 12)
    (lo := (201459 / 500000000)) (hi := (402919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000403 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000403 / 1000000) = 1/(1000000 / 1000403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11185 : Bounds (201459 / 500000000) (402919 / 1000000000) (Real.log (1000403 / 1000000)) := by
  have h := reflection_log_11185_neg
  have he : Real.log (1000403 / 1000000) = -Real.log (1000000 / 1000403) := by
    rw [show ((1000403 / 1000000) : ℝ) = ((1000000 / 1000403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11186_neg : (403081 / 1000000000) ≤ -Real.log (999597 / 1000000) ∧
    -Real.log (999597 / 1000000) ≤ (201541 / 500000000) := by
  have h := checkLog_sound (w := (403 / 1999597)) (n := 12)
    (lo := (403081 / 1000000000)) (hi := (201541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999597) = 1/(999597 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11186 : Bounds (-201541 / 500000000) (-403081 / 1000000000) (Real.log (999597 / 1000000)) := by
  have h := reflection_log_11186_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11187_neg : (188104801 / 1000000000) ≤ -Real.log (12500 / 15087) ∧
    -Real.log (12500 / 15087) ≤ (94052401 / 500000000) := by
  have h := checkLog_sound (w := (2587 / 27587)) (n := 12)
    (lo := (188104801 / 1000000000)) (hi := (94052401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15087 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15087 / 12500) = 1/(12500 / 15087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11187 : Bounds (188104801 / 1000000000) (94052401 / 500000000) (Real.log (15087 / 12500)) := by
  have h := reflection_log_11187_neg
  have he : Real.log (15087 / 12500) = -Real.log (12500 / 15087) := by
    rw [show ((15087 / 12500) : ℝ) = ((12500 / 15087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11188_neg : (231881617 / 1000000000) ≤ -Real.log (9913 / 12500) ∧
    -Real.log (9913 / 12500) ≤ (115940809 / 500000000) := by
  have h := checkLog_sound (w := (2587 / 22413)) (n := 12)
    (lo := (231881617 / 1000000000)) (hi := (115940809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 9913) = 1/(9913 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11188 : Bounds (-115940809 / 500000000) (-231881617 / 1000000000) (Real.log (9913 / 12500)) := by
  have h := reflection_log_11188_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11189_neg : (94441243 / 500000000) ≤ -Real.log (1000000 / 1207899) ∧
    -Real.log (1000000 / 1207899) ≤ (188882487 / 1000000000) := by
  have h := checkLog_sound (w := (207899 / 2207899)) (n := 12)
    (lo := (94441243 / 500000000)) (hi := (188882487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1207899 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1207899 / 1000000) = 1/(1000000 / 1207899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11189 : Bounds (94441243 / 500000000) (188882487 / 1000000000) (Real.log (1207899 / 1000000)) := by
  have h := reflection_log_11189_neg
  have he : Real.log (1207899 / 1000000) = -Real.log (1000000 / 1207899) := by
    rw [show ((1207899 / 1000000) : ℝ) = ((1000000 / 1207899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11190_neg : (23306637 / 100000000) ≤ -Real.log (792101 / 1000000) ∧
    -Real.log (792101 / 1000000) ≤ (233066371 / 1000000000) := by
  have h := checkLog_sound (w := (207899 / 1792101)) (n := 12)
    (lo := (23306637 / 100000000)) (hi := (233066371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 792101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 792101) = 1/(792101 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11190 : Bounds (-233066371 / 1000000000) (-23306637 / 100000000) (Real.log (792101 / 1000000)) := by
  have h := reflection_log_11190_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11191_neg : (44183883 / 1000000000) ≤ -Real.log (956778005799 / 1000000000000) ∧
    -Real.log (956778005799 / 1000000000000) ≤ (11045971 / 250000000) := by
  have h := checkLog_sound (w := (43221994201 / 1956778005799)) (n := 12)
    (lo := (44183883 / 1000000000)) (hi := (11045971 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 956778005799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 956778005799) = 1/(956778005799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11191 : Bounds (-11045971 / 250000000) (-44183883 / 1000000000) (Real.log (956778005799 / 1000000000000)) := by
  have h := reflection_log_11191_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11192_neg : (8755363 / 200000000) ≤ -Real.log (149557431 / 156250000) ∧
    -Real.log (149557431 / 156250000) ≤ (2736051 / 62500000) := by
  have h := checkLog_sound (w := (6692569 / 305807431)) (n := 12)
    (lo := (8755363 / 200000000)) (hi := (2736051 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 149557431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 149557431) = 1/(149557431 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11192 : Bounds (-2736051 / 62500000) (-8755363 / 200000000) (Real.log (149557431 / 156250000)) := by
  have h := reflection_log_11192_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11193_neg : (209993209 / 500000000) ≤ -Real.log (125000000000 / 190242610713) ∧
    -Real.log (125000000000 / 190242610713) ≤ (419986419 / 1000000000) := by
  have h := checkLog_sound (w := (65242610713 / 315242610713)) (n := 12)
    (lo := (209993209 / 500000000)) (hi := (419986419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190242610713 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(190242610713 / 125000000000) = 1/(125000000000 / 190242610713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11193 : Bounds (209993209 / 500000000) (419986419 / 1000000000) (Real.log (190242610713 / 125000000000)) := by
  have h := reflection_log_11193_neg
  have he : Real.log (190242610713 / 125000000000) = -Real.log (125000000000 / 190242610713) := by
    rw [show ((190242610713 / 125000000000) : ℝ) = ((125000000000 / 190242610713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11194_neg : (52743607 / 125000000) ≤ -Real.log (20000000000 / 30498610657) ∧
    -Real.log (20000000000 / 30498610657) ≤ (421948857 / 1000000000) := by
  have h := checkLog_sound (w := (10498610657 / 50498610657)) (n := 12)
    (lo := (52743607 / 125000000)) (hi := (421948857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30498610657 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30498610657 / 20000000000) = 1/(20000000000 / 30498610657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11194 : Bounds (52743607 / 125000000) (421948857 / 1000000000) (Real.log (30498610657 / 20000000000)) := by
  have h := reflection_log_11194_neg
  have he : Real.log (30498610657 / 20000000000) = -Real.log (20000000000 / 30498610657) := by
    rw [show ((30498610657 / 20000000000) : ℝ) = ((20000000000 / 30498610657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11195_neg : (852064313 / 1000000000) ≤ -Real.log (20000000000 / 46889632107) ∧
    -Real.log (20000000000 / 46889632107) ≤ (170412863 / 200000000) := by
  have h := checkLog_sound (w := (6889632107 / 86889632107)) (n := 12)
    (lo := (158917133 / 1000000000)) (hi := (79458567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46889632107 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(46889632107 / 40000000000) = 1/(20000000000 / 46889632107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11195 : Bounds (852064313 / 1000000000) (170412863 / 200000000) (Real.log (46889632107 / 20000000000)) := by
  have h := reflection_log_11195_neg
  have he : Real.log (46889632107 / 20000000000) = -Real.log (20000000000 / 46889632107) := by
    rw [show ((46889632107 / 20000000000) : ℝ) = ((20000000000 / 46889632107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11196_neg : (427225483 / 500000000) ≤ -Real.log (500000000000 / 1175041876047) ∧
    -Real.log (500000000000 / 1175041876047) ≤ (106806371 / 125000000) := by
  have h := checkLog_sound (w := (175041876047 / 2175041876047)) (n := 12)
    (lo := (80651893 / 500000000)) (hi := (161303787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1175041876047 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1175041876047 / 1000000000000) = 1/(500000000000 / 1175041876047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11196 : Bounds (427225483 / 500000000) (106806371 / 125000000) (Real.log (1175041876047 / 500000000000)) := by
  have h := reflection_log_11196_neg
  have he : Real.log (1175041876047 / 500000000000) = -Real.log (500000000000 / 1175041876047) := by
    rw [show ((1175041876047 / 500000000000) : ℝ) = ((500000000000 / 1175041876047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11197_neg : (67865061 / 200000000) ≤ -Real.log (250 / 351) ∧
    -Real.log (250 / 351) ≤ (169662653 / 500000000) := by
  have h := checkLog_sound (w := (101 / 601)) (n := 12)
    (lo := (67865061 / 200000000)) (hi := (169662653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351 / 250) = 1/(250 / 351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11197 : Bounds (67865061 / 200000000) (169662653 / 500000000) (Real.log (351 / 250)) := by
  have h := reflection_log_11197_neg
  have he : Real.log (351 / 250) = -Real.log (250 / 351) := by
    rw [show ((351 / 250) : ℝ) = ((250 / 351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11198_neg : (517514611 / 1000000000) ≤ -Real.log (149 / 250) ∧
    -Real.log (149 / 250) ≤ (129378653 / 250000000) := by
  have h := checkLog_sound (w := (101 / 399)) (n := 12)
    (lo := (517514611 / 1000000000)) (hi := (129378653 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 149) = 1/(149 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11198 : Bounds (-129378653 / 250000000) (-517514611 / 1000000000) (Real.log (149 / 250)) := by
  have h := reflection_log_11198_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11199_neg : (201959 / 500000000) ≤ -Real.log (250000 / 250101) ∧
    -Real.log (250000 / 250101) ≤ (403919 / 1000000000) := by
  have h := checkLog_sound (w := (101 / 500101)) (n := 12)
    (lo := (201959 / 500000000)) (hi := (403919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250101 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250101 / 250000) = 1/(250000 / 250101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11199 : Bounds (201959 / 500000000) (403919 / 1000000000) (Real.log (250101 / 250000)) := by
  have h := reflection_log_11199_neg
  have he : Real.log (250101 / 250000) = -Real.log (250000 / 250101) := by
    rw [show ((250101 / 250000) : ℝ) = ((250000 / 250101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


