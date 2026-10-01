-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0141__4_q02
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0141__4_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:34:36.278412+00:00
-- url     : https://prove2.me/theorems/a83109b0-dc19-4c58-a77e-5c74a2b8a5f4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0141 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0142, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0141 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0142, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0143, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0144) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0141 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0142, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0143, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0144) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0141 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0142, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0143, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0144) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0141 (+3 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0142, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0143, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0144) (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0141__4_q01

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0143 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9152_neg : (15180593 / 100000000) ≤ -Real.log (171831 / 200000) ∧
    -Real.log (171831 / 200000) ≤ (151805931 / 1000000000) := by
  have h := checkLog_sound (w := (28169 / 371831)) (n := 12)
    (lo := (15180593 / 100000000)) (hi := (151805931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 171831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 171831) = 1/(171831 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9152 : Bounds (-151805931 / 1000000000) (-15180593 / 100000000) (Real.log (171831 / 200000)) := by
  have h := reflection_log_9152_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9153_neg : (33059733 / 250000000) ≤ -Real.log (1000000 / 1141381) ∧
    -Real.log (1000000 / 1141381) ≤ (132238933 / 1000000000) := by
  have h := checkLog_sound (w := (141381 / 2141381)) (n := 12)
    (lo := (33059733 / 250000000)) (hi := (132238933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1141381 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1141381 / 1000000) = 1/(1000000 / 1141381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9153 : Bounds (33059733 / 250000000) (132238933 / 1000000000) (Real.log (1141381 / 1000000)) := by
  have h := reflection_log_9153_neg
  have he : Real.log (1141381 / 1000000) = -Real.log (1000000 / 1141381) := by
    rw [show ((1141381 / 1000000) : ℝ) = ((1000000 / 1141381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9154_neg : (76214997 / 500000000) ≤ -Real.log (858619 / 1000000) ∧
    -Real.log (858619 / 1000000) ≤ (30485999 / 200000000) := by
  have h := checkLog_sound (w := (141381 / 1858619)) (n := 12)
    (lo := (76214997 / 500000000)) (hi := (30485999 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 858619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 858619) = 1/(858619 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9154 : Bounds (-30485999 / 200000000) (-76214997 / 500000000) (Real.log (858619 / 1000000)) := by
  have h := reflection_log_9154_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9155_neg : (20191061 / 1000000000) ≤ -Real.log (980011412839 / 1000000000000) ∧
    -Real.log (980011412839 / 1000000000000) ≤ (10095531 / 500000000) := by
  have h := checkLog_sound (w := (19988587161 / 1980011412839)) (n := 12)
    (lo := (20191061 / 1000000000)) (hi := (10095531 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980011412839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980011412839) = 1/(980011412839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9155 : Bounds (-10095531 / 500000000) (-20191061 / 1000000000) (Real.log (980011412839 / 1000000000000)) := by
  have h := reflection_log_9155_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9156_neg : (10018357 / 500000000) ≤ -Real.log (39206507439 / 40000000000) ∧
    -Real.log (39206507439 / 40000000000) ≤ (4007343 / 200000000) := by
  have h := checkLog_sound (w := (793492561 / 79206507439)) (n := 12)
    (lo := (10018357 / 500000000)) (hi := (4007343 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39206507439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39206507439) = 1/(39206507439 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9156 : Bounds (-4007343 / 200000000) (-10018357 / 500000000) (Real.log (39206507439 / 40000000000)) := by
  have h := reflection_log_9156_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9157_neg : (141787573 / 500000000) ≤ -Real.log (20000000000 / 26557373233) ∧
    -Real.log (20000000000 / 26557373233) ≤ (283575147 / 1000000000) := by
  have h := checkLog_sound (w := (6557373233 / 46557373233)) (n := 12)
    (lo := (141787573 / 500000000)) (hi := (283575147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26557373233 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26557373233 / 20000000000) = 1/(20000000000 / 26557373233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9157 : Bounds (141787573 / 500000000) (283575147 / 1000000000) (Real.log (26557373233 / 20000000000)) := by
  have h := reflection_log_9157_neg
  have he : Real.log (26557373233 / 20000000000) = -Real.log (20000000000 / 26557373233) := by
    rw [show ((26557373233 / 20000000000) : ℝ) = ((20000000000 / 26557373233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9158_neg : (284668927 / 1000000000) ≤ -Real.log (250000000000 / 332330463221) ∧
    -Real.log (250000000000 / 332330463221) ≤ (555994 / 1953125) := by
  have h := checkLog_sound (w := (82330463221 / 582330463221)) (n := 12)
    (lo := (284668927 / 1000000000)) (hi := (555994 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((332330463221 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(332330463221 / 250000000000) = 1/(250000000000 / 332330463221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9158 : Bounds (284668927 / 1000000000) (555994 / 1953125) (Real.log (332330463221 / 250000000000)) := by
  have h := reflection_log_9158_neg
  have he : Real.log (332330463221 / 250000000000) = -Real.log (250000000000 / 332330463221) := by
    rw [show ((332330463221 / 250000000000) : ℝ) = ((250000000000 / 332330463221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9159_neg : (8922289 / 15625000) ≤ -Real.log (250000000000 / 442520775623) ∧
    -Real.log (250000000000 / 442520775623) ≤ (571026497 / 1000000000) := by
  have h := checkLog_sound (w := (192520775623 / 692520775623)) (n := 12)
    (lo := (8922289 / 15625000)) (hi := (571026497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((442520775623 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(442520775623 / 250000000000) = 1/(250000000000 / 442520775623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9159 : Bounds (8922289 / 15625000) (571026497 / 1000000000) (Real.log (442520775623 / 250000000000)) := by
  have h := reflection_log_9159_neg
  have he : Real.log (442520775623 / 250000000000) = -Real.log (250000000000 / 442520775623) := by
    rw [show ((442520775623 / 250000000000) : ℝ) = ((250000000000 / 442520775623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9160_neg : (35756901 / 62500000) ≤ -Real.log (250000000000 / 443000693001) ∧
    -Real.log (250000000000 / 443000693001) ≤ (572110417 / 1000000000) := by
  have h := checkLog_sound (w := (193000693001 / 693000693001)) (n := 12)
    (lo := (35756901 / 62500000)) (hi := (572110417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((443000693001 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(443000693001 / 250000000000) = 1/(250000000000 / 443000693001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9160 : Bounds (35756901 / 62500000) (572110417 / 1000000000) (Real.log (443000693001 / 250000000000)) := by
  have h := reflection_log_9160_neg
  have he : Real.log (443000693001 / 250000000000) = -Real.log (250000000000 / 443000693001) := by
    rw [show ((443000693001 / 250000000000) : ℝ) = ((250000000000 / 443000693001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9161_neg : (123039261 / 500000000) ≤ -Real.log (1000 / 1279) ∧
    -Real.log (1000 / 1279) ≤ (246078523 / 1000000000) := by
  have h := checkLog_sound (w := (279 / 2279)) (n := 12)
    (lo := (123039261 / 500000000)) (hi := (246078523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1279 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1279 / 1000) = 1/(1000 / 1279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9161 : Bounds (123039261 / 500000000) (246078523 / 1000000000) (Real.log (1279 / 1000)) := by
  have h := reflection_log_9161_neg
  have he : Real.log (1279 / 1000) = -Real.log (1000 / 1279) := by
    rw [show ((1279 / 1000) : ℝ) = ((1000 / 1279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9162_neg : (327116141 / 1000000000) ≤ -Real.log (721 / 1000) ∧
    -Real.log (721 / 1000) ≤ (163558071 / 500000000) := by
  have h := checkLog_sound (w := (279 / 1721)) (n := 12)
    (lo := (327116141 / 1000000000)) (hi := (163558071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 721) = 1/(721 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9162 : Bounds (-163558071 / 500000000) (-327116141 / 1000000000) (Real.log (721 / 1000)) := by
  have h := reflection_log_9162_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9163_neg : (278961 / 1000000000) ≤ -Real.log (1000000 / 1000279) ∧
    -Real.log (1000000 / 1000279) ≤ (139481 / 500000000) := by
  have h := checkLog_sound (w := (279 / 2000279)) (n := 12)
    (lo := (278961 / 1000000000)) (hi := (139481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000279 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000279 / 1000000) = 1/(1000000 / 1000279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9163 : Bounds (278961 / 1000000000) (139481 / 500000000) (Real.log (1000279 / 1000000)) := by
  have h := reflection_log_9163_neg
  have he : Real.log (1000279 / 1000000) = -Real.log (1000000 / 1000279) := by
    rw [show ((1000279 / 1000000) : ℝ) = ((1000000 / 1000279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9164_neg : (139519 / 500000000) ≤ -Real.log (999721 / 1000000) ∧
    -Real.log (999721 / 1000000) ≤ (279039 / 1000000000) := by
  have h := checkLog_sound (w := (279 / 1999721)) (n := 12)
    (lo := (139519 / 500000000)) (hi := (279039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999721) = 1/(999721 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9164 : Bounds (-279039 / 1000000000) (-139519 / 500000000) (Real.log (999721 / 1000000)) := by
  have h := reflection_log_9164_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9165_neg : (131997967 / 1000000000) ≤ -Real.log (500000 / 570553) ∧
    -Real.log (500000 / 570553) ≤ (8249873 / 62500000) := by
  have h := checkLog_sound (w := (70553 / 1070553)) (n := 12)
    (lo := (131997967 / 1000000000)) (hi := (8249873 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((570553 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(570553 / 500000) = 1/(500000 / 570553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9165 : Bounds (131997967 / 1000000000) (8249873 / 62500000) (Real.log (570553 / 500000)) := by
  have h := reflection_log_9165_neg
  have he : Real.log (570553 / 500000) = -Real.log (500000 / 570553) := by
    rw [show ((570553 / 500000) : ℝ) = ((500000 / 570553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9166_neg : (152109763 / 1000000000) ≤ -Real.log (429447 / 500000) ∧
    -Real.log (429447 / 500000) ≤ (38027441 / 250000000) := by
  have h := checkLog_sound (w := (70553 / 929447)) (n := 12)
    (lo := (152109763 / 1000000000)) (hi := (38027441 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 429447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 429447) = 1/(429447 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9166 : Bounds (-38027441 / 250000000) (-152109763 / 1000000000) (Real.log (429447 / 500000)) := by
  have h := reflection_log_9166_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9167_neg : (16558447 / 125000000) ≤ -Real.log (500000 / 570821) ∧
    -Real.log (500000 / 570821) ≤ (132467577 / 1000000000) := by
  have h := checkLog_sound (w := (70821 / 1070821)) (n := 12)
    (lo := (16558447 / 125000000)) (hi := (132467577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((570821 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(570821 / 500000) = 1/(500000 / 570821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9167 : Bounds (16558447 / 125000000) (132467577 / 1000000000) (Real.log (570821 / 500000)) := by
  have h := reflection_log_9167_neg
  have he : Real.log (570821 / 500000) = -Real.log (500000 / 570821) := by
    rw [show ((570821 / 500000) : ℝ) = ((500000 / 570821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9168_neg : (152734017 / 1000000000) ≤ -Real.log (429179 / 500000) ∧
    -Real.log (429179 / 500000) ≤ (76367009 / 500000000) := by
  have h := checkLog_sound (w := (70821 / 929179)) (n := 12)
    (lo := (152734017 / 1000000000)) (hi := (76367009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 429179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 429179) = 1/(429179 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9168 : Bounds (-76367009 / 500000000) (-152734017 / 1000000000) (Real.log (429179 / 500000)) := by
  have h := reflection_log_9168_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9169_neg : (506661 / 25000000) ≤ -Real.log (244984385959 / 250000000000) ∧
    -Real.log (244984385959 / 250000000000) ≤ (20266441 / 1000000000) := by
  have h := checkLog_sound (w := (5015614041 / 494984385959)) (n := 12)
    (lo := (506661 / 25000000)) (hi := (20266441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244984385959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244984385959) = 1/(244984385959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9169 : Bounds (-20266441 / 1000000000) (-506661 / 25000000) (Real.log (244984385959 / 250000000000)) := by
  have h := reflection_log_9169_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9170_neg : (5027949 / 250000000) ≤ -Real.log (245022274191 / 250000000000) ∧
    -Real.log (245022274191 / 250000000000) ≤ (20111797 / 1000000000) := by
  have h := checkLog_sound (w := (4977725809 / 495022274191)) (n := 12)
    (lo := (5027949 / 250000000)) (hi := (20111797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245022274191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245022274191) = 1/(245022274191 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9170 : Bounds (-20111797 / 1000000000) (-5027949 / 250000000) (Real.log (245022274191 / 250000000000)) := by
  have h := reflection_log_9170_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9171_neg : (284107731 / 1000000000) ≤ -Real.log (500000000000 / 664288026229) ∧
    -Real.log (500000000000 / 664288026229) ≤ (71026933 / 250000000) := by
  have h := checkLog_sound (w := (164288026229 / 1164288026229)) (n := 12)
    (lo := (284107731 / 1000000000)) (hi := (71026933 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((664288026229 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(664288026229 / 500000000000) = 1/(500000000000 / 664288026229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9171 : Bounds (284107731 / 1000000000) (71026933 / 250000000) (Real.log (664288026229 / 500000000000)) := by
  have h := reflection_log_9171_neg
  have he : Real.log (664288026229 / 500000000000) = -Real.log (500000000000 / 664288026229) := by
    rw [show ((664288026229 / 500000000000) : ℝ) = ((500000000000 / 664288026229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9172_neg : (142600797 / 500000000) ≤ -Real.log (100000000000 / 133003012729) ∧
    -Real.log (100000000000 / 133003012729) ≤ (57040319 / 200000000) := by
  have h := checkLog_sound (w := (33003012729 / 233003012729)) (n := 12)
    (lo := (142600797 / 500000000)) (hi := (57040319 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133003012729 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133003012729 / 100000000000) = 1/(100000000000 / 133003012729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9172 : Bounds (142600797 / 500000000) (57040319 / 200000000) (Real.log (133003012729 / 100000000000)) := by
  have h := reflection_log_9172_neg
  have he : Real.log (133003012729 / 100000000000) = -Real.log (100000000000 / 133003012729) := by
    rw [show ((133003012729 / 100000000000) : ℝ) = ((100000000000 / 133003012729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9173_neg : (35756901 / 62500000) ≤ -Real.log (500000000000 / 886001386001) ∧
    -Real.log (500000000000 / 886001386001) ≤ (572110417 / 1000000000) := by
  have h := checkLog_sound (w := (386001386001 / 1386001386001)) (n := 12)
    (lo := (35756901 / 62500000)) (hi := (572110417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((886001386001 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(886001386001 / 500000000000) = 1/(500000000000 / 886001386001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9173 : Bounds (35756901 / 62500000) (572110417 / 1000000000) (Real.log (886001386001 / 500000000000)) := by
  have h := reflection_log_9173_neg
  have he : Real.log (886001386001 / 500000000000) = -Real.log (500000000000 / 886001386001) := by
    rw [show ((886001386001 / 500000000000) : ℝ) = ((500000000000 / 886001386001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9174_neg : (71649333 / 125000000) ≤ -Real.log (125000000000 / 221740638003) ∧
    -Real.log (125000000000 / 221740638003) ≤ (114638933 / 200000000) := by
  have h := checkLog_sound (w := (96740638003 / 346740638003)) (n := 12)
    (lo := (71649333 / 125000000)) (hi := (114638933 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((221740638003 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(221740638003 / 125000000000) = 1/(125000000000 / 221740638003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9174 : Bounds (71649333 / 125000000) (114638933 / 200000000) (Real.log (221740638003 / 125000000000)) := by
  have h := reflection_log_9174_neg
  have he : Real.log (221740638003 / 125000000000) = -Real.log (125000000000 / 221740638003) := by
    rw [show ((221740638003 / 125000000000) : ℝ) = ((125000000000 / 221740638003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9175_neg : (962771 / 3906250) ≤ -Real.log (2000 / 2559) ∧
    -Real.log (2000 / 2559) ≤ (246469377 / 1000000000) := by
  have h := checkLog_sound (w := (559 / 4559)) (n := 12)
    (lo := (962771 / 3906250)) (hi := (246469377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2559 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2559 / 2000) = 1/(2000 / 2559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9175 : Bounds (962771 / 3906250) (246469377 / 1000000000) (Real.log (2559 / 2000)) := by
  have h := reflection_log_9175_neg
  have he : Real.log (2559 / 2000) = -Real.log (2000 / 2559) := by
    rw [show ((2559 / 2000) : ℝ) = ((2000 / 2559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9176_neg : (327809863 / 1000000000) ≤ -Real.log (1441 / 2000) ∧
    -Real.log (1441 / 2000) ≤ (40976233 / 125000000) := by
  have h := checkLog_sound (w := (559 / 3441)) (n := 12)
    (lo := (327809863 / 1000000000)) (hi := (40976233 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1441) = 1/(1441 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9176 : Bounds (-40976233 / 125000000) (-327809863 / 1000000000) (Real.log (1441 / 2000)) := by
  have h := reflection_log_9176_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9177_neg : (13973 / 50000000) ≤ -Real.log (2000000 / 2000559) ∧
    -Real.log (2000000 / 2000559) ≤ (279461 / 1000000000) := by
  have h := checkLog_sound (w := (559 / 4000559)) (n := 12)
    (lo := (13973 / 50000000)) (hi := (279461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000559 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000559 / 2000000) = 1/(2000000 / 2000559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9177 : Bounds (13973 / 50000000) (279461 / 1000000000) (Real.log (2000559 / 2000000)) := by
  have h := reflection_log_9177_neg
  have he : Real.log (2000559 / 2000000) = -Real.log (2000000 / 2000559) := by
    rw [show ((2000559 / 2000000) : ℝ) = ((2000000 / 2000559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9178_neg : (279539 / 1000000000) ≤ -Real.log (1999441 / 2000000) ∧
    -Real.log (1999441 / 2000000) ≤ (13977 / 50000000) := by
  have h := checkLog_sound (w := (559 / 3999441)) (n := 12)
    (lo := (279539 / 1000000000)) (hi := (13977 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999441) = 1/(1999441 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9178 : Bounds (-13977 / 50000000) (-279539 / 1000000000) (Real.log (1999441 / 2000000)) := by
  have h := reflection_log_9178_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9179_neg : (13222579 / 100000000) ≤ -Real.log (500000 / 570683) ∧
    -Real.log (500000 / 570683) ≤ (132225791 / 1000000000) := by
  have h := checkLog_sound (w := (70683 / 1070683)) (n := 12)
    (lo := (13222579 / 100000000)) (hi := (132225791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((570683 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(570683 / 500000) = 1/(500000 / 570683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9179 : Bounds (13222579 / 100000000) (132225791 / 1000000000) (Real.log (570683 / 500000)) := by
  have h := reflection_log_9179_neg
  have he : Real.log (570683 / 500000) = -Real.log (500000 / 570683) := by
    rw [show ((570683 / 500000) : ℝ) = ((500000 / 570683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9180_neg : (38103131 / 250000000) ≤ -Real.log (429317 / 500000) ∧
    -Real.log (429317 / 500000) ≤ (6096501 / 40000000) := by
  have h := checkLog_sound (w := (70683 / 929317)) (n := 12)
    (lo := (38103131 / 250000000)) (hi := (6096501 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 429317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 429317) = 1/(429317 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9180 : Bounds (-6096501 / 40000000) (-38103131 / 250000000) (Real.log (429317 / 500000)) := by
  have h := reflection_log_9180_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9181_neg : (16587021 / 125000000) ≤ -Real.log (1000000 / 1141903) ∧
    -Real.log (1000000 / 1141903) ≤ (132696169 / 1000000000) := by
  have h := checkLog_sound (w := (141903 / 2141903)) (n := 12)
    (lo := (16587021 / 125000000)) (hi := (132696169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1141903 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1141903 / 1000000) = 1/(1000000 / 1141903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9181 : Bounds (16587021 / 125000000) (132696169 / 1000000000) (Real.log (1141903 / 1000000)) := by
  have h := reflection_log_9181_neg
  have he : Real.log (1141903 / 1000000) = -Real.log (1000000 / 1141903) := by
    rw [show ((1141903 / 1000000) : ℝ) = ((1000000 / 1141903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9182_neg : (38259533 / 250000000) ≤ -Real.log (858097 / 1000000) ∧
    -Real.log (858097 / 1000000) ≤ (153038133 / 1000000000) := by
  have h := checkLog_sound (w := (141903 / 1858097)) (n := 12)
    (lo := (38259533 / 250000000)) (hi := (153038133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 858097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 858097) = 1/(858097 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9182 : Bounds (-153038133 / 1000000000) (-38259533 / 250000000) (Real.log (858097 / 1000000)) := by
  have h := reflection_log_9182_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9183_neg : (20341963 / 1000000000) ≤ -Real.log (979863538591 / 1000000000000) ∧
    -Real.log (979863538591 / 1000000000000) ≤ (5085491 / 250000000) := by
  have h := checkLog_sound (w := (20136461409 / 1979863538591)) (n := 12)
    (lo := (20341963 / 1000000000)) (hi := (5085491 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979863538591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979863538591) = 1/(979863538591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9183 : Bounds (-5085491 / 250000000) (-20341963 / 1000000000) (Real.log (979863538591 / 1000000000000)) := by
  have h := reflection_log_9183_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9184_neg : (20186733 / 1000000000) ≤ -Real.log (245003913511 / 250000000000) ∧
    -Real.log (245003913511 / 250000000000) ≤ (10093367 / 500000000) := by
  have h := checkLog_sound (w := (4996086489 / 495003913511)) (n := 12)
    (lo := (20186733 / 1000000000)) (hi := (10093367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245003913511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245003913511) = 1/(245003913511 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9184 : Bounds (-10093367 / 500000000) (-20186733 / 1000000000) (Real.log (245003913511 / 250000000000)) := by
  have h := reflection_log_9184_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9185_neg : (56927663 / 200000000) ≤ -Real.log (50000000000 / 66464058027) ∧
    -Real.log (50000000000 / 66464058027) ≤ (71159579 / 250000000) := by
  have h := checkLog_sound (w := (16464058027 / 116464058027)) (n := 12)
    (lo := (56927663 / 200000000)) (hi := (71159579 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66464058027 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(66464058027 / 50000000000) = 1/(50000000000 / 66464058027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9185 : Bounds (56927663 / 200000000) (71159579 / 250000000) (Real.log (66464058027 / 50000000000)) := by
  have h := reflection_log_9185_neg
  have he : Real.log (66464058027 / 50000000000) = -Real.log (50000000000 / 66464058027) := by
    rw [show ((66464058027 / 50000000000) : ℝ) = ((50000000000 / 66464058027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9186_neg : (285734301 / 1000000000) ≤ -Real.log (500000000000 / 665369416279) ∧
    -Real.log (500000000000 / 665369416279) ≤ (142867151 / 500000000) := by
  have h := checkLog_sound (w := (165369416279 / 1165369416279)) (n := 12)
    (lo := (285734301 / 1000000000)) (hi := (142867151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((665369416279 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(665369416279 / 500000000000) = 1/(500000000000 / 665369416279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9186 : Bounds (285734301 / 1000000000) (142867151 / 500000000) (Real.log (665369416279 / 500000000000)) := by
  have h := reflection_log_9186_neg
  have he : Real.log (665369416279 / 500000000000) = -Real.log (500000000000 / 665369416279) := by
    rw [show ((665369416279 / 500000000000) : ℝ) = ((500000000000 / 665369416279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9187_neg : (71649333 / 125000000) ≤ -Real.log (500000000000 / 886962552011) ∧
    -Real.log (500000000000 / 886962552011) ≤ (114638933 / 200000000) := by
  have h := checkLog_sound (w := (386962552011 / 1386962552011)) (n := 12)
    (lo := (71649333 / 125000000)) (hi := (114638933 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((886962552011 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(886962552011 / 500000000000) = 1/(500000000000 / 886962552011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9187 : Bounds (71649333 / 125000000) (114638933 / 200000000) (Real.log (886962552011 / 500000000000)) := by
  have h := reflection_log_9187_neg
  have he : Real.log (886962552011 / 500000000000) = -Real.log (500000000000 / 886962552011) := by
    rw [show ((886962552011 / 500000000000) : ℝ) = ((500000000000 / 886962552011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9188_neg : (14356981 / 25000000) ≤ -Real.log (31250000000 / 55495315753) ∧
    -Real.log (31250000000 / 55495315753) ≤ (574279241 / 1000000000) := by
  have h := checkLog_sound (w := (24245315753 / 86745315753)) (n := 12)
    (lo := (14356981 / 25000000)) (hi := (574279241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55495315753 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55495315753 / 31250000000) = 1/(31250000000 / 55495315753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9188 : Bounds (14356981 / 25000000) (574279241 / 1000000000) (Real.log (55495315753 / 31250000000)) := by
  have h := reflection_log_9188_neg
  have he : Real.log (55495315753 / 31250000000) = -Real.log (31250000000 / 55495315753) := by
    rw [show ((55495315753 / 31250000000) : ℝ) = ((31250000000 / 55495315753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9189_neg : (246860077 / 1000000000) ≤ -Real.log (25 / 32) ∧
    -Real.log (25 / 32) ≤ (123430039 / 500000000) := by
  have h := checkLog_sound (w := (7 / 57)) (n := 12)
    (lo := (246860077 / 1000000000)) (hi := (123430039 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32 / 25) = 1/(25 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9189 : Bounds (246860077 / 1000000000) (123430039 / 500000000) (Real.log (32 / 25)) := by
  have h := reflection_log_9189_neg
  have he : Real.log (32 / 25) = -Real.log (25 / 32) := by
    rw [show ((32 / 25) : ℝ) = ((25 / 32) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9190_neg : (164252033 / 500000000) ≤ -Real.log (18 / 25) ∧
    -Real.log (18 / 25) ≤ (328504067 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 43)) (n := 12)
    (lo := (164252033 / 500000000)) (hi := (328504067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 18) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25 / 18) = 1/(18 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9190 : Bounds (-328504067 / 1000000000) (-164252033 / 500000000) (Real.log (18 / 25)) := by
  have h := reflection_log_9190_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9191_neg : (6999 / 25000000) ≤ -Real.log (25000 / 25007) ∧
    -Real.log (25000 / 25007) ≤ (279961 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 50007)) (n := 12)
    (lo := (6999 / 25000000)) (hi := (279961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25007 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25007 / 25000) = 1/(25000 / 25007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9191 : Bounds (6999 / 25000000) (279961 / 1000000000) (Real.log (25007 / 25000)) := by
  have h := reflection_log_9191_neg
  have he : Real.log (25007 / 25000) = -Real.log (25000 / 25007) := by
    rw [show ((25007 / 25000) : ℝ) = ((25000 / 25007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9192_neg : (280039 / 1000000000) ≤ -Real.log (24993 / 25000) ∧
    -Real.log (24993 / 25000) ≤ (7001 / 25000000) := by
  have h := checkLog_sound (w := (7 / 49993)) (n := 12)
    (lo := (280039 / 1000000000)) (hi := (7001 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 24993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 24993) = 1/(24993 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9192 : Bounds (-7001 / 25000000) (-280039 / 1000000000) (Real.log (24993 / 25000)) := by
  have h := reflection_log_9192_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9193_neg : (132454437 / 1000000000) ≤ -Real.log (1000000 / 1141627) ∧
    -Real.log (1000000 / 1141627) ≤ (66227219 / 500000000) := by
  have h := checkLog_sound (w := (141627 / 2141627)) (n := 12)
    (lo := (132454437 / 1000000000)) (hi := (66227219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1141627 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1141627 / 1000000) = 1/(1000000 / 1141627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9193 : Bounds (132454437 / 1000000000) (66227219 / 500000000) (Real.log (1141627 / 1000000)) := by
  have h := reflection_log_9193_neg
  have he : Real.log (1141627 / 1000000) = -Real.log (1000000 / 1141627) := by
    rw [show ((1141627 / 1000000) : ℝ) = ((1000000 / 1141627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9194_neg : (76358271 / 500000000) ≤ -Real.log (858373 / 1000000) ∧
    -Real.log (858373 / 1000000) ≤ (152716543 / 1000000000) := by
  have h := checkLog_sound (w := (141627 / 1858373)) (n := 12)
    (lo := (76358271 / 500000000)) (hi := (152716543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 858373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 858373) = 1/(858373 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9194 : Bounds (-152716543 / 1000000000) (-76358271 / 500000000) (Real.log (858373 / 1000000)) := by
  have h := reflection_log_9194_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9195_neg : (8307849 / 62500000) ≤ -Real.log (200000 / 228433) ∧
    -Real.log (200000 / 228433) ≤ (26585117 / 200000000) := by
  have h := checkLog_sound (w := (28433 / 428433)) (n := 12)
    (lo := (8307849 / 62500000)) (hi := (26585117 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((228433 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(228433 / 200000) = 1/(200000 / 228433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9195 : Bounds (8307849 / 62500000) (26585117 / 200000000) (Real.log (228433 / 200000)) := by
  have h := reflection_log_9195_neg
  have he : Real.log (228433 / 200000) = -Real.log (200000 / 228433) := by
    rw [show ((228433 / 200000) : ℝ) = ((200000 / 228433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9196_neg : (30668701 / 200000000) ≤ -Real.log (171567 / 200000) ∧
    -Real.log (171567 / 200000) ≤ (76671753 / 500000000) := by
  have h := checkLog_sound (w := (28433 / 371567)) (n := 12)
    (lo := (30668701 / 200000000)) (hi := (76671753 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 171567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 171567) = 1/(171567 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9196 : Bounds (-76671753 / 500000000) (-30668701 / 200000000) (Real.log (171567 / 200000)) := by
  have h := reflection_log_9196_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9197_neg : (20417921 / 1000000000) ≤ -Real.log (39191564511 / 40000000000) ∧
    -Real.log (39191564511 / 40000000000) ≤ (10208961 / 500000000) := by
  have h := checkLog_sound (w := (808435489 / 79191564511)) (n := 12)
    (lo := (20417921 / 1000000000)) (hi := (10208961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39191564511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39191564511) = 1/(39191564511 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9197 : Bounds (-10208961 / 500000000) (-20417921 / 1000000000) (Real.log (39191564511 / 40000000000)) := by
  have h := reflection_log_9197_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9198_neg : (2532763 / 125000000) ≤ -Real.log (979941792871 / 1000000000000) ∧
    -Real.log (979941792871 / 1000000000000) ≤ (4052421 / 200000000) := by
  have h := checkLog_sound (w := (20058207129 / 1979941792871)) (n := 12)
    (lo := (2532763 / 125000000)) (hi := (4052421 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979941792871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979941792871) = 1/(979941792871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9198 : Bounds (-4052421 / 200000000) (-2532763 / 125000000) (Real.log (979941792871 / 1000000000000)) := by
  have h := reflection_log_9198_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9199_neg : (285170979 / 1000000000) ≤ -Real.log (500000000000 / 664994705099) ∧
    -Real.log (500000000000 / 664994705099) ≤ (14258549 / 50000000) := by
  have h := checkLog_sound (w := (164994705099 / 1164994705099)) (n := 12)
    (lo := (285170979 / 1000000000)) (hi := (14258549 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((664994705099 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(664994705099 / 500000000000) = 1/(500000000000 / 664994705099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9199 : Bounds (285170979 / 1000000000) (14258549 / 50000000) (Real.log (664994705099 / 500000000000)) := by
  have h := reflection_log_9199_neg
  have he : Real.log (664994705099 / 500000000000) = -Real.log (500000000000 / 664994705099) := by
    rw [show ((664994705099 / 500000000000) : ℝ) = ((500000000000 / 664994705099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9200_neg : (286269089 / 1000000000) ≤ -Real.log (125000000000 / 166431335863) ∧
    -Real.log (125000000000 / 166431335863) ≤ (28626909 / 100000000) := by
  have h := checkLog_sound (w := (41431335863 / 291431335863)) (n := 12)
    (lo := (286269089 / 1000000000)) (hi := (28626909 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166431335863 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(166431335863 / 125000000000) = 1/(125000000000 / 166431335863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9200 : Bounds (286269089 / 1000000000) (28626909 / 100000000) (Real.log (166431335863 / 125000000000)) := by
  have h := reflection_log_9200_neg
  have he : Real.log (166431335863 / 125000000000) = -Real.log (125000000000 / 166431335863) := by
    rw [show ((166431335863 / 125000000000) : ℝ) = ((125000000000 / 166431335863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9201_neg : (14356981 / 25000000) ≤ -Real.log (500000000000 / 887925052047) ∧
    -Real.log (500000000000 / 887925052047) ≤ (574279241 / 1000000000) := by
  have h := checkLog_sound (w := (387925052047 / 1387925052047)) (n := 12)
    (lo := (14356981 / 25000000)) (hi := (574279241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((887925052047 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(887925052047 / 500000000000) = 1/(500000000000 / 887925052047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9201 : Bounds (14356981 / 25000000) (574279241 / 1000000000) (Real.log (887925052047 / 500000000000)) := by
  have h := reflection_log_9201_neg
  have he : Real.log (887925052047 / 500000000000) = -Real.log (500000000000 / 887925052047) := by
    rw [show ((887925052047 / 500000000000) : ℝ) = ((500000000000 / 887925052047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9202_neg : (35960259 / 62500000) ≤ -Real.log (500000000000 / 888888888889) ∧
    -Real.log (500000000000 / 888888888889) ≤ (115072829 / 200000000) := by
  have h := checkLog_sound (w := (388888888889 / 1388888888889)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((888888888889 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(888888888889 / 500000000000) = 1/(500000000000 / 888888888889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9202 : Bounds (35960259 / 62500000) (115072829 / 200000000) (Real.log (888888888889 / 500000000000)) := by
  have h := reflection_log_9202_neg
  have he : Real.log (888888888889 / 500000000000) = -Real.log (500000000000 / 888888888889) := by
    rw [show ((888888888889 / 500000000000) : ℝ) = ((500000000000 / 888888888889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9203_neg : (123625313 / 500000000) ≤ -Real.log (2000 / 2561) ∧
    -Real.log (2000 / 2561) ≤ (247250627 / 1000000000) := by
  have h := checkLog_sound (w := (561 / 4561)) (n := 12)
    (lo := (123625313 / 500000000)) (hi := (247250627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2561 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2561 / 2000) = 1/(2000 / 2561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9203 : Bounds (123625313 / 500000000) (247250627 / 1000000000) (Real.log (2561 / 2000)) := by
  have h := reflection_log_9203_neg
  have he : Real.log (2561 / 2000) = -Real.log (2000 / 2561) := by
    rw [show ((2561 / 2000) : ℝ) = ((2000 / 2561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9204_neg : (10287461 / 31250000) ≤ -Real.log (1439 / 2000) ∧
    -Real.log (1439 / 2000) ≤ (329198753 / 1000000000) := by
  have h := checkLog_sound (w := (561 / 3439)) (n := 12)
    (lo := (10287461 / 31250000)) (hi := (329198753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1439) = 1/(1439 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9204 : Bounds (-329198753 / 1000000000) (-10287461 / 31250000) (Real.log (1439 / 2000)) := by
  have h := reflection_log_9204_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9205_neg : (14023 / 50000000) ≤ -Real.log (2000000 / 2000561) ∧
    -Real.log (2000000 / 2000561) ≤ (280461 / 1000000000) := by
  have h := checkLog_sound (w := (561 / 4000561)) (n := 12)
    (lo := (14023 / 50000000)) (hi := (280461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000561 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000561 / 2000000) = 1/(2000000 / 2000561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9205 : Bounds (14023 / 50000000) (280461 / 1000000000) (Real.log (2000561 / 2000000)) := by
  have h := reflection_log_9205_neg
  have he : Real.log (2000561 / 2000000) = -Real.log (2000000 / 2000561) := by
    rw [show ((2000561 / 2000000) : ℝ) = ((2000000 / 2000561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9206_neg : (280539 / 1000000000) ≤ -Real.log (1999439 / 2000000) ∧
    -Real.log (1999439 / 2000000) ≤ (14027 / 50000000) := by
  have h := checkLog_sound (w := (561 / 3999439)) (n := 12)
    (lo := (280539 / 1000000000)) (hi := (14027 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999439) = 1/(1999439 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9206 : Bounds (-14027 / 50000000) (-280539 / 1000000000) (Real.log (1999439 / 2000000)) := by
  have h := reflection_log_9206_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9207_neg : (16585379 / 125000000) ≤ -Real.log (15625 / 17842) ∧
    -Real.log (15625 / 17842) ≤ (132683033 / 1000000000) := by
  have h := checkLog_sound (w := (2217 / 33467)) (n := 12)
    (lo := (16585379 / 125000000)) (hi := (132683033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17842 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17842 / 15625) = 1/(15625 / 17842) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9207 : Bounds (16585379 / 125000000) (132683033 / 1000000000) (Real.log (17842 / 15625)) := by
  have h := reflection_log_9207_neg
  have he : Real.log (17842 / 15625) = -Real.log (15625 / 17842) := by
    rw [show ((17842 / 15625) : ℝ) = ((15625 / 17842) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9208_neg : (153020651 / 1000000000) ≤ -Real.log (13408 / 15625) ∧
    -Real.log (13408 / 15625) ≤ (38255163 / 250000000) := by
  have h := checkLog_sound (w := (2217 / 29033)) (n := 12)
    (lo := (153020651 / 1000000000)) (hi := (38255163 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13408) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 13408) = 1/(13408 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9208 : Bounds (-38255163 / 250000000) (-153020651 / 1000000000) (Real.log (13408 / 15625)) := by
  have h := reflection_log_9208_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9209_neg : (133154071 / 1000000000) ≤ -Real.log (500000 / 571213) ∧
    -Real.log (500000 / 571213) ≤ (16644259 / 125000000) := by
  have h := checkLog_sound (w := (71213 / 1071213)) (n := 12)
    (lo := (133154071 / 1000000000)) (hi := (16644259 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((571213 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(571213 / 500000) = 1/(500000 / 571213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9209 : Bounds (133154071 / 1000000000) (16644259 / 125000000) (Real.log (571213 / 500000)) := by
  have h := reflection_log_9209_neg
  have he : Real.log (571213 / 500000) = -Real.log (500000 / 571213) := by
    rw [show ((571213 / 500000) : ℝ) = ((500000 / 571213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9210_neg : (76823903 / 500000000) ≤ -Real.log (428787 / 500000) ∧
    -Real.log (428787 / 500000) ≤ (153647807 / 1000000000) := by
  have h := checkLog_sound (w := (71213 / 928787)) (n := 12)
    (lo := (76823903 / 500000000)) (hi := (153647807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 428787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 428787) = 1/(428787 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9210 : Bounds (-153647807 / 1000000000) (-76823903 / 500000000) (Real.log (428787 / 500000)) := by
  have h := reflection_log_9210_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9211_neg : (10246867 / 500000000) ≤ -Real.log (244928708631 / 250000000000) ∧
    -Real.log (244928708631 / 250000000000) ≤ (4098747 / 200000000) := by
  have h := checkLog_sound (w := (5071291369 / 494928708631)) (n := 12)
    (lo := (10246867 / 500000000)) (hi := (4098747 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244928708631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244928708631) = 1/(244928708631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9211 : Bounds (-4098747 / 200000000) (-10246867 / 500000000) (Real.log (244928708631 / 250000000000)) := by
  have h := reflection_log_9211_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9212_neg : (20337619 / 1000000000) ≤ -Real.log (239225536 / 244140625) ∧
    -Real.log (239225536 / 244140625) ≤ (1016881 / 50000000) := by
  have h := checkLog_sound (w := (4915089 / 483366161)) (n := 12)
    (lo := (20337619 / 1000000000)) (hi := (1016881 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 239225536) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 239225536) = 1/(239225536 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9212 : Bounds (-1016881 / 50000000) (-20337619 / 1000000000) (Real.log (239225536 / 244140625)) := by
  have h := reflection_log_9212_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9213_neg : (71425921 / 250000000) ≤ -Real.log (250000000000 / 332674522673) ∧
    -Real.log (250000000000 / 332674522673) ≤ (57140737 / 200000000) := by
  have h := checkLog_sound (w := (82674522673 / 582674522673)) (n := 12)
    (lo := (71425921 / 250000000)) (hi := (57140737 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((332674522673 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(332674522673 / 250000000000) = 1/(250000000000 / 332674522673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9213 : Bounds (71425921 / 250000000) (57140737 / 200000000) (Real.log (332674522673 / 250000000000)) := by
  have h := reflection_log_9213_neg
  have he : Real.log (332674522673 / 250000000000) = -Real.log (250000000000 / 332674522673) := by
    rw [show ((332674522673 / 250000000000) : ℝ) = ((250000000000 / 332674522673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9214_neg : (286801877 / 1000000000) ≤ -Real.log (500000000000 / 666080128363) ∧
    -Real.log (500000000000 / 666080128363) ≤ (143400939 / 500000000) := by
  have h := checkLog_sound (w := (166080128363 / 1166080128363)) (n := 12)
    (lo := (286801877 / 1000000000)) (hi := (143400939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((666080128363 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(666080128363 / 500000000000) = 1/(500000000000 / 666080128363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9214 : Bounds (286801877 / 1000000000) (143400939 / 500000000) (Real.log (666080128363 / 500000000000)) := by
  have h := reflection_log_9214_neg
  have he : Real.log (666080128363 / 500000000000) = -Real.log (500000000000 / 666080128363) := by
    rw [show ((666080128363 / 500000000000) : ℝ) = ((500000000000 / 666080128363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9215_neg : (35960259 / 62500000) ≤ -Real.log (62500000000 / 111111111111) ∧
    -Real.log (62500000000 / 111111111111) ≤ (115072829 / 200000000) := by
  have h := checkLog_sound (w := (48611111111 / 173611111111)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111111111111 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111111111111 / 62500000000) = 1/(62500000000 / 111111111111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9215 : Bounds (35960259 / 62500000) (115072829 / 200000000) (Real.log (111111111111 / 62500000000)) := by
  have h := reflection_log_9215_neg
  have he : Real.log (111111111111 / 62500000000) = -Real.log (62500000000 / 111111111111) := by
    rw [show ((111111111111 / 62500000000) : ℝ) = ((62500000000 / 111111111111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


