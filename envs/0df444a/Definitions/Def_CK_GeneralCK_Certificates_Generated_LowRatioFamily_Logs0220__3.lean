-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0220__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0220__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:19:48.803953+00:00
-- url     : https://prove2.me/theorems/66d86f2e-ccf6-4505-abf4-d4ae0c88ab3d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0220 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0221, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0220 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0221, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0222)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0220 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0221, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0222)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0220 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0221, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0222) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0220 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0221, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0222).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0220 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14080_neg : (97943621 / 250000000) ≤ -Real.log (250000 / 369901) ∧
    -Real.log (250000 / 369901) ≤ (78354897 / 200000000) := by
  have h := checkLog_sound (w := (119901 / 619901)) (n := 12)
    (lo := (97943621 / 250000000)) (hi := (78354897 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369901 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369901 / 250000) = 1/(250000 / 369901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14080 : Bounds (97943621 / 250000000) (78354897 / 200000000) (Real.log (369901 / 250000)) := by
  have h := reflection_log_14080_neg
  have he : Real.log (369901 / 250000) = -Real.log (250000 / 369901) := by
    rw [show ((369901 / 250000) : ℝ) = ((250000 / 369901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14081_neg : (326582609 / 500000000) ≤ -Real.log (130099 / 250000) ∧
    -Real.log (130099 / 250000) ≤ (653165219 / 1000000000) := by
  have h := checkLog_sound (w := (119901 / 380099)) (n := 12)
    (lo := (326582609 / 500000000)) (hi := (653165219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 130099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 130099) = 1/(130099 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14081 : Bounds (-653165219 / 1000000000) (-326582609 / 500000000) (Real.log (130099 / 250000)) := by
  have h := reflection_log_14081_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14082_neg : (393854633 / 1000000000) ≤ -Real.log (200000 / 296537) ∧
    -Real.log (200000 / 296537) ≤ (196927317 / 500000000) := by
  have h := checkLog_sound (w := (96537 / 496537)) (n := 12)
    (lo := (393854633 / 1000000000)) (hi := (196927317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296537 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296537 / 200000) = 1/(200000 / 296537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14082 : Bounds (393854633 / 1000000000) (196927317 / 500000000) (Real.log (296537 / 200000)) := by
  have h := reflection_log_14082_neg
  have he : Real.log (296537 / 200000) = -Real.log (200000 / 296537) := by
    rw [show ((296537 / 200000) : ℝ) = ((200000 / 296537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14083_neg : (131820661 / 200000000) ≤ -Real.log (103463 / 200000) ∧
    -Real.log (103463 / 200000) ≤ (329551653 / 500000000) := by
  have h := checkLog_sound (w := (96537 / 303463)) (n := 12)
    (lo := (131820661 / 200000000)) (hi := (329551653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 103463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 103463) = 1/(103463 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14083 : Bounds (-329551653 / 500000000) (-131820661 / 200000000) (Real.log (103463 / 200000)) := by
  have h := reflection_log_14083_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14084_neg : (8289021 / 31250000) ≤ -Real.log (30680607631 / 40000000000) ∧
    -Real.log (30680607631 / 40000000000) ≤ (265248673 / 1000000000) := by
  have h := checkLog_sound (w := (9319392369 / 70680607631)) (n := 12)
    (lo := (8289021 / 31250000)) (hi := (265248673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 30680607631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 30680607631) = 1/(30680607631 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14084 : Bounds (-265248673 / 1000000000) (-8289021 / 31250000) (Real.log (30680607631 / 40000000000)) := by
  have h := reflection_log_14084_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14085_neg : (130695367 / 500000000) ≤ -Real.log (48123750199 / 62500000000) ∧
    -Real.log (48123750199 / 62500000000) ≤ (52278147 / 200000000) := by
  have h := checkLog_sound (w := (14376249801 / 110623750199)) (n := 12)
    (lo := (130695367 / 500000000)) (hi := (52278147 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 48123750199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 48123750199) = 1/(48123750199 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14085 : Bounds (-52278147 / 200000000) (-130695367 / 500000000) (Real.log (48123750199 / 62500000000)) := by
  have h := reflection_log_14085_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14086_neg : (522469851 / 500000000) ≤ -Real.log (500000000000 / 1421613540457) ∧
    -Real.log (500000000000 / 1421613540457) ≤ (130617463 / 125000000) := by
  have h := checkLog_sound (w := (421613540457 / 2421613540457)) (n := 12)
    (lo := (175896261 / 500000000)) (hi := (351792523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1421613540457 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1421613540457 / 1000000000000) = 1/(500000000000 / 1421613540457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14086 : Bounds (522469851 / 500000000) (130617463 / 125000000) (Real.log (1421613540457 / 500000000000)) := by
  have h := reflection_log_14086_neg
  have he : Real.log (1421613540457 / 500000000000) = -Real.log (500000000000 / 1421613540457) := by
    rw [show ((1421613540457 / 500000000000) : ℝ) = ((500000000000 / 1421613540457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14087_neg : (526478969 / 500000000) ≤ -Real.log (500000000000 / 1433058194717) ∧
    -Real.log (500000000000 / 1433058194717) ≤ (52647897 / 50000000) := by
  have h := checkLog_sound (w := (433058194717 / 2433058194717)) (n := 12)
    (lo := (179905379 / 500000000)) (hi := (359810759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1433058194717 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1433058194717 / 1000000000000) = 1/(500000000000 / 1433058194717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14087 : Bounds (526478969 / 500000000) (52647897 / 50000000) (Real.log (1433058194717 / 500000000000)) := by
  have h := reflection_log_14087_neg
  have he : Real.log (1433058194717 / 500000000000) = -Real.log (500000000000 / 1433058194717) := by
    rw [show ((1433058194717 / 500000000000) : ℝ) = ((500000000000 / 1433058194717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14088_neg : (29464237 / 12500000) ≤ -Real.log (500000000000 / 5280346820809) ∧
    -Real.log (500000000000 / 5280346820809) ≤ (589284741 / 250000000) := by
  have h := checkLog_sound (w := (1280346820809 / 9280346820809)) (n := 12)
    (lo := (13884871 / 50000000)) (hi := (277697421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5280346820809 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5280346820809 / 4000000000000) = 1/(500000000000 / 5280346820809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14088 : Bounds (29464237 / 12500000) (589284741 / 250000000) (Real.log (5280346820809 / 500000000000)) := by
  have h := reflection_log_14088_neg
  have he : Real.log (5280346820809 / 500000000000) = -Real.log (500000000000 / 5280346820809) := by
    rw [show ((5280346820809 / 500000000000) : ℝ) = ((500000000000 / 5280346820809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14089_neg : (2376272807 / 1000000000) ≤ -Real.log (500000000000 / 5382352941177) ∧
    -Real.log (500000000000 / 5382352941177) ≤ (2376272811 / 1000000000) := by
  have h := checkLog_sound (w := (1382352941177 / 9382352941177)) (n := 12)
    (lo := (296831267 / 1000000000)) (hi := (74207817 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5382352941177 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5382352941177 / 4000000000000) = 1/(500000000000 / 5382352941177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14089 : Bounds (2376272807 / 1000000000) (2376272811 / 1000000000) (Real.log (5382352941177 / 500000000000)) := by
  have h := reflection_log_14089_neg
  have he : Real.log (5382352941177 / 500000000000) = -Real.log (500000000000 / 5382352941177) := by
    rw [show ((5382352941177 / 500000000000) : ℝ) = ((500000000000 / 5382352941177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14090_neg : (37872123 / 62500000) ≤ -Real.log (1000 / 1833) ∧
    -Real.log (1000 / 1833) ≤ (605953969 / 1000000000) := by
  have h := checkLog_sound (w := (833 / 2833)) (n := 12)
    (lo := (37872123 / 62500000)) (hi := (605953969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1833 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1833 / 1000) = 1/(1000 / 1833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14090 : Bounds (37872123 / 62500000) (605953969 / 1000000000) (Real.log (1833 / 1000)) := by
  have h := reflection_log_14090_neg
  have he : Real.log (1833 / 1000) = -Real.log (1000 / 1833) := by
    rw [show ((1833 / 1000) : ℝ) = ((1000 / 1833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14091_neg : (357952293 / 200000000) ≤ -Real.log (167 / 1000) ∧
    -Real.log (167 / 1000) ≤ (447440367 / 250000000) := by
  have h := checkLog_sound (w := (83 / 417)) (n := 12)
    (lo := (80693421 / 200000000)) (hi := (201733553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 167) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 167) = 1/(167 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14091 : Bounds (-447440367 / 250000000) (-357952293 / 200000000) (Real.log (167 / 1000)) := by
  have h := reflection_log_14091_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14092_neg : (832653 / 1000000000) ≤ -Real.log (1000000 / 1000833) ∧
    -Real.log (1000000 / 1000833) ≤ (416327 / 500000000) := by
  have h := checkLog_sound (w := (833 / 2000833)) (n := 12)
    (lo := (832653 / 1000000000)) (hi := (416327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000833 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000833 / 1000000) = 1/(1000000 / 1000833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14092 : Bounds (832653 / 1000000000) (416327 / 500000000) (Real.log (1000833 / 1000000)) := by
  have h := reflection_log_14092_neg
  have he : Real.log (1000833 / 1000000) = -Real.log (1000000 / 1000833) := by
    rw [show ((1000833 / 1000000) : ℝ) = ((1000000 / 1000833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14093_neg : (833347 / 1000000000) ≤ -Real.log (999167 / 1000000) ∧
    -Real.log (999167 / 1000000) ≤ (208337 / 250000000) := by
  have h := checkLog_sound (w := (833 / 1999167)) (n := 12)
    (lo := (833347 / 1000000000)) (hi := (208337 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999167) = 1/(999167 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14093 : Bounds (-208337 / 250000000) (-833347 / 1000000000) (Real.log (999167 / 1000000)) := by
  have h := reflection_log_14093_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14094_neg : (49175331 / 125000000) ≤ -Real.log (200000 / 296403) ∧
    -Real.log (200000 / 296403) ≤ (393402649 / 1000000000) := by
  have h := checkLog_sound (w := (96403 / 496403)) (n := 12)
    (lo := (49175331 / 125000000)) (hi := (393402649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296403 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296403 / 200000) = 1/(200000 / 296403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14094 : Bounds (49175331 / 125000000) (393402649 / 1000000000) (Real.log (296403 / 200000)) := by
  have h := reflection_log_14094_neg
  have he : Real.log (296403 / 200000) = -Real.log (200000 / 296403) := by
    rw [show ((296403 / 200000) : ℝ) = ((200000 / 296403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14095_neg : (328904497 / 500000000) ≤ -Real.log (103597 / 200000) ∧
    -Real.log (103597 / 200000) ≤ (131561799 / 200000000) := by
  have h := checkLog_sound (w := (96403 / 303597)) (n := 12)
    (lo := (328904497 / 500000000)) (hi := (131561799 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 103597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 103597) = 1/(103597 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14095 : Bounds (-131561799 / 200000000) (-328904497 / 500000000) (Real.log (103597 / 200000)) := by
  have h := reflection_log_14095_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14096_neg : (39548817 / 100000000) ≤ -Real.log (1000000 / 1485109) ∧
    -Real.log (1000000 / 1485109) ≤ (395488171 / 1000000000) := by
  have h := checkLog_sound (w := (485109 / 2485109)) (n := 12)
    (lo := (39548817 / 100000000)) (hi := (395488171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1485109 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1485109 / 1000000) = 1/(1000000 / 1485109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14096 : Bounds (39548817 / 100000000) (395488171 / 1000000000) (Real.log (1485109 / 1000000)) := by
  have h := reflection_log_14096_neg
  have he : Real.log (1485109 / 1000000) = -Real.log (1000000 / 1485109) := by
    rw [show ((1485109 / 1000000) : ℝ) = ((1000000 / 1485109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14097_neg : (663800051 / 1000000000) ≤ -Real.log (514891 / 1000000) ∧
    -Real.log (514891 / 1000000) ≤ (165950013 / 250000000) := by
  have h := checkLog_sound (w := (485109 / 1514891)) (n := 12)
    (lo := (663800051 / 1000000000)) (hi := (165950013 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 514891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 514891) = 1/(514891 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14097 : Bounds (-165950013 / 250000000) (-663800051 / 1000000000) (Real.log (514891 / 1000000)) := by
  have h := reflection_log_14097_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14098_neg : (6707797 / 25000000) ≤ -Real.log (764669258119 / 1000000000000) ∧
    -Real.log (764669258119 / 1000000000000) ≤ (268311881 / 1000000000) := by
  have h := checkLog_sound (w := (235330741881 / 1764669258119)) (n := 12)
    (lo := (6707797 / 25000000)) (hi := (268311881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 764669258119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 764669258119) = 1/(764669258119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14098 : Bounds (-268311881 / 1000000000) (-6707797 / 25000000) (Real.log (764669258119 / 1000000000000)) := by
  have h := reflection_log_14098_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14099_neg : (132203173 / 500000000) ≤ -Real.log (30706461591 / 40000000000) ∧
    -Real.log (30706461591 / 40000000000) ≤ (264406347 / 1000000000) := by
  have h := checkLog_sound (w := (9293538409 / 70706461591)) (n := 12)
    (lo := (132203173 / 500000000)) (hi := (264406347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 30706461591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 30706461591) = 1/(30706461591 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14099 : Bounds (-264406347 / 1000000000) (-132203173 / 500000000) (Real.log (30706461591 / 40000000000)) := by
  have h := reflection_log_14099_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14100_neg : (525605821 / 500000000) ≤ -Real.log (250000000000 / 715278917343) ∧
    -Real.log (250000000000 / 715278917343) ≤ (262802911 / 250000000) := by
  have h := checkLog_sound (w := (215278917343 / 1215278917343)) (n := 12)
    (lo := (179032231 / 500000000)) (hi := (358064463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((715278917343 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(715278917343 / 500000000000) = 1/(250000000000 / 715278917343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14100 : Bounds (525605821 / 500000000) (262802911 / 250000000) (Real.log (715278917343 / 250000000000)) := by
  have h := reflection_log_14100_neg
  have he : Real.log (715278917343 / 250000000000) = -Real.log (250000000000 / 715278917343) := by
    rw [show ((715278917343 / 250000000000) : ℝ) = ((250000000000 / 715278917343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14101_neg : (52964411 / 50000000) ≤ -Real.log (500000000000 / 1442158631633) ∧
    -Real.log (500000000000 / 1442158631633) ≤ (529644111 / 500000000) := by
  have h := checkLog_sound (w := (442158631633 / 2442158631633)) (n := 12)
    (lo := (4576763 / 12500000)) (hi := (366141041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1442158631633 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1442158631633 / 1000000000000) = 1/(500000000000 / 1442158631633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14101 : Bounds (52964411 / 50000000) (529644111 / 500000000) (Real.log (1442158631633 / 500000000000)) := by
  have h := reflection_log_14101_neg
  have he : Real.log (1442158631633 / 500000000000) = -Real.log (500000000000 / 1442158631633) := by
    rw [show ((1442158631633 / 500000000000) : ℝ) = ((500000000000 / 1442158631633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14102_neg : (2376272807 / 1000000000) ≤ -Real.log (62500000000 / 672794117647) ∧
    -Real.log (62500000000 / 672794117647) ≤ (2376272811 / 1000000000) := by
  have h := checkLog_sound (w := (172794117647 / 1172794117647)) (n := 12)
    (lo := (296831267 / 1000000000)) (hi := (74207817 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((672794117647 / 500000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(672794117647 / 500000000000) = 1/(62500000000 / 672794117647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14102 : Bounds (2376272807 / 1000000000) (2376272811 / 1000000000) (Real.log (672794117647 / 62500000000)) := by
  have h := reflection_log_14102_neg
  have he : Real.log (672794117647 / 62500000000) = -Real.log (62500000000 / 672794117647) := by
    rw [show ((672794117647 / 62500000000) : ℝ) = ((62500000000 / 672794117647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14103_neg : (2395715433 / 1000000000) ≤ -Real.log (15625000000 / 171500748503) ∧
    -Real.log (15625000000 / 171500748503) ≤ (2395715437 / 1000000000) := by
  have h := checkLog_sound (w := (46500748503 / 296500748503)) (n := 12)
    (lo := (316273893 / 1000000000)) (hi := (158136947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171500748503 / 125000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(171500748503 / 125000000000) = 1/(15625000000 / 171500748503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14103 : Bounds (2395715433 / 1000000000) (2395715437 / 1000000000) (Real.log (171500748503 / 15625000000)) := by
  have h := reflection_log_14103_neg
  have he : Real.log (171500748503 / 15625000000) = -Real.log (15625000000 / 171500748503) := by
    rw [show ((171500748503 / 15625000000) : ℝ) = ((15625000000 / 171500748503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14104_neg : (151897323 / 250000000) ≤ -Real.log (250 / 459) ∧
    -Real.log (250 / 459) ≤ (607589293 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 709)) (n := 12)
    (lo := (151897323 / 250000000)) (hi := (607589293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((459 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(459 / 250) = 1/(250 / 459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14104 : Bounds (151897323 / 250000000) (607589293 / 1000000000) (Real.log (459 / 250)) := by
  have h := reflection_log_14104_neg
  have he : Real.log (459 / 250) = -Real.log (250 / 459) := by
    rw [show ((459 / 250) : ℝ) = ((250 / 459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14105_neg : (36157777 / 20000000) ≤ -Real.log (41 / 250) ∧
    -Real.log (41 / 250) ≤ (1807888853 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 207)) (n := 12)
    (lo := (42159449 / 100000000)) (hi := (421594491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 82) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 82) = 1/(41 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14105 : Bounds (-1807888853 / 1000000000) (-36157777 / 20000000) (Real.log (41 / 250)) := by
  have h := reflection_log_14105_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14106_neg : (16713 / 20000000) ≤ -Real.log (250000 / 250209) ∧
    -Real.log (250000 / 250209) ≤ (835651 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 500209)) (n := 12)
    (lo := (16713 / 20000000)) (hi := (835651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250209 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250209 / 250000) = 1/(250000 / 250209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14106 : Bounds (16713 / 20000000) (835651 / 1000000000) (Real.log (250209 / 250000)) := by
  have h := reflection_log_14106_neg
  have he : Real.log (250209 / 250000) = -Real.log (250000 / 250209) := by
    rw [show ((250209 / 250000) : ℝ) = ((250000 / 250209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14107_neg : (836349 / 1000000000) ≤ -Real.log (249791 / 250000) ∧
    -Real.log (249791 / 250000) ≤ (16727 / 20000000) := by
  have h := checkLog_sound (w := (209 / 499791)) (n := 12)
    (lo := (836349 / 1000000000)) (hi := (16727 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249791) = 1/(249791 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14107 : Bounds (-16727 / 20000000) (-836349 / 1000000000) (Real.log (249791 / 250000)) := by
  have h := reflection_log_14107_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14108_neg : (395036923 / 1000000000) ≤ -Real.log (1000000 / 1484439) ∧
    -Real.log (1000000 / 1484439) ≤ (98759231 / 250000000) := by
  have h := checkLog_sound (w := (484439 / 2484439)) (n := 12)
    (lo := (395036923 / 1000000000)) (hi := (98759231 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1484439 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1484439 / 1000000) = 1/(1000000 / 1484439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14108 : Bounds (395036923 / 1000000000) (98759231 / 250000000) (Real.log (1484439 / 1000000)) := by
  have h := reflection_log_14108_neg
  have he : Real.log (1484439 / 1000000) = -Real.log (1000000 / 1484439) := by
    rw [show ((1484439 / 1000000) : ℝ) = ((1000000 / 1484439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14109_neg : (13249993 / 20000000) ≤ -Real.log (515561 / 1000000) ∧
    -Real.log (515561 / 1000000) ≤ (662499651 / 1000000000) := by
  have h := checkLog_sound (w := (484439 / 1515561)) (n := 12)
    (lo := (13249993 / 20000000)) (hi := (662499651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 515561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 515561) = 1/(515561 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14109 : Bounds (-662499651 / 1000000000) (-13249993 / 20000000) (Real.log (515561 / 1000000)) := by
  have h := reflection_log_14109_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14110_neg : (198563891 / 500000000) ≤ -Real.log (500000 / 743773) ∧
    -Real.log (500000 / 743773) ≤ (397127783 / 1000000000) := by
  have h := checkLog_sound (w := (243773 / 1243773)) (n := 12)
    (lo := (198563891 / 500000000)) (hi := (397127783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743773 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743773 / 500000) = 1/(500000 / 743773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14110 : Bounds (198563891 / 500000000) (397127783 / 1000000000) (Real.log (743773 / 500000)) := by
  have h := reflection_log_14110_neg
  have he : Real.log (743773 / 500000) = -Real.log (500000 / 743773) := by
    rw [show ((743773 / 500000) : ℝ) = ((500000 / 743773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14111_neg : (83568041 / 125000000) ≤ -Real.log (256227 / 500000) ∧
    -Real.log (256227 / 500000) ≤ (668544329 / 1000000000) := by
  have h := checkLog_sound (w := (243773 / 756227)) (n := 12)
    (lo := (83568041 / 125000000)) (hi := (668544329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 256227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 256227) = 1/(256227 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14111 : Bounds (-668544329 / 1000000000) (-83568041 / 125000000) (Real.log (256227 / 500000)) := by
  have h := reflection_log_14111_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14112_neg : (54283309 / 200000000) ≤ -Real.log (190574724471 / 250000000000) ∧
    -Real.log (190574724471 / 250000000000) ≤ (135708273 / 500000000) := by
  have h := checkLog_sound (w := (59425275529 / 440574724471)) (n := 12)
    (lo := (54283309 / 200000000)) (hi := (135708273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 190574724471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 190574724471) = 1/(190574724471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14112 : Bounds (-135708273 / 500000000) (-54283309 / 200000000) (Real.log (190574724471 / 250000000000)) := by
  have h := reflection_log_14112_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14113_neg : (267462727 / 1000000000) ≤ -Real.log (765318855279 / 1000000000000) ∧
    -Real.log (765318855279 / 1000000000000) ≤ (33432841 / 125000000) := by
  have h := checkLog_sound (w := (234681144721 / 1765318855279)) (n := 12)
    (lo := (267462727 / 1000000000)) (hi := (33432841 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 765318855279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 765318855279) = 1/(765318855279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14113 : Bounds (-33432841 / 125000000) (-267462727 / 1000000000) (Real.log (765318855279 / 1000000000000)) := by
  have h := reflection_log_14113_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14114_neg : (1057536573 / 1000000000) ≤ -Real.log (250000000000 / 719817344601) ∧
    -Real.log (250000000000 / 719817344601) ≤ (42301463 / 40000000) := by
  have h := checkLog_sound (w := (219817344601 / 1219817344601)) (n := 12)
    (lo := (364389393 / 1000000000)) (hi := (182194697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719817344601 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(719817344601 / 500000000000) = 1/(250000000000 / 719817344601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14114 : Bounds (1057536573 / 1000000000) (42301463 / 40000000) (Real.log (719817344601 / 250000000000)) := by
  have h := reflection_log_14114_neg
  have he : Real.log (719817344601 / 250000000000) = -Real.log (250000000000 / 719817344601) := by
    rw [show ((719817344601 / 250000000000) : ℝ) = ((250000000000 / 719817344601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14115_neg : (1065672109 / 1000000000) ≤ -Real.log (100000000000 / 290278932353) ∧
    -Real.log (100000000000 / 290278932353) ≤ (1065672111 / 1000000000) := by
  have h := checkLog_sound (w := (90278932353 / 490278932353)) (n := 12)
    (lo := (372524929 / 1000000000)) (hi := (37252493 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((290278932353 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(290278932353 / 200000000000) = 1/(100000000000 / 290278932353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14115 : Bounds (1065672109 / 1000000000) (1065672111 / 1000000000) (Real.log (290278932353 / 100000000000)) := by
  have h := reflection_log_14115_neg
  have he : Real.log (290278932353 / 100000000000) = -Real.log (100000000000 / 290278932353) := by
    rw [show ((290278932353 / 100000000000) : ℝ) = ((100000000000 / 290278932353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14116_neg : (2395715433 / 1000000000) ≤ -Real.log (100000000000 / 1097604790419) ∧
    -Real.log (100000000000 / 1097604790419) ≤ (2395715437 / 1000000000) := by
  have h := checkLog_sound (w := (297604790419 / 1897604790419)) (n := 12)
    (lo := (316273893 / 1000000000)) (hi := (158136947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097604790419 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1097604790419 / 800000000000) = 1/(100000000000 / 1097604790419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14116 : Bounds (2395715433 / 1000000000) (2395715437 / 1000000000) (Real.log (1097604790419 / 100000000000)) := by
  have h := reflection_log_14116_neg
  have he : Real.log (1097604790419 / 100000000000) = -Real.log (100000000000 / 1097604790419) := by
    rw [show ((1097604790419 / 100000000000) : ℝ) = ((100000000000 / 1097604790419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14117_neg : (2415478141 / 1000000000) ≤ -Real.log (50000000000 / 559756097561) ∧
    -Real.log (50000000000 / 559756097561) ≤ (483095629 / 200000000) := by
  have h := checkLog_sound (w := (159756097561 / 959756097561)) (n := 12)
    (lo := (336036601 / 1000000000)) (hi := (168018301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((559756097561 / 400000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(559756097561 / 400000000000) = 1/(50000000000 / 559756097561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14117 : Bounds (2415478141 / 1000000000) (483095629 / 200000000) (Real.log (559756097561 / 50000000000)) := by
  have h := reflection_log_14117_neg
  have he : Real.log (559756097561 / 50000000000) = -Real.log (50000000000 / 559756097561) := by
    rw [show ((559756097561 / 50000000000) : ℝ) = ((50000000000 / 559756097561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14118_neg : (121844389 / 200000000) ≤ -Real.log (1000 / 1839) ∧
    -Real.log (1000 / 1839) ≤ (304610973 / 500000000) := by
  have h := checkLog_sound (w := (839 / 2839)) (n := 12)
    (lo := (121844389 / 200000000)) (hi := (304610973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1839 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1839 / 1000) = 1/(1000 / 1839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14118 : Bounds (121844389 / 200000000) (304610973 / 500000000) (Real.log (1839 / 1000)) := by
  have h := reflection_log_14118_neg
  have he : Real.log (1839 / 1000) = -Real.log (1000 / 1839) := by
    rw [show ((1839 / 1000) : ℝ) = ((1000 / 1839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14119_neg : (28536733 / 15625000) ≤ -Real.log (161 / 1000) ∧
    -Real.log (161 / 1000) ≤ (365270183 / 200000000) := by
  have h := checkLog_sound (w := (89 / 411)) (n := 12)
    (lo := (55007069 / 125000000)) (hi := (440056553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 161) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 161) = 1/(161 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14119 : Bounds (-365270183 / 200000000) (-28536733 / 15625000) (Real.log (161 / 1000)) := by
  have h := reflection_log_14119_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14120_neg : (104831 / 125000000) ≤ -Real.log (1000000 / 1000839) ∧
    -Real.log (1000000 / 1000839) ≤ (838649 / 1000000000) := by
  have h := checkLog_sound (w := (839 / 2000839)) (n := 12)
    (lo := (104831 / 125000000)) (hi := (838649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000839 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000839 / 1000000) = 1/(1000000 / 1000839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14120 : Bounds (104831 / 125000000) (838649 / 1000000000) (Real.log (1000839 / 1000000)) := by
  have h := reflection_log_14120_neg
  have he : Real.log (1000839 / 1000000) = -Real.log (1000000 / 1000839) := by
    rw [show ((1000839 / 1000000) : ℝ) = ((1000000 / 1000839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14121_neg : (104919 / 125000000) ≤ -Real.log (999161 / 1000000) ∧
    -Real.log (999161 / 1000000) ≤ (839353 / 1000000000) := by
  have h := checkLog_sound (w := (839 / 1999161)) (n := 12)
    (lo := (104919 / 125000000)) (hi := (839353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999161) = 1/(999161 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14121 : Bounds (-839353 / 1000000000) (-104919 / 125000000) (Real.log (999161 / 1000000)) := by
  have h := reflection_log_14121_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14122_neg : (198338301 / 500000000) ≤ -Real.log (1600 / 2379) ∧
    -Real.log (1600 / 2379) ≤ (396676603 / 1000000000) := by
  have h := checkLog_sound (w := (779 / 3979)) (n := 12)
    (lo := (198338301 / 500000000)) (hi := (396676603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2379 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2379 / 1600) = 1/(1600 / 2379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14122 : Bounds (198338301 / 500000000) (396676603 / 1000000000) (Real.log (2379 / 1600)) := by
  have h := reflection_log_14122_neg
  have he : Real.log (2379 / 1600) = -Real.log (1600 / 2379) := by
    rw [show ((2379 / 1600) : ℝ) = ((1600 / 2379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14123_neg : (333617899 / 500000000) ≤ -Real.log (821 / 1600) ∧
    -Real.log (821 / 1600) ≤ (667235799 / 1000000000) := by
  have h := checkLog_sound (w := (779 / 2421)) (n := 12)
    (lo := (333617899 / 500000000)) (hi := (667235799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600 / 821) = 1/(821 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14123 : Bounds (-667235799 / 1000000000) (-333617899 / 500000000) (Real.log (821 / 1600)) := by
  have h := reflection_log_14123_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14124_neg : (99693191 / 250000000) ≤ -Real.log (200000 / 297999) ∧
    -Real.log (200000 / 297999) ≤ (79754553 / 200000000) := by
  have h := checkLog_sound (w := (97999 / 497999)) (n := 12)
    (lo := (99693191 / 250000000)) (hi := (79754553 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297999 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297999 / 200000) = 1/(200000 / 297999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14124 : Bounds (99693191 / 250000000) (79754553 / 200000000) (Real.log (297999 / 200000)) := by
  have h := reflection_log_14124_neg
  have he : Real.log (297999 / 200000) = -Real.log (200000 / 297999) := by
    rw [show ((297999 / 200000) : ℝ) = ((200000 / 297999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14125_neg : (673334749 / 1000000000) ≤ -Real.log (102001 / 200000) ∧
    -Real.log (102001 / 200000) ≤ (2693339 / 4000000) := by
  have h := checkLog_sound (w := (97999 / 302001)) (n := 12)
    (lo := (673334749 / 1000000000)) (hi := (2693339 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 102001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 102001) = 1/(102001 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14125 : Bounds (-2693339 / 4000000) (-673334749 / 1000000000) (Real.log (102001 / 200000)) := by
  have h := reflection_log_14125_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14126_neg : (54912397 / 200000000) ≤ -Real.log (30396195999 / 40000000000) ∧
    -Real.log (30396195999 / 40000000000) ≤ (137280993 / 500000000) := by
  have h := checkLog_sound (w := (9603804001 / 70396195999)) (n := 12)
    (lo := (54912397 / 200000000)) (hi := (137280993 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 30396195999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 30396195999) = 1/(30396195999 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14126 : Bounds (-137280993 / 500000000) (-54912397 / 200000000) (Real.log (30396195999 / 40000000000)) := by
  have h := reflection_log_14126_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14127_neg : (67639799 / 250000000) ≤ -Real.log (1953159 / 2560000) ∧
    -Real.log (1953159 / 2560000) ≤ (270559197 / 1000000000) := by
  have h := checkLog_sound (w := (606841 / 4513159)) (n := 12)
    (lo := (67639799 / 250000000)) (hi := (270559197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560000 / 1953159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560000 / 1953159) = 1/(1953159 / 2560000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14127 : Bounds (-270559197 / 1000000000) (-67639799 / 250000000) (Real.log (1953159 / 2560000)) := by
  have h := reflection_log_14127_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14128_neg : (2659781 / 2500000) ≤ -Real.log (500000000000 / 1448842874543) ∧
    -Real.log (500000000000 / 1448842874543) ≤ (531956201 / 500000000) := by
  have h := checkLog_sound (w := (448842874543 / 2448842874543)) (n := 12)
    (lo := (18538261 / 50000000)) (hi := (370765221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1448842874543 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1448842874543 / 1000000000000) = 1/(500000000000 / 1448842874543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14128 : Bounds (2659781 / 2500000) (531956201 / 500000000) (Real.log (1448842874543 / 500000000000)) := by
  have h := reflection_log_14128_neg
  have he : Real.log (1448842874543 / 500000000000) = -Real.log (500000000000 / 1448842874543) := by
    rw [show ((1448842874543 / 500000000000) : ℝ) = ((500000000000 / 1448842874543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14129_neg : (1072107513 / 1000000000) ≤ -Real.log (500000000000 / 1460765090539) ∧
    -Real.log (500000000000 / 1460765090539) ≤ (214421503 / 200000000) := by
  have h := checkLog_sound (w := (460765090539 / 2460765090539)) (n := 12)
    (lo := (378960333 / 1000000000)) (hi := (189480167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1460765090539 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1460765090539 / 1000000000000) = 1/(500000000000 / 1460765090539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14129 : Bounds (1072107513 / 1000000000) (214421503 / 200000000) (Real.log (1460765090539 / 500000000000)) := by
  have h := reflection_log_14129_neg
  have he : Real.log (1460765090539 / 500000000000) = -Real.log (500000000000 / 1460765090539) := by
    rw [show ((1460765090539 / 500000000000) : ℝ) = ((500000000000 / 1460765090539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14130_neg : (2415478141 / 1000000000) ≤ -Real.log (500000000000 / 5597560975609) ∧
    -Real.log (500000000000 / 5597560975609) ≤ (483095629 / 200000000) := by
  have h := checkLog_sound (w := (1597560975609 / 9597560975609)) (n := 12)
    (lo := (336036601 / 1000000000)) (hi := (168018301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5597560975609 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5597560975609 / 4000000000000) = 1/(500000000000 / 5597560975609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14130 : Bounds (2415478141 / 1000000000) (483095629 / 200000000) (Real.log (5597560975609 / 500000000000)) := by
  have h := reflection_log_14130_neg
  have he : Real.log (5597560975609 / 500000000000) = -Real.log (500000000000 / 5597560975609) := by
    rw [show ((5597560975609 / 500000000000) : ℝ) = ((500000000000 / 5597560975609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14131_neg : (2435572857 / 1000000000) ≤ -Real.log (7812500000 / 89237189441) ∧
    -Real.log (7812500000 / 89237189441) ≤ (2435572861 / 1000000000) := by
  have h := checkLog_sound (w := (26737189441 / 151737189441)) (n := 12)
    (lo := (356131317 / 1000000000)) (hi := (178065659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89237189441 / 62500000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(89237189441 / 62500000000) = 1/(7812500000 / 89237189441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14131 : Bounds (2435572857 / 1000000000) (2435572861 / 1000000000) (Real.log (89237189441 / 7812500000)) := by
  have h := reflection_log_14131_neg
  have he : Real.log (89237189441 / 7812500000) = -Real.log (7812500000 / 89237189441) := by
    rw [show ((89237189441 / 7812500000) : ℝ) = ((7812500000 / 89237189441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14132_neg : (610851937 / 1000000000) ≤ -Real.log (500 / 921) ∧
    -Real.log (500 / 921) ≤ (305425969 / 500000000) := by
  have h := checkLog_sound (w := (421 / 1421)) (n := 12)
    (lo := (610851937 / 1000000000)) (hi := (305425969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((921 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(921 / 500) = 1/(500 / 921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14132 : Bounds (610851937 / 1000000000) (305425969 / 500000000) (Real.log (921 / 500)) := by
  have h := reflection_log_14132_neg
  have he : Real.log (921 / 500) = -Real.log (500 / 921) := by
    rw [show ((921 / 500) : ℝ) = ((500 / 921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14133_neg : (461290061 / 250000000) ≤ -Real.log (79 / 500) ∧
    -Real.log (79 / 500) ≤ (1845160247 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 102)) (n := 12)
    (lo := (114716471 / 250000000)) (hi := (91773177 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 79) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 79) = 1/(79 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14133 : Bounds (-1845160247 / 1000000000) (-461290061 / 250000000) (Real.log (79 / 500)) := by
  have h := reflection_log_14133_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14134_neg : (168329 / 200000000) ≤ -Real.log (500000 / 500421) ∧
    -Real.log (500000 / 500421) ≤ (420823 / 500000000) := by
  have h := checkLog_sound (w := (421 / 1000421)) (n := 12)
    (lo := (168329 / 200000000)) (hi := (420823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500421 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500421 / 500000) = 1/(500000 / 500421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14134 : Bounds (168329 / 200000000) (420823 / 500000000) (Real.log (500421 / 500000)) := by
  have h := reflection_log_14134_neg
  have he : Real.log (500421 / 500000) = -Real.log (500000 / 500421) := by
    rw [show ((500421 / 500000) : ℝ) = ((500000 / 500421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14135_neg : (421177 / 500000000) ≤ -Real.log (499579 / 500000) ∧
    -Real.log (499579 / 500000) ≤ (168471 / 200000000) := by
  have h := checkLog_sound (w := (421 / 999579)) (n := 12)
    (lo := (421177 / 500000000)) (hi := (168471 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499579) = 1/(499579 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14135 : Bounds (-168471 / 200000000) (-421177 / 500000000) (Real.log (499579 / 500000)) := by
  have h := reflection_log_14135_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14136_neg : (15932893 / 40000000) ≤ -Real.log (250000 / 372331) ∧
    -Real.log (250000 / 372331) ≤ (199161163 / 500000000) := by
  have h := checkLog_sound (w := (122331 / 622331)) (n := 12)
    (lo := (15932893 / 40000000)) (hi := (199161163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372331 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372331 / 250000) = 1/(250000 / 372331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14136 : Bounds (15932893 / 40000000) (199161163 / 500000000) (Real.log (372331 / 250000)) := by
  have h := reflection_log_14136_neg
  have he : Real.log (372331 / 250000) = -Real.log (250000 / 372331) := by
    rw [show ((372331 / 250000) : ℝ) = ((250000 / 372331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14137_neg : (33600997 / 50000000) ≤ -Real.log (127669 / 250000) ∧
    -Real.log (127669 / 250000) ≤ (672019941 / 1000000000) := by
  have h := checkLog_sound (w := (122331 / 377669)) (n := 12)
    (lo := (33600997 / 50000000)) (hi := (672019941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 127669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 127669) = 1/(127669 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14137 : Bounds (-672019941 / 1000000000) (-33600997 / 50000000) (Real.log (127669 / 250000)) := by
  have h := reflection_log_14137_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14138_neg : (80084751 / 200000000) ≤ -Real.log (1000000 / 1492457) ∧
    -Real.log (1000000 / 1492457) ≤ (100105939 / 250000000) := by
  have h := checkLog_sound (w := (492457 / 2492457)) (n := 12)
    (lo := (80084751 / 200000000)) (hi := (100105939 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1492457 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1492457 / 1000000) = 1/(1000000 / 1492457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14138 : Bounds (80084751 / 200000000) (100105939 / 250000000) (Real.log (1492457 / 1000000)) := by
  have h := reflection_log_14138_neg
  have he : Real.log (1492457 / 1000000) = -Real.log (1000000 / 1492457) := by
    rw [show ((1492457 / 1000000) : ℝ) = ((1000000 / 1492457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14139_neg : (339086921 / 500000000) ≤ -Real.log (507543 / 1000000) ∧
    -Real.log (507543 / 1000000) ≤ (678173843 / 1000000000) := by
  have h := checkLog_sound (w := (492457 / 1507543)) (n := 12)
    (lo := (339086921 / 500000000)) (hi := (678173843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 507543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 507543) = 1/(507543 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14139 : Bounds (-678173843 / 1000000000) (-339086921 / 500000000) (Real.log (507543 / 1000000)) := by
  have h := reflection_log_14139_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14140_neg : (277750087 / 1000000000) ≤ -Real.log (757486103151 / 1000000000000) ∧
    -Real.log (757486103151 / 1000000000000) ≤ (34718761 / 125000000) := by
  have h := checkLog_sound (w := (242513896849 / 1757486103151)) (n := 12)
    (lo := (277750087 / 1000000000)) (hi := (34718761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 757486103151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 757486103151) = 1/(757486103151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14140 : Bounds (-34718761 / 125000000) (-277750087 / 1000000000) (Real.log (757486103151 / 1000000000000)) := by
  have h := reflection_log_14140_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14141_neg : (54739523 / 200000000) ≤ -Real.log (47535126439 / 62500000000) ∧
    -Real.log (47535126439 / 62500000000) ≤ (17106101 / 62500000) := by
  have h := checkLog_sound (w := (14964873561 / 110035126439)) (n := 12)
    (lo := (54739523 / 200000000)) (hi := (17106101 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 47535126439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 47535126439) = 1/(47535126439 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14141 : Bounds (-17106101 / 62500000) (-54739523 / 200000000) (Real.log (47535126439 / 62500000000)) := by
  have h := reflection_log_14141_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14142_neg : (214068453 / 200000000) ≤ -Real.log (50000000000 / 145818875373) ∧
    -Real.log (50000000000 / 145818875373) ≤ (1070342267 / 1000000000) := by
  have h := checkLog_sound (w := (45818875373 / 245818875373)) (n := 12)
    (lo := (75439017 / 200000000)) (hi := (188597543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145818875373 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(145818875373 / 100000000000) = 1/(50000000000 / 145818875373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14142 : Bounds (214068453 / 200000000) (1070342267 / 1000000000) (Real.log (145818875373 / 50000000000)) := by
  have h := reflection_log_14142_neg
  have he : Real.log (145818875373 / 50000000000) = -Real.log (50000000000 / 145818875373) := by
    rw [show ((145818875373 / 50000000000) : ℝ) = ((50000000000 / 145818875373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14143_neg : (1078597597 / 1000000000) ≤ -Real.log (250000000000 / 735138205039) ∧
    -Real.log (250000000000 / 735138205039) ≤ (1078597599 / 1000000000) := by
  have h := checkLog_sound (w := (235138205039 / 1235138205039)) (n := 12)
    (lo := (385450417 / 1000000000)) (hi := (192725209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735138205039 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(735138205039 / 500000000000) = 1/(250000000000 / 735138205039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14143 : Bounds (1078597597 / 1000000000) (1078597599 / 1000000000) (Real.log (735138205039 / 250000000000)) := by
  have h := reflection_log_14143_neg
  have he : Real.log (735138205039 / 250000000000) = -Real.log (250000000000 / 735138205039) := by
    rw [show ((735138205039 / 250000000000) : ℝ) = ((250000000000 / 735138205039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0221 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14144_neg : (2435572857 / 1000000000) ≤ -Real.log (500000000000 / 5711180124223) ∧
    -Real.log (500000000000 / 5711180124223) ≤ (2435572861 / 1000000000) := by
  have h := checkLog_sound (w := (1711180124223 / 9711180124223)) (n := 12)
    (lo := (356131317 / 1000000000)) (hi := (178065659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5711180124223 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5711180124223 / 4000000000000) = 1/(500000000000 / 5711180124223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14144 : Bounds (2435572857 / 1000000000) (2435572861 / 1000000000) (Real.log (5711180124223 / 500000000000)) := by
  have h := reflection_log_14144_neg
  have he : Real.log (5711180124223 / 500000000000) = -Real.log (500000000000 / 5711180124223) := by
    rw [show ((5711180124223 / 500000000000) : ℝ) = ((500000000000 / 5711180124223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14145_neg : (1228006091 / 500000000) ≤ -Real.log (500000000000 / 5829113924051) ∧
    -Real.log (500000000000 / 5829113924051) ≤ (1228006093 / 500000000) := by
  have h := checkLog_sound (w := (1829113924051 / 9829113924051)) (n := 12)
    (lo := (188285321 / 500000000)) (hi := (376570643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5829113924051 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5829113924051 / 4000000000000) = 1/(500000000000 / 5829113924051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14145 : Bounds (1228006091 / 500000000) (1228006093 / 500000000) (Real.log (5829113924051 / 500000000000)) := by
  have h := reflection_log_14145_neg
  have he : Real.log (5829113924051 / 500000000000) = -Real.log (500000000000 / 5829113924051) := by
    rw [show ((5829113924051 / 500000000000) : ℝ) = ((500000000000 / 5829113924051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14146_neg : (612479277 / 1000000000) ≤ -Real.log (200 / 369) ∧
    -Real.log (200 / 369) ≤ (306239639 / 500000000) := by
  have h := checkLog_sound (w := (169 / 569)) (n := 12)
    (lo := (612479277 / 1000000000)) (hi := (306239639 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369 / 200) = 1/(200 / 369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14146 : Bounds (612479277 / 1000000000) (306239639 / 500000000) (Real.log (369 / 200)) := by
  have h := reflection_log_14146_neg
  have he : Real.log (369 / 200) = -Real.log (200 / 369) := by
    rw [show ((369 / 200) : ℝ) = ((200 / 369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14147_neg : (23304127 / 12500000) ≤ -Real.log (31 / 200) ∧
    -Real.log (31 / 200) ≤ (1864330163 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 81)) (n := 12)
    (lo := (2390179 / 5000000)) (hi := (478035801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 31) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50 / 31) = 1/(31 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14147 : Bounds (-1864330163 / 1000000000) (-23304127 / 12500000) (Real.log (31 / 200)) := by
  have h := reflection_log_14147_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14148_neg : (844643 / 1000000000) ≤ -Real.log (200000 / 200169) ∧
    -Real.log (200000 / 200169) ≤ (211161 / 250000000) := by
  have h := checkLog_sound (w := (169 / 400169)) (n := 12)
    (lo := (844643 / 1000000000)) (hi := (211161 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200169 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200169 / 200000) = 1/(200000 / 200169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14148 : Bounds (844643 / 1000000000) (211161 / 250000000) (Real.log (200169 / 200000)) := by
  have h := reflection_log_14148_neg
  have he : Real.log (200169 / 200000) = -Real.log (200000 / 200169) := by
    rw [show ((200169 / 200000) : ℝ) = ((200000 / 200169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14149_neg : (845357 / 1000000000) ≤ -Real.log (199831 / 200000) ∧
    -Real.log (199831 / 200000) ≤ (422679 / 500000000) := by
  have h := checkLog_sound (w := (169 / 399831)) (n := 12)
    (lo := (845357 / 1000000000)) (hi := (422679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199831) = 1/(199831 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14149 : Bounds (-422679 / 500000000) (-845357 / 1000000000) (Real.log (199831 / 200000)) := by
  have h := reflection_log_14149_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14150_neg : (399973389 / 1000000000) ≤ -Real.log (200000 / 298357) ∧
    -Real.log (200000 / 298357) ≤ (39997339 / 100000000) := by
  have h := checkLog_sound (w := (98357 / 498357)) (n := 12)
    (lo := (399973389 / 1000000000)) (hi := (39997339 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298357 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298357 / 200000) = 1/(200000 / 298357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14150 : Bounds (399973389 / 1000000000) (39997339 / 100000000) (Real.log (298357 / 200000)) := by
  have h := reflection_log_14150_neg
  have he : Real.log (298357 / 200000) = -Real.log (200000 / 298357) := by
    rw [show ((298357 / 200000) : ℝ) = ((200000 / 298357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14151_neg : (169212673 / 250000000) ≤ -Real.log (101643 / 200000) ∧
    -Real.log (101643 / 200000) ≤ (676850693 / 1000000000) := by
  have h := checkLog_sound (w := (98357 / 301643)) (n := 12)
    (lo := (169212673 / 250000000)) (hi := (676850693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 101643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 101643) = 1/(101643 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14151 : Bounds (-676850693 / 1000000000) (-169212673 / 250000000) (Real.log (101643 / 200000)) := by
  have h := reflection_log_14151_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14152_neg : (5026009 / 12500000) ≤ -Real.log (250000 / 373733) ∧
    -Real.log (250000 / 373733) ≤ (402080721 / 1000000000) := by
  have h := checkLog_sound (w := (123733 / 623733)) (n := 12)
    (lo := (5026009 / 12500000)) (hi := (402080721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373733 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373733 / 250000) = 1/(250000 / 373733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14152 : Bounds (5026009 / 12500000) (402080721 / 1000000000) (Real.log (373733 / 250000)) := by
  have h := reflection_log_14152_neg
  have he : Real.log (373733 / 250000) = -Real.log (250000 / 373733) := by
    rw [show ((373733 / 250000) : ℝ) = ((250000 / 373733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14153_neg : (136612441 / 200000000) ≤ -Real.log (126267 / 250000) ∧
    -Real.log (126267 / 250000) ≤ (341531103 / 500000000) := by
  have h := checkLog_sound (w := (123733 / 376267)) (n := 12)
    (lo := (136612441 / 200000000)) (hi := (341531103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 126267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 126267) = 1/(126267 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14153 : Bounds (-341531103 / 500000000) (-136612441 / 200000000) (Real.log (126267 / 250000)) := by
  have h := reflection_log_14153_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14154_neg : (70245371 / 250000000) ≤ -Real.log (47190144711 / 62500000000) ∧
    -Real.log (47190144711 / 62500000000) ≤ (56196297 / 200000000) := by
  have h := checkLog_sound (w := (15309855289 / 109690144711)) (n := 12)
    (lo := (70245371 / 250000000)) (hi := (56196297 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 47190144711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 47190144711) = 1/(47190144711 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14154 : Bounds (-56196297 / 200000000) (-70245371 / 250000000) (Real.log (47190144711 / 62500000000)) := by
  have h := reflection_log_14154_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14155_neg : (276877303 / 1000000000) ≤ -Real.log (30325900551 / 40000000000) ∧
    -Real.log (30325900551 / 40000000000) ≤ (34609663 / 125000000) := by
  have h := checkLog_sound (w := (9674099449 / 70325900551)) (n := 12)
    (lo := (276877303 / 1000000000)) (hi := (34609663 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 30325900551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 30325900551) = 1/(30325900551 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14155 : Bounds (-34609663 / 125000000) (-276877303 / 1000000000) (Real.log (30325900551 / 40000000000)) := by
  have h := reflection_log_14155_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14156_neg : (1076824081 / 1000000000) ≤ -Real.log (100000000000 / 293534232559) ∧
    -Real.log (100000000000 / 293534232559) ≤ (1076824083 / 1000000000) := by
  have h := checkLog_sound (w := (93534232559 / 493534232559)) (n := 12)
    (lo := (383676901 / 1000000000)) (hi := (191838451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293534232559 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(293534232559 / 200000000000) = 1/(100000000000 / 293534232559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14156 : Bounds (1076824081 / 1000000000) (1076824083 / 1000000000) (Real.log (293534232559 / 100000000000)) := by
  have h := reflection_log_14156_neg
  have he : Real.log (293534232559 / 100000000000) = -Real.log (100000000000 / 293534232559) := by
    rw [show ((293534232559 / 100000000000) : ℝ) = ((100000000000 / 293534232559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14157_neg : (43405717 / 40000000) ≤ -Real.log (62500000000 / 184991426897) ∧
    -Real.log (62500000000 / 184991426897) ≤ (1085142927 / 1000000000) := by
  have h := checkLog_sound (w := (59991426897 / 309991426897)) (n := 12)
    (lo := (78399149 / 200000000)) (hi := (195997873 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184991426897 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(184991426897 / 125000000000) = 1/(62500000000 / 184991426897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14157 : Bounds (43405717 / 40000000) (1085142927 / 1000000000) (Real.log (184991426897 / 62500000000)) := by
  have h := reflection_log_14157_neg
  have he : Real.log (184991426897 / 62500000000) = -Real.log (62500000000 / 184991426897) := by
    rw [show ((184991426897 / 62500000000) : ℝ) = ((62500000000 / 184991426897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14158_neg : (1228006091 / 500000000) ≤ -Real.log (10000000000 / 116582278481) ∧
    -Real.log (10000000000 / 116582278481) ≤ (1228006093 / 500000000) := by
  have h := checkLog_sound (w := (36582278481 / 196582278481)) (n := 12)
    (lo := (188285321 / 500000000)) (hi := (376570643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116582278481 / 80000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(116582278481 / 80000000000) = 1/(10000000000 / 116582278481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14158 : Bounds (1228006091 / 500000000) (1228006093 / 500000000) (Real.log (116582278481 / 10000000000)) := by
  have h := reflection_log_14158_neg
  have he : Real.log (116582278481 / 10000000000) = -Real.log (10000000000 / 116582278481) := by
    rw [show ((116582278481 / 10000000000) : ℝ) = ((10000000000 / 116582278481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14159_neg : (2476809437 / 1000000000) ≤ -Real.log (250000000000 / 2975806451613) ∧
    -Real.log (250000000000 / 2975806451613) ≤ (2476809441 / 1000000000) := by
  have h := checkLog_sound (w := (975806451613 / 4975806451613)) (n := 12)
    (lo := (397367897 / 1000000000)) (hi := (198683949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2975806451613 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2975806451613 / 2000000000000) = 1/(250000000000 / 2975806451613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14159 : Bounds (2476809437 / 1000000000) (2476809441 / 1000000000) (Real.log (2975806451613 / 250000000000)) := by
  have h := reflection_log_14159_neg
  have he : Real.log (2975806451613 / 250000000000) = -Real.log (250000000000 / 2975806451613) := by
    rw [show ((2975806451613 / 250000000000) : ℝ) = ((250000000000 / 2975806451613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14160_neg : (614103973 / 1000000000) ≤ -Real.log (125 / 231) ∧
    -Real.log (125 / 231) ≤ (307051987 / 500000000) := by
  have h := checkLog_sound (w := (53 / 178)) (n := 12)
    (lo := (614103973 / 1000000000)) (hi := (307051987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231 / 125) = 1/(125 / 231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14160 : Bounds (614103973 / 1000000000) (307051987 / 500000000) (Real.log (231 / 125)) := by
  have h := reflection_log_14160_neg
  have he : Real.log (231 / 125) = -Real.log (125 / 231) := by
    rw [show ((231 / 125) : ℝ) = ((125 / 231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14161_neg : (1883874757 / 1000000000) ≤ -Real.log (19 / 125) ∧
    -Real.log (19 / 125) ≤ (47096869 / 25000000) := by
  have h := checkLog_sound (w := (49 / 201)) (n := 12)
    (lo := (497580397 / 1000000000)) (hi := (248790199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 76) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 76) = 1/(19 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14161 : Bounds (-47096869 / 25000000) (-1883874757 / 1000000000) (Real.log (19 / 125)) := by
  have h := reflection_log_14161_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14162_neg : (21191 / 25000000) ≤ -Real.log (62500 / 62553) ∧
    -Real.log (62500 / 62553) ≤ (847641 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 125053)) (n := 12)
    (lo := (21191 / 25000000)) (hi := (847641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62553 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62553 / 62500) = 1/(62500 / 62553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14162 : Bounds (21191 / 25000000) (847641 / 1000000000) (Real.log (62553 / 62500)) := by
  have h := reflection_log_14162_neg
  have he : Real.log (62553 / 62500) = -Real.log (62500 / 62553) := by
    rw [show ((62553 / 62500) : ℝ) = ((62500 / 62553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14163_neg : (848359 / 1000000000) ≤ -Real.log (62447 / 62500) ∧
    -Real.log (62447 / 62500) ≤ (21209 / 25000000) := by
  have h := checkLog_sound (w := (53 / 124947)) (n := 12)
    (lo := (848359 / 1000000000)) (hi := (21209 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62447) = 1/(62447 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14163 : Bounds (-21209 / 25000000) (-848359 / 1000000000) (Real.log (62447 / 62500)) := by
  have h := reflection_log_14163_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14164_neg : (401631101 / 1000000000) ≤ -Real.log (50000 / 74713) ∧
    -Real.log (50000 / 74713) ≤ (200815551 / 500000000) := by
  have h := checkLog_sound (w := (24713 / 124713)) (n := 12)
    (lo := (401631101 / 1000000000)) (hi := (200815551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74713 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74713 / 50000) = 1/(50000 / 74713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14164 : Bounds (401631101 / 1000000000) (200815551 / 500000000) (Real.log (74713 / 50000)) := by
  have h := reflection_log_14164_neg
  have he : Real.log (74713 / 50000) = -Real.log (50000 / 74713) := by
    rw [show ((74713 / 50000) : ℝ) = ((50000 / 74713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14165_neg : (27269303 / 40000000) ≤ -Real.log (25287 / 50000) ∧
    -Real.log (25287 / 50000) ≤ (21304143 / 31250000) := by
  have h := checkLog_sound (w := (24713 / 75287)) (n := 12)
    (lo := (27269303 / 40000000)) (hi := (21304143 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 25287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 25287) = 1/(25287 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14165 : Bounds (-21304143 / 31250000) (-27269303 / 40000000) (Real.log (25287 / 50000)) := by
  have h := reflection_log_14165_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14166_neg : (80748859 / 200000000) ≤ -Real.log (1000000 / 1497421) ∧
    -Real.log (1000000 / 1497421) ≤ (50468037 / 125000000) := by
  have h := checkLog_sound (w := (497421 / 2497421)) (n := 12)
    (lo := (80748859 / 200000000)) (hi := (50468037 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1497421 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1497421 / 1000000) = 1/(1000000 / 1497421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14166 : Bounds (80748859 / 200000000) (50468037 / 125000000) (Real.log (1497421 / 1000000)) := by
  have h := reflection_log_14166_neg
  have he : Real.log (1497421 / 1000000) = -Real.log (1000000 / 1497421) := by
    rw [show ((1497421 / 1000000) : ℝ) = ((1000000 / 1497421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14167_neg : (688002437 / 1000000000) ≤ -Real.log (502579 / 1000000) ∧
    -Real.log (502579 / 1000000) ≤ (344001219 / 500000000) := by
  have h := checkLog_sound (w := (497421 / 1502579)) (n := 12)
    (lo := (688002437 / 1000000000)) (hi := (344001219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 502579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 502579) = 1/(502579 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14167 : Bounds (-344001219 / 500000000) (-688002437 / 1000000000) (Real.log (502579 / 1000000)) := by
  have h := reflection_log_14167_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14168_neg : (142129071 / 500000000) ≤ -Real.log (752572348759 / 1000000000000) ∧
    -Real.log (752572348759 / 1000000000000) ≤ (284258143 / 1000000000) := by
  have h := checkLog_sound (w := (247427651241 / 1752572348759)) (n := 12)
    (lo := (142129071 / 500000000)) (hi := (284258143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 752572348759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 752572348759) = 1/(752572348759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14168 : Bounds (-284258143 / 1000000000) (-142129071 / 500000000) (Real.log (752572348759 / 1000000000000)) := by
  have h := reflection_log_14168_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14169_neg : (140050737 / 500000000) ≤ -Real.log (1889267631 / 2500000000) ∧
    -Real.log (1889267631 / 2500000000) ≤ (11204059 / 40000000) := by
  have h := checkLog_sound (w := (610732369 / 4389267631)) (n := 12)
    (lo := (140050737 / 500000000)) (hi := (11204059 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 1889267631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 1889267631) = 1/(1889267631 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14169 : Bounds (-11204059 / 40000000) (-140050737 / 500000000) (Real.log (1889267631 / 2500000000)) := by
  have h := reflection_log_14169_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14170_neg : (270840919 / 250000000) ≤ -Real.log (100000000000 / 295460117847) ∧
    -Real.log (100000000000 / 295460117847) ≤ (541681839 / 500000000) := by
  have h := checkLog_sound (w := (95460117847 / 495460117847)) (n := 12)
    (lo := (24388531 / 62500000)) (hi := (390216497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295460117847 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(295460117847 / 200000000000) = 1/(100000000000 / 295460117847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14170 : Bounds (270840919 / 250000000) (541681839 / 500000000) (Real.log (295460117847 / 100000000000)) := by
  have h := reflection_log_14170_neg
  have he : Real.log (295460117847 / 100000000000) = -Real.log (100000000000 / 295460117847) := by
    rw [show ((295460117847 / 100000000000) : ℝ) = ((100000000000 / 295460117847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14171_neg : (1091746731 / 1000000000) ≤ -Real.log (6250000000 / 18621711711) ∧
    -Real.log (6250000000 / 18621711711) ≤ (1091746733 / 1000000000) := by
  have h := checkLog_sound (w := (6121711711 / 31121711711)) (n := 12)
    (lo := (398599551 / 1000000000)) (hi := (3114059 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18621711711 / 12500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(18621711711 / 12500000000) = 1/(6250000000 / 18621711711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14171 : Bounds (1091746731 / 1000000000) (1091746733 / 1000000000) (Real.log (18621711711 / 6250000000)) := by
  have h := reflection_log_14171_neg
  have he : Real.log (18621711711 / 6250000000) = -Real.log (6250000000 / 18621711711) := by
    rw [show ((18621711711 / 6250000000) : ℝ) = ((6250000000 / 18621711711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14172_neg : (2476809437 / 1000000000) ≤ -Real.log (20000000000 / 238064516129) ∧
    -Real.log (20000000000 / 238064516129) ≤ (2476809441 / 1000000000) := by
  have h := checkLog_sound (w := (78064516129 / 398064516129)) (n := 12)
    (lo := (397367897 / 1000000000)) (hi := (198683949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((238064516129 / 160000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(238064516129 / 160000000000) = 1/(20000000000 / 238064516129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14172 : Bounds (2476809437 / 1000000000) (2476809441 / 1000000000) (Real.log (238064516129 / 20000000000)) := by
  have h := reflection_log_14172_neg
  have he : Real.log (238064516129 / 20000000000) = -Real.log (20000000000 / 238064516129) := by
    rw [show ((238064516129 / 20000000000) : ℝ) = ((20000000000 / 238064516129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14173_neg : (2497978729 / 1000000000) ≤ -Real.log (250000000000 / 3039473684211) ∧
    -Real.log (250000000000 / 3039473684211) ≤ (2497978733 / 1000000000) := by
  have h := checkLog_sound (w := (1039473684211 / 5039473684211)) (n := 12)
    (lo := (418537189 / 1000000000)) (hi := (41853719 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3039473684211 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3039473684211 / 2000000000000) = 1/(250000000000 / 3039473684211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14173 : Bounds (2497978729 / 1000000000) (2497978733 / 1000000000) (Real.log (3039473684211 / 250000000000)) := by
  have h := reflection_log_14173_neg
  have he : Real.log (3039473684211 / 250000000000) = -Real.log (250000000000 / 3039473684211) := by
    rw [show ((3039473684211 / 250000000000) : ℝ) = ((250000000000 / 3039473684211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14174_neg : (615726033 / 1000000000) ≤ -Real.log (1000 / 1851) ∧
    -Real.log (1000 / 1851) ≤ (307863017 / 500000000) := by
  have h := checkLog_sound (w := (851 / 2851)) (n := 12)
    (lo := (615726033 / 1000000000)) (hi := (307863017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1851 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1851 / 1000) = 1/(1000 / 1851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14174 : Bounds (615726033 / 1000000000) (307863017 / 500000000) (Real.log (1851 / 1000)) := by
  have h := reflection_log_14174_neg
  have he : Real.log (1851 / 1000) = -Real.log (1000 / 1851) := by
    rw [show ((1851 / 1000) : ℝ) = ((1000 / 1851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14175_neg : (1903808971 / 1000000000) ≤ -Real.log (149 / 1000) ∧
    -Real.log (149 / 1000) ≤ (951904487 / 500000000) := by
  have h := checkLog_sound (w := (101 / 399)) (n := 12)
    (lo := (517514611 / 1000000000)) (hi := (129378653 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 149) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 149) = 1/(149 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14175 : Bounds (-951904487 / 500000000) (-1903808971 / 1000000000) (Real.log (149 / 1000)) := by
  have h := reflection_log_14175_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14176_neg : (425319 / 500000000) ≤ -Real.log (1000000 / 1000851) ∧
    -Real.log (1000000 / 1000851) ≤ (850639 / 1000000000) := by
  have h := checkLog_sound (w := (851 / 2000851)) (n := 12)
    (lo := (425319 / 500000000)) (hi := (850639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000851 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000851 / 1000000) = 1/(1000000 / 1000851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14176 : Bounds (425319 / 500000000) (850639 / 1000000000) (Real.log (1000851 / 1000000)) := by
  have h := reflection_log_14176_neg
  have he : Real.log (1000851 / 1000000) = -Real.log (1000000 / 1000851) := by
    rw [show ((1000851 / 1000000) : ℝ) = ((1000000 / 1000851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14177_neg : (425681 / 500000000) ≤ -Real.log (999149 / 1000000) ∧
    -Real.log (999149 / 1000000) ≤ (851363 / 1000000000) := by
  have h := checkLog_sound (w := (851 / 1999149)) (n := 12)
    (lo := (425681 / 500000000)) (hi := (851363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999149) = 1/(999149 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14177 : Bounds (-851363 / 1000000000) (-425681 / 500000000) (Real.log (999149 / 1000000)) := by
  have h := reflection_log_14177_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14178_neg : (201647377 / 500000000) ≤ -Real.log (250000 / 374187) ∧
    -Real.log (250000 / 374187) ≤ (80658951 / 200000000) := by
  have h := checkLog_sound (w := (124187 / 624187)) (n := 12)
    (lo := (201647377 / 500000000)) (hi := (80658951 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374187 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374187 / 250000) = 1/(250000 / 374187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14178 : Bounds (201647377 / 500000000) (80658951 / 200000000) (Real.log (374187 / 250000)) := by
  have h := reflection_log_14178_neg
  have he : Real.log (374187 / 250000) = -Real.log (250000 / 374187) := by
    rw [show ((374187 / 250000) : ℝ) = ((250000 / 374187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14179_neg : (8583303 / 12500000) ≤ -Real.log (125813 / 250000) ∧
    -Real.log (125813 / 250000) ≤ (686664241 / 1000000000) := by
  have h := checkLog_sound (w := (124187 / 375813)) (n := 12)
    (lo := (8583303 / 12500000)) (hi := (686664241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 125813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 125813) = 1/(125813 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14179 : Bounds (-686664241 / 1000000000) (-8583303 / 12500000) (Real.log (125813 / 250000)) := by
  have h := reflection_log_14179_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14180_neg : (405413773 / 1000000000) ≤ -Real.log (1000000 / 1499923) ∧
    -Real.log (1000000 / 1499923) ≤ (202706887 / 500000000) := by
  have h := checkLog_sound (w := (499923 / 2499923)) (n := 12)
    (lo := (405413773 / 1000000000)) (hi := (202706887 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1499923 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1499923 / 1000000) = 1/(1000000 / 1499923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14180 : Bounds (405413773 / 1000000000) (202706887 / 500000000) (Real.log (1499923 / 1000000)) := by
  have h := reflection_log_14180_neg
  have he : Real.log (1499923 / 1000000) = -Real.log (1000000 / 1499923) := by
    rw [show ((1499923 / 1000000) : ℝ) = ((1000000 / 1499923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14181_neg : (86624149 / 125000000) ≤ -Real.log (500077 / 1000000) ∧
    -Real.log (500077 / 1000000) ≤ (692993193 / 1000000000) := by
  have h := checkLog_sound (w := (499923 / 1500077)) (n := 12)
    (lo := (86624149 / 125000000)) (hi := (692993193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 500077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 500077) = 1/(500077 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14181 : Bounds (-692993193 / 1000000000) (-86624149 / 125000000) (Real.log (500077 / 1000000)) := by
  have h := reflection_log_14181_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14182_neg : (143789709 / 500000000) ≤ -Real.log (750076994071 / 1000000000000) ∧
    -Real.log (750076994071 / 1000000000000) ≤ (287579419 / 1000000000) := by
  have h := checkLog_sound (w := (249923005929 / 1750076994071)) (n := 12)
    (lo := (143789709 / 500000000)) (hi := (287579419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 750076994071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 750076994071) = 1/(750076994071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14182 : Bounds (-287579419 / 1000000000) (-143789709 / 500000000) (Real.log (750076994071 / 1000000000000)) := by
  have h := reflection_log_14182_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14183_neg : (56673897 / 200000000) ≤ -Real.log (47077589031 / 62500000000) ∧
    -Real.log (47077589031 / 62500000000) ≤ (141684743 / 500000000) := by
  have h := checkLog_sound (w := (15422410969 / 109577589031)) (n := 12)
    (lo := (56673897 / 200000000)) (hi := (141684743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 47077589031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 47077589031) = 1/(47077589031 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14183 : Bounds (-141684743 / 500000000) (-56673897 / 200000000) (Real.log (47077589031 / 62500000000)) := by
  have h := reflection_log_14183_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14184_neg : (544979497 / 500000000) ≤ -Real.log (500000000000 / 1487076057323) ∧
    -Real.log (500000000000 / 1487076057323) ≤ (272489749 / 250000000) := by
  have h := checkLog_sound (w := (487076057323 / 2487076057323)) (n := 12)
    (lo := (198405907 / 500000000)) (hi := (79362363 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1487076057323 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1487076057323 / 1000000000000) = 1/(500000000000 / 1487076057323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14184 : Bounds (544979497 / 500000000) (272489749 / 250000000) (Real.log (1487076057323 / 500000000000)) := by
  have h := reflection_log_14184_neg
  have he : Real.log (1487076057323 / 500000000000) = -Real.log (500000000000 / 1487076057323) := by
    rw [show ((1487076057323 / 500000000000) : ℝ) = ((500000000000 / 1487076057323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14185_neg : (219681393 / 200000000) ≤ -Real.log (20000000000 / 59987681897) ∧
    -Real.log (20000000000 / 59987681897) ≤ (1098406967 / 1000000000) := by
  have h := checkLog_sound (w := (19987681897 / 99987681897)) (n := 12)
    (lo := (81051957 / 200000000)) (hi := (202629893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59987681897 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(59987681897 / 40000000000) = 1/(20000000000 / 59987681897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14185 : Bounds (219681393 / 200000000) (1098406967 / 1000000000) (Real.log (59987681897 / 20000000000)) := by
  have h := reflection_log_14185_neg
  have he : Real.log (59987681897 / 20000000000) = -Real.log (20000000000 / 59987681897) := by
    rw [show ((59987681897 / 20000000000) : ℝ) = ((20000000000 / 59987681897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14186_neg : (2497978729 / 1000000000) ≤ -Real.log (500000000000 / 6078947368421) ∧
    -Real.log (500000000000 / 6078947368421) ≤ (2497978733 / 1000000000) := by
  have h := checkLog_sound (w := (2078947368421 / 10078947368421)) (n := 12)
    (lo := (418537189 / 1000000000)) (hi := (41853719 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6078947368421 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6078947368421 / 4000000000000) = 1/(500000000000 / 6078947368421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14186 : Bounds (2497978729 / 1000000000) (2497978733 / 1000000000) (Real.log (6078947368421 / 500000000000)) := by
  have h := reflection_log_14186_neg
  have he : Real.log (6078947368421 / 500000000000) = -Real.log (500000000000 / 6078947368421) := by
    rw [show ((6078947368421 / 500000000000) : ℝ) = ((500000000000 / 6078947368421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14187_neg : (629883751 / 250000000) ≤ -Real.log (250000000000 / 3105704697987) ∧
    -Real.log (250000000000 / 3105704697987) ≤ (78735469 / 31250000) := by
  have h := checkLog_sound (w := (1105704697987 / 5105704697987)) (n := 12)
    (lo := (55011683 / 125000000)) (hi := (88018693 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3105704697987 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3105704697987 / 2000000000000) = 1/(250000000000 / 3105704697987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14187 : Bounds (629883751 / 250000000) (78735469 / 31250000) (Real.log (3105704697987 / 250000000000)) := by
  have h := reflection_log_14187_neg
  have he : Real.log (3105704697987 / 250000000000) = -Real.log (250000000000 / 3105704697987) := by
    rw [show ((3105704697987 / 250000000000) : ℝ) = ((250000000000 / 3105704697987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14188_neg : (617345467 / 1000000000) ≤ -Real.log (500 / 927) ∧
    -Real.log (500 / 927) ≤ (154336367 / 250000000) := by
  have h := checkLog_sound (w := (427 / 1427)) (n := 12)
    (lo := (617345467 / 1000000000)) (hi := (154336367 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((927 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(927 / 500) = 1/(500 / 927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14188 : Bounds (617345467 / 1000000000) (154336367 / 250000000) (Real.log (927 / 500)) := by
  have h := reflection_log_14188_neg
  have he : Real.log (927 / 500) = -Real.log (500 / 927) := by
    rw [show ((927 / 500) : ℝ) = ((500 / 927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14189_neg : (120259291 / 62500000) ≤ -Real.log (73 / 500) ∧
    -Real.log (73 / 500) ≤ (1924148659 / 1000000000) := by
  have h := checkLog_sound (w := (26 / 99)) (n := 12)
    (lo := (67231787 / 125000000)) (hi := (537854297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 73) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 73) = 1/(73 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14189 : Bounds (-1924148659 / 1000000000) (-120259291 / 62500000) (Real.log (73 / 500)) := by
  have h := reflection_log_14189_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14190_neg : (170727 / 200000000) ≤ -Real.log (500000 / 500427) ∧
    -Real.log (500000 / 500427) ≤ (213409 / 250000000) := by
  have h := checkLog_sound (w := (427 / 1000427)) (n := 12)
    (lo := (170727 / 200000000)) (hi := (213409 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500427 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500427 / 500000) = 1/(500000 / 500427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14190 : Bounds (170727 / 200000000) (213409 / 250000000) (Real.log (500427 / 500000)) := by
  have h := reflection_log_14190_neg
  have he : Real.log (500427 / 500000) = -Real.log (500000 / 500427) := by
    rw [show ((500427 / 500000) : ℝ) = ((500000 / 500427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14191_neg : (213591 / 250000000) ≤ -Real.log (499573 / 500000) ∧
    -Real.log (499573 / 500000) ≤ (170873 / 200000000) := by
  have h := checkLog_sound (w := (427 / 999573)) (n := 12)
    (lo := (213591 / 250000000)) (hi := (170873 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499573) = 1/(499573 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14191 : Bounds (-170873 / 200000000) (-213591 / 250000000) (Real.log (499573 / 500000)) := by
  have h := reflection_log_14191_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14192_neg : (404964983 / 1000000000) ≤ -Real.log (4000 / 5997) ∧
    -Real.log (4000 / 5997) ≤ (50620623 / 125000000) := by
  have h := checkLog_sound (w := (1997 / 9997)) (n := 12)
    (lo := (404964983 / 1000000000)) (hi := (50620623 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5997 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5997 / 4000) = 1/(4000 / 5997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14192 : Bounds (404964983 / 1000000000) (50620623 / 125000000) (Real.log (5997 / 4000)) := by
  have h := reflection_log_14192_neg
  have he : Real.log (5997 / 4000) = -Real.log (4000 / 5997) := by
    rw [show ((5997 / 4000) : ℝ) = ((4000 / 5997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14193_neg : (43228019 / 62500000) ≤ -Real.log (2003 / 4000) ∧
    -Real.log (2003 / 4000) ≤ (138329661 / 200000000) := by
  have h := checkLog_sound (w := (1997 / 6003)) (n := 12)
    (lo := (43228019 / 62500000)) (hi := (138329661 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 2003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000 / 2003) = 1/(2003 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14193 : Bounds (-138329661 / 200000000) (-43228019 / 62500000) (Real.log (2003 / 4000)) := by
  have h := reflection_log_14193_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14194_neg : (407089787 / 1000000000) ≤ -Real.log (1000000 / 1502439) ∧
    -Real.log (1000000 / 1502439) ≤ (101772447 / 250000000) := by
  have h := checkLog_sound (w := (502439 / 2502439)) (n := 12)
    (lo := (407089787 / 1000000000)) (hi := (101772447 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1502439 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1502439 / 1000000) = 1/(1000000 / 1502439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14194 : Bounds (407089787 / 1000000000) (101772447 / 250000000) (Real.log (1502439 / 1000000)) := by
  have h := reflection_log_14194_neg
  have he : Real.log (1502439 / 1000000) = -Real.log (1000000 / 1502439) := by
    rw [show ((1502439 / 1000000) : ℝ) = ((1000000 / 1502439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14195_neg : (174509279 / 250000000) ≤ -Real.log (497561 / 1000000) ∧
    -Real.log (497561 / 1000000) ≤ (349018559 / 500000000) := by
  have h := checkLog_sound (w := (2439 / 997561)) (n := 12)
    (lo := (305621 / 62500000)) (hi := (4889937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 497561) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 497561) = 1/(497561 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14195 : Bounds (-349018559 / 500000000) (-174509279 / 250000000) (Real.log (497561 / 1000000)) := by
  have h := reflection_log_14195_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14196_neg : (290947329 / 1000000000) ≤ -Real.log (747555051279 / 1000000000000) ∧
    -Real.log (747555051279 / 1000000000000) ≤ (29094733 / 100000000) := by
  have h := checkLog_sound (w := (252444948721 / 1747555051279)) (n := 12)
    (lo := (290947329 / 1000000000)) (hi := (29094733 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 747555051279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 747555051279) = 1/(747555051279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14196 : Bounds (-29094733 / 100000000) (-290947329 / 1000000000) (Real.log (747555051279 / 1000000000000)) := by
  have h := reflection_log_14196_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14197_neg : (286683321 / 1000000000) ≤ -Real.log (12011991 / 16000000) ∧
    -Real.log (12011991 / 16000000) ≤ (143341661 / 500000000) := by
  have h := checkLog_sound (w := (3988009 / 28011991)) (n := 12)
    (lo := (286683321 / 1000000000)) (hi := (143341661 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16000000 / 12011991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16000000 / 12011991) = 1/(12011991 / 16000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14197 : Bounds (-143341661 / 500000000) (-286683321 / 1000000000) (Real.log (12011991 / 16000000)) := by
  have h := reflection_log_14197_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14198_neg : (548306643 / 500000000) ≤ -Real.log (25000000000 / 74850224663) ∧
    -Real.log (25000000000 / 74850224663) ≤ (137076661 / 125000000) := by
  have h := checkLog_sound (w := (24850224663 / 124850224663)) (n := 12)
    (lo := (201733053 / 500000000)) (hi := (403466107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74850224663 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(74850224663 / 50000000000) = 1/(25000000000 / 74850224663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14198 : Bounds (548306643 / 500000000) (137076661 / 125000000) (Real.log (74850224663 / 25000000000)) := by
  have h := reflection_log_14198_neg
  have he : Real.log (74850224663 / 25000000000) = -Real.log (25000000000 / 74850224663) := by
    rw [show ((74850224663 / 25000000000) : ℝ) = ((25000000000 / 74850224663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14199_neg : (1105126903 / 1000000000) ≤ -Real.log (500000000000 / 1509803823049) ∧
    -Real.log (500000000000 / 1509803823049) ≤ (221025381 / 200000000) := by
  have h := checkLog_sound (w := (509803823049 / 2509803823049)) (n := 12)
    (lo := (411979723 / 1000000000)) (hi := (102994931 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1509803823049 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1509803823049 / 1000000000000) = 1/(500000000000 / 1509803823049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14199 : Bounds (1105126903 / 1000000000) (221025381 / 200000000) (Real.log (1509803823049 / 500000000000)) := by
  have h := reflection_log_14199_neg
  have he : Real.log (1509803823049 / 500000000000) = -Real.log (500000000000 / 1509803823049) := by
    rw [show ((1509803823049 / 500000000000) : ℝ) = ((500000000000 / 1509803823049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14200_neg : (629883751 / 250000000) ≤ -Real.log (500000000000 / 6211409395973) ∧
    -Real.log (500000000000 / 6211409395973) ≤ (78735469 / 31250000) := by
  have h := checkLog_sound (w := (2211409395973 / 10211409395973)) (n := 12)
    (lo := (55011683 / 125000000)) (hi := (88018693 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6211409395973 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6211409395973 / 4000000000000) = 1/(500000000000 / 6211409395973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14200 : Bounds (629883751 / 250000000) (78735469 / 31250000) (Real.log (6211409395973 / 500000000000)) := by
  have h := reflection_log_14200_neg
  have he : Real.log (6211409395973 / 500000000000) = -Real.log (500000000000 / 6211409395973) := by
    rw [show ((6211409395973 / 500000000000) : ℝ) = ((500000000000 / 6211409395973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14201_neg : (1270747061 / 500000000) ≤ -Real.log (250000000000 / 3174657534247) ∧
    -Real.log (250000000000 / 3174657534247) ≤ (1270747063 / 500000000) := by
  have h := checkLog_sound (w := (1174657534247 / 5174657534247)) (n := 12)
    (lo := (231026291 / 500000000)) (hi := (462052583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3174657534247 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3174657534247 / 2000000000000) = 1/(250000000000 / 3174657534247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14201 : Bounds (1270747061 / 500000000) (1270747063 / 500000000) (Real.log (3174657534247 / 250000000000)) := by
  have h := reflection_log_14201_neg
  have he : Real.log (3174657534247 / 250000000000) = -Real.log (250000000000 / 3174657534247) := by
    rw [show ((3174657534247 / 250000000000) : ℝ) = ((250000000000 / 3174657534247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14202_neg : (309481141 / 500000000) ≤ -Real.log (1000 / 1857) ∧
    -Real.log (1000 / 1857) ≤ (618962283 / 1000000000) := by
  have h := checkLog_sound (w := (857 / 2857)) (n := 12)
    (lo := (309481141 / 500000000)) (hi := (618962283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1857 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1857 / 1000) = 1/(1000 / 1857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14202 : Bounds (309481141 / 500000000) (618962283 / 1000000000) (Real.log (1857 / 1000)) := by
  have h := reflection_log_14202_neg
  have he : Real.log (1857 / 1000) = -Real.log (1000 / 1857) := by
    rw [show ((1857 / 1000) : ℝ) = ((1000 / 1857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14203_neg : (1944910647 / 1000000000) ≤ -Real.log (143 / 1000) ∧
    -Real.log (143 / 1000) ≤ (38898213 / 20000000) := by
  have h := checkLog_sound (w := (107 / 393)) (n := 12)
    (lo := (558616287 / 1000000000)) (hi := (17456759 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 143) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 143) = 1/(143 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14203 : Bounds (-38898213 / 20000000) (-1944910647 / 1000000000) (Real.log (143 / 1000)) := by
  have h := reflection_log_14203_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14204_neg : (107079 / 125000000) ≤ -Real.log (1000000 / 1000857) ∧
    -Real.log (1000000 / 1000857) ≤ (856633 / 1000000000) := by
  have h := checkLog_sound (w := (857 / 2000857)) (n := 12)
    (lo := (107079 / 125000000)) (hi := (856633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000857 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000857 / 1000000) = 1/(1000000 / 1000857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14204 : Bounds (107079 / 125000000) (856633 / 1000000000) (Real.log (1000857 / 1000000)) := by
  have h := reflection_log_14204_neg
  have he : Real.log (1000857 / 1000000) = -Real.log (1000000 / 1000857) := by
    rw [show ((1000857 / 1000000) : ℝ) = ((1000000 / 1000857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14205_neg : (857367 / 1000000000) ≤ -Real.log (999143 / 1000000) ∧
    -Real.log (999143 / 1000000) ≤ (107171 / 125000000) := by
  have h := checkLog_sound (w := (857 / 1999143)) (n := 12)
    (lo := (857367 / 1000000000)) (hi := (107171 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999143) = 1/(999143 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14205 : Bounds (-107171 / 125000000) (-857367 / 1000000000) (Real.log (999143 / 1000000)) := by
  have h := reflection_log_14205_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14206_neg : (406641083 / 1000000000) ≤ -Real.log (200000 / 300353) ∧
    -Real.log (200000 / 300353) ≤ (101660271 / 250000000) := by
  have h := checkLog_sound (w := (100353 / 500353)) (n := 12)
    (lo := (406641083 / 1000000000)) (hi := (101660271 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300353 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300353 / 200000) = 1/(200000 / 300353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14206 : Bounds (406641083 / 1000000000) (101660271 / 250000000) (Real.log (300353 / 200000)) := by
  have h := reflection_log_14206_neg
  have he : Real.log (300353 / 200000) = -Real.log (200000 / 300353) := by
    rw [show ((300353 / 200000) : ℝ) = ((200000 / 300353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14207_neg : (27867337 / 40000000) ≤ -Real.log (99647 / 200000) ∧
    -Real.log (99647 / 200000) ≤ (696683427 / 1000000000) := by
  have h := checkLog_sound (w := (353 / 199647)) (n := 12)
    (lo := (707249 / 200000000)) (hi := (1768123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99647) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 99647) = 1/(99647 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14207 : Bounds (-696683427 / 1000000000) (-27867337 / 40000000) (Real.log (99647 / 200000)) := by
  have h := reflection_log_14207_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0222 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14208_neg : (408772299 / 1000000000) ≤ -Real.log (1000000 / 1504969) ∧
    -Real.log (1000000 / 1504969) ≤ (4087723 / 10000000) := by
  have h := checkLog_sound (w := (504969 / 2504969)) (n := 12)
    (lo := (408772299 / 1000000000)) (hi := (4087723 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1504969 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1504969 / 1000000) = 1/(1000000 / 1504969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14208 : Bounds (408772299 / 1000000000) (4087723 / 10000000) (Real.log (1504969 / 1000000)) := by
  have h := reflection_log_14208_neg
  have he : Real.log (1504969 / 1000000) = -Real.log (1000000 / 1504969) := by
    rw [show ((1504969 / 1000000) : ℝ) = ((1000000 / 1504969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14209_neg : (703134891 / 1000000000) ≤ -Real.log (495031 / 1000000) ∧
    -Real.log (495031 / 1000000) ≤ (703134893 / 1000000000) := by
  have h := checkLog_sound (w := (4969 / 995031)) (n := 12)
    (lo := (9987711 / 1000000000)) (hi := (78029 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 495031) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 495031) = 1/(495031 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14209 : Bounds (-703134893 / 1000000000) (-703134891 / 1000000000) (Real.log (495031 / 1000000)) := by
  have h := reflection_log_14209_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14210_neg : (9198831 / 31250000) ≤ -Real.log (745006309039 / 1000000000000) ∧
    -Real.log (745006309039 / 1000000000000) ≤ (294362593 / 1000000000) := by
  have h := checkLog_sound (w := (254993690961 / 1745006309039)) (n := 12)
    (lo := (9198831 / 31250000)) (hi := (294362593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 745006309039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 745006309039) = 1/(745006309039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14210 : Bounds (-294362593 / 1000000000) (-9198831 / 31250000) (Real.log (745006309039 / 1000000000000)) := by
  have h := reflection_log_14210_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14211_neg : (145021171 / 500000000) ≤ -Real.log (29929275391 / 40000000000) ∧
    -Real.log (29929275391 / 40000000000) ≤ (290042343 / 1000000000) := by
  have h := checkLog_sound (w := (10070724609 / 69929275391)) (n := 12)
    (lo := (145021171 / 500000000)) (hi := (290042343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 29929275391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 29929275391) = 1/(29929275391 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14211 : Bounds (-290042343 / 1000000000) (-145021171 / 500000000) (Real.log (29929275391 / 40000000000)) := by
  have h := reflection_log_14211_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14212_neg : (275831127 / 250000000) ≤ -Real.log (100000000000 / 301417002017) ∧
    -Real.log (100000000000 / 301417002017) ≤ (110332451 / 100000000) := by
  have h := checkLog_sound (w := (101417002017 / 501417002017)) (n := 12)
    (lo := (25636083 / 62500000)) (hi := (410177329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301417002017 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(301417002017 / 200000000000) = 1/(100000000000 / 301417002017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14212 : Bounds (275831127 / 250000000) (110332451 / 100000000) (Real.log (301417002017 / 100000000000)) := by
  have h := reflection_log_14212_neg
  have he : Real.log (301417002017 / 100000000000) = -Real.log (100000000000 / 301417002017) := by
    rw [show ((301417002017 / 100000000000) : ℝ) = ((100000000000 / 301417002017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14213_neg : (1111907191 / 1000000000) ≤ -Real.log (500000000000 / 1520075510423) ∧
    -Real.log (500000000000 / 1520075510423) ≤ (1111907193 / 1000000000) := by
  have h := checkLog_sound (w := (520075510423 / 2520075510423)) (n := 12)
    (lo := (418760011 / 1000000000)) (hi := (104690003 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1520075510423 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1520075510423 / 1000000000000) = 1/(500000000000 / 1520075510423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14213 : Bounds (1111907191 / 1000000000) (1111907193 / 1000000000) (Real.log (1520075510423 / 500000000000)) := by
  have h := reflection_log_14213_neg
  have he : Real.log (1520075510423 / 500000000000) = -Real.log (500000000000 / 1520075510423) := by
    rw [show ((1520075510423 / 500000000000) : ℝ) = ((500000000000 / 1520075510423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14214_neg : (1270747061 / 500000000) ≤ -Real.log (500000000000 / 6349315068493) ∧
    -Real.log (500000000000 / 6349315068493) ≤ (1270747063 / 500000000) := by
  have h := checkLog_sound (w := (2349315068493 / 10349315068493)) (n := 12)
    (lo := (231026291 / 500000000)) (hi := (462052583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6349315068493 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6349315068493 / 4000000000000) = 1/(500000000000 / 6349315068493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14214 : Bounds (1270747061 / 500000000) (1270747063 / 500000000) (Real.log (6349315068493 / 500000000000)) := by
  have h := reflection_log_14214_neg
  have he : Real.log (6349315068493 / 500000000000) = -Real.log (500000000000 / 6349315068493) := by
    rw [show ((6349315068493 / 500000000000) : ℝ) = ((500000000000 / 6349315068493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14215_neg : (2563872929 / 1000000000) ≤ -Real.log (500000000000 / 6493006993007) ∧
    -Real.log (500000000000 / 6493006993007) ≤ (2563872933 / 1000000000) := by
  have h := checkLog_sound (w := (2493006993007 / 10493006993007)) (n := 12)
    (lo := (484431389 / 1000000000)) (hi := (48443139 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6493006993007 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6493006993007 / 4000000000000) = 1/(500000000000 / 6493006993007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14215 : Bounds (2563872929 / 1000000000) (2563872933 / 1000000000) (Real.log (6493006993007 / 500000000000)) := by
  have h := reflection_log_14215_neg
  have he : Real.log (6493006993007 / 500000000000) = -Real.log (500000000000 / 6493006993007) := by
    rw [show ((6493006993007 / 500000000000) : ℝ) = ((500000000000 / 6493006993007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14216_neg : (620576487 / 1000000000) ≤ -Real.log (50 / 93) ∧
    -Real.log (50 / 93) ≤ (77572061 / 125000000) := by
  have h := checkLog_sound (w := (43 / 143)) (n := 12)
    (lo := (620576487 / 1000000000)) (hi := (77572061 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93 / 50) = 1/(50 / 93) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14216 : Bounds (620576487 / 1000000000) (77572061 / 125000000) (Real.log (93 / 50)) := by
  have h := reflection_log_14216_neg
  have he : Real.log (93 / 50) = -Real.log (50 / 93) := by
    rw [show ((93 / 50) : ℝ) = ((50 / 93) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14217_neg : (393222571 / 200000000) ≤ -Real.log (7 / 50) ∧
    -Real.log (7 / 50) ≤ (983056429 / 500000000) := by
  have h := checkLog_sound (w := (11 / 39)) (n := 12)
    (lo := (115963699 / 200000000)) (hi := (1132458 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 14) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(25 / 14) = 1/(7 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14217 : Bounds (-983056429 / 500000000) (-393222571 / 200000000) (Real.log (7 / 50)) := by
  have h := reflection_log_14217_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14218_neg : (85963 / 100000000) ≤ -Real.log (50000 / 50043) ∧
    -Real.log (50000 / 50043) ≤ (859631 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 100043)) (n := 12)
    (lo := (85963 / 100000000)) (hi := (859631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50043 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50043 / 50000) = 1/(50000 / 50043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14218 : Bounds (85963 / 100000000) (859631 / 1000000000) (Real.log (50043 / 50000)) := by
  have h := reflection_log_14218_neg
  have he : Real.log (50043 / 50000) = -Real.log (50000 / 50043) := by
    rw [show ((50043 / 50000) : ℝ) = ((50000 / 50043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14219_neg : (86037 / 100000000) ≤ -Real.log (49957 / 50000) ∧
    -Real.log (49957 / 50000) ≤ (860371 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 99957)) (n := 12)
    (lo := (86037 / 100000000)) (hi := (860371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 49957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 49957) = 1/(49957 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14219 : Bounds (-860371 / 1000000000) (-86037 / 100000000) (Real.log (49957 / 50000)) := by
  have h := reflection_log_14219_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14220_neg : (408324349 / 1000000000) ≤ -Real.log (200000 / 300859) ∧
    -Real.log (200000 / 300859) ≤ (8166487 / 20000000) := by
  have h := checkLog_sound (w := (100859 / 500859)) (n := 12)
    (lo := (408324349 / 1000000000)) (hi := (8166487 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300859 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300859 / 200000) = 1/(200000 / 300859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14220 : Bounds (408324349 / 1000000000) (8166487 / 20000000) (Real.log (300859 / 200000)) := by
  have h := reflection_log_14220_neg
  have he : Real.log (300859 / 200000) = -Real.log (200000 / 300859) := by
    rw [show ((300859 / 200000) : ℝ) = ((200000 / 300859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14221_neg : (350887143 / 500000000) ≤ -Real.log (99141 / 200000) ∧
    -Real.log (99141 / 200000) ≤ (43860893 / 62500000) := by
  have h := checkLog_sound (w := (859 / 199141)) (n := 12)
    (lo := (4313553 / 500000000)) (hi := (8627107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99141) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 99141) = 1/(99141 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14221 : Bounds (-43860893 / 62500000) (-350887143 / 500000000) (Real.log (99141 / 200000)) := by
  have h := reflection_log_14221_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14222_neg : (25653871 / 62500000) ≤ -Real.log (500000 / 753757) ∧
    -Real.log (500000 / 753757) ≤ (410461937 / 1000000000) := by
  have h := checkLog_sound (w := (253757 / 1253757)) (n := 12)
    (lo := (25653871 / 62500000)) (hi := (410461937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((753757 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(753757 / 500000) = 1/(500000 / 753757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14222 : Bounds (25653871 / 62500000) (410461937 / 1000000000) (Real.log (753757 / 500000)) := by
  have h := reflection_log_14222_neg
  have he : Real.log (753757 / 500000) = -Real.log (500000 / 753757) := by
    rw [show ((753757 / 500000) : ℝ) = ((500000 / 753757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14223_neg : (177072311 / 250000000) ≤ -Real.log (246243 / 500000) ∧
    -Real.log (246243 / 500000) ≤ (354144623 / 500000000) := by
  have h := checkLog_sound (w := (3757 / 496243)) (n := 12)
    (lo := (946379 / 62500000)) (hi := (3028413 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 246243) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 246243) = 1/(246243 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14223 : Bounds (-354144623 / 500000000) (-177072311 / 250000000) (Real.log (246243 / 500000)) := by
  have h := reflection_log_14223_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14224_neg : (74456827 / 250000000) ≤ -Real.log (185607384951 / 250000000000) ∧
    -Real.log (185607384951 / 250000000000) ≤ (297827309 / 1000000000) := by
  have h := checkLog_sound (w := (64392615049 / 435607384951)) (n := 12)
    (lo := (74456827 / 250000000)) (hi := (297827309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 185607384951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 185607384951) = 1/(185607384951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14224 : Bounds (-297827309 / 1000000000) (-74456827 / 250000000) (Real.log (185607384951 / 250000000000)) := by
  have h := reflection_log_14224_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14225_neg : (293449937 / 1000000000) ≤ -Real.log (29827462119 / 40000000000) ∧
    -Real.log (29827462119 / 40000000000) ≤ (146724969 / 500000000) := by
  have h := checkLog_sound (w := (10172537881 / 69827462119)) (n := 12)
    (lo := (293449937 / 1000000000)) (hi := (146724969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 29827462119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 29827462119) = 1/(29827462119 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14225 : Bounds (-146724969 / 500000000) (-293449937 / 1000000000) (Real.log (29827462119 / 40000000000)) := by
  have h := reflection_log_14225_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14226_neg : (277524659 / 250000000) ≤ -Real.log (500000000000 / 1517328854863) ∧
    -Real.log (500000000000 / 1517328854863) ≤ (555049319 / 500000000) := by
  have h := checkLog_sound (w := (517328854863 / 2517328854863)) (n := 12)
    (lo := (13029733 / 31250000)) (hi := (416951457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1517328854863 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1517328854863 / 1000000000000) = 1/(500000000000 / 1517328854863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14226 : Bounds (277524659 / 250000000) (555049319 / 500000000) (Real.log (1517328854863 / 500000000000)) := by
  have h := reflection_log_14226_neg
  have he : Real.log (1517328854863 / 500000000000) = -Real.log (500000000000 / 1517328854863) := by
    rw [show ((1517328854863 / 500000000000) : ℝ) = ((500000000000 / 1517328854863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14227_neg : (1118751181 / 1000000000) ≤ -Real.log (125000000000 / 382628643251) ∧
    -Real.log (125000000000 / 382628643251) ≤ (1118751183 / 1000000000) := by
  have h := checkLog_sound (w := (132628643251 / 632628643251)) (n := 12)
    (lo := (425604001 / 1000000000)) (hi := (212802001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((382628643251 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(382628643251 / 250000000000) = 1/(125000000000 / 382628643251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14227 : Bounds (1118751181 / 1000000000) (1118751183 / 1000000000) (Real.log (382628643251 / 125000000000)) := by
  have h := reflection_log_14227_neg
  have he : Real.log (382628643251 / 125000000000) = -Real.log (125000000000 / 382628643251) := by
    rw [show ((382628643251 / 125000000000) : ℝ) = ((125000000000 / 382628643251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14228_neg : (2563872929 / 1000000000) ≤ -Real.log (250000000000 / 3246503496503) ∧
    -Real.log (250000000000 / 3246503496503) ≤ (2563872933 / 1000000000) := by
  have h := checkLog_sound (w := (1246503496503 / 5246503496503)) (n := 12)
    (lo := (484431389 / 1000000000)) (hi := (48443139 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3246503496503 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3246503496503 / 2000000000000) = 1/(250000000000 / 3246503496503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14228 : Bounds (2563872929 / 1000000000) (2563872933 / 1000000000) (Real.log (3246503496503 / 250000000000)) := by
  have h := reflection_log_14228_neg
  have he : Real.log (3246503496503 / 250000000000) = -Real.log (250000000000 / 3246503496503) := by
    rw [show ((3246503496503 / 250000000000) : ℝ) = ((250000000000 / 3246503496503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14229_neg : (1293344671 / 500000000) ≤ -Real.log (250000000000 / 3321428571429) ∧
    -Real.log (250000000000 / 3321428571429) ≤ (1293344673 / 500000000) := by
  have h := checkLog_sound (w := (1321428571429 / 5321428571429)) (n := 12)
    (lo := (253623901 / 500000000)) (hi := (507247803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3321428571429 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3321428571429 / 2000000000000) = 1/(250000000000 / 3321428571429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14229 : Bounds (1293344671 / 500000000) (1293344673 / 500000000) (Real.log (3321428571429 / 250000000000)) := by
  have h := reflection_log_14229_neg
  have he : Real.log (3321428571429 / 250000000000) = -Real.log (250000000000 / 3321428571429) := by
    rw [show ((3321428571429 / 250000000000) : ℝ) = ((250000000000 / 3321428571429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14230_neg : (622188091 / 1000000000) ≤ -Real.log (1000 / 1863) ∧
    -Real.log (1000 / 1863) ≤ (155547023 / 250000000) := by
  have h := checkLog_sound (w := (863 / 2863)) (n := 12)
    (lo := (622188091 / 1000000000)) (hi := (155547023 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1863 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1863 / 1000) = 1/(1000 / 1863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14230 : Bounds (622188091 / 1000000000) (155547023 / 250000000) (Real.log (1863 / 1000)) := by
  have h := reflection_log_14230_neg
  have he : Real.log (1863 / 1000) = -Real.log (1000 / 1863) := by
    rw [show ((1863 / 1000) : ℝ) = ((1000 / 1863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14231_neg : (124235897 / 62500000) ≤ -Real.log (137 / 1000) ∧
    -Real.log (137 / 1000) ≤ (397554871 / 200000000) := by
  have h := checkLog_sound (w := (113 / 387)) (n := 12)
    (lo := (75184999 / 125000000)) (hi := (601479993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 137) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 137) = 1/(137 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14231 : Bounds (-397554871 / 200000000) (-124235897 / 62500000) (Real.log (137 / 1000)) := by
  have h := reflection_log_14231_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14232_neg : (862627 / 1000000000) ≤ -Real.log (1000000 / 1000863) ∧
    -Real.log (1000000 / 1000863) ≤ (215657 / 250000000) := by
  have h := checkLog_sound (w := (863 / 2000863)) (n := 12)
    (lo := (862627 / 1000000000)) (hi := (215657 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000863 / 1000000) = 1/(1000000 / 1000863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14232 : Bounds (862627 / 1000000000) (215657 / 250000000) (Real.log (1000863 / 1000000)) := by
  have h := reflection_log_14232_neg
  have he : Real.log (1000863 / 1000000) = -Real.log (1000000 / 1000863) := by
    rw [show ((1000863 / 1000000) : ℝ) = ((1000000 / 1000863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14233_neg : (215843 / 250000000) ≤ -Real.log (999137 / 1000000) ∧
    -Real.log (999137 / 1000000) ≤ (863373 / 1000000000) := by
  have h := checkLog_sound (w := (863 / 1999137)) (n := 12)
    (lo := (215843 / 250000000)) (hi := (863373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999137) = 1/(999137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14233 : Bounds (-863373 / 1000000000) (-215843 / 250000000) (Real.log (999137 / 1000000)) := by
  have h := reflection_log_14233_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14234_neg : (205007371 / 500000000) ≤ -Real.log (25000 / 37671) ∧
    -Real.log (25000 / 37671) ≤ (410014743 / 1000000000) := by
  have h := checkLog_sound (w := (12671 / 62671)) (n := 12)
    (lo := (205007371 / 500000000)) (hi := (410014743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37671 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37671 / 25000) = 1/(25000 / 37671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14234 : Bounds (205007371 / 500000000) (410014743 / 1000000000) (Real.log (37671 / 25000)) := by
  have h := reflection_log_14234_neg
  have he : Real.log (37671 / 25000) = -Real.log (25000 / 37671) := by
    rw [show ((37671 / 25000) : ℝ) = ((25000 / 37671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14235_neg : (706921613 / 1000000000) ≤ -Real.log (12329 / 25000) ∧
    -Real.log (12329 / 25000) ≤ (141384323 / 200000000) := by
  have h := checkLog_sound (w := (171 / 24829)) (n := 12)
    (lo := (13774433 / 1000000000)) (hi := (6887217 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 12329) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(12500 / 12329) = 1/(12329 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14235 : Bounds (-141384323 / 200000000) (-706921613 / 1000000000) (Real.log (12329 / 25000)) := by
  have h := reflection_log_14235_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14236_neg : (6439979 / 15625000) ≤ -Real.log (500000 / 755037) ∧
    -Real.log (500000 / 755037) ≤ (412158657 / 1000000000) := by
  have h := checkLog_sound (w := (255037 / 1255037)) (n := 12)
    (lo := (6439979 / 15625000)) (hi := (412158657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((755037 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(755037 / 500000) = 1/(500000 / 755037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14236 : Bounds (6439979 / 15625000) (412158657 / 1000000000) (Real.log (755037 / 500000)) := by
  have h := reflection_log_14236_neg
  have he : Real.log (755037 / 500000) = -Real.log (500000 / 755037) := by
    rw [show ((755037 / 500000) : ℝ) = ((500000 / 755037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14237_neg : (713500919 / 1000000000) ≤ -Real.log (244963 / 500000) ∧
    -Real.log (244963 / 500000) ≤ (713500921 / 1000000000) := by
  have h := checkLog_sound (w := (5037 / 494963)) (n := 12)
    (lo := (20353739 / 1000000000)) (hi := (1017687 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 244963) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 244963) = 1/(244963 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14237 : Bounds (-713500921 / 1000000000) (-713500919 / 1000000000) (Real.log (244963 / 500000)) := by
  have h := reflection_log_14237_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14238_neg : (301342263 / 1000000000) ≤ -Real.log (184956128631 / 250000000000) ∧
    -Real.log (184956128631 / 250000000000) ≤ (37667783 / 125000000) := by
  have h := checkLog_sound (w := (65043871369 / 434956128631)) (n := 12)
    (lo := (301342263 / 1000000000)) (hi := (37667783 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 184956128631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 184956128631) = 1/(184956128631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14238 : Bounds (-37667783 / 125000000) (-301342263 / 1000000000) (Real.log (184956128631 / 250000000000)) := by
  have h := reflection_log_14238_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14239_neg : (296906871 / 1000000000) ≤ -Real.log (464445759 / 625000000) ∧
    -Real.log (464445759 / 625000000) ≤ (37113359 / 125000000) := by
  have h := checkLog_sound (w := (160554241 / 1089445759)) (n := 12)
    (lo := (296906871 / 1000000000)) (hi := (37113359 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 464445759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 464445759) = 1/(464445759 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14239 : Bounds (-37113359 / 125000000) (-296906871 / 1000000000) (Real.log (464445759 / 625000000)) := by
  have h := reflection_log_14239_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14240_neg : (279234089 / 250000000) ≤ -Real.log (7812500000 / 23870929313) ∧
    -Real.log (7812500000 / 23870929313) ≤ (558468179 / 500000000) := by
  have h := checkLog_sound (w := (8245929313 / 39495929313)) (n := 12)
    (lo := (52973647 / 125000000)) (hi := (423789177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23870929313 / 15625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(23870929313 / 15625000000) = 1/(7812500000 / 23870929313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14240 : Bounds (279234089 / 250000000) (558468179 / 500000000) (Real.log (23870929313 / 7812500000)) := by
  have h := reflection_log_14240_neg
  have he : Real.log (23870929313 / 7812500000) = -Real.log (7812500000 / 23870929313) := by
    rw [show ((23870929313 / 7812500000) : ℝ) = ((7812500000 / 23870929313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14241_neg : (45026383 / 40000000) ≤ -Real.log (250000000000 / 770562288999) ∧
    -Real.log (250000000000 / 770562288999) ≤ (1125659577 / 1000000000) := by
  have h := checkLog_sound (w := (270562288999 / 1270562288999)) (n := 12)
    (lo := (86502479 / 200000000)) (hi := (108128099 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((770562288999 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(770562288999 / 500000000000) = 1/(250000000000 / 770562288999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14241 : Bounds (45026383 / 40000000) (1125659577 / 1000000000) (Real.log (770562288999 / 250000000000)) := by
  have h := reflection_log_14241_neg
  have he : Real.log (770562288999 / 250000000000) = -Real.log (250000000000 / 770562288999) := by
    rw [show ((770562288999 / 250000000000) : ℝ) = ((250000000000 / 770562288999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14242_neg : (1293344671 / 500000000) ≤ -Real.log (500000000000 / 6642857142857) ∧
    -Real.log (500000000000 / 6642857142857) ≤ (1293344673 / 500000000) := by
  have h := checkLog_sound (w := (2642857142857 / 10642857142857)) (n := 12)
    (lo := (253623901 / 500000000)) (hi := (507247803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6642857142857 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6642857142857 / 4000000000000) = 1/(500000000000 / 6642857142857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14242 : Bounds (1293344671 / 500000000) (1293344673 / 500000000) (Real.log (6642857142857 / 500000000000)) := by
  have h := reflection_log_14242_neg
  have he : Real.log (6642857142857 / 500000000000) = -Real.log (500000000000 / 6642857142857) := by
    rw [show ((6642857142857 / 500000000000) : ℝ) = ((500000000000 / 6642857142857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14243_neg : (2609962443 / 1000000000) ≤ -Real.log (500000000000 / 6799270072993) ∧
    -Real.log (500000000000 / 6799270072993) ≤ (2609962447 / 1000000000) := by
  have h := checkLog_sound (w := (2799270072993 / 10799270072993)) (n := 12)
    (lo := (530520903 / 1000000000)) (hi := (66315113 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6799270072993 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6799270072993 / 4000000000000) = 1/(500000000000 / 6799270072993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14243 : Bounds (2609962443 / 1000000000) (2609962447 / 1000000000) (Real.log (6799270072993 / 500000000000)) := by
  have h := reflection_log_14243_neg
  have he : Real.log (6799270072993 / 500000000000) = -Real.log (500000000000 / 6799270072993) := by
    rw [show ((6799270072993 / 500000000000) : ℝ) = ((500000000000 / 6799270072993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14244_neg : (311898551 / 500000000) ≤ -Real.log (500 / 933) ∧
    -Real.log (500 / 933) ≤ (623797103 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 1433)) (n := 12)
    (lo := (311898551 / 500000000)) (hi := (623797103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((933 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(933 / 500) = 1/(500 / 933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14244 : Bounds (311898551 / 500000000) (623797103 / 1000000000) (Real.log (933 / 500)) := by
  have h := reflection_log_14244_neg
  have he : Real.log (933 / 500) = -Real.log (500 / 933) := by
    rw [show ((933 / 500) : ℝ) = ((500 / 933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14245_neg : (2009915477 / 1000000000) ≤ -Real.log (67 / 500) ∧
    -Real.log (67 / 500) ≤ (50247887 / 25000000) := by
  have h := checkLog_sound (w := (29 / 96)) (n := 12)
    (lo := (623621117 / 1000000000)) (hi := (311810559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 67) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 67) = 1/(67 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14245 : Bounds (-50247887 / 25000000) (-2009915477 / 1000000000) (Real.log (67 / 500)) := by
  have h := reflection_log_14245_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14246_neg : (277 / 320000) ≤ -Real.log (500000 / 500433) ∧
    -Real.log (500000 / 500433) ≤ (432813 / 500000000) := by
  have h := checkLog_sound (w := (433 / 1000433)) (n := 12)
    (lo := (277 / 320000)) (hi := (432813 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500433 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500433 / 500000) = 1/(500000 / 500433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14246 : Bounds (277 / 320000) (432813 / 500000000) (Real.log (500433 / 500000)) := by
  have h := reflection_log_14246_neg
  have he : Real.log (500433 / 500000) = -Real.log (500000 / 500433) := by
    rw [show ((500433 / 500000) : ℝ) = ((500000 / 500433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14247_neg : (6931 / 8000000) ≤ -Real.log (499567 / 500000) ∧
    -Real.log (499567 / 500000) ≤ (108297 / 125000000) := by
  have h := checkLog_sound (w := (433 / 999567)) (n := 12)
    (lo := (6931 / 8000000)) (hi := (108297 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499567) = 1/(499567 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14247 : Bounds (-108297 / 125000000) (-6931 / 8000000) (Real.log (499567 / 500000)) := by
  have h := reflection_log_14247_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14248_neg : (205855779 / 500000000) ≤ -Real.log (1000000 / 1509399) ∧
    -Real.log (1000000 / 1509399) ≤ (411711559 / 1000000000) := by
  have h := checkLog_sound (w := (509399 / 2509399)) (n := 12)
    (lo := (205855779 / 500000000)) (hi := (411711559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1509399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1509399 / 1000000) = 1/(1000000 / 1509399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14248 : Bounds (205855779 / 500000000) (411711559 / 1000000000) (Real.log (1509399 / 1000000)) := by
  have h := reflection_log_14248_neg
  have he : Real.log (1509399 / 1000000) = -Real.log (1000000 / 1509399) := by
    rw [show ((1509399 / 1000000) : ℝ) = ((1000000 / 1509399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14249_neg : (178031027 / 250000000) ≤ -Real.log (490601 / 1000000) ∧
    -Real.log (490601 / 1000000) ≤ (71212411 / 100000000) := by
  have h := checkLog_sound (w := (9399 / 990601)) (n := 12)
    (lo := (593029 / 31250000)) (hi := (18976929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 490601) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 490601) = 1/(490601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14249 : Bounds (-71212411 / 100000000) (-178031027 / 250000000) (Real.log (490601 / 1000000)) := by
  have h := reflection_log_14249_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14250_neg : (413861757 / 1000000000) ≤ -Real.log (125000 / 189081) ∧
    -Real.log (125000 / 189081) ≤ (206930879 / 500000000) := by
  have h := checkLog_sound (w := (64081 / 314081)) (n := 12)
    (lo := (413861757 / 1000000000)) (hi := (206930879 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189081 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189081 / 125000) = 1/(125000 / 189081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14250 : Bounds (413861757 / 1000000000) (206930879 / 500000000) (Real.log (189081 / 125000)) := by
  have h := reflection_log_14250_neg
  have he : Real.log (189081 / 125000) = -Real.log (125000 / 189081) := by
    rw [show ((189081 / 125000) : ℝ) = ((125000 / 189081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14251_neg : (718768623 / 1000000000) ≤ -Real.log (60919 / 125000) ∧
    -Real.log (60919 / 125000) ≤ (5750149 / 8000000) := by
  have h := checkLog_sound (w := (1581 / 123419)) (n := 12)
    (lo := (25621443 / 1000000000)) (hi := (6405361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 60919) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 60919) = 1/(60919 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14251 : Bounds (-5750149 / 8000000) (-718768623 / 1000000000) (Real.log (60919 / 125000)) := by
  have h := reflection_log_14251_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14252_neg : (304906867 / 1000000000) ≤ -Real.log (11518625439 / 15625000000) ∧
    -Real.log (11518625439 / 15625000000) ≤ (76226717 / 250000000) := by
  have h := checkLog_sound (w := (4106374561 / 27143625439)) (n := 12)
    (lo := (304906867 / 1000000000)) (hi := (76226717 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 11518625439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 11518625439) = 1/(11518625439 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14252 : Bounds (-76226717 / 250000000) (-304906867 / 1000000000) (Real.log (11518625439 / 15625000000)) := by
  have h := reflection_log_14252_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14253_neg : (6008251 / 20000000) ≤ -Real.log (740512658799 / 1000000000000) ∧
    -Real.log (740512658799 / 1000000000000) ≤ (300412551 / 1000000000) := by
  have h := checkLog_sound (w := (259487341201 / 1740512658799)) (n := 12)
    (lo := (6008251 / 20000000)) (hi := (300412551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 740512658799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 740512658799) = 1/(740512658799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14253 : Bounds (-300412551 / 1000000000) (-6008251 / 20000000) (Real.log (740512658799 / 1000000000000)) := by
  have h := reflection_log_14253_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14254_neg : (561917833 / 500000000) ≤ -Real.log (125000000000 / 384579067307) ∧
    -Real.log (125000000000 / 384579067307) ≤ (280958917 / 250000000) := by
  have h := checkLog_sound (w := (134579067307 / 634579067307)) (n := 12)
    (lo := (215344243 / 500000000)) (hi := (430688487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((384579067307 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(384579067307 / 250000000000) = 1/(125000000000 / 384579067307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14254 : Bounds (561917833 / 500000000) (280958917 / 250000000) (Real.log (384579067307 / 125000000000)) := by
  have h := reflection_log_14254_neg
  have he : Real.log (384579067307 / 125000000000) = -Real.log (125000000000 / 384579067307) := by
    rw [show ((384579067307 / 125000000000) : ℝ) = ((125000000000 / 384579067307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14255_neg : (1132630381 / 1000000000) ≤ -Real.log (31250000000 / 96994061787) ∧
    -Real.log (31250000000 / 96994061787) ≤ (1132630383 / 1000000000) := by
  have h := checkLog_sound (w := (34494061787 / 159494061787)) (n := 12)
    (lo := (439483201 / 1000000000)) (hi := (219741601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96994061787 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(96994061787 / 62500000000) = 1/(31250000000 / 96994061787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14255 : Bounds (1132630381 / 1000000000) (1132630383 / 1000000000) (Real.log (96994061787 / 31250000000)) := by
  have h := reflection_log_14255_neg
  have he : Real.log (96994061787 / 31250000000) = -Real.log (31250000000 / 96994061787) := by
    rw [show ((96994061787 / 31250000000) : ℝ) = ((31250000000 / 96994061787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14256_neg : (2609962443 / 1000000000) ≤ -Real.log (15625000000 / 212477189781) ∧
    -Real.log (15625000000 / 212477189781) ≤ (2609962447 / 1000000000) := by
  have h := checkLog_sound (w := (87477189781 / 337477189781)) (n := 12)
    (lo := (530520903 / 1000000000)) (hi := (66315113 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((212477189781 / 125000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(212477189781 / 125000000000) = 1/(15625000000 / 212477189781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14256 : Bounds (2609962443 / 1000000000) (2609962447 / 1000000000) (Real.log (212477189781 / 15625000000)) := by
  have h := reflection_log_14256_neg
  have he : Real.log (212477189781 / 15625000000) = -Real.log (15625000000 / 212477189781) := by
    rw [show ((212477189781 / 15625000000) : ℝ) = ((15625000000 / 212477189781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14257_neg : (2633712579 / 1000000000) ≤ -Real.log (100000000000 / 1392537313433) ∧
    -Real.log (100000000000 / 1392537313433) ≤ (2633712583 / 1000000000) := by
  have h := checkLog_sound (w := (592537313433 / 2192537313433)) (n := 12)
    (lo := (554271039 / 1000000000)) (hi := (1732097 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1392537313433 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1392537313433 / 800000000000) = 1/(100000000000 / 1392537313433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14257 : Bounds (2633712579 / 1000000000) (2633712583 / 1000000000) (Real.log (1392537313433 / 100000000000)) := by
  have h := reflection_log_14257_neg
  have he : Real.log (1392537313433 / 100000000000) = -Real.log (100000000000 / 1392537313433) := by
    rw [show ((1392537313433 / 100000000000) : ℝ) = ((100000000000 / 1392537313433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14258_neg : (78175441 / 125000000) ≤ -Real.log (1000 / 1869) ∧
    -Real.log (1000 / 1869) ≤ (625403529 / 1000000000) := by
  have h := checkLog_sound (w := (869 / 2869)) (n := 12)
    (lo := (78175441 / 125000000)) (hi := (625403529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1869 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1869 / 1000) = 1/(1000 / 1869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14258 : Bounds (78175441 / 125000000) (625403529 / 1000000000) (Real.log (1869 / 1000)) := by
  have h := reflection_log_14258_neg
  have he : Real.log (1869 / 1000) = -Real.log (1000 / 1869) := by
    rw [show ((1869 / 1000) : ℝ) = ((1000 / 1869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14259_neg : (1016278977 / 500000000) ≤ -Real.log (131 / 1000) ∧
    -Real.log (131 / 1000) ≤ (2032557957 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 381)) (n := 12)
    (lo := (323131797 / 500000000)) (hi := (129252719 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 131) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 131) = 1/(131 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14259 : Bounds (-2032557957 / 1000000000) (-1016278977 / 500000000) (Real.log (131 / 1000)) := by
  have h := reflection_log_14259_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14260_neg : (434311 / 500000000) ≤ -Real.log (1000000 / 1000869) ∧
    -Real.log (1000000 / 1000869) ≤ (868623 / 1000000000) := by
  have h := checkLog_sound (w := (869 / 2000869)) (n := 12)
    (lo := (434311 / 500000000)) (hi := (868623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000869 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000869 / 1000000) = 1/(1000000 / 1000869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14260 : Bounds (434311 / 500000000) (868623 / 1000000000) (Real.log (1000869 / 1000000)) := by
  have h := reflection_log_14260_neg
  have he : Real.log (1000869 / 1000000) = -Real.log (1000000 / 1000869) := by
    rw [show ((1000869 / 1000000) : ℝ) = ((1000000 / 1000869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14261_neg : (869377 / 1000000000) ≤ -Real.log (999131 / 1000000) ∧
    -Real.log (999131 / 1000000) ≤ (434689 / 500000000) := by
  have h := checkLog_sound (w := (869 / 1999131)) (n := 12)
    (lo := (869377 / 1000000000)) (hi := (434689 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999131) = 1/(999131 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14261 : Bounds (-434689 / 500000000) (-869377 / 1000000000) (Real.log (999131 / 1000000)) := by
  have h := reflection_log_14261_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14262_neg : (413416081 / 1000000000) ≤ -Real.log (500000 / 755987) ∧
    -Real.log (500000 / 755987) ≤ (206708041 / 500000000) := by
  have h := checkLog_sound (w := (255987 / 1255987)) (n := 12)
    (lo := (413416081 / 1000000000)) (hi := (206708041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((755987 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(755987 / 500000) = 1/(500000 / 755987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14262 : Bounds (413416081 / 1000000000) (206708041 / 500000000) (Real.log (755987 / 500000)) := by
  have h := reflection_log_14262_neg
  have he : Real.log (755987 / 500000) = -Real.log (500000 / 755987) := by
    rw [show ((755987 / 500000) : ℝ) = ((500000 / 755987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14263_neg : (143477319 / 200000000) ≤ -Real.log (244013 / 500000) ∧
    -Real.log (244013 / 500000) ≤ (717386597 / 1000000000) := by
  have h := checkLog_sound (w := (5987 / 494013)) (n := 12)
    (lo := (4847883 / 200000000)) (hi := (3029927 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 244013) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 244013) = 1/(244013 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14263 : Bounds (-717386597 / 1000000000) (-143477319 / 200000000) (Real.log (244013 / 500000)) := by
  have h := reflection_log_14263_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14264_neg : (207786591 / 500000000) ≤ -Real.log (1000000 / 1515239) ∧
    -Real.log (1000000 / 1515239) ≤ (415573183 / 1000000000) := by
  have h := checkLog_sound (w := (515239 / 2515239)) (n := 12)
    (lo := (207786591 / 500000000)) (hi := (415573183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1515239 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1515239 / 1000000) = 1/(1000000 / 1515239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14264 : Bounds (207786591 / 500000000) (415573183 / 1000000000) (Real.log (1515239 / 1000000)) := by
  have h := reflection_log_14264_neg
  have he : Real.log (1515239 / 1000000) = -Real.log (1000000 / 1515239) := by
    rw [show ((1515239 / 1000000) : ℝ) = ((1000000 / 1515239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14265_neg : (181024823 / 250000000) ≤ -Real.log (484761 / 1000000) ∧
    -Real.log (484761 / 1000000) ≤ (362049647 / 500000000) := by
  have h := checkLog_sound (w := (15239 / 984761)) (n := 12)
    (lo := (1934507 / 62500000)) (hi := (30952113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 484761) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 484761) = 1/(484761 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14265 : Bounds (-362049647 / 500000000) (-181024823 / 250000000) (Real.log (484761 / 1000000)) := by
  have h := reflection_log_14265_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14266_neg : (30852611 / 100000000) ≤ -Real.log (734528772879 / 1000000000000) ∧
    -Real.log (734528772879 / 1000000000000) ≤ (308526111 / 1000000000) := by
  have h := checkLog_sound (w := (265471227121 / 1734528772879)) (n := 12)
    (lo := (30852611 / 100000000)) (hi := (308526111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 734528772879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 734528772879) = 1/(734528772879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14266 : Bounds (-308526111 / 1000000000) (-30852611 / 100000000) (Real.log (734528772879 / 1000000000000)) := by
  have h := reflection_log_14266_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14267_neg : (151985257 / 500000000) ≤ -Real.log (184470655831 / 250000000000) ∧
    -Real.log (184470655831 / 250000000000) ≤ (60794103 / 200000000) := by
  have h := checkLog_sound (w := (65529344169 / 434470655831)) (n := 12)
    (lo := (151985257 / 500000000)) (hi := (60794103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 184470655831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 184470655831) = 1/(184470655831 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14267 : Bounds (-60794103 / 200000000) (-151985257 / 500000000) (Real.log (184470655831 / 250000000000)) := by
  have h := reflection_log_14267_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14268_neg : (1130802677 / 1000000000) ≤ -Real.log (125000000000 / 387267789011) ∧
    -Real.log (125000000000 / 387267789011) ≤ (1130802679 / 1000000000) := by
  have h := checkLog_sound (w := (137267789011 / 637267789011)) (n := 12)
    (lo := (437655497 / 1000000000)) (hi := (218827749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387267789011 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(387267789011 / 250000000000) = 1/(125000000000 / 387267789011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14268 : Bounds (1130802677 / 1000000000) (1130802679 / 1000000000) (Real.log (387267789011 / 125000000000)) := by
  have h := reflection_log_14268_neg
  have he : Real.log (387267789011 / 125000000000) = -Real.log (125000000000 / 387267789011) := by
    rw [show ((387267789011 / 125000000000) : ℝ) = ((125000000000 / 387267789011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14269_neg : (569836237 / 500000000) ≤ -Real.log (500000000000 / 1562872219507) ∧
    -Real.log (500000000000 / 1562872219507) ≤ (284918119 / 250000000) := by
  have h := checkLog_sound (w := (562872219507 / 2562872219507)) (n := 12)
    (lo := (223262647 / 500000000)) (hi := (89305059 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1562872219507 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1562872219507 / 1000000000000) = 1/(500000000000 / 1562872219507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14269 : Bounds (569836237 / 500000000) (284918119 / 250000000) (Real.log (1562872219507 / 500000000000)) := by
  have h := reflection_log_14269_neg
  have he : Real.log (1562872219507 / 500000000000) = -Real.log (500000000000 / 1562872219507) := by
    rw [show ((1562872219507 / 500000000000) : ℝ) = ((500000000000 / 1562872219507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14270_neg : (2633712579 / 1000000000) ≤ -Real.log (125000000000 / 1740671641791) ∧
    -Real.log (125000000000 / 1740671641791) ≤ (2633712583 / 1000000000) := by
  have h := checkLog_sound (w := (740671641791 / 2740671641791)) (n := 12)
    (lo := (554271039 / 1000000000)) (hi := (1732097 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1740671641791 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1740671641791 / 1000000000000) = 1/(125000000000 / 1740671641791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14270 : Bounds (2633712579 / 1000000000) (2633712583 / 1000000000) (Real.log (1740671641791 / 125000000000)) := by
  have h := reflection_log_14270_neg
  have he : Real.log (1740671641791 / 125000000000) = -Real.log (125000000000 / 1740671641791) := by
    rw [show ((1740671641791 / 125000000000) : ℝ) = ((125000000000 / 1740671641791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14271_neg : (1328980741 / 500000000) ≤ -Real.log (25000000000 / 356679389313) ∧
    -Real.log (25000000000 / 356679389313) ≤ (1328980743 / 500000000) := by
  have h := checkLog_sound (w := (156679389313 / 556679389313)) (n := 12)
    (lo := (289259971 / 500000000)) (hi := (578519943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((356679389313 / 200000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(356679389313 / 200000000000) = 1/(25000000000 / 356679389313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14271 : Bounds (1328980741 / 500000000) (1328980743 / 500000000) (Real.log (356679389313 / 25000000000)) := by
  have h := reflection_log_14271_neg
  have he : Real.log (356679389313 / 25000000000) = -Real.log (25000000000 / 356679389313) := by
    rw [show ((356679389313 / 25000000000) : ℝ) = ((25000000000 / 356679389313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


