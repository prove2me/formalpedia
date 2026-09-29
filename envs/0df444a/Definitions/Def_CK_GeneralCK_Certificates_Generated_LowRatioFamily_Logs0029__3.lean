-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0029__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0029__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T10:43:37.755667+00:00
-- url     : https://prove2.me/theorems/61cd52ba-8a53-44a8-9b30-109327639a1b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0029 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0030, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0029 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0030, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0031)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0029 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0030, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0031)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0029 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0030, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0031) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0029 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0030, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0031).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0029 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1856_neg : (13182 / 1953125) ≤ -Real.log (39730941591 / 40000000000) ∧
    -Real.log (39730941591 / 40000000000) ≤ (1349837 / 200000000) := by
  have h := checkLog_sound (w := (269058409 / 79730941591)) (n := 12)
    (lo := (13182 / 1953125)) (hi := (1349837 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39730941591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39730941591) = 1/(39730941591 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1856 : Bounds (-1349837 / 200000000) (-13182 / 1953125) (Real.log (39730941591 / 40000000000)) := by
  have h := reflection_log_1856_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1857_neg : (164399271 / 1000000000) ≤ -Real.log (500000000000 / 589342418449) ∧
    -Real.log (500000000000 / 589342418449) ≤ (20549909 / 125000000) := by
  have h := checkLog_sound (w := (89342418449 / 1089342418449)) (n := 12)
    (lo := (164399271 / 1000000000)) (hi := (20549909 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589342418449 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589342418449 / 500000000000) = 1/(500000000000 / 589342418449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1857 : Bounds (164399271 / 1000000000) (20549909 / 125000000) (Real.log (589342418449 / 500000000000)) := by
  have h := reflection_log_1857_neg
  have he : Real.log (589342418449 / 500000000000) = -Real.log (500000000000 / 589342418449) := by
    rw [show ((589342418449 / 500000000000) : ℝ) = ((500000000000 / 589342418449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1858_neg : (164830177 / 1000000000) ≤ -Real.log (500000000000 / 589596424381) ∧
    -Real.log (500000000000 / 589596424381) ≤ (82415089 / 500000000) := by
  have h := checkLog_sound (w := (89596424381 / 1089596424381)) (n := 12)
    (lo := (164830177 / 1000000000)) (hi := (82415089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589596424381 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589596424381 / 500000000000) = 1/(500000000000 / 589596424381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1858 : Bounds (164830177 / 1000000000) (82415089 / 500000000) (Real.log (589596424381 / 500000000000)) := by
  have h := reflection_log_1858_neg
  have he : Real.log (589596424381 / 500000000000) = -Real.log (500000000000 / 589596424381) := by
    rw [show ((589596424381 / 500000000000) : ℝ) = ((500000000000 / 589596424381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1859_neg : (82438993 / 250000000) ≤ -Real.log (250000000000 / 347657183839) ∧
    -Real.log (250000000000 / 347657183839) ≤ (329755973 / 1000000000) := by
  have h := checkLog_sound (w := (97657183839 / 597657183839)) (n := 12)
    (lo := (82438993 / 250000000)) (hi := (329755973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347657183839 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(347657183839 / 250000000000) = 1/(250000000000 / 347657183839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1859 : Bounds (82438993 / 250000000) (329755973 / 1000000000) (Real.log (347657183839 / 250000000000)) := by
  have h := reflection_log_1859_neg
  have he : Real.log (347657183839 / 250000000000) = -Real.log (250000000000 / 347657183839) := by
    rw [show ((347657183839 / 250000000000) : ℝ) = ((250000000000 / 347657183839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1860_neg : (164980731 / 500000000) ≤ -Real.log (500000000000 / 695457262403) ∧
    -Real.log (500000000000 / 695457262403) ≤ (329961463 / 1000000000) := by
  have h := checkLog_sound (w := (195457262403 / 1195457262403)) (n := 12)
    (lo := (164980731 / 500000000)) (hi := (329961463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695457262403 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695457262403 / 500000000000) = 1/(500000000000 / 695457262403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1860 : Bounds (164980731 / 500000000) (329961463 / 1000000000) (Real.log (695457262403 / 500000000000)) := by
  have h := reflection_log_1860_neg
  have he : Real.log (695457262403 / 500000000000) = -Real.log (500000000000 / 695457262403) := by
    rw [show ((695457262403 / 500000000000) : ℝ) = ((500000000000 / 695457262403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1861_neg : (151518647 / 1000000000) ≤ -Real.log (2500 / 2909) ∧
    -Real.log (2500 / 2909) ≤ (18939831 / 125000000) := by
  have h := checkLog_sound (w := (409 / 5409)) (n := 12)
    (lo := (151518647 / 1000000000)) (hi := (18939831 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2909 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2909 / 2500) = 1/(2500 / 2909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1861 : Bounds (151518647 / 1000000000) (18939831 / 125000000) (Real.log (2909 / 2500)) := by
  have h := reflection_log_1861_neg
  have he : Real.log (2909 / 2500) = -Real.log (2500 / 2909) := by
    rw [show ((2909 / 2500) : ℝ) = ((2500 / 2909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1862_neg : (178648311 / 1000000000) ≤ -Real.log (2091 / 2500) ∧
    -Real.log (2091 / 2500) ≤ (22331039 / 125000000) := by
  have h := checkLog_sound (w := (409 / 4591)) (n := 12)
    (lo := (178648311 / 1000000000)) (hi := (22331039 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2091) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2091) = 1/(2091 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1862 : Bounds (-22331039 / 125000000) (-178648311 / 1000000000) (Real.log (2091 / 2500)) := by
  have h := reflection_log_1862_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1863_neg : (81793 / 500000000) ≤ -Real.log (2500000 / 2500409) ∧
    -Real.log (2500000 / 2500409) ≤ (163587 / 1000000000) := by
  have h := checkLog_sound (w := (409 / 5000409)) (n := 12)
    (lo := (81793 / 500000000)) (hi := (163587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500409 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500409 / 2500000) = 1/(2500000 / 2500409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1863 : Bounds (81793 / 500000000) (163587 / 1000000000) (Real.log (2500409 / 2500000)) := by
  have h := reflection_log_1863_neg
  have he : Real.log (2500409 / 2500000) = -Real.log (2500000 / 2500409) := by
    rw [show ((2500409 / 2500000) : ℝ) = ((2500000 / 2500409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1864_neg : (163613 / 1000000000) ≤ -Real.log (2499591 / 2500000) ∧
    -Real.log (2499591 / 2500000) ≤ (81807 / 500000000) := by
  have h := checkLog_sound (w := (409 / 4999591)) (n := 12)
    (lo := (163613 / 1000000000)) (hi := (81807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499591) = 1/(2499591 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1864 : Bounds (-81807 / 500000000) (-163613 / 1000000000) (Real.log (2499591 / 2500000)) := by
  have h := reflection_log_1864_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1865_neg : (19717813 / 250000000) ≤ -Real.log (200000 / 216413) ∧
    -Real.log (200000 / 216413) ≤ (78871253 / 1000000000) := by
  have h := checkLog_sound (w := (16413 / 416413)) (n := 12)
    (lo := (19717813 / 250000000)) (hi := (78871253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216413 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216413 / 200000) = 1/(200000 / 216413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1865 : Bounds (19717813 / 250000000) (78871253 / 1000000000) (Real.log (216413 / 200000)) := by
  have h := reflection_log_1865_neg
  have he : Real.log (216413 / 200000) = -Real.log (200000 / 216413) := by
    rw [show ((216413 / 200000) : ℝ) = ((200000 / 216413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1866_neg : (10703587 / 125000000) ≤ -Real.log (183587 / 200000) ∧
    -Real.log (183587 / 200000) ≤ (85628697 / 1000000000) := by
  have h := checkLog_sound (w := (16413 / 383587)) (n := 12)
    (lo := (10703587 / 125000000)) (hi := (85628697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183587) = 1/(183587 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1866 : Bounds (-85628697 / 1000000000) (-10703587 / 125000000) (Real.log (183587 / 200000)) := by
  have h := reflection_log_1866_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1867_neg : (39534963 / 500000000) ≤ -Real.log (25000 / 27057) ∧
    -Real.log (25000 / 27057) ≤ (79069927 / 1000000000) := by
  have h := checkLog_sound (w := (2057 / 52057)) (n := 12)
    (lo := (39534963 / 500000000)) (hi := (79069927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27057 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27057 / 25000) = 1/(25000 / 27057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1867 : Bounds (39534963 / 500000000) (79069927 / 1000000000) (Real.log (27057 / 25000)) := by
  have h := reflection_log_1867_neg
  have he : Real.log (27057 / 25000) = -Real.log (25000 / 27057) := by
    rw [show ((27057 / 25000) : ℝ) = ((25000 / 27057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1868_neg : (17172589 / 200000000) ≤ -Real.log (22943 / 25000) ∧
    -Real.log (22943 / 25000) ≤ (42931473 / 500000000) := by
  have h := checkLog_sound (w := (2057 / 47943)) (n := 12)
    (lo := (17172589 / 200000000)) (hi := (42931473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 22943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 22943) = 1/(22943 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1868 : Bounds (-42931473 / 500000000) (-17172589 / 200000000) (Real.log (22943 / 25000)) := by
  have h := reflection_log_1868_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1869_neg : (3396509 / 500000000) ≤ -Real.log (620768751 / 625000000) ∧
    -Real.log (620768751 / 625000000) ≤ (6793019 / 1000000000) := by
  have h := checkLog_sound (w := (4231249 / 1245768751)) (n := 12)
    (lo := (3396509 / 500000000)) (hi := (6793019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 620768751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 620768751) = 1/(620768751 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1869 : Bounds (-6793019 / 1000000000) (-3396509 / 500000000) (Real.log (620768751 / 625000000)) := by
  have h := reflection_log_1869_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1870_neg : (1689361 / 250000000) ≤ -Real.log (39730613431 / 40000000000) ∧
    -Real.log (39730613431 / 40000000000) ≤ (1351489 / 200000000) := by
  have h := checkLog_sound (w := (269386569 / 79730613431)) (n := 12)
    (lo := (1689361 / 250000000)) (hi := (1351489 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39730613431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39730613431) = 1/(39730613431 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1870 : Bounds (-1351489 / 200000000) (-1689361 / 250000000) (Real.log (39730613431 / 40000000000)) := by
  have h := reflection_log_1870_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1871_neg : (164499949 / 1000000000) ≤ -Real.log (250000000000 / 294700877513) ∧
    -Real.log (250000000000 / 294700877513) ≤ (3289999 / 20000000) := by
  have h := checkLog_sound (w := (44700877513 / 544700877513)) (n := 12)
    (lo := (164499949 / 1000000000)) (hi := (3289999 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294700877513 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294700877513 / 250000000000) = 1/(250000000000 / 294700877513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1871 : Bounds (164499949 / 1000000000) (3289999 / 20000000) (Real.log (294700877513 / 250000000000)) := by
  have h := reflection_log_1871_neg
  have he : Real.log (294700877513 / 250000000000) = -Real.log (250000000000 / 294700877513) := by
    rw [show ((294700877513 / 250000000000) : ℝ) = ((250000000000 / 294700877513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1872_neg : (20616609 / 125000000) ≤ -Real.log (31250000000 / 36853560999) ∧
    -Real.log (31250000000 / 36853560999) ≤ (164932873 / 1000000000) := by
  have h := checkLog_sound (w := (5603560999 / 68103560999)) (n := 12)
    (lo := (20616609 / 125000000)) (hi := (164932873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36853560999 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36853560999 / 31250000000) = 1/(31250000000 / 36853560999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1872 : Bounds (20616609 / 125000000) (164932873 / 1000000000) (Real.log (36853560999 / 31250000000)) := by
  have h := reflection_log_1872_neg
  have he : Real.log (36853560999 / 31250000000) = -Real.log (31250000000 / 36853560999) := by
    rw [show ((36853560999 / 31250000000) : ℝ) = ((31250000000 / 36853560999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1873_neg : (164980731 / 500000000) ≤ -Real.log (250000000000 / 347728631201) ∧
    -Real.log (250000000000 / 347728631201) ≤ (329961463 / 1000000000) := by
  have h := checkLog_sound (w := (97728631201 / 597728631201)) (n := 12)
    (lo := (164980731 / 500000000)) (hi := (329961463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347728631201 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(347728631201 / 250000000000) = 1/(250000000000 / 347728631201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1873 : Bounds (164980731 / 500000000) (329961463 / 1000000000) (Real.log (347728631201 / 250000000000)) := by
  have h := reflection_log_1873_neg
  have he : Real.log (347728631201 / 250000000000) = -Real.log (250000000000 / 347728631201) := by
    rw [show ((347728631201 / 250000000000) : ℝ) = ((250000000000 / 347728631201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1874_neg : (330166959 / 1000000000) ≤ -Real.log (500000000000 / 695600191297) ∧
    -Real.log (500000000000 / 695600191297) ≤ (4127087 / 12500000) := by
  have h := checkLog_sound (w := (195600191297 / 1195600191297)) (n := 12)
    (lo := (330166959 / 1000000000)) (hi := (4127087 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695600191297 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695600191297 / 500000000000) = 1/(500000000000 / 695600191297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1874 : Bounds (330166959 / 1000000000) (4127087 / 12500000) (Real.log (695600191297 / 500000000000)) := by
  have h := reflection_log_1874_neg
  have he : Real.log (695600191297 / 500000000000) = -Real.log (500000000000 / 695600191297) := by
    rw [show ((695600191297 / 500000000000) : ℝ) = ((500000000000 / 695600191297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1875_neg : (18950573 / 125000000) ≤ -Real.log (10000 / 11637) ∧
    -Real.log (10000 / 11637) ≤ (30320917 / 200000000) := by
  have h := checkLog_sound (w := (1637 / 21637)) (n := 12)
    (lo := (18950573 / 125000000)) (hi := (30320917 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11637 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11637 / 10000) = 1/(10000 / 11637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1875 : Bounds (18950573 / 125000000) (30320917 / 200000000) (Real.log (11637 / 10000)) := by
  have h := reflection_log_1875_neg
  have he : Real.log (11637 / 10000) = -Real.log (10000 / 11637) := by
    rw [show ((11637 / 10000) : ℝ) = ((10000 / 11637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1876_neg : (89383939 / 500000000) ≤ -Real.log (8363 / 10000) ∧
    -Real.log (8363 / 10000) ≤ (178767879 / 1000000000) := by
  have h := checkLog_sound (w := (1637 / 18363)) (n := 12)
    (lo := (89383939 / 500000000)) (hi := (178767879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8363) = 1/(8363 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1876 : Bounds (-178767879 / 1000000000) (-89383939 / 500000000) (Real.log (8363 / 10000)) := by
  have h := reflection_log_1876_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1877_neg : (81843 / 500000000) ≤ -Real.log (10000000 / 10001637) ∧
    -Real.log (10000000 / 10001637) ≤ (163687 / 1000000000) := by
  have h := checkLog_sound (w := (1637 / 20001637)) (n := 12)
    (lo := (81843 / 500000000)) (hi := (163687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001637 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001637 / 10000000) = 1/(10000000 / 10001637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1877 : Bounds (81843 / 500000000) (163687 / 1000000000) (Real.log (10001637 / 10000000)) := by
  have h := reflection_log_1877_neg
  have he : Real.log (10001637 / 10000000) = -Real.log (10000000 / 10001637) := by
    rw [show ((10001637 / 10000000) : ℝ) = ((10000000 / 10001637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1878_neg : (163713 / 1000000000) ≤ -Real.log (9998363 / 10000000) ∧
    -Real.log (9998363 / 10000000) ≤ (81857 / 500000000) := by
  have h := checkLog_sound (w := (1637 / 19998363)) (n := 12)
    (lo := (163713 / 1000000000)) (hi := (81857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998363) = 1/(9998363 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1878 : Bounds (-81857 / 500000000) (-163713 / 1000000000) (Real.log (9998363 / 10000000)) := by
  have h := reflection_log_1878_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1879_neg : (78918383 / 1000000000) ≤ -Real.log (250000 / 270529) ∧
    -Real.log (250000 / 270529) ≤ (4932399 / 62500000) := by
  have h := checkLog_sound (w := (20529 / 520529)) (n := 12)
    (lo := (78918383 / 1000000000)) (hi := (4932399 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270529 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270529 / 250000) = 1/(250000 / 270529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1879 : Bounds (78918383 / 1000000000) (4932399 / 62500000) (Real.log (270529 / 250000)) := by
  have h := reflection_log_1879_neg
  have he : Real.log (270529 / 250000) = -Real.log (250000 / 270529) := by
    rw [show ((270529 / 250000) : ℝ) = ((250000 / 270529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1880_neg : (42842129 / 500000000) ≤ -Real.log (229471 / 250000) ∧
    -Real.log (229471 / 250000) ≤ (85684259 / 1000000000) := by
  have h := checkLog_sound (w := (20529 / 479471)) (n := 12)
    (lo := (42842129 / 500000000)) (hi := (85684259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229471) = 1/(229471 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1880 : Bounds (-85684259 / 1000000000) (-42842129 / 500000000) (Real.log (229471 / 250000)) := by
  have h := reflection_log_1880_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1881_neg : (9889631 / 125000000) ≤ -Real.log (1000000 / 1082331) ∧
    -Real.log (1000000 / 1082331) ≤ (79117049 / 1000000000) := by
  have h := checkLog_sound (w := (82331 / 2082331)) (n := 12)
    (lo := (9889631 / 125000000)) (hi := (79117049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082331 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082331 / 1000000) = 1/(1000000 / 1082331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1881 : Bounds (9889631 / 125000000) (79117049 / 1000000000) (Real.log (1082331 / 1000000)) := by
  have h := reflection_log_1881_neg
  have he : Real.log (1082331 / 1000000) = -Real.log (1000000 / 1082331) := by
    rw [show ((1082331 / 1000000) : ℝ) = ((1000000 / 1082331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1882_neg : (85918519 / 1000000000) ≤ -Real.log (917669 / 1000000) ∧
    -Real.log (917669 / 1000000) ≤ (2147963 / 25000000) := by
  have h := checkLog_sound (w := (82331 / 1917669)) (n := 12)
    (lo := (85918519 / 1000000000)) (hi := (2147963 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917669) = 1/(917669 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1882 : Bounds (-2147963 / 25000000) (-85918519 / 1000000000) (Real.log (917669 / 1000000)) := by
  have h := reflection_log_1882_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1883_neg : (6801471 / 1000000000) ≤ -Real.log (993221606439 / 1000000000000) ∧
    -Real.log (993221606439 / 1000000000000) ≤ (106273 / 15625000) := by
  have h := checkLog_sound (w := (6778393561 / 1993221606439)) (n := 12)
    (lo := (6801471 / 1000000000)) (hi := (106273 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993221606439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993221606439) = 1/(993221606439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1883 : Bounds (-106273 / 15625000) (-6801471 / 1000000000) (Real.log (993221606439 / 1000000000000)) := by
  have h := reflection_log_1883_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1884_neg : (3382937 / 500000000) ≤ -Real.log (62078560159 / 62500000000) ∧
    -Real.log (62078560159 / 62500000000) ≤ (54127 / 8000000) := by
  have h := checkLog_sound (w := (421439841 / 124578560159)) (n := 12)
    (lo := (3382937 / 500000000)) (hi := (54127 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62078560159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62078560159) = 1/(62078560159 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1884 : Bounds (-54127 / 8000000) (-3382937 / 500000000) (Real.log (62078560159 / 62500000000)) := by
  have h := reflection_log_1884_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1885_neg : (164602641 / 1000000000) ≤ -Real.log (250000000000 / 294731142497) ∧
    -Real.log (250000000000 / 294731142497) ≤ (82301321 / 500000000) := by
  have h := checkLog_sound (w := (44731142497 / 544731142497)) (n := 12)
    (lo := (164602641 / 1000000000)) (hi := (82301321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294731142497 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294731142497 / 250000000000) = 1/(250000000000 / 294731142497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1885 : Bounds (164602641 / 1000000000) (82301321 / 500000000) (Real.log (294731142497 / 250000000000)) := by
  have h := reflection_log_1885_neg
  have he : Real.log (294731142497 / 250000000000) = -Real.log (250000000000 / 294731142497) := by
    rw [show ((294731142497 / 250000000000) : ℝ) = ((250000000000 / 294731142497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1886_neg : (10314723 / 62500000) ≤ -Real.log (250000000000 / 294858767159) ∧
    -Real.log (250000000000 / 294858767159) ≤ (165035569 / 1000000000) := by
  have h := checkLog_sound (w := (44858767159 / 544858767159)) (n := 12)
    (lo := (10314723 / 62500000)) (hi := (165035569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294858767159 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294858767159 / 250000000000) = 1/(250000000000 / 294858767159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1886 : Bounds (10314723 / 62500000) (165035569 / 1000000000) (Real.log (294858767159 / 250000000000)) := by
  have h := reflection_log_1886_neg
  have he : Real.log (294858767159 / 250000000000) = -Real.log (250000000000 / 294858767159) := by
    rw [show ((294858767159 / 250000000000) : ℝ) = ((250000000000 / 294858767159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1887_neg : (330166959 / 1000000000) ≤ -Real.log (7812500000 / 10868752989) ∧
    -Real.log (7812500000 / 10868752989) ≤ (4127087 / 12500000) := by
  have h := checkLog_sound (w := (3056252989 / 18681252989)) (n := 12)
    (lo := (330166959 / 1000000000)) (hi := (4127087 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10868752989 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10868752989 / 7812500000) = 1/(7812500000 / 10868752989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1887 : Bounds (330166959 / 1000000000) (4127087 / 12500000) (Real.log (10868752989 / 7812500000)) := by
  have h := reflection_log_1887_neg
  have he : Real.log (10868752989 / 7812500000) = -Real.log (7812500000 / 10868752989) := by
    rw [show ((10868752989 / 7812500000) : ℝ) = ((7812500000 / 10868752989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1888_neg : (165186231 / 500000000) ≤ -Real.log (500000000000 / 695743154371) ∧
    -Real.log (500000000000 / 695743154371) ≤ (330372463 / 1000000000) := by
  have h := checkLog_sound (w := (195743154371 / 1195743154371)) (n := 12)
    (lo := (165186231 / 500000000)) (hi := (330372463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695743154371 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695743154371 / 500000000000) = 1/(500000000000 / 695743154371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1888 : Bounds (165186231 / 500000000) (330372463 / 1000000000) (Real.log (695743154371 / 500000000000)) := by
  have h := reflection_log_1888_neg
  have he : Real.log (695743154371 / 500000000000) = -Real.log (500000000000 / 695743154371) := by
    rw [show ((695743154371 / 500000000000) : ℝ) = ((500000000000 / 695743154371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1889_neg : (151690513 / 1000000000) ≤ -Real.log (5000 / 5819) ∧
    -Real.log (5000 / 5819) ≤ (75845257 / 500000000) := by
  have h := checkLog_sound (w := (819 / 10819)) (n := 12)
    (lo := (151690513 / 1000000000)) (hi := (75845257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5819 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5819 / 5000) = 1/(5000 / 5819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1889 : Bounds (151690513 / 1000000000) (75845257 / 500000000) (Real.log (5819 / 5000)) := by
  have h := reflection_log_1889_neg
  have he : Real.log (5819 / 5000) = -Real.log (5000 / 5819) := by
    rw [show ((5819 / 5000) : ℝ) = ((5000 / 5819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1890_neg : (8944373 / 50000000) ≤ -Real.log (4181 / 5000) ∧
    -Real.log (4181 / 5000) ≤ (178887461 / 1000000000) := by
  have h := checkLog_sound (w := (819 / 9181)) (n := 12)
    (lo := (8944373 / 50000000)) (hi := (178887461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4181) = 1/(4181 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1890 : Bounds (-178887461 / 1000000000) (-8944373 / 50000000) (Real.log (4181 / 5000)) := by
  have h := reflection_log_1890_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1891_neg : (81893 / 500000000) ≤ -Real.log (5000000 / 5000819) ∧
    -Real.log (5000000 / 5000819) ≤ (163787 / 1000000000) := by
  have h := checkLog_sound (w := (819 / 10000819)) (n := 12)
    (lo := (81893 / 500000000)) (hi := (163787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000819 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000819 / 5000000) = 1/(5000000 / 5000819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1891 : Bounds (81893 / 500000000) (163787 / 1000000000) (Real.log (5000819 / 5000000)) := by
  have h := reflection_log_1891_neg
  have he : Real.log (5000819 / 5000000) = -Real.log (5000000 / 5000819) := by
    rw [show ((5000819 / 5000000) : ℝ) = ((5000000 / 5000819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1892_neg : (163813 / 1000000000) ≤ -Real.log (4999181 / 5000000) ∧
    -Real.log (4999181 / 5000000) ≤ (81907 / 500000000) := by
  have h := checkLog_sound (w := (819 / 9999181)) (n := 12)
    (lo := (163813 / 1000000000)) (hi := (81907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999181) = 1/(4999181 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1892 : Bounds (-81907 / 500000000) (-163813 / 1000000000) (Real.log (4999181 / 5000000)) := by
  have h := reflection_log_1892_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1893_neg : (9870689 / 125000000) ≤ -Real.log (1000000 / 1082167) ∧
    -Real.log (1000000 / 1082167) ≤ (78965513 / 1000000000) := by
  have h := checkLog_sound (w := (82167 / 2082167)) (n := 12)
    (lo := (9870689 / 125000000)) (hi := (78965513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082167 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082167 / 1000000) = 1/(1000000 / 1082167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1893 : Bounds (9870689 / 125000000) (78965513 / 1000000000) (Real.log (1082167 / 1000000)) := by
  have h := reflection_log_1893_neg
  have he : Real.log (1082167 / 1000000) = -Real.log (1000000 / 1082167) := by
    rw [show ((1082167 / 1000000) : ℝ) = ((1000000 / 1082167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1894_neg : (42869911 / 500000000) ≤ -Real.log (917833 / 1000000) ∧
    -Real.log (917833 / 1000000) ≤ (85739823 / 1000000000) := by
  have h := checkLog_sound (w := (82167 / 1917833)) (n := 12)
    (lo := (42869911 / 500000000)) (hi := (85739823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917833) = 1/(917833 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1894 : Bounds (-85739823 / 1000000000) (-42869911 / 500000000) (Real.log (917833 / 1000000)) := by
  have h := reflection_log_1894_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1895_neg : (19790811 / 250000000) ≤ -Real.log (1000000 / 1082381) ∧
    -Real.log (1000000 / 1082381) ≤ (15832649 / 200000000) := by
  have h := checkLog_sound (w := (82381 / 2082381)) (n := 12)
    (lo := (19790811 / 250000000)) (hi := (15832649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082381 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082381 / 1000000) = 1/(1000000 / 1082381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1895 : Bounds (19790811 / 250000000) (15832649 / 200000000) (Real.log (1082381 / 1000000)) := by
  have h := reflection_log_1895_neg
  have he : Real.log (1082381 / 1000000) = -Real.log (1000000 / 1082381) := by
    rw [show ((1082381 / 1000000) : ℝ) = ((1000000 / 1082381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1896_neg : (85973007 / 1000000000) ≤ -Real.log (917619 / 1000000) ∧
    -Real.log (917619 / 1000000) ≤ (5373313 / 62500000) := by
  have h := checkLog_sound (w := (82381 / 1917619)) (n := 12)
    (lo := (85973007 / 1000000000)) (hi := (5373313 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917619) = 1/(917619 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1896 : Bounds (-5373313 / 62500000) (-85973007 / 1000000000) (Real.log (917619 / 1000000)) := by
  have h := reflection_log_1896_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1897_neg : (6809763 / 1000000000) ≤ -Real.log (993213370839 / 1000000000000) ∧
    -Real.log (993213370839 / 1000000000000) ≤ (1702441 / 250000000) := by
  have h := checkLog_sound (w := (6786629161 / 1993213370839)) (n := 12)
    (lo := (6809763 / 1000000000)) (hi := (1702441 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993213370839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993213370839) = 1/(993213370839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1897 : Bounds (-1702441 / 250000000) (-6809763 / 1000000000) (Real.log (993213370839 / 1000000000000)) := by
  have h := reflection_log_1897_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1898_neg : (6774309 / 1000000000) ≤ -Real.log (993248584111 / 1000000000000) ∧
    -Real.log (993248584111 / 1000000000000) ≤ (677431 / 100000000) := by
  have h := checkLog_sound (w := (6751415889 / 1993248584111)) (n := 12)
    (lo := (6774309 / 1000000000)) (hi := (677431 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993248584111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993248584111) = 1/(993248584111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1898 : Bounds (-677431 / 100000000) (-6774309 / 1000000000) (Real.log (993248584111 / 1000000000000)) := by
  have h := reflection_log_1898_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1899_neg : (82352667 / 500000000) ≤ -Real.log (500000000000 / 589522821689) ∧
    -Real.log (500000000000 / 589522821689) ≤ (32941067 / 200000000) := by
  have h := checkLog_sound (w := (89522821689 / 1089522821689)) (n := 12)
    (lo := (82352667 / 500000000)) (hi := (32941067 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589522821689 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589522821689 / 500000000000) = 1/(500000000000 / 589522821689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1899 : Bounds (82352667 / 500000000) (32941067 / 200000000) (Real.log (589522821689 / 500000000000)) := by
  have h := reflection_log_1899_neg
  have he : Real.log (589522821689 / 500000000000) = -Real.log (500000000000 / 589522821689) := by
    rw [show ((589522821689 / 500000000000) : ℝ) = ((500000000000 / 589522821689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1900_neg : (165136251 / 1000000000) ≤ -Real.log (500000000000 / 589776911769) ∧
    -Real.log (500000000000 / 589776911769) ≤ (41284063 / 250000000) := by
  have h := checkLog_sound (w := (89776911769 / 1089776911769)) (n := 12)
    (lo := (165136251 / 1000000000)) (hi := (41284063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589776911769 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589776911769 / 500000000000) = 1/(500000000000 / 589776911769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1900 : Bounds (165136251 / 1000000000) (41284063 / 250000000) (Real.log (589776911769 / 500000000000)) := by
  have h := reflection_log_1900_neg
  have he : Real.log (589776911769 / 500000000000) = -Real.log (500000000000 / 589776911769) := by
    rw [show ((589776911769 / 500000000000) : ℝ) = ((500000000000 / 589776911769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1901_neg : (165186231 / 500000000) ≤ -Real.log (50000000000 / 69574315437) ∧
    -Real.log (50000000000 / 69574315437) ≤ (330372463 / 1000000000) := by
  have h := checkLog_sound (w := (19574315437 / 119574315437)) (n := 12)
    (lo := (165186231 / 500000000)) (hi := (330372463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69574315437 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69574315437 / 50000000000) = 1/(50000000000 / 69574315437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1901 : Bounds (165186231 / 500000000) (330372463 / 1000000000) (Real.log (69574315437 / 50000000000)) := by
  have h := reflection_log_1901_neg
  have he : Real.log (69574315437 / 50000000000) = -Real.log (50000000000 / 69574315437) := by
    rw [show ((69574315437 / 50000000000) : ℝ) = ((50000000000 / 69574315437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1902_neg : (330577973 / 1000000000) ≤ -Real.log (500000000000 / 695886151639) ∧
    -Real.log (500000000000 / 695886151639) ≤ (165288987 / 500000000) := by
  have h := checkLog_sound (w := (195886151639 / 1195886151639)) (n := 12)
    (lo := (330577973 / 1000000000)) (hi := (165288987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695886151639 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695886151639 / 500000000000) = 1/(500000000000 / 695886151639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1902 : Bounds (330577973 / 1000000000) (165288987 / 500000000) (Real.log (695886151639 / 500000000000)) := by
  have h := reflection_log_1902_neg
  have he : Real.log (695886151639 / 500000000000) = -Real.log (500000000000 / 695886151639) := by
    rw [show ((695886151639 / 500000000000) : ℝ) = ((500000000000 / 695886151639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1903_neg : (75888217 / 500000000) ≤ -Real.log (10000 / 11639) ∧
    -Real.log (10000 / 11639) ≤ (30355287 / 200000000) := by
  have h := checkLog_sound (w := (1639 / 21639)) (n := 12)
    (lo := (75888217 / 500000000)) (hi := (30355287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11639 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11639 / 10000) = 1/(10000 / 11639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1903 : Bounds (75888217 / 500000000) (30355287 / 200000000) (Real.log (11639 / 10000)) := by
  have h := reflection_log_1903_neg
  have he : Real.log (11639 / 10000) = -Real.log (10000 / 11639) := by
    rw [show ((11639 / 10000) : ℝ) = ((10000 / 11639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1904_neg : (35801411 / 200000000) ≤ -Real.log (8361 / 10000) ∧
    -Real.log (8361 / 10000) ≤ (11187941 / 62500000) := by
  have h := checkLog_sound (w := (1639 / 18361)) (n := 12)
    (lo := (35801411 / 200000000)) (hi := (11187941 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8361) = 1/(8361 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1904 : Bounds (-11187941 / 62500000) (-35801411 / 200000000) (Real.log (8361 / 10000)) := by
  have h := reflection_log_1904_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1905_neg : (81943 / 500000000) ≤ -Real.log (10000000 / 10001639) ∧
    -Real.log (10000000 / 10001639) ≤ (163887 / 1000000000) := by
  have h := checkLog_sound (w := (1639 / 20001639)) (n := 12)
    (lo := (81943 / 500000000)) (hi := (163887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001639 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001639 / 10000000) = 1/(10000000 / 10001639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1905 : Bounds (81943 / 500000000) (163887 / 1000000000) (Real.log (10001639 / 10000000)) := by
  have h := reflection_log_1905_neg
  have he : Real.log (10001639 / 10000000) = -Real.log (10000000 / 10001639) := by
    rw [show ((10001639 / 10000000) : ℝ) = ((10000000 / 10001639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1906_neg : (163913 / 1000000000) ≤ -Real.log (9998361 / 10000000) ∧
    -Real.log (9998361 / 10000000) ≤ (81957 / 500000000) := by
  have h := checkLog_sound (w := (1639 / 19998361)) (n := 12)
    (lo := (163913 / 1000000000)) (hi := (81957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998361) = 1/(9998361 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1906 : Bounds (-81957 / 500000000) (-163913 / 1000000000) (Real.log (9998361 / 10000000)) := by
  have h := reflection_log_1906_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1907_neg : (39505857 / 500000000) ≤ -Real.log (1000000 / 1082217) ∧
    -Real.log (1000000 / 1082217) ≤ (15802343 / 200000000) := by
  have h := checkLog_sound (w := (82217 / 2082217)) (n := 12)
    (lo := (39505857 / 500000000)) (hi := (15802343 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082217 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082217 / 1000000) = 1/(1000000 / 1082217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1907 : Bounds (39505857 / 500000000) (15802343 / 200000000) (Real.log (1082217 / 1000000)) := by
  have h := reflection_log_1907_neg
  have he : Real.log (1082217 / 1000000) = -Real.log (1000000 / 1082217) := by
    rw [show ((1082217 / 1000000) : ℝ) = ((1000000 / 1082217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1908_neg : (85794299 / 1000000000) ≤ -Real.log (917783 / 1000000) ∧
    -Real.log (917783 / 1000000) ≤ (857943 / 10000000) := by
  have h := checkLog_sound (w := (82217 / 1917783)) (n := 12)
    (lo := (85794299 / 1000000000)) (hi := (857943 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917783) = 1/(917783 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1908 : Bounds (-857943 / 10000000) (-85794299 / 1000000000) (Real.log (917783 / 1000000)) := by
  have h := reflection_log_1908_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1909_neg : (79210361 / 1000000000) ≤ -Real.log (15625 / 16913) ∧
    -Real.log (15625 / 16913) ≤ (39605181 / 500000000) := by
  have h := checkLog_sound (w := (644 / 16269)) (n := 12)
    (lo := (79210361 / 1000000000)) (hi := (39605181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16913 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16913 / 15625) = 1/(15625 / 16913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1909 : Bounds (79210361 / 1000000000) (39605181 / 500000000) (Real.log (16913 / 15625)) := by
  have h := reflection_log_1909_neg
  have he : Real.log (16913 / 15625) = -Real.log (15625 / 16913) := by
    rw [show ((16913 / 15625) : ℝ) = ((15625 / 16913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1910_neg : (86028587 / 1000000000) ≤ -Real.log (14337 / 15625) ∧
    -Real.log (14337 / 15625) ≤ (21507147 / 250000000) := by
  have h := checkLog_sound (w := (644 / 14981)) (n := 12)
    (lo := (86028587 / 1000000000)) (hi := (21507147 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 14337) = 1/(14337 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1910 : Bounds (-21507147 / 250000000) (-86028587 / 1000000000) (Real.log (14337 / 15625)) := by
  have h := reflection_log_1910_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1911_neg : (272729 / 40000000) ≤ -Real.log (242481681 / 244140625) ∧
    -Real.log (242481681 / 244140625) ≤ (3409113 / 500000000) := by
  have h := checkLog_sound (w := (829472 / 243311153)) (n := 12)
    (lo := (272729 / 40000000)) (hi := (3409113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 242481681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 242481681) = 1/(242481681 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1911 : Bounds (-3409113 / 500000000) (-272729 / 40000000) (Real.log (242481681 / 244140625)) := by
  have h := reflection_log_1911_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1912_neg : (847823 / 125000000) ≤ -Real.log (993240364911 / 1000000000000) ∧
    -Real.log (993240364911 / 1000000000000) ≤ (1356517 / 200000000) := by
  have h := checkLog_sound (w := (6759635089 / 1993240364911)) (n := 12)
    (lo := (847823 / 125000000)) (hi := (1356517 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993240364911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993240364911) = 1/(993240364911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1912 : Bounds (-1356517 / 200000000) (-847823 / 125000000) (Real.log (993240364911 / 1000000000000)) := by
  have h := reflection_log_1912_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1913_neg : (82403007 / 500000000) ≤ -Real.log (250000000000 / 294791088961) ∧
    -Real.log (250000000000 / 294791088961) ≤ (32961203 / 200000000) := by
  have h := checkLog_sound (w := (44791088961 / 544791088961)) (n := 12)
    (lo := (82403007 / 500000000)) (hi := (32961203 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294791088961 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294791088961 / 250000000000) = 1/(250000000000 / 294791088961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1913 : Bounds (82403007 / 500000000) (32961203 / 200000000) (Real.log (294791088961 / 250000000000)) := by
  have h := reflection_log_1913_neg
  have he : Real.log (294791088961 / 250000000000) = -Real.log (250000000000 / 294791088961) := by
    rw [show ((294791088961 / 250000000000) : ℝ) = ((250000000000 / 294791088961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1914_neg : (41309737 / 250000000) ≤ -Real.log (100000000000 / 117967496687) ∧
    -Real.log (100000000000 / 117967496687) ≤ (165238949 / 1000000000) := by
  have h := checkLog_sound (w := (17967496687 / 217967496687)) (n := 12)
    (lo := (41309737 / 250000000)) (hi := (165238949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117967496687 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117967496687 / 100000000000) = 1/(100000000000 / 117967496687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1914 : Bounds (41309737 / 250000000) (165238949 / 1000000000) (Real.log (117967496687 / 100000000000)) := by
  have h := reflection_log_1914_neg
  have he : Real.log (117967496687 / 100000000000) = -Real.log (100000000000 / 117967496687) := by
    rw [show ((117967496687 / 100000000000) : ℝ) = ((100000000000 / 117967496687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1915_neg : (330577973 / 1000000000) ≤ -Real.log (250000000000 / 347943075819) ∧
    -Real.log (250000000000 / 347943075819) ≤ (165288987 / 500000000) := by
  have h := checkLog_sound (w := (97943075819 / 597943075819)) (n := 12)
    (lo := (330577973 / 1000000000)) (hi := (165288987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347943075819 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(347943075819 / 250000000000) = 1/(250000000000 / 347943075819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1915 : Bounds (330577973 / 1000000000) (165288987 / 500000000) (Real.log (347943075819 / 250000000000)) := by
  have h := reflection_log_1915_neg
  have he : Real.log (347943075819 / 250000000000) = -Real.log (250000000000 / 347943075819) := by
    rw [show ((347943075819 / 250000000000) : ℝ) = ((250000000000 / 347943075819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1916_neg : (33078349 / 100000000) ≤ -Real.log (500000000000 / 696029183113) ∧
    -Real.log (500000000000 / 696029183113) ≤ (330783491 / 1000000000) := by
  have h := checkLog_sound (w := (196029183113 / 1196029183113)) (n := 12)
    (lo := (33078349 / 100000000)) (hi := (330783491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696029183113 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696029183113 / 500000000000) = 1/(500000000000 / 696029183113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1916 : Bounds (33078349 / 100000000) (330783491 / 1000000000) (Real.log (696029183113 / 500000000000)) := by
  have h := reflection_log_1916_neg
  have he : Real.log (696029183113 / 500000000000) = -Real.log (500000000000 / 696029183113) := by
    rw [show ((696029183113 / 500000000000) : ℝ) = ((500000000000 / 696029183113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1917_neg : (151862349 / 1000000000) ≤ -Real.log (250 / 291) ∧
    -Real.log (250 / 291) ≤ (3037247 / 20000000) := by
  have h := checkLog_sound (w := (41 / 541)) (n := 12)
    (lo := (151862349 / 1000000000)) (hi := (3037247 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291 / 250) = 1/(250 / 291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1917 : Bounds (151862349 / 1000000000) (3037247 / 20000000) (Real.log (291 / 250)) := by
  have h := reflection_log_1917_neg
  have he : Real.log (291 / 250) = -Real.log (250 / 291) := by
    rw [show ((291 / 250) : ℝ) = ((250 / 291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1918_neg : (35825333 / 200000000) ≤ -Real.log (209 / 250) ∧
    -Real.log (209 / 250) ≤ (89563333 / 500000000) := by
  have h := checkLog_sound (w := (41 / 459)) (n := 12)
    (lo := (35825333 / 200000000)) (hi := (89563333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 209) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 209) = 1/(209 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1918 : Bounds (-89563333 / 500000000) (-35825333 / 200000000) (Real.log (209 / 250)) := by
  have h := reflection_log_1918_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1919_neg : (81993 / 500000000) ≤ -Real.log (250000 / 250041) ∧
    -Real.log (250000 / 250041) ≤ (163987 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 500041)) (n := 12)
    (lo := (81993 / 500000000)) (hi := (163987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250041 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250041 / 250000) = 1/(250000 / 250041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1919 : Bounds (81993 / 500000000) (163987 / 1000000000) (Real.log (250041 / 250000)) := by
  have h := reflection_log_1919_neg
  have he : Real.log (250041 / 250000) = -Real.log (250000 / 250041) := by
    rw [show ((250041 / 250000) : ℝ) = ((250000 / 250041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0030 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1920_neg : (164013 / 1000000000) ≤ -Real.log (249959 / 250000) ∧
    -Real.log (249959 / 250000) ≤ (82007 / 500000000) := by
  have h := checkLog_sound (w := (41 / 499959)) (n := 12)
    (lo := (164013 / 1000000000)) (hi := (82007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249959) = 1/(249959 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1920 : Bounds (-82007 / 500000000) (-164013 / 1000000000) (Real.log (249959 / 250000)) := by
  have h := reflection_log_1920_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1921_neg : (79058839 / 1000000000) ≤ -Real.log (250000 / 270567) ∧
    -Real.log (250000 / 270567) ≤ (1976471 / 25000000) := by
  have h := checkLog_sound (w := (20567 / 520567)) (n := 12)
    (lo := (79058839 / 1000000000)) (hi := (1976471 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270567 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270567 / 250000) = 1/(250000 / 270567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1921 : Bounds (79058839 / 1000000000) (1976471 / 25000000) (Real.log (270567 / 250000)) := by
  have h := reflection_log_1921_neg
  have he : Real.log (270567 / 250000) = -Real.log (250000 / 270567) := by
    rw [show ((270567 / 250000) : ℝ) = ((250000 / 270567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1922_neg : (85849869 / 1000000000) ≤ -Real.log (229433 / 250000) ∧
    -Real.log (229433 / 250000) ≤ (8584987 / 100000000) := by
  have h := checkLog_sound (w := (20567 / 479433)) (n := 12)
    (lo := (85849869 / 1000000000)) (hi := (8584987 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229433) = 1/(229433 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1922 : Bounds (-8584987 / 100000000) (-85849869 / 1000000000) (Real.log (229433 / 250000)) := by
  have h := reflection_log_1922_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1923_neg : (19814369 / 250000000) ≤ -Real.log (1000000 / 1082483) ∧
    -Real.log (1000000 / 1082483) ≤ (79257477 / 1000000000) := by
  have h := checkLog_sound (w := (82483 / 2082483)) (n := 12)
    (lo := (19814369 / 250000000)) (hi := (79257477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082483 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082483 / 1000000) = 1/(1000000 / 1082483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1923 : Bounds (19814369 / 250000000) (79257477 / 1000000000) (Real.log (1082483 / 1000000)) := by
  have h := reflection_log_1923_neg
  have he : Real.log (1082483 / 1000000) = -Real.log (1000000 / 1082483) := by
    rw [show ((1082483 / 1000000) : ℝ) = ((1000000 / 1082483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1924_neg : (8608417 / 100000000) ≤ -Real.log (917517 / 1000000) ∧
    -Real.log (917517 / 1000000) ≤ (86084171 / 1000000000) := by
  have h := checkLog_sound (w := (82483 / 1917517)) (n := 12)
    (lo := (8608417 / 100000000)) (hi := (86084171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917517) = 1/(917517 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1924 : Bounds (-86084171 / 1000000000) (-8608417 / 100000000) (Real.log (917517 / 1000000)) := by
  have h := reflection_log_1924_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1925_neg : (3413347 / 500000000) ≤ -Real.log (993196554711 / 1000000000000) ∧
    -Real.log (993196554711 / 1000000000000) ≤ (1365339 / 200000000) := by
  have h := checkLog_sound (w := (6803445289 / 1993196554711)) (n := 12)
    (lo := (3413347 / 500000000)) (hi := (1365339 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993196554711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993196554711) = 1/(993196554711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1925 : Bounds (-1365339 / 200000000) (-3413347 / 500000000) (Real.log (993196554711 / 1000000000000)) := by
  have h := reflection_log_1925_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1926_neg : (679103 / 100000000) ≤ -Real.log (62076998511 / 62500000000) ∧
    -Real.log (62076998511 / 62500000000) ≤ (6791031 / 1000000000) := by
  have h := checkLog_sound (w := (423001489 / 124576998511)) (n := 12)
    (lo := (679103 / 100000000)) (hi := (6791031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62076998511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62076998511) = 1/(62076998511 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1926 : Bounds (-6791031 / 1000000000) (-679103 / 100000000) (Real.log (62076998511 / 62500000000)) := by
  have h := reflection_log_1926_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1927_neg : (164908709 / 1000000000) ≤ -Real.log (250000000000 / 294821363971) ∧
    -Real.log (250000000000 / 294821363971) ≤ (16490871 / 100000000) := by
  have h := checkLog_sound (w := (44821363971 / 544821363971)) (n := 12)
    (lo := (164908709 / 1000000000)) (hi := (16490871 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294821363971 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294821363971 / 250000000000) = 1/(250000000000 / 294821363971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1927 : Bounds (164908709 / 1000000000) (16490871 / 100000000) (Real.log (294821363971 / 250000000000)) := by
  have h := reflection_log_1927_neg
  have he : Real.log (294821363971 / 250000000000) = -Real.log (250000000000 / 294821363971) := by
    rw [show ((294821363971 / 250000000000) : ℝ) = ((250000000000 / 294821363971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1928_neg : (82670823 / 500000000) ≤ -Real.log (100000000000 / 117979612367) ∧
    -Real.log (100000000000 / 117979612367) ≤ (165341647 / 1000000000) := by
  have h := checkLog_sound (w := (17979612367 / 217979612367)) (n := 12)
    (lo := (82670823 / 500000000)) (hi := (165341647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117979612367 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117979612367 / 100000000000) = 1/(100000000000 / 117979612367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1928 : Bounds (82670823 / 500000000) (165341647 / 1000000000) (Real.log (117979612367 / 100000000000)) := by
  have h := reflection_log_1928_neg
  have he : Real.log (117979612367 / 100000000000) = -Real.log (100000000000 / 117979612367) := by
    rw [show ((117979612367 / 100000000000) : ℝ) = ((100000000000 / 117979612367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1929_neg : (33078349 / 100000000) ≤ -Real.log (62500000000 / 87003647889) ∧
    -Real.log (62500000000 / 87003647889) ≤ (330783491 / 1000000000) := by
  have h := checkLog_sound (w := (24503647889 / 149503647889)) (n := 12)
    (lo := (33078349 / 100000000)) (hi := (330783491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87003647889 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87003647889 / 62500000000) = 1/(62500000000 / 87003647889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1929 : Bounds (33078349 / 100000000) (330783491 / 1000000000) (Real.log (87003647889 / 62500000000)) := by
  have h := reflection_log_1929_neg
  have he : Real.log (87003647889 / 62500000000) = -Real.log (62500000000 / 87003647889) := by
    rw [show ((87003647889 / 62500000000) : ℝ) = ((62500000000 / 87003647889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1930_neg : (66197803 / 200000000) ≤ -Real.log (125000000000 / 174043062201) ∧
    -Real.log (125000000000 / 174043062201) ≤ (41373627 / 125000000) := by
  have h := checkLog_sound (w := (49043062201 / 299043062201)) (n := 12)
    (lo := (66197803 / 200000000)) (hi := (41373627 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174043062201 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(174043062201 / 125000000000) = 1/(125000000000 / 174043062201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1930 : Bounds (66197803 / 200000000) (41373627 / 125000000) (Real.log (174043062201 / 125000000000)) := by
  have h := reflection_log_1930_neg
  have he : Real.log (174043062201 / 125000000000) = -Real.log (125000000000 / 174043062201) := by
    rw [show ((174043062201 / 125000000000) : ℝ) = ((125000000000 / 174043062201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1931_neg : (4748383 / 31250000) ≤ -Real.log (10000 / 11641) ∧
    -Real.log (10000 / 11641) ≤ (151948257 / 1000000000) := by
  have h := checkLog_sound (w := (1641 / 21641)) (n := 12)
    (lo := (4748383 / 31250000)) (hi := (151948257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11641 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11641 / 10000) = 1/(10000 / 11641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1931 : Bounds (4748383 / 31250000) (151948257 / 1000000000) (Real.log (11641 / 10000)) := by
  have h := reflection_log_1931_neg
  have he : Real.log (11641 / 10000) = -Real.log (10000 / 11641) := by
    rw [show ((11641 / 10000) : ℝ) = ((10000 / 11641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1932_neg : (17924629 / 100000000) ≤ -Real.log (8359 / 10000) ∧
    -Real.log (8359 / 10000) ≤ (179246291 / 1000000000) := by
  have h := checkLog_sound (w := (1641 / 18359)) (n := 12)
    (lo := (17924629 / 100000000)) (hi := (179246291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8359) = 1/(8359 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1932 : Bounds (-179246291 / 1000000000) (-17924629 / 100000000) (Real.log (8359 / 10000)) := by
  have h := reflection_log_1932_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1933_neg : (82043 / 500000000) ≤ -Real.log (10000000 / 10001641) ∧
    -Real.log (10000000 / 10001641) ≤ (164087 / 1000000000) := by
  have h := checkLog_sound (w := (1641 / 20001641)) (n := 12)
    (lo := (82043 / 500000000)) (hi := (164087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001641 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001641 / 10000000) = 1/(10000000 / 10001641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1933 : Bounds (82043 / 500000000) (164087 / 1000000000) (Real.log (10001641 / 10000000)) := by
  have h := reflection_log_1933_neg
  have he : Real.log (10001641 / 10000000) = -Real.log (10000000 / 10001641) := by
    rw [show ((10001641 / 10000000) : ℝ) = ((10000000 / 10001641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1934_neg : (164113 / 1000000000) ≤ -Real.log (9998359 / 10000000) ∧
    -Real.log (9998359 / 10000000) ≤ (82057 / 500000000) := by
  have h := checkLog_sound (w := (1641 / 19998359)) (n := 12)
    (lo := (164113 / 1000000000)) (hi := (82057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998359) = 1/(9998359 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1934 : Bounds (-82057 / 500000000) (-164113 / 1000000000) (Real.log (9998359 / 10000000)) := by
  have h := reflection_log_1934_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1935_neg : (79105961 / 1000000000) ≤ -Real.log (1000000 / 1082319) ∧
    -Real.log (1000000 / 1082319) ≤ (39552981 / 500000000) := by
  have h := checkLog_sound (w := (82319 / 2082319)) (n := 12)
    (lo := (79105961 / 1000000000)) (hi := (39552981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082319 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082319 / 1000000) = 1/(1000000 / 1082319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1935 : Bounds (79105961 / 1000000000) (39552981 / 500000000) (Real.log (1082319 / 1000000)) := by
  have h := reflection_log_1935_neg
  have he : Real.log (1082319 / 1000000) = -Real.log (1000000 / 1082319) := by
    rw [show ((1082319 / 1000000) : ℝ) = ((1000000 / 1082319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1936_neg : (85905443 / 1000000000) ≤ -Real.log (917681 / 1000000) ∧
    -Real.log (917681 / 1000000) ≤ (21476361 / 250000000) := by
  have h := checkLog_sound (w := (82319 / 1917681)) (n := 12)
    (lo := (85905443 / 1000000000)) (hi := (21476361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917681) = 1/(917681 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1936 : Bounds (-21476361 / 250000000) (-85905443 / 1000000000) (Real.log (917681 / 1000000)) := by
  have h := reflection_log_1936_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1937_neg : (79304589 / 1000000000) ≤ -Real.log (500000 / 541267) ∧
    -Real.log (500000 / 541267) ≤ (7930459 / 100000000) := by
  have h := checkLog_sound (w := (41267 / 1041267)) (n := 12)
    (lo := (79304589 / 1000000000)) (hi := (7930459 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541267 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541267 / 500000) = 1/(500000 / 541267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1937 : Bounds (79304589 / 1000000000) (7930459 / 100000000) (Real.log (541267 / 500000)) := by
  have h := reflection_log_1937_neg
  have he : Real.log (541267 / 500000) = -Real.log (500000 / 541267) := by
    rw [show ((541267 / 500000) : ℝ) = ((500000 / 541267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1938_neg : (21534939 / 250000000) ≤ -Real.log (458733 / 500000) ∧
    -Real.log (458733 / 500000) ≤ (86139757 / 1000000000) := by
  have h := checkLog_sound (w := (41267 / 958733)) (n := 12)
    (lo := (21534939 / 250000000)) (hi := (86139757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458733) = 1/(458733 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1938 : Bounds (-86139757 / 1000000000) (-21534939 / 250000000) (Real.log (458733 / 500000)) := by
  have h := reflection_log_1938_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1939_neg : (6835167 / 1000000000) ≤ -Real.log (248297034711 / 250000000000) ∧
    -Real.log (248297034711 / 250000000000) ≤ (213599 / 31250000) := by
  have h := checkLog_sound (w := (1702965289 / 498297034711)) (n := 12)
    (lo := (6835167 / 1000000000)) (hi := (213599 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248297034711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248297034711) = 1/(248297034711 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1939 : Bounds (-213599 / 31250000) (-6835167 / 1000000000) (Real.log (248297034711 / 250000000000)) := by
  have h := reflection_log_1939_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1940_neg : (6799481 / 1000000000) ≤ -Real.log (993223582239 / 1000000000000) ∧
    -Real.log (993223582239 / 1000000000000) ≤ (3399741 / 500000000) := by
  have h := checkLog_sound (w := (6776417761 / 1993223582239)) (n := 12)
    (lo := (6799481 / 1000000000)) (hi := (3399741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993223582239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993223582239) = 1/(993223582239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1940 : Bounds (-3399741 / 500000000) (-6799481 / 1000000000) (Real.log (993223582239 / 1000000000000)) := by
  have h := reflection_log_1940_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1941_neg : (41252851 / 250000000) ≤ -Real.log (125000000000 / 147425821173) ∧
    -Real.log (125000000000 / 147425821173) ≤ (33002281 / 200000000) := by
  have h := checkLog_sound (w := (22425821173 / 272425821173)) (n := 12)
    (lo := (41252851 / 250000000)) (hi := (33002281 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147425821173 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147425821173 / 125000000000) = 1/(125000000000 / 147425821173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1941 : Bounds (41252851 / 250000000) (33002281 / 200000000) (Real.log (147425821173 / 125000000000)) := by
  have h := reflection_log_1941_neg
  have he : Real.log (147425821173 / 125000000000) = -Real.log (125000000000 / 147425821173) := by
    rw [show ((147425821173 / 125000000000) : ℝ) = ((125000000000 / 147425821173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1942_neg : (82722173 / 500000000) ≤ -Real.log (500000000000 / 589958646969) ∧
    -Real.log (500000000000 / 589958646969) ≤ (165444347 / 1000000000) := by
  have h := checkLog_sound (w := (89958646969 / 1089958646969)) (n := 12)
    (lo := (82722173 / 500000000)) (hi := (165444347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589958646969 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589958646969 / 500000000000) = 1/(500000000000 / 589958646969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1942 : Bounds (82722173 / 500000000) (165444347 / 1000000000) (Real.log (589958646969 / 500000000000)) := by
  have h := reflection_log_1942_neg
  have he : Real.log (589958646969 / 500000000000) = -Real.log (500000000000 / 589958646969) := by
    rw [show ((589958646969 / 500000000000) : ℝ) = ((500000000000 / 589958646969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1943_neg : (66197803 / 200000000) ≤ -Real.log (500000000000 / 696172248803) ∧
    -Real.log (500000000000 / 696172248803) ≤ (41373627 / 125000000) := by
  have h := checkLog_sound (w := (196172248803 / 1196172248803)) (n := 12)
    (lo := (66197803 / 200000000)) (hi := (41373627 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696172248803 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696172248803 / 500000000000) = 1/(500000000000 / 696172248803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1943 : Bounds (66197803 / 200000000) (41373627 / 125000000) (Real.log (696172248803 / 500000000000)) := by
  have h := reflection_log_1943_neg
  have he : Real.log (696172248803 / 500000000000) = -Real.log (500000000000 / 696172248803) := by
    rw [show ((696172248803 / 500000000000) : ℝ) = ((500000000000 / 696172248803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1944_neg : (165597273 / 500000000) ≤ -Real.log (250000000000 / 348157674363) ∧
    -Real.log (250000000000 / 348157674363) ≤ (331194547 / 1000000000) := by
  have h := checkLog_sound (w := (98157674363 / 598157674363)) (n := 12)
    (lo := (165597273 / 500000000)) (hi := (331194547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((348157674363 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(348157674363 / 250000000000) = 1/(250000000000 / 348157674363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1944 : Bounds (165597273 / 500000000) (331194547 / 1000000000) (Real.log (348157674363 / 250000000000)) := by
  have h := reflection_log_1944_neg
  have he : Real.log (348157674363 / 250000000000) = -Real.log (250000000000 / 348157674363) := by
    rw [show ((348157674363 / 250000000000) : ℝ) = ((250000000000 / 348157674363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1945_neg : (30406831 / 200000000) ≤ -Real.log (5000 / 5821) ∧
    -Real.log (5000 / 5821) ≤ (38008539 / 250000000) := by
  have h := checkLog_sound (w := (821 / 10821)) (n := 12)
    (lo := (30406831 / 200000000)) (hi := (38008539 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5821 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5821 / 5000) = 1/(5000 / 5821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1945 : Bounds (30406831 / 200000000) (38008539 / 250000000) (Real.log (5821 / 5000)) := by
  have h := reflection_log_1945_neg
  have he : Real.log (5821 / 5000) = -Real.log (5000 / 5821) := by
    rw [show ((5821 / 5000) : ℝ) = ((5000 / 5821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1946_neg : (22420741 / 125000000) ≤ -Real.log (4179 / 5000) ∧
    -Real.log (4179 / 5000) ≤ (179365929 / 1000000000) := by
  have h := checkLog_sound (w := (821 / 9179)) (n := 12)
    (lo := (22420741 / 125000000)) (hi := (179365929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4179) = 1/(4179 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1946 : Bounds (-179365929 / 1000000000) (-22420741 / 125000000) (Real.log (4179 / 5000)) := by
  have h := reflection_log_1946_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1947_neg : (82093 / 500000000) ≤ -Real.log (5000000 / 5000821) ∧
    -Real.log (5000000 / 5000821) ≤ (164187 / 1000000000) := by
  have h := checkLog_sound (w := (821 / 10000821)) (n := 12)
    (lo := (82093 / 500000000)) (hi := (164187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000821 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000821 / 5000000) = 1/(5000000 / 5000821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1947 : Bounds (82093 / 500000000) (164187 / 1000000000) (Real.log (5000821 / 5000000)) := by
  have h := reflection_log_1947_neg
  have he : Real.log (5000821 / 5000000) = -Real.log (5000000 / 5000821) := by
    rw [show ((5000821 / 5000000) : ℝ) = ((5000000 / 5000821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1948_neg : (164213 / 1000000000) ≤ -Real.log (4999179 / 5000000) ∧
    -Real.log (4999179 / 5000000) ≤ (82107 / 500000000) := by
  have h := checkLog_sound (w := (821 / 9999179)) (n := 12)
    (lo := (164213 / 1000000000)) (hi := (82107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999179) = 1/(4999179 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1948 : Bounds (-82107 / 500000000) (-164213 / 1000000000) (Real.log (4999179 / 5000000)) := by
  have h := reflection_log_1948_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1949_neg : (79152157 / 1000000000) ≤ -Real.log (1000000 / 1082369) ∧
    -Real.log (1000000 / 1082369) ≤ (39576079 / 500000000) := by
  have h := checkLog_sound (w := (82369 / 2082369)) (n := 12)
    (lo := (79152157 / 1000000000)) (hi := (39576079 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082369 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082369 / 1000000) = 1/(1000000 / 1082369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1949 : Bounds (79152157 / 1000000000) (39576079 / 500000000) (Real.log (1082369 / 1000000)) := by
  have h := reflection_log_1949_neg
  have he : Real.log (1082369 / 1000000) = -Real.log (1000000 / 1082369) := by
    rw [show ((1082369 / 1000000) : ℝ) = ((1000000 / 1082369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1950_neg : (85959929 / 1000000000) ≤ -Real.log (917631 / 1000000) ∧
    -Real.log (917631 / 1000000) ≤ (8595993 / 100000000) := by
  have h := checkLog_sound (w := (82369 / 1917631)) (n := 12)
    (lo := (85959929 / 1000000000)) (hi := (8595993 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917631) = 1/(917631 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1950 : Bounds (-8595993 / 100000000) (-85959929 / 1000000000) (Real.log (917631 / 1000000)) := by
  have h := reflection_log_1950_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1951_neg : (79351699 / 1000000000) ≤ -Real.log (200000 / 216517) ∧
    -Real.log (200000 / 216517) ≤ (793517 / 10000000) := by
  have h := checkLog_sound (w := (16517 / 416517)) (n := 12)
    (lo := (79351699 / 1000000000)) (hi := (793517 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216517 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216517 / 200000) = 1/(200000 / 216517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1951 : Bounds (79351699 / 1000000000) (793517 / 10000000) (Real.log (216517 / 200000)) := by
  have h := reflection_log_1951_neg
  have he : Real.log (216517 / 200000) = -Real.log (200000 / 216517) := by
    rw [show ((216517 / 200000) : ℝ) = ((200000 / 216517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1952_neg : (43097673 / 500000000) ≤ -Real.log (183483 / 200000) ∧
    -Real.log (183483 / 200000) ≤ (86195347 / 1000000000) := by
  have h := checkLog_sound (w := (16517 / 383483)) (n := 12)
    (lo := (43097673 / 500000000)) (hi := (86195347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183483) = 1/(183483 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1952 : Bounds (-86195347 / 1000000000) (-43097673 / 500000000) (Real.log (183483 / 200000)) := by
  have h := reflection_log_1952_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1953_neg : (3421823 / 500000000) ≤ -Real.log (39727188711 / 40000000000) ∧
    -Real.log (39727188711 / 40000000000) ≤ (6843647 / 1000000000) := by
  have h := checkLog_sound (w := (272811289 / 79727188711)) (n := 12)
    (lo := (3421823 / 500000000)) (hi := (6843647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39727188711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39727188711) = 1/(39727188711 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1953 : Bounds (-6843647 / 1000000000) (-3421823 / 500000000) (Real.log (39727188711 / 40000000000)) := by
  have h := reflection_log_1953_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1954_neg : (1701943 / 250000000) ≤ -Real.log (993215347839 / 1000000000000) ∧
    -Real.log (993215347839 / 1000000000000) ≤ (6807773 / 1000000000) := by
  have h := checkLog_sound (w := (6784652161 / 1993215347839)) (n := 12)
    (lo := (1701943 / 250000000)) (hi := (6807773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993215347839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993215347839) = 1/(993215347839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1954 : Bounds (-6807773 / 1000000000) (-1701943 / 250000000) (Real.log (993215347839 / 1000000000000)) := by
  have h := reflection_log_1954_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1955_neg : (165112087 / 1000000000) ≤ -Real.log (50000000000 / 58976266059) ∧
    -Real.log (50000000000 / 58976266059) ≤ (20639011 / 125000000) := by
  have h := checkLog_sound (w := (8976266059 / 108976266059)) (n := 12)
    (lo := (165112087 / 1000000000)) (hi := (20639011 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58976266059 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58976266059 / 50000000000) = 1/(50000000000 / 58976266059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1955 : Bounds (165112087 / 1000000000) (20639011 / 125000000) (Real.log (58976266059 / 50000000000)) := by
  have h := reflection_log_1955_neg
  have he : Real.log (58976266059 / 50000000000) = -Real.log (50000000000 / 58976266059) := by
    rw [show ((58976266059 / 50000000000) : ℝ) = ((50000000000 / 58976266059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1956_neg : (82773523 / 500000000) ≤ -Real.log (12500000000 / 14750480971) ∧
    -Real.log (12500000000 / 14750480971) ≤ (165547047 / 1000000000) := by
  have h := checkLog_sound (w := (2250480971 / 27250480971)) (n := 12)
    (lo := (82773523 / 500000000)) (hi := (165547047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14750480971 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14750480971 / 12500000000) = 1/(12500000000 / 14750480971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1956 : Bounds (82773523 / 500000000) (165547047 / 1000000000) (Real.log (14750480971 / 12500000000)) := by
  have h := reflection_log_1956_neg
  have he : Real.log (14750480971 / 12500000000) = -Real.log (12500000000 / 14750480971) := by
    rw [show ((14750480971 / 12500000000) : ℝ) = ((12500000000 / 14750480971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1957_neg : (165597273 / 500000000) ≤ -Real.log (20000000000 / 27852613949) ∧
    -Real.log (20000000000 / 27852613949) ≤ (331194547 / 1000000000) := by
  have h := checkLog_sound (w := (7852613949 / 47852613949)) (n := 12)
    (lo := (165597273 / 500000000)) (hi := (331194547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27852613949 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27852613949 / 20000000000) = 1/(20000000000 / 27852613949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1957 : Bounds (165597273 / 500000000) (331194547 / 1000000000) (Real.log (27852613949 / 20000000000)) := by
  have h := reflection_log_1957_neg
  have he : Real.log (27852613949 / 20000000000) = -Real.log (20000000000 / 27852613949) := by
    rw [show ((27852613949 / 20000000000) : ℝ) = ((20000000000 / 27852613949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1958_neg : (82850021 / 250000000) ≤ -Real.log (500000000000 / 696458482891) ∧
    -Real.log (500000000000 / 696458482891) ≤ (66280017 / 200000000) := by
  have h := checkLog_sound (w := (196458482891 / 1196458482891)) (n := 12)
    (lo := (82850021 / 250000000)) (hi := (66280017 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696458482891 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696458482891 / 500000000000) = 1/(500000000000 / 696458482891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1958 : Bounds (82850021 / 250000000) (66280017 / 200000000) (Real.log (696458482891 / 500000000000)) := by
  have h := reflection_log_1958_neg
  have he : Real.log (696458482891 / 500000000000) = -Real.log (500000000000 / 696458482891) := by
    rw [show ((696458482891 / 500000000000) : ℝ) = ((500000000000 / 696458482891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1959_neg : (9507503 / 62500000) ≤ -Real.log (10000 / 11643) ∧
    -Real.log (10000 / 11643) ≤ (152120049 / 1000000000) := by
  have h := checkLog_sound (w := (1643 / 21643)) (n := 12)
    (lo := (9507503 / 62500000)) (hi := (152120049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11643 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11643 / 10000) = 1/(10000 / 11643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1959 : Bounds (9507503 / 62500000) (152120049 / 1000000000) (Real.log (11643 / 10000)) := by
  have h := reflection_log_1959_neg
  have he : Real.log (11643 / 10000) = -Real.log (10000 / 11643) := by
    rw [show ((11643 / 10000) : ℝ) = ((10000 / 11643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1960_neg : (179485581 / 1000000000) ≤ -Real.log (8357 / 10000) ∧
    -Real.log (8357 / 10000) ≤ (89742791 / 500000000) := by
  have h := checkLog_sound (w := (1643 / 18357)) (n := 12)
    (lo := (179485581 / 1000000000)) (hi := (89742791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8357) = 1/(8357 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1960 : Bounds (-89742791 / 500000000) (-179485581 / 1000000000) (Real.log (8357 / 10000)) := by
  have h := reflection_log_1960_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1961_neg : (82143 / 500000000) ≤ -Real.log (10000000 / 10001643) ∧
    -Real.log (10000000 / 10001643) ≤ (164287 / 1000000000) := by
  have h := checkLog_sound (w := (1643 / 20001643)) (n := 12)
    (lo := (82143 / 500000000)) (hi := (164287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001643 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001643 / 10000000) = 1/(10000000 / 10001643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1961 : Bounds (82143 / 500000000) (164287 / 1000000000) (Real.log (10001643 / 10000000)) := by
  have h := reflection_log_1961_neg
  have he : Real.log (10001643 / 10000000) = -Real.log (10000000 / 10001643) := by
    rw [show ((10001643 / 10000000) : ℝ) = ((10000000 / 10001643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1962_neg : (164313 / 1000000000) ≤ -Real.log (9998357 / 10000000) ∧
    -Real.log (9998357 / 10000000) ≤ (82157 / 500000000) := by
  have h := checkLog_sound (w := (1643 / 19998357)) (n := 12)
    (lo := (164313 / 1000000000)) (hi := (82157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998357) = 1/(9998357 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1962 : Bounds (-82157 / 500000000) (-164313 / 1000000000) (Real.log (9998357 / 10000000)) := by
  have h := reflection_log_1962_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1963_neg : (3167971 / 40000000) ≤ -Real.log (50000 / 54121) ∧
    -Real.log (50000 / 54121) ≤ (19799819 / 250000000) := by
  have h := checkLog_sound (w := (4121 / 104121)) (n := 12)
    (lo := (3167971 / 40000000)) (hi := (19799819 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54121 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54121 / 50000) = 1/(50000 / 54121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1963 : Bounds (3167971 / 40000000) (19799819 / 250000000) (Real.log (54121 / 50000)) := by
  have h := reflection_log_1963_neg
  have he : Real.log (54121 / 50000) = -Real.log (50000 / 54121) := by
    rw [show ((54121 / 50000) : ℝ) = ((50000 / 54121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1964_neg : (86015509 / 1000000000) ≤ -Real.log (45879 / 50000) ∧
    -Real.log (45879 / 50000) ≤ (8601551 / 100000000) := by
  have h := checkLog_sound (w := (4121 / 95879)) (n := 12)
    (lo := (86015509 / 1000000000)) (hi := (8601551 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45879) = 1/(45879 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1964 : Bounds (-8601551 / 100000000) (-86015509 / 1000000000) (Real.log (45879 / 50000)) := by
  have h := reflection_log_1964_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1965_neg : (19849471 / 250000000) ≤ -Real.log (200000 / 216527) ∧
    -Real.log (200000 / 216527) ≤ (15879577 / 200000000) := by
  have h := checkLog_sound (w := (16527 / 416527)) (n := 12)
    (lo := (19849471 / 250000000)) (hi := (15879577 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216527 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216527 / 200000) = 1/(200000 / 216527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1965 : Bounds (19849471 / 250000000) (15879577 / 200000000) (Real.log (216527 / 200000)) := by
  have h := reflection_log_1965_neg
  have he : Real.log (216527 / 200000) = -Real.log (200000 / 216527) := by
    rw [show ((216527 / 200000) : ℝ) = ((200000 / 216527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1966_neg : (10781231 / 125000000) ≤ -Real.log (183473 / 200000) ∧
    -Real.log (183473 / 200000) ≤ (86249849 / 1000000000) := by
  have h := checkLog_sound (w := (16527 / 383473)) (n := 12)
    (lo := (10781231 / 125000000)) (hi := (86249849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183473) = 1/(183473 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1966 : Bounds (-86249849 / 1000000000) (-10781231 / 125000000) (Real.log (183473 / 200000)) := by
  have h := reflection_log_1966_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1967_neg : (1712991 / 250000000) ≤ -Real.log (39726858271 / 40000000000) ∧
    -Real.log (39726858271 / 40000000000) ≤ (1370393 / 200000000) := by
  have h := checkLog_sound (w := (273141729 / 79726858271)) (n := 12)
    (lo := (1712991 / 250000000)) (hi := (1370393 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39726858271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39726858271) = 1/(39726858271 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1967 : Bounds (-1370393 / 200000000) (-1712991 / 250000000) (Real.log (39726858271 / 40000000000)) := by
  have h := reflection_log_1967_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1968_neg : (3408117 / 500000000) ≤ -Real.log (2483017359 / 2500000000) ∧
    -Real.log (2483017359 / 2500000000) ≤ (1363247 / 200000000) := by
  have h := checkLog_sound (w := (16982641 / 4983017359)) (n := 12)
    (lo := (3408117 / 500000000)) (hi := (1363247 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2483017359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2483017359) = 1/(2483017359 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1968 : Bounds (-1363247 / 200000000) (-3408117 / 500000000) (Real.log (2483017359 / 2500000000)) := by
  have h := reflection_log_1968_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1969_neg : (2581481 / 15625000) ≤ -Real.log (500000000000 / 589823230671) ∧
    -Real.log (500000000000 / 589823230671) ≤ (33042957 / 200000000) := by
  have h := checkLog_sound (w := (89823230671 / 1089823230671)) (n := 12)
    (lo := (2581481 / 15625000)) (hi := (33042957 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589823230671 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589823230671 / 500000000000) = 1/(500000000000 / 589823230671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1969 : Bounds (2581481 / 15625000) (33042957 / 200000000) (Real.log (589823230671 / 500000000000)) := by
  have h := reflection_log_1969_neg
  have he : Real.log (589823230671 / 500000000000) = -Real.log (500000000000 / 589823230671) := by
    rw [show ((589823230671 / 500000000000) : ℝ) = ((500000000000 / 589823230671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1970_neg : (165647733 / 1000000000) ≤ -Real.log (20000000000 / 23603145967) ∧
    -Real.log (20000000000 / 23603145967) ≤ (82823867 / 500000000) := by
  have h := checkLog_sound (w := (3603145967 / 43603145967)) (n := 12)
    (lo := (165647733 / 1000000000)) (hi := (82823867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23603145967 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23603145967 / 20000000000) = 1/(20000000000 / 23603145967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1970 : Bounds (165647733 / 1000000000) (82823867 / 500000000) (Real.log (23603145967 / 20000000000)) := by
  have h := reflection_log_1970_neg
  have he : Real.log (23603145967 / 20000000000) = -Real.log (20000000000 / 23603145967) := by
    rw [show ((23603145967 / 20000000000) : ℝ) = ((20000000000 / 23603145967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1971_neg : (82850021 / 250000000) ≤ -Real.log (50000000000 / 69645848289) ∧
    -Real.log (50000000000 / 69645848289) ≤ (66280017 / 200000000) := by
  have h := checkLog_sound (w := (19645848289 / 119645848289)) (n := 12)
    (lo := (82850021 / 250000000)) (hi := (66280017 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69645848289 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69645848289 / 50000000000) = 1/(50000000000 / 69645848289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1971 : Bounds (82850021 / 250000000) (66280017 / 200000000) (Real.log (69645848289 / 50000000000)) := by
  have h := reflection_log_1971_neg
  have he : Real.log (69645848289 / 50000000000) = -Real.log (50000000000 / 69645848289) := by
    rw [show ((69645848289 / 50000000000) : ℝ) = ((50000000000 / 69645848289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1972_neg : (33160563 / 100000000) ≤ -Real.log (500000000000 / 696601651311) ∧
    -Real.log (500000000000 / 696601651311) ≤ (331605631 / 1000000000) := by
  have h := checkLog_sound (w := (196601651311 / 1196601651311)) (n := 12)
    (lo := (33160563 / 100000000)) (hi := (331605631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696601651311 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696601651311 / 500000000000) = 1/(500000000000 / 696601651311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1972 : Bounds (33160563 / 100000000) (331605631 / 1000000000) (Real.log (696601651311 / 500000000000)) := by
  have h := reflection_log_1972_neg
  have he : Real.log (696601651311 / 500000000000) = -Real.log (500000000000 / 696601651311) := by
    rw [show ((696601651311 / 500000000000) : ℝ) = ((500000000000 / 696601651311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1973_neg : (38051483 / 250000000) ≤ -Real.log (2500 / 2911) ∧
    -Real.log (2500 / 2911) ≤ (152205933 / 1000000000) := by
  have h := checkLog_sound (w := (411 / 5411)) (n := 12)
    (lo := (38051483 / 250000000)) (hi := (152205933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2911 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2911 / 2500) = 1/(2500 / 2911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1973 : Bounds (38051483 / 250000000) (152205933 / 1000000000) (Real.log (2911 / 2500)) := by
  have h := reflection_log_1973_neg
  have he : Real.log (2911 / 2500) = -Real.log (2500 / 2911) := by
    rw [show ((2911 / 2500) : ℝ) = ((2500 / 2911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1974_neg : (179605249 / 1000000000) ≤ -Real.log (2089 / 2500) ∧
    -Real.log (2089 / 2500) ≤ (718421 / 4000000) := by
  have h := checkLog_sound (w := (411 / 4589)) (n := 12)
    (lo := (179605249 / 1000000000)) (hi := (718421 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2089) = 1/(2089 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1974 : Bounds (-718421 / 4000000) (-179605249 / 1000000000) (Real.log (2089 / 2500)) := by
  have h := reflection_log_1974_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1975_neg : (82193 / 500000000) ≤ -Real.log (2500000 / 2500411) ∧
    -Real.log (2500000 / 2500411) ≤ (164387 / 1000000000) := by
  have h := checkLog_sound (w := (411 / 5000411)) (n := 12)
    (lo := (82193 / 500000000)) (hi := (164387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500411 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500411 / 2500000) = 1/(2500000 / 2500411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1975 : Bounds (82193 / 500000000) (164387 / 1000000000) (Real.log (2500411 / 2500000)) := by
  have h := reflection_log_1975_neg
  have he : Real.log (2500411 / 2500000) = -Real.log (2500000 / 2500411) := by
    rw [show ((2500411 / 2500000) : ℝ) = ((2500000 / 2500411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1976_neg : (164413 / 1000000000) ≤ -Real.log (2499589 / 2500000) ∧
    -Real.log (2499589 / 2500000) ≤ (82207 / 500000000) := by
  have h := checkLog_sound (w := (411 / 4999589)) (n := 12)
    (lo := (164413 / 1000000000)) (hi := (82207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499589) = 1/(2499589 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1976 : Bounds (-82207 / 500000000) (-164413 / 1000000000) (Real.log (2499589 / 2500000)) := by
  have h := reflection_log_1976_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1977_neg : (7924639 / 100000000) ≤ -Real.log (1000000 / 1082471) ∧
    -Real.log (1000000 / 1082471) ≤ (79246391 / 1000000000) := by
  have h := checkLog_sound (w := (82471 / 2082471)) (n := 12)
    (lo := (7924639 / 100000000)) (hi := (79246391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082471 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082471 / 1000000) = 1/(1000000 / 1082471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1977 : Bounds (7924639 / 100000000) (79246391 / 1000000000) (Real.log (1082471 / 1000000)) := by
  have h := reflection_log_1977_neg
  have he : Real.log (1082471 / 1000000) = -Real.log (1000000 / 1082471) := by
    rw [show ((1082471 / 1000000) : ℝ) = ((1000000 / 1082471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1978_neg : (86071091 / 1000000000) ≤ -Real.log (917529 / 1000000) ∧
    -Real.log (917529 / 1000000) ≤ (21517773 / 250000000) := by
  have h := checkLog_sound (w := (82471 / 1917529)) (n := 12)
    (lo := (86071091 / 1000000000)) (hi := (21517773 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917529) = 1/(917529 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1978 : Bounds (-21517773 / 250000000) (-86071091 / 1000000000) (Real.log (917529 / 1000000)) := by
  have h := reflection_log_1978_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1979_neg : (7944499 / 100000000) ≤ -Real.log (500000 / 541343) ∧
    -Real.log (500000 / 541343) ≤ (79444991 / 1000000000) := by
  have h := checkLog_sound (w := (41343 / 1041343)) (n := 12)
    (lo := (7944499 / 100000000)) (hi := (79444991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541343 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541343 / 500000) = 1/(500000 / 541343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1979 : Bounds (7944499 / 100000000) (79444991 / 1000000000) (Real.log (541343 / 500000)) := by
  have h := reflection_log_1979_neg
  have he : Real.log (541343 / 500000) = -Real.log (500000 / 541343) := by
    rw [show ((541343 / 500000) : ℝ) = ((500000 / 541343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1980_neg : (21576361 / 250000000) ≤ -Real.log (458657 / 500000) ∧
    -Real.log (458657 / 500000) ≤ (17261089 / 200000000) := by
  have h := checkLog_sound (w := (41343 / 958657)) (n := 12)
    (lo := (21576361 / 250000000)) (hi := (17261089 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458657) = 1/(458657 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1980 : Bounds (-17261089 / 200000000) (-21576361 / 250000000) (Real.log (458657 / 500000)) := by
  have h := reflection_log_1980_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1981_neg : (6860453 / 1000000000) ≤ -Real.log (248290756351 / 250000000000) ∧
    -Real.log (248290756351 / 250000000000) ≤ (3430227 / 500000000) := by
  have h := checkLog_sound (w := (1709243649 / 498290756351)) (n := 12)
    (lo := (6860453 / 1000000000)) (hi := (3430227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248290756351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248290756351) = 1/(248290756351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1981 : Bounds (-3430227 / 500000000) (-6860453 / 1000000000) (Real.log (248290756351 / 250000000000)) := by
  have h := reflection_log_1981_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1982_neg : (6824701 / 1000000000) ≤ -Real.log (993198534159 / 1000000000000) ∧
    -Real.log (993198534159 / 1000000000000) ≤ (3412351 / 500000000) := by
  have h := checkLog_sound (w := (6801465841 / 1993198534159)) (n := 12)
    (lo := (6824701 / 1000000000)) (hi := (3412351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993198534159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993198534159) = 1/(993198534159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1982 : Bounds (-3412351 / 500000000) (-6824701 / 1000000000) (Real.log (993198534159 / 1000000000000)) := by
  have h := reflection_log_1982_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1983_neg : (82658741 / 500000000) ≤ -Real.log (500000000000 / 589883807487) ∧
    -Real.log (500000000000 / 589883807487) ≤ (165317483 / 1000000000) := by
  have h := checkLog_sound (w := (89883807487 / 1089883807487)) (n := 12)
    (lo := (82658741 / 500000000)) (hi := (165317483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589883807487 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589883807487 / 500000000000) = 1/(500000000000 / 589883807487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1983 : Bounds (82658741 / 500000000) (165317483 / 1000000000) (Real.log (589883807487 / 500000000000)) := by
  have h := reflection_log_1983_neg
  have he : Real.log (589883807487 / 500000000000) = -Real.log (500000000000 / 589883807487) := by
    rw [show ((589883807487 / 500000000000) : ℝ) = ((500000000000 / 589883807487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0031 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1984_neg : (33150087 / 200000000) ≤ -Real.log (500000000000 / 590139254389) ∧
    -Real.log (500000000000 / 590139254389) ≤ (41437609 / 250000000) := by
  have h := checkLog_sound (w := (90139254389 / 1090139254389)) (n := 12)
    (lo := (33150087 / 200000000)) (hi := (41437609 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590139254389 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590139254389 / 500000000000) = 1/(500000000000 / 590139254389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1984 : Bounds (33150087 / 200000000) (41437609 / 250000000) (Real.log (590139254389 / 500000000000)) := by
  have h := reflection_log_1984_neg
  have he : Real.log (590139254389 / 500000000000) = -Real.log (500000000000 / 590139254389) := by
    rw [show ((590139254389 / 500000000000) : ℝ) = ((500000000000 / 590139254389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1985_neg : (33160563 / 100000000) ≤ -Real.log (50000000000 / 69660165131) ∧
    -Real.log (50000000000 / 69660165131) ≤ (331605631 / 1000000000) := by
  have h := checkLog_sound (w := (19660165131 / 119660165131)) (n := 12)
    (lo := (33160563 / 100000000)) (hi := (331605631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69660165131 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69660165131 / 50000000000) = 1/(50000000000 / 69660165131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1985 : Bounds (33160563 / 100000000) (331605631 / 1000000000) (Real.log (69660165131 / 50000000000)) := by
  have h := reflection_log_1985_neg
  have he : Real.log (69660165131 / 50000000000) = -Real.log (50000000000 / 69660165131) := by
    rw [show ((69660165131 / 50000000000) : ℝ) = ((50000000000 / 69660165131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1986_neg : (165905591 / 500000000) ≤ -Real.log (250000000000 / 348372426999) ∧
    -Real.log (250000000000 / 348372426999) ≤ (331811183 / 1000000000) := by
  have h := checkLog_sound (w := (98372426999 / 598372426999)) (n := 12)
    (lo := (165905591 / 500000000)) (hi := (331811183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((348372426999 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(348372426999 / 250000000000) = 1/(250000000000 / 348372426999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1986 : Bounds (165905591 / 500000000) (331811183 / 1000000000) (Real.log (348372426999 / 250000000000)) := by
  have h := reflection_log_1986_neg
  have he : Real.log (348372426999 / 250000000000) = -Real.log (250000000000 / 348372426999) := by
    rw [show ((348372426999 / 250000000000) : ℝ) = ((250000000000 / 348372426999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1987_neg : (15229181 / 100000000) ≤ -Real.log (2000 / 2329) ∧
    -Real.log (2000 / 2329) ≤ (152291811 / 1000000000) := by
  have h := checkLog_sound (w := (329 / 4329)) (n := 12)
    (lo := (15229181 / 100000000)) (hi := (152291811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2329 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2329 / 2000) = 1/(2000 / 2329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1987 : Bounds (15229181 / 100000000) (152291811 / 1000000000) (Real.log (2329 / 2000)) := by
  have h := reflection_log_1987_neg
  have he : Real.log (2329 / 2000) = -Real.log (2000 / 2329) := by
    rw [show ((2329 / 2000) : ℝ) = ((2000 / 2329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1988_neg : (17972493 / 100000000) ≤ -Real.log (1671 / 2000) ∧
    -Real.log (1671 / 2000) ≤ (179724931 / 1000000000) := by
  have h := checkLog_sound (w := (329 / 3671)) (n := 12)
    (lo := (17972493 / 100000000)) (hi := (179724931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1671) = 1/(1671 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1988 : Bounds (-179724931 / 1000000000) (-17972493 / 100000000) (Real.log (1671 / 2000)) := by
  have h := reflection_log_1988_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1989_neg : (82243 / 500000000) ≤ -Real.log (2000000 / 2000329) ∧
    -Real.log (2000000 / 2000329) ≤ (164487 / 1000000000) := by
  have h := checkLog_sound (w := (329 / 4000329)) (n := 12)
    (lo := (82243 / 500000000)) (hi := (164487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000329 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000329 / 2000000) = 1/(2000000 / 2000329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1989 : Bounds (82243 / 500000000) (164487 / 1000000000) (Real.log (2000329 / 2000000)) := by
  have h := reflection_log_1989_neg
  have he : Real.log (2000329 / 2000000) = -Real.log (2000000 / 2000329) := by
    rw [show ((2000329 / 2000000) : ℝ) = ((2000000 / 2000329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1990_neg : (164513 / 1000000000) ≤ -Real.log (1999671 / 2000000) ∧
    -Real.log (1999671 / 2000000) ≤ (82257 / 500000000) := by
  have h := checkLog_sound (w := (329 / 3999671)) (n := 12)
    (lo := (164513 / 1000000000)) (hi := (82257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999671) = 1/(1999671 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1990 : Bounds (-82257 / 500000000) (-164513 / 1000000000) (Real.log (1999671 / 2000000)) := by
  have h := reflection_log_1990_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1991_neg : (1238961 / 15625000) ≤ -Real.log (500000 / 541261) ∧
    -Real.log (500000 / 541261) ≤ (15858701 / 200000000) := by
  have h := checkLog_sound (w := (41261 / 1041261)) (n := 12)
    (lo := (1238961 / 15625000)) (hi := (15858701 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541261 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541261 / 500000) = 1/(500000 / 541261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1991 : Bounds (1238961 / 15625000) (15858701 / 200000000) (Real.log (541261 / 500000)) := by
  have h := reflection_log_1991_neg
  have he : Real.log (541261 / 500000) = -Real.log (500000 / 541261) := by
    rw [show ((541261 / 500000) : ℝ) = ((500000 / 541261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1992_neg : (86126677 / 1000000000) ≤ -Real.log (458739 / 500000) ∧
    -Real.log (458739 / 500000) ≤ (43063339 / 500000000) := by
  have h := checkLog_sound (w := (41261 / 958739)) (n := 12)
    (lo := (86126677 / 1000000000)) (hi := (43063339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458739) = 1/(458739 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1992 : Bounds (-43063339 / 500000000) (-86126677 / 1000000000) (Real.log (458739 / 500000)) := by
  have h := reflection_log_1992_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1993_neg : (39746047 / 500000000) ≤ -Real.log (1000000 / 1082737) ∧
    -Real.log (1000000 / 1082737) ≤ (15898419 / 200000000) := by
  have h := checkLog_sound (w := (82737 / 2082737)) (n := 12)
    (lo := (39746047 / 500000000)) (hi := (15898419 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082737 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082737 / 1000000) = 1/(1000000 / 1082737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1993 : Bounds (39746047 / 500000000) (15898419 / 200000000) (Real.log (1082737 / 1000000)) := by
  have h := reflection_log_1993_neg
  have he : Real.log (1082737 / 1000000) = -Real.log (1000000 / 1082737) := by
    rw [show ((1082737 / 1000000) : ℝ) = ((1000000 / 1082737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1994_neg : (86361043 / 1000000000) ≤ -Real.log (917263 / 1000000) ∧
    -Real.log (917263 / 1000000) ≤ (21590261 / 250000000) := by
  have h := checkLog_sound (w := (82737 / 1917263)) (n := 12)
    (lo := (86361043 / 1000000000)) (hi := (21590261 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917263) = 1/(917263 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1994 : Bounds (-21590261 / 250000000) (-86361043 / 1000000000) (Real.log (917263 / 1000000)) := by
  have h := reflection_log_1994_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1995_neg : (1717237 / 250000000) ≤ -Real.log (993154588831 / 1000000000000) ∧
    -Real.log (993154588831 / 1000000000000) ≤ (6868949 / 1000000000) := by
  have h := checkLog_sound (w := (6845411169 / 1993154588831)) (n := 12)
    (lo := (1717237 / 250000000)) (hi := (6868949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993154588831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993154588831) = 1/(993154588831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1995 : Bounds (-6868949 / 1000000000) (-1717237 / 250000000) (Real.log (993154588831 / 1000000000000)) := by
  have h := reflection_log_1995_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1996_neg : (6833173 / 1000000000) ≤ -Real.log (248297529879 / 250000000000) ∧
    -Real.log (248297529879 / 250000000000) ≤ (3416587 / 500000000) := by
  have h := checkLog_sound (w := (1702470121 / 498297529879)) (n := 12)
    (lo := (6833173 / 1000000000)) (hi := (3416587 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248297529879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248297529879) = 1/(248297529879 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1996 : Bounds (-3416587 / 500000000) (-6833173 / 1000000000) (Real.log (248297529879 / 250000000000)) := by
  have h := reflection_log_1996_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1997_neg : (165420181 / 1000000000) ≤ -Real.log (500000000000 / 589944391037) ∧
    -Real.log (500000000000 / 589944391037) ≤ (82710091 / 500000000) := by
  have h := checkLog_sound (w := (89944391037 / 1089944391037)) (n := 12)
    (lo := (165420181 / 1000000000)) (hi := (82710091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589944391037 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589944391037 / 500000000000) = 1/(500000000000 / 589944391037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1997 : Bounds (165420181 / 1000000000) (82710091 / 500000000) (Real.log (589944391037 / 500000000000)) := by
  have h := reflection_log_1997_neg
  have he : Real.log (589944391037 / 500000000000) = -Real.log (500000000000 / 589944391037) := by
    rw [show ((589944391037 / 500000000000) : ℝ) = ((500000000000 / 589944391037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1998_neg : (165853137 / 1000000000) ≤ -Real.log (250000000000 / 295099933171) ∧
    -Real.log (250000000000 / 295099933171) ≤ (82926569 / 500000000) := by
  have h := checkLog_sound (w := (45099933171 / 545099933171)) (n := 12)
    (lo := (165853137 / 1000000000)) (hi := (82926569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295099933171 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295099933171 / 250000000000) = 1/(250000000000 / 295099933171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1998 : Bounds (165853137 / 1000000000) (82926569 / 500000000) (Real.log (295099933171 / 250000000000)) := by
  have h := reflection_log_1998_neg
  have he : Real.log (295099933171 / 250000000000) = -Real.log (250000000000 / 295099933171) := by
    rw [show ((295099933171 / 250000000000) : ℝ) = ((250000000000 / 295099933171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1999_neg : (165905591 / 500000000) ≤ -Real.log (500000000000 / 696744853997) ∧
    -Real.log (500000000000 / 696744853997) ≤ (331811183 / 1000000000) := by
  have h := checkLog_sound (w := (196744853997 / 1196744853997)) (n := 12)
    (lo := (165905591 / 500000000)) (hi := (331811183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696744853997 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696744853997 / 500000000000) = 1/(500000000000 / 696744853997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1999 : Bounds (165905591 / 500000000) (331811183 / 1000000000) (Real.log (696744853997 / 500000000000)) := by
  have h := reflection_log_1999_neg
  have he : Real.log (696744853997 / 500000000000) = -Real.log (500000000000 / 696744853997) := by
    rw [show ((696744853997 / 500000000000) : ℝ) = ((500000000000 / 696744853997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2000_neg : (332016741 / 1000000000) ≤ -Real.log (125000000000 / 174222022741) ∧
    -Real.log (125000000000 / 174222022741) ≤ (166008371 / 500000000) := by
  have h := checkLog_sound (w := (49222022741 / 299222022741)) (n := 12)
    (lo := (332016741 / 1000000000)) (hi := (166008371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174222022741 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(174222022741 / 125000000000) = 1/(125000000000 / 174222022741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2000 : Bounds (332016741 / 1000000000) (166008371 / 500000000) (Real.log (174222022741 / 125000000000)) := by
  have h := reflection_log_2000_neg
  have he : Real.log (174222022741 / 125000000000) = -Real.log (125000000000 / 174222022741) := by
    rw [show ((174222022741 / 125000000000) : ℝ) = ((125000000000 / 174222022741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2001_neg : (1904721 / 12500000) ≤ -Real.log (5000 / 5823) ∧
    -Real.log (5000 / 5823) ≤ (152377681 / 1000000000) := by
  have h := checkLog_sound (w := (823 / 10823)) (n := 12)
    (lo := (1904721 / 12500000)) (hi := (152377681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5823 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5823 / 5000) = 1/(5000 / 5823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2001 : Bounds (1904721 / 12500000) (152377681 / 1000000000) (Real.log (5823 / 5000)) := by
  have h := reflection_log_2001_neg
  have he : Real.log (5823 / 5000) = -Real.log (5000 / 5823) := by
    rw [show ((5823 / 5000) : ℝ) = ((5000 / 5823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2002_neg : (89922313 / 500000000) ≤ -Real.log (4177 / 5000) ∧
    -Real.log (4177 / 5000) ≤ (179844627 / 1000000000) := by
  have h := checkLog_sound (w := (823 / 9177)) (n := 12)
    (lo := (89922313 / 500000000)) (hi := (179844627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4177) = 1/(4177 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2002 : Bounds (-179844627 / 1000000000) (-89922313 / 500000000) (Real.log (4177 / 5000)) := by
  have h := reflection_log_2002_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2003_neg : (82293 / 500000000) ≤ -Real.log (5000000 / 5000823) ∧
    -Real.log (5000000 / 5000823) ≤ (164587 / 1000000000) := by
  have h := checkLog_sound (w := (823 / 10000823)) (n := 12)
    (lo := (82293 / 500000000)) (hi := (164587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000823 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000823 / 5000000) = 1/(5000000 / 5000823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2003 : Bounds (82293 / 500000000) (164587 / 1000000000) (Real.log (5000823 / 5000000)) := by
  have h := reflection_log_2003_neg
  have he : Real.log (5000823 / 5000000) = -Real.log (5000000 / 5000823) := by
    rw [show ((5000823 / 5000000) : ℝ) = ((5000000 / 5000823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2004_neg : (164613 / 1000000000) ≤ -Real.log (4999177 / 5000000) ∧
    -Real.log (4999177 / 5000000) ≤ (82307 / 500000000) := by
  have h := checkLog_sound (w := (823 / 9999177)) (n := 12)
    (lo := (164613 / 1000000000)) (hi := (82307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999177) = 1/(4999177 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2004 : Bounds (-82307 / 500000000) (-164613 / 1000000000) (Real.log (4999177 / 5000000)) := by
  have h := reflection_log_2004_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2005_neg : (79339691 / 1000000000) ≤ -Real.log (250000 / 270643) ∧
    -Real.log (250000 / 270643) ≤ (19834923 / 250000000) := by
  have h := checkLog_sound (w := (20643 / 520643)) (n := 12)
    (lo := (79339691 / 1000000000)) (hi := (19834923 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270643 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270643 / 250000) = 1/(250000 / 270643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2005 : Bounds (79339691 / 1000000000) (19834923 / 250000000) (Real.log (270643 / 250000)) := by
  have h := reflection_log_2005_neg
  have he : Real.log (270643 / 250000) = -Real.log (250000 / 270643) := by
    rw [show ((270643 / 250000) : ℝ) = ((250000 / 270643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2006_neg : (10772647 / 125000000) ≤ -Real.log (229357 / 250000) ∧
    -Real.log (229357 / 250000) ≤ (86181177 / 1000000000) := by
  have h := checkLog_sound (w := (20643 / 479357)) (n := 12)
    (lo := (10772647 / 125000000)) (hi := (86181177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229357) = 1/(229357 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2006 : Bounds (-86181177 / 1000000000) (-10772647 / 125000000) (Real.log (229357 / 250000)) := by
  have h := reflection_log_2006_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2007_neg : (19884799 / 250000000) ≤ -Real.log (250000 / 270697) ∧
    -Real.log (250000 / 270697) ≤ (79539197 / 1000000000) := by
  have h := checkLog_sound (w := (20697 / 520697)) (n := 12)
    (lo := (19884799 / 250000000)) (hi := (79539197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270697 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270697 / 250000) = 1/(250000 / 270697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2007 : Bounds (19884799 / 250000000) (79539197 / 1000000000) (Real.log (270697 / 250000)) := by
  have h := reflection_log_2007_neg
  have he : Real.log (270697 / 250000) = -Real.log (250000 / 270697) := by
    rw [show ((270697 / 250000) : ℝ) = ((250000 / 270697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2008_neg : (21604161 / 250000000) ≤ -Real.log (229303 / 250000) ∧
    -Real.log (229303 / 250000) ≤ (17283329 / 200000000) := by
  have h := checkLog_sound (w := (20697 / 479303)) (n := 12)
    (lo := (21604161 / 250000000)) (hi := (17283329 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229303) = 1/(229303 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2008 : Bounds (-17283329 / 200000000) (-21604161 / 250000000) (Real.log (229303 / 250000)) := by
  have h := reflection_log_2008_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2009_neg : (859681 / 125000000) ≤ -Real.log (62071634191 / 62500000000) ∧
    -Real.log (62071634191 / 62500000000) ≤ (6877449 / 1000000000) := by
  have h := checkLog_sound (w := (428365809 / 124571634191)) (n := 12)
    (lo := (859681 / 125000000)) (hi := (6877449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62071634191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62071634191) = 1/(62071634191 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2009 : Bounds (-6877449 / 1000000000) (-859681 / 125000000) (Real.log (62071634191 / 62500000000)) := by
  have h := reflection_log_2009_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2010_neg : (1710371 / 250000000) ≤ -Real.log (62073866551 / 62500000000) ∧
    -Real.log (62073866551 / 62500000000) ≤ (1368297 / 200000000) := by
  have h := checkLog_sound (w := (426133449 / 124573866551)) (n := 12)
    (lo := (1710371 / 250000000)) (hi := (1368297 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62073866551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62073866551) = 1/(62073866551 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2010 : Bounds (-1368297 / 200000000) (-1710371 / 250000000) (Real.log (62073866551 / 62500000000)) := by
  have h := reflection_log_2010_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2011_neg : (165520867 / 1000000000) ≤ -Real.log (500000000000 / 590003793213) ∧
    -Real.log (500000000000 / 590003793213) ≤ (41380217 / 250000000) := by
  have h := checkLog_sound (w := (90003793213 / 1090003793213)) (n := 12)
    (lo := (165520867 / 1000000000)) (hi := (41380217 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590003793213 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590003793213 / 500000000000) = 1/(500000000000 / 590003793213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2011 : Bounds (165520867 / 1000000000) (41380217 / 250000000) (Real.log (590003793213 / 500000000000)) := by
  have h := reflection_log_2011_neg
  have he : Real.log (590003793213 / 500000000000) = -Real.log (500000000000 / 590003793213) := by
    rw [show ((590003793213 / 500000000000) : ℝ) = ((500000000000 / 590003793213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2012_neg : (165955841 / 1000000000) ≤ -Real.log (125000000000 / 147565121259) ∧
    -Real.log (125000000000 / 147565121259) ≤ (82977921 / 500000000) := by
  have h := checkLog_sound (w := (22565121259 / 272565121259)) (n := 12)
    (lo := (165955841 / 1000000000)) (hi := (82977921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147565121259 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147565121259 / 125000000000) = 1/(125000000000 / 147565121259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2012 : Bounds (165955841 / 1000000000) (82977921 / 500000000) (Real.log (147565121259 / 125000000000)) := by
  have h := reflection_log_2012_neg
  have he : Real.log (147565121259 / 125000000000) = -Real.log (125000000000 / 147565121259) := by
    rw [show ((147565121259 / 125000000000) : ℝ) = ((125000000000 / 147565121259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2013_neg : (332016741 / 1000000000) ≤ -Real.log (500000000000 / 696888090963) ∧
    -Real.log (500000000000 / 696888090963) ≤ (166008371 / 500000000) := by
  have h := checkLog_sound (w := (196888090963 / 1196888090963)) (n := 12)
    (lo := (332016741 / 1000000000)) (hi := (166008371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696888090963 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696888090963 / 500000000000) = 1/(500000000000 / 696888090963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2013 : Bounds (332016741 / 1000000000) (166008371 / 500000000) (Real.log (696888090963 / 500000000000)) := by
  have h := reflection_log_2013_neg
  have he : Real.log (696888090963 / 500000000000) = -Real.log (500000000000 / 696888090963) := by
    rw [show ((696888090963 / 500000000000) : ℝ) = ((500000000000 / 696888090963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2014_neg : (332222307 / 1000000000) ≤ -Real.log (250000000000 / 348515681111) ∧
    -Real.log (250000000000 / 348515681111) ≤ (83055577 / 250000000) := by
  have h := checkLog_sound (w := (98515681111 / 598515681111)) (n := 12)
    (lo := (332222307 / 1000000000)) (hi := (83055577 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((348515681111 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(348515681111 / 250000000000) = 1/(250000000000 / 348515681111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2014 : Bounds (332222307 / 1000000000) (83055577 / 250000000) (Real.log (348515681111 / 250000000000)) := by
  have h := reflection_log_2014_neg
  have he : Real.log (348515681111 / 250000000000) = -Real.log (250000000000 / 348515681111) := by
    rw [show ((348515681111 / 250000000000) : ℝ) = ((250000000000 / 348515681111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2015_neg : (152463543 / 1000000000) ≤ -Real.log (10000 / 11647) ∧
    -Real.log (10000 / 11647) ≤ (19057943 / 125000000) := by
  have h := checkLog_sound (w := (1647 / 21647)) (n := 12)
    (lo := (152463543 / 1000000000)) (hi := (19057943 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11647 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11647 / 10000) = 1/(10000 / 11647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2015 : Bounds (152463543 / 1000000000) (19057943 / 125000000) (Real.log (11647 / 10000)) := by
  have h := reflection_log_2015_neg
  have he : Real.log (11647 / 10000) = -Real.log (10000 / 11647) := by
    rw [show ((11647 / 10000) : ℝ) = ((10000 / 11647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2016_neg : (179964337 / 1000000000) ≤ -Real.log (8353 / 10000) ∧
    -Real.log (8353 / 10000) ≤ (89982169 / 500000000) := by
  have h := checkLog_sound (w := (1647 / 18353)) (n := 12)
    (lo := (179964337 / 1000000000)) (hi := (89982169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8353) = 1/(8353 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2016 : Bounds (-89982169 / 500000000) (-179964337 / 1000000000) (Real.log (8353 / 10000)) := by
  have h := reflection_log_2016_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2017_neg : (82343 / 500000000) ≤ -Real.log (10000000 / 10001647) ∧
    -Real.log (10000000 / 10001647) ≤ (164687 / 1000000000) := by
  have h := checkLog_sound (w := (1647 / 20001647)) (n := 12)
    (lo := (82343 / 500000000)) (hi := (164687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001647 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001647 / 10000000) = 1/(10000000 / 10001647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2017 : Bounds (82343 / 500000000) (164687 / 1000000000) (Real.log (10001647 / 10000000)) := by
  have h := reflection_log_2017_neg
  have he : Real.log (10001647 / 10000000) = -Real.log (10000000 / 10001647) := by
    rw [show ((10001647 / 10000000) : ℝ) = ((10000000 / 10001647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2018_neg : (164713 / 1000000000) ≤ -Real.log (9998353 / 10000000) ∧
    -Real.log (9998353 / 10000000) ≤ (82357 / 500000000) := by
  have h := checkLog_sound (w := (1647 / 19998353)) (n := 12)
    (lo := (164713 / 1000000000)) (hi := (82357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998353) = 1/(9998353 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2018 : Bounds (-82357 / 500000000) (-164713 / 1000000000) (Real.log (9998353 / 10000000)) := by
  have h := reflection_log_2018_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2019_neg : (198467 / 2500000) ≤ -Real.log (1000000 / 1082623) ∧
    -Real.log (1000000 / 1082623) ≤ (79386801 / 1000000000) := by
  have h := checkLog_sound (w := (82623 / 2082623)) (n := 12)
    (lo := (198467 / 2500000)) (hi := (79386801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082623 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082623 / 1000000) = 1/(1000000 / 1082623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2019 : Bounds (198467 / 2500000) (79386801 / 1000000000) (Real.log (1082623 / 1000000)) := by
  have h := reflection_log_2019_neg
  have he : Real.log (1082623 / 1000000) = -Real.log (1000000 / 1082623) := by
    rw [show ((1082623 / 1000000) : ℝ) = ((1000000 / 1082623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2020_neg : (86236767 / 1000000000) ≤ -Real.log (917377 / 1000000) ∧
    -Real.log (917377 / 1000000) ≤ (2694899 / 31250000) := by
  have h := checkLog_sound (w := (82623 / 1917377)) (n := 12)
    (lo := (86236767 / 1000000000)) (hi := (2694899 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917377) = 1/(917377 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2020 : Bounds (-2694899 / 31250000) (-86236767 / 1000000000) (Real.log (917377 / 1000000)) := by
  have h := reflection_log_2020_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2021_neg : (15917259 / 200000000) ≤ -Real.log (1000000 / 1082839) ∧
    -Real.log (1000000 / 1082839) ≤ (9948287 / 125000000) := by
  have h := checkLog_sound (w := (82839 / 2082839)) (n := 12)
    (lo := (15917259 / 200000000)) (hi := (9948287 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082839 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082839 / 1000000) = 1/(1000000 / 1082839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2021 : Bounds (15917259 / 200000000) (9948287 / 125000000) (Real.log (1082839 / 1000000)) := by
  have h := reflection_log_2021_neg
  have he : Real.log (1082839 / 1000000) = -Real.log (1000000 / 1082839) := by
    rw [show ((1082839 / 1000000) : ℝ) = ((1000000 / 1082839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2022_neg : (86472249 / 1000000000) ≤ -Real.log (917161 / 1000000) ∧
    -Real.log (917161 / 1000000) ≤ (345889 / 4000000) := by
  have h := checkLog_sound (w := (82839 / 1917161)) (n := 12)
    (lo := (86472249 / 1000000000)) (hi := (345889 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917161) = 1/(917161 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2022 : Bounds (-345889 / 4000000) (-86472249 / 1000000000) (Real.log (917161 / 1000000)) := by
  have h := reflection_log_2022_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2023_neg : (6885953 / 1000000000) ≤ -Real.log (993137700079 / 1000000000000) ∧
    -Real.log (993137700079 / 1000000000000) ≤ (3442977 / 500000000) := by
  have h := checkLog_sound (w := (6862299921 / 1993137700079)) (n := 12)
    (lo := (6885953 / 1000000000)) (hi := (3442977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993137700079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993137700079) = 1/(993137700079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2023 : Bounds (-3442977 / 500000000) (-6885953 / 1000000000) (Real.log (993137700079 / 1000000000000)) := by
  have h := reflection_log_2023_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2024_neg : (6849967 / 1000000000) ≤ -Real.log (993173439871 / 1000000000000) ∧
    -Real.log (993173439871 / 1000000000000) ≤ (428123 / 62500000) := by
  have h := checkLog_sound (w := (6826560129 / 1993173439871)) (n := 12)
    (lo := (6849967 / 1000000000)) (hi := (428123 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993173439871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993173439871) = 1/(993173439871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2024 : Bounds (-428123 / 62500000) (-6849967 / 1000000000) (Real.log (993173439871 / 1000000000000)) := by
  have h := reflection_log_2024_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2025_neg : (10351473 / 62500000) ≤ -Real.log (500000000000 / 590064390103) ∧
    -Real.log (500000000000 / 590064390103) ≤ (165623569 / 1000000000) := by
  have h := checkLog_sound (w := (90064390103 / 1090064390103)) (n := 12)
    (lo := (10351473 / 62500000)) (hi := (165623569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590064390103 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590064390103 / 500000000000) = 1/(500000000000 / 590064390103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2025 : Bounds (10351473 / 62500000) (165623569 / 1000000000) (Real.log (590064390103 / 500000000000)) := by
  have h := reflection_log_2025_neg
  have he : Real.log (590064390103 / 500000000000) = -Real.log (500000000000 / 590064390103) := by
    rw [show ((590064390103 / 500000000000) : ℝ) = ((500000000000 / 590064390103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2026_neg : (33211709 / 200000000) ≤ -Real.log (500000000000 / 590321110471) ∧
    -Real.log (500000000000 / 590321110471) ≤ (83029273 / 500000000) := by
  have h := checkLog_sound (w := (90321110471 / 1090321110471)) (n := 12)
    (lo := (33211709 / 200000000)) (hi := (83029273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590321110471 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590321110471 / 500000000000) = 1/(500000000000 / 590321110471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2026 : Bounds (33211709 / 200000000) (83029273 / 500000000) (Real.log (590321110471 / 500000000000)) := by
  have h := reflection_log_2026_neg
  have he : Real.log (590321110471 / 500000000000) = -Real.log (500000000000 / 590321110471) := by
    rw [show ((590321110471 / 500000000000) : ℝ) = ((500000000000 / 590321110471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2027_neg : (332222307 / 1000000000) ≤ -Real.log (500000000000 / 697031362221) ∧
    -Real.log (500000000000 / 697031362221) ≤ (83055577 / 250000000) := by
  have h := checkLog_sound (w := (197031362221 / 1197031362221)) (n := 12)
    (lo := (332222307 / 1000000000)) (hi := (83055577 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697031362221 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697031362221 / 500000000000) = 1/(500000000000 / 697031362221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2027 : Bounds (332222307 / 1000000000) (83055577 / 250000000) (Real.log (697031362221 / 500000000000)) := by
  have h := reflection_log_2027_neg
  have he : Real.log (697031362221 / 500000000000) = -Real.log (500000000000 / 697031362221) := by
    rw [show ((697031362221 / 500000000000) : ℝ) = ((500000000000 / 697031362221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2028_neg : (8310697 / 25000000) ≤ -Real.log (100000000000 / 139434933557) ∧
    -Real.log (100000000000 / 139434933557) ≤ (332427881 / 1000000000) := by
  have h := checkLog_sound (w := (39434933557 / 239434933557)) (n := 12)
    (lo := (8310697 / 25000000)) (hi := (332427881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139434933557 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139434933557 / 100000000000) = 1/(100000000000 / 139434933557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2028 : Bounds (8310697 / 25000000) (332427881 / 1000000000) (Real.log (139434933557 / 100000000000)) := by
  have h := reflection_log_2028_neg
  have he : Real.log (139434933557 / 100000000000) = -Real.log (100000000000 / 139434933557) := by
    rw [show ((139434933557 / 100000000000) : ℝ) = ((100000000000 / 139434933557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2029_neg : (76274699 / 500000000) ≤ -Real.log (625 / 728) ∧
    -Real.log (625 / 728) ≤ (152549399 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 1353)) (n := 12)
    (lo := (76274699 / 500000000)) (hi := (152549399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((728 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(728 / 625) = 1/(625 / 728) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2029 : Bounds (76274699 / 500000000) (152549399 / 1000000000) (Real.log (728 / 625)) := by
  have h := reflection_log_2029_neg
  have he : Real.log (728 / 625) = -Real.log (625 / 728) := by
    rw [show ((728 / 625) : ℝ) = ((625 / 728) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2030_neg : (180084061 / 1000000000) ≤ -Real.log (522 / 625) ∧
    -Real.log (522 / 625) ≤ (90042031 / 500000000) := by
  have h := checkLog_sound (w := (103 / 1147)) (n := 12)
    (lo := (180084061 / 1000000000)) (hi := (90042031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 522) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 522) = 1/(522 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2030 : Bounds (-90042031 / 500000000) (-180084061 / 1000000000) (Real.log (522 / 625)) := by
  have h := reflection_log_2030_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2031_neg : (82393 / 500000000) ≤ -Real.log (625000 / 625103) ∧
    -Real.log (625000 / 625103) ≤ (164787 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 1250103)) (n := 12)
    (lo := (82393 / 500000000)) (hi := (164787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625103 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625103 / 625000) = 1/(625000 / 625103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2031 : Bounds (82393 / 500000000) (164787 / 1000000000) (Real.log (625103 / 625000)) := by
  have h := reflection_log_2031_neg
  have he : Real.log (625103 / 625000) = -Real.log (625000 / 625103) := by
    rw [show ((625103 / 625000) : ℝ) = ((625000 / 625103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2032_neg : (164813 / 1000000000) ≤ -Real.log (624897 / 625000) ∧
    -Real.log (624897 / 625000) ≤ (82407 / 500000000) := by
  have h := checkLog_sound (w := (103 / 1249897)) (n := 12)
    (lo := (164813 / 1000000000)) (hi := (82407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624897) = 1/(624897 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2032 : Bounds (-82407 / 500000000) (-164813 / 1000000000) (Real.log (624897 / 625000)) := by
  have h := reflection_log_2032_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2033_neg : (79433907 / 1000000000) ≤ -Real.log (500000 / 541337) ∧
    -Real.log (500000 / 541337) ≤ (19858477 / 250000000) := by
  have h := checkLog_sound (w := (41337 / 1041337)) (n := 12)
    (lo := (79433907 / 1000000000)) (hi := (19858477 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541337 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541337 / 500000) = 1/(500000 / 541337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2033 : Bounds (79433907 / 1000000000) (19858477 / 250000000) (Real.log (541337 / 500000)) := by
  have h := reflection_log_2033_neg
  have he : Real.log (541337 / 500000) = -Real.log (500000 / 541337) := by
    rw [show ((541337 / 500000) : ℝ) = ((500000 / 541337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2034_neg : (43146181 / 500000000) ≤ -Real.log (458663 / 500000) ∧
    -Real.log (458663 / 500000) ≤ (86292363 / 1000000000) := by
  have h := checkLog_sound (w := (41337 / 958663)) (n := 12)
    (lo := (43146181 / 500000000)) (hi := (86292363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458663) = 1/(458663 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2034 : Bounds (-86292363 / 1000000000) (-43146181 / 500000000) (Real.log (458663 / 500000)) := by
  have h := reflection_log_2034_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2035_neg : (79632469 / 1000000000) ≤ -Real.log (1000000 / 1082889) ∧
    -Real.log (1000000 / 1082889) ≤ (7963247 / 100000000) := by
  have h := checkLog_sound (w := (82889 / 2082889)) (n := 12)
    (lo := (79632469 / 1000000000)) (hi := (7963247 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082889 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082889 / 1000000) = 1/(1000000 / 1082889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2035 : Bounds (79632469 / 1000000000) (7963247 / 100000000) (Real.log (1082889 / 1000000)) := by
  have h := reflection_log_2035_neg
  have he : Real.log (1082889 / 1000000) = -Real.log (1000000 / 1082889) := by
    rw [show ((1082889 / 1000000) : ℝ) = ((1000000 / 1082889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2036_neg : (86526767 / 1000000000) ≤ -Real.log (917111 / 1000000) ∧
    -Real.log (917111 / 1000000) ≤ (5407923 / 62500000) := by
  have h := checkLog_sound (w := (82889 / 1917111)) (n := 12)
    (lo := (86526767 / 1000000000)) (hi := (5407923 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917111) = 1/(917111 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2036 : Bounds (-5407923 / 62500000) (-86526767 / 1000000000) (Real.log (917111 / 1000000)) := by
  have h := reflection_log_2036_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2037_neg : (6894297 / 1000000000) ≤ -Real.log (993129413679 / 1000000000000) ∧
    -Real.log (993129413679 / 1000000000000) ≤ (3447149 / 500000000) := by
  have h := checkLog_sound (w := (6870586321 / 1993129413679)) (n := 12)
    (lo := (6894297 / 1000000000)) (hi := (3447149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993129413679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993129413679) = 1/(993129413679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2037 : Bounds (-3447149 / 500000000) (-6894297 / 1000000000) (Real.log (993129413679 / 1000000000000)) := by
  have h := reflection_log_2037_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2038_neg : (1371691 / 200000000) ≤ -Real.log (248291252431 / 250000000000) ∧
    -Real.log (248291252431 / 250000000000) ≤ (857307 / 125000000) := by
  have h := checkLog_sound (w := (1708747569 / 498291252431)) (n := 12)
    (lo := (1371691 / 200000000)) (hi := (857307 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248291252431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248291252431) = 1/(248291252431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2038 : Bounds (-857307 / 125000000) (-1371691 / 200000000) (Real.log (248291252431 / 250000000000)) := by
  have h := reflection_log_2038_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2039_neg : (165726269 / 1000000000) ≤ -Real.log (500000000000 / 590124993731) ∧
    -Real.log (500000000000 / 590124993731) ≤ (16572627 / 100000000) := by
  have h := checkLog_sound (w := (90124993731 / 1090124993731)) (n := 12)
    (lo := (165726269 / 1000000000)) (hi := (16572627 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590124993731 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590124993731 / 500000000000) = 1/(500000000000 / 590124993731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2039 : Bounds (165726269 / 1000000000) (16572627 / 100000000) (Real.log (590124993731 / 500000000000)) := by
  have h := reflection_log_2039_neg
  have he : Real.log (590124993731 / 500000000000) = -Real.log (500000000000 / 590124993731) := by
    rw [show ((590124993731 / 500000000000) : ℝ) = ((500000000000 / 590124993731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2040_neg : (41539809 / 250000000) ≤ -Real.log (250000000000 / 295190276859) ∧
    -Real.log (250000000000 / 295190276859) ≤ (166159237 / 1000000000) := by
  have h := checkLog_sound (w := (45190276859 / 545190276859)) (n := 12)
    (lo := (41539809 / 250000000)) (hi := (166159237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295190276859 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295190276859 / 250000000000) = 1/(250000000000 / 295190276859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2040 : Bounds (41539809 / 250000000) (166159237 / 1000000000) (Real.log (295190276859 / 250000000000)) := by
  have h := reflection_log_2040_neg
  have he : Real.log (295190276859 / 250000000000) = -Real.log (250000000000 / 295190276859) := by
    rw [show ((295190276859 / 250000000000) : ℝ) = ((250000000000 / 295190276859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2041_neg : (8310697 / 25000000) ≤ -Real.log (62500000000 / 87146833473) ∧
    -Real.log (62500000000 / 87146833473) ≤ (332427881 / 1000000000) := by
  have h := checkLog_sound (w := (24646833473 / 149646833473)) (n := 12)
    (lo := (8310697 / 25000000)) (hi := (332427881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87146833473 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87146833473 / 62500000000) = 1/(62500000000 / 87146833473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2041 : Bounds (8310697 / 25000000) (332427881 / 1000000000) (Real.log (87146833473 / 62500000000)) := by
  have h := reflection_log_2041_neg
  have he : Real.log (87146833473 / 62500000000) = -Real.log (62500000000 / 87146833473) := by
    rw [show ((87146833473 / 62500000000) : ℝ) = ((62500000000 / 87146833473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2042_neg : (16631673 / 50000000) ≤ -Real.log (500000000000 / 697318007663) ∧
    -Real.log (500000000000 / 697318007663) ≤ (332633461 / 1000000000) := by
  have h := checkLog_sound (w := (197318007663 / 1197318007663)) (n := 12)
    (lo := (16631673 / 50000000)) (hi := (332633461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697318007663 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697318007663 / 500000000000) = 1/(500000000000 / 697318007663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2042 : Bounds (16631673 / 50000000) (332633461 / 1000000000) (Real.log (697318007663 / 500000000000)) := by
  have h := reflection_log_2042_neg
  have he : Real.log (697318007663 / 500000000000) = -Real.log (500000000000 / 697318007663) := by
    rw [show ((697318007663 / 500000000000) : ℝ) = ((500000000000 / 697318007663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2043_neg : (76317623 / 500000000) ≤ -Real.log (10000 / 11649) ∧
    -Real.log (10000 / 11649) ≤ (152635247 / 1000000000) := by
  have h := checkLog_sound (w := (1649 / 21649)) (n := 12)
    (lo := (76317623 / 500000000)) (hi := (152635247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11649 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11649 / 10000) = 1/(10000 / 11649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2043 : Bounds (76317623 / 500000000) (152635247 / 1000000000) (Real.log (11649 / 10000)) := by
  have h := reflection_log_2043_neg
  have he : Real.log (11649 / 10000) = -Real.log (10000 / 11649) := by
    rw [show ((11649 / 10000) : ℝ) = ((10000 / 11649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2044_neg : (901019 / 5000000) ≤ -Real.log (8351 / 10000) ∧
    -Real.log (8351 / 10000) ≤ (180203801 / 1000000000) := by
  have h := checkLog_sound (w := (1649 / 18351)) (n := 12)
    (lo := (901019 / 5000000)) (hi := (180203801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8351) = 1/(8351 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2044 : Bounds (-180203801 / 1000000000) (-901019 / 5000000) (Real.log (8351 / 10000)) := by
  have h := reflection_log_2044_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2045_neg : (82443 / 500000000) ≤ -Real.log (10000000 / 10001649) ∧
    -Real.log (10000000 / 10001649) ≤ (164887 / 1000000000) := by
  have h := checkLog_sound (w := (1649 / 20001649)) (n := 12)
    (lo := (82443 / 500000000)) (hi := (164887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001649 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001649 / 10000000) = 1/(10000000 / 10001649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2045 : Bounds (82443 / 500000000) (164887 / 1000000000) (Real.log (10001649 / 10000000)) := by
  have h := reflection_log_2045_neg
  have he : Real.log (10001649 / 10000000) = -Real.log (10000000 / 10001649) := by
    rw [show ((10001649 / 10000000) : ℝ) = ((10000000 / 10001649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2046_neg : (164913 / 1000000000) ≤ -Real.log (9998351 / 10000000) ∧
    -Real.log (9998351 / 10000000) ≤ (82457 / 500000000) := by
  have h := checkLog_sound (w := (1649 / 19998351)) (n := 12)
    (lo := (164913 / 1000000000)) (hi := (82457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998351) = 1/(9998351 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2046 : Bounds (-82457 / 500000000) (-164913 / 1000000000) (Real.log (9998351 / 10000000)) := by
  have h := reflection_log_2046_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2047_neg : (79480087 / 1000000000) ≤ -Real.log (250000 / 270681) ∧
    -Real.log (250000 / 270681) ≤ (9935011 / 125000000) := by
  have h := checkLog_sound (w := (20681 / 520681)) (n := 12)
    (lo := (79480087 / 1000000000)) (hi := (9935011 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270681 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270681 / 250000) = 1/(250000 / 270681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2047 : Bounds (79480087 / 1000000000) (9935011 / 125000000) (Real.log (270681 / 250000)) := by
  have h := reflection_log_2047_neg
  have he : Real.log (270681 / 250000) = -Real.log (250000 / 270681) := by
    rw [show ((270681 / 250000) : ℝ) = ((250000 / 270681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


