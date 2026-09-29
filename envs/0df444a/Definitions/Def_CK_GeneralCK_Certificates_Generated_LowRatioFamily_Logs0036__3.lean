-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0036__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0036__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T07:54:39.502133+00:00
-- url     : https://prove2.me/theorems/907726b1-3cbe-4b17-af0d-f523b7298545
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0036 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0037, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0036 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0037, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0038)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0036 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0037, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0038)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0036 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0037, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0038) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0036 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0037, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0038).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0036 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2304_neg : (438733 / 62500000) ≤ -Real.log (993004852231 / 1000000000000) ∧
    -Real.log (993004852231 / 1000000000000) ≤ (7019729 / 1000000000) := by
  have h := checkLog_sound (w := (6995147769 / 1993004852231)) (n := 12)
    (lo := (438733 / 62500000)) (hi := (7019729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993004852231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993004852231) = 1/(993004852231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2304 : Bounds (-7019729 / 1000000000) (-438733 / 62500000) (Real.log (993004852231 / 1000000000000)) := by
  have h := reflection_log_2304_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2305_neg : (2095821 / 12500000) ≤ -Real.log (62500000000 / 73908824887) ∧
    -Real.log (62500000000 / 73908824887) ≤ (167665681 / 1000000000) := by
  have h := checkLog_sound (w := (11408824887 / 136408824887)) (n := 12)
    (lo := (2095821 / 12500000)) (hi := (167665681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73908824887 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73908824887 / 62500000000) = 1/(62500000000 / 73908824887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2305 : Bounds (2095821 / 12500000) (167665681 / 1000000000) (Real.log (73908824887 / 62500000000)) := by
  have h := reflection_log_2305_neg
  have he : Real.log (73908824887 / 62500000000) = -Real.log (62500000000 / 73908824887) := by
    rw [show ((73908824887 / 62500000000) : ℝ) = ((62500000000 / 73908824887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2306_neg : (4202619 / 25000000) ≤ -Real.log (31250000000 / 36970641929) ∧
    -Real.log (31250000000 / 36970641929) ≤ (168104761 / 1000000000) := by
  have h := checkLog_sound (w := (5720641929 / 68220641929)) (n := 12)
    (lo := (4202619 / 25000000)) (hi := (168104761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36970641929 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36970641929 / 31250000000) = 1/(31250000000 / 36970641929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2306 : Bounds (4202619 / 25000000) (168104761 / 1000000000) (Real.log (36970641929 / 31250000000)) := by
  have h := reflection_log_2306_neg
  have he : Real.log (36970641929 / 31250000000) = -Real.log (31250000000 / 36970641929) := by
    rw [show ((36970641929 / 31250000000) : ℝ) = ((31250000000 / 36970641929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2307_neg : (67267019 / 200000000) ≤ -Real.log (500000000000 / 699904007679) ∧
    -Real.log (500000000000 / 699904007679) ≤ (42041887 / 125000000) := by
  have h := checkLog_sound (w := (199904007679 / 1199904007679)) (n := 12)
    (lo := (67267019 / 200000000)) (hi := (42041887 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699904007679 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699904007679 / 500000000000) = 1/(500000000000 / 699904007679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2307 : Bounds (67267019 / 200000000) (42041887 / 125000000) (Real.log (699904007679 / 500000000000)) := by
  have h := reflection_log_2307_neg
  have he : Real.log (699904007679 / 500000000000) = -Real.log (500000000000 / 699904007679) := by
    rw [show ((699904007679 / 500000000000) : ℝ) = ((500000000000 / 699904007679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2308_neg : (42067601 / 125000000) ≤ -Real.log (500000000000 / 700048001921) ∧
    -Real.log (500000000000 / 700048001921) ≤ (336540809 / 1000000000) := by
  have h := checkLog_sound (w := (200048001921 / 1200048001921)) (n := 12)
    (lo := (42067601 / 125000000)) (hi := (336540809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((700048001921 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(700048001921 / 500000000000) = 1/(500000000000 / 700048001921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2308 : Bounds (42067601 / 125000000) (336540809 / 1000000000) (Real.log (700048001921 / 500000000000)) := by
  have h := reflection_log_2308_neg
  have he : Real.log (700048001921 / 500000000000) = -Real.log (500000000000 / 700048001921) := by
    rw [show ((700048001921 / 500000000000) : ℝ) = ((500000000000 / 700048001921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2309_neg : (154264959 / 1000000000) ≤ -Real.log (2500 / 2917) ∧
    -Real.log (2500 / 2917) ≤ (241039 / 1562500) := by
  have h := checkLog_sound (w := (417 / 5417)) (n := 12)
    (lo := (154264959 / 1000000000)) (hi := (241039 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2917 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2917 / 2500) = 1/(2500 / 2917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2309 : Bounds (154264959 / 1000000000) (241039 / 1562500) (Real.log (2917 / 2500)) := by
  have h := reflection_log_2309_neg
  have he : Real.log (2917 / 2500) = -Real.log (2500 / 2917) := by
    rw [show ((2917 / 2500) : ℝ) = ((2500 / 2917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2310_neg : (182481569 / 1000000000) ≤ -Real.log (2083 / 2500) ∧
    -Real.log (2083 / 2500) ≤ (18248157 / 100000000) := by
  have h := checkLog_sound (w := (417 / 4583)) (n := 12)
    (lo := (182481569 / 1000000000)) (hi := (18248157 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2083) = 1/(2083 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2310 : Bounds (-18248157 / 100000000) (-182481569 / 1000000000) (Real.log (2083 / 2500)) := by
  have h := reflection_log_2310_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2311_neg : (83393 / 500000000) ≤ -Real.log (2500000 / 2500417) ∧
    -Real.log (2500000 / 2500417) ≤ (166787 / 1000000000) := by
  have h := checkLog_sound (w := (417 / 5000417)) (n := 12)
    (lo := (83393 / 500000000)) (hi := (166787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500417 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500417 / 2500000) = 1/(2500000 / 2500417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2311 : Bounds (83393 / 500000000) (166787 / 1000000000) (Real.log (2500417 / 2500000)) := by
  have h := reflection_log_2311_neg
  have he : Real.log (2500417 / 2500000) = -Real.log (2500000 / 2500417) := by
    rw [show ((2500417 / 2500000) : ℝ) = ((2500000 / 2500417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2312_neg : (166813 / 1000000000) ≤ -Real.log (2499583 / 2500000) ∧
    -Real.log (2499583 / 2500000) ≤ (83407 / 500000000) := by
  have h := checkLog_sound (w := (417 / 4999583)) (n := 12)
    (lo := (166813 / 1000000000)) (hi := (83407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499583) = 1/(2499583 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2312 : Bounds (-83407 / 500000000) (-166813 / 1000000000) (Real.log (2499583 / 2500000)) := by
  have h := reflection_log_2312_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2313_neg : (40185019 / 500000000) ≤ -Real.log (125000 / 135461) ∧
    -Real.log (125000 / 135461) ≤ (80370039 / 1000000000) := by
  have h := checkLog_sound (w := (10461 / 260461)) (n := 12)
    (lo := (40185019 / 500000000)) (hi := (80370039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135461 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135461 / 125000) = 1/(125000 / 135461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2313 : Bounds (40185019 / 500000000) (80370039 / 1000000000) (Real.log (135461 / 125000)) := by
  have h := reflection_log_2313_neg
  have he : Real.log (135461 / 125000) = -Real.log (125000 / 135461) := by
    rw [show ((135461 / 125000) : ℝ) = ((125000 / 135461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2314_neg : (2184959 / 25000000) ≤ -Real.log (114539 / 125000) ∧
    -Real.log (114539 / 125000) ≤ (87398361 / 1000000000) := by
  have h := checkLog_sound (w := (10461 / 239539)) (n := 12)
    (lo := (2184959 / 25000000)) (hi := (87398361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 114539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 114539) = 1/(114539 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2314 : Bounds (-87398361 / 1000000000) (-2184959 / 25000000) (Real.log (114539 / 125000)) := by
  have h := reflection_log_2314_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2315_neg : (4028513 / 50000000) ≤ -Real.log (200000 / 216781) ∧
    -Real.log (200000 / 216781) ≤ (80570261 / 1000000000) := by
  have h := checkLog_sound (w := (16781 / 416781)) (n := 12)
    (lo := (4028513 / 50000000)) (hi := (80570261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216781 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216781 / 200000) = 1/(200000 / 216781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2315 : Bounds (4028513 / 50000000) (80570261 / 1000000000) (Real.log (216781 / 200000)) := by
  have h := reflection_log_2315_neg
  have he : Real.log (216781 / 200000) = -Real.log (200000 / 216781) := by
    rw [show ((216781 / 200000) : ℝ) = ((200000 / 216781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2316_neg : (87635207 / 1000000000) ≤ -Real.log (183219 / 200000) ∧
    -Real.log (183219 / 200000) ≤ (10954401 / 125000000) := by
  have h := checkLog_sound (w := (16781 / 383219)) (n := 12)
    (lo := (87635207 / 1000000000)) (hi := (10954401 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183219) = 1/(183219 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2316 : Bounds (-10954401 / 125000000) (-87635207 / 1000000000) (Real.log (183219 / 200000)) := by
  have h := reflection_log_2316_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2317_neg : (7064947 / 1000000000) ≤ -Real.log (39718398039 / 40000000000) ∧
    -Real.log (39718398039 / 40000000000) ≤ (1766237 / 250000000) := by
  have h := checkLog_sound (w := (281601961 / 79718398039)) (n := 12)
    (lo := (7064947 / 1000000000)) (hi := (1766237 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39718398039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39718398039) = 1/(39718398039 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2317 : Bounds (-1766237 / 250000000) (-7064947 / 1000000000) (Real.log (39718398039 / 40000000000)) := by
  have h := reflection_log_2317_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2318_neg : (3514161 / 500000000) ≤ -Real.log (15515567479 / 15625000000) ∧
    -Real.log (15515567479 / 15625000000) ≤ (7028323 / 1000000000) := by
  have h := checkLog_sound (w := (109432521 / 31140567479)) (n := 12)
    (lo := (3514161 / 500000000)) (hi := (7028323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15515567479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15515567479) = 1/(15515567479 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2318 : Bounds (-7028323 / 1000000000) (-3514161 / 500000000) (Real.log (15515567479 / 15625000000)) := by
  have h := reflection_log_2318_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2319_neg : (167768399 / 1000000000) ≤ -Real.log (125000000000 / 147832834231) ∧
    -Real.log (125000000000 / 147832834231) ≤ (419421 / 2500000) := by
  have h := checkLog_sound (w := (22832834231 / 272832834231)) (n := 12)
    (lo := (167768399 / 1000000000)) (hi := (419421 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147832834231 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147832834231 / 125000000000) = 1/(125000000000 / 147832834231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2319 : Bounds (167768399 / 1000000000) (419421 / 2500000) (Real.log (147832834231 / 125000000000)) := by
  have h := reflection_log_2319_neg
  have he : Real.log (147832834231 / 125000000000) = -Real.log (125000000000 / 147832834231) := by
    rw [show ((147832834231 / 125000000000) : ℝ) = ((125000000000 / 147832834231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2320_neg : (42051367 / 250000000) ≤ -Real.log (31250000000 / 36974365377) ∧
    -Real.log (31250000000 / 36974365377) ≤ (168205469 / 1000000000) := by
  have h := checkLog_sound (w := (5724365377 / 68224365377)) (n := 12)
    (lo := (42051367 / 250000000)) (hi := (168205469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36974365377 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36974365377 / 31250000000) = 1/(31250000000 / 36974365377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2320 : Bounds (42051367 / 250000000) (168205469 / 1000000000) (Real.log (36974365377 / 31250000000)) := by
  have h := reflection_log_2320_neg
  have he : Real.log (36974365377 / 31250000000) = -Real.log (31250000000 / 36974365377) := by
    rw [show ((36974365377 / 31250000000) : ℝ) = ((31250000000 / 36974365377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2321_neg : (42067601 / 125000000) ≤ -Real.log (781250000 / 1093825003) ∧
    -Real.log (781250000 / 1093825003) ≤ (336540809 / 1000000000) := by
  have h := checkLog_sound (w := (312575003 / 1875075003)) (n := 12)
    (lo := (42067601 / 125000000)) (hi := (336540809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093825003 / 781250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093825003 / 781250000) = 1/(781250000 / 1093825003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2321 : Bounds (42067601 / 125000000) (336540809 / 1000000000) (Real.log (1093825003 / 781250000)) := by
  have h := reflection_log_2321_neg
  have he : Real.log (1093825003 / 781250000) = -Real.log (781250000 / 1093825003) := by
    rw [show ((1093825003 / 781250000) : ℝ) = ((781250000 / 1093825003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2322_neg : (10523329 / 31250000) ≤ -Real.log (20000000000 / 28007681229) ∧
    -Real.log (20000000000 / 28007681229) ≤ (336746529 / 1000000000) := by
  have h := checkLog_sound (w := (8007681229 / 48007681229)) (n := 12)
    (lo := (10523329 / 31250000)) (hi := (336746529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28007681229 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28007681229 / 20000000000) = 1/(20000000000 / 28007681229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2322 : Bounds (10523329 / 31250000) (336746529 / 1000000000) (Real.log (28007681229 / 20000000000)) := by
  have h := reflection_log_2322_neg
  have he : Real.log (28007681229 / 20000000000) = -Real.log (20000000000 / 28007681229) := by
    rw [show ((28007681229 / 20000000000) : ℝ) = ((20000000000 / 28007681229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2323_neg : (154350659 / 1000000000) ≤ -Real.log (10000 / 11669) ∧
    -Real.log (10000 / 11669) ≤ (7717533 / 50000000) := by
  have h := checkLog_sound (w := (1669 / 21669)) (n := 12)
    (lo := (154350659 / 1000000000)) (hi := (7717533 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11669 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11669 / 10000) = 1/(10000 / 11669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2323 : Bounds (154350659 / 1000000000) (7717533 / 50000000) (Real.log (11669 / 10000)) := by
  have h := reflection_log_2323_neg
  have he : Real.log (11669 / 10000) = -Real.log (10000 / 11669) := by
    rw [show ((11669 / 10000) : ℝ) = ((10000 / 11669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2324_neg : (45650399 / 250000000) ≤ -Real.log (8331 / 10000) ∧
    -Real.log (8331 / 10000) ≤ (182601597 / 1000000000) := by
  have h := checkLog_sound (w := (1669 / 18331)) (n := 12)
    (lo := (45650399 / 250000000)) (hi := (182601597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8331) = 1/(8331 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2324 : Bounds (-182601597 / 1000000000) (-45650399 / 250000000) (Real.log (8331 / 10000)) := by
  have h := reflection_log_2324_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2325_neg : (83443 / 500000000) ≤ -Real.log (10000000 / 10001669) ∧
    -Real.log (10000000 / 10001669) ≤ (166887 / 1000000000) := by
  have h := checkLog_sound (w := (1669 / 20001669)) (n := 12)
    (lo := (83443 / 500000000)) (hi := (166887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001669 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001669 / 10000000) = 1/(10000000 / 10001669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2325 : Bounds (83443 / 500000000) (166887 / 1000000000) (Real.log (10001669 / 10000000)) := by
  have h := reflection_log_2325_neg
  have he : Real.log (10001669 / 10000000) = -Real.log (10000000 / 10001669) := by
    rw [show ((10001669 / 10000000) : ℝ) = ((10000000 / 10001669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2326_neg : (166913 / 1000000000) ≤ -Real.log (9998331 / 10000000) ∧
    -Real.log (9998331 / 10000000) ≤ (83457 / 500000000) := by
  have h := checkLog_sound (w := (1669 / 19998331)) (n := 12)
    (lo := (166913 / 1000000000)) (hi := (83457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998331) = 1/(9998331 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2326 : Bounds (-83457 / 500000000) (-166913 / 1000000000) (Real.log (9998331 / 10000000)) := by
  have h := reflection_log_2326_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2327_neg : (5026011 / 62500000) ≤ -Real.log (500000 / 541869) ∧
    -Real.log (500000 / 541869) ≤ (80416177 / 1000000000) := by
  have h := checkLog_sound (w := (41869 / 1041869)) (n := 12)
    (lo := (5026011 / 62500000)) (hi := (80416177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541869 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541869 / 500000) = 1/(500000 / 541869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2327 : Bounds (5026011 / 62500000) (80416177 / 1000000000) (Real.log (541869 / 500000)) := by
  have h := reflection_log_2327_neg
  have he : Real.log (541869 / 500000) = -Real.log (500000 / 541869) := by
    rw [show ((541869 / 500000) : ℝ) = ((500000 / 541869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2328_neg : (87452929 / 1000000000) ≤ -Real.log (458131 / 500000) ∧
    -Real.log (458131 / 500000) ≤ (8745293 / 100000000) := by
  have h := checkLog_sound (w := (41869 / 958131)) (n := 12)
    (lo := (87452929 / 1000000000)) (hi := (8745293 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458131) = 1/(458131 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2328 : Bounds (-8745293 / 100000000) (-87452929 / 1000000000) (Real.log (458131 / 500000)) := by
  have h := reflection_log_2328_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2329_neg : (80617311 / 1000000000) ≤ -Real.log (250000 / 270989) ∧
    -Real.log (250000 / 270989) ≤ (2519291 / 31250000) := by
  have h := checkLog_sound (w := (20989 / 520989)) (n := 12)
    (lo := (80617311 / 1000000000)) (hi := (2519291 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270989 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270989 / 250000) = 1/(250000 / 270989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2329 : Bounds (80617311 / 1000000000) (2519291 / 31250000) (Real.log (270989 / 250000)) := by
  have h := reflection_log_2329_neg
  have he : Real.log (270989 / 250000) = -Real.log (250000 / 270989) := by
    rw [show ((270989 / 250000) : ℝ) = ((250000 / 270989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2330_neg : (137017 / 1562500) ≤ -Real.log (229011 / 250000) ∧
    -Real.log (229011 / 250000) ≤ (87690881 / 1000000000) := by
  have h := checkLog_sound (w := (20989 / 479011)) (n := 12)
    (lo := (137017 / 1562500)) (hi := (87690881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229011) = 1/(229011 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2330 : Bounds (-87690881 / 1000000000) (-137017 / 1562500) (Real.log (229011 / 250000)) := by
  have h := reflection_log_2330_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2331_neg : (221049 / 31250000) ≤ -Real.log (62059461879 / 62500000000) ∧
    -Real.log (62059461879 / 62500000000) ≤ (7073569 / 1000000000) := by
  have h := checkLog_sound (w := (440538121 / 124559461879)) (n := 12)
    (lo := (221049 / 31250000)) (hi := (7073569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62059461879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62059461879) = 1/(62059461879 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2331 : Bounds (-7073569 / 1000000000) (-221049 / 31250000) (Real.log (62059461879 / 62500000000)) := by
  have h := reflection_log_2331_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2332_neg : (439797 / 62500000) ≤ -Real.log (248246986839 / 250000000000) ∧
    -Real.log (248246986839 / 250000000000) ≤ (7036753 / 1000000000) := by
  have h := checkLog_sound (w := (1753013161 / 498246986839)) (n := 12)
    (lo := (439797 / 62500000)) (hi := (7036753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248246986839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248246986839) = 1/(248246986839 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2332 : Bounds (-7036753 / 1000000000) (-439797 / 62500000) (Real.log (248246986839 / 250000000000)) := by
  have h := reflection_log_2332_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2333_neg : (33573821 / 200000000) ≤ -Real.log (250000000000 / 295695445189) ∧
    -Real.log (250000000000 / 295695445189) ≤ (83934553 / 500000000) := by
  have h := checkLog_sound (w := (45695445189 / 545695445189)) (n := 12)
    (lo := (33573821 / 200000000)) (hi := (83934553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295695445189 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295695445189 / 250000000000) = 1/(250000000000 / 295695445189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2333 : Bounds (33573821 / 200000000) (83934553 / 500000000) (Real.log (295695445189 / 250000000000)) := by
  have h := reflection_log_2333_neg
  have he : Real.log (295695445189 / 250000000000) = -Real.log (250000000000 / 295695445189) := by
    rw [show ((295695445189 / 250000000000) : ℝ) = ((250000000000 / 295695445189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2334_neg : (5259631 / 31250000) ≤ -Real.log (500000000000 / 591650619403) ∧
    -Real.log (500000000000 / 591650619403) ≤ (168308193 / 1000000000) := by
  have h := checkLog_sound (w := (91650619403 / 1091650619403)) (n := 12)
    (lo := (5259631 / 31250000)) (hi := (168308193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591650619403 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591650619403 / 500000000000) = 1/(500000000000 / 591650619403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2334 : Bounds (5259631 / 31250000) (168308193 / 1000000000) (Real.log (591650619403 / 500000000000)) := by
  have h := reflection_log_2334_neg
  have he : Real.log (591650619403 / 500000000000) = -Real.log (500000000000 / 591650619403) := by
    rw [show ((591650619403 / 500000000000) : ℝ) = ((500000000000 / 591650619403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2335_neg : (10523329 / 31250000) ≤ -Real.log (125000000000 / 175048007681) ∧
    -Real.log (125000000000 / 175048007681) ≤ (336746529 / 1000000000) := by
  have h := checkLog_sound (w := (50048007681 / 300048007681)) (n := 12)
    (lo := (10523329 / 31250000)) (hi := (336746529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175048007681 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175048007681 / 125000000000) = 1/(125000000000 / 175048007681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2335 : Bounds (10523329 / 31250000) (336746529 / 1000000000) (Real.log (175048007681 / 125000000000)) := by
  have h := reflection_log_2335_neg
  have he : Real.log (175048007681 / 125000000000) = -Real.log (125000000000 / 175048007681) := by
    rw [show ((175048007681 / 125000000000) : ℝ) = ((125000000000 / 175048007681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2336_neg : (67390451 / 200000000) ≤ -Real.log (500000000000 / 700336094107) ∧
    -Real.log (500000000000 / 700336094107) ≤ (5264879 / 15625000) := by
  have h := checkLog_sound (w := (200336094107 / 1200336094107)) (n := 12)
    (lo := (67390451 / 200000000)) (hi := (5264879 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((700336094107 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(700336094107 / 500000000000) = 1/(500000000000 / 700336094107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2336 : Bounds (67390451 / 200000000) (5264879 / 15625000) (Real.log (700336094107 / 500000000000)) := by
  have h := reflection_log_2336_neg
  have he : Real.log (700336094107 / 500000000000) = -Real.log (500000000000 / 700336094107) := by
    rw [show ((700336094107 / 500000000000) : ℝ) = ((500000000000 / 700336094107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2337_neg : (154436353 / 1000000000) ≤ -Real.log (1000 / 1167) ∧
    -Real.log (1000 / 1167) ≤ (77218177 / 500000000) := by
  have h := checkLog_sound (w := (167 / 2167)) (n := 12)
    (lo := (154436353 / 1000000000)) (hi := (77218177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1167 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1167 / 1000) = 1/(1000 / 1167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2337 : Bounds (154436353 / 1000000000) (77218177 / 500000000) (Real.log (1167 / 1000)) := by
  have h := reflection_log_2337_neg
  have he : Real.log (1167 / 1000) = -Real.log (1000 / 1167) := by
    rw [show ((1167 / 1000) : ℝ) = ((1000 / 1167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2338_neg : (45680409 / 250000000) ≤ -Real.log (833 / 1000) ∧
    -Real.log (833 / 1000) ≤ (182721637 / 1000000000) := by
  have h := checkLog_sound (w := (167 / 1833)) (n := 12)
    (lo := (45680409 / 250000000)) (hi := (182721637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 833) = 1/(833 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2338 : Bounds (-182721637 / 1000000000) (-45680409 / 250000000) (Real.log (833 / 1000)) := by
  have h := reflection_log_2338_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2339_neg : (83493 / 500000000) ≤ -Real.log (1000000 / 1000167) ∧
    -Real.log (1000000 / 1000167) ≤ (166987 / 1000000000) := by
  have h := checkLog_sound (w := (167 / 2000167)) (n := 12)
    (lo := (83493 / 500000000)) (hi := (166987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000167 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000167 / 1000000) = 1/(1000000 / 1000167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2339 : Bounds (83493 / 500000000) (166987 / 1000000000) (Real.log (1000167 / 1000000)) := by
  have h := reflection_log_2339_neg
  have he : Real.log (1000167 / 1000000) = -Real.log (1000000 / 1000167) := by
    rw [show ((1000167 / 1000000) : ℝ) = ((1000000 / 1000167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2340_neg : (167013 / 1000000000) ≤ -Real.log (999833 / 1000000) ∧
    -Real.log (999833 / 1000000) ≤ (83507 / 500000000) := by
  have h := checkLog_sound (w := (167 / 1999833)) (n := 12)
    (lo := (167013 / 1000000000)) (hi := (83507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999833) = 1/(999833 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2340 : Bounds (-83507 / 500000000) (-167013 / 1000000000) (Real.log (999833 / 1000000)) := by
  have h := reflection_log_2340_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2341_neg : (40231617 / 500000000) ≤ -Real.log (1000000 / 1083789) ∧
    -Real.log (1000000 / 1083789) ≤ (16092647 / 200000000) := by
  have h := checkLog_sound (w := (83789 / 2083789)) (n := 12)
    (lo := (40231617 / 500000000)) (hi := (16092647 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083789 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083789 / 1000000) = 1/(1000000 / 1083789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2341 : Bounds (40231617 / 500000000) (16092647 / 200000000) (Real.log (1083789 / 1000000)) := by
  have h := reflection_log_2341_neg
  have he : Real.log (1083789 / 1000000) = -Real.log (1000000 / 1083789) := by
    rw [show ((1083789 / 1000000) : ℝ) = ((1000000 / 1083789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2342_neg : (87508591 / 1000000000) ≤ -Real.log (916211 / 1000000) ∧
    -Real.log (916211 / 1000000) ≤ (5469287 / 62500000) := by
  have h := checkLog_sound (w := (83789 / 1916211)) (n := 12)
    (lo := (87508591 / 1000000000)) (hi := (5469287 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916211) = 1/(916211 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2342 : Bounds (-5469287 / 62500000) (-87508591 / 1000000000) (Real.log (916211 / 1000000)) := by
  have h := reflection_log_2342_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2343_neg : (2016609 / 25000000) ≤ -Real.log (1000000 / 1084007) ∧
    -Real.log (1000000 / 1084007) ≤ (80664361 / 1000000000) := by
  have h := checkLog_sound (w := (84007 / 2084007)) (n := 12)
    (lo := (2016609 / 25000000)) (hi := (80664361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084007 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084007 / 1000000) = 1/(1000000 / 1084007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2343 : Bounds (2016609 / 25000000) (80664361 / 1000000000) (Real.log (1084007 / 1000000)) := by
  have h := reflection_log_2343_neg
  have he : Real.log (1084007 / 1000000) = -Real.log (1000000 / 1084007) := by
    rw [show ((1084007 / 1000000) : ℝ) = ((1000000 / 1084007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2344_neg : (21936639 / 250000000) ≤ -Real.log (915993 / 1000000) ∧
    -Real.log (915993 / 1000000) ≤ (87746557 / 1000000000) := by
  have h := checkLog_sound (w := (84007 / 1915993)) (n := 12)
    (lo := (21936639 / 250000000)) (hi := (87746557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915993) = 1/(915993 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2344 : Bounds (-87746557 / 1000000000) (-21936639 / 250000000) (Real.log (915993 / 1000000)) := by
  have h := reflection_log_2344_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2345_neg : (1416439 / 200000000) ≤ -Real.log (992942823951 / 1000000000000) ∧
    -Real.log (992942823951 / 1000000000000) ≤ (1770549 / 250000000) := by
  have h := checkLog_sound (w := (7057176049 / 1992942823951)) (n := 12)
    (lo := (1416439 / 200000000)) (hi := (1770549 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992942823951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992942823951) = 1/(992942823951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2345 : Bounds (-1770549 / 250000000) (-1416439 / 200000000) (Real.log (992942823951 / 1000000000000)) := by
  have h := reflection_log_2345_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2346_neg : (1761339 / 250000000) ≤ -Real.log (992979403479 / 1000000000000) ∧
    -Real.log (992979403479 / 1000000000000) ≤ (7045357 / 1000000000) := by
  have h := checkLog_sound (w := (7020596521 / 1992979403479)) (n := 12)
    (lo := (1761339 / 250000000)) (hi := (7045357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992979403479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992979403479) = 1/(992979403479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2346 : Bounds (-7045357 / 1000000000) (-1761339 / 250000000) (Real.log (992979403479 / 1000000000000)) := by
  have h := reflection_log_2346_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2347_neg : (83985913 / 500000000) ≤ -Real.log (500000000000 / 591451641597) ∧
    -Real.log (500000000000 / 591451641597) ≤ (167971827 / 1000000000) := by
  have h := checkLog_sound (w := (91451641597 / 1091451641597)) (n := 12)
    (lo := (83985913 / 500000000)) (hi := (167971827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591451641597 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591451641597 / 500000000000) = 1/(500000000000 / 591451641597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2347 : Bounds (83985913 / 500000000) (167971827 / 1000000000) (Real.log (591451641597 / 500000000000)) := by
  have h := reflection_log_2347_neg
  have he : Real.log (591451641597 / 500000000000) = -Real.log (500000000000 / 591451641597) := by
    rw [show ((591451641597 / 500000000000) : ℝ) = ((500000000000 / 591451641597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2348_neg : (42102729 / 250000000) ≤ -Real.log (250000000000 / 295855699771) ∧
    -Real.log (250000000000 / 295855699771) ≤ (168410917 / 1000000000) := by
  have h := checkLog_sound (w := (45855699771 / 545855699771)) (n := 12)
    (lo := (42102729 / 250000000)) (hi := (168410917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295855699771 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295855699771 / 250000000000) = 1/(250000000000 / 295855699771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2348 : Bounds (42102729 / 250000000) (168410917 / 1000000000) (Real.log (295855699771 / 250000000000)) := by
  have h := reflection_log_2348_neg
  have he : Real.log (295855699771 / 250000000000) = -Real.log (250000000000 / 295855699771) := by
    rw [show ((295855699771 / 250000000000) : ℝ) = ((250000000000 / 295855699771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2349_neg : (67390451 / 200000000) ≤ -Real.log (250000000000 / 350168047053) ∧
    -Real.log (250000000000 / 350168047053) ≤ (5264879 / 15625000) := by
  have h := checkLog_sound (w := (100168047053 / 600168047053)) (n := 12)
    (lo := (67390451 / 200000000)) (hi := (5264879 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((350168047053 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(350168047053 / 250000000000) = 1/(250000000000 / 350168047053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2349 : Bounds (67390451 / 200000000) (5264879 / 15625000) (Real.log (350168047053 / 250000000000)) := by
  have h := reflection_log_2349_neg
  have he : Real.log (350168047053 / 250000000000) = -Real.log (250000000000 / 350168047053) := by
    rw [show ((350168047053 / 250000000000) : ℝ) = ((250000000000 / 350168047053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2350_neg : (33715799 / 100000000) ≤ -Real.log (500000000000 / 700480192077) ∧
    -Real.log (500000000000 / 700480192077) ≤ (337157991 / 1000000000) := by
  have h := checkLog_sound (w := (200480192077 / 1200480192077)) (n := 12)
    (lo := (33715799 / 100000000)) (hi := (337157991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((700480192077 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(700480192077 / 500000000000) = 1/(500000000000 / 700480192077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2350 : Bounds (33715799 / 100000000) (337157991 / 1000000000) (Real.log (700480192077 / 500000000000)) := by
  have h := reflection_log_2350_neg
  have he : Real.log (700480192077 / 500000000000) = -Real.log (500000000000 / 700480192077) := by
    rw [show ((700480192077 / 500000000000) : ℝ) = ((500000000000 / 700480192077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2351_neg : (154522039 / 1000000000) ≤ -Real.log (10000 / 11671) ∧
    -Real.log (10000 / 11671) ≤ (3863051 / 25000000) := by
  have h := checkLog_sound (w := (1671 / 21671)) (n := 12)
    (lo := (154522039 / 1000000000)) (hi := (3863051 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11671 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11671 / 10000) = 1/(10000 / 11671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2351 : Bounds (154522039 / 1000000000) (3863051 / 25000000) (Real.log (11671 / 10000)) := by
  have h := reflection_log_2351_neg
  have he : Real.log (11671 / 10000) = -Real.log (10000 / 11671) := by
    rw [show ((11671 / 10000) : ℝ) = ((10000 / 11671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2352_neg : (45710423 / 250000000) ≤ -Real.log (8329 / 10000) ∧
    -Real.log (8329 / 10000) ≤ (182841693 / 1000000000) := by
  have h := checkLog_sound (w := (1671 / 18329)) (n := 12)
    (lo := (45710423 / 250000000)) (hi := (182841693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8329) = 1/(8329 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2352 : Bounds (-182841693 / 1000000000) (-45710423 / 250000000) (Real.log (8329 / 10000)) := by
  have h := reflection_log_2352_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2353_neg : (83543 / 500000000) ≤ -Real.log (10000000 / 10001671) ∧
    -Real.log (10000000 / 10001671) ≤ (167087 / 1000000000) := by
  have h := checkLog_sound (w := (1671 / 20001671)) (n := 12)
    (lo := (83543 / 500000000)) (hi := (167087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001671 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001671 / 10000000) = 1/(10000000 / 10001671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2353 : Bounds (83543 / 500000000) (167087 / 1000000000) (Real.log (10001671 / 10000000)) := by
  have h := reflection_log_2353_neg
  have he : Real.log (10001671 / 10000000) = -Real.log (10000000 / 10001671) := by
    rw [show ((10001671 / 10000000) : ℝ) = ((10000000 / 10001671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2354_neg : (167113 / 1000000000) ≤ -Real.log (9998329 / 10000000) ∧
    -Real.log (9998329 / 10000000) ≤ (83557 / 500000000) := by
  have h := checkLog_sound (w := (1671 / 19998329)) (n := 12)
    (lo := (167113 / 1000000000)) (hi := (83557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998329) = 1/(9998329 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2354 : Bounds (-83557 / 500000000) (-167113 / 1000000000) (Real.log (9998329 / 10000000)) := by
  have h := reflection_log_2354_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2355_neg : (8051029 / 100000000) ≤ -Real.log (3125 / 3387) ∧
    -Real.log (3125 / 3387) ≤ (80510291 / 1000000000) := by
  have h := checkLog_sound (w := (131 / 3256)) (n := 12)
    (lo := (8051029 / 100000000)) (hi := (80510291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3387 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3387 / 3125) = 1/(3125 / 3387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2355 : Bounds (8051029 / 100000000) (80510291 / 1000000000) (Real.log (3387 / 3125)) := by
  have h := reflection_log_2355_neg
  have he : Real.log (3387 / 3125) = -Real.log (3125 / 3387) := by
    rw [show ((3387 / 3125) : ℝ) = ((3125 / 3387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2356_neg : (87564257 / 1000000000) ≤ -Real.log (2863 / 3125) ∧
    -Real.log (2863 / 3125) ≤ (43782129 / 500000000) := by
  have h := checkLog_sound (w := (131 / 2994)) (n := 12)
    (lo := (87564257 / 1000000000)) (hi := (43782129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2863) = 1/(2863 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2356 : Bounds (-43782129 / 500000000) (-87564257 / 1000000000) (Real.log (2863 / 3125)) := by
  have h := reflection_log_2356_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2357_neg : (80711407 / 1000000000) ≤ -Real.log (500000 / 542029) ∧
    -Real.log (500000 / 542029) ≤ (5044463 / 62500000) := by
  have h := checkLog_sound (w := (42029 / 1042029)) (n := 12)
    (lo := (80711407 / 1000000000)) (hi := (5044463 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542029 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542029 / 500000) = 1/(500000 / 542029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2357 : Bounds (80711407 / 1000000000) (5044463 / 62500000) (Real.log (542029 / 500000)) := by
  have h := reflection_log_2357_neg
  have he : Real.log (542029 / 500000) = -Real.log (500000 / 542029) := by
    rw [show ((542029 / 500000) : ℝ) = ((500000 / 542029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2358_neg : (17560447 / 200000000) ≤ -Real.log (457971 / 500000) ∧
    -Real.log (457971 / 500000) ≤ (21950559 / 250000000) := by
  have h := checkLog_sound (w := (42029 / 957971)) (n := 12)
    (lo := (17560447 / 200000000)) (hi := (21950559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457971) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457971) = 1/(457971 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2358 : Bounds (-21950559 / 250000000) (-17560447 / 200000000) (Real.log (457971 / 500000)) := by
  have h := reflection_log_2358_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2359_neg : (7090827 / 1000000000) ≤ -Real.log (248233563159 / 250000000000) ∧
    -Real.log (248233563159 / 250000000000) ≤ (1772707 / 250000000) := by
  have h := checkLog_sound (w := (1766436841 / 498233563159)) (n := 12)
    (lo := (7090827 / 1000000000)) (hi := (1772707 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248233563159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248233563159) = 1/(248233563159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2359 : Bounds (-1772707 / 250000000) (-7090827 / 1000000000) (Real.log (248233563159 / 250000000000)) := by
  have h := reflection_log_2359_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2360_neg : (3526983 / 500000000) ≤ -Real.log (9696981 / 9765625) ∧
    -Real.log (9696981 / 9765625) ≤ (7053967 / 1000000000) := by
  have h := checkLog_sound (w := (34322 / 9731303)) (n := 12)
    (lo := (3526983 / 500000000)) (hi := (7053967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9765625 / 9696981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9765625 / 9696981) = 1/(9696981 / 9765625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2360 : Bounds (-7053967 / 1000000000) (-3526983 / 500000000) (Real.log (9696981 / 9765625)) := by
  have h := reflection_log_2360_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2361_neg : (168074547 / 1000000000) ≤ -Real.log (25000000000 / 29575619979) ∧
    -Real.log (25000000000 / 29575619979) ≤ (42018637 / 250000000) := by
  have h := checkLog_sound (w := (4575619979 / 54575619979)) (n := 12)
    (lo := (168074547 / 1000000000)) (hi := (42018637 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29575619979 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29575619979 / 25000000000) = 1/(25000000000 / 29575619979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2361 : Bounds (168074547 / 1000000000) (42018637 / 250000000) (Real.log (29575619979 / 25000000000)) := by
  have h := reflection_log_2361_neg
  have he : Real.log (29575619979 / 25000000000) = -Real.log (25000000000 / 29575619979) := by
    rw [show ((29575619979 / 25000000000) : ℝ) = ((25000000000 / 29575619979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2362_neg : (84256821 / 500000000) ≤ -Real.log (500000000000 / 591772186449) ∧
    -Real.log (500000000000 / 591772186449) ≤ (168513643 / 1000000000) := by
  have h := checkLog_sound (w := (91772186449 / 1091772186449)) (n := 12)
    (lo := (84256821 / 500000000)) (hi := (168513643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591772186449 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591772186449 / 500000000000) = 1/(500000000000 / 591772186449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2362 : Bounds (84256821 / 500000000) (168513643 / 1000000000) (Real.log (591772186449 / 500000000000)) := by
  have h := reflection_log_2362_neg
  have he : Real.log (591772186449 / 500000000000) = -Real.log (500000000000 / 591772186449) := by
    rw [show ((591772186449 / 500000000000) : ℝ) = ((500000000000 / 591772186449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2363_neg : (33715799 / 100000000) ≤ -Real.log (125000000000 / 175120048019) ∧
    -Real.log (125000000000 / 175120048019) ≤ (337157991 / 1000000000) := by
  have h := checkLog_sound (w := (50120048019 / 300120048019)) (n := 12)
    (lo := (33715799 / 100000000)) (hi := (337157991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175120048019 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175120048019 / 125000000000) = 1/(125000000000 / 175120048019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2363 : Bounds (33715799 / 100000000) (337157991 / 1000000000) (Real.log (175120048019 / 125000000000)) := by
  have h := reflection_log_2363_neg
  have he : Real.log (175120048019 / 125000000000) = -Real.log (125000000000 / 175120048019) := by
    rw [show ((175120048019 / 125000000000) : ℝ) = ((125000000000 / 175120048019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2364_neg : (337363731 / 1000000000) ≤ -Real.log (500000000000 / 700624324649) ∧
    -Real.log (500000000000 / 700624324649) ≤ (84340933 / 250000000) := by
  have h := checkLog_sound (w := (200624324649 / 1200624324649)) (n := 12)
    (lo := (337363731 / 1000000000)) (hi := (84340933 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((700624324649 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(700624324649 / 500000000000) = 1/(500000000000 / 700624324649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2364 : Bounds (337363731 / 1000000000) (84340933 / 250000000) (Real.log (700624324649 / 500000000000)) := by
  have h := reflection_log_2364_neg
  have he : Real.log (700624324649 / 500000000000) = -Real.log (500000000000 / 700624324649) := by
    rw [show ((700624324649 / 500000000000) : ℝ) = ((500000000000 / 700624324649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2365_neg : (77303859 / 500000000) ≤ -Real.log (1250 / 1459) ∧
    -Real.log (1250 / 1459) ≤ (154607719 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 2709)) (n := 12)
    (lo := (77303859 / 500000000)) (hi := (154607719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1459 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1459 / 1250) = 1/(1250 / 1459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2365 : Bounds (77303859 / 500000000) (154607719 / 1000000000) (Real.log (1459 / 1250)) := by
  have h := reflection_log_2365_neg
  have he : Real.log (1459 / 1250) = -Real.log (1250 / 1459) := by
    rw [show ((1459 / 1250) : ℝ) = ((1250 / 1459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2366_neg : (182961761 / 1000000000) ≤ -Real.log (1041 / 1250) ∧
    -Real.log (1041 / 1250) ≤ (91480881 / 500000000) := by
  have h := checkLog_sound (w := (209 / 2291)) (n := 12)
    (lo := (182961761 / 1000000000)) (hi := (91480881 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1041) = 1/(1041 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2366 : Bounds (-91480881 / 500000000) (-182961761 / 1000000000) (Real.log (1041 / 1250)) := by
  have h := reflection_log_2366_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2367_neg : (83593 / 500000000) ≤ -Real.log (1250000 / 1250209) ∧
    -Real.log (1250000 / 1250209) ≤ (167187 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 2500209)) (n := 12)
    (lo := (83593 / 500000000)) (hi := (167187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250209 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250209 / 1250000) = 1/(1250000 / 1250209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2367 : Bounds (83593 / 500000000) (167187 / 1000000000) (Real.log (1250209 / 1250000)) := by
  have h := reflection_log_2367_neg
  have he : Real.log (1250209 / 1250000) = -Real.log (1250000 / 1250209) := by
    rw [show ((1250209 / 1250000) : ℝ) = ((1250000 / 1250209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0037 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2368_neg : (167213 / 1000000000) ≤ -Real.log (1249791 / 1250000) ∧
    -Real.log (1249791 / 1250000) ≤ (83607 / 500000000) := by
  have h := checkLog_sound (w := (209 / 2499791)) (n := 12)
    (lo := (167213 / 1000000000)) (hi := (83607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249791) = 1/(1249791 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2368 : Bounds (-83607 / 500000000) (-167213 / 1000000000) (Real.log (1249791 / 1250000)) := by
  have h := reflection_log_2368_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2369_neg : (2517417 / 31250000) ≤ -Real.log (1000000 / 1083891) ∧
    -Real.log (1000000 / 1083891) ≤ (16111469 / 200000000) := by
  have h := checkLog_sound (w := (83891 / 2083891)) (n := 12)
    (lo := (2517417 / 31250000)) (hi := (16111469 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083891 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083891 / 1000000) = 1/(1000000 / 1083891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2369 : Bounds (2517417 / 31250000) (16111469 / 200000000) (Real.log (1083891 / 1000000)) := by
  have h := reflection_log_2369_neg
  have he : Real.log (1083891 / 1000000) = -Real.log (1000000 / 1083891) := by
    rw [show ((1083891 / 1000000) : ℝ) = ((1000000 / 1083891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2370_neg : (3504797 / 40000000) ≤ -Real.log (916109 / 1000000) ∧
    -Real.log (916109 / 1000000) ≤ (43809963 / 500000000) := by
  have h := checkLog_sound (w := (83891 / 1916109)) (n := 12)
    (lo := (3504797 / 40000000)) (hi := (43809963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916109) = 1/(916109 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2370 : Bounds (-43809963 / 500000000) (-3504797 / 40000000) (Real.log (916109 / 1000000)) := by
  have h := reflection_log_2370_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2371_neg : (80758451 / 1000000000) ≤ -Real.log (1000000 / 1084109) ∧
    -Real.log (1000000 / 1084109) ≤ (20189613 / 250000000) := by
  have h := checkLog_sound (w := (84109 / 2084109)) (n := 12)
    (lo := (80758451 / 1000000000)) (hi := (20189613 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084109 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084109 / 1000000) = 1/(1000000 / 1084109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2371 : Bounds (80758451 / 1000000000) (20189613 / 250000000) (Real.log (1084109 / 1000000)) := by
  have h := reflection_log_2371_neg
  have he : Real.log (1084109 / 1000000) = -Real.log (1000000 / 1084109) := by
    rw [show ((1084109 / 1000000) : ℝ) = ((1000000 / 1084109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2372_neg : (87857917 / 1000000000) ≤ -Real.log (915891 / 1000000) ∧
    -Real.log (915891 / 1000000) ≤ (43928959 / 500000000) := by
  have h := checkLog_sound (w := (84109 / 1915891)) (n := 12)
    (lo := (87857917 / 1000000000)) (hi := (43928959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915891) = 1/(915891 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2372 : Bounds (-43928959 / 500000000) (-87857917 / 1000000000) (Real.log (915891 / 1000000)) := by
  have h := reflection_log_2372_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2373_neg : (1419893 / 200000000) ≤ -Real.log (992925676119 / 1000000000000) ∧
    -Real.log (992925676119 / 1000000000000) ≤ (3549733 / 500000000) := by
  have h := checkLog_sound (w := (7074323881 / 1992925676119)) (n := 12)
    (lo := (1419893 / 200000000)) (hi := (3549733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992925676119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992925676119) = 1/(992925676119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2373 : Bounds (-3549733 / 500000000) (-1419893 / 200000000) (Real.log (992925676119 / 1000000000000)) := by
  have h := reflection_log_2373_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2374_neg : (7062581 / 1000000000) ≤ -Real.log (992962300119 / 1000000000000) ∧
    -Real.log (992962300119 / 1000000000000) ≤ (3531291 / 500000000) := by
  have h := checkLog_sound (w := (7037699881 / 1992962300119)) (n := 12)
    (lo := (7062581 / 1000000000)) (hi := (3531291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992962300119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992962300119) = 1/(992962300119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2374 : Bounds (-3531291 / 500000000) (-7062581 / 1000000000) (Real.log (992962300119 / 1000000000000)) := by
  have h := reflection_log_2374_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2375_neg : (16817727 / 100000000) ≤ -Real.log (62500000000 / 73946645541) ∧
    -Real.log (62500000000 / 73946645541) ≤ (168177271 / 1000000000) := by
  have h := checkLog_sound (w := (11446645541 / 136446645541)) (n := 12)
    (lo := (16817727 / 100000000)) (hi := (168177271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73946645541 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73946645541 / 62500000000) = 1/(62500000000 / 73946645541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2375 : Bounds (16817727 / 100000000) (168177271 / 1000000000) (Real.log (73946645541 / 62500000000)) := by
  have h := reflection_log_2375_neg
  have he : Real.log (73946645541 / 62500000000) = -Real.log (62500000000 / 73946645541) := by
    rw [show ((73946645541 / 62500000000) : ℝ) = ((62500000000 / 73946645541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2376_neg : (10538523 / 62500000) ≤ -Real.log (250000000000 / 295916490063) ∧
    -Real.log (250000000000 / 295916490063) ≤ (168616369 / 1000000000) := by
  have h := checkLog_sound (w := (45916490063 / 545916490063)) (n := 12)
    (lo := (10538523 / 62500000)) (hi := (168616369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295916490063 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295916490063 / 250000000000) = 1/(250000000000 / 295916490063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2376 : Bounds (10538523 / 62500000) (168616369 / 1000000000) (Real.log (295916490063 / 250000000000)) := by
  have h := reflection_log_2376_neg
  have he : Real.log (295916490063 / 250000000000) = -Real.log (250000000000 / 295916490063) := by
    rw [show ((295916490063 / 250000000000) : ℝ) = ((250000000000 / 295916490063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2377_neg : (337363731 / 1000000000) ≤ -Real.log (62500000000 / 87578040581) ∧
    -Real.log (62500000000 / 87578040581) ≤ (84340933 / 250000000) := by
  have h := checkLog_sound (w := (25078040581 / 150078040581)) (n := 12)
    (lo := (337363731 / 1000000000)) (hi := (84340933 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87578040581 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87578040581 / 62500000000) = 1/(62500000000 / 87578040581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2377 : Bounds (337363731 / 1000000000) (84340933 / 250000000) (Real.log (87578040581 / 62500000000)) := by
  have h := reflection_log_2377_neg
  have he : Real.log (87578040581 / 62500000000) = -Real.log (62500000000 / 87578040581) := by
    rw [show ((87578040581 / 62500000000) : ℝ) = ((62500000000 / 87578040581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2378_neg : (337569479 / 1000000000) ≤ -Real.log (100000000000 / 140153698367) ∧
    -Real.log (100000000000 / 140153698367) ≤ (8439237 / 25000000) := by
  have h := checkLog_sound (w := (40153698367 / 240153698367)) (n := 12)
    (lo := (337569479 / 1000000000)) (hi := (8439237 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140153698367 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140153698367 / 100000000000) = 1/(100000000000 / 140153698367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2378 : Bounds (337569479 / 1000000000) (8439237 / 25000000) (Real.log (140153698367 / 100000000000)) := by
  have h := reflection_log_2378_neg
  have he : Real.log (140153698367 / 100000000000) = -Real.log (100000000000 / 140153698367) := by
    rw [show ((140153698367 / 100000000000) : ℝ) = ((100000000000 / 140153698367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2379_neg : (154693389 / 1000000000) ≤ -Real.log (10000 / 11673) ∧
    -Real.log (10000 / 11673) ≤ (15469339 / 100000000) := by
  have h := checkLog_sound (w := (1673 / 21673)) (n := 12)
    (lo := (154693389 / 1000000000)) (hi := (15469339 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11673 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11673 / 10000) = 1/(10000 / 11673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2379 : Bounds (154693389 / 1000000000) (15469339 / 100000000) (Real.log (11673 / 10000)) := by
  have h := reflection_log_2379_neg
  have he : Real.log (11673 / 10000) = -Real.log (10000 / 11673) := by
    rw [show ((11673 / 10000) : ℝ) = ((10000 / 11673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2380_neg : (36616369 / 200000000) ≤ -Real.log (8327 / 10000) ∧
    -Real.log (8327 / 10000) ≤ (91540923 / 500000000) := by
  have h := checkLog_sound (w := (1673 / 18327)) (n := 12)
    (lo := (36616369 / 200000000)) (hi := (91540923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8327) = 1/(8327 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2380 : Bounds (-91540923 / 500000000) (-36616369 / 200000000) (Real.log (8327 / 10000)) := by
  have h := reflection_log_2380_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2381_neg : (83643 / 500000000) ≤ -Real.log (10000000 / 10001673) ∧
    -Real.log (10000000 / 10001673) ≤ (167287 / 1000000000) := by
  have h := checkLog_sound (w := (1673 / 20001673)) (n := 12)
    (lo := (83643 / 500000000)) (hi := (167287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001673 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001673 / 10000000) = 1/(10000000 / 10001673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2381 : Bounds (83643 / 500000000) (167287 / 1000000000) (Real.log (10001673 / 10000000)) := by
  have h := reflection_log_2381_neg
  have he : Real.log (10001673 / 10000000) = -Real.log (10000000 / 10001673) := by
    rw [show ((10001673 / 10000000) : ℝ) = ((10000000 / 10001673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2382_neg : (167313 / 1000000000) ≤ -Real.log (9998327 / 10000000) ∧
    -Real.log (9998327 / 10000000) ≤ (83657 / 500000000) := by
  have h := checkLog_sound (w := (1673 / 19998327)) (n := 12)
    (lo := (167313 / 1000000000)) (hi := (83657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998327) = 1/(9998327 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2382 : Bounds (-83657 / 500000000) (-167313 / 1000000000) (Real.log (9998327 / 10000000)) := by
  have h := reflection_log_2382_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2383_neg : (80603473 / 1000000000) ≤ -Real.log (1000000 / 1083941) ∧
    -Real.log (1000000 / 1083941) ≤ (40301737 / 500000000) := by
  have h := checkLog_sound (w := (83941 / 2083941)) (n := 12)
    (lo := (80603473 / 1000000000)) (hi := (40301737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083941 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083941 / 1000000) = 1/(1000000 / 1083941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2383 : Bounds (80603473 / 1000000000) (40301737 / 500000000) (Real.log (1083941 / 1000000)) := by
  have h := reflection_log_2383_neg
  have he : Real.log (1083941 / 1000000) = -Real.log (1000000 / 1083941) := by
    rw [show ((1083941 / 1000000) : ℝ) = ((1000000 / 1083941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2384_neg : (17534901 / 200000000) ≤ -Real.log (916059 / 1000000) ∧
    -Real.log (916059 / 1000000) ≤ (43837253 / 500000000) := by
  have h := checkLog_sound (w := (83941 / 1916059)) (n := 12)
    (lo := (17534901 / 200000000)) (hi := (43837253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916059) = 1/(916059 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2384 : Bounds (-43837253 / 500000000) (-17534901 / 200000000) (Real.log (916059 / 1000000)) := by
  have h := reflection_log_2384_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2385_neg : (80804571 / 1000000000) ≤ -Real.log (1000000 / 1084159) ∧
    -Real.log (1000000 / 1084159) ≤ (20201143 / 250000000) := by
  have h := checkLog_sound (w := (84159 / 2084159)) (n := 12)
    (lo := (80804571 / 1000000000)) (hi := (20201143 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084159 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084159 / 1000000) = 1/(1000000 / 1084159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2385 : Bounds (80804571 / 1000000000) (20201143 / 250000000) (Real.log (1084159 / 1000000)) := by
  have h := reflection_log_2385_neg
  have he : Real.log (1084159 / 1000000) = -Real.log (1000000 / 1084159) := by
    rw [show ((1084159 / 1000000) : ℝ) = ((1000000 / 1084159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2386_neg : (8791251 / 100000000) ≤ -Real.log (915841 / 1000000) ∧
    -Real.log (915841 / 1000000) ≤ (87912511 / 1000000000) := by
  have h := checkLog_sound (w := (84159 / 1915841)) (n := 12)
    (lo := (8791251 / 100000000)) (hi := (87912511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915841) = 1/(915841 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2386 : Bounds (-87912511 / 1000000000) (-8791251 / 100000000) (Real.log (915841 / 1000000)) := by
  have h := reflection_log_2386_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2387_neg : (3553969 / 500000000) ≤ -Real.log (992917262719 / 1000000000000) ∧
    -Real.log (992917262719 / 1000000000000) ≤ (7107939 / 1000000000) := by
  have h := checkLog_sound (w := (7082737281 / 1992917262719)) (n := 12)
    (lo := (3553969 / 500000000)) (hi := (7107939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992917262719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992917262719) = 1/(992917262719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2387 : Bounds (-7107939 / 1000000000) (-3553969 / 500000000) (Real.log (992917262719 / 1000000000000)) := by
  have h := reflection_log_2387_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2388_neg : (883879 / 125000000) ≤ -Real.log (992953908519 / 1000000000000) ∧
    -Real.log (992953908519 / 1000000000000) ≤ (7071033 / 1000000000) := by
  have h := checkLog_sound (w := (7046091481 / 1992953908519)) (n := 12)
    (lo := (883879 / 125000000)) (hi := (7071033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992953908519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992953908519) = 1/(992953908519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2388 : Bounds (-7071033 / 1000000000) (-883879 / 125000000) (Real.log (992953908519 / 1000000000000)) := by
  have h := reflection_log_2388_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2389_neg : (168277979 / 1000000000) ≤ -Real.log (500000000000 / 591632744179) ∧
    -Real.log (500000000000 / 591632744179) ≤ (8413899 / 50000000) := by
  have h := checkLog_sound (w := (91632744179 / 1091632744179)) (n := 12)
    (lo := (168277979 / 1000000000)) (hi := (8413899 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591632744179 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591632744179 / 500000000000) = 1/(500000000000 / 591632744179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2389 : Bounds (168277979 / 1000000000) (8413899 / 50000000) (Real.log (591632744179 / 500000000000)) := by
  have h := reflection_log_2389_neg
  have he : Real.log (591632744179 / 500000000000) = -Real.log (500000000000 / 591632744179) := by
    rw [show ((591632744179 / 500000000000) : ℝ) = ((500000000000 / 591632744179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2390_neg : (168717081 / 1000000000) ≤ -Real.log (500000000000 / 591892588343) ∧
    -Real.log (500000000000 / 591892588343) ≤ (84358541 / 500000000) := by
  have h := checkLog_sound (w := (91892588343 / 1091892588343)) (n := 12)
    (lo := (168717081 / 1000000000)) (hi := (84358541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591892588343 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591892588343 / 500000000000) = 1/(500000000000 / 591892588343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2390 : Bounds (168717081 / 1000000000) (84358541 / 500000000) (Real.log (591892588343 / 500000000000)) := by
  have h := reflection_log_2390_neg
  have he : Real.log (591892588343 / 500000000000) = -Real.log (500000000000 / 591892588343) := by
    rw [show ((591892588343 / 500000000000) : ℝ) = ((500000000000 / 591892588343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2391_neg : (337569479 / 1000000000) ≤ -Real.log (250000000000 / 350384245917) ∧
    -Real.log (250000000000 / 350384245917) ≤ (8439237 / 25000000) := by
  have h := checkLog_sound (w := (100384245917 / 600384245917)) (n := 12)
    (lo := (337569479 / 1000000000)) (hi := (8439237 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((350384245917 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(350384245917 / 250000000000) = 1/(250000000000 / 350384245917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2391 : Bounds (337569479 / 1000000000) (8439237 / 25000000) (Real.log (350384245917 / 250000000000)) := by
  have h := reflection_log_2391_neg
  have he : Real.log (350384245917 / 250000000000) = -Real.log (250000000000 / 350384245917) := by
    rw [show ((350384245917 / 250000000000) : ℝ) = ((250000000000 / 350384245917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2392_neg : (67555047 / 200000000) ≤ -Real.log (31250000000 / 43807043353) ∧
    -Real.log (31250000000 / 43807043353) ≤ (84443809 / 250000000) := by
  have h := checkLog_sound (w := (12557043353 / 75057043353)) (n := 12)
    (lo := (67555047 / 200000000)) (hi := (84443809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43807043353 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43807043353 / 31250000000) = 1/(31250000000 / 43807043353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2392 : Bounds (67555047 / 200000000) (84443809 / 250000000) (Real.log (43807043353 / 31250000000)) := by
  have h := reflection_log_2392_neg
  have he : Real.log (43807043353 / 31250000000) = -Real.log (31250000000 / 43807043353) := by
    rw [show ((43807043353 / 31250000000) : ℝ) = ((31250000000 / 43807043353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2393_neg : (154779053 / 1000000000) ≤ -Real.log (5000 / 5837) ∧
    -Real.log (5000 / 5837) ≤ (77389527 / 500000000) := by
  have h := checkLog_sound (w := (837 / 10837)) (n := 12)
    (lo := (154779053 / 1000000000)) (hi := (77389527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5837 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5837 / 5000) = 1/(5000 / 5837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2393 : Bounds (154779053 / 1000000000) (77389527 / 500000000) (Real.log (5837 / 5000)) := by
  have h := reflection_log_2393_neg
  have he : Real.log (5837 / 5000) = -Real.log (5000 / 5837) := by
    rw [show ((5837 / 5000) : ℝ) = ((5000 / 5837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2394_neg : (22900243 / 125000000) ≤ -Real.log (4163 / 5000) ∧
    -Real.log (4163 / 5000) ≤ (36640389 / 200000000) := by
  have h := checkLog_sound (w := (837 / 9163)) (n := 12)
    (lo := (22900243 / 125000000)) (hi := (36640389 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4163) = 1/(4163 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2394 : Bounds (-36640389 / 200000000) (-22900243 / 125000000) (Real.log (4163 / 5000)) := by
  have h := reflection_log_2394_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2395_neg : (33477 / 200000000) ≤ -Real.log (5000000 / 5000837) ∧
    -Real.log (5000000 / 5000837) ≤ (83693 / 500000000) := by
  have h := checkLog_sound (w := (837 / 10000837)) (n := 12)
    (lo := (33477 / 200000000)) (hi := (83693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000837 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000837 / 5000000) = 1/(5000000 / 5000837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2395 : Bounds (33477 / 200000000) (83693 / 500000000) (Real.log (5000837 / 5000000)) := by
  have h := reflection_log_2395_neg
  have he : Real.log (5000837 / 5000000) = -Real.log (5000000 / 5000837) := by
    rw [show ((5000837 / 5000000) : ℝ) = ((5000000 / 5000837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2396_neg : (83707 / 500000000) ≤ -Real.log (4999163 / 5000000) ∧
    -Real.log (4999163 / 5000000) ≤ (33483 / 200000000) := by
  have h := checkLog_sound (w := (837 / 9999163)) (n := 12)
    (lo := (83707 / 500000000)) (hi := (33483 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999163) = 1/(4999163 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2396 : Bounds (-33483 / 200000000) (-83707 / 500000000) (Real.log (4999163 / 5000000)) := by
  have h := reflection_log_2396_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2397_neg : (40325261 / 500000000) ≤ -Real.log (125000 / 135499) ∧
    -Real.log (125000 / 135499) ≤ (80650523 / 1000000000) := by
  have h := checkLog_sound (w := (10499 / 260499)) (n := 12)
    (lo := (40325261 / 500000000)) (hi := (80650523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135499 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135499 / 125000) = 1/(125000 / 135499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2397 : Bounds (40325261 / 500000000) (80650523 / 1000000000) (Real.log (135499 / 125000)) := by
  have h := reflection_log_2397_neg
  have he : Real.log (135499 / 125000) = -Real.log (125000 / 135499) := by
    rw [show ((135499 / 125000) : ℝ) = ((125000 / 135499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2398_neg : (4386509 / 50000000) ≤ -Real.log (114501 / 125000) ∧
    -Real.log (114501 / 125000) ≤ (87730181 / 1000000000) := by
  have h := checkLog_sound (w := (10499 / 239501)) (n := 12)
    (lo := (4386509 / 50000000)) (hi := (87730181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 114501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 114501) = 1/(114501 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2398 : Bounds (-87730181 / 1000000000) (-4386509 / 50000000) (Real.log (114501 / 125000)) := by
  have h := reflection_log_2398_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2399_neg : (80851611 / 1000000000) ≤ -Real.log (100000 / 108421) ∧
    -Real.log (100000 / 108421) ≤ (20212903 / 250000000) := by
  have h := checkLog_sound (w := (8421 / 208421)) (n := 12)
    (lo := (80851611 / 1000000000)) (hi := (20212903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108421 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108421 / 100000) = 1/(100000 / 108421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2399 : Bounds (80851611 / 1000000000) (20212903 / 250000000) (Real.log (108421 / 100000)) := by
  have h := reflection_log_2399_neg
  have he : Real.log (108421 / 100000) = -Real.log (100000 / 108421) := by
    rw [show ((108421 / 100000) : ℝ) = ((100000 / 108421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2400_neg : (43984099 / 500000000) ≤ -Real.log (91579 / 100000) ∧
    -Real.log (91579 / 100000) ≤ (87968199 / 1000000000) := by
  have h := checkLog_sound (w := (8421 / 191579)) (n := 12)
    (lo := (43984099 / 500000000)) (hi := (87968199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 91579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 91579) = 1/(91579 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2400 : Bounds (-87968199 / 1000000000) (-43984099 / 500000000) (Real.log (91579 / 100000)) := by
  have h := reflection_log_2400_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2401_neg : (7116587 / 1000000000) ≤ -Real.log (9929086759 / 10000000000) ∧
    -Real.log (9929086759 / 10000000000) ≤ (1779147 / 250000000) := by
  have h := checkLog_sound (w := (70913241 / 19929086759)) (n := 12)
    (lo := (7116587 / 1000000000)) (hi := (1779147 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9929086759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9929086759) = 1/(9929086759 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2401 : Bounds (-1779147 / 250000000) (-7116587 / 1000000000) (Real.log (9929086759 / 10000000000)) := by
  have h := reflection_log_2401_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2402_neg : (7079657 / 1000000000) ≤ -Real.log (15514770999 / 15625000000) ∧
    -Real.log (15514770999 / 15625000000) ≤ (3539829 / 500000000) := by
  have h := checkLog_sound (w := (110229001 / 31139770999)) (n := 12)
    (lo := (7079657 / 1000000000)) (hi := (3539829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15514770999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15514770999) = 1/(15514770999 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2402 : Bounds (-3539829 / 500000000) (-7079657 / 1000000000) (Real.log (15514770999 / 15625000000)) := by
  have h := reflection_log_2402_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2403_neg : (168380703 / 1000000000) ≤ -Real.log (500000000000 / 591693522327) ∧
    -Real.log (500000000000 / 591693522327) ≤ (5261897 / 31250000) := by
  have h := checkLog_sound (w := (91693522327 / 1091693522327)) (n := 12)
    (lo := (168380703 / 1000000000)) (hi := (5261897 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591693522327 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591693522327 / 500000000000) = 1/(500000000000 / 591693522327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2403 : Bounds (168380703 / 1000000000) (5261897 / 31250000) (Real.log (591693522327 / 500000000000)) := by
  have h := reflection_log_2403_neg
  have he : Real.log (591693522327 / 500000000000) = -Real.log (500000000000 / 591693522327) := by
    rw [show ((591693522327 / 500000000000) : ℝ) = ((500000000000 / 591693522327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2404_neg : (168819809 / 1000000000) ≤ -Real.log (50000000000 / 59195339543) ∧
    -Real.log (50000000000 / 59195339543) ≤ (16881981 / 100000000) := by
  have h := checkLog_sound (w := (9195339543 / 109195339543)) (n := 12)
    (lo := (168819809 / 1000000000)) (hi := (16881981 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59195339543 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59195339543 / 50000000000) = 1/(50000000000 / 59195339543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2404 : Bounds (168819809 / 1000000000) (16881981 / 100000000) (Real.log (59195339543 / 50000000000)) := by
  have h := reflection_log_2404_neg
  have he : Real.log (59195339543 / 50000000000) = -Real.log (50000000000 / 59195339543) := by
    rw [show ((59195339543 / 50000000000) : ℝ) = ((50000000000 / 59195339543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2405_neg : (67555047 / 200000000) ≤ -Real.log (500000000000 / 700912693647) ∧
    -Real.log (500000000000 / 700912693647) ≤ (84443809 / 250000000) := by
  have h := checkLog_sound (w := (200912693647 / 1200912693647)) (n := 12)
    (lo := (67555047 / 200000000)) (hi := (84443809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((700912693647 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(700912693647 / 500000000000) = 1/(500000000000 / 700912693647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2405 : Bounds (67555047 / 200000000) (84443809 / 250000000) (Real.log (700912693647 / 500000000000)) := by
  have h := reflection_log_2405_neg
  have he : Real.log (700912693647 / 500000000000) = -Real.log (500000000000 / 700912693647) := by
    rw [show ((700912693647 / 500000000000) : ℝ) = ((500000000000 / 700912693647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2406_neg : (168990499 / 500000000) ≤ -Real.log (500000000000 / 701056930099) ∧
    -Real.log (500000000000 / 701056930099) ≤ (337980999 / 1000000000) := by
  have h := checkLog_sound (w := (201056930099 / 1201056930099)) (n := 12)
    (lo := (168990499 / 500000000)) (hi := (337980999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((701056930099 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(701056930099 / 500000000000) = 1/(500000000000 / 701056930099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2406 : Bounds (168990499 / 500000000) (337980999 / 1000000000) (Real.log (701056930099 / 500000000000)) := by
  have h := reflection_log_2406_neg
  have he : Real.log (701056930099 / 500000000000) = -Real.log (500000000000 / 701056930099) := by
    rw [show ((701056930099 / 500000000000) : ℝ) = ((500000000000 / 701056930099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2407_neg : (15486471 / 100000000) ≤ -Real.log (400 / 467) ∧
    -Real.log (400 / 467) ≤ (154864711 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 867)) (n := 12)
    (lo := (15486471 / 100000000)) (hi := (154864711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((467 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(467 / 400) = 1/(400 / 467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2407 : Bounds (15486471 / 100000000) (154864711 / 1000000000) (Real.log (467 / 400)) := by
  have h := reflection_log_2407_neg
  have he : Real.log (467 / 400) = -Real.log (400 / 467) := by
    rw [show ((467 / 400) : ℝ) = ((400 / 467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2408_neg : (183322057 / 1000000000) ≤ -Real.log (333 / 400) ∧
    -Real.log (333 / 400) ≤ (91661029 / 500000000) := by
  have h := checkLog_sound (w := (67 / 733)) (n := 12)
    (lo := (183322057 / 1000000000)) (hi := (91661029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 333) = 1/(333 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2408 : Bounds (-91661029 / 500000000) (-183322057 / 1000000000) (Real.log (333 / 400)) := by
  have h := reflection_log_2408_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2409_neg : (33497 / 200000000) ≤ -Real.log (400000 / 400067) ∧
    -Real.log (400000 / 400067) ≤ (83743 / 500000000) := by
  have h := checkLog_sound (w := (67 / 800067)) (n := 12)
    (lo := (33497 / 200000000)) (hi := (83743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400067 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400067 / 400000) = 1/(400000 / 400067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2409 : Bounds (33497 / 200000000) (83743 / 500000000) (Real.log (400067 / 400000)) := by
  have h := reflection_log_2409_neg
  have he : Real.log (400067 / 400000) = -Real.log (400000 / 400067) := by
    rw [show ((400067 / 400000) : ℝ) = ((400000 / 400067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2410_neg : (83757 / 500000000) ≤ -Real.log (399933 / 400000) ∧
    -Real.log (399933 / 400000) ≤ (33503 / 200000000) := by
  have h := checkLog_sound (w := (67 / 799933)) (n := 12)
    (lo := (83757 / 500000000)) (hi := (33503 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399933) = 1/(399933 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2410 : Bounds (-33503 / 200000000) (-83757 / 500000000) (Real.log (399933 / 400000)) := by
  have h := reflection_log_2410_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2411_neg : (8069757 / 100000000) ≤ -Real.log (1000000 / 1084043) ∧
    -Real.log (1000000 / 1084043) ≤ (80697571 / 1000000000) := by
  have h := checkLog_sound (w := (84043 / 2084043)) (n := 12)
    (lo := (8069757 / 100000000)) (hi := (80697571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084043 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084043 / 1000000) = 1/(1000000 / 1084043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2411 : Bounds (8069757 / 100000000) (80697571 / 1000000000) (Real.log (1084043 / 1000000)) := by
  have h := reflection_log_2411_neg
  have he : Real.log (1084043 / 1000000) = -Real.log (1000000 / 1084043) := by
    rw [show ((1084043 / 1000000) : ℝ) = ((1000000 / 1084043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2412_neg : (43892929 / 500000000) ≤ -Real.log (915957 / 1000000) ∧
    -Real.log (915957 / 1000000) ≤ (87785859 / 1000000000) := by
  have h := checkLog_sound (w := (84043 / 1915957)) (n := 12)
    (lo := (43892929 / 500000000)) (hi := (87785859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915957) = 1/(915957 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2412 : Bounds (-87785859 / 1000000000) (-43892929 / 500000000) (Real.log (915957 / 1000000)) := by
  have h := reflection_log_2412_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2413_neg : (10112331 / 125000000) ≤ -Real.log (1000000 / 1084261) ∧
    -Real.log (1000000 / 1084261) ≤ (80898649 / 1000000000) := by
  have h := checkLog_sound (w := (84261 / 2084261)) (n := 12)
    (lo := (10112331 / 125000000)) (hi := (80898649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084261 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084261 / 1000000) = 1/(1000000 / 1084261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2413 : Bounds (10112331 / 125000000) (80898649 / 1000000000) (Real.log (1084261 / 1000000)) := by
  have h := reflection_log_2413_neg
  have he : Real.log (1084261 / 1000000) = -Real.log (1000000 / 1084261) := by
    rw [show ((1084261 / 1000000) : ℝ) = ((1000000 / 1084261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2414_neg : (88023889 / 1000000000) ≤ -Real.log (915739 / 1000000) ∧
    -Real.log (915739 / 1000000) ≤ (8802389 / 100000000) := by
  have h := checkLog_sound (w := (84261 / 1915739)) (n := 12)
    (lo := (88023889 / 1000000000)) (hi := (8802389 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915739) = 1/(915739 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2414 : Bounds (-8802389 / 100000000) (-88023889 / 1000000000) (Real.log (915739 / 1000000)) := by
  have h := reflection_log_2414_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2415_neg : (178131 / 25000000) ≤ -Real.log (992900083879 / 1000000000000) ∧
    -Real.log (992900083879 / 1000000000000) ≤ (7125241 / 1000000000) := by
  have h := checkLog_sound (w := (7099916121 / 1992900083879)) (n := 12)
    (lo := (178131 / 25000000)) (hi := (7125241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992900083879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992900083879) = 1/(992900083879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2415 : Bounds (-7125241 / 1000000000) (-178131 / 25000000) (Real.log (992900083879 / 1000000000000)) := by
  have h := reflection_log_2415_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2416_neg : (221509 / 31250000) ≤ -Real.log (992936774151 / 1000000000000) ∧
    -Real.log (992936774151 / 1000000000000) ≤ (7088289 / 1000000000) := by
  have h := checkLog_sound (w := (7063225849 / 1992936774151)) (n := 12)
    (lo := (221509 / 31250000)) (hi := (7088289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992936774151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992936774151) = 1/(992936774151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2416 : Bounds (-7088289 / 1000000000) (-221509 / 31250000) (Real.log (992936774151 / 1000000000000)) := by
  have h := reflection_log_2416_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2417_neg : (42120857 / 250000000) ≤ -Real.log (500000000000 / 591754307243) ∧
    -Real.log (500000000000 / 591754307243) ≤ (168483429 / 1000000000) := by
  have h := checkLog_sound (w := (91754307243 / 1091754307243)) (n := 12)
    (lo := (42120857 / 250000000)) (hi := (168483429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591754307243 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591754307243 / 500000000000) = 1/(500000000000 / 591754307243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2417 : Bounds (42120857 / 250000000) (168483429 / 1000000000) (Real.log (591754307243 / 500000000000)) := by
  have h := reflection_log_2417_neg
  have he : Real.log (591754307243 / 500000000000) = -Real.log (500000000000 / 591754307243) := by
    rw [show ((591754307243 / 500000000000) : ℝ) = ((500000000000 / 591754307243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2418_neg : (84461269 / 500000000) ≤ -Real.log (500000000000 / 592014209289) ∧
    -Real.log (500000000000 / 592014209289) ≤ (168922539 / 1000000000) := by
  have h := checkLog_sound (w := (92014209289 / 1092014209289)) (n := 12)
    (lo := (84461269 / 500000000)) (hi := (168922539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592014209289 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592014209289 / 500000000000) = 1/(500000000000 / 592014209289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2418 : Bounds (84461269 / 500000000) (168922539 / 1000000000) (Real.log (592014209289 / 500000000000)) := by
  have h := reflection_log_2418_neg
  have he : Real.log (592014209289 / 500000000000) = -Real.log (500000000000 / 592014209289) := by
    rw [show ((592014209289 / 500000000000) : ℝ) = ((500000000000 / 592014209289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2419_neg : (168990499 / 500000000) ≤ -Real.log (250000000000 / 350528465049) ∧
    -Real.log (250000000000 / 350528465049) ≤ (337980999 / 1000000000) := by
  have h := checkLog_sound (w := (100528465049 / 600528465049)) (n := 12)
    (lo := (168990499 / 500000000)) (hi := (337980999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((350528465049 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(350528465049 / 250000000000) = 1/(250000000000 / 350528465049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2419 : Bounds (168990499 / 500000000) (337980999 / 1000000000) (Real.log (350528465049 / 250000000000)) := by
  have h := reflection_log_2419_neg
  have he : Real.log (350528465049 / 250000000000) = -Real.log (250000000000 / 350528465049) := by
    rw [show ((350528465049 / 250000000000) : ℝ) = ((250000000000 / 350528465049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2420_neg : (338186767 / 1000000000) ≤ -Real.log (250000000000 / 350600600601) ∧
    -Real.log (250000000000 / 350600600601) ≤ (21136673 / 62500000) := by
  have h := checkLog_sound (w := (100600600601 / 600600600601)) (n := 12)
    (lo := (338186767 / 1000000000)) (hi := (21136673 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((350600600601 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(350600600601 / 250000000000) = 1/(250000000000 / 350600600601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2420 : Bounds (338186767 / 1000000000) (21136673 / 62500000) (Real.log (350600600601 / 250000000000)) := by
  have h := reflection_log_2420_neg
  have he : Real.log (350600600601 / 250000000000) = -Real.log (250000000000 / 350600600601) := by
    rw [show ((350600600601 / 250000000000) : ℝ) = ((250000000000 / 350600600601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2421_neg : (154950359 / 1000000000) ≤ -Real.log (2500 / 2919) ∧
    -Real.log (2500 / 2919) ≤ (3873759 / 25000000) := by
  have h := checkLog_sound (w := (419 / 5419)) (n := 12)
    (lo := (154950359 / 1000000000)) (hi := (3873759 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2919 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2919 / 2500) = 1/(2500 / 2919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2421 : Bounds (154950359 / 1000000000) (3873759 / 25000000) (Real.log (2919 / 2500)) := by
  have h := reflection_log_2421_neg
  have he : Real.log (2919 / 2500) = -Real.log (2500 / 2919) := by
    rw [show ((2919 / 2500) : ℝ) = ((2500 / 2919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2422_neg : (22930273 / 125000000) ≤ -Real.log (2081 / 2500) ∧
    -Real.log (2081 / 2500) ≤ (36688437 / 200000000) := by
  have h := checkLog_sound (w := (419 / 4581)) (n := 12)
    (lo := (22930273 / 125000000)) (hi := (36688437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2081) = 1/(2081 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2422 : Bounds (-36688437 / 200000000) (-22930273 / 125000000) (Real.log (2081 / 2500)) := by
  have h := reflection_log_2422_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2423_neg : (33517 / 200000000) ≤ -Real.log (2500000 / 2500419) ∧
    -Real.log (2500000 / 2500419) ≤ (83793 / 500000000) := by
  have h := checkLog_sound (w := (419 / 5000419)) (n := 12)
    (lo := (33517 / 200000000)) (hi := (83793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500419 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500419 / 2500000) = 1/(2500000 / 2500419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2423 : Bounds (33517 / 200000000) (83793 / 500000000) (Real.log (2500419 / 2500000)) := by
  have h := reflection_log_2423_neg
  have he : Real.log (2500419 / 2500000) = -Real.log (2500000 / 2500419) := by
    rw [show ((2500419 / 2500000) : ℝ) = ((2500000 / 2500419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2424_neg : (83807 / 500000000) ≤ -Real.log (2499581 / 2500000) ∧
    -Real.log (2499581 / 2500000) ≤ (33523 / 200000000) := by
  have h := checkLog_sound (w := (419 / 4999581)) (n := 12)
    (lo := (83807 / 500000000)) (hi := (33523 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499581) = 1/(2499581 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2424 : Bounds (-33523 / 200000000) (-83807 / 500000000) (Real.log (2499581 / 2500000)) := by
  have h := reflection_log_2424_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2425_neg : (20185923 / 250000000) ≤ -Real.log (1000000 / 1084093) ∧
    -Real.log (1000000 / 1084093) ≤ (80743693 / 1000000000) := by
  have h := checkLog_sound (w := (84093 / 2084093)) (n := 12)
    (lo := (20185923 / 250000000)) (hi := (80743693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084093 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084093 / 1000000) = 1/(1000000 / 1084093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2425 : Bounds (20185923 / 250000000) (80743693 / 1000000000) (Real.log (1084093 / 1000000)) := by
  have h := reflection_log_2425_neg
  have he : Real.log (1084093 / 1000000) = -Real.log (1000000 / 1084093) := by
    rw [show ((1084093 / 1000000) : ℝ) = ((1000000 / 1084093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2426_neg : (87840447 / 1000000000) ≤ -Real.log (915907 / 1000000) ∧
    -Real.log (915907 / 1000000) ≤ (1372507 / 15625000) := by
  have h := checkLog_sound (w := (84093 / 1915907)) (n := 12)
    (lo := (87840447 / 1000000000)) (hi := (1372507 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915907) = 1/(915907 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2426 : Bounds (-1372507 / 15625000) (-87840447 / 1000000000) (Real.log (915907 / 1000000)) := by
  have h := reflection_log_2426_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2427_neg : (20236421 / 250000000) ≤ -Real.log (125000 / 135539) ∧
    -Real.log (125000 / 135539) ≤ (16189137 / 200000000) := by
  have h := checkLog_sound (w := (10539 / 260539)) (n := 12)
    (lo := (20236421 / 250000000)) (hi := (16189137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135539 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135539 / 125000) = 1/(125000 / 135539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2427 : Bounds (20236421 / 250000000) (16189137 / 200000000) (Real.log (135539 / 125000)) := by
  have h := reflection_log_2427_neg
  have he : Real.log (135539 / 125000) = -Real.log (125000 / 135539) := by
    rw [show ((135539 / 125000) : ℝ) = ((125000 / 135539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2428_neg : (88079583 / 1000000000) ≤ -Real.log (114461 / 125000) ∧
    -Real.log (114461 / 125000) ≤ (2752487 / 31250000) := by
  have h := checkLog_sound (w := (10539 / 239461)) (n := 12)
    (lo := (88079583 / 1000000000)) (hi := (2752487 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 114461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 114461) = 1/(114461 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2428 : Bounds (-2752487 / 31250000) (-88079583 / 1000000000) (Real.log (114461 / 125000)) := by
  have h := reflection_log_2428_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2429_neg : (7133899 / 1000000000) ≤ -Real.log (15513929479 / 15625000000) ∧
    -Real.log (15513929479 / 15625000000) ≤ (71339 / 10000000) := by
  have h := checkLog_sound (w := (111070521 / 31138929479)) (n := 12)
    (lo := (7133899 / 1000000000)) (hi := (71339 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15513929479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15513929479) = 1/(15513929479 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2429 : Bounds (-71339 / 10000000) (-7133899 / 1000000000) (Real.log (15513929479 / 15625000000)) := by
  have h := reflection_log_2429_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2430_neg : (1419351 / 200000000) ≤ -Real.log (992928367351 / 1000000000000) ∧
    -Real.log (992928367351 / 1000000000000) ≤ (1774189 / 250000000) := by
  have h := checkLog_sound (w := (7071632649 / 1992928367351)) (n := 12)
    (lo := (1419351 / 200000000)) (hi := (1774189 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992928367351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992928367351) = 1/(992928367351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2430 : Bounds (-1774189 / 250000000) (-1419351 / 200000000) (Real.log (992928367351 / 1000000000000)) := by
  have h := reflection_log_2430_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2431_neg : (8429207 / 50000000) ≤ -Real.log (50000000000 / 59181390687) ∧
    -Real.log (50000000000 / 59181390687) ≤ (168584141 / 1000000000) := by
  have h := checkLog_sound (w := (9181390687 / 109181390687)) (n := 12)
    (lo := (8429207 / 50000000)) (hi := (168584141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59181390687 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59181390687 / 50000000000) = 1/(50000000000 / 59181390687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2431 : Bounds (8429207 / 50000000) (168584141 / 1000000000) (Real.log (59181390687 / 50000000000)) := by
  have h := reflection_log_2431_neg
  have he : Real.log (59181390687 / 50000000000) = -Real.log (50000000000 / 59181390687) := by
    rw [show ((59181390687 / 50000000000) : ℝ) = ((50000000000 / 59181390687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0038 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2432_neg : (42256317 / 250000000) ≤ -Real.log (500000000000 / 592075029923) ∧
    -Real.log (500000000000 / 592075029923) ≤ (169025269 / 1000000000) := by
  have h := checkLog_sound (w := (92075029923 / 1092075029923)) (n := 12)
    (lo := (42256317 / 250000000)) (hi := (169025269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592075029923 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592075029923 / 500000000000) = 1/(500000000000 / 592075029923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2432 : Bounds (42256317 / 250000000) (169025269 / 1000000000) (Real.log (592075029923 / 500000000000)) := by
  have h := reflection_log_2432_neg
  have he : Real.log (592075029923 / 500000000000) = -Real.log (500000000000 / 592075029923) := by
    rw [show ((592075029923 / 500000000000) : ℝ) = ((500000000000 / 592075029923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2433_neg : (338186767 / 1000000000) ≤ -Real.log (500000000000 / 701201201201) ∧
    -Real.log (500000000000 / 701201201201) ≤ (21136673 / 62500000) := by
  have h := checkLog_sound (w := (201201201201 / 1201201201201)) (n := 12)
    (lo := (338186767 / 1000000000)) (hi := (21136673 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((701201201201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(701201201201 / 500000000000) = 1/(500000000000 / 701201201201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2433 : Bounds (338186767 / 1000000000) (21136673 / 62500000) (Real.log (701201201201 / 500000000000)) := by
  have h := reflection_log_2433_neg
  have he : Real.log (701201201201 / 500000000000) = -Real.log (500000000000 / 701201201201) := by
    rw [show ((701201201201 / 500000000000) : ℝ) = ((500000000000 / 701201201201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2434_neg : (10574767 / 31250000) ≤ -Real.log (62500000000 / 87668188371) ∧
    -Real.log (62500000000 / 87668188371) ≤ (67678509 / 200000000) := by
  have h := checkLog_sound (w := (25168188371 / 150168188371)) (n := 12)
    (lo := (10574767 / 31250000)) (hi := (67678509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87668188371 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87668188371 / 62500000000) = 1/(62500000000 / 87668188371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2434 : Bounds (10574767 / 31250000) (67678509 / 200000000) (Real.log (87668188371 / 62500000000)) := by
  have h := reflection_log_2434_neg
  have he : Real.log (87668188371 / 62500000000) = -Real.log (62500000000 / 87668188371) := by
    rw [show ((87668188371 / 62500000000) : ℝ) = ((62500000000 / 87668188371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2435_neg : (77518001 / 500000000) ≤ -Real.log (10000 / 11677) ∧
    -Real.log (10000 / 11677) ≤ (155036003 / 1000000000) := by
  have h := checkLog_sound (w := (1677 / 21677)) (n := 12)
    (lo := (77518001 / 500000000)) (hi := (155036003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11677 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11677 / 10000) = 1/(10000 / 11677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2435 : Bounds (77518001 / 500000000) (155036003 / 1000000000) (Real.log (11677 / 10000)) := by
  have h := reflection_log_2435_neg
  have he : Real.log (11677 / 10000) = -Real.log (10000 / 11677) := by
    rw [show ((11677 / 10000) : ℝ) = ((10000 / 11677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2436_neg : (91781163 / 500000000) ≤ -Real.log (8323 / 10000) ∧
    -Real.log (8323 / 10000) ≤ (183562327 / 1000000000) := by
  have h := checkLog_sound (w := (1677 / 18323)) (n := 12)
    (lo := (91781163 / 500000000)) (hi := (183562327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8323) = 1/(8323 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2436 : Bounds (-183562327 / 1000000000) (-91781163 / 500000000) (Real.log (8323 / 10000)) := by
  have h := reflection_log_2436_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2437_neg : (33537 / 200000000) ≤ -Real.log (10000000 / 10001677) ∧
    -Real.log (10000000 / 10001677) ≤ (83843 / 500000000) := by
  have h := checkLog_sound (w := (1677 / 20001677)) (n := 12)
    (lo := (33537 / 200000000)) (hi := (83843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001677 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001677 / 10000000) = 1/(10000000 / 10001677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2437 : Bounds (33537 / 200000000) (83843 / 500000000) (Real.log (10001677 / 10000000)) := by
  have h := reflection_log_2437_neg
  have he : Real.log (10001677 / 10000000) = -Real.log (10000000 / 10001677) := by
    rw [show ((10001677 / 10000000) : ℝ) = ((10000000 / 10001677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2438_neg : (83857 / 500000000) ≤ -Real.log (9998323 / 10000000) ∧
    -Real.log (9998323 / 10000000) ≤ (33543 / 200000000) := by
  have h := checkLog_sound (w := (1677 / 19998323)) (n := 12)
    (lo := (83857 / 500000000)) (hi := (33543 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998323) = 1/(9998323 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2438 : Bounds (-33543 / 200000000) (-83857 / 500000000) (Real.log (9998323 / 10000000)) := by
  have h := reflection_log_2438_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2439_neg : (16158147 / 200000000) ≤ -Real.log (62500 / 67759) ∧
    -Real.log (62500 / 67759) ≤ (5049421 / 62500000) := by
  have h := checkLog_sound (w := (5259 / 130259)) (n := 12)
    (lo := (16158147 / 200000000)) (hi := (5049421 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67759 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67759 / 62500) = 1/(62500 / 67759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2439 : Bounds (16158147 / 200000000) (5049421 / 62500000) (Real.log (67759 / 62500)) := by
  have h := reflection_log_2439_neg
  have he : Real.log (67759 / 62500) = -Real.log (62500 / 67759) := by
    rw [show ((67759 / 62500) : ℝ) = ((62500 / 67759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2440_neg : (87896131 / 1000000000) ≤ -Real.log (57241 / 62500) ∧
    -Real.log (57241 / 62500) ≤ (21974033 / 250000000) := by
  have h := checkLog_sound (w := (5259 / 119741)) (n := 12)
    (lo := (87896131 / 1000000000)) (hi := (21974033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 57241) = 1/(57241 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2440 : Bounds (-21974033 / 250000000) (-87896131 / 1000000000) (Real.log (57241 / 62500)) := by
  have h := reflection_log_2440_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2441_neg : (80992717 / 1000000000) ≤ -Real.log (1000000 / 1084363) ∧
    -Real.log (1000000 / 1084363) ≤ (40496359 / 500000000) := by
  have h := checkLog_sound (w := (84363 / 2084363)) (n := 12)
    (lo := (80992717 / 1000000000)) (hi := (40496359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084363 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084363 / 1000000) = 1/(1000000 / 1084363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2441 : Bounds (80992717 / 1000000000) (40496359 / 500000000) (Real.log (1084363 / 1000000)) := by
  have h := reflection_log_2441_neg
  have he : Real.log (1084363 / 1000000) = -Real.log (1000000 / 1084363) := by
    rw [show ((1084363 / 1000000) : ℝ) = ((1000000 / 1084363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2442_neg : (88135281 / 1000000000) ≤ -Real.log (915637 / 1000000) ∧
    -Real.log (915637 / 1000000) ≤ (44067641 / 500000000) := by
  have h := checkLog_sound (w := (84363 / 1915637)) (n := 12)
    (lo := (88135281 / 1000000000)) (hi := (44067641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915637) = 1/(915637 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2442 : Bounds (-44067641 / 500000000) (-88135281 / 1000000000) (Real.log (915637 / 1000000)) := by
  have h := reflection_log_2442_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2443_neg : (7142563 / 1000000000) ≤ -Real.log (992882884231 / 1000000000000) ∧
    -Real.log (992882884231 / 1000000000000) ≤ (1785641 / 250000000) := by
  have h := checkLog_sound (w := (7117115769 / 1992882884231)) (n := 12)
    (lo := (7142563 / 1000000000)) (hi := (1785641 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992882884231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992882884231) = 1/(992882884231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2443 : Bounds (-1785641 / 250000000) (-7142563 / 1000000000) (Real.log (992882884231 / 1000000000000)) := by
  have h := reflection_log_2443_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2444_neg : (1776349 / 250000000) ≤ -Real.log (3878592919 / 3906250000) ∧
    -Real.log (3878592919 / 3906250000) ≤ (7105397 / 1000000000) := by
  have h := checkLog_sound (w := (27657081 / 7784842919)) (n := 12)
    (lo := (1776349 / 250000000)) (hi := (7105397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3878592919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3878592919) = 1/(3878592919 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2444 : Bounds (-7105397 / 1000000000) (-1776349 / 250000000) (Real.log (3878592919 / 3906250000)) := by
  have h := reflection_log_2444_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2445_neg : (168686867 / 1000000000) ≤ -Real.log (500000000000 / 591874705193) ∧
    -Real.log (500000000000 / 591874705193) ≤ (42171717 / 250000000) := by
  have h := checkLog_sound (w := (91874705193 / 1091874705193)) (n := 12)
    (lo := (168686867 / 1000000000)) (hi := (42171717 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591874705193 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591874705193 / 500000000000) = 1/(500000000000 / 591874705193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2445 : Bounds (168686867 / 1000000000) (42171717 / 250000000) (Real.log (591874705193 / 500000000000)) := by
  have h := reflection_log_2445_neg
  have he : Real.log (591874705193 / 500000000000) = -Real.log (500000000000 / 591874705193) := by
    rw [show ((591874705193 / 500000000000) : ℝ) = ((500000000000 / 591874705193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2446_neg : (84563999 / 500000000) ≤ -Real.log (500000000000 / 592135857333) ∧
    -Real.log (500000000000 / 592135857333) ≤ (169127999 / 1000000000) := by
  have h := checkLog_sound (w := (92135857333 / 1092135857333)) (n := 12)
    (lo := (84563999 / 500000000)) (hi := (169127999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592135857333 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592135857333 / 500000000000) = 1/(500000000000 / 592135857333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2446 : Bounds (84563999 / 500000000) (169127999 / 1000000000) (Real.log (592135857333 / 500000000000)) := by
  have h := reflection_log_2446_neg
  have he : Real.log (592135857333 / 500000000000) = -Real.log (500000000000 / 592135857333) := by
    rw [show ((592135857333 / 500000000000) : ℝ) = ((500000000000 / 592135857333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2447_neg : (10574767 / 31250000) ≤ -Real.log (500000000000 / 701345506967) ∧
    -Real.log (500000000000 / 701345506967) ≤ (67678509 / 200000000) := by
  have h := checkLog_sound (w := (201345506967 / 1201345506967)) (n := 12)
    (lo := (10574767 / 31250000)) (hi := (67678509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((701345506967 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(701345506967 / 500000000000) = 1/(500000000000 / 701345506967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2447 : Bounds (10574767 / 31250000) (67678509 / 200000000) (Real.log (701345506967 / 500000000000)) := by
  have h := reflection_log_2447_neg
  have he : Real.log (701345506967 / 500000000000) = -Real.log (500000000000 / 701345506967) := by
    rw [show ((701345506967 / 500000000000) : ℝ) = ((500000000000 / 701345506967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2448_neg : (42324791 / 125000000) ≤ -Real.log (500000000000 / 701489847411) ∧
    -Real.log (500000000000 / 701489847411) ≤ (338598329 / 1000000000) := by
  have h := checkLog_sound (w := (201489847411 / 1201489847411)) (n := 12)
    (lo := (42324791 / 125000000)) (hi := (338598329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((701489847411 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(701489847411 / 500000000000) = 1/(500000000000 / 701489847411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2448 : Bounds (42324791 / 125000000) (338598329 / 1000000000) (Real.log (701489847411 / 500000000000)) := by
  have h := reflection_log_2448_neg
  have he : Real.log (701489847411 / 500000000000) = -Real.log (500000000000 / 701489847411) := by
    rw [show ((701489847411 / 500000000000) : ℝ) = ((500000000000 / 701489847411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2449_neg : (38780409 / 250000000) ≤ -Real.log (5000 / 5839) ∧
    -Real.log (5000 / 5839) ≤ (155121637 / 1000000000) := by
  have h := checkLog_sound (w := (839 / 10839)) (n := 12)
    (lo := (38780409 / 250000000)) (hi := (155121637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5839 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5839 / 5000) = 1/(5000 / 5839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2449 : Bounds (38780409 / 250000000) (155121637 / 1000000000) (Real.log (5839 / 5000)) := by
  have h := reflection_log_2449_neg
  have he : Real.log (5839 / 5000) = -Real.log (5000 / 5839) := by
    rw [show ((5839 / 5000) : ℝ) = ((5000 / 5839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2450_neg : (91841241 / 500000000) ≤ -Real.log (4161 / 5000) ∧
    -Real.log (4161 / 5000) ≤ (183682483 / 1000000000) := by
  have h := checkLog_sound (w := (839 / 9161)) (n := 12)
    (lo := (91841241 / 500000000)) (hi := (183682483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4161) = 1/(4161 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2450 : Bounds (-183682483 / 1000000000) (-91841241 / 500000000) (Real.log (4161 / 5000)) := by
  have h := reflection_log_2450_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2451_neg : (33557 / 200000000) ≤ -Real.log (5000000 / 5000839) ∧
    -Real.log (5000000 / 5000839) ≤ (83893 / 500000000) := by
  have h := checkLog_sound (w := (839 / 10000839)) (n := 12)
    (lo := (33557 / 200000000)) (hi := (83893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000839 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000839 / 5000000) = 1/(5000000 / 5000839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2451 : Bounds (33557 / 200000000) (83893 / 500000000) (Real.log (5000839 / 5000000)) := by
  have h := reflection_log_2451_neg
  have he : Real.log (5000839 / 5000000) = -Real.log (5000000 / 5000839) := by
    rw [show ((5000839 / 5000000) : ℝ) = ((5000000 / 5000839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2452_neg : (83907 / 500000000) ≤ -Real.log (4999161 / 5000000) ∧
    -Real.log (4999161 / 5000000) ≤ (33563 / 200000000) := by
  have h := checkLog_sound (w := (839 / 9999161)) (n := 12)
    (lo := (83907 / 500000000)) (hi := (33563 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999161) = 1/(4999161 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2452 : Bounds (-33563 / 200000000) (-83907 / 500000000) (Real.log (4999161 / 5000000)) := by
  have h := reflection_log_2452_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2453_neg : (5052361 / 62500000) ≤ -Real.log (200000 / 216839) ∧
    -Real.log (200000 / 216839) ≤ (80837777 / 1000000000) := by
  have h := checkLog_sound (w := (16839 / 416839)) (n := 12)
    (lo := (5052361 / 62500000)) (hi := (80837777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216839 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216839 / 200000) = 1/(200000 / 216839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2453 : Bounds (5052361 / 62500000) (80837777 / 1000000000) (Real.log (216839 / 200000)) := by
  have h := reflection_log_2453_neg
  have he : Real.log (216839 / 200000) = -Real.log (200000 / 216839) := by
    rw [show ((216839 / 200000) : ℝ) = ((200000 / 216839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2454_neg : (87951819 / 1000000000) ≤ -Real.log (183161 / 200000) ∧
    -Real.log (183161 / 200000) ≤ (4397591 / 50000000) := by
  have h := checkLog_sound (w := (16839 / 383161)) (n := 12)
    (lo := (87951819 / 1000000000)) (hi := (4397591 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183161) = 1/(183161 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2454 : Bounds (-4397591 / 50000000) (-87951819 / 1000000000) (Real.log (183161 / 200000)) := by
  have h := reflection_log_2454_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2455_neg : (20259937 / 250000000) ≤ -Real.log (500000 / 542207) ∧
    -Real.log (500000 / 542207) ≤ (81039749 / 1000000000) := by
  have h := checkLog_sound (w := (42207 / 1042207)) (n := 12)
    (lo := (20259937 / 250000000)) (hi := (81039749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542207 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542207 / 500000) = 1/(500000 / 542207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2455 : Bounds (20259937 / 250000000) (81039749 / 1000000000) (Real.log (542207 / 500000)) := by
  have h := reflection_log_2455_neg
  have he : Real.log (542207 / 500000) = -Real.log (500000 / 542207) := by
    rw [show ((542207 / 500000) : ℝ) = ((500000 / 542207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2456_neg : (88190981 / 1000000000) ≤ -Real.log (457793 / 500000) ∧
    -Real.log (457793 / 500000) ≤ (44095491 / 500000000) := by
  have h := checkLog_sound (w := (42207 / 957793)) (n := 12)
    (lo := (88190981 / 1000000000)) (hi := (44095491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457793) = 1/(457793 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2456 : Bounds (-44095491 / 500000000) (-88190981 / 1000000000) (Real.log (457793 / 500000)) := by
  have h := reflection_log_2456_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2457_neg : (55869 / 7812500) ≤ -Real.log (248218569151 / 250000000000) ∧
    -Real.log (248218569151 / 250000000000) ≤ (7151233 / 1000000000) := by
  have h := checkLog_sound (w := (1781430849 / 498218569151)) (n := 12)
    (lo := (55869 / 7812500)) (hi := (7151233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248218569151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248218569151) = 1/(248218569151 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2457 : Bounds (-7151233 / 1000000000) (-55869 / 7812500) (Real.log (248218569151 / 250000000000)) := by
  have h := reflection_log_2457_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2458_neg : (3557021 / 500000000) ≤ -Real.log (39716448079 / 40000000000) ∧
    -Real.log (39716448079 / 40000000000) ≤ (7114043 / 1000000000) := by
  have h := checkLog_sound (w := (283551921 / 79716448079)) (n := 12)
    (lo := (3557021 / 500000000)) (hi := (7114043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39716448079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39716448079) = 1/(39716448079 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2458 : Bounds (-7114043 / 1000000000) (-3557021 / 500000000) (Real.log (39716448079 / 40000000000)) := by
  have h := reflection_log_2458_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2459_neg : (33757919 / 200000000) ≤ -Real.log (31250000000 / 36995969393) ∧
    -Real.log (31250000000 / 36995969393) ≤ (42197399 / 250000000) := by
  have h := checkLog_sound (w := (5745969393 / 68245969393)) (n := 12)
    (lo := (33757919 / 200000000)) (hi := (42197399 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36995969393 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36995969393 / 31250000000) = 1/(31250000000 / 36995969393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2459 : Bounds (33757919 / 200000000) (42197399 / 250000000) (Real.log (36995969393 / 31250000000)) := by
  have h := reflection_log_2459_neg
  have he : Real.log (36995969393 / 31250000000) = -Real.log (31250000000 / 36995969393) := by
    rw [show ((36995969393 / 31250000000) : ℝ) = ((31250000000 / 36995969393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2460_neg : (16923073 / 100000000) ≤ -Real.log (250000000000 / 296098345759) ∧
    -Real.log (250000000000 / 296098345759) ≤ (169230731 / 1000000000) := by
  have h := checkLog_sound (w := (46098345759 / 546098345759)) (n := 12)
    (lo := (16923073 / 100000000)) (hi := (169230731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296098345759 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296098345759 / 250000000000) = 1/(250000000000 / 296098345759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2460 : Bounds (16923073 / 100000000) (169230731 / 1000000000) (Real.log (296098345759 / 250000000000)) := by
  have h := reflection_log_2460_neg
  have he : Real.log (296098345759 / 250000000000) = -Real.log (250000000000 / 296098345759) := by
    rw [show ((296098345759 / 250000000000) : ℝ) = ((250000000000 / 296098345759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2461_neg : (42324791 / 125000000) ≤ -Real.log (50000000000 / 70148984741) ∧
    -Real.log (50000000000 / 70148984741) ≤ (338598329 / 1000000000) := by
  have h := checkLog_sound (w := (20148984741 / 120148984741)) (n := 12)
    (lo := (42324791 / 125000000)) (hi := (338598329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70148984741 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(70148984741 / 50000000000) = 1/(50000000000 / 70148984741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2461 : Bounds (42324791 / 125000000) (338598329 / 1000000000) (Real.log (70148984741 / 50000000000)) := by
  have h := reflection_log_2461_neg
  have he : Real.log (70148984741 / 50000000000) = -Real.log (50000000000 / 70148984741) := by
    rw [show ((70148984741 / 50000000000) : ℝ) = ((50000000000 / 70148984741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2462_neg : (338804119 / 1000000000) ≤ -Real.log (500000000000 / 701634222543) ∧
    -Real.log (500000000000 / 701634222543) ≤ (8470103 / 25000000) := by
  have h := checkLog_sound (w := (201634222543 / 1201634222543)) (n := 12)
    (lo := (338804119 / 1000000000)) (hi := (8470103 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((701634222543 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(701634222543 / 500000000000) = 1/(500000000000 / 701634222543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2462 : Bounds (338804119 / 1000000000) (8470103 / 25000000) (Real.log (701634222543 / 500000000000)) := by
  have h := reflection_log_2462_neg
  have he : Real.log (701634222543 / 500000000000) = -Real.log (500000000000 / 701634222543) := by
    rw [show ((701634222543 / 500000000000) : ℝ) = ((500000000000 / 701634222543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2463_neg : (4850227 / 31250000) ≤ -Real.log (10000 / 11679) ∧
    -Real.log (10000 / 11679) ≤ (31041453 / 200000000) := by
  have h := checkLog_sound (w := (1679 / 21679)) (n := 12)
    (lo := (4850227 / 31250000)) (hi := (31041453 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11679 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11679 / 10000) = 1/(10000 / 11679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2463 : Bounds (4850227 / 31250000) (31041453 / 200000000) (Real.log (11679 / 10000)) := by
  have h := reflection_log_2463_neg
  have he : Real.log (11679 / 10000) = -Real.log (10000 / 11679) := by
    rw [show ((11679 / 10000) : ℝ) = ((10000 / 11679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2464_neg : (183802653 / 1000000000) ≤ -Real.log (8321 / 10000) ∧
    -Real.log (8321 / 10000) ≤ (91901327 / 500000000) := by
  have h := checkLog_sound (w := (1679 / 18321)) (n := 12)
    (lo := (183802653 / 1000000000)) (hi := (91901327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8321) = 1/(8321 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2464 : Bounds (-91901327 / 500000000) (-183802653 / 1000000000) (Real.log (8321 / 10000)) := by
  have h := reflection_log_2464_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2465_neg : (33577 / 200000000) ≤ -Real.log (10000000 / 10001679) ∧
    -Real.log (10000000 / 10001679) ≤ (83943 / 500000000) := by
  have h := checkLog_sound (w := (1679 / 20001679)) (n := 12)
    (lo := (33577 / 200000000)) (hi := (83943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001679 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001679 / 10000000) = 1/(10000000 / 10001679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2465 : Bounds (33577 / 200000000) (83943 / 500000000) (Real.log (10001679 / 10000000)) := by
  have h := reflection_log_2465_neg
  have he : Real.log (10001679 / 10000000) = -Real.log (10000000 / 10001679) := by
    rw [show ((10001679 / 10000000) : ℝ) = ((10000000 / 10001679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2466_neg : (83957 / 500000000) ≤ -Real.log (9998321 / 10000000) ∧
    -Real.log (9998321 / 10000000) ≤ (33583 / 200000000) := by
  have h := checkLog_sound (w := (1679 / 19998321)) (n := 12)
    (lo := (83957 / 500000000)) (hi := (33583 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998321) = 1/(9998321 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2466 : Bounds (-33583 / 200000000) (-83957 / 500000000) (Real.log (9998321 / 10000000)) := by
  have h := reflection_log_2466_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2467_neg : (40442407 / 500000000) ≤ -Real.log (500000 / 542123) ∧
    -Real.log (500000 / 542123) ≤ (16176963 / 200000000) := by
  have h := checkLog_sound (w := (42123 / 1042123)) (n := 12)
    (lo := (40442407 / 500000000)) (hi := (16176963 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542123 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542123 / 500000) = 1/(500000 / 542123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2467 : Bounds (40442407 / 500000000) (16176963 / 200000000) (Real.log (542123 / 500000)) := by
  have h := reflection_log_2467_neg
  have he : Real.log (542123 / 500000) = -Real.log (500000 / 542123) := by
    rw [show ((542123 / 500000) : ℝ) = ((500000 / 542123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2468_neg : (88007509 / 1000000000) ≤ -Real.log (457877 / 500000) ∧
    -Real.log (457877 / 500000) ≤ (8800751 / 100000000) := by
  have h := checkLog_sound (w := (42123 / 957877)) (n := 12)
    (lo := (88007509 / 1000000000)) (hi := (8800751 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457877) = 1/(457877 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2468 : Bounds (-8800751 / 100000000) (-88007509 / 1000000000) (Real.log (457877 / 500000)) := by
  have h := reflection_log_2468_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2469_neg : (16217171 / 200000000) ≤ -Real.log (62500 / 67779) ∧
    -Real.log (62500 / 67779) ≤ (2533933 / 31250000) := by
  have h := checkLog_sound (w := (5279 / 130279)) (n := 12)
    (lo := (16217171 / 200000000)) (hi := (2533933 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67779 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67779 / 62500) = 1/(62500 / 67779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2469 : Bounds (16217171 / 200000000) (2533933 / 31250000) (Real.log (67779 / 62500)) := by
  have h := reflection_log_2469_neg
  have he : Real.log (67779 / 62500) = -Real.log (62500 / 67779) := by
    rw [show ((67779 / 62500) : ℝ) = ((62500 / 67779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2470_neg : (11030699 / 125000000) ≤ -Real.log (57221 / 62500) ∧
    -Real.log (57221 / 62500) ≤ (88245593 / 1000000000) := by
  have h := checkLog_sound (w := (5279 / 119721)) (n := 12)
    (lo := (11030699 / 125000000)) (hi := (88245593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 57221) = 1/(57221 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2470 : Bounds (-88245593 / 1000000000) (-11030699 / 125000000) (Real.log (57221 / 62500)) := by
  have h := reflection_log_2470_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2471_neg : (7159737 / 1000000000) ≤ -Real.log (3878382159 / 3906250000) ∧
    -Real.log (3878382159 / 3906250000) ≤ (3579869 / 500000000) := by
  have h := checkLog_sound (w := (27867841 / 7784632159)) (n := 12)
    (lo := (7159737 / 1000000000)) (hi := (3579869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3878382159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3878382159) = 1/(3878382159 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2471 : Bounds (-3579869 / 500000000) (-7159737 / 1000000000) (Real.log (3878382159 / 3906250000)) := by
  have h := reflection_log_2471_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2472_neg : (3561347 / 500000000) ≤ -Real.log (248225652871 / 250000000000) ∧
    -Real.log (248225652871 / 250000000000) ≤ (1424539 / 200000000) := by
  have h := checkLog_sound (w := (1774347129 / 498225652871)) (n := 12)
    (lo := (3561347 / 500000000)) (hi := (1424539 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248225652871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248225652871) = 1/(248225652871 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2472 : Bounds (-1424539 / 200000000) (-3561347 / 500000000) (Real.log (248225652871 / 250000000000)) := by
  have h := reflection_log_2472_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2473_neg : (168892323 / 1000000000) ≤ -Real.log (125000000000 / 147999080539) ∧
    -Real.log (125000000000 / 147999080539) ≤ (42223081 / 250000000) := by
  have h := checkLog_sound (w := (22999080539 / 272999080539)) (n := 12)
    (lo := (168892323 / 1000000000)) (hi := (42223081 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147999080539 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147999080539 / 125000000000) = 1/(125000000000 / 147999080539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2473 : Bounds (168892323 / 1000000000) (42223081 / 250000000) (Real.log (147999080539 / 125000000000)) := by
  have h := reflection_log_2473_neg
  have he : Real.log (147999080539 / 125000000000) = -Real.log (125000000000 / 147999080539) := by
    rw [show ((147999080539 / 125000000000) : ℝ) = ((125000000000 / 147999080539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2474_neg : (21166431 / 125000000) ≤ -Real.log (976562500 / 1156750663) ∧
    -Real.log (976562500 / 1156750663) ≤ (169331449 / 1000000000) := by
  have h := checkLog_sound (w := (180188163 / 2133313163)) (n := 12)
    (lo := (21166431 / 125000000)) (hi := (169331449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1156750663 / 976562500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1156750663 / 976562500) = 1/(976562500 / 1156750663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2474 : Bounds (21166431 / 125000000) (169331449 / 1000000000) (Real.log (1156750663 / 976562500)) := by
  have h := reflection_log_2474_neg
  have he : Real.log (1156750663 / 976562500) = -Real.log (976562500 / 1156750663) := by
    rw [show ((1156750663 / 976562500) : ℝ) = ((976562500 / 1156750663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2475_neg : (338804119 / 1000000000) ≤ -Real.log (250000000000 / 350817111271) ∧
    -Real.log (250000000000 / 350817111271) ≤ (8470103 / 25000000) := by
  have h := checkLog_sound (w := (100817111271 / 600817111271)) (n := 12)
    (lo := (338804119 / 1000000000)) (hi := (8470103 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((350817111271 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(350817111271 / 250000000000) = 1/(250000000000 / 350817111271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2475 : Bounds (338804119 / 1000000000) (8470103 / 25000000) (Real.log (350817111271 / 250000000000)) := by
  have h := reflection_log_2475_neg
  have he : Real.log (350817111271 / 250000000000) = -Real.log (250000000000 / 350817111271) := by
    rw [show ((350817111271 / 250000000000) : ℝ) = ((250000000000 / 350817111271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2476_neg : (339009917 / 1000000000) ≤ -Real.log (62500000000 / 87722329047) ∧
    -Real.log (62500000000 / 87722329047) ≤ (169504959 / 500000000) := by
  have h := checkLog_sound (w := (25222329047 / 150222329047)) (n := 12)
    (lo := (339009917 / 1000000000)) (hi := (169504959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87722329047 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87722329047 / 62500000000) = 1/(62500000000 / 87722329047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2476 : Bounds (339009917 / 1000000000) (169504959 / 500000000) (Real.log (87722329047 / 62500000000)) := by
  have h := reflection_log_2476_neg
  have he : Real.log (87722329047 / 62500000000) = -Real.log (62500000000 / 87722329047) := by
    rw [show ((87722329047 / 62500000000) : ℝ) = ((62500000000 / 87722329047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2477_neg : (38823221 / 250000000) ≤ -Real.log (125 / 146) ∧
    -Real.log (125 / 146) ≤ (31058577 / 200000000) := by
  have h := checkLog_sound (w := (21 / 271)) (n := 12)
    (lo := (38823221 / 250000000)) (hi := (31058577 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146 / 125) = 1/(125 / 146) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2477 : Bounds (38823221 / 250000000) (31058577 / 200000000) (Real.log (146 / 125)) := by
  have h := reflection_log_2477_neg
  have he : Real.log (146 / 125) = -Real.log (125 / 146) := by
    rw [show ((146 / 125) : ℝ) = ((125 / 146) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2478_neg : (91961419 / 500000000) ≤ -Real.log (104 / 125) ∧
    -Real.log (104 / 125) ≤ (183922839 / 1000000000) := by
  have h := checkLog_sound (w := (21 / 229)) (n := 12)
    (lo := (91961419 / 500000000)) (hi := (183922839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 104) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 104) = 1/(104 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2478 : Bounds (-183922839 / 1000000000) (-91961419 / 500000000) (Real.log (104 / 125)) := by
  have h := reflection_log_2478_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2479_neg : (33597 / 200000000) ≤ -Real.log (125000 / 125021) ∧
    -Real.log (125000 / 125021) ≤ (83993 / 500000000) := by
  have h := checkLog_sound (w := (21 / 250021)) (n := 12)
    (lo := (33597 / 200000000)) (hi := (83993 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125021 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125021 / 125000) = 1/(125000 / 125021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2479 : Bounds (33597 / 200000000) (83993 / 500000000) (Real.log (125021 / 125000)) := by
  have h := reflection_log_2479_neg
  have he : Real.log (125021 / 125000) = -Real.log (125000 / 125021) := by
    rw [show ((125021 / 125000) : ℝ) = ((125000 / 125021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2480_neg : (84007 / 500000000) ≤ -Real.log (124979 / 125000) ∧
    -Real.log (124979 / 125000) ≤ (33603 / 200000000) := by
  have h := checkLog_sound (w := (21 / 249979)) (n := 12)
    (lo := (84007 / 500000000)) (hi := (33603 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124979) = 1/(124979 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2480 : Bounds (-33603 / 200000000) (-84007 / 500000000) (Real.log (124979 / 125000)) := by
  have h := reflection_log_2480_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2481_neg : (5058183 / 62500000) ≤ -Real.log (125000 / 135537) ∧
    -Real.log (125000 / 135537) ≤ (80930929 / 1000000000) := by
  have h := checkLog_sound (w := (10537 / 260537)) (n := 12)
    (lo := (5058183 / 62500000)) (hi := (80930929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135537 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135537 / 125000) = 1/(125000 / 135537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2481 : Bounds (5058183 / 62500000) (80930929 / 1000000000) (Real.log (135537 / 125000)) := by
  have h := reflection_log_2481_neg
  have he : Real.log (135537 / 125000) = -Real.log (125000 / 135537) := by
    rw [show ((135537 / 125000) : ℝ) = ((125000 / 135537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2482_neg : (8806211 / 100000000) ≤ -Real.log (114463 / 125000) ∧
    -Real.log (114463 / 125000) ≤ (88062111 / 1000000000) := by
  have h := checkLog_sound (w := (10537 / 239463)) (n := 12)
    (lo := (8806211 / 100000000)) (hi := (88062111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 114463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 114463) = 1/(114463 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2482 : Bounds (-88062111 / 1000000000) (-8806211 / 100000000) (Real.log (114463 / 125000)) := by
  have h := reflection_log_2482_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2483_neg : (40566441 / 500000000) ≤ -Real.log (200000 / 216903) ∧
    -Real.log (200000 / 216903) ≤ (81132883 / 1000000000) := by
  have h := checkLog_sound (w := (16903 / 416903)) (n := 12)
    (lo := (40566441 / 500000000)) (hi := (81132883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216903 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216903 / 200000) = 1/(200000 / 216903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2483 : Bounds (40566441 / 500000000) (81132883 / 1000000000) (Real.log (216903 / 200000)) := by
  have h := reflection_log_2483_neg
  have he : Real.log (216903 / 200000) = -Real.log (200000 / 216903) := by
    rw [show ((216903 / 200000) : ℝ) = ((200000 / 216903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2484_neg : (88301299 / 1000000000) ≤ -Real.log (183097 / 200000) ∧
    -Real.log (183097 / 200000) ≤ (883013 / 10000000) := by
  have h := checkLog_sound (w := (16903 / 383097)) (n := 12)
    (lo := (88301299 / 1000000000)) (hi := (883013 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183097) = 1/(183097 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2484 : Bounds (-883013 / 10000000) (-88301299 / 1000000000) (Real.log (183097 / 200000)) := by
  have h := reflection_log_2484_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2485_neg : (7168417 / 1000000000) ≤ -Real.log (39714288591 / 40000000000) ∧
    -Real.log (39714288591 / 40000000000) ≤ (3584209 / 500000000) := by
  have h := checkLog_sound (w := (285711409 / 79714288591)) (n := 12)
    (lo := (7168417 / 1000000000)) (hi := (3584209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39714288591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39714288591) = 1/(39714288591 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2485 : Bounds (-3584209 / 500000000) (-7168417 / 1000000000) (Real.log (39714288591 / 40000000000)) := by
  have h := reflection_log_2485_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2486_neg : (3565591 / 500000000) ≤ -Real.log (15513971631 / 15625000000) ∧
    -Real.log (15513971631 / 15625000000) ≤ (7131183 / 1000000000) := by
  have h := checkLog_sound (w := (111028369 / 31138971631)) (n := 12)
    (lo := (3565591 / 500000000)) (hi := (7131183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15513971631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15513971631) = 1/(15513971631 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2486 : Bounds (-7131183 / 1000000000) (-3565591 / 500000000) (Real.log (15513971631 / 15625000000)) := by
  have h := reflection_log_2486_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2487_neg : (168993039 / 1000000000) ≤ -Real.log (50000000000 / 59205594821) ∧
    -Real.log (50000000000 / 59205594821) ≤ (2112413 / 12500000) := by
  have h := checkLog_sound (w := (9205594821 / 109205594821)) (n := 12)
    (lo := (168993039 / 1000000000)) (hi := (2112413 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59205594821 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59205594821 / 50000000000) = 1/(50000000000 / 59205594821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2487 : Bounds (168993039 / 1000000000) (2112413 / 12500000) (Real.log (59205594821 / 50000000000)) := by
  have h := reflection_log_2487_neg
  have he : Real.log (59205594821 / 50000000000) = -Real.log (50000000000 / 59205594821) := by
    rw [show ((59205594821 / 50000000000) : ℝ) = ((50000000000 / 59205594821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2488_neg : (169434181 / 1000000000) ≤ -Real.log (100000000000 / 118463437413) ∧
    -Real.log (100000000000 / 118463437413) ≤ (84717091 / 500000000) := by
  have h := checkLog_sound (w := (18463437413 / 218463437413)) (n := 12)
    (lo := (169434181 / 1000000000)) (hi := (84717091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118463437413 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118463437413 / 100000000000) = 1/(100000000000 / 118463437413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2488 : Bounds (169434181 / 1000000000) (84717091 / 500000000) (Real.log (118463437413 / 100000000000)) := by
  have h := reflection_log_2488_neg
  have he : Real.log (118463437413 / 100000000000) = -Real.log (100000000000 / 118463437413) := by
    rw [show ((118463437413 / 100000000000) : ℝ) = ((100000000000 / 118463437413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2489_neg : (339009917 / 1000000000) ≤ -Real.log (4000000000 / 5614229059) ∧
    -Real.log (4000000000 / 5614229059) ≤ (169504959 / 500000000) := by
  have h := checkLog_sound (w := (1614229059 / 9614229059)) (n := 12)
    (lo := (339009917 / 1000000000)) (hi := (169504959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5614229059 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5614229059 / 4000000000) = 1/(4000000000 / 5614229059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2489 : Bounds (339009917 / 1000000000) (169504959 / 500000000) (Real.log (5614229059 / 4000000000)) := by
  have h := reflection_log_2489_neg
  have he : Real.log (5614229059 / 4000000000) = -Real.log (4000000000 / 5614229059) := by
    rw [show ((5614229059 / 4000000000) : ℝ) = ((4000000000 / 5614229059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2490_neg : (169607861 / 500000000) ≤ -Real.log (125000000000 / 175480769231) ∧
    -Real.log (125000000000 / 175480769231) ≤ (339215723 / 1000000000) := by
  have h := checkLog_sound (w := (50480769231 / 300480769231)) (n := 12)
    (lo := (169607861 / 500000000)) (hi := (339215723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175480769231 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175480769231 / 125000000000) = 1/(125000000000 / 175480769231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2490 : Bounds (169607861 / 500000000) (339215723 / 1000000000) (Real.log (175480769231 / 125000000000)) := by
  have h := reflection_log_2490_neg
  have he : Real.log (175480769231 / 125000000000) = -Real.log (125000000000 / 175480769231) := by
    rw [show ((175480769231 / 125000000000) : ℝ) = ((125000000000 / 175480769231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2491_neg : (155378497 / 1000000000) ≤ -Real.log (10000 / 11681) ∧
    -Real.log (10000 / 11681) ≤ (77689249 / 500000000) := by
  have h := checkLog_sound (w := (1681 / 21681)) (n := 12)
    (lo := (155378497 / 1000000000)) (hi := (77689249 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11681 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11681 / 10000) = 1/(10000 / 11681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2491 : Bounds (155378497 / 1000000000) (77689249 / 500000000) (Real.log (11681 / 10000)) := by
  have h := reflection_log_2491_neg
  have he : Real.log (11681 / 10000) = -Real.log (10000 / 11681) := by
    rw [show ((11681 / 10000) : ℝ) = ((10000 / 11681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2492_neg : (184043037 / 1000000000) ≤ -Real.log (8319 / 10000) ∧
    -Real.log (8319 / 10000) ≤ (92021519 / 500000000) := by
  have h := checkLog_sound (w := (1681 / 18319)) (n := 12)
    (lo := (184043037 / 1000000000)) (hi := (92021519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8319) = 1/(8319 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2492 : Bounds (-92021519 / 500000000) (-184043037 / 1000000000) (Real.log (8319 / 10000)) := by
  have h := reflection_log_2492_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2493_neg : (33617 / 200000000) ≤ -Real.log (10000000 / 10001681) ∧
    -Real.log (10000000 / 10001681) ≤ (84043 / 500000000) := by
  have h := checkLog_sound (w := (1681 / 20001681)) (n := 12)
    (lo := (33617 / 200000000)) (hi := (84043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001681 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001681 / 10000000) = 1/(10000000 / 10001681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2493 : Bounds (33617 / 200000000) (84043 / 500000000) (Real.log (10001681 / 10000000)) := by
  have h := reflection_log_2493_neg
  have he : Real.log (10001681 / 10000000) = -Real.log (10000000 / 10001681) := by
    rw [show ((10001681 / 10000000) : ℝ) = ((10000000 / 10001681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2494_neg : (84057 / 500000000) ≤ -Real.log (9998319 / 10000000) ∧
    -Real.log (9998319 / 10000000) ≤ (33623 / 200000000) := by
  have h := checkLog_sound (w := (1681 / 19998319)) (n := 12)
    (lo := (84057 / 500000000)) (hi := (33623 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998319) = 1/(9998319 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2494 : Bounds (-33623 / 200000000) (-84057 / 500000000) (Real.log (9998319 / 10000000)) := by
  have h := reflection_log_2494_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2495_neg : (40488981 / 500000000) ≤ -Real.log (1000000 / 1084347) ∧
    -Real.log (1000000 / 1084347) ≤ (80977963 / 1000000000) := by
  have h := checkLog_sound (w := (84347 / 2084347)) (n := 12)
    (lo := (40488981 / 500000000)) (hi := (80977963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084347 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084347 / 1000000) = 1/(1000000 / 1084347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2495 : Bounds (40488981 / 500000000) (80977963 / 1000000000) (Real.log (1084347 / 1000000)) := by
  have h := reflection_log_2495_neg
  have he : Real.log (1084347 / 1000000) = -Real.log (1000000 / 1084347) := by
    rw [show ((1084347 / 1000000) : ℝ) = ((1000000 / 1084347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


