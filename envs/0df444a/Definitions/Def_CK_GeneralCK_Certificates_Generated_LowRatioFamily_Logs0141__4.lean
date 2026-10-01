-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0141__4
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0141__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:25:00.427986+00:00
-- url     : https://prove2.me/theorems/055156b6-6cf2-46fd-853d-51f625fef903
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0141 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0142, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0141 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0142, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0143, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0144)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0141 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0142, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0143, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0144)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0141 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0142, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0143, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0144) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0141 (+3 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0142, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0143, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0144).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0141__4_q02

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0144 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9216_neg : (576449379 / 1000000000) ≤ -Real.log (125000000000 / 222463516331) ∧
    -Real.log (125000000000 / 222463516331) ≤ (28822469 / 50000000) := by
  have h := checkLog_sound (w := (97463516331 / 347463516331)) (n := 12)
    (lo := (576449379 / 1000000000)) (hi := (28822469 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((222463516331 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(222463516331 / 125000000000) = 1/(125000000000 / 222463516331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9216 : Bounds (576449379 / 1000000000) (28822469 / 50000000) (Real.log (222463516331 / 125000000000)) := by
  have h := reflection_log_9216_neg
  have he : Real.log (222463516331 / 125000000000) = -Real.log (125000000000 / 222463516331) := by
    rw [show ((222463516331 / 125000000000) : ℝ) = ((125000000000 / 222463516331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9217_neg : (123820511 / 500000000) ≤ -Real.log (1000 / 1281) ∧
    -Real.log (1000 / 1281) ≤ (247641023 / 1000000000) := by
  have h := checkLog_sound (w := (281 / 2281)) (n := 12)
    (lo := (123820511 / 500000000)) (hi := (247641023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1281 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1281 / 1000) = 1/(1000 / 1281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9217 : Bounds (123820511 / 500000000) (247641023 / 1000000000) (Real.log (1281 / 1000)) := by
  have h := reflection_log_9217_neg
  have he : Real.log (1281 / 1000) = -Real.log (1000 / 1281) := by
    rw [show ((1281 / 1000) : ℝ) = ((1000 / 1281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9218_neg : (329893921 / 1000000000) ≤ -Real.log (719 / 1000) ∧
    -Real.log (719 / 1000) ≤ (164946961 / 500000000) := by
  have h := checkLog_sound (w := (281 / 1719)) (n := 12)
    (lo := (329893921 / 1000000000)) (hi := (164946961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 719) = 1/(719 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9218 : Bounds (-164946961 / 500000000) (-329893921 / 1000000000) (Real.log (719 / 1000)) := by
  have h := reflection_log_9218_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9219_neg : (439 / 1562500) ≤ -Real.log (1000000 / 1000281) ∧
    -Real.log (1000000 / 1000281) ≤ (280961 / 1000000000) := by
  have h := checkLog_sound (w := (281 / 2000281)) (n := 12)
    (lo := (439 / 1562500)) (hi := (280961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000281 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000281 / 1000000) = 1/(1000000 / 1000281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9219 : Bounds (439 / 1562500) (280961 / 1000000000) (Real.log (1000281 / 1000000)) := by
  have h := reflection_log_9219_neg
  have he : Real.log (1000281 / 1000000) = -Real.log (1000000 / 1000281) := by
    rw [show ((1000281 / 1000000) : ℝ) = ((1000000 / 1000281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9220_neg : (281039 / 1000000000) ≤ -Real.log (999719 / 1000000) ∧
    -Real.log (999719 / 1000000) ≤ (3513 / 12500000) := by
  have h := checkLog_sound (w := (281 / 1999719)) (n := 12)
    (lo := (281039 / 1000000000)) (hi := (3513 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999719) = 1/(999719 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9220 : Bounds (-3513 / 12500000) (-281039 / 1000000000) (Real.log (999719 / 1000000)) := by
  have h := reflection_log_9220_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9221_neg : (5316463 / 40000000) ≤ -Real.log (1000000 / 1142149) ∧
    -Real.log (1000000 / 1142149) ≤ (16613947 / 125000000) := by
  have h := checkLog_sound (w := (142149 / 2142149)) (n := 12)
    (lo := (5316463 / 40000000)) (hi := (16613947 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1142149 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1142149 / 1000000) = 1/(1000000 / 1142149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9221 : Bounds (5316463 / 40000000) (16613947 / 125000000) (Real.log (1142149 / 1000000)) := by
  have h := reflection_log_9221_neg
  have he : Real.log (1142149 / 1000000) = -Real.log (1000000 / 1142149) := by
    rw [show ((1142149 / 1000000) : ℝ) = ((1000000 / 1142149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9222_neg : (76662427 / 500000000) ≤ -Real.log (857851 / 1000000) ∧
    -Real.log (857851 / 1000000) ≤ (30664971 / 200000000) := by
  have h := checkLog_sound (w := (142149 / 1857851)) (n := 12)
    (lo := (76662427 / 500000000)) (hi := (30664971 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 857851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 857851) = 1/(857851 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9222 : Bounds (-30664971 / 200000000) (-76662427 / 500000000) (Real.log (857851 / 1000000)) := by
  have h := reflection_log_9222_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9223_neg : (66691253 / 500000000) ≤ -Real.log (1000000 / 1142687) ∧
    -Real.log (1000000 / 1142687) ≤ (133382507 / 1000000000) := by
  have h := checkLog_sound (w := (142687 / 2142687)) (n := 12)
    (lo := (66691253 / 500000000)) (hi := (133382507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1142687 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1142687 / 1000000) = 1/(1000000 / 1142687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9223 : Bounds (66691253 / 500000000) (133382507 / 1000000000) (Real.log (1142687 / 1000000)) := by
  have h := reflection_log_9223_neg
  have he : Real.log (1142687 / 1000000) = -Real.log (1000000 / 1142687) := by
    rw [show ((1142687 / 1000000) : ℝ) = ((1000000 / 1142687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9224_neg : (153952199 / 1000000000) ≤ -Real.log (857313 / 1000000) ∧
    -Real.log (857313 / 1000000) ≤ (769761 / 5000000) := by
  have h := checkLog_sound (w := (142687 / 1857313)) (n := 12)
    (lo := (153952199 / 1000000000)) (hi := (769761 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 857313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 857313) = 1/(857313 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9224 : Bounds (-769761 / 5000000) (-153952199 / 1000000000) (Real.log (857313 / 1000000)) := by
  have h := reflection_log_9224_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9225_neg : (5142423 / 250000000) ≤ -Real.log (979640420031 / 1000000000000) ∧
    -Real.log (979640420031 / 1000000000000) ≤ (20569693 / 1000000000) := by
  have h := checkLog_sound (w := (20359579969 / 1979640420031)) (n := 12)
    (lo := (5142423 / 250000000)) (hi := (20569693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979640420031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979640420031) = 1/(979640420031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9225 : Bounds (-20569693 / 1000000000) (-5142423 / 250000000) (Real.log (979640420031 / 1000000000000)) := by
  have h := reflection_log_9225_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9226_neg : (10206639 / 500000000) ≤ -Real.log (979793661799 / 1000000000000) ∧
    -Real.log (979793661799 / 1000000000000) ≤ (20413279 / 1000000000) := by
  have h := checkLog_sound (w := (20206338201 / 1979793661799)) (n := 12)
    (lo := (10206639 / 500000000)) (hi := (20413279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979793661799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979793661799) = 1/(979793661799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9226 : Bounds (-20413279 / 1000000000) (-10206639 / 500000000) (Real.log (979793661799 / 1000000000000)) := by
  have h := reflection_log_9226_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9227_neg : (286236429 / 1000000000) ≤ -Real.log (62500000000 / 83212950151) ∧
    -Real.log (62500000000 / 83212950151) ≤ (28623643 / 100000000) := by
  have h := checkLog_sound (w := (20712950151 / 145712950151)) (n := 12)
    (lo := (286236429 / 1000000000)) (hi := (28623643 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83212950151 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83212950151 / 62500000000) = 1/(62500000000 / 83212950151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9227 : Bounds (286236429 / 1000000000) (28623643 / 100000000) (Real.log (83212950151 / 62500000000)) := by
  have h := reflection_log_9227_neg
  have he : Real.log (83212950151 / 62500000000) = -Real.log (62500000000 / 83212950151) := by
    rw [show ((83212950151 / 62500000000) : ℝ) = ((62500000000 / 83212950151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9228_neg : (143667353 / 500000000) ≤ -Real.log (250000000000 / 333217564647) ∧
    -Real.log (250000000000 / 333217564647) ≤ (287334707 / 1000000000) := by
  have h := checkLog_sound (w := (83217564647 / 583217564647)) (n := 12)
    (lo := (143667353 / 500000000)) (hi := (287334707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((333217564647 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(333217564647 / 250000000000) = 1/(250000000000 / 333217564647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9228 : Bounds (143667353 / 500000000) (287334707 / 1000000000) (Real.log (333217564647 / 250000000000)) := by
  have h := reflection_log_9228_neg
  have he : Real.log (333217564647 / 250000000000) = -Real.log (250000000000 / 333217564647) := by
    rw [show ((333217564647 / 250000000000) : ℝ) = ((250000000000 / 333217564647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9229_neg : (576449379 / 1000000000) ≤ -Real.log (500000000000 / 889854065323) ∧
    -Real.log (500000000000 / 889854065323) ≤ (28822469 / 50000000) := by
  have h := checkLog_sound (w := (389854065323 / 1389854065323)) (n := 12)
    (lo := (576449379 / 1000000000)) (hi := (28822469 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((889854065323 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(889854065323 / 500000000000) = 1/(500000000000 / 889854065323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9229 : Bounds (576449379 / 1000000000) (28822469 / 50000000) (Real.log (889854065323 / 500000000000)) := by
  have h := reflection_log_9229_neg
  have he : Real.log (889854065323 / 500000000000) = -Real.log (500000000000 / 889854065323) := by
    rw [show ((889854065323 / 500000000000) : ℝ) = ((500000000000 / 889854065323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9230_neg : (18047967 / 31250000) ≤ -Real.log (100000000000 / 178164116829) ∧
    -Real.log (100000000000 / 178164116829) ≤ (115506989 / 200000000) := by
  have h := checkLog_sound (w := (78164116829 / 278164116829)) (n := 12)
    (lo := (18047967 / 31250000)) (hi := (115506989 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178164116829 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178164116829 / 100000000000) = 1/(100000000000 / 178164116829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9230 : Bounds (18047967 / 31250000) (115506989 / 200000000) (Real.log (178164116829 / 100000000000)) := by
  have h := reflection_log_9230_neg
  have he : Real.log (178164116829 / 100000000000) = -Real.log (100000000000 / 178164116829) := by
    rw [show ((178164116829 / 100000000000) : ℝ) = ((100000000000 / 178164116829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9231_neg : (124015633 / 500000000) ≤ -Real.log (2000 / 2563) ∧
    -Real.log (2000 / 2563) ≤ (248031267 / 1000000000) := by
  have h := checkLog_sound (w := (563 / 4563)) (n := 12)
    (lo := (124015633 / 500000000)) (hi := (248031267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2563 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2563 / 2000) = 1/(2000 / 2563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9231 : Bounds (124015633 / 500000000) (248031267 / 1000000000) (Real.log (2563 / 2000)) := by
  have h := reflection_log_9231_neg
  have he : Real.log (2563 / 2000) = -Real.log (2000 / 2563) := by
    rw [show ((2563 / 2000) : ℝ) = ((2000 / 2563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9232_neg : (330589573 / 1000000000) ≤ -Real.log (1437 / 2000) ∧
    -Real.log (1437 / 2000) ≤ (165294787 / 500000000) := by
  have h := checkLog_sound (w := (563 / 3437)) (n := 12)
    (lo := (330589573 / 1000000000)) (hi := (165294787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1437) = 1/(1437 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9232 : Bounds (-165294787 / 500000000) (-330589573 / 1000000000) (Real.log (1437 / 2000)) := by
  have h := reflection_log_9232_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9233_neg : (14073 / 50000000) ≤ -Real.log (2000000 / 2000563) ∧
    -Real.log (2000000 / 2000563) ≤ (281461 / 1000000000) := by
  have h := checkLog_sound (w := (563 / 4000563)) (n := 12)
    (lo := (14073 / 50000000)) (hi := (281461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000563 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000563 / 2000000) = 1/(2000000 / 2000563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9233 : Bounds (14073 / 50000000) (281461 / 1000000000) (Real.log (2000563 / 2000000)) := by
  have h := reflection_log_9233_neg
  have he : Real.log (2000563 / 2000000) = -Real.log (2000000 / 2000563) := by
    rw [show ((2000563 / 2000000) : ℝ) = ((2000000 / 2000563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9234_neg : (281539 / 1000000000) ≤ -Real.log (1999437 / 2000000) ∧
    -Real.log (1999437 / 2000000) ≤ (14077 / 50000000) := by
  have h := checkLog_sound (w := (563 / 3999437)) (n := 12)
    (lo := (281539 / 1000000000)) (hi := (14077 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999437) = 1/(1999437 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9234 : Bounds (-14077 / 50000000) (-281539 / 1000000000) (Real.log (1999437 / 2000000)) := by
  have h := reflection_log_9234_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9235_neg : (13313919 / 100000000) ≤ -Real.log (1000000 / 1142409) ∧
    -Real.log (1000000 / 1142409) ≤ (133139191 / 1000000000) := by
  have h := checkLog_sound (w := (142409 / 2142409)) (n := 12)
    (lo := (13313919 / 100000000)) (hi := (133139191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1142409 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1142409 / 1000000) = 1/(1000000 / 1142409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9235 : Bounds (13313919 / 100000000) (133139191 / 1000000000) (Real.log (1142409 / 1000000)) := by
  have h := reflection_log_9235_neg
  have he : Real.log (1142409 / 1000000) = -Real.log (1000000 / 1142409) := by
    rw [show ((1142409 / 1000000) : ℝ) = ((1000000 / 1142409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9236_neg : (153627983 / 1000000000) ≤ -Real.log (857591 / 1000000) ∧
    -Real.log (857591 / 1000000) ≤ (9601749 / 62500000) := by
  have h := checkLog_sound (w := (142409 / 1857591)) (n := 12)
    (lo := (153627983 / 1000000000)) (hi := (9601749 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 857591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 857591) = 1/(857591 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9236 : Bounds (-9601749 / 62500000) (-153627983 / 1000000000) (Real.log (857591 / 1000000)) := by
  have h := reflection_log_9236_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9237_neg : (33402941 / 250000000) ≤ -Real.log (1000000 / 1142949) ∧
    -Real.log (1000000 / 1142949) ≤ (26722353 / 200000000) := by
  have h := checkLog_sound (w := (142949 / 2142949)) (n := 12)
    (lo := (33402941 / 250000000)) (hi := (26722353 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1142949 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1142949 / 1000000) = 1/(1000000 / 1142949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9237 : Bounds (33402941 / 250000000) (26722353 / 200000000) (Real.log (1142949 / 1000000)) := by
  have h := reflection_log_9237_neg
  have he : Real.log (1142949 / 1000000) = -Real.log (1000000 / 1142949) := by
    rw [show ((1142949 / 1000000) : ℝ) = ((1000000 / 1142949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9238_neg : (38564463 / 250000000) ≤ -Real.log (857051 / 1000000) ∧
    -Real.log (857051 / 1000000) ≤ (154257853 / 1000000000) := by
  have h := checkLog_sound (w := (142949 / 1857051)) (n := 12)
    (lo := (38564463 / 250000000)) (hi := (154257853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 857051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 857051) = 1/(857051 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9238 : Bounds (-154257853 / 1000000000) (-38564463 / 250000000) (Real.log (857051 / 1000000)) := by
  have h := reflection_log_9238_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9239_neg : (20646087 / 1000000000) ≤ -Real.log (979565583399 / 1000000000000) ∧
    -Real.log (979565583399 / 1000000000000) ≤ (2580761 / 125000000) := by
  have h := checkLog_sound (w := (20434416601 / 1979565583399)) (n := 12)
    (lo := (20646087 / 1000000000)) (hi := (2580761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979565583399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979565583399) = 1/(979565583399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9239 : Bounds (-2580761 / 125000000) (-20646087 / 1000000000) (Real.log (979565583399 / 1000000000000)) := by
  have h := reflection_log_9239_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9240_neg : (2561099 / 125000000) ≤ -Real.log (979719676719 / 1000000000000) ∧
    -Real.log (979719676719 / 1000000000000) ≤ (20488793 / 1000000000) := by
  have h := checkLog_sound (w := (20280323281 / 1979719676719)) (n := 12)
    (lo := (2561099 / 125000000)) (hi := (20488793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979719676719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979719676719) = 1/(979719676719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9240 : Bounds (-20488793 / 1000000000) (-2561099 / 125000000) (Real.log (979719676719 / 1000000000000)) := by
  have h := reflection_log_9240_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9241_neg : (286767173 / 1000000000) ≤ -Real.log (500000000000 / 666057013191) ∧
    -Real.log (500000000000 / 666057013191) ≤ (143383587 / 500000000) := by
  have h := checkLog_sound (w := (166057013191 / 1166057013191)) (n := 12)
    (lo := (286767173 / 1000000000)) (hi := (143383587 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((666057013191 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(666057013191 / 500000000000) = 1/(500000000000 / 666057013191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9241 : Bounds (286767173 / 1000000000) (143383587 / 500000000) (Real.log (666057013191 / 500000000000)) := by
  have h := reflection_log_9241_neg
  have he : Real.log (666057013191 / 500000000000) = -Real.log (500000000000 / 666057013191) := by
    rw [show ((666057013191 / 500000000000) : ℝ) = ((500000000000 / 666057013191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9242_neg : (17991851 / 62500000) ≤ -Real.log (100000000000 / 133358341569) ∧
    -Real.log (100000000000 / 133358341569) ≤ (287869617 / 1000000000) := by
  have h := checkLog_sound (w := (33358341569 / 233358341569)) (n := 12)
    (lo := (17991851 / 62500000)) (hi := (287869617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133358341569 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133358341569 / 100000000000) = 1/(100000000000 / 133358341569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9242 : Bounds (17991851 / 62500000) (287869617 / 1000000000) (Real.log (133358341569 / 100000000000)) := by
  have h := reflection_log_9242_neg
  have he : Real.log (133358341569 / 100000000000) = -Real.log (100000000000 / 133358341569) := by
    rw [show ((133358341569 / 100000000000) : ℝ) = ((100000000000 / 133358341569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9243_neg : (18047967 / 31250000) ≤ -Real.log (31250000000 / 55676286509) ∧
    -Real.log (31250000000 / 55676286509) ≤ (115506989 / 200000000) := by
  have h := checkLog_sound (w := (24426286509 / 86926286509)) (n := 12)
    (lo := (18047967 / 31250000)) (hi := (115506989 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55676286509 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55676286509 / 31250000000) = 1/(31250000000 / 55676286509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9243 : Bounds (18047967 / 31250000) (115506989 / 200000000) (Real.log (55676286509 / 31250000000)) := by
  have h := reflection_log_9243_neg
  have he : Real.log (55676286509 / 31250000000) = -Real.log (31250000000 / 55676286509) := by
    rw [show ((55676286509 / 31250000000) : ℝ) = ((31250000000 / 55676286509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9244_neg : (14465521 / 25000000) ≤ -Real.log (125000000000 / 222947112039) ∧
    -Real.log (125000000000 / 222947112039) ≤ (578620841 / 1000000000) := by
  have h := checkLog_sound (w := (97947112039 / 347947112039)) (n := 12)
    (lo := (14465521 / 25000000)) (hi := (578620841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((222947112039 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(222947112039 / 125000000000) = 1/(125000000000 / 222947112039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9244 : Bounds (14465521 / 25000000) (578620841 / 1000000000) (Real.log (222947112039 / 125000000000)) := by
  have h := reflection_log_9244_neg
  have he : Real.log (222947112039 / 125000000000) = -Real.log (125000000000 / 222947112039) := by
    rw [show ((222947112039 / 125000000000) : ℝ) = ((125000000000 / 222947112039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9245_neg : (124210679 / 500000000) ≤ -Real.log (500 / 641) ∧
    -Real.log (500 / 641) ≤ (248421359 / 1000000000) := by
  have h := checkLog_sound (w := (141 / 1141)) (n := 12)
    (lo := (124210679 / 500000000)) (hi := (248421359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((641 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(641 / 500) = 1/(500 / 641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9245 : Bounds (124210679 / 500000000) (248421359 / 1000000000) (Real.log (641 / 500)) := by
  have h := reflection_log_9245_neg
  have he : Real.log (641 / 500) = -Real.log (500 / 641) := by
    rw [show ((641 / 500) : ℝ) = ((500 / 641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9246_neg : (331285709 / 1000000000) ≤ -Real.log (359 / 500) ∧
    -Real.log (359 / 500) ≤ (33128571 / 100000000) := by
  have h := checkLog_sound (w := (141 / 859)) (n := 12)
    (lo := (331285709 / 1000000000)) (hi := (33128571 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 359) = 1/(359 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9246 : Bounds (-33128571 / 100000000) (-331285709 / 1000000000) (Real.log (359 / 500)) := by
  have h := reflection_log_9246_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9247_neg : (7049 / 25000000) ≤ -Real.log (500000 / 500141) ∧
    -Real.log (500000 / 500141) ≤ (281961 / 1000000000) := by
  have h := checkLog_sound (w := (141 / 1000141)) (n := 12)
    (lo := (7049 / 25000000)) (hi := (281961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500141 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500141 / 500000) = 1/(500000 / 500141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9247 : Bounds (7049 / 25000000) (281961 / 1000000000) (Real.log (500141 / 500000)) := by
  have h := reflection_log_9247_neg
  have he : Real.log (500141 / 500000) = -Real.log (500000 / 500141) := by
    rw [show ((500141 / 500000) : ℝ) = ((500000 / 500141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9248_neg : (282039 / 1000000000) ≤ -Real.log (499859 / 500000) ∧
    -Real.log (499859 / 500000) ≤ (7051 / 25000000) := by
  have h := checkLog_sound (w := (141 / 999859)) (n := 12)
    (lo := (282039 / 1000000000)) (hi := (7051 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499859) = 1/(499859 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9248 : Bounds (-7051 / 25000000) (-282039 / 1000000000) (Real.log (499859 / 500000)) := by
  have h := reflection_log_9248_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9249_neg : (133367629 / 1000000000) ≤ -Real.log (100000 / 114267) ∧
    -Real.log (100000 / 114267) ≤ (13336763 / 100000000) := by
  have h := checkLog_sound (w := (14267 / 214267)) (n := 12)
    (lo := (133367629 / 1000000000)) (hi := (13336763 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114267 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(114267 / 100000) = 1/(100000 / 114267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9249 : Bounds (133367629 / 1000000000) (13336763 / 100000000) (Real.log (114267 / 100000)) := by
  have h := reflection_log_9249_neg
  have he : Real.log (114267 / 100000) = -Real.log (100000 / 114267) := by
    rw [show ((114267 / 100000) : ℝ) = ((100000 / 114267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9250_neg : (15393237 / 100000000) ≤ -Real.log (85733 / 100000) ∧
    -Real.log (85733 / 100000) ≤ (153932371 / 1000000000) := by
  have h := checkLog_sound (w := (14267 / 185733)) (n := 12)
    (lo := (15393237 / 100000000)) (hi := (153932371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 85733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 85733) = 1/(85733 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9250 : Bounds (-153932371 / 1000000000) (-15393237 / 100000000) (Real.log (85733 / 100000)) := by
  have h := reflection_log_9250_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9251_neg : (66920047 / 500000000) ≤ -Real.log (100000 / 114321) ∧
    -Real.log (100000 / 114321) ≤ (26768019 / 200000000) := by
  have h := checkLog_sound (w := (14321 / 214321)) (n := 12)
    (lo := (66920047 / 500000000)) (hi := (26768019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114321 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(114321 / 100000) = 1/(100000 / 114321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9251 : Bounds (66920047 / 500000000) (26768019 / 200000000) (Real.log (114321 / 100000)) := by
  have h := reflection_log_9251_neg
  have he : Real.log (114321 / 100000) = -Real.log (100000 / 114321) := by
    rw [show ((114321 / 100000) : ℝ) = ((100000 / 114321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9252_neg : (154562431 / 1000000000) ≤ -Real.log (85679 / 100000) ∧
    -Real.log (85679 / 100000) ≤ (1207519 / 7812500) := by
  have h := checkLog_sound (w := (14321 / 185679)) (n := 12)
    (lo := (154562431 / 1000000000)) (hi := (1207519 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 85679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 85679) = 1/(85679 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9252 : Bounds (-1207519 / 7812500) (-154562431 / 1000000000) (Real.log (85679 / 100000)) := by
  have h := reflection_log_9252_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9253_neg : (647573 / 31250000) ≤ -Real.log (9794908959 / 10000000000) ∧
    -Real.log (9794908959 / 10000000000) ≤ (20722337 / 1000000000) := by
  have h := checkLog_sound (w := (205091041 / 19794908959)) (n := 12)
    (lo := (647573 / 31250000)) (hi := (20722337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9794908959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9794908959) = 1/(9794908959 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9253 : Bounds (-20722337 / 1000000000) (-647573 / 31250000) (Real.log (9794908959 / 10000000000)) := by
  have h := reflection_log_9253_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9254_neg : (20564741 / 1000000000) ≤ -Real.log (9796452711 / 10000000000) ∧
    -Real.log (9796452711 / 10000000000) ≤ (10282371 / 500000000) := by
  have h := checkLog_sound (w := (203547289 / 19796452711)) (n := 12)
    (lo := (20564741 / 1000000000)) (hi := (10282371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9796452711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9796452711) = 1/(9796452711 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9254 : Bounds (-10282371 / 500000000) (-20564741 / 1000000000) (Real.log (9796452711 / 10000000000)) := by
  have h := reflection_log_9254_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9255_neg : (287299999 / 1000000000) ≤ -Real.log (250000000000 / 333206000023) ∧
    -Real.log (250000000000 / 333206000023) ≤ (2873 / 10000) := by
  have h := checkLog_sound (w := (83206000023 / 583206000023)) (n := 12)
    (lo := (287299999 / 1000000000)) (hi := (2873 / 10000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((333206000023 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(333206000023 / 250000000000) = 1/(250000000000 / 333206000023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9255 : Bounds (287299999 / 1000000000) (2873 / 10000) (Real.log (333206000023 / 250000000000)) := by
  have h := reflection_log_9255_neg
  have he : Real.log (333206000023 / 250000000000) = -Real.log (250000000000 / 333206000023) := by
    rw [show ((333206000023 / 250000000000) : ℝ) = ((250000000000 / 333206000023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9256_neg : (144201263 / 500000000) ≤ -Real.log (500000000000 / 667147142241) ∧
    -Real.log (500000000000 / 667147142241) ≤ (288402527 / 1000000000) := by
  have h := checkLog_sound (w := (167147142241 / 1167147142241)) (n := 12)
    (lo := (144201263 / 500000000)) (hi := (288402527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667147142241 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667147142241 / 500000000000) = 1/(500000000000 / 667147142241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9256 : Bounds (144201263 / 500000000) (288402527 / 1000000000) (Real.log (667147142241 / 500000000000)) := by
  have h := reflection_log_9256_neg
  have he : Real.log (667147142241 / 500000000000) = -Real.log (500000000000 / 667147142241) := by
    rw [show ((667147142241 / 500000000000) : ℝ) = ((500000000000 / 667147142241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9257_neg : (14465521 / 25000000) ≤ -Real.log (100000000000 / 178357689631) ∧
    -Real.log (100000000000 / 178357689631) ≤ (578620841 / 1000000000) := by
  have h := checkLog_sound (w := (78357689631 / 278357689631)) (n := 12)
    (lo := (14465521 / 25000000)) (hi := (578620841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178357689631 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178357689631 / 100000000000) = 1/(100000000000 / 178357689631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9257 : Bounds (14465521 / 25000000) (578620841 / 1000000000) (Real.log (178357689631 / 100000000000)) := by
  have h := reflection_log_9257_neg
  have he : Real.log (178357689631 / 100000000000) = -Real.log (100000000000 / 178357689631) := by
    rw [show ((178357689631 / 100000000000) : ℝ) = ((100000000000 / 178357689631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9258_neg : (144926767 / 250000000) ≤ -Real.log (62500000000 / 111594707521) ∧
    -Real.log (62500000000 / 111594707521) ≤ (579707069 / 1000000000) := by
  have h := checkLog_sound (w := (49094707521 / 174094707521)) (n := 12)
    (lo := (144926767 / 250000000)) (hi := (579707069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111594707521 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111594707521 / 62500000000) = 1/(62500000000 / 111594707521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9258 : Bounds (144926767 / 250000000) (579707069 / 1000000000) (Real.log (111594707521 / 62500000000)) := by
  have h := reflection_log_9258_neg
  have he : Real.log (111594707521 / 62500000000) = -Real.log (62500000000 / 111594707521) := by
    rw [show ((111594707521 / 62500000000) : ℝ) = ((62500000000 / 111594707521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9259_neg : (124405649 / 500000000) ≤ -Real.log (400 / 513) ∧
    -Real.log (400 / 513) ≤ (248811299 / 1000000000) := by
  have h := checkLog_sound (w := (113 / 913)) (n := 12)
    (lo := (124405649 / 500000000)) (hi := (248811299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((513 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(513 / 400) = 1/(400 / 513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9259 : Bounds (124405649 / 500000000) (248811299 / 1000000000) (Real.log (513 / 400)) := by
  have h := reflection_log_9259_neg
  have he : Real.log (513 / 400) = -Real.log (400 / 513) := by
    rw [show ((513 / 400) : ℝ) = ((400 / 513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9260_neg : (331982331 / 1000000000) ≤ -Real.log (287 / 400) ∧
    -Real.log (287 / 400) ≤ (82995583 / 250000000) := by
  have h := checkLog_sound (w := (113 / 687)) (n := 12)
    (lo := (331982331 / 1000000000)) (hi := (82995583 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 287) = 1/(287 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9260 : Bounds (-82995583 / 250000000) (-331982331 / 1000000000) (Real.log (287 / 400)) := by
  have h := reflection_log_9260_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9261_neg : (14123 / 50000000) ≤ -Real.log (400000 / 400113) ∧
    -Real.log (400000 / 400113) ≤ (282461 / 1000000000) := by
  have h := checkLog_sound (w := (113 / 800113)) (n := 12)
    (lo := (14123 / 50000000)) (hi := (282461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400113 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400113 / 400000) = 1/(400000 / 400113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9261 : Bounds (14123 / 50000000) (282461 / 1000000000) (Real.log (400113 / 400000)) := by
  have h := reflection_log_9261_neg
  have he : Real.log (400113 / 400000) = -Real.log (400000 / 400113) := by
    rw [show ((400113 / 400000) : ℝ) = ((400000 / 400113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9262_neg : (282539 / 1000000000) ≤ -Real.log (399887 / 400000) ∧
    -Real.log (399887 / 400000) ≤ (14127 / 50000000) := by
  have h := checkLog_sound (w := (113 / 799887)) (n := 12)
    (lo := (282539 / 1000000000)) (hi := (14127 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399887) = 1/(399887 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9262 : Bounds (-14127 / 50000000) (-282539 / 1000000000) (Real.log (399887 / 400000)) := by
  have h := reflection_log_9262_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9263_neg : (26719203 / 200000000) ≤ -Real.log (1000000 / 1142931) ∧
    -Real.log (1000000 / 1142931) ≤ (8349751 / 62500000) := by
  have h := checkLog_sound (w := (142931 / 2142931)) (n := 12)
    (lo := (26719203 / 200000000)) (hi := (8349751 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1142931 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1142931 / 1000000) = 1/(1000000 / 1142931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9263 : Bounds (26719203 / 200000000) (8349751 / 62500000) (Real.log (1142931 / 1000000)) := by
  have h := reflection_log_9263_neg
  have he : Real.log (1142931 / 1000000) = -Real.log (1000000 / 1142931) := by
    rw [show ((1142931 / 1000000) : ℝ) = ((1000000 / 1142931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9264_neg : (3084737 / 20000000) ≤ -Real.log (857069 / 1000000) ∧
    -Real.log (857069 / 1000000) ≤ (154236851 / 1000000000) := by
  have h := checkLog_sound (w := (142931 / 1857069)) (n := 12)
    (lo := (3084737 / 20000000)) (hi := (154236851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 857069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 857069) = 1/(857069 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9264 : Bounds (-154236851 / 1000000000) (-3084737 / 20000000) (Real.log (857069 / 1000000)) := by
  have h := reflection_log_9264_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9265_neg : (134069247 / 1000000000) ≤ -Real.log (62500 / 71467) ∧
    -Real.log (62500 / 71467) ≤ (261854 / 1953125) := by
  have h := checkLog_sound (w := (8967 / 133967)) (n := 12)
    (lo := (134069247 / 1000000000)) (hi := (261854 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71467 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71467 / 62500) = 1/(62500 / 71467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9265 : Bounds (134069247 / 1000000000) (261854 / 1953125) (Real.log (71467 / 62500)) := by
  have h := reflection_log_9265_neg
  have he : Real.log (71467 / 62500) = -Real.log (62500 / 71467) := by
    rw [show ((71467 / 62500) : ℝ) = ((62500 / 71467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9266_neg : (15486827 / 100000000) ≤ -Real.log (53533 / 62500) ∧
    -Real.log (53533 / 62500) ≤ (154868271 / 1000000000) := by
  have h := checkLog_sound (w := (8967 / 116033)) (n := 12)
    (lo := (15486827 / 100000000)) (hi := (154868271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 53533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 53533) = 1/(53533 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9266 : Bounds (-154868271 / 1000000000) (-15486827 / 100000000) (Real.log (53533 / 62500)) := by
  have h := reflection_log_9266_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9267_neg : (10399511 / 500000000) ≤ -Real.log (3825842911 / 3906250000) ∧
    -Real.log (3825842911 / 3906250000) ≤ (20799023 / 1000000000) := by
  have h := checkLog_sound (w := (80407089 / 7732092911)) (n := 12)
    (lo := (10399511 / 500000000)) (hi := (20799023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3825842911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3825842911) = 1/(3825842911 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9267 : Bounds (-20799023 / 1000000000) (-10399511 / 500000000) (Real.log (3825842911 / 3906250000)) := by
  have h := reflection_log_9267_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9268_neg : (10320417 / 500000000) ≤ -Real.log (979570729239 / 1000000000000) ∧
    -Real.log (979570729239 / 1000000000000) ≤ (4128167 / 200000000) := by
  have h := checkLog_sound (w := (20429270761 / 1979570729239)) (n := 12)
    (lo := (10320417 / 500000000)) (hi := (4128167 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979570729239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979570729239) = 1/(979570729239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9268 : Bounds (-4128167 / 200000000) (-10320417 / 500000000) (Real.log (979570729239 / 1000000000000)) := by
  have h := reflection_log_9268_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9269_neg : (57566573 / 200000000) ≤ -Real.log (500000000000 / 666767203107) ∧
    -Real.log (500000000000 / 666767203107) ≤ (143916433 / 500000000) := by
  have h := checkLog_sound (w := (166767203107 / 1166767203107)) (n := 12)
    (lo := (57566573 / 200000000)) (hi := (143916433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((666767203107 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(666767203107 / 500000000000) = 1/(500000000000 / 666767203107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9269 : Bounds (57566573 / 200000000) (143916433 / 500000000) (Real.log (666767203107 / 500000000000)) := by
  have h := reflection_log_9269_neg
  have he : Real.log (666767203107 / 500000000000) = -Real.log (500000000000 / 666767203107) := by
    rw [show ((666767203107 / 500000000000) : ℝ) = ((500000000000 / 666767203107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9270_neg : (144468759 / 500000000) ≤ -Real.log (100000000000 / 133500831263) ∧
    -Real.log (100000000000 / 133500831263) ≤ (288937519 / 1000000000) := by
  have h := checkLog_sound (w := (33500831263 / 233500831263)) (n := 12)
    (lo := (144468759 / 500000000)) (hi := (288937519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133500831263 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133500831263 / 100000000000) = 1/(100000000000 / 133500831263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9270 : Bounds (144468759 / 500000000) (288937519 / 1000000000) (Real.log (133500831263 / 100000000000)) := by
  have h := reflection_log_9270_neg
  have he : Real.log (133500831263 / 100000000000) = -Real.log (100000000000 / 133500831263) := by
    rw [show ((133500831263 / 100000000000) : ℝ) = ((100000000000 / 133500831263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9271_neg : (144926767 / 250000000) ≤ -Real.log (500000000000 / 892757660167) ∧
    -Real.log (500000000000 / 892757660167) ≤ (579707069 / 1000000000) := by
  have h := checkLog_sound (w := (392757660167 / 1392757660167)) (n := 12)
    (lo := (144926767 / 250000000)) (hi := (579707069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((892757660167 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(892757660167 / 500000000000) = 1/(500000000000 / 892757660167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9271 : Bounds (144926767 / 250000000) (579707069 / 1000000000) (Real.log (892757660167 / 500000000000)) := by
  have h := reflection_log_9271_neg
  have he : Real.log (892757660167 / 500000000000) = -Real.log (500000000000 / 892757660167) := by
    rw [show ((892757660167 / 500000000000) : ℝ) = ((500000000000 / 892757660167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9272_neg : (580793629 / 1000000000) ≤ -Real.log (500000000000 / 893728222997) ∧
    -Real.log (500000000000 / 893728222997) ≤ (58079363 / 100000000) := by
  have h := checkLog_sound (w := (393728222997 / 1393728222997)) (n := 12)
    (lo := (580793629 / 1000000000)) (hi := (58079363 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((893728222997 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(893728222997 / 500000000000) = 1/(500000000000 / 893728222997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9272 : Bounds (580793629 / 1000000000) (58079363 / 100000000) (Real.log (893728222997 / 500000000000)) := by
  have h := reflection_log_9272_neg
  have he : Real.log (893728222997 / 500000000000) = -Real.log (500000000000 / 893728222997) := by
    rw [show ((893728222997 / 500000000000) : ℝ) = ((500000000000 / 893728222997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9273_neg : (49840217 / 200000000) ≤ -Real.log (1000 / 1283) ∧
    -Real.log (1000 / 1283) ≤ (124600543 / 500000000) := by
  have h := checkLog_sound (w := (283 / 2283)) (n := 12)
    (lo := (49840217 / 200000000)) (hi := (124600543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1283 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1283 / 1000) = 1/(1000 / 1283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9273 : Bounds (49840217 / 200000000) (124600543 / 500000000) (Real.log (1283 / 1000)) := by
  have h := reflection_log_9273_neg
  have he : Real.log (1283 / 1000) = -Real.log (1000 / 1283) := by
    rw [show ((1283 / 1000) : ℝ) = ((1000 / 1283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9274_neg : (166339719 / 500000000) ≤ -Real.log (717 / 1000) ∧
    -Real.log (717 / 1000) ≤ (332679439 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 1717)) (n := 12)
    (lo := (166339719 / 500000000)) (hi := (332679439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 717) = 1/(717 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9274 : Bounds (-332679439 / 1000000000) (-166339719 / 500000000) (Real.log (717 / 1000)) := by
  have h := reflection_log_9274_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9275_neg : (282959 / 1000000000) ≤ -Real.log (1000000 / 1000283) ∧
    -Real.log (1000000 / 1000283) ≤ (3537 / 12500000) := by
  have h := checkLog_sound (w := (283 / 2000283)) (n := 12)
    (lo := (282959 / 1000000000)) (hi := (3537 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000283 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000283 / 1000000) = 1/(1000000 / 1000283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9275 : Bounds (282959 / 1000000000) (3537 / 12500000) (Real.log (1000283 / 1000000)) := by
  have h := reflection_log_9275_neg
  have he : Real.log (1000283 / 1000000) = -Real.log (1000000 / 1000283) := by
    rw [show ((1000283 / 1000000) : ℝ) = ((1000000 / 1000283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9276_neg : (1769 / 6250000) ≤ -Real.log (999717 / 1000000) ∧
    -Real.log (999717 / 1000000) ≤ (283041 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 1999717)) (n := 12)
    (lo := (1769 / 6250000)) (hi := (283041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999717) = 1/(999717 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9276 : Bounds (-283041 / 1000000000) (-1769 / 6250000) (Real.log (999717 / 1000000)) := by
  have h := reflection_log_9276_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9277_neg : (133824349 / 1000000000) ≤ -Real.log (125000 / 142899) ∧
    -Real.log (125000 / 142899) ≤ (2676487 / 20000000) := by
  have h := checkLog_sound (w := (17899 / 267899)) (n := 12)
    (lo := (133824349 / 1000000000)) (hi := (2676487 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142899 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142899 / 125000) = 1/(125000 / 142899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9277 : Bounds (133824349 / 1000000000) (2676487 / 20000000) (Real.log (142899 / 125000)) := by
  have h := reflection_log_9277_neg
  have he : Real.log (142899 / 125000) = -Real.log (125000 / 142899) := by
    rw [show ((142899 / 125000) : ℝ) = ((125000 / 142899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9278_neg : (77270711 / 500000000) ≤ -Real.log (107101 / 125000) ∧
    -Real.log (107101 / 125000) ≤ (154541423 / 1000000000) := by
  have h := checkLog_sound (w := (17899 / 232101)) (n := 12)
    (lo := (77270711 / 500000000)) (hi := (154541423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 107101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 107101) = 1/(107101 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9278 : Bounds (-154541423 / 1000000000) (-77270711 / 500000000) (Real.log (107101 / 125000)) := by
  have h := reflection_log_9278_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9279_neg : (67148737 / 500000000) ≤ -Real.log (1000000 / 1143733) ∧
    -Real.log (1000000 / 1143733) ≤ (5371899 / 40000000) := by
  have h := checkLog_sound (w := (143733 / 2143733)) (n := 12)
    (lo := (67148737 / 500000000)) (hi := (5371899 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1143733 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1143733 / 1000000) = 1/(1000000 / 1143733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9279 : Bounds (67148737 / 500000000) (5371899 / 40000000) (Real.log (1143733 / 1000000)) := by
  have h := reflection_log_9279_neg
  have he : Real.log (1143733 / 1000000) = -Real.log (1000000 / 1143733) := by
    rw [show ((1143733 / 1000000) : ℝ) = ((1000000 / 1143733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


