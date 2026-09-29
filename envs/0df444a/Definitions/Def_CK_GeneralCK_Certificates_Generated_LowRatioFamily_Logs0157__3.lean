-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0157__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0157__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T20:21:40.305593+00:00
-- url     : https://prove2.me/theorems/70bb2e1c-a009-4572-a3bd-2e280078409d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0157 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0158, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0157 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0158, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0159)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0157 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0158, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0159)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0157 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0158, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0159) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0157 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0158, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0159).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0157 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10048_neg : (35559959 / 200000000) ≤ -Real.log (83711 / 100000) ∧
    -Real.log (83711 / 100000) ≤ (44449949 / 250000000) := by
  have h := checkLog_sound (w := (16289 / 183711)) (n := 12)
    (lo := (35559959 / 200000000)) (hi := (44449949 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 83711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 83711) = 1/(83711 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10048 : Bounds (-44449949 / 250000000) (-35559959 / 200000000) (Real.log (83711 / 100000)) := by
  have h := reflection_log_10048_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10049_neg : (758169 / 5000000) ≤ -Real.log (500000 / 581867) ∧
    -Real.log (500000 / 581867) ≤ (151633801 / 1000000000) := by
  have h := checkLog_sound (w := (81867 / 1081867)) (n := 12)
    (lo := (758169 / 5000000)) (hi := (151633801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581867 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581867 / 500000) = 1/(500000 / 581867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10049 : Bounds (758169 / 5000000) (151633801 / 1000000000) (Real.log (581867 / 500000)) := by
  have h := reflection_log_10049_neg
  have he : Real.log (581867 / 500000) = -Real.log (500000 / 581867) := by
    rw [show ((581867 / 500000) : ℝ) = ((500000 / 581867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10050_neg : (89404267 / 500000000) ≤ -Real.log (418133 / 500000) ∧
    -Real.log (418133 / 500000) ≤ (35761707 / 200000000) := by
  have h := checkLog_sound (w := (81867 / 918133)) (n := 12)
    (lo := (89404267 / 500000000)) (hi := (35761707 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 418133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 418133) = 1/(418133 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10050 : Bounds (-35761707 / 200000000) (-89404267 / 500000000) (Real.log (418133 / 500000)) := by
  have h := reflection_log_10050_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10051_neg : (27174733 / 1000000000) ≤ -Real.log (243297794311 / 250000000000) ∧
    -Real.log (243297794311 / 250000000000) ≤ (13587367 / 500000000) := by
  have h := checkLog_sound (w := (6702205689 / 493297794311)) (n := 12)
    (lo := (27174733 / 1000000000)) (hi := (13587367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243297794311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243297794311) = 1/(243297794311 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10051 : Bounds (-13587367 / 500000000) (-27174733 / 1000000000) (Real.log (243297794311 / 250000000000)) := by
  have h := reflection_log_10051_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10052_neg : (26891509 / 1000000000) ≤ -Real.log (9734668479 / 10000000000) ∧
    -Real.log (9734668479 / 10000000000) ≤ (2689151 / 100000000) := by
  have h := checkLog_sound (w := (265331521 / 19734668479)) (n := 12)
    (lo := (26891509 / 1000000000)) (hi := (2689151 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9734668479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9734668479) = 1/(9734668479 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10052 : Bounds (-2689151 / 100000000) (-26891509 / 1000000000) (Real.log (9734668479 / 10000000000)) := by
  have h := reflection_log_10052_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10053_neg : (328708081 / 1000000000) ≤ -Real.log (500000000000 / 694586135633) ∧
    -Real.log (500000000000 / 694586135633) ≤ (164354041 / 500000000) := by
  have h := checkLog_sound (w := (194586135633 / 1194586135633)) (n := 12)
    (lo := (328708081 / 1000000000)) (hi := (164354041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694586135633 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694586135633 / 500000000000) = 1/(500000000000 / 694586135633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10053 : Bounds (328708081 / 1000000000) (164354041 / 500000000) (Real.log (694586135633 / 500000000000)) := by
  have h := reflection_log_10053_neg
  have he : Real.log (694586135633 / 500000000000) = -Real.log (500000000000 / 694586135633) := by
    rw [show ((694586135633 / 500000000000) : ℝ) = ((500000000000 / 694586135633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10054_neg : (66088467 / 200000000) ≤ -Real.log (100000000000 / 139158353921) ∧
    -Real.log (100000000000 / 139158353921) ≤ (10326323 / 31250000) := by
  have h := checkLog_sound (w := (39158353921 / 239158353921)) (n := 12)
    (lo := (66088467 / 200000000)) (hi := (10326323 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139158353921 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139158353921 / 100000000000) = 1/(100000000000 / 139158353921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10054 : Bounds (66088467 / 200000000) (10326323 / 31250000) (Real.log (139158353921 / 100000000000)) := by
  have h := reflection_log_10054_neg
  have he : Real.log (139158353921 / 100000000000) = -Real.log (100000000000 / 139158353921) := by
    rw [show ((139158353921 / 100000000000) : ℝ) = ((100000000000 / 139158353921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10055_neg : (663294217 / 1000000000) ≤ -Real.log (250000000000 / 485294117647) ∧
    -Real.log (250000000000 / 485294117647) ≤ (331647109 / 500000000) := by
  have h := checkLog_sound (w := (235294117647 / 735294117647)) (n := 12)
    (lo := (663294217 / 1000000000)) (hi := (331647109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((485294117647 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(485294117647 / 250000000000) = 1/(250000000000 / 485294117647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10055 : Bounds (663294217 / 1000000000) (331647109 / 500000000) (Real.log (485294117647 / 250000000000)) := by
  have h := reflection_log_10055_neg
  have he : Real.log (485294117647 / 250000000000) = -Real.log (250000000000 / 485294117647) := by
    rw [show ((485294117647 / 250000000000) : ℝ) = ((250000000000 / 485294117647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10056_neg : (83190397 / 125000000) ≤ -Real.log (250000000000 / 486377025037) ∧
    -Real.log (250000000000 / 486377025037) ≤ (665523177 / 1000000000) := by
  have h := checkLog_sound (w := (236377025037 / 736377025037)) (n := 12)
    (lo := (83190397 / 125000000)) (hi := (665523177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((486377025037 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(486377025037 / 250000000000) = 1/(250000000000 / 486377025037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10056 : Bounds (83190397 / 125000000) (665523177 / 1000000000) (Real.log (486377025037 / 250000000000)) := by
  have h := reflection_log_10056_neg
  have he : Real.log (486377025037 / 250000000000) = -Real.log (250000000000 / 486377025037) := by
    rw [show ((486377025037 / 250000000000) : ℝ) = ((250000000000 / 486377025037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10057_neg : (279145741 / 1000000000) ≤ -Real.log (500 / 661) ∧
    -Real.log (500 / 661) ≤ (139572871 / 500000000) := by
  have h := checkLog_sound (w := (161 / 1161)) (n := 12)
    (lo := (279145741 / 1000000000)) (hi := (139572871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((661 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(661 / 500) = 1/(500 / 661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10057 : Bounds (279145741 / 1000000000) (139572871 / 500000000) (Real.log (661 / 500)) := by
  have h := reflection_log_10057_neg
  have he : Real.log (661 / 500) = -Real.log (500 / 661) := by
    rw [show ((661 / 500) : ℝ) = ((500 / 661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10058_neg : (388607991 / 1000000000) ≤ -Real.log (339 / 500) ∧
    -Real.log (339 / 500) ≤ (48575999 / 125000000) := by
  have h := checkLog_sound (w := (161 / 839)) (n := 12)
    (lo := (388607991 / 1000000000)) (hi := (48575999 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 339) = 1/(339 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10058 : Bounds (-48575999 / 125000000) (-388607991 / 1000000000) (Real.log (339 / 500)) := by
  have h := reflection_log_10058_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10059_neg : (80487 / 250000000) ≤ -Real.log (500000 / 500161) ∧
    -Real.log (500000 / 500161) ≤ (321949 / 1000000000) := by
  have h := checkLog_sound (w := (161 / 1000161)) (n := 12)
    (lo := (80487 / 250000000)) (hi := (321949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500161 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500161 / 500000) = 1/(500000 / 500161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10059 : Bounds (80487 / 250000000) (321949 / 1000000000) (Real.log (500161 / 500000)) := by
  have h := reflection_log_10059_neg
  have he : Real.log (500161 / 500000) = -Real.log (500000 / 500161) := by
    rw [show ((500161 / 500000) : ℝ) = ((500000 / 500161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10060_neg : (322051 / 1000000000) ≤ -Real.log (499839 / 500000) ∧
    -Real.log (499839 / 500000) ≤ (80513 / 250000000) := by
  have h := checkLog_sound (w := (161 / 999839)) (n := 12)
    (lo := (322051 / 1000000000)) (hi := (80513 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499839) = 1/(499839 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10060 : Bounds (-80513 / 250000000) (-322051 / 1000000000) (Real.log (499839 / 500000)) := by
  have h := reflection_log_10060_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10061_neg : (9460139 / 62500000) ≤ -Real.log (500000 / 581709) ∧
    -Real.log (500000 / 581709) ≤ (6054489 / 40000000) := by
  have h := checkLog_sound (w := (81709 / 1081709)) (n := 12)
    (lo := (9460139 / 62500000)) (hi := (6054489 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581709 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581709 / 500000) = 1/(500000 / 581709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10061 : Bounds (9460139 / 62500000) (6054489 / 40000000) (Real.log (581709 / 500000)) := by
  have h := reflection_log_10061_neg
  have he : Real.log (581709 / 500000) = -Real.log (500000 / 581709) := by
    rw [show ((581709 / 500000) : ℝ) = ((500000 / 581709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10062_neg : (35686147 / 200000000) ≤ -Real.log (418291 / 500000) ∧
    -Real.log (418291 / 500000) ≤ (11151921 / 62500000) := by
  have h := checkLog_sound (w := (81709 / 918291)) (n := 12)
    (lo := (35686147 / 200000000)) (hi := (11151921 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 418291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 418291) = 1/(418291 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10062 : Bounds (-11151921 / 62500000) (-35686147 / 200000000) (Real.log (418291 / 500000)) := by
  have h := reflection_log_10062_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10063_neg : (152089127 / 1000000000) ≤ -Real.log (125000 / 145533) ∧
    -Real.log (125000 / 145533) ≤ (19011141 / 125000000) := by
  have h := checkLog_sound (w := (20533 / 270533)) (n := 12)
    (lo := (152089127 / 1000000000)) (hi := (19011141 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145533 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145533 / 125000) = 1/(125000 / 145533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10063 : Bounds (152089127 / 1000000000) (19011141 / 125000000) (Real.log (145533 / 125000)) := by
  have h := reflection_log_10063_neg
  have he : Real.log (145533 / 125000) = -Real.log (125000 / 145533) := by
    rw [show ((145533 / 125000) : ℝ) = ((125000 / 145533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10064_neg : (35888501 / 200000000) ≤ -Real.log (104467 / 125000) ∧
    -Real.log (104467 / 125000) ≤ (89721253 / 500000000) := by
  have h := checkLog_sound (w := (20533 / 229467)) (n := 12)
    (lo := (35888501 / 200000000)) (hi := (89721253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 104467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 104467) = 1/(104467 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10064 : Bounds (-89721253 / 500000000) (-35888501 / 200000000) (Real.log (104467 / 125000)) := by
  have h := reflection_log_10064_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10065_neg : (27353377 / 1000000000) ≤ -Real.log (15203395911 / 15625000000) ∧
    -Real.log (15203395911 / 15625000000) ≤ (13676689 / 500000000) := by
  have h := checkLog_sound (w := (421604089 / 30828395911)) (n := 12)
    (lo := (27353377 / 1000000000)) (hi := (13676689 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15203395911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15203395911) = 1/(15203395911 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10065 : Bounds (-13676689 / 500000000) (-27353377 / 1000000000) (Real.log (15203395911 / 15625000000)) := by
  have h := reflection_log_10065_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10066_neg : (27068511 / 1000000000) ≤ -Real.log (243323639319 / 250000000000) ∧
    -Real.log (243323639319 / 250000000000) ≤ (845891 / 31250000) := by
  have h := checkLog_sound (w := (6676360681 / 493323639319)) (n := 12)
    (lo := (27068511 / 1000000000)) (hi := (845891 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243323639319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243323639319) = 1/(243323639319 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10066 : Bounds (-845891 / 31250000) (-27068511 / 1000000000) (Real.log (243323639319 / 250000000000)) := by
  have h := reflection_log_10066_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10067_neg : (1030603 / 3125000) ≤ -Real.log (500000000000 / 695340086207) ∧
    -Real.log (500000000000 / 695340086207) ≤ (329792961 / 1000000000) := by
  have h := checkLog_sound (w := (195340086207 / 1195340086207)) (n := 12)
    (lo := (1030603 / 3125000)) (hi := (329792961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695340086207 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695340086207 / 500000000000) = 1/(500000000000 / 695340086207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10067 : Bounds (1030603 / 3125000) (329792961 / 1000000000) (Real.log (695340086207 / 500000000000)) := by
  have h := reflection_log_10067_neg
  have he : Real.log (695340086207 / 500000000000) = -Real.log (500000000000 / 695340086207) := by
    rw [show ((695340086207 / 500000000000) : ℝ) = ((500000000000 / 695340086207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10068_neg : (20720727 / 62500000) ≤ -Real.log (500000000000 / 696550106733) ∧
    -Real.log (500000000000 / 696550106733) ≤ (331531633 / 1000000000) := by
  have h := checkLog_sound (w := (196550106733 / 1196550106733)) (n := 12)
    (lo := (20720727 / 62500000)) (hi := (331531633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696550106733 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696550106733 / 500000000000) = 1/(500000000000 / 696550106733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10068 : Bounds (20720727 / 62500000) (331531633 / 1000000000) (Real.log (696550106733 / 500000000000)) := by
  have h := reflection_log_10068_neg
  have he : Real.log (696550106733 / 500000000000) = -Real.log (500000000000 / 696550106733) := by
    rw [show ((696550106733 / 500000000000) : ℝ) = ((500000000000 / 696550106733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10069_neg : (83190397 / 125000000) ≤ -Real.log (500000000000 / 972754050073) ∧
    -Real.log (500000000000 / 972754050073) ≤ (665523177 / 1000000000) := by
  have h := checkLog_sound (w := (472754050073 / 1472754050073)) (n := 12)
    (lo := (83190397 / 125000000)) (hi := (665523177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((972754050073 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(972754050073 / 500000000000) = 1/(500000000000 / 972754050073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10069 : Bounds (83190397 / 125000000) (665523177 / 1000000000) (Real.log (972754050073 / 500000000000)) := by
  have h := reflection_log_10069_neg
  have he : Real.log (972754050073 / 500000000000) = -Real.log (500000000000 / 972754050073) := by
    rw [show ((972754050073 / 500000000000) : ℝ) = ((500000000000 / 972754050073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10070_neg : (166938433 / 250000000) ≤ -Real.log (62500000000 / 121865781711) ∧
    -Real.log (62500000000 / 121865781711) ≤ (667753733 / 1000000000) := by
  have h := checkLog_sound (w := (59365781711 / 184365781711)) (n := 12)
    (lo := (166938433 / 250000000)) (hi := (667753733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121865781711 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121865781711 / 62500000000) = 1/(62500000000 / 121865781711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10070 : Bounds (166938433 / 250000000) (667753733 / 1000000000) (Real.log (121865781711 / 62500000000)) := by
  have h := reflection_log_10070_neg
  have he : Real.log (121865781711 / 62500000000) = -Real.log (62500000000 / 121865781711) := by
    rw [show ((121865781711 / 62500000000) : ℝ) = ((62500000000 / 121865781711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10071_neg : (55980377 / 200000000) ≤ -Real.log (1000 / 1323) ∧
    -Real.log (1000 / 1323) ≤ (139950943 / 500000000) := by
  have h := checkLog_sound (w := (323 / 2323)) (n := 12)
    (lo := (55980377 / 200000000)) (hi := (139950943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1323 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1323 / 1000) = 1/(1000 / 1323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10071 : Bounds (55980377 / 200000000) (139950943 / 500000000) (Real.log (1323 / 1000)) := by
  have h := reflection_log_10071_neg
  have he : Real.log (1323 / 1000) = -Real.log (1000 / 1323) := by
    rw [show ((1323 / 1000) : ℝ) = ((1000 / 1323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10072_neg : (195042003 / 500000000) ≤ -Real.log (677 / 1000) ∧
    -Real.log (677 / 1000) ≤ (390084007 / 1000000000) := by
  have h := checkLog_sound (w := (323 / 1677)) (n := 12)
    (lo := (195042003 / 500000000)) (hi := (390084007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 677) = 1/(677 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10072 : Bounds (-390084007 / 1000000000) (-195042003 / 500000000) (Real.log (677 / 1000)) := by
  have h := reflection_log_10072_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10073_neg : (322947 / 1000000000) ≤ -Real.log (1000000 / 1000323) ∧
    -Real.log (1000000 / 1000323) ≤ (80737 / 250000000) := by
  have h := checkLog_sound (w := (323 / 2000323)) (n := 12)
    (lo := (322947 / 1000000000)) (hi := (80737 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000323 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000323 / 1000000) = 1/(1000000 / 1000323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10073 : Bounds (322947 / 1000000000) (80737 / 250000000) (Real.log (1000323 / 1000000)) := by
  have h := reflection_log_10073_neg
  have he : Real.log (1000323 / 1000000) = -Real.log (1000000 / 1000323) := by
    rw [show ((1000323 / 1000000) : ℝ) = ((1000000 / 1000323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10074_neg : (80763 / 250000000) ≤ -Real.log (999677 / 1000000) ∧
    -Real.log (999677 / 1000000) ≤ (323053 / 1000000000) := by
  have h := checkLog_sound (w := (323 / 1999677)) (n := 12)
    (lo := (80763 / 250000000)) (hi := (323053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999677) = 1/(999677 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10074 : Bounds (-323053 / 1000000000) (-80763 / 250000000) (Real.log (999677 / 1000000)) := by
  have h := reflection_log_10074_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10075_neg : (30363363 / 200000000) ≤ -Real.log (1000000 / 1163947) ∧
    -Real.log (1000000 / 1163947) ≤ (9488551 / 62500000) := by
  have h := checkLog_sound (w := (163947 / 2163947)) (n := 12)
    (lo := (30363363 / 200000000)) (hi := (9488551 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1163947 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1163947 / 1000000) = 1/(1000000 / 1163947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10075 : Bounds (30363363 / 200000000) (9488551 / 62500000) (Real.log (1163947 / 1000000)) := by
  have h := reflection_log_10075_neg
  have he : Real.log (1163947 / 1000000) = -Real.log (1000000 / 1163947) := by
    rw [show ((1163947 / 1000000) : ℝ) = ((1000000 / 1163947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10076_neg : (17906327 / 100000000) ≤ -Real.log (836053 / 1000000) ∧
    -Real.log (836053 / 1000000) ≤ (179063271 / 1000000000) := by
  have h := checkLog_sound (w := (163947 / 1836053)) (n := 12)
    (lo := (17906327 / 100000000)) (hi := (179063271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 836053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 836053) = 1/(836053 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10076 : Bounds (-179063271 / 1000000000) (-17906327 / 100000000) (Real.log (836053 / 1000000)) := by
  have h := reflection_log_10076_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10077_neg : (152544247 / 1000000000) ≤ -Real.log (500000 / 582397) ∧
    -Real.log (500000 / 582397) ≤ (19068031 / 125000000) := by
  have h := checkLog_sound (w := (82397 / 1082397)) (n := 12)
    (lo := (152544247 / 1000000000)) (hi := (19068031 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582397 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582397 / 500000) = 1/(500000 / 582397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10077 : Bounds (152544247 / 1000000000) (19068031 / 125000000) (Real.log (582397 / 500000)) := by
  have h := reflection_log_10077_neg
  have he : Real.log (582397 / 500000) = -Real.log (500000 / 582397) := by
    rw [show ((582397 / 500000) : ℝ) = ((500000 / 582397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10078_neg : (180076877 / 1000000000) ≤ -Real.log (417603 / 500000) ∧
    -Real.log (417603 / 500000) ≤ (90038439 / 500000000) := by
  have h := checkLog_sound (w := (82397 / 917603)) (n := 12)
    (lo := (180076877 / 1000000000)) (hi := (90038439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 417603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 417603) = 1/(417603 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10078 : Bounds (-90038439 / 500000000) (-180076877 / 1000000000) (Real.log (417603 / 500000)) := by
  have h := reflection_log_10078_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10079_neg : (2753263 / 100000000) ≤ -Real.log (243210734391 / 250000000000) ∧
    -Real.log (243210734391 / 250000000000) ≤ (27532631 / 1000000000) := by
  have h := checkLog_sound (w := (6789265609 / 493210734391)) (n := 12)
    (lo := (2753263 / 100000000)) (hi := (27532631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243210734391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243210734391) = 1/(243210734391 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10079 : Bounds (-27532631 / 1000000000) (-2753263 / 100000000) (Real.log (243210734391 / 250000000000)) := by
  have h := reflection_log_10079_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10080_neg : (5449291 / 200000000) ≤ -Real.log (973121381191 / 1000000000000) ∧
    -Real.log (973121381191 / 1000000000000) ≤ (3405807 / 125000000) := by
  have h := checkLog_sound (w := (26878618809 / 1973121381191)) (n := 12)
    (lo := (5449291 / 200000000)) (hi := (3405807 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973121381191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973121381191) = 1/(973121381191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10080 : Bounds (-3405807 / 125000000) (-5449291 / 200000000) (Real.log (973121381191 / 1000000000000)) := by
  have h := reflection_log_10080_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10081_neg : (165440043 / 500000000) ≤ -Real.log (125000000000 / 174024104931) ∧
    -Real.log (125000000000 / 174024104931) ≤ (330880087 / 1000000000) := by
  have h := checkLog_sound (w := (49024104931 / 299024104931)) (n := 12)
    (lo := (165440043 / 500000000)) (hi := (330880087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174024104931 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(174024104931 / 125000000000) = 1/(125000000000 / 174024104931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10081 : Bounds (165440043 / 500000000) (330880087 / 1000000000) (Real.log (174024104931 / 125000000000)) := by
  have h := reflection_log_10081_neg
  have he : Real.log (174024104931 / 125000000000) = -Real.log (125000000000 / 174024104931) := by
    rw [show ((174024104931 / 125000000000) : ℝ) = ((125000000000 / 174024104931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10082_neg : (2660969 / 8000000) ≤ -Real.log (500000000000 / 697309406303) ∧
    -Real.log (500000000000 / 697309406303) ≤ (166310563 / 500000000) := by
  have h := checkLog_sound (w := (197309406303 / 1197309406303)) (n := 12)
    (lo := (2660969 / 8000000)) (hi := (166310563 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697309406303 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697309406303 / 500000000000) = 1/(500000000000 / 697309406303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10082 : Bounds (2660969 / 8000000) (166310563 / 500000000) (Real.log (697309406303 / 500000000000)) := by
  have h := reflection_log_10082_neg
  have he : Real.log (697309406303 / 500000000000) = -Real.log (500000000000 / 697309406303) := by
    rw [show ((697309406303 / 500000000000) : ℝ) = ((500000000000 / 697309406303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10083_neg : (166938433 / 250000000) ≤ -Real.log (500000000000 / 974926253687) ∧
    -Real.log (500000000000 / 974926253687) ≤ (667753733 / 1000000000) := by
  have h := checkLog_sound (w := (474926253687 / 1474926253687)) (n := 12)
    (lo := (166938433 / 250000000)) (hi := (667753733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((974926253687 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(974926253687 / 500000000000) = 1/(500000000000 / 974926253687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10083 : Bounds (166938433 / 250000000) (667753733 / 1000000000) (Real.log (974926253687 / 500000000000)) := by
  have h := reflection_log_10083_neg
  have he : Real.log (974926253687 / 500000000000) = -Real.log (500000000000 / 974926253687) := by
    rw [show ((974926253687 / 500000000000) : ℝ) = ((500000000000 / 974926253687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10084_neg : (669985891 / 1000000000) ≤ -Real.log (500000000000 / 977104874447) ∧
    -Real.log (500000000000 / 977104874447) ≤ (167496473 / 250000000) := by
  have h := checkLog_sound (w := (477104874447 / 1477104874447)) (n := 12)
    (lo := (669985891 / 1000000000)) (hi := (167496473 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((977104874447 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(977104874447 / 500000000000) = 1/(500000000000 / 977104874447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10084 : Bounds (669985891 / 1000000000) (167496473 / 250000000) (Real.log (977104874447 / 500000000000)) := by
  have h := reflection_log_10084_neg
  have he : Real.log (977104874447 / 500000000000) = -Real.log (500000000000 / 977104874447) := by
    rw [show ((977104874447 / 500000000000) : ℝ) = ((500000000000 / 977104874447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10085_neg : (280657457 / 1000000000) ≤ -Real.log (250 / 331) ∧
    -Real.log (250 / 331) ≤ (140328729 / 500000000) := by
  have h := checkLog_sound (w := (81 / 581)) (n := 12)
    (lo := (280657457 / 1000000000)) (hi := (140328729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((331 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(331 / 250) = 1/(250 / 331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10085 : Bounds (280657457 / 1000000000) (140328729 / 500000000) (Real.log (331 / 250)) := by
  have h := reflection_log_10085_neg
  have he : Real.log (331 / 250) = -Real.log (250 / 331) := by
    rw [show ((331 / 250) : ℝ) = ((250 / 331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10086_neg : (195781101 / 500000000) ≤ -Real.log (169 / 250) ∧
    -Real.log (169 / 250) ≤ (391562203 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 419)) (n := 12)
    (lo := (195781101 / 500000000)) (hi := (391562203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 169) = 1/(169 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10086 : Bounds (-391562203 / 1000000000) (-195781101 / 500000000) (Real.log (169 / 250)) := by
  have h := reflection_log_10086_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10087_neg : (323947 / 1000000000) ≤ -Real.log (250000 / 250081) ∧
    -Real.log (250000 / 250081) ≤ (80987 / 250000000) := by
  have h := checkLog_sound (w := (81 / 500081)) (n := 12)
    (lo := (323947 / 1000000000)) (hi := (80987 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250081 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250081 / 250000) = 1/(250000 / 250081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10087 : Bounds (323947 / 1000000000) (80987 / 250000000) (Real.log (250081 / 250000)) := by
  have h := reflection_log_10087_neg
  have he : Real.log (250081 / 250000) = -Real.log (250000 / 250081) := by
    rw [show ((250081 / 250000) : ℝ) = ((250000 / 250081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10088_neg : (81013 / 250000000) ≤ -Real.log (249919 / 250000) ∧
    -Real.log (249919 / 250000) ≤ (324053 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 499919)) (n := 12)
    (lo := (81013 / 250000000)) (hi := (324053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249919) = 1/(249919 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10088 : Bounds (-324053 / 1000000000) (-81013 / 250000000) (Real.log (249919 / 250000)) := by
  have h := reflection_log_10088_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10089_neg : (152272059 / 1000000000) ≤ -Real.log (1000000 / 1164477) ∧
    -Real.log (1000000 / 1164477) ≤ (7613603 / 50000000) := by
  have h := checkLog_sound (w := (164477 / 2164477)) (n := 12)
    (lo := (152272059 / 1000000000)) (hi := (7613603 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1164477 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1164477 / 1000000) = 1/(1000000 / 1164477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10089 : Bounds (152272059 / 1000000000) (7613603 / 50000000) (Real.log (1164477 / 1000000)) := by
  have h := reflection_log_10089_neg
  have he : Real.log (1164477 / 1000000) = -Real.log (1000000 / 1164477) := by
    rw [show ((1164477 / 1000000) : ℝ) = ((1000000 / 1164477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10090_neg : (89848701 / 500000000) ≤ -Real.log (835523 / 1000000) ∧
    -Real.log (835523 / 1000000) ≤ (179697403 / 1000000000) := by
  have h := checkLog_sound (w := (164477 / 1835523)) (n := 12)
    (lo := (89848701 / 500000000)) (hi := (179697403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 835523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 835523) = 1/(835523 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10090 : Bounds (-179697403 / 1000000000) (-89848701 / 500000000) (Real.log (835523 / 1000000)) := by
  have h := reflection_log_10090_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10091_neg : (76500009 / 500000000) ≤ -Real.log (40000 / 46613) ∧
    -Real.log (40000 / 46613) ≤ (153000019 / 1000000000) := by
  have h := checkLog_sound (w := (6613 / 86613)) (n := 12)
    (lo := (76500009 / 500000000)) (hi := (153000019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46613 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46613 / 40000) = 1/(40000 / 46613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10091 : Bounds (76500009 / 500000000) (153000019 / 1000000000) (Real.log (46613 / 40000)) := by
  have h := reflection_log_10091_neg
  have he : Real.log (46613 / 40000) = -Real.log (40000 / 46613) := by
    rw [show ((46613 / 40000) : ℝ) = ((40000 / 46613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10092_neg : (180712851 / 1000000000) ≤ -Real.log (33387 / 40000) ∧
    -Real.log (33387 / 40000) ≤ (45178213 / 250000000) := by
  have h := checkLog_sound (w := (6613 / 73387)) (n := 12)
    (lo := (180712851 / 1000000000)) (hi := (45178213 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 33387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 33387) = 1/(33387 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10092 : Bounds (-45178213 / 250000000) (-180712851 / 1000000000) (Real.log (33387 / 40000)) := by
  have h := reflection_log_10092_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10093_neg : (27712833 / 1000000000) ≤ -Real.log (1556268231 / 1600000000) ∧
    -Real.log (1556268231 / 1600000000) ≤ (13856417 / 500000000) := by
  have h := checkLog_sound (w := (43731769 / 3156268231)) (n := 12)
    (lo := (27712833 / 1000000000)) (hi := (13856417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1556268231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1556268231) = 1/(1556268231 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10093 : Bounds (-13856417 / 500000000) (-27712833 / 1000000000) (Real.log (1556268231 / 1600000000)) := by
  have h := reflection_log_10093_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10094_neg : (27425343 / 1000000000) ≤ -Real.log (972947316471 / 1000000000000) ∧
    -Real.log (972947316471 / 1000000000000) ≤ (428521 / 15625000) := by
  have h := checkLog_sound (w := (27052683529 / 1972947316471)) (n := 12)
    (lo := (27425343 / 1000000000)) (hi := (428521 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 972947316471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 972947316471) = 1/(972947316471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10094 : Bounds (-428521 / 15625000) (-27425343 / 1000000000) (Real.log (972947316471 / 1000000000000)) := by
  have h := reflection_log_10094_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10095_neg : (165984731 / 500000000) ≤ -Real.log (20000000000 / 27874205737) ∧
    -Real.log (20000000000 / 27874205737) ≤ (331969463 / 1000000000) := by
  have h := checkLog_sound (w := (7874205737 / 47874205737)) (n := 12)
    (lo := (165984731 / 500000000)) (hi := (331969463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27874205737 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27874205737 / 20000000000) = 1/(20000000000 / 27874205737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10095 : Bounds (165984731 / 500000000) (331969463 / 1000000000) (Real.log (27874205737 / 20000000000)) := by
  have h := reflection_log_10095_neg
  have he : Real.log (27874205737 / 20000000000) = -Real.log (20000000000 / 27874205737) := by
    rw [show ((27874205737 / 20000000000) : ℝ) = ((20000000000 / 27874205737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10096_neg : (333712869 / 1000000000) ≤ -Real.log (500000000000 / 698071105521) ∧
    -Real.log (500000000000 / 698071105521) ≤ (33371287 / 100000000) := by
  have h := checkLog_sound (w := (198071105521 / 1198071105521)) (n := 12)
    (lo := (333712869 / 1000000000)) (hi := (33371287 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((698071105521 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(698071105521 / 500000000000) = 1/(500000000000 / 698071105521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10096 : Bounds (333712869 / 1000000000) (33371287 / 100000000) (Real.log (698071105521 / 500000000000)) := by
  have h := reflection_log_10096_neg
  have he : Real.log (698071105521 / 500000000000) = -Real.log (500000000000 / 698071105521) := by
    rw [show ((698071105521 / 500000000000) : ℝ) = ((500000000000 / 698071105521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10097_neg : (669985891 / 1000000000) ≤ -Real.log (250000000000 / 488552437223) ∧
    -Real.log (250000000000 / 488552437223) ≤ (167496473 / 250000000) := by
  have h := checkLog_sound (w := (238552437223 / 738552437223)) (n := 12)
    (lo := (669985891 / 1000000000)) (hi := (167496473 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((488552437223 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(488552437223 / 250000000000) = 1/(250000000000 / 488552437223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10097 : Bounds (669985891 / 1000000000) (167496473 / 250000000) (Real.log (488552437223 / 250000000000)) := by
  have h := reflection_log_10097_neg
  have he : Real.log (488552437223 / 250000000000) = -Real.log (250000000000 / 488552437223) := by
    rw [show ((488552437223 / 250000000000) : ℝ) = ((250000000000 / 488552437223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10098_neg : (33610983 / 50000000) ≤ -Real.log (500000000000 / 979289940829) ∧
    -Real.log (500000000000 / 979289940829) ≤ (672219661 / 1000000000) := by
  have h := checkLog_sound (w := (479289940829 / 1479289940829)) (n := 12)
    (lo := (33610983 / 50000000)) (hi := (672219661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((979289940829 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(979289940829 / 500000000000) = 1/(500000000000 / 979289940829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10098 : Bounds (33610983 / 50000000) (672219661 / 1000000000) (Real.log (979289940829 / 500000000000)) := by
  have h := reflection_log_10098_neg
  have he : Real.log (979289940829 / 500000000000) = -Real.log (500000000000 / 979289940829) := by
    rw [show ((979289940829 / 500000000000) : ℝ) = ((500000000000 / 979289940829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10099_neg : (281412459 / 1000000000) ≤ -Real.log (40 / 53) ∧
    -Real.log (40 / 53) ≤ (14070623 / 50000000) := by
  have h := checkLog_sound (w := (13 / 93)) (n := 12)
    (lo := (281412459 / 1000000000)) (hi := (14070623 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53 / 40) = 1/(40 / 53) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10099 : Bounds (281412459 / 1000000000) (14070623 / 50000000) (Real.log (53 / 40)) := by
  have h := reflection_log_10099_neg
  have he : Real.log (53 / 40) = -Real.log (40 / 53) := by
    rw [show ((53 / 40) : ℝ) = ((40 / 53) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10100_neg : (98260647 / 250000000) ≤ -Real.log (27 / 40) ∧
    -Real.log (27 / 40) ≤ (393042589 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 27) = 1/(27 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10100 : Bounds (-393042589 / 1000000000) (-98260647 / 250000000) (Real.log (27 / 40)) := by
  have h := reflection_log_10100_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10101_neg : (324947 / 1000000000) ≤ -Real.log (40000 / 40013) ∧
    -Real.log (40000 / 40013) ≤ (81237 / 250000000) := by
  have h := checkLog_sound (w := (13 / 80013)) (n := 12)
    (lo := (324947 / 1000000000)) (hi := (81237 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40013 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40013 / 40000) = 1/(40000 / 40013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10101 : Bounds (324947 / 1000000000) (81237 / 250000000) (Real.log (40013 / 40000)) := by
  have h := reflection_log_10101_neg
  have he : Real.log (40013 / 40000) = -Real.log (40000 / 40013) := by
    rw [show ((40013 / 40000) : ℝ) = ((40000 / 40013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10102_neg : (81263 / 250000000) ≤ -Real.log (39987 / 40000) ∧
    -Real.log (39987 / 40000) ≤ (325053 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 79987)) (n := 12)
    (lo := (81263 / 250000000)) (hi := (325053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 39987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 39987) = 1/(39987 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10102 : Bounds (-325053 / 1000000000) (-81263 / 250000000) (Real.log (39987 / 40000)) := by
  have h := reflection_log_10102_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10103_neg : (152726237 / 1000000000) ≤ -Real.log (500000 / 582503) ∧
    -Real.log (500000 / 582503) ≤ (76363119 / 500000000) := by
  have h := checkLog_sound (w := (82503 / 1082503)) (n := 12)
    (lo := (152726237 / 1000000000)) (hi := (76363119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582503 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582503 / 500000) = 1/(500000 / 582503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10103 : Bounds (152726237 / 1000000000) (76363119 / 500000000) (Real.log (582503 / 500000)) := by
  have h := reflection_log_10103_neg
  have he : Real.log (582503 / 500000) = -Real.log (500000 / 582503) := by
    rw [show ((582503 / 500000) : ℝ) = ((500000 / 582503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10104_neg : (180330739 / 1000000000) ≤ -Real.log (417497 / 500000) ∧
    -Real.log (417497 / 500000) ≤ (9016537 / 50000000) := by
  have h := checkLog_sound (w := (82503 / 917497)) (n := 12)
    (lo := (180330739 / 1000000000)) (hi := (9016537 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 417497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 417497) = 1/(417497 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10104 : Bounds (-9016537 / 50000000) (-180330739 / 1000000000) (Real.log (417497 / 500000)) := by
  have h := reflection_log_10104_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10105_neg : (153454723 / 1000000000) ≤ -Real.log (200000 / 233171) ∧
    -Real.log (200000 / 233171) ≤ (38363681 / 250000000) := by
  have h := checkLog_sound (w := (33171 / 433171)) (n := 12)
    (lo := (153454723 / 1000000000)) (hi := (38363681 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233171 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233171 / 200000) = 1/(200000 / 233171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10105 : Bounds (153454723 / 1000000000) (38363681 / 250000000) (Real.log (233171 / 200000)) := by
  have h := reflection_log_10105_neg
  have he : Real.log (233171 / 200000) = -Real.log (200000 / 233171) := by
    rw [show ((233171 / 200000) : ℝ) = ((200000 / 233171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10106_neg : (18134803 / 100000000) ≤ -Real.log (166829 / 200000) ∧
    -Real.log (166829 / 200000) ≤ (181348031 / 1000000000) := by
  have h := checkLog_sound (w := (33171 / 366829)) (n := 12)
    (lo := (18134803 / 100000000)) (hi := (181348031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 166829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 166829) = 1/(166829 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10106 : Bounds (-181348031 / 1000000000) (-18134803 / 100000000) (Real.log (166829 / 200000)) := by
  have h := reflection_log_10106_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10107_neg : (27893307 / 1000000000) ≤ -Real.log (38899684759 / 40000000000) ∧
    -Real.log (38899684759 / 40000000000) ≤ (6973327 / 250000000) := by
  have h := checkLog_sound (w := (1100315241 / 78899684759)) (n := 12)
    (lo := (27893307 / 1000000000)) (hi := (6973327 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38899684759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38899684759) = 1/(38899684759 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10107 : Bounds (-6973327 / 250000000) (-27893307 / 1000000000) (Real.log (38899684759 / 40000000000)) := by
  have h := reflection_log_10107_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10108_neg : (13802251 / 500000000) ≤ -Real.log (243193254991 / 250000000000) ∧
    -Real.log (243193254991 / 250000000000) ≤ (27604503 / 1000000000) := by
  have h := checkLog_sound (w := (6806745009 / 493193254991)) (n := 12)
    (lo := (13802251 / 500000000)) (hi := (27604503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243193254991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243193254991) = 1/(243193254991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10108 : Bounds (-27604503 / 1000000000) (-13802251 / 500000000) (Real.log (243193254991 / 250000000000)) := by
  have h := reflection_log_10108_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10109_neg : (333056977 / 1000000000) ≤ -Real.log (62500000000 / 87201674503) ∧
    -Real.log (62500000000 / 87201674503) ≤ (166528489 / 500000000) := by
  have h := checkLog_sound (w := (24701674503 / 149701674503)) (n := 12)
    (lo := (333056977 / 1000000000)) (hi := (166528489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87201674503 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87201674503 / 62500000000) = 1/(62500000000 / 87201674503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10109 : Bounds (333056977 / 1000000000) (166528489 / 500000000) (Real.log (87201674503 / 62500000000)) := by
  have h := reflection_log_10109_neg
  have he : Real.log (87201674503 / 62500000000) = -Real.log (62500000000 / 87201674503) := by
    rw [show ((87201674503 / 62500000000) : ℝ) = ((62500000000 / 87201674503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10110_neg : (167401377 / 500000000) ≤ -Real.log (62500000000 / 87354042163) ∧
    -Real.log (62500000000 / 87354042163) ≤ (66960551 / 200000000) := by
  have h := checkLog_sound (w := (24854042163 / 149854042163)) (n := 12)
    (lo := (167401377 / 500000000)) (hi := (66960551 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87354042163 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87354042163 / 62500000000) = 1/(62500000000 / 87354042163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10110 : Bounds (167401377 / 500000000) (66960551 / 200000000) (Real.log (87354042163 / 62500000000)) := by
  have h := reflection_log_10110_neg
  have he : Real.log (87354042163 / 62500000000) = -Real.log (62500000000 / 87354042163) := by
    rw [show ((87354042163 / 62500000000) : ℝ) = ((62500000000 / 87354042163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10111_neg : (33610983 / 50000000) ≤ -Real.log (125000000000 / 244822485207) ∧
    -Real.log (125000000000 / 244822485207) ≤ (672219661 / 1000000000) := by
  have h := checkLog_sound (w := (119822485207 / 369822485207)) (n := 12)
    (lo := (33610983 / 50000000)) (hi := (672219661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244822485207 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244822485207 / 125000000000) = 1/(125000000000 / 244822485207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10111 : Bounds (33610983 / 50000000) (672219661 / 1000000000) (Real.log (244822485207 / 125000000000)) := by
  have h := reflection_log_10111_neg
  have he : Real.log (244822485207 / 125000000000) = -Real.log (125000000000 / 244822485207) := by
    rw [show ((244822485207 / 125000000000) : ℝ) = ((125000000000 / 244822485207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0158 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10112_neg : (674455047 / 1000000000) ≤ -Real.log (250000000000 / 490740740741) ∧
    -Real.log (250000000000 / 490740740741) ≤ (84306881 / 125000000) := by
  have h := checkLog_sound (w := (240740740741 / 740740740741)) (n := 12)
    (lo := (674455047 / 1000000000)) (hi := (84306881 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((490740740741 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(490740740741 / 250000000000) = 1/(250000000000 / 490740740741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10112 : Bounds (674455047 / 1000000000) (84306881 / 125000000) (Real.log (490740740741 / 250000000000)) := by
  have h := reflection_log_10112_neg
  have he : Real.log (490740740741 / 250000000000) = -Real.log (250000000000 / 490740740741) := by
    rw [show ((490740740741 / 250000000000) : ℝ) = ((250000000000 / 490740740741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10113_neg : (282166891 / 1000000000) ≤ -Real.log (500 / 663) ∧
    -Real.log (500 / 663) ≤ (70541723 / 250000000) := by
  have h := checkLog_sound (w := (163 / 1163)) (n := 12)
    (lo := (282166891 / 1000000000)) (hi := (70541723 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((663 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(663 / 500) = 1/(500 / 663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10113 : Bounds (282166891 / 1000000000) (70541723 / 250000000) (Real.log (663 / 500)) := by
  have h := reflection_log_10113_neg
  have he : Real.log (663 / 500) = -Real.log (500 / 663) := by
    rw [show ((663 / 500) : ℝ) = ((500 / 663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10114_neg : (24657823 / 62500000) ≤ -Real.log (337 / 500) ∧
    -Real.log (337 / 500) ≤ (394525169 / 1000000000) := by
  have h := checkLog_sound (w := (163 / 837)) (n := 12)
    (lo := (24657823 / 62500000)) (hi := (394525169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 337) = 1/(337 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10114 : Bounds (-394525169 / 1000000000) (-24657823 / 62500000) (Real.log (337 / 500)) := by
  have h := reflection_log_10114_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10115_neg : (162973 / 500000000) ≤ -Real.log (500000 / 500163) ∧
    -Real.log (500000 / 500163) ≤ (325947 / 1000000000) := by
  have h := checkLog_sound (w := (163 / 1000163)) (n := 12)
    (lo := (162973 / 500000000)) (hi := (325947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500163 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500163 / 500000) = 1/(500000 / 500163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10115 : Bounds (162973 / 500000000) (325947 / 1000000000) (Real.log (500163 / 500000)) := by
  have h := reflection_log_10115_neg
  have he : Real.log (500163 / 500000) = -Real.log (500000 / 500163) := by
    rw [show ((500163 / 500000) : ℝ) = ((500000 / 500163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10116_neg : (326053 / 1000000000) ≤ -Real.log (499837 / 500000) ∧
    -Real.log (499837 / 500000) ≤ (163027 / 500000000) := by
  have h := checkLog_sound (w := (163 / 999837)) (n := 12)
    (lo := (326053 / 1000000000)) (hi := (163027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499837) = 1/(499837 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10116 : Bounds (-163027 / 500000000) (-326053 / 1000000000) (Real.log (499837 / 500000)) := by
  have h := reflection_log_10116_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10117_neg : (153181067 / 1000000000) ≤ -Real.log (31250 / 36423) ∧
    -Real.log (31250 / 36423) ≤ (38295267 / 250000000) := by
  have h := checkLog_sound (w := (5173 / 67673)) (n := 12)
    (lo := (153181067 / 1000000000)) (hi := (38295267 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36423 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36423 / 31250) = 1/(31250 / 36423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10117 : Bounds (153181067 / 1000000000) (38295267 / 250000000) (Real.log (36423 / 31250)) := by
  have h := reflection_log_10117_neg
  have he : Real.log (36423 / 31250) = -Real.log (31250 / 36423) := by
    rw [show ((36423 / 31250) : ℝ) = ((31250 / 36423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10118_neg : (45241419 / 250000000) ≤ -Real.log (26077 / 31250) ∧
    -Real.log (26077 / 31250) ≤ (180965677 / 1000000000) := by
  have h := checkLog_sound (w := (5173 / 57327)) (n := 12)
    (lo := (45241419 / 250000000)) (hi := (180965677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 26077) = 1/(26077 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10118 : Bounds (-180965677 / 1000000000) (-45241419 / 250000000) (Real.log (26077 / 31250)) := by
  have h := reflection_log_10118_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10119_neg : (153910079 / 1000000000) ≤ -Real.log (500000 / 583193) ∧
    -Real.log (500000 / 583193) ≤ (480969 / 3125000) := by
  have h := checkLog_sound (w := (83193 / 1083193)) (n := 12)
    (lo := (153910079 / 1000000000)) (hi := (480969 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583193 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583193 / 500000) = 1/(500000 / 583193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10119 : Bounds (153910079 / 1000000000) (480969 / 3125000) (Real.log (583193 / 500000)) := by
  have h := reflection_log_10119_neg
  have he : Real.log (583193 / 500000) = -Real.log (500000 / 583193) := by
    rw [show ((583193 / 500000) : ℝ) = ((500000 / 583193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10120_neg : (181984813 / 1000000000) ≤ -Real.log (416807 / 500000) ∧
    -Real.log (416807 / 500000) ≤ (90992407 / 500000000) := by
  have h := checkLog_sound (w := (83193 / 916807)) (n := 12)
    (lo := (181984813 / 1000000000)) (hi := (90992407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 416807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 416807) = 1/(416807 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10120 : Bounds (-90992407 / 500000000) (-181984813 / 1000000000) (Real.log (416807 / 500000)) := by
  have h := reflection_log_10120_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10121_neg : (14037367 / 500000000) ≤ -Real.log (243078924751 / 250000000000) ∧
    -Real.log (243078924751 / 250000000000) ≤ (5614947 / 200000000) := by
  have h := checkLog_sound (w := (6921075249 / 493078924751)) (n := 12)
    (lo := (14037367 / 500000000)) (hi := (5614947 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243078924751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243078924751) = 1/(243078924751 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10121 : Bounds (-5614947 / 200000000) (-14037367 / 500000000) (Real.log (243078924751 / 250000000000)) := by
  have h := reflection_log_10121_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10122_neg : (27784609 / 1000000000) ≤ -Real.log (949802571 / 976562500) ∧
    -Real.log (949802571 / 976562500) ≤ (2778461 / 100000000) := by
  have h := checkLog_sound (w := (26759929 / 1926365071)) (n := 12)
    (lo := (27784609 / 1000000000)) (hi := (2778461 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 949802571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 949802571) = 1/(949802571 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10122 : Bounds (-2778461 / 100000000) (-27784609 / 1000000000) (Real.log (949802571 / 976562500)) := by
  have h := reflection_log_10122_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10123_neg : (334146743 / 1000000000) ≤ -Real.log (250000000000 / 349187023047) ∧
    -Real.log (250000000000 / 349187023047) ≤ (41768343 / 125000000) := by
  have h := checkLog_sound (w := (99187023047 / 599187023047)) (n := 12)
    (lo := (334146743 / 1000000000)) (hi := (41768343 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349187023047 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349187023047 / 250000000000) = 1/(250000000000 / 349187023047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10123 : Bounds (334146743 / 1000000000) (41768343 / 125000000) (Real.log (349187023047 / 250000000000)) := by
  have h := reflection_log_10123_neg
  have he : Real.log (349187023047 / 250000000000) = -Real.log (250000000000 / 349187023047) := by
    rw [show ((349187023047 / 250000000000) : ℝ) = ((250000000000 / 349187023047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10124_neg : (83973723 / 250000000) ≤ -Real.log (125000000000 / 174898994019) ∧
    -Real.log (125000000000 / 174898994019) ≤ (335894893 / 1000000000) := by
  have h := checkLog_sound (w := (49898994019 / 299898994019)) (n := 12)
    (lo := (83973723 / 250000000)) (hi := (335894893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174898994019 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(174898994019 / 125000000000) = 1/(125000000000 / 174898994019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10124 : Bounds (83973723 / 250000000) (335894893 / 1000000000) (Real.log (174898994019 / 125000000000)) := by
  have h := reflection_log_10124_neg
  have he : Real.log (174898994019 / 125000000000) = -Real.log (125000000000 / 174898994019) := by
    rw [show ((174898994019 / 125000000000) : ℝ) = ((125000000000 / 174898994019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10125_neg : (674455047 / 1000000000) ≤ -Real.log (500000000000 / 981481481481) ∧
    -Real.log (500000000000 / 981481481481) ≤ (84306881 / 125000000) := by
  have h := checkLog_sound (w := (481481481481 / 1481481481481)) (n := 12)
    (lo := (674455047 / 1000000000)) (hi := (84306881 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981481481481 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981481481481 / 500000000000) = 1/(500000000000 / 981481481481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10125 : Bounds (674455047 / 1000000000) (84306881 / 125000000) (Real.log (981481481481 / 500000000000)) := by
  have h := reflection_log_10125_neg
  have he : Real.log (981481481481 / 500000000000) = -Real.log (500000000000 / 981481481481) := by
    rw [show ((981481481481 / 500000000000) : ℝ) = ((500000000000 / 981481481481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10126_neg : (676692059 / 1000000000) ≤ -Real.log (500000000000 / 983679525223) ∧
    -Real.log (500000000000 / 983679525223) ≤ (33834603 / 50000000) := by
  have h := checkLog_sound (w := (483679525223 / 1483679525223)) (n := 12)
    (lo := (676692059 / 1000000000)) (hi := (33834603 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983679525223 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983679525223 / 500000000000) = 1/(500000000000 / 983679525223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10126 : Bounds (676692059 / 1000000000) (33834603 / 50000000) (Real.log (983679525223 / 500000000000)) := by
  have h := reflection_log_10126_neg
  have he : Real.log (983679525223 / 500000000000) = -Real.log (500000000000 / 983679525223) := by
    rw [show ((983679525223 / 500000000000) : ℝ) = ((500000000000 / 983679525223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10127_neg : (56584151 / 200000000) ≤ -Real.log (1000 / 1327) ∧
    -Real.log (1000 / 1327) ≤ (70730189 / 250000000) := by
  have h := checkLog_sound (w := (327 / 2327)) (n := 12)
    (lo := (56584151 / 200000000)) (hi := (70730189 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1327 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1327 / 1000) = 1/(1000 / 1327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10127 : Bounds (56584151 / 200000000) (70730189 / 250000000) (Real.log (1327 / 1000)) := by
  have h := reflection_log_10127_neg
  have he : Real.log (1327 / 1000) = -Real.log (1000 / 1327) := by
    rw [show ((1327 / 1000) : ℝ) = ((1000 / 1327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10128_neg : (396009949 / 1000000000) ≤ -Real.log (673 / 1000) ∧
    -Real.log (673 / 1000) ≤ (7920199 / 20000000) := by
  have h := checkLog_sound (w := (327 / 1673)) (n := 12)
    (lo := (396009949 / 1000000000)) (hi := (7920199 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 673) = 1/(673 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10128 : Bounds (-7920199 / 20000000) (-396009949 / 1000000000) (Real.log (673 / 1000)) := by
  have h := reflection_log_10128_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10129_neg : (163473 / 500000000) ≤ -Real.log (1000000 / 1000327) ∧
    -Real.log (1000000 / 1000327) ≤ (326947 / 1000000000) := by
  have h := checkLog_sound (w := (327 / 2000327)) (n := 12)
    (lo := (163473 / 500000000)) (hi := (326947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000327 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000327 / 1000000) = 1/(1000000 / 1000327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10129 : Bounds (163473 / 500000000) (326947 / 1000000000) (Real.log (1000327 / 1000000)) := by
  have h := reflection_log_10129_neg
  have he : Real.log (1000327 / 1000000) = -Real.log (1000000 / 1000327) := by
    rw [show ((1000327 / 1000000) : ℝ) = ((1000000 / 1000327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10130_neg : (327053 / 1000000000) ≤ -Real.log (999673 / 1000000) ∧
    -Real.log (999673 / 1000000) ≤ (163527 / 500000000) := by
  have h := checkLog_sound (w := (327 / 1999673)) (n := 12)
    (lo := (327053 / 1000000000)) (hi := (163527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999673) = 1/(999673 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10130 : Bounds (-163527 / 500000000) (-327053 / 1000000000) (Real.log (999673 / 1000000)) := by
  have h := reflection_log_10130_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10131_neg : (9602177 / 62500000) ≤ -Real.log (200000 / 233213) ∧
    -Real.log (200000 / 233213) ≤ (153634833 / 1000000000) := by
  have h := checkLog_sound (w := (33213 / 433213)) (n := 12)
    (lo := (9602177 / 62500000)) (hi := (153634833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233213 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233213 / 200000) = 1/(200000 / 233213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10131 : Bounds (9602177 / 62500000) (153634833 / 1000000000) (Real.log (233213 / 200000)) := by
  have h := reflection_log_10131_neg
  have he : Real.log (233213 / 200000) = -Real.log (200000 / 233213) := by
    rw [show ((233213 / 200000) : ℝ) = ((200000 / 233213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10132_neg : (181599817 / 1000000000) ≤ -Real.log (166787 / 200000) ∧
    -Real.log (166787 / 200000) ≤ (90799909 / 500000000) := by
  have h := checkLog_sound (w := (33213 / 366787)) (n := 12)
    (lo := (181599817 / 1000000000)) (hi := (90799909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 166787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 166787) = 1/(166787 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10132 : Bounds (-90799909 / 500000000) (-181599817 / 1000000000) (Real.log (166787 / 200000)) := by
  have h := reflection_log_10132_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10133_neg : (38591307 / 250000000) ≤ -Real.log (1000000 / 1166917) ∧
    -Real.log (1000000 / 1166917) ≤ (154365229 / 1000000000) := by
  have h := checkLog_sound (w := (166917 / 2166917)) (n := 12)
    (lo := (38591307 / 250000000)) (hi := (154365229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1166917 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1166917 / 1000000) = 1/(1000000 / 1166917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10133 : Bounds (38591307 / 250000000) (154365229 / 1000000000) (Real.log (1166917 / 1000000)) := by
  have h := reflection_log_10133_neg
  have he : Real.log (1166917 / 1000000) = -Real.log (1000000 / 1166917) := by
    rw [show ((1166917 / 1000000) : ℝ) = ((1000000 / 1166917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10134_neg : (182622001 / 1000000000) ≤ -Real.log (833083 / 1000000) ∧
    -Real.log (833083 / 1000000) ≤ (91311001 / 500000000) := by
  have h := checkLog_sound (w := (166917 / 1833083)) (n := 12)
    (lo := (182622001 / 1000000000)) (hi := (91311001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 833083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 833083) = 1/(833083 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10134 : Bounds (-91311001 / 500000000) (-182622001 / 1000000000) (Real.log (833083 / 1000000)) := by
  have h := reflection_log_10134_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10135_neg : (28256773 / 1000000000) ≤ -Real.log (972138715111 / 1000000000000) ∧
    -Real.log (972138715111 / 1000000000000) ≤ (14128387 / 500000000) := by
  have h := checkLog_sound (w := (27861284889 / 1972138715111)) (n := 12)
    (lo := (28256773 / 1000000000)) (hi := (14128387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 972138715111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 972138715111) = 1/(972138715111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10135 : Bounds (-14128387 / 500000000) (-28256773 / 1000000000) (Real.log (972138715111 / 1000000000000)) := by
  have h := reflection_log_10135_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10136_neg : (3495623 / 125000000) ≤ -Real.log (38896896631 / 40000000000) ∧
    -Real.log (38896896631 / 40000000000) ≤ (5592997 / 200000000) := by
  have h := checkLog_sound (w := (1103103369 / 78896896631)) (n := 12)
    (lo := (3495623 / 125000000)) (hi := (5592997 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38896896631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38896896631) = 1/(38896896631 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10136 : Bounds (-5592997 / 200000000) (-3495623 / 125000000) (Real.log (38896896631 / 40000000000)) := by
  have h := reflection_log_10136_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10137_neg : (335234649 / 1000000000) ≤ -Real.log (500000000000 / 699134225089) ∧
    -Real.log (500000000000 / 699134225089) ≤ (6704693 / 20000000) := by
  have h := checkLog_sound (w := (199134225089 / 1199134225089)) (n := 12)
    (lo := (335234649 / 1000000000)) (hi := (6704693 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699134225089 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699134225089 / 500000000000) = 1/(500000000000 / 699134225089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10137 : Bounds (335234649 / 1000000000) (6704693 / 20000000) (Real.log (699134225089 / 500000000000)) := by
  have h := reflection_log_10137_neg
  have he : Real.log (699134225089 / 500000000000) = -Real.log (500000000000 / 699134225089) := by
    rw [show ((699134225089 / 500000000000) : ℝ) = ((500000000000 / 699134225089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10138_neg : (33698723 / 100000000) ≤ -Real.log (500000000000 / 700360588321) ∧
    -Real.log (500000000000 / 700360588321) ≤ (336987231 / 1000000000) := by
  have h := checkLog_sound (w := (200360588321 / 1200360588321)) (n := 12)
    (lo := (33698723 / 100000000)) (hi := (336987231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((700360588321 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(700360588321 / 500000000000) = 1/(500000000000 / 700360588321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10138 : Bounds (33698723 / 100000000) (336987231 / 1000000000) (Real.log (700360588321 / 500000000000)) := by
  have h := reflection_log_10138_neg
  have he : Real.log (700360588321 / 500000000000) = -Real.log (500000000000 / 700360588321) := by
    rw [show ((700360588321 / 500000000000) : ℝ) = ((500000000000 / 700360588321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10139_neg : (676692059 / 1000000000) ≤ -Real.log (250000000000 / 491839762611) ∧
    -Real.log (250000000000 / 491839762611) ≤ (33834603 / 50000000) := by
  have h := checkLog_sound (w := (241839762611 / 741839762611)) (n := 12)
    (lo := (676692059 / 1000000000)) (hi := (33834603 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491839762611 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491839762611 / 250000000000) = 1/(250000000000 / 491839762611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10139 : Bounds (676692059 / 1000000000) (33834603 / 50000000) (Real.log (491839762611 / 250000000000)) := by
  have h := reflection_log_10139_neg
  have he : Real.log (491839762611 / 250000000000) = -Real.log (250000000000 / 491839762611) := by
    rw [show ((491839762611 / 250000000000) : ℝ) = ((250000000000 / 491839762611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10140_neg : (42433169 / 62500000) ≤ -Real.log (500000000000 / 985884101041) ∧
    -Real.log (500000000000 / 985884101041) ≤ (135786141 / 200000000) := by
  have h := checkLog_sound (w := (485884101041 / 1485884101041)) (n := 12)
    (lo := (42433169 / 62500000)) (hi := (135786141 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((985884101041 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(985884101041 / 500000000000) = 1/(500000000000 / 985884101041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10140 : Bounds (42433169 / 62500000) (135786141 / 200000000) (Real.log (985884101041 / 500000000000)) := by
  have h := reflection_log_10140_neg
  have he : Real.log (985884101041 / 500000000000) = -Real.log (500000000000 / 985884101041) := by
    rw [show ((985884101041 / 500000000000) : ℝ) = ((500000000000 / 985884101041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10141_neg : (283674051 / 1000000000) ≤ -Real.log (125 / 166) ∧
    -Real.log (125 / 166) ≤ (70918513 / 250000000) := by
  have h := checkLog_sound (w := (41 / 291)) (n := 12)
    (lo := (283674051 / 1000000000)) (hi := (70918513 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(166 / 125) = 1/(125 / 166) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10141 : Bounds (283674051 / 1000000000) (70918513 / 250000000) (Real.log (166 / 125)) := by
  have h := reflection_log_10141_neg
  have he : Real.log (166 / 125) = -Real.log (125 / 166) := by
    rw [show ((166 / 125) : ℝ) = ((125 / 166) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10142_neg : (198748469 / 500000000) ≤ -Real.log (84 / 125) ∧
    -Real.log (84 / 125) ≤ (397496939 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 209)) (n := 12)
    (lo := (198748469 / 500000000)) (hi := (397496939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 84) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 84) = 1/(84 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10142 : Bounds (-397496939 / 1000000000) (-198748469 / 500000000) (Real.log (84 / 125)) := by
  have h := reflection_log_10142_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10143_neg : (163973 / 500000000) ≤ -Real.log (125000 / 125041) ∧
    -Real.log (125000 / 125041) ≤ (327947 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 250041)) (n := 12)
    (lo := (163973 / 500000000)) (hi := (327947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125041 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125041 / 125000) = 1/(125000 / 125041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10143 : Bounds (163973 / 500000000) (327947 / 1000000000) (Real.log (125041 / 125000)) := by
  have h := reflection_log_10143_neg
  have he : Real.log (125041 / 125000) = -Real.log (125000 / 125041) := by
    rw [show ((125041 / 125000) : ℝ) = ((125000 / 125041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10144_neg : (328053 / 1000000000) ≤ -Real.log (124959 / 125000) ∧
    -Real.log (124959 / 125000) ≤ (164027 / 500000000) := by
  have h := checkLog_sound (w := (41 / 249959)) (n := 12)
    (lo := (328053 / 1000000000)) (hi := (164027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124959) = 1/(124959 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10144 : Bounds (-164027 / 500000000) (-328053 / 1000000000) (Real.log (124959 / 125000)) := by
  have h := reflection_log_10144_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10145_neg : (154089249 / 1000000000) ≤ -Real.log (200000 / 233319) ∧
    -Real.log (200000 / 233319) ≤ (616357 / 4000000) := by
  have h := checkLog_sound (w := (33319 / 433319)) (n := 12)
    (lo := (154089249 / 1000000000)) (hi := (616357 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233319 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233319 / 200000) = 1/(200000 / 233319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10145 : Bounds (154089249 / 1000000000) (616357 / 4000000) (Real.log (233319 / 200000)) := by
  have h := reflection_log_10145_neg
  have he : Real.log (233319 / 200000) = -Real.log (200000 / 233319) := by
    rw [show ((233319 / 200000) : ℝ) = ((200000 / 233319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10146_neg : (4555889 / 25000000) ≤ -Real.log (166681 / 200000) ∧
    -Real.log (166681 / 200000) ≤ (182235561 / 1000000000) := by
  have h := checkLog_sound (w := (33319 / 366681)) (n := 12)
    (lo := (4555889 / 25000000)) (hi := (182235561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 166681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 166681) = 1/(166681 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10146 : Bounds (-182235561 / 1000000000) (-4555889 / 25000000) (Real.log (166681 / 200000)) := by
  have h := reflection_log_10146_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10147_neg : (154820169 / 1000000000) ≤ -Real.log (125000 / 145931) ∧
    -Real.log (125000 / 145931) ≤ (15482017 / 100000000) := by
  have h := checkLog_sound (w := (20931 / 270931)) (n := 12)
    (lo := (154820169 / 1000000000)) (hi := (15482017 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145931 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145931 / 125000) = 1/(125000 / 145931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10147 : Bounds (154820169 / 1000000000) (15482017 / 100000000) (Real.log (145931 / 125000)) := by
  have h := reflection_log_10147_neg
  have he : Real.log (145931 / 125000) = -Real.log (125000 / 145931) := by
    rw [show ((145931 / 125000) : ℝ) = ((125000 / 145931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10148_neg : (45814899 / 250000000) ≤ -Real.log (104069 / 125000) ∧
    -Real.log (104069 / 125000) ≤ (183259597 / 1000000000) := by
  have h := checkLog_sound (w := (20931 / 229069)) (n := 12)
    (lo := (45814899 / 250000000)) (hi := (183259597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 104069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 104069) = 1/(104069 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10148 : Bounds (-183259597 / 1000000000) (-45814899 / 250000000) (Real.log (104069 / 125000)) := by
  have h := reflection_log_10148_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10149_neg : (14219713 / 500000000) ≤ -Real.log (15186893239 / 15625000000) ∧
    -Real.log (15186893239 / 15625000000) ≤ (28439427 / 1000000000) := by
  have h := checkLog_sound (w := (438106761 / 30811893239)) (n := 12)
    (lo := (14219713 / 500000000)) (hi := (28439427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15186893239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15186893239) = 1/(15186893239 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10149 : Bounds (-28439427 / 1000000000) (-14219713 / 500000000) (Real.log (15186893239 / 15625000000)) := by
  have h := reflection_log_10149_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10150_neg : (28146311 / 1000000000) ≤ -Real.log (38889844239 / 40000000000) ∧
    -Real.log (38889844239 / 40000000000) ≤ (3518289 / 125000000) := by
  have h := checkLog_sound (w := (1110155761 / 78889844239)) (n := 12)
    (lo := (28146311 / 1000000000)) (hi := (3518289 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38889844239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38889844239) = 1/(38889844239 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10150 : Bounds (-3518289 / 125000000) (-28146311 / 1000000000) (Real.log (38889844239 / 40000000000)) := by
  have h := reflection_log_10150_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10151_neg : (336324809 / 1000000000) ≤ -Real.log (250000000000 / 349948404437) ∧
    -Real.log (250000000000 / 349948404437) ≤ (33632481 / 100000000) := by
  have h := checkLog_sound (w := (99948404437 / 599948404437)) (n := 12)
    (lo := (336324809 / 1000000000)) (hi := (33632481 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349948404437 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349948404437 / 250000000000) = 1/(250000000000 / 349948404437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10151 : Bounds (336324809 / 1000000000) (33632481 / 100000000) (Real.log (349948404437 / 250000000000)) := by
  have h := reflection_log_10151_neg
  have he : Real.log (349948404437 / 250000000000) = -Real.log (250000000000 / 349948404437) := by
    rw [show ((349948404437 / 250000000000) : ℝ) = ((250000000000 / 349948404437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10152_neg : (169039883 / 500000000) ≤ -Real.log (500000000000 / 701126175903) ∧
    -Real.log (500000000000 / 701126175903) ≤ (338079767 / 1000000000) := by
  have h := checkLog_sound (w := (201126175903 / 1201126175903)) (n := 12)
    (lo := (169039883 / 500000000)) (hi := (338079767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((701126175903 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(701126175903 / 500000000000) = 1/(500000000000 / 701126175903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10152 : Bounds (169039883 / 500000000) (338079767 / 1000000000) (Real.log (701126175903 / 500000000000)) := by
  have h := reflection_log_10152_neg
  have he : Real.log (701126175903 / 500000000000) = -Real.log (500000000000 / 701126175903) := by
    rw [show ((701126175903 / 500000000000) : ℝ) = ((500000000000 / 701126175903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10153_neg : (42433169 / 62500000) ≤ -Real.log (6250000000 / 12323551263) ∧
    -Real.log (6250000000 / 12323551263) ≤ (135786141 / 200000000) := by
  have h := checkLog_sound (w := (6073551263 / 18573551263)) (n := 12)
    (lo := (42433169 / 62500000)) (hi := (135786141 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12323551263 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12323551263 / 6250000000) = 1/(6250000000 / 12323551263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10153 : Bounds (42433169 / 62500000) (135786141 / 200000000) (Real.log (12323551263 / 6250000000)) := by
  have h := reflection_log_10153_neg
  have he : Real.log (12323551263 / 6250000000) = -Real.log (6250000000 / 12323551263) := by
    rw [show ((12323551263 / 6250000000) : ℝ) = ((6250000000 / 12323551263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10154_neg : (681170989 / 1000000000) ≤ -Real.log (31250000000 / 61755952381) ∧
    -Real.log (31250000000 / 61755952381) ≤ (68117099 / 100000000) := by
  have h := checkLog_sound (w := (30505952381 / 93005952381)) (n := 12)
    (lo := (681170989 / 1000000000)) (hi := (68117099 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61755952381 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61755952381 / 31250000000) = 1/(31250000000 / 61755952381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10154 : Bounds (681170989 / 1000000000) (68117099 / 100000000) (Real.log (61755952381 / 31250000000)) := by
  have h := reflection_log_10154_neg
  have he : Real.log (61755952381 / 31250000000) = -Real.log (31250000000 / 61755952381) := by
    rw [show ((61755952381 / 31250000000) : ℝ) = ((31250000000 / 61755952381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10155_neg : (284426779 / 1000000000) ≤ -Real.log (1000 / 1329) ∧
    -Real.log (1000 / 1329) ≤ (14221339 / 50000000) := by
  have h := checkLog_sound (w := (329 / 2329)) (n := 12)
    (lo := (284426779 / 1000000000)) (hi := (14221339 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1329 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1329 / 1000) = 1/(1000 / 1329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10155 : Bounds (284426779 / 1000000000) (14221339 / 50000000) (Real.log (1329 / 1000)) := by
  have h := reflection_log_10155_neg
  have he : Real.log (1329 / 1000) = -Real.log (1000 / 1329) := by
    rw [show ((1329 / 1000) : ℝ) = ((1000 / 1329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10156_neg : (199493071 / 500000000) ≤ -Real.log (671 / 1000) ∧
    -Real.log (671 / 1000) ≤ (398986143 / 1000000000) := by
  have h := checkLog_sound (w := (329 / 1671)) (n := 12)
    (lo := (199493071 / 500000000)) (hi := (398986143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 671) = 1/(671 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10156 : Bounds (-398986143 / 1000000000) (-199493071 / 500000000) (Real.log (671 / 1000)) := by
  have h := reflection_log_10156_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10157_neg : (65789 / 200000000) ≤ -Real.log (1000000 / 1000329) ∧
    -Real.log (1000000 / 1000329) ≤ (164473 / 500000000) := by
  have h := checkLog_sound (w := (329 / 2000329)) (n := 12)
    (lo := (65789 / 200000000)) (hi := (164473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000329 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000329 / 1000000) = 1/(1000000 / 1000329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10157 : Bounds (65789 / 200000000) (164473 / 500000000) (Real.log (1000329 / 1000000)) := by
  have h := reflection_log_10157_neg
  have he : Real.log (1000329 / 1000000) = -Real.log (1000000 / 1000329) := by
    rw [show ((1000329 / 1000000) : ℝ) = ((1000000 / 1000329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10158_neg : (164527 / 500000000) ≤ -Real.log (999671 / 1000000) ∧
    -Real.log (999671 / 1000000) ≤ (65811 / 200000000) := by
  have h := checkLog_sound (w := (329 / 1999671)) (n := 12)
    (lo := (164527 / 500000000)) (hi := (65811 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999671) = 1/(999671 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10158 : Bounds (-65811 / 200000000) (-164527 / 500000000) (Real.log (999671 / 1000000)) := by
  have h := reflection_log_10158_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10159_neg : (38636079 / 250000000) ≤ -Real.log (500000 / 583563) ∧
    -Real.log (500000 / 583563) ≤ (154544317 / 1000000000) := by
  have h := checkLog_sound (w := (83563 / 1083563)) (n := 12)
    (lo := (38636079 / 250000000)) (hi := (154544317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583563 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583563 / 500000) = 1/(500000 / 583563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10159 : Bounds (38636079 / 250000000) (154544317 / 1000000000) (Real.log (583563 / 500000)) := by
  have h := reflection_log_10159_neg
  have he : Real.log (583563 / 500000) = -Real.log (500000 / 583563) := by
    rw [show ((583563 / 500000) : ℝ) = ((500000 / 583563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10160_neg : (45718227 / 250000000) ≤ -Real.log (416437 / 500000) ∧
    -Real.log (416437 / 500000) ≤ (182872909 / 1000000000) := by
  have h := checkLog_sound (w := (83563 / 916437)) (n := 12)
    (lo := (45718227 / 250000000)) (hi := (182872909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 416437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 416437) = 1/(416437 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10160 : Bounds (-182872909 / 1000000000) (-45718227 / 250000000) (Real.log (416437 / 500000)) := by
  have h := reflection_log_10160_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10161_neg : (19409363 / 125000000) ≤ -Real.log (1000000 / 1167979) ∧
    -Real.log (1000000 / 1167979) ≤ (31054981 / 200000000) := by
  have h := checkLog_sound (w := (167979 / 2167979)) (n := 12)
    (lo := (19409363 / 125000000)) (hi := (31054981 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1167979 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1167979 / 1000000) = 1/(1000000 / 1167979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10161 : Bounds (19409363 / 125000000) (31054981 / 200000000) (Real.log (1167979 / 1000000)) := by
  have h := reflection_log_10161_neg
  have he : Real.log (1167979 / 1000000) = -Real.log (1000000 / 1167979) := by
    rw [show ((1167979 / 1000000) : ℝ) = ((1000000 / 1167979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10162_neg : (91948799 / 500000000) ≤ -Real.log (832021 / 1000000) ∧
    -Real.log (832021 / 1000000) ≤ (183897599 / 1000000000) := by
  have h := checkLog_sound (w := (167979 / 1832021)) (n := 12)
    (lo := (91948799 / 500000000)) (hi := (183897599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 832021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 832021) = 1/(832021 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10162 : Bounds (-183897599 / 1000000000) (-91948799 / 500000000) (Real.log (832021 / 1000000)) := by
  have h := reflection_log_10162_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10163_neg : (28622693 / 1000000000) ≤ -Real.log (971783055559 / 1000000000000) ∧
    -Real.log (971783055559 / 1000000000000) ≤ (14311347 / 500000000) := by
  have h := checkLog_sound (w := (28216944441 / 1971783055559)) (n := 12)
    (lo := (28622693 / 1000000000)) (hi := (14311347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 971783055559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 971783055559) = 1/(971783055559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10163 : Bounds (-14311347 / 500000000) (-28622693 / 1000000000) (Real.log (971783055559 / 1000000000000)) := by
  have h := reflection_log_10163_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10164_neg : (1770537 / 62500000) ≤ -Real.log (243017225031 / 250000000000) ∧
    -Real.log (243017225031 / 250000000000) ≤ (28328593 / 1000000000) := by
  have h := checkLog_sound (w := (6982774969 / 493017225031)) (n := 12)
    (lo := (1770537 / 62500000)) (hi := (28328593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243017225031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243017225031) = 1/(243017225031 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10164 : Bounds (-28328593 / 1000000000) (-1770537 / 62500000) (Real.log (243017225031 / 250000000000)) := by
  have h := reflection_log_10164_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10165_neg : (13496689 / 40000000) ≤ -Real.log (250000000000 / 350330902393) ∧
    -Real.log (250000000000 / 350330902393) ≤ (168708613 / 500000000) := by
  have h := checkLog_sound (w := (100330902393 / 600330902393)) (n := 12)
    (lo := (13496689 / 40000000)) (hi := (168708613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((350330902393 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(350330902393 / 250000000000) = 1/(250000000000 / 350330902393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10165 : Bounds (13496689 / 40000000) (168708613 / 500000000) (Real.log (350330902393 / 250000000000)) := by
  have h := reflection_log_10165_neg
  have he : Real.log (350330902393 / 250000000000) = -Real.log (250000000000 / 350330902393) := by
    rw [show ((350330902393 / 250000000000) : ℝ) = ((250000000000 / 350330902393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10166_neg : (169586251 / 500000000) ≤ -Real.log (500000000000 / 701892740689) ∧
    -Real.log (500000000000 / 701892740689) ≤ (339172503 / 1000000000) := by
  have h := checkLog_sound (w := (201892740689 / 1201892740689)) (n := 12)
    (lo := (169586251 / 500000000)) (hi := (339172503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((701892740689 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(701892740689 / 500000000000) = 1/(500000000000 / 701892740689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10166 : Bounds (169586251 / 500000000) (339172503 / 1000000000) (Real.log (701892740689 / 500000000000)) := by
  have h := reflection_log_10166_neg
  have he : Real.log (701892740689 / 500000000000) = -Real.log (500000000000 / 701892740689) := by
    rw [show ((701892740689 / 500000000000) : ℝ) = ((500000000000 / 701892740689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10167_neg : (681170989 / 1000000000) ≤ -Real.log (100000000000 / 197619047619) ∧
    -Real.log (100000000000 / 197619047619) ≤ (68117099 / 100000000) := by
  have h := checkLog_sound (w := (97619047619 / 297619047619)) (n := 12)
    (lo := (681170989 / 1000000000)) (hi := (68117099 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197619047619 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197619047619 / 100000000000) = 1/(100000000000 / 197619047619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10167 : Bounds (681170989 / 1000000000) (68117099 / 100000000) (Real.log (197619047619 / 100000000000)) := by
  have h := reflection_log_10167_neg
  have he : Real.log (197619047619 / 100000000000) = -Real.log (100000000000 / 197619047619) := by
    rw [show ((197619047619 / 100000000000) : ℝ) = ((100000000000 / 197619047619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10168_neg : (683412921 / 1000000000) ≤ -Real.log (500000000000 / 990312965723) ∧
    -Real.log (500000000000 / 990312965723) ≤ (341706461 / 500000000) := by
  have h := checkLog_sound (w := (490312965723 / 1490312965723)) (n := 12)
    (lo := (683412921 / 1000000000)) (hi := (341706461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990312965723 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990312965723 / 500000000000) = 1/(500000000000 / 990312965723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10168 : Bounds (683412921 / 1000000000) (341706461 / 500000000) (Real.log (990312965723 / 500000000000)) := by
  have h := reflection_log_10168_neg
  have he : Real.log (990312965723 / 500000000000) = -Real.log (500000000000 / 990312965723) := by
    rw [show ((990312965723 / 500000000000) : ℝ) = ((500000000000 / 990312965723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10169_neg : (142589471 / 500000000) ≤ -Real.log (100 / 133) ∧
    -Real.log (100 / 133) ≤ (285178943 / 1000000000) := by
  have h := checkLog_sound (w := (33 / 233)) (n := 12)
    (lo := (142589471 / 500000000)) (hi := (285178943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133 / 100) = 1/(100 / 133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10169 : Bounds (142589471 / 500000000) (285178943 / 1000000000) (Real.log (133 / 100)) := by
  have h := reflection_log_10169_neg
  have he : Real.log (133 / 100) = -Real.log (100 / 133) := by
    rw [show ((133 / 100) : ℝ) = ((100 / 133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10170_neg : (200238783 / 500000000) ≤ -Real.log (67 / 100) ∧
    -Real.log (67 / 100) ≤ (400477567 / 1000000000) := by
  have h := checkLog_sound (w := (33 / 167)) (n := 12)
    (lo := (200238783 / 500000000)) (hi := (400477567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 67) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 67) = 1/(67 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10170 : Bounds (-400477567 / 1000000000) (-200238783 / 500000000) (Real.log (67 / 100)) := by
  have h := reflection_log_10170_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10171_neg : (65989 / 200000000) ≤ -Real.log (100000 / 100033) ∧
    -Real.log (100000 / 100033) ≤ (164973 / 500000000) := by
  have h := checkLog_sound (w := (33 / 200033)) (n := 12)
    (lo := (65989 / 200000000)) (hi := (164973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100033 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100033 / 100000) = 1/(100000 / 100033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10171 : Bounds (65989 / 200000000) (164973 / 500000000) (Real.log (100033 / 100000)) := by
  have h := reflection_log_10171_neg
  have he : Real.log (100033 / 100000) = -Real.log (100000 / 100033) := by
    rw [show ((100033 / 100000) : ℝ) = ((100000 / 100033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10172_neg : (165027 / 500000000) ≤ -Real.log (99967 / 100000) ∧
    -Real.log (99967 / 100000) ≤ (66011 / 200000000) := by
  have h := checkLog_sound (w := (33 / 199967)) (n := 12)
    (lo := (165027 / 500000000)) (hi := (66011 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99967) = 1/(99967 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10172 : Bounds (-66011 / 200000000) (-165027 / 500000000) (Real.log (99967 / 100000)) := by
  have h := reflection_log_10172_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10173_neg : (1937479 / 12500000) ≤ -Real.log (125000 / 145957) ∧
    -Real.log (125000 / 145957) ≤ (154998321 / 1000000000) := by
  have h := checkLog_sound (w := (20957 / 270957)) (n := 12)
    (lo := (1937479 / 12500000)) (hi := (154998321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145957 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145957 / 125000) = 1/(125000 / 145957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10173 : Bounds (1937479 / 12500000) (154998321 / 1000000000) (Real.log (145957 / 125000)) := by
  have h := reflection_log_10173_neg
  have he : Real.log (145957 / 125000) = -Real.log (125000 / 145957) := by
    rw [show ((145957 / 125000) : ℝ) = ((125000 / 145957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10174_neg : (91754731 / 500000000) ≤ -Real.log (104043 / 125000) ∧
    -Real.log (104043 / 125000) ≤ (183509463 / 1000000000) := by
  have h := checkLog_sound (w := (20957 / 229043)) (n := 12)
    (lo := (91754731 / 500000000)) (hi := (183509463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 104043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 104043) = 1/(104043 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10174 : Bounds (-183509463 / 1000000000) (-91754731 / 500000000) (Real.log (104043 / 125000)) := by
  have h := reflection_log_10174_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10175_neg : (9733143 / 62500000) ≤ -Real.log (1000000 / 1168511) ∧
    -Real.log (1000000 / 1168511) ≤ (155730289 / 1000000000) := by
  have h := checkLog_sound (w := (168511 / 2168511)) (n := 12)
    (lo := (9733143 / 62500000)) (hi := (155730289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1168511 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1168511 / 1000000) = 1/(1000000 / 1168511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10175 : Bounds (9733143 / 62500000) (155730289 / 1000000000) (Real.log (1168511 / 1000000)) := by
  have h := reflection_log_10175_neg
  have he : Real.log (1168511 / 1000000) = -Real.log (1000000 / 1168511) := by
    rw [show ((1168511 / 1000000) : ℝ) = ((1000000 / 1168511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0159 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10176_neg : (184537209 / 1000000000) ≤ -Real.log (831489 / 1000000) ∧
    -Real.log (831489 / 1000000) ≤ (18453721 / 100000000) := by
  have h := checkLog_sound (w := (168511 / 1831489)) (n := 12)
    (lo := (184537209 / 1000000000)) (hi := (18453721 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 831489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 831489) = 1/(831489 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10176 : Bounds (-18453721 / 100000000) (-184537209 / 1000000000) (Real.log (831489 / 1000000)) := by
  have h := reflection_log_10176_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10177_neg : (720173 / 25000000) ≤ -Real.log (971604042879 / 1000000000000) ∧
    -Real.log (971604042879 / 1000000000000) ≤ (28806921 / 1000000000) := by
  have h := checkLog_sound (w := (28395957121 / 1971604042879)) (n := 12)
    (lo := (720173 / 25000000)) (hi := (28806921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 971604042879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 971604042879) = 1/(971604042879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10177 : Bounds (-28806921 / 1000000000) (-720173 / 25000000) (Real.log (971604042879 / 1000000000000)) := by
  have h := reflection_log_10177_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10178_neg : (28511141 / 1000000000) ≤ -Real.log (15185804151 / 15625000000) ∧
    -Real.log (15185804151 / 15625000000) ≤ (14255571 / 500000000) := by
  have h := checkLog_sound (w := (439195849 / 30810804151)) (n := 12)
    (lo := (28511141 / 1000000000)) (hi := (14255571 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15185804151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15185804151) = 1/(15185804151 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10178 : Bounds (-14255571 / 500000000) (-28511141 / 1000000000) (Real.log (15185804151 / 15625000000)) := by
  have h := reflection_log_10178_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10179_neg : (169253891 / 500000000) ≤ -Real.log (250000000000 / 350713166671) ∧
    -Real.log (250000000000 / 350713166671) ≤ (338507783 / 1000000000) := by
  have h := checkLog_sound (w := (100713166671 / 600713166671)) (n := 12)
    (lo := (169253891 / 500000000)) (hi := (338507783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((350713166671 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(350713166671 / 250000000000) = 1/(250000000000 / 350713166671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10179 : Bounds (169253891 / 500000000) (338507783 / 1000000000) (Real.log (350713166671 / 250000000000)) := by
  have h := reflection_log_10179_neg
  have he : Real.log (350713166671 / 250000000000) = -Real.log (250000000000 / 350713166671) := by
    rw [show ((350713166671 / 250000000000) : ℝ) = ((250000000000 / 350713166671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10180_neg : (170133749 / 500000000) ≤ -Real.log (500000000000 / 702661730943) ∧
    -Real.log (500000000000 / 702661730943) ≤ (340267499 / 1000000000) := by
  have h := checkLog_sound (w := (202661730943 / 1202661730943)) (n := 12)
    (lo := (170133749 / 500000000)) (hi := (340267499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((702661730943 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(702661730943 / 500000000000) = 1/(500000000000 / 702661730943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10180 : Bounds (170133749 / 500000000) (340267499 / 1000000000) (Real.log (702661730943 / 500000000000)) := by
  have h := reflection_log_10180_neg
  have he : Real.log (702661730943 / 500000000000) = -Real.log (500000000000 / 702661730943) := by
    rw [show ((702661730943 / 500000000000) : ℝ) = ((500000000000 / 702661730943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10181_neg : (683412921 / 1000000000) ≤ -Real.log (250000000000 / 495156482861) ∧
    -Real.log (250000000000 / 495156482861) ≤ (341706461 / 500000000) := by
  have h := checkLog_sound (w := (245156482861 / 745156482861)) (n := 12)
    (lo := (683412921 / 1000000000)) (hi := (341706461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((495156482861 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(495156482861 / 250000000000) = 1/(250000000000 / 495156482861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10181 : Bounds (683412921 / 1000000000) (341706461 / 500000000) (Real.log (495156482861 / 250000000000)) := by
  have h := reflection_log_10181_neg
  have he : Real.log (495156482861 / 250000000000) = -Real.log (250000000000 / 495156482861) := by
    rw [show ((495156482861 / 250000000000) : ℝ) = ((250000000000 / 495156482861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10182_neg : (171414127 / 250000000) ≤ -Real.log (500000000000 / 992537313433) ∧
    -Real.log (500000000000 / 992537313433) ≤ (685656509 / 1000000000) := by
  have h := checkLog_sound (w := (492537313433 / 1492537313433)) (n := 12)
    (lo := (171414127 / 250000000)) (hi := (685656509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((992537313433 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(992537313433 / 500000000000) = 1/(500000000000 / 992537313433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10182 : Bounds (171414127 / 250000000) (685656509 / 1000000000) (Real.log (992537313433 / 500000000000)) := by
  have h := reflection_log_10182_neg
  have he : Real.log (992537313433 / 500000000000) = -Real.log (500000000000 / 992537313433) := by
    rw [show ((992537313433 / 500000000000) : ℝ) = ((500000000000 / 992537313433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10183_neg : (285930539 / 1000000000) ≤ -Real.log (1000 / 1331) ∧
    -Real.log (1000 / 1331) ≤ (14296527 / 50000000) := by
  have h := checkLog_sound (w := (331 / 2331)) (n := 12)
    (lo := (285930539 / 1000000000)) (hi := (14296527 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1331 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1331 / 1000) = 1/(1000 / 1331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10183 : Bounds (285930539 / 1000000000) (14296527 / 50000000) (Real.log (1331 / 1000)) := by
  have h := reflection_log_10183_neg
  have he : Real.log (1331 / 1000) = -Real.log (1000 / 1331) := by
    rw [show ((1331 / 1000) : ℝ) = ((1000 / 1331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10184_neg : (200985609 / 500000000) ≤ -Real.log (669 / 1000) ∧
    -Real.log (669 / 1000) ≤ (401971219 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 1669)) (n := 12)
    (lo := (200985609 / 500000000)) (hi := (401971219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 669) = 1/(669 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10184 : Bounds (-401971219 / 1000000000) (-200985609 / 500000000) (Real.log (669 / 1000)) := by
  have h := reflection_log_10184_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10185_neg : (66189 / 200000000) ≤ -Real.log (1000000 / 1000331) ∧
    -Real.log (1000000 / 1000331) ≤ (165473 / 500000000) := by
  have h := checkLog_sound (w := (331 / 2000331)) (n := 12)
    (lo := (66189 / 200000000)) (hi := (165473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000331 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000331 / 1000000) = 1/(1000000 / 1000331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10185 : Bounds (66189 / 200000000) (165473 / 500000000) (Real.log (1000331 / 1000000)) := by
  have h := reflection_log_10185_neg
  have he : Real.log (1000331 / 1000000) = -Real.log (1000000 / 1000331) := by
    rw [show ((1000331 / 1000000) : ℝ) = ((1000000 / 1000331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10186_neg : (165527 / 500000000) ≤ -Real.log (999669 / 1000000) ∧
    -Real.log (999669 / 1000000) ≤ (66211 / 200000000) := by
  have h := checkLog_sound (w := (331 / 1999669)) (n := 12)
    (lo := (165527 / 500000000)) (hi := (66211 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999669) = 1/(999669 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10186 : Bounds (-66211 / 200000000) (-165527 / 500000000) (Real.log (999669 / 1000000)) := by
  have h := reflection_log_10186_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10187_neg : (77726059 / 500000000) ≤ -Real.log (500000 / 584093) ∧
    -Real.log (500000 / 584093) ≤ (155452119 / 1000000000) := by
  have h := checkLog_sound (w := (84093 / 1084093)) (n := 12)
    (lo := (77726059 / 500000000)) (hi := (155452119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584093 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584093 / 500000) = 1/(500000 / 584093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10187 : Bounds (77726059 / 500000000) (155452119 / 1000000000) (Real.log (584093 / 500000)) := by
  have h := reflection_log_10187_neg
  have he : Real.log (584093 / 500000) = -Real.log (500000 / 584093) := by
    rw [show ((584093 / 500000) : ℝ) = ((500000 / 584093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10188_neg : (9207321 / 50000000) ≤ -Real.log (415907 / 500000) ∧
    -Real.log (415907 / 500000) ≤ (184146421 / 1000000000) := by
  have h := checkLog_sound (w := (84093 / 915907)) (n := 12)
    (lo := (9207321 / 50000000)) (hi := (184146421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 415907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 415907) = 1/(415907 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10188 : Bounds (-184146421 / 1000000000) (-9207321 / 50000000) (Real.log (415907 / 500000)) := by
  have h := reflection_log_10188_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10189_neg : (156184609 / 1000000000) ≤ -Real.log (500000 / 584521) ∧
    -Real.log (500000 / 584521) ≤ (15618461 / 100000000) := by
  have h := checkLog_sound (w := (84521 / 1084521)) (n := 12)
    (lo := (156184609 / 1000000000)) (hi := (15618461 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584521 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584521 / 500000) = 1/(500000 / 584521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10189 : Bounds (156184609 / 1000000000) (15618461 / 100000000) (Real.log (584521 / 500000)) := by
  have h := reflection_log_10189_neg
  have he : Real.log (584521 / 500000) = -Real.log (500000 / 584521) := by
    rw [show ((584521 / 500000) : ℝ) = ((500000 / 584521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10190_neg : (92588013 / 500000000) ≤ -Real.log (415479 / 500000) ∧
    -Real.log (415479 / 500000) ≤ (185176027 / 1000000000) := by
  have h := checkLog_sound (w := (84521 / 915479)) (n := 12)
    (lo := (92588013 / 500000000)) (hi := (185176027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 415479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 415479) = 1/(415479 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10190 : Bounds (-185176027 / 1000000000) (-92588013 / 500000000) (Real.log (415479 / 500000)) := by
  have h := reflection_log_10190_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10191_neg : (3623927 / 125000000) ≤ -Real.log (242856200559 / 250000000000) ∧
    -Real.log (242856200559 / 250000000000) ≤ (28991417 / 1000000000) := by
  have h := checkLog_sound (w := (7143799441 / 492856200559)) (n := 12)
    (lo := (3623927 / 125000000)) (hi := (28991417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242856200559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242856200559) = 1/(242856200559 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10191 : Bounds (-28991417 / 1000000000) (-3623927 / 125000000) (Real.log (242856200559 / 250000000000)) := by
  have h := reflection_log_10191_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10192_neg : (14347151 / 500000000) ≤ -Real.log (242928367351 / 250000000000) ∧
    -Real.log (242928367351 / 250000000000) ≤ (28694303 / 1000000000) := by
  have h := checkLog_sound (w := (7071632649 / 492928367351)) (n := 12)
    (lo := (14347151 / 500000000)) (hi := (28694303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242928367351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242928367351) = 1/(242928367351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10192 : Bounds (-28694303 / 1000000000) (-14347151 / 500000000) (Real.log (242928367351 / 250000000000)) := by
  have h := reflection_log_10192_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10193_neg : (339598539 / 1000000000) ≤ -Real.log (100000000000 / 140438367231) ∧
    -Real.log (100000000000 / 140438367231) ≤ (16979927 / 50000000) := by
  have h := checkLog_sound (w := (40438367231 / 240438367231)) (n := 12)
    (lo := (339598539 / 1000000000)) (hi := (16979927 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140438367231 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140438367231 / 100000000000) = 1/(100000000000 / 140438367231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10193 : Bounds (339598539 / 1000000000) (16979927 / 50000000) (Real.log (140438367231 / 100000000000)) := by
  have h := reflection_log_10193_neg
  have he : Real.log (140438367231 / 100000000000) = -Real.log (100000000000 / 140438367231) := by
    rw [show ((140438367231 / 100000000000) : ℝ) = ((100000000000 / 140438367231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10194_neg : (85340159 / 250000000) ≤ -Real.log (500000000000 / 703430257607) ∧
    -Real.log (500000000000 / 703430257607) ≤ (341360637 / 1000000000) := by
  have h := checkLog_sound (w := (203430257607 / 1203430257607)) (n := 12)
    (lo := (85340159 / 250000000)) (hi := (341360637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703430257607 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703430257607 / 500000000000) = 1/(500000000000 / 703430257607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10194 : Bounds (85340159 / 250000000) (341360637 / 1000000000) (Real.log (703430257607 / 500000000000)) := by
  have h := reflection_log_10194_neg
  have he : Real.log (703430257607 / 500000000000) = -Real.log (500000000000 / 703430257607) := by
    rw [show ((703430257607 / 500000000000) : ℝ) = ((500000000000 / 703430257607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10195_neg : (171414127 / 250000000) ≤ -Real.log (62500000000 / 124067164179) ∧
    -Real.log (62500000000 / 124067164179) ≤ (685656509 / 1000000000) := by
  have h := checkLog_sound (w := (61567164179 / 186567164179)) (n := 12)
    (lo := (171414127 / 250000000)) (hi := (685656509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((124067164179 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(124067164179 / 62500000000) = 1/(62500000000 / 124067164179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10195 : Bounds (171414127 / 250000000) (685656509 / 1000000000) (Real.log (124067164179 / 62500000000)) := by
  have h := reflection_log_10195_neg
  have he : Real.log (124067164179 / 62500000000) = -Real.log (62500000000 / 124067164179) := by
    rw [show ((124067164179 / 62500000000) : ℝ) = ((62500000000 / 124067164179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10196_neg : (343950879 / 500000000) ≤ -Real.log (3906250000 / 7771627429) ∧
    -Real.log (3906250000 / 7771627429) ≤ (687901759 / 1000000000) := by
  have h := checkLog_sound (w := (3865377429 / 11677877429)) (n := 12)
    (lo := (343950879 / 500000000)) (hi := (687901759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7771627429 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7771627429 / 3906250000) = 1/(3906250000 / 7771627429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10196 : Bounds (343950879 / 500000000) (687901759 / 1000000000) (Real.log (7771627429 / 3906250000)) := by
  have h := reflection_log_10196_neg
  have he : Real.log (7771627429 / 3906250000) = -Real.log (3906250000 / 7771627429) := by
    rw [show ((7771627429 / 3906250000) : ℝ) = ((3906250000 / 7771627429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10197_neg : (71670393 / 250000000) ≤ -Real.log (250 / 333) ∧
    -Real.log (250 / 333) ≤ (286681573 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 583)) (n := 12)
    (lo := (71670393 / 250000000)) (hi := (286681573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((333 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(333 / 250) = 1/(250 / 333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10197 : Bounds (71670393 / 250000000) (286681573 / 1000000000) (Real.log (333 / 250)) := by
  have h := reflection_log_10197_neg
  have he : Real.log (333 / 250) = -Real.log (250 / 333) := by
    rw [show ((333 / 250) : ℝ) = ((250 / 333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10198_neg : (80693421 / 200000000) ≤ -Real.log (167 / 250) ∧
    -Real.log (167 / 250) ≤ (201733553 / 500000000) := by
  have h := checkLog_sound (w := (83 / 417)) (n := 12)
    (lo := (80693421 / 200000000)) (hi := (201733553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 167) = 1/(167 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10198 : Bounds (-201733553 / 500000000) (-80693421 / 200000000) (Real.log (167 / 250)) := by
  have h := reflection_log_10198_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10199_neg : (41493 / 125000000) ≤ -Real.log (250000 / 250083) ∧
    -Real.log (250000 / 250083) ≤ (66389 / 200000000) := by
  have h := checkLog_sound (w := (83 / 500083)) (n := 12)
    (lo := (41493 / 125000000)) (hi := (66389 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250083 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250083 / 250000) = 1/(250000 / 250083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10199 : Bounds (41493 / 125000000) (66389 / 200000000) (Real.log (250083 / 250000)) := by
  have h := reflection_log_10199_neg
  have he : Real.log (250083 / 250000) = -Real.log (250000 / 250083) := by
    rw [show ((250083 / 250000) : ℝ) = ((250000 / 250083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10200_neg : (66411 / 200000000) ≤ -Real.log (249917 / 250000) ∧
    -Real.log (249917 / 250000) ≤ (41507 / 125000000) := by
  have h := checkLog_sound (w := (83 / 499917)) (n := 12)
    (lo := (66411 / 200000000)) (hi := (41507 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249917) = 1/(249917 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10200 : Bounds (-41507 / 125000000) (-66411 / 200000000) (Real.log (249917 / 250000)) := by
  have h := reflection_log_10200_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10201_neg : (31181313 / 200000000) ≤ -Real.log (1000000 / 1168717) ∧
    -Real.log (1000000 / 1168717) ≤ (77953283 / 500000000) := by
  have h := checkLog_sound (w := (168717 / 2168717)) (n := 12)
    (lo := (31181313 / 200000000)) (hi := (77953283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1168717 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1168717 / 1000000) = 1/(1000000 / 1168717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10201 : Bounds (31181313 / 200000000) (77953283 / 500000000) (Real.log (1168717 / 1000000)) := by
  have h := reflection_log_10201_neg
  have he : Real.log (1168717 / 1000000) = -Real.log (1000000 / 1168717) := by
    rw [show ((1168717 / 1000000) : ℝ) = ((1000000 / 1168717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10202_neg : (46196247 / 250000000) ≤ -Real.log (831283 / 1000000) ∧
    -Real.log (831283 / 1000000) ≤ (184784989 / 1000000000) := by
  have h := checkLog_sound (w := (168717 / 1831283)) (n := 12)
    (lo := (46196247 / 250000000)) (hi := (184784989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 831283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 831283) = 1/(831283 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10202 : Bounds (-184784989 / 1000000000) (-46196247 / 250000000) (Real.log (831283 / 1000000)) := by
  have h := reflection_log_10202_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10203_neg : (156639579 / 1000000000) ≤ -Real.log (500000 / 584787) ∧
    -Real.log (500000 / 584787) ≤ (7831979 / 50000000) := by
  have h := checkLog_sound (w := (84787 / 1084787)) (n := 12)
    (lo := (156639579 / 1000000000)) (hi := (7831979 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584787 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584787 / 500000) = 1/(500000 / 584787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10203 : Bounds (156639579 / 1000000000) (7831979 / 50000000) (Real.log (584787 / 500000)) := by
  have h := reflection_log_10203_neg
  have he : Real.log (584787 / 500000) = -Real.log (500000 / 584787) := by
    rw [show ((584787 / 500000) : ℝ) = ((500000 / 584787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10204_neg : (23227057 / 125000000) ≤ -Real.log (415213 / 500000) ∧
    -Real.log (415213 / 500000) ≤ (185816457 / 1000000000) := by
  have h := checkLog_sound (w := (84787 / 915213)) (n := 12)
    (lo := (23227057 / 125000000)) (hi := (185816457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 415213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 415213) = 1/(415213 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10204 : Bounds (-185816457 / 1000000000) (-23227057 / 125000000) (Real.log (415213 / 500000)) := by
  have h := reflection_log_10204_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10205_neg : (7294219 / 250000000) ≤ -Real.log (242811164631 / 250000000000) ∧
    -Real.log (242811164631 / 250000000000) ≤ (29176877 / 1000000000) := by
  have h := checkLog_sound (w := (7188835369 / 492811164631)) (n := 12)
    (lo := (7294219 / 250000000)) (hi := (29176877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242811164631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242811164631) = 1/(242811164631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10205 : Bounds (-29176877 / 1000000000) (-7294219 / 250000000) (Real.log (242811164631 / 250000000000)) := by
  have h := reflection_log_10205_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10206_neg : (14439211 / 500000000) ≤ -Real.log (971534573911 / 1000000000000) ∧
    -Real.log (971534573911 / 1000000000000) ≤ (28878423 / 1000000000) := by
  have h := checkLog_sound (w := (28465426089 / 1971534573911)) (n := 12)
    (lo := (14439211 / 500000000)) (hi := (28878423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 971534573911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 971534573911) = 1/(971534573911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10206 : Bounds (-28878423 / 1000000000) (-14439211 / 500000000) (Real.log (971534573911 / 1000000000000)) := by
  have h := reflection_log_10206_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10207_neg : (170345777 / 500000000) ≤ -Real.log (250000000000 / 351479881099) ∧
    -Real.log (250000000000 / 351479881099) ≤ (68138311 / 200000000) := by
  have h := checkLog_sound (w := (101479881099 / 601479881099)) (n := 12)
    (lo := (170345777 / 500000000)) (hi := (68138311 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351479881099 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351479881099 / 250000000000) = 1/(250000000000 / 351479881099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10207 : Bounds (170345777 / 500000000) (68138311 / 200000000) (Real.log (351479881099 / 250000000000)) := by
  have h := reflection_log_10207_neg
  have he : Real.log (351479881099 / 250000000000) = -Real.log (250000000000 / 351479881099) := by
    rw [show ((351479881099 / 250000000000) : ℝ) = ((250000000000 / 351479881099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10208_neg : (85614009 / 250000000) ≤ -Real.log (500000000000 / 704201217207) ∧
    -Real.log (500000000000 / 704201217207) ≤ (342456037 / 1000000000) := by
  have h := checkLog_sound (w := (204201217207 / 1204201217207)) (n := 12)
    (lo := (85614009 / 250000000)) (hi := (342456037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704201217207 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(704201217207 / 500000000000) = 1/(500000000000 / 704201217207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10208 : Bounds (85614009 / 250000000) (342456037 / 1000000000) (Real.log (704201217207 / 500000000000)) := by
  have h := reflection_log_10208_neg
  have he : Real.log (704201217207 / 500000000000) = -Real.log (500000000000 / 704201217207) := by
    rw [show ((704201217207 / 500000000000) : ℝ) = ((500000000000 / 704201217207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10209_neg : (343950879 / 500000000) ≤ -Real.log (500000000000 / 994768310911) ∧
    -Real.log (500000000000 / 994768310911) ≤ (687901759 / 1000000000) := by
  have h := checkLog_sound (w := (494768310911 / 1494768310911)) (n := 12)
    (lo := (343950879 / 500000000)) (hi := (687901759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((994768310911 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(994768310911 / 500000000000) = 1/(500000000000 / 994768310911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10209 : Bounds (343950879 / 500000000) (687901759 / 1000000000) (Real.log (994768310911 / 500000000000)) := by
  have h := reflection_log_10209_neg
  have he : Real.log (994768310911 / 500000000000) = -Real.log (500000000000 / 994768310911) := by
    rw [show ((994768310911 / 500000000000) : ℝ) = ((500000000000 / 994768310911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10210_neg : (690148677 / 1000000000) ≤ -Real.log (62500000000 / 124625748503) ∧
    -Real.log (62500000000 / 124625748503) ≤ (345074339 / 500000000) := by
  have h := checkLog_sound (w := (62125748503 / 187125748503)) (n := 12)
    (lo := (690148677 / 1000000000)) (hi := (345074339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((124625748503 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(124625748503 / 62500000000) = 1/(62500000000 / 124625748503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10210 : Bounds (690148677 / 1000000000) (345074339 / 500000000) (Real.log (124625748503 / 62500000000)) := by
  have h := reflection_log_10210_neg
  have he : Real.log (124625748503 / 62500000000) = -Real.log (62500000000 / 124625748503) := by
    rw [show ((124625748503 / 62500000000) : ℝ) = ((62500000000 / 124625748503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10211_neg : (287432041 / 1000000000) ≤ -Real.log (1000 / 1333) ∧
    -Real.log (1000 / 1333) ≤ (143716021 / 500000000) := by
  have h := checkLog_sound (w := (333 / 2333)) (n := 12)
    (lo := (287432041 / 1000000000)) (hi := (143716021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1333 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1333 / 1000) = 1/(1000 / 1333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10211 : Bounds (287432041 / 1000000000) (143716021 / 500000000) (Real.log (1333 / 1000)) := by
  have h := reflection_log_10211_neg
  have he : Real.log (1333 / 1000) = -Real.log (1000 / 1333) := by
    rw [show ((1333 / 1000) : ℝ) = ((1000 / 1333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10212_neg : (404965233 / 1000000000) ≤ -Real.log (667 / 1000) ∧
    -Real.log (667 / 1000) ≤ (202482617 / 500000000) := by
  have h := checkLog_sound (w := (333 / 1667)) (n := 12)
    (lo := (404965233 / 1000000000)) (hi := (202482617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 667) = 1/(667 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10212 : Bounds (-202482617 / 500000000) (-404965233 / 1000000000) (Real.log (667 / 1000)) := by
  have h := reflection_log_10212_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10213_neg : (20809 / 62500000) ≤ -Real.log (1000000 / 1000333) ∧
    -Real.log (1000000 / 1000333) ≤ (66589 / 200000000) := by
  have h := checkLog_sound (w := (333 / 2000333)) (n := 12)
    (lo := (20809 / 62500000)) (hi := (66589 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000333 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000333 / 1000000) = 1/(1000000 / 1000333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10213 : Bounds (20809 / 62500000) (66589 / 200000000) (Real.log (1000333 / 1000000)) := by
  have h := reflection_log_10213_neg
  have he : Real.log (1000333 / 1000000) = -Real.log (1000000 / 1000333) := by
    rw [show ((1000333 / 1000000) : ℝ) = ((1000000 / 1000333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10214_neg : (66611 / 200000000) ≤ -Real.log (999667 / 1000000) ∧
    -Real.log (999667 / 1000000) ≤ (1301 / 3906250) := by
  have h := checkLog_sound (w := (333 / 1999667)) (n := 12)
    (lo := (66611 / 200000000)) (hi := (1301 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999667) = 1/(999667 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10214 : Bounds (-1301 / 3906250) (-66611 / 200000000) (Real.log (999667 / 1000000)) := by
  have h := reflection_log_10214_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10215_neg : (156360807 / 1000000000) ≤ -Real.log (31250 / 36539) ∧
    -Real.log (31250 / 36539) ≤ (19545101 / 125000000) := by
  have h := checkLog_sound (w := (5289 / 67789)) (n := 12)
    (lo := (156360807 / 1000000000)) (hi := (19545101 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36539 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36539 / 31250) = 1/(31250 / 36539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10215 : Bounds (156360807 / 1000000000) (19545101 / 125000000) (Real.log (36539 / 31250)) := by
  have h := reflection_log_10215_neg
  have he : Real.log (36539 / 31250) = -Real.log (31250 / 36539) := by
    rw [show ((36539 / 31250) : ℝ) = ((31250 / 36539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10216_neg : (46355991 / 250000000) ≤ -Real.log (25961 / 31250) ∧
    -Real.log (25961 / 31250) ≤ (37084793 / 200000000) := by
  have h := checkLog_sound (w := (5289 / 57211)) (n := 12)
    (lo := (46355991 / 250000000)) (hi := (37084793 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 25961) = 1/(25961 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10216 : Bounds (-37084793 / 200000000) (-46355991 / 250000000) (Real.log (25961 / 31250)) := by
  have h := reflection_log_10216_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10217_neg : (78547171 / 500000000) ≤ -Real.log (500000 / 585053) ∧
    -Real.log (500000 / 585053) ≤ (157094343 / 1000000000) := by
  have h := checkLog_sound (w := (85053 / 1085053)) (n := 12)
    (lo := (78547171 / 500000000)) (hi := (157094343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585053 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585053 / 500000) = 1/(500000 / 585053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10217 : Bounds (78547171 / 500000000) (157094343 / 1000000000) (Real.log (585053 / 500000)) := by
  have h := reflection_log_10217_neg
  have he : Real.log (585053 / 500000) = -Real.log (500000 / 585053) := by
    rw [show ((585053 / 500000) : ℝ) = ((500000 / 585053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10218_neg : (186457297 / 1000000000) ≤ -Real.log (414947 / 500000) ∧
    -Real.log (414947 / 500000) ≤ (93228649 / 500000000) := by
  have h := checkLog_sound (w := (85053 / 914947)) (n := 12)
    (lo := (186457297 / 1000000000)) (hi := (93228649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 414947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 414947) = 1/(414947 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10218 : Bounds (-93228649 / 500000000) (-186457297 / 1000000000) (Real.log (414947 / 500000)) := by
  have h := reflection_log_10218_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10219_neg : (14681477 / 500000000) ≤ -Real.log (242765987191 / 250000000000) ∧
    -Real.log (242765987191 / 250000000000) ≤ (5872591 / 200000000) := by
  have h := checkLog_sound (w := (7234012809 / 492765987191)) (n := 12)
    (lo := (14681477 / 500000000)) (hi := (5872591 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242765987191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242765987191) = 1/(242765987191 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10219 : Bounds (-5872591 / 200000000) (-14681477 / 500000000) (Real.log (242765987191 / 250000000000)) := by
  have h := reflection_log_10219_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10220_neg : (29063157 / 1000000000) ≤ -Real.log (948588979 / 976562500) ∧
    -Real.log (948588979 / 976562500) ≤ (14531579 / 500000000) := by
  have h := checkLog_sound (w := (27973521 / 1925151479)) (n := 12)
    (lo := (29063157 / 1000000000)) (hi := (14531579 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 948588979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 948588979) = 1/(948588979 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10220 : Bounds (-14531579 / 500000000) (-29063157 / 1000000000) (Real.log (948588979 / 976562500)) := by
  have h := reflection_log_10220_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10221_neg : (341784771 / 1000000000) ≤ -Real.log (500000000000 / 703728669927) ∧
    -Real.log (500000000000 / 703728669927) ≤ (85446193 / 250000000) := by
  have h := checkLog_sound (w := (203728669927 / 1203728669927)) (n := 12)
    (lo := (341784771 / 1000000000)) (hi := (85446193 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703728669927 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703728669927 / 500000000000) = 1/(500000000000 / 703728669927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10221 : Bounds (341784771 / 1000000000) (85446193 / 250000000) (Real.log (703728669927 / 500000000000)) := by
  have h := reflection_log_10221_neg
  have he : Real.log (703728669927 / 500000000000) = -Real.log (500000000000 / 703728669927) := by
    rw [show ((703728669927 / 500000000000) : ℝ) = ((500000000000 / 703728669927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10222_neg : (8588791 / 25000000) ≤ -Real.log (7812500000 / 11015205707) ∧
    -Real.log (7812500000 / 11015205707) ≤ (343551641 / 1000000000) := by
  have h := checkLog_sound (w := (3202705707 / 18827705707)) (n := 12)
    (lo := (8588791 / 25000000)) (hi := (343551641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11015205707 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11015205707 / 7812500000) = 1/(7812500000 / 11015205707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10222 : Bounds (8588791 / 25000000) (343551641 / 1000000000) (Real.log (11015205707 / 7812500000)) := by
  have h := reflection_log_10222_neg
  have he : Real.log (11015205707 / 7812500000) = -Real.log (7812500000 / 11015205707) := by
    rw [show ((11015205707 / 7812500000) : ℝ) = ((7812500000 / 11015205707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10223_neg : (690148677 / 1000000000) ≤ -Real.log (500000000000 / 997005988023) ∧
    -Real.log (500000000000 / 997005988023) ≤ (345074339 / 500000000) := by
  have h := checkLog_sound (w := (497005988023 / 1497005988023)) (n := 12)
    (lo := (690148677 / 1000000000)) (hi := (345074339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((997005988023 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(997005988023 / 500000000000) = 1/(500000000000 / 997005988023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10223 : Bounds (690148677 / 1000000000) (345074339 / 500000000) (Real.log (997005988023 / 500000000000)) := by
  have h := reflection_log_10223_neg
  have he : Real.log (997005988023 / 500000000000) = -Real.log (500000000000 / 997005988023) := by
    rw [show ((997005988023 / 500000000000) : ℝ) = ((500000000000 / 997005988023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10224_neg : (346198637 / 500000000) ≤ -Real.log (500000000000 / 999250374813) ∧
    -Real.log (500000000000 / 999250374813) ≤ (27695891 / 40000000) := by
  have h := checkLog_sound (w := (499250374813 / 1499250374813)) (n := 12)
    (lo := (346198637 / 500000000)) (hi := (27695891 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((999250374813 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(999250374813 / 500000000000) = 1/(500000000000 / 999250374813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10224 : Bounds (346198637 / 500000000) (27695891 / 40000000) (Real.log (999250374813 / 500000000000)) := by
  have h := reflection_log_10224_neg
  have he : Real.log (999250374813 / 500000000000) = -Real.log (500000000000 / 999250374813) := by
    rw [show ((999250374813 / 500000000000) : ℝ) = ((500000000000 / 999250374813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10225_neg : (288181947 / 1000000000) ≤ -Real.log (500 / 667) ∧
    -Real.log (500 / 667) ≤ (72045487 / 250000000) := by
  have h := checkLog_sound (w := (167 / 1167)) (n := 12)
    (lo := (288181947 / 1000000000)) (hi := (72045487 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667 / 500) = 1/(500 / 667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10225 : Bounds (288181947 / 1000000000) (72045487 / 250000000) (Real.log (667 / 500)) := by
  have h := reflection_log_10225_neg
  have he : Real.log (667 / 500) = -Real.log (500 / 667) := by
    rw [show ((667 / 500) : ℝ) = ((500 / 667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10226_neg : (50808201 / 125000000) ≤ -Real.log (333 / 500) ∧
    -Real.log (333 / 500) ≤ (406465609 / 1000000000) := by
  have h := checkLog_sound (w := (167 / 833)) (n := 12)
    (lo := (50808201 / 125000000)) (hi := (406465609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 333) = 1/(333 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10226 : Bounds (-406465609 / 1000000000) (-50808201 / 125000000) (Real.log (333 / 500)) := by
  have h := reflection_log_10226_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10227_neg : (41743 / 125000000) ≤ -Real.log (500000 / 500167) ∧
    -Real.log (500000 / 500167) ≤ (66789 / 200000000) := by
  have h := checkLog_sound (w := (167 / 1000167)) (n := 12)
    (lo := (41743 / 125000000)) (hi := (66789 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500167 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500167 / 500000) = 1/(500000 / 500167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10227 : Bounds (41743 / 125000000) (66789 / 200000000) (Real.log (500167 / 500000)) := by
  have h := reflection_log_10227_neg
  have he : Real.log (500167 / 500000) = -Real.log (500000 / 500167) := by
    rw [show ((500167 / 500000) : ℝ) = ((500000 / 500167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10228_neg : (66811 / 200000000) ≤ -Real.log (499833 / 500000) ∧
    -Real.log (499833 / 500000) ≤ (41757 / 125000000) := by
  have h := checkLog_sound (w := (167 / 999833)) (n := 12)
    (lo := (66811 / 200000000)) (hi := (41757 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499833) = 1/(499833 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10228 : Bounds (-41757 / 125000000) (-66811 / 200000000) (Real.log (499833 / 500000)) := by
  have h := reflection_log_10228_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10229_neg : (78407421 / 500000000) ≤ -Real.log (1000000 / 1169779) ∧
    -Real.log (1000000 / 1169779) ≤ (156814843 / 1000000000) := by
  have h := checkLog_sound (w := (169779 / 2169779)) (n := 12)
    (lo := (78407421 / 500000000)) (hi := (156814843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1169779 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1169779 / 1000000) = 1/(1000000 / 1169779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10229 : Bounds (78407421 / 500000000) (156814843 / 1000000000) (Real.log (1169779 / 1000000)) := by
  have h := reflection_log_10229_neg
  have he : Real.log (1169779 / 1000000) = -Real.log (1000000 / 1169779) := by
    rw [show ((1169779 / 1000000) : ℝ) = ((1000000 / 1169779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10230_neg : (46515837 / 250000000) ≤ -Real.log (830221 / 1000000) ∧
    -Real.log (830221 / 1000000) ≤ (186063349 / 1000000000) := by
  have h := checkLog_sound (w := (169779 / 1830221)) (n := 12)
    (lo := (46515837 / 250000000)) (hi := (186063349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 830221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 830221) = 1/(830221 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10230 : Bounds (-186063349 / 1000000000) (-46515837 / 250000000) (Real.log (830221 / 1000000)) := by
  have h := reflection_log_10230_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10231_neg : (157549753 / 1000000000) ≤ -Real.log (1000000 / 1170639) ∧
    -Real.log (1000000 / 1170639) ≤ (78774877 / 500000000) := by
  have h := checkLog_sound (w := (170639 / 2170639)) (n := 12)
    (lo := (157549753 / 1000000000)) (hi := (78774877 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1170639 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1170639 / 1000000) = 1/(1000000 / 1170639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10231 : Bounds (157549753 / 1000000000) (78774877 / 500000000) (Real.log (1170639 / 1000000)) := by
  have h := reflection_log_10231_neg
  have he : Real.log (1170639 / 1000000) = -Real.log (1000000 / 1170639) := by
    rw [show ((1170639 / 1000000) : ℝ) = ((1000000 / 1170639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10232_neg : (93549877 / 500000000) ≤ -Real.log (829361 / 1000000) ∧
    -Real.log (829361 / 1000000) ≤ (37419951 / 200000000) := by
  have h := checkLog_sound (w := (170639 / 1829361)) (n := 12)
    (lo := (93549877 / 500000000)) (hi := (37419951 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 829361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 829361) = 1/(829361 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10232 : Bounds (-37419951 / 200000000) (-93549877 / 500000000) (Real.log (829361 / 1000000)) := by
  have h := reflection_log_10232_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10233_neg : (591 / 20000) ≤ -Real.log (970882331679 / 1000000000000) ∧
    -Real.log (970882331679 / 1000000000000) ≤ (29550001 / 1000000000) := by
  have h := checkLog_sound (w := (29117668321 / 1970882331679)) (n := 12)
    (lo := (591 / 20000)) (hi := (29550001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 970882331679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 970882331679) = 1/(970882331679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10233 : Bounds (-29550001 / 1000000000) (-591 / 20000) (Real.log (970882331679 / 1000000000000)) := by
  have h := reflection_log_10233_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10234_neg : (14624253 / 500000000) ≤ -Real.log (971175091159 / 1000000000000) ∧
    -Real.log (971175091159 / 1000000000000) ≤ (29248507 / 1000000000) := by
  have h := checkLog_sound (w := (28824908841 / 1971175091159)) (n := 12)
    (lo := (14624253 / 500000000)) (hi := (29248507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 971175091159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 971175091159) = 1/(971175091159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10234 : Bounds (-29248507 / 1000000000) (-14624253 / 500000000) (Real.log (971175091159 / 1000000000000)) := by
  have h := reflection_log_10234_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10235_neg : (34287819 / 100000000) ≤ -Real.log (250000000000 / 352249280613) ∧
    -Real.log (250000000000 / 352249280613) ≤ (342878191 / 1000000000) := by
  have h := checkLog_sound (w := (102249280613 / 602249280613)) (n := 12)
    (lo := (34287819 / 100000000)) (hi := (342878191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352249280613 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352249280613 / 250000000000) = 1/(250000000000 / 352249280613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10235 : Bounds (34287819 / 100000000) (342878191 / 1000000000) (Real.log (352249280613 / 250000000000)) := by
  have h := reflection_log_10235_neg
  have he : Real.log (352249280613 / 250000000000) = -Real.log (250000000000 / 352249280613) := by
    rw [show ((352249280613 / 250000000000) : ℝ) = ((250000000000 / 352249280613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10236_neg : (344649507 / 1000000000) ≤ -Real.log (500000000000 / 705747557457) ∧
    -Real.log (500000000000 / 705747557457) ≤ (86162377 / 250000000) := by
  have h := checkLog_sound (w := (205747557457 / 1205747557457)) (n := 12)
    (lo := (344649507 / 1000000000)) (hi := (86162377 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705747557457 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705747557457 / 500000000000) = 1/(500000000000 / 705747557457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10236 : Bounds (344649507 / 1000000000) (86162377 / 250000000) (Real.log (705747557457 / 500000000000)) := by
  have h := reflection_log_10236_neg
  have he : Real.log (705747557457 / 500000000000) = -Real.log (500000000000 / 705747557457) := by
    rw [show ((705747557457 / 500000000000) : ℝ) = ((500000000000 / 705747557457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10237_neg : (346198637 / 500000000) ≤ -Real.log (125000000000 / 249812593703) ∧
    -Real.log (125000000000 / 249812593703) ≤ (27695891 / 40000000) := by
  have h := checkLog_sound (w := (124812593703 / 374812593703)) (n := 12)
    (lo := (346198637 / 500000000)) (hi := (27695891 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249812593703 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(249812593703 / 125000000000) = 1/(125000000000 / 249812593703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10237 : Bounds (346198637 / 500000000) (27695891 / 40000000) (Real.log (249812593703 / 125000000000)) := by
  have h := reflection_log_10237_neg
  have he : Real.log (249812593703 / 125000000000) = -Real.log (125000000000 / 249812593703) := by
    rw [show ((249812593703 / 125000000000) : ℝ) = ((125000000000 / 249812593703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10238_neg : (138929511 / 200000000) ≤ -Real.log (250000000000 / 500750750751) ∧
    -Real.log (250000000000 / 500750750751) ≤ (694647557 / 1000000000) := by
  have h := checkLog_sound (w := (750750751 / 1000750750751)) (n := 12)
    (lo := (12003 / 8000000)) (hi := (187547 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500750750751 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500750750751 / 500000000000) = 1/(250000000000 / 500750750751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10238 : Bounds (138929511 / 200000000) (694647557 / 1000000000) (Real.log (500750750751 / 250000000000)) := by
  have h := reflection_log_10238_neg
  have he : Real.log (500750750751 / 250000000000) = -Real.log (250000000000 / 500750750751) := by
    rw [show ((500750750751 / 250000000000) : ℝ) = ((250000000000 / 500750750751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10239_neg : (288931291 / 1000000000) ≤ -Real.log (200 / 267) ∧
    -Real.log (200 / 267) ≤ (72232823 / 250000000) := by
  have h := checkLog_sound (w := (67 / 467)) (n := 12)
    (lo := (288931291 / 1000000000)) (hi := (72232823 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((267 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(267 / 200) = 1/(200 / 267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10239 : Bounds (288931291 / 1000000000) (72232823 / 250000000) (Real.log (267 / 200)) := by
  have h := reflection_log_10239_neg
  have he : Real.log (267 / 200) = -Real.log (200 / 267) := by
    rw [show ((267 / 200) : ℝ) = ((200 / 267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


