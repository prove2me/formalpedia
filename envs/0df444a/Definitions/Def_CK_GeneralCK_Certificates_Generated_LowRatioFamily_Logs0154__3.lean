-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0154__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0154__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T20:37:07.881164+00:00
-- url     : https://prove2.me/theorems/feb9c24c-db73-485d-8c37-fd8e1b195e7f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0154 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0155, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0154 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0155, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0156)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0154 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0155, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0156)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0154 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0155, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0156) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0154 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0155, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0156).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0154 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9856_neg : (3059913 / 125000000) ≤ -Real.log (243954470991 / 250000000000) ∧
    -Real.log (243954470991 / 250000000000) ≤ (4895861 / 200000000) := by
  have h := checkLog_sound (w := (6045529009 / 493954470991)) (n := 12)
    (lo := (3059913 / 125000000)) (hi := (4895861 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243954470991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243954470991) = 1/(243954470991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9856 : Bounds (-4895861 / 200000000) (-3059913 / 125000000) (Real.log (243954470991 / 250000000000)) := by
  have h := reflection_log_9856_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9857_neg : (31355599 / 100000000) ≤ -Real.log (500000000000 / 684141035933) ∧
    -Real.log (500000000000 / 684141035933) ≤ (313555991 / 1000000000) := by
  have h := checkLog_sound (w := (184141035933 / 1184141035933)) (n := 12)
    (lo := (31355599 / 100000000)) (hi := (313555991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((684141035933 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(684141035933 / 500000000000) = 1/(500000000000 / 684141035933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9857 : Bounds (31355599 / 100000000) (313555991 / 1000000000) (Real.log (684141035933 / 500000000000)) := by
  have h := reflection_log_9857_neg
  have he : Real.log (684141035933 / 500000000000) = -Real.log (500000000000 / 684141035933) := by
    rw [show ((684141035933 / 500000000000) : ℝ) = ((500000000000 / 684141035933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9858_neg : (315255303 / 1000000000) ≤ -Real.log (31250000000 / 42831537103) ∧
    -Real.log (31250000000 / 42831537103) ≤ (39406913 / 125000000) := by
  have h := checkLog_sound (w := (11581537103 / 74081537103)) (n := 12)
    (lo := (315255303 / 1000000000)) (hi := (39406913 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42831537103 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42831537103 / 31250000000) = 1/(31250000000 / 42831537103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9858 : Bounds (315255303 / 1000000000) (39406913 / 125000000) (Real.log (42831537103 / 31250000000)) := by
  have h := reflection_log_9858_neg
  have he : Real.log (42831537103 / 31250000000) = -Real.log (31250000000 / 42831537103) := by
    rw [show ((42831537103 / 31250000000) : ℝ) = ((31250000000 / 42831537103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9859_neg : (632252349 / 1000000000) ≤ -Real.log (500000000000 / 940922190201) ∧
    -Real.log (500000000000 / 940922190201) ≤ (12645047 / 20000000) := by
  have h := checkLog_sound (w := (440922190201 / 1440922190201)) (n := 12)
    (lo := (632252349 / 1000000000)) (hi := (12645047 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((940922190201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(940922190201 / 500000000000) = 1/(500000000000 / 940922190201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9859 : Bounds (632252349 / 1000000000) (12645047 / 20000000) (Real.log (940922190201 / 500000000000)) := by
  have h := reflection_log_9859_neg
  have he : Real.log (940922190201 / 500000000000) = -Real.log (500000000000 / 940922190201) := by
    rw [show ((940922190201 / 500000000000) : ℝ) = ((500000000000 / 940922190201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9860_neg : (317229857 / 500000000) ≤ -Real.log (250000000000 / 471500721501) ∧
    -Real.log (250000000000 / 471500721501) ≤ (126891943 / 200000000) := by
  have h := checkLog_sound (w := (221500721501 / 721500721501)) (n := 12)
    (lo := (317229857 / 500000000)) (hi := (126891943 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((471500721501 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(471500721501 / 250000000000) = 1/(250000000000 / 471500721501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9860 : Bounds (317229857 / 500000000) (126891943 / 200000000) (Real.log (471500721501 / 250000000000)) := by
  have h := reflection_log_9860_neg
  have he : Real.log (471500721501 / 250000000000) = -Real.log (250000000000 / 471500721501) := by
    rw [show ((471500721501 / 250000000000) : ℝ) = ((250000000000 / 471500721501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9861_neg : (268499253 / 1000000000) ≤ -Real.log (250 / 327) ∧
    -Real.log (250 / 327) ≤ (134249627 / 500000000) := by
  have h := checkLog_sound (w := (77 / 577)) (n := 12)
    (lo := (268499253 / 1000000000)) (hi := (134249627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((327 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(327 / 250) = 1/(250 / 327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9861 : Bounds (268499253 / 1000000000) (134249627 / 500000000) (Real.log (327 / 250)) := by
  have h := reflection_log_9861_neg
  have he : Real.log (327 / 250) = -Real.log (250 / 327) := by
    rw [show ((327 / 250) : ℝ) = ((250 / 327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9862_neg : (368169323 / 1000000000) ≤ -Real.log (173 / 250) ∧
    -Real.log (173 / 250) ≤ (92042331 / 250000000) := by
  have h := checkLog_sound (w := (77 / 423)) (n := 12)
    (lo := (368169323 / 1000000000)) (hi := (92042331 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 173) = 1/(173 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9862 : Bounds (-92042331 / 250000000) (-368169323 / 1000000000) (Real.log (173 / 250)) := by
  have h := reflection_log_9862_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9863_neg : (19247 / 62500000) ≤ -Real.log (250000 / 250077) ∧
    -Real.log (250000 / 250077) ≤ (307953 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 500077)) (n := 12)
    (lo := (19247 / 62500000)) (hi := (307953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250077 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250077 / 250000) = 1/(250000 / 250077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9863 : Bounds (19247 / 62500000) (307953 / 1000000000) (Real.log (250077 / 250000)) := by
  have h := reflection_log_9863_neg
  have he : Real.log (250077 / 250000) = -Real.log (250000 / 250077) := by
    rw [show ((250077 / 250000) : ℝ) = ((250000 / 250077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9864_neg : (308047 / 1000000000) ≤ -Real.log (249923 / 250000) ∧
    -Real.log (249923 / 250000) ≤ (19253 / 62500000) := by
  have h := checkLog_sound (w := (77 / 499923)) (n := 12)
    (lo := (308047 / 1000000000)) (hi := (19253 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249923) = 1/(249923 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9864 : Bounds (-19253 / 62500000) (-308047 / 1000000000) (Real.log (249923 / 250000)) := by
  have h := reflection_log_9864_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9865_neg : (36248579 / 250000000) ≤ -Real.log (1000000 / 1156033) ∧
    -Real.log (1000000 / 1156033) ≤ (144994317 / 1000000000) := by
  have h := checkLog_sound (w := (156033 / 2156033)) (n := 12)
    (lo := (36248579 / 250000000)) (hi := (144994317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1156033 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1156033 / 1000000) = 1/(1000000 / 1156033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9865 : Bounds (36248579 / 250000000) (144994317 / 1000000000) (Real.log (1156033 / 1000000)) := by
  have h := reflection_log_9865_neg
  have he : Real.log (1156033 / 1000000) = -Real.log (1000000 / 1156033) := by
    rw [show ((1156033 / 1000000) : ℝ) = ((1000000 / 1156033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9866_neg : (42410471 / 250000000) ≤ -Real.log (843967 / 1000000) ∧
    -Real.log (843967 / 1000000) ≤ (33928377 / 200000000) := by
  have h := checkLog_sound (w := (156033 / 1843967)) (n := 12)
    (lo := (42410471 / 250000000)) (hi := (33928377 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 843967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 843967) = 1/(843967 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9866 : Bounds (-33928377 / 200000000) (-42410471 / 250000000) (Real.log (843967 / 1000000)) := by
  have h := reflection_log_9866_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9867_neg : (145711167 / 1000000000) ≤ -Real.log (500000 / 578431) ∧
    -Real.log (500000 / 578431) ≤ (2276737 / 15625000) := by
  have h := checkLog_sound (w := (78431 / 1078431)) (n := 12)
    (lo := (145711167 / 1000000000)) (hi := (2276737 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((578431 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(578431 / 500000) = 1/(500000 / 578431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9867 : Bounds (145711167 / 1000000000) (2276737 / 15625000) (Real.log (578431 / 500000)) := by
  have h := reflection_log_9867_neg
  have he : Real.log (578431 / 500000) = -Real.log (500000 / 578431) := by
    rw [show ((578431 / 500000) : ℝ) = ((500000 / 578431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9868_neg : (170624633 / 1000000000) ≤ -Real.log (421569 / 500000) ∧
    -Real.log (421569 / 500000) ≤ (85312317 / 500000000) := by
  have h := checkLog_sound (w := (78431 / 921569)) (n := 12)
    (lo := (170624633 / 1000000000)) (hi := (85312317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 421569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 421569) = 1/(421569 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9868 : Bounds (-85312317 / 500000000) (-170624633 / 1000000000) (Real.log (421569 / 500000)) := by
  have h := reflection_log_9868_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9869_neg : (12456733 / 500000000) ≤ -Real.log (243848578239 / 250000000000) ∧
    -Real.log (243848578239 / 250000000000) ≤ (24913467 / 1000000000) := by
  have h := checkLog_sound (w := (6151421761 / 493848578239)) (n := 12)
    (lo := (12456733 / 500000000)) (hi := (24913467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243848578239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243848578239) = 1/(243848578239 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9869 : Bounds (-24913467 / 1000000000) (-12456733 / 500000000) (Real.log (243848578239 / 250000000000)) := by
  have h := reflection_log_9869_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9870_neg : (1540473 / 62500000) ≤ -Real.log (975653702911 / 1000000000000) ∧
    -Real.log (975653702911 / 1000000000000) ≤ (24647569 / 1000000000) := by
  have h := checkLog_sound (w := (24346297089 / 1975653702911)) (n := 12)
    (lo := (1540473 / 62500000)) (hi := (24647569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975653702911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975653702911) = 1/(975653702911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9870 : Bounds (-24647569 / 1000000000) (-1540473 / 62500000) (Real.log (975653702911 / 1000000000000)) := by
  have h := reflection_log_9870_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9871_neg : (314636201 / 1000000000) ≤ -Real.log (250000000000 / 342440225743) ∧
    -Real.log (250000000000 / 342440225743) ≤ (157318101 / 500000000) := by
  have h := checkLog_sound (w := (92440225743 / 592440225743)) (n := 12)
    (lo := (314636201 / 1000000000)) (hi := (157318101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342440225743 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342440225743 / 250000000000) = 1/(250000000000 / 342440225743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9871 : Bounds (314636201 / 1000000000) (157318101 / 500000000) (Real.log (342440225743 / 250000000000)) := by
  have h := reflection_log_9871_neg
  have he : Real.log (342440225743 / 250000000000) = -Real.log (250000000000 / 342440225743) := by
    rw [show ((342440225743 / 250000000000) : ℝ) = ((250000000000 / 342440225743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9872_neg : (1581679 / 5000000) ≤ -Real.log (100000000000 / 137209092699) ∧
    -Real.log (100000000000 / 137209092699) ≤ (316335801 / 1000000000) := by
  have h := checkLog_sound (w := (37209092699 / 237209092699)) (n := 12)
    (lo := (1581679 / 5000000)) (hi := (316335801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137209092699 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137209092699 / 100000000000) = 1/(100000000000 / 137209092699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9872 : Bounds (1581679 / 5000000) (316335801 / 1000000000) (Real.log (137209092699 / 100000000000)) := by
  have h := reflection_log_9872_neg
  have he : Real.log (137209092699 / 100000000000) = -Real.log (100000000000 / 137209092699) := by
    rw [show ((137209092699 / 100000000000) : ℝ) = ((100000000000 / 137209092699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9873_neg : (317229857 / 500000000) ≤ -Real.log (500000000000 / 943001443001) ∧
    -Real.log (500000000000 / 943001443001) ≤ (126891943 / 200000000) := by
  have h := checkLog_sound (w := (443001443001 / 1443001443001)) (n := 12)
    (lo := (317229857 / 500000000)) (hi := (126891943 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((943001443001 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(943001443001 / 500000000000) = 1/(500000000000 / 943001443001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9873 : Bounds (317229857 / 500000000) (126891943 / 200000000) (Real.log (943001443001 / 500000000000)) := by
  have h := reflection_log_9873_neg
  have he : Real.log (943001443001 / 500000000000) = -Real.log (500000000000 / 943001443001) := by
    rw [show ((943001443001 / 500000000000) : ℝ) = ((500000000000 / 943001443001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9874_neg : (19895893 / 31250000) ≤ -Real.log (500000000000 / 945086705203) ∧
    -Real.log (500000000000 / 945086705203) ≤ (636668577 / 1000000000) := by
  have h := checkLog_sound (w := (445086705203 / 1445086705203)) (n := 12)
    (lo := (19895893 / 31250000)) (hi := (636668577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((945086705203 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(945086705203 / 500000000000) = 1/(500000000000 / 945086705203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9874 : Bounds (19895893 / 31250000) (636668577 / 1000000000) (Real.log (945086705203 / 500000000000)) := by
  have h := reflection_log_9874_neg
  have he : Real.log (945086705203 / 500000000000) = -Real.log (500000000000 / 945086705203) := by
    rw [show ((945086705203 / 500000000000) : ℝ) = ((500000000000 / 945086705203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9875_neg : (134631743 / 500000000) ≤ -Real.log (1000 / 1309) ∧
    -Real.log (1000 / 1309) ≤ (269263487 / 1000000000) := by
  have h := checkLog_sound (w := (309 / 2309)) (n := 12)
    (lo := (134631743 / 500000000)) (hi := (269263487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1309 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1309 / 1000) = 1/(1000 / 1309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9875 : Bounds (134631743 / 500000000) (269263487 / 1000000000) (Real.log (1309 / 1000)) := by
  have h := reflection_log_9875_neg
  have he : Real.log (1309 / 1000) = -Real.log (1000 / 1309) := by
    rw [show ((1309 / 1000) : ℝ) = ((1000 / 1309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9876_neg : (73923091 / 200000000) ≤ -Real.log (691 / 1000) ∧
    -Real.log (691 / 1000) ≤ (11550483 / 31250000) := by
  have h := checkLog_sound (w := (309 / 1691)) (n := 12)
    (lo := (73923091 / 200000000)) (hi := (11550483 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 691) = 1/(691 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9876 : Bounds (-11550483 / 31250000) (-73923091 / 200000000) (Real.log (691 / 1000)) := by
  have h := reflection_log_9876_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9877_neg : (38619 / 125000000) ≤ -Real.log (1000000 / 1000309) ∧
    -Real.log (1000000 / 1000309) ≤ (308953 / 1000000000) := by
  have h := checkLog_sound (w := (309 / 2000309)) (n := 12)
    (lo := (38619 / 125000000)) (hi := (308953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000309 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000309 / 1000000) = 1/(1000000 / 1000309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9877 : Bounds (38619 / 125000000) (308953 / 1000000000) (Real.log (1000309 / 1000000)) := by
  have h := reflection_log_9877_neg
  have he : Real.log (1000309 / 1000000) = -Real.log (1000000 / 1000309) := by
    rw [show ((1000309 / 1000000) : ℝ) = ((1000000 / 1000309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9878_neg : (309047 / 1000000000) ≤ -Real.log (999691 / 1000000) ∧
    -Real.log (999691 / 1000000) ≤ (38631 / 125000000) := by
  have h := checkLog_sound (w := (309 / 1999691)) (n := 12)
    (lo := (309047 / 1000000000)) (hi := (38631 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999691) = 1/(999691 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9878 : Bounds (-38631 / 125000000) (-309047 / 1000000000) (Real.log (999691 / 1000000)) := by
  have h := reflection_log_9878_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9879_neg : (145449217 / 1000000000) ≤ -Real.log (1000000 / 1156559) ∧
    -Real.log (1000000 / 1156559) ≤ (72724609 / 500000000) := by
  have h := checkLog_sound (w := (156559 / 2156559)) (n := 12)
    (lo := (145449217 / 1000000000)) (hi := (72724609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1156559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1156559 / 1000000) = 1/(1000000 / 1156559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9879 : Bounds (145449217 / 1000000000) (72724609 / 500000000) (Real.log (1156559 / 1000000)) := by
  have h := reflection_log_9879_neg
  have he : Real.log (1156559 / 1000000) = -Real.log (1000000 / 1156559) := by
    rw [show ((1156559 / 1000000) : ℝ) = ((1000000 / 1156559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9880_neg : (85132663 / 500000000) ≤ -Real.log (843441 / 1000000) ∧
    -Real.log (843441 / 1000000) ≤ (170265327 / 1000000000) := by
  have h := checkLog_sound (w := (156559 / 1843441)) (n := 12)
    (lo := (85132663 / 500000000)) (hi := (170265327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 843441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 843441) = 1/(843441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9880 : Bounds (-170265327 / 1000000000) (-85132663 / 500000000) (Real.log (843441 / 1000000)) := by
  have h := reflection_log_9880_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9881_neg : (14616747 / 100000000) ≤ -Real.log (100000 / 115739) ∧
    -Real.log (100000 / 115739) ≤ (146167471 / 1000000000) := by
  have h := checkLog_sound (w := (15739 / 215739)) (n := 12)
    (lo := (14616747 / 100000000)) (hi := (146167471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((115739 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(115739 / 100000) = 1/(100000 / 115739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9881 : Bounds (14616747 / 100000000) (146167471 / 1000000000) (Real.log (115739 / 100000)) := by
  have h := reflection_log_9881_neg
  have he : Real.log (115739 / 100000) = -Real.log (100000 / 115739) := by
    rw [show ((115739 / 100000) : ℝ) = ((100000 / 115739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9882_neg : (171251061 / 1000000000) ≤ -Real.log (84261 / 100000) ∧
    -Real.log (84261 / 100000) ≤ (85625531 / 500000000) := by
  have h := checkLog_sound (w := (15739 / 184261)) (n := 12)
    (lo := (171251061 / 1000000000)) (hi := (85625531 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 84261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 84261) = 1/(84261 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9882 : Bounds (-85625531 / 500000000) (-171251061 / 1000000000) (Real.log (84261 / 100000)) := by
  have h := reflection_log_9882_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9883_neg : (25083591 / 1000000000) ≤ -Real.log (9752283879 / 10000000000) ∧
    -Real.log (9752283879 / 10000000000) ≤ (3135449 / 125000000) := by
  have h := checkLog_sound (w := (247716121 / 19752283879)) (n := 12)
    (lo := (25083591 / 1000000000)) (hi := (3135449 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9752283879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9752283879) = 1/(9752283879 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9883 : Bounds (-3135449 / 125000000) (-25083591 / 1000000000) (Real.log (9752283879 / 10000000000)) := by
  have h := reflection_log_9883_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9884_neg : (6204027 / 250000000) ≤ -Real.log (975489279519 / 1000000000000) ∧
    -Real.log (975489279519 / 1000000000000) ≤ (24816109 / 1000000000) := by
  have h := checkLog_sound (w := (24510720481 / 1975489279519)) (n := 12)
    (lo := (6204027 / 250000000)) (hi := (24816109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975489279519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975489279519) = 1/(975489279519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9884 : Bounds (-24816109 / 1000000000) (-6204027 / 250000000) (Real.log (975489279519 / 1000000000000)) := by
  have h := reflection_log_9884_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9885_neg : (315714543 / 1000000000) ≤ -Real.log (500000000000 / 685619385351) ∧
    -Real.log (500000000000 / 685619385351) ≤ (19732159 / 62500000) := by
  have h := checkLog_sound (w := (185619385351 / 1185619385351)) (n := 12)
    (lo := (315714543 / 1000000000)) (hi := (19732159 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685619385351 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685619385351 / 500000000000) = 1/(500000000000 / 685619385351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9885 : Bounds (315714543 / 1000000000) (19732159 / 62500000) (Real.log (685619385351 / 500000000000)) := by
  have h := reflection_log_9885_neg
  have he : Real.log (685619385351 / 500000000000) = -Real.log (500000000000 / 685619385351) := by
    rw [show ((685619385351 / 500000000000) : ℝ) = ((500000000000 / 685619385351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9886_neg : (317418531 / 1000000000) ≤ -Real.log (250000000000 / 343394334271) ∧
    -Real.log (250000000000 / 343394334271) ≤ (79354633 / 250000000) := by
  have h := checkLog_sound (w := (93394334271 / 593394334271)) (n := 12)
    (lo := (317418531 / 1000000000)) (hi := (79354633 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343394334271 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343394334271 / 250000000000) = 1/(250000000000 / 343394334271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9886 : Bounds (317418531 / 1000000000) (79354633 / 250000000) (Real.log (343394334271 / 250000000000)) := by
  have h := reflection_log_9886_neg
  have he : Real.log (343394334271 / 250000000000) = -Real.log (250000000000 / 343394334271) := by
    rw [show ((343394334271 / 250000000000) : ℝ) = ((250000000000 / 343394334271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9887_neg : (19895893 / 31250000) ≤ -Real.log (250000000000 / 472543352601) ∧
    -Real.log (250000000000 / 472543352601) ≤ (636668577 / 1000000000) := by
  have h := checkLog_sound (w := (222543352601 / 722543352601)) (n := 12)
    (lo := (19895893 / 31250000)) (hi := (636668577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((472543352601 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(472543352601 / 250000000000) = 1/(250000000000 / 472543352601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9887 : Bounds (19895893 / 31250000) (636668577 / 1000000000) (Real.log (472543352601 / 250000000000)) := by
  have h := reflection_log_9887_neg
  have he : Real.log (472543352601 / 250000000000) = -Real.log (250000000000 / 472543352601) := by
    rw [show ((472543352601 / 250000000000) : ℝ) = ((250000000000 / 472543352601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9888_neg : (319439471 / 500000000) ≤ -Real.log (100000000000 / 189435600579) ∧
    -Real.log (100000000000 / 189435600579) ≤ (638878943 / 1000000000) := by
  have h := checkLog_sound (w := (89435600579 / 289435600579)) (n := 12)
    (lo := (319439471 / 500000000)) (hi := (638878943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189435600579 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189435600579 / 100000000000) = 1/(100000000000 / 189435600579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9888 : Bounds (319439471 / 500000000) (638878943 / 1000000000) (Real.log (189435600579 / 100000000000)) := by
  have h := reflection_log_9888_neg
  have he : Real.log (189435600579 / 100000000000) = -Real.log (100000000000 / 189435600579) := by
    rw [show ((189435600579 / 100000000000) : ℝ) = ((100000000000 / 189435600579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9889_neg : (270027137 / 1000000000) ≤ -Real.log (100 / 131) ∧
    -Real.log (100 / 131) ≤ (135013569 / 500000000) := by
  have h := checkLog_sound (w := (31 / 231)) (n := 12)
    (lo := (270027137 / 1000000000)) (hi := (135013569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(131 / 100) = 1/(100 / 131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9889 : Bounds (270027137 / 1000000000) (135013569 / 500000000) (Real.log (131 / 100)) := by
  have h := reflection_log_9889_neg
  have he : Real.log (131 / 100) = -Real.log (100 / 131) := by
    rw [show ((131 / 100) : ℝ) = ((100 / 131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9890_neg : (371063681 / 1000000000) ≤ -Real.log (69 / 100) ∧
    -Real.log (69 / 100) ≤ (185531841 / 500000000) := by
  have h := checkLog_sound (w := (31 / 169)) (n := 12)
    (lo := (371063681 / 1000000000)) (hi := (185531841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 69) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 69) = 1/(69 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9890 : Bounds (-185531841 / 500000000) (-371063681 / 1000000000) (Real.log (69 / 100)) := by
  have h := reflection_log_9890_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9891_neg : (309951 / 1000000000) ≤ -Real.log (100000 / 100031) ∧
    -Real.log (100000 / 100031) ≤ (4843 / 15625000) := by
  have h := checkLog_sound (w := (31 / 200031)) (n := 12)
    (lo := (309951 / 1000000000)) (hi := (4843 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100031 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100031 / 100000) = 1/(100000 / 100031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9891 : Bounds (309951 / 1000000000) (4843 / 15625000) (Real.log (100031 / 100000)) := by
  have h := reflection_log_9891_neg
  have he : Real.log (100031 / 100000) = -Real.log (100000 / 100031) := by
    rw [show ((100031 / 100000) : ℝ) = ((100000 / 100031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9892_neg : (9689 / 31250000) ≤ -Real.log (99969 / 100000) ∧
    -Real.log (99969 / 100000) ≤ (310049 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 199969)) (n := 12)
    (lo := (9689 / 31250000)) (hi := (310049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99969) = 1/(99969 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9892 : Bounds (-310049 / 1000000000) (-9689 / 31250000) (Real.log (99969 / 100000)) := by
  have h := reflection_log_9892_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9893_neg : (145903911 / 1000000000) ≤ -Real.log (200000 / 231417) ∧
    -Real.log (200000 / 231417) ≤ (18237989 / 125000000) := by
  have h := checkLog_sound (w := (31417 / 431417)) (n := 12)
    (lo := (145903911 / 1000000000)) (hi := (18237989 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231417 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231417 / 200000) = 1/(200000 / 231417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9893 : Bounds (145903911 / 1000000000) (18237989 / 125000000) (Real.log (231417 / 200000)) := by
  have h := reflection_log_9893_neg
  have he : Real.log (231417 / 200000) = -Real.log (200000 / 231417) := by
    rw [show ((231417 / 200000) : ℝ) = ((200000 / 231417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9894_neg : (42722289 / 250000000) ≤ -Real.log (168583 / 200000) ∧
    -Real.log (168583 / 200000) ≤ (170889157 / 1000000000) := by
  have h := checkLog_sound (w := (31417 / 368583)) (n := 12)
    (lo := (42722289 / 250000000)) (hi := (170889157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 168583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 168583) = 1/(168583 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9894 : Bounds (-170889157 / 1000000000) (-42722289 / 250000000) (Real.log (168583 / 200000)) := by
  have h := reflection_log_9894_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9895_neg : (146622701 / 1000000000) ≤ -Real.log (1000000 / 1157917) ∧
    -Real.log (1000000 / 1157917) ≤ (73311351 / 500000000) := by
  have h := checkLog_sound (w := (157917 / 2157917)) (n := 12)
    (lo := (146622701 / 1000000000)) (hi := (73311351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1157917 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1157917 / 1000000) = 1/(1000000 / 1157917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9895 : Bounds (146622701 / 1000000000) (73311351 / 500000000) (Real.log (1157917 / 1000000)) := by
  have h := reflection_log_9895_neg
  have he : Real.log (1157917 / 1000000) = -Real.log (1000000 / 1157917) := by
    rw [show ((1157917 / 1000000) : ℝ) = ((1000000 / 1157917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9896_neg : (85938347 / 500000000) ≤ -Real.log (842083 / 1000000) ∧
    -Real.log (842083 / 1000000) ≤ (34375339 / 200000000) := by
  have h := checkLog_sound (w := (157917 / 1842083)) (n := 12)
    (lo := (85938347 / 500000000)) (hi := (34375339 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 842083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 842083) = 1/(842083 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9896 : Bounds (-34375339 / 200000000) (-85938347 / 500000000) (Real.log (842083 / 1000000)) := by
  have h := reflection_log_9896_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9897_neg : (25253993 / 1000000000) ≤ -Real.log (975062221111 / 1000000000000) ∧
    -Real.log (975062221111 / 1000000000000) ≤ (12626997 / 500000000) := by
  have h := checkLog_sound (w := (24937778889 / 1975062221111)) (n := 12)
    (lo := (25253993 / 1000000000)) (hi := (12626997 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975062221111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975062221111) = 1/(975062221111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9897 : Bounds (-12626997 / 500000000) (-25253993 / 1000000000) (Real.log (975062221111 / 1000000000000)) := by
  have h := reflection_log_9897_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9898_neg : (4997049 / 200000000) ≤ -Real.log (39012972111 / 40000000000) ∧
    -Real.log (39012972111 / 40000000000) ≤ (12492623 / 500000000) := by
  have h := checkLog_sound (w := (987027889 / 79012972111)) (n := 12)
    (lo := (4997049 / 200000000)) (hi := (12492623 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39012972111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39012972111) = 1/(39012972111 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9898 : Bounds (-12492623 / 500000000) (-4997049 / 200000000) (Real.log (39012972111 / 40000000000)) := by
  have h := reflection_log_9898_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9899_neg : (316793067 / 1000000000) ≤ -Real.log (500000000000 / 686359241441) ∧
    -Real.log (500000000000 / 686359241441) ≤ (79198267 / 250000000) := by
  have h := checkLog_sound (w := (186359241441 / 1186359241441)) (n := 12)
    (lo := (316793067 / 1000000000)) (hi := (79198267 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((686359241441 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(686359241441 / 500000000000) = 1/(500000000000 / 686359241441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9899 : Bounds (316793067 / 1000000000) (79198267 / 250000000) (Real.log (686359241441 / 500000000000)) := by
  have h := reflection_log_9899_neg
  have he : Real.log (686359241441 / 500000000000) = -Real.log (500000000000 / 686359241441) := by
    rw [show ((686359241441 / 500000000000) : ℝ) = ((500000000000 / 686359241441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9900_neg : (79624849 / 250000000) ≤ -Real.log (250000000000 / 343765697681) ∧
    -Real.log (250000000000 / 343765697681) ≤ (318499397 / 1000000000) := by
  have h := checkLog_sound (w := (93765697681 / 593765697681)) (n := 12)
    (lo := (79624849 / 250000000)) (hi := (318499397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343765697681 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343765697681 / 250000000000) = 1/(250000000000 / 343765697681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9900 : Bounds (79624849 / 250000000) (318499397 / 1000000000) (Real.log (343765697681 / 250000000000)) := by
  have h := reflection_log_9900_neg
  have he : Real.log (343765697681 / 250000000000) = -Real.log (250000000000 / 343765697681) := by
    rw [show ((343765697681 / 250000000000) : ℝ) = ((250000000000 / 343765697681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9901_neg : (319439471 / 500000000) ≤ -Real.log (250000000000 / 473589001447) ∧
    -Real.log (250000000000 / 473589001447) ≤ (638878943 / 1000000000) := by
  have h := checkLog_sound (w := (223589001447 / 723589001447)) (n := 12)
    (lo := (319439471 / 500000000)) (hi := (638878943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((473589001447 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(473589001447 / 250000000000) = 1/(250000000000 / 473589001447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9901 : Bounds (319439471 / 500000000) (638878943 / 1000000000) (Real.log (473589001447 / 250000000000)) := by
  have h := reflection_log_9901_neg
  have he : Real.log (473589001447 / 250000000000) = -Real.log (250000000000 / 473589001447) := by
    rw [show ((473589001447 / 250000000000) : ℝ) = ((250000000000 / 473589001447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9902_neg : (320545409 / 500000000) ≤ -Real.log (500000000000 / 949275362319) ∧
    -Real.log (500000000000 / 949275362319) ≤ (641090819 / 1000000000) := by
  have h := checkLog_sound (w := (449275362319 / 1449275362319)) (n := 12)
    (lo := (320545409 / 500000000)) (hi := (641090819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((949275362319 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(949275362319 / 500000000000) = 1/(500000000000 / 949275362319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9902 : Bounds (320545409 / 500000000) (641090819 / 1000000000) (Real.log (949275362319 / 500000000000)) := by
  have h := reflection_log_9902_neg
  have he : Real.log (949275362319 / 500000000000) = -Real.log (500000000000 / 949275362319) := by
    rw [show ((949275362319 / 500000000000) : ℝ) = ((500000000000 / 949275362319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9903_neg : (67697551 / 250000000) ≤ -Real.log (1000 / 1311) ∧
    -Real.log (1000 / 1311) ≤ (54158041 / 200000000) := by
  have h := checkLog_sound (w := (311 / 2311)) (n := 12)
    (lo := (67697551 / 250000000)) (hi := (54158041 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1311 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1311 / 1000) = 1/(1000 / 1311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9903 : Bounds (67697551 / 250000000) (54158041 / 200000000) (Real.log (1311 / 1000)) := by
  have h := reflection_log_9903_neg
  have he : Real.log (1311 / 1000) = -Real.log (1000 / 1311) := by
    rw [show ((1311 / 1000) : ℝ) = ((1000 / 1311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9904_neg : (372514007 / 1000000000) ≤ -Real.log (689 / 1000) ∧
    -Real.log (689 / 1000) ≤ (46564251 / 125000000) := by
  have h := checkLog_sound (w := (311 / 1689)) (n := 12)
    (lo := (372514007 / 1000000000)) (hi := (46564251 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 689) = 1/(689 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9904 : Bounds (-46564251 / 125000000) (-372514007 / 1000000000) (Real.log (689 / 1000)) := by
  have h := reflection_log_9904_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9905_neg : (310951 / 1000000000) ≤ -Real.log (1000000 / 1000311) ∧
    -Real.log (1000000 / 1000311) ≤ (38869 / 125000000) := by
  have h := checkLog_sound (w := (311 / 2000311)) (n := 12)
    (lo := (310951 / 1000000000)) (hi := (38869 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000311 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000311 / 1000000) = 1/(1000000 / 1000311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9905 : Bounds (310951 / 1000000000) (38869 / 125000000) (Real.log (1000311 / 1000000)) := by
  have h := reflection_log_9905_neg
  have he : Real.log (1000311 / 1000000) = -Real.log (1000000 / 1000311) := by
    rw [show ((1000311 / 1000000) : ℝ) = ((1000000 / 1000311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9906_neg : (38881 / 125000000) ≤ -Real.log (999689 / 1000000) ∧
    -Real.log (999689 / 1000000) ≤ (311049 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 1999689)) (n := 12)
    (lo := (38881 / 125000000)) (hi := (311049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999689) = 1/(999689 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9906 : Bounds (-311049 / 1000000000) (-38881 / 125000000) (Real.log (999689 / 1000000)) := by
  have h := reflection_log_9906_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9907_neg : (73179631 / 500000000) ≤ -Real.log (250000 / 289403) ∧
    -Real.log (250000 / 289403) ≤ (146359263 / 1000000000) := by
  have h := checkLog_sound (w := (39403 / 539403)) (n := 12)
    (lo := (73179631 / 500000000)) (hi := (146359263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((289403 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(289403 / 250000) = 1/(250000 / 289403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9907 : Bounds (73179631 / 500000000) (146359263 / 1000000000) (Real.log (289403 / 250000)) := by
  have h := reflection_log_9907_neg
  have he : Real.log (289403 / 250000) = -Real.log (250000 / 289403) := by
    rw [show ((289403 / 250000) : ℝ) = ((250000 / 289403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9908_neg : (171514563 / 1000000000) ≤ -Real.log (210597 / 250000) ∧
    -Real.log (210597 / 250000) ≤ (42878641 / 250000000) := by
  have h := checkLog_sound (w := (39403 / 460597)) (n := 12)
    (lo := (171514563 / 1000000000)) (hi := (42878641 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 210597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 210597) = 1/(210597 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9908 : Bounds (-42878641 / 250000000) (-171514563 / 1000000000) (Real.log (210597 / 250000)) := by
  have h := reflection_log_9908_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9909_neg : (36769647 / 250000000) ≤ -Real.log (200000 / 231689) ∧
    -Real.log (200000 / 231689) ≤ (147078589 / 1000000000) := by
  have h := checkLog_sound (w := (31689 / 431689)) (n := 12)
    (lo := (36769647 / 250000000)) (hi := (147078589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231689 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231689 / 200000) = 1/(200000 / 231689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9909 : Bounds (36769647 / 250000000) (147078589 / 1000000000) (Real.log (231689 / 200000)) := by
  have h := reflection_log_9909_neg
  have he : Real.log (231689 / 200000) = -Real.log (200000 / 231689) := by
    rw [show ((231689 / 200000) : ℝ) = ((200000 / 231689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9910_neg : (43125977 / 250000000) ≤ -Real.log (168311 / 200000) ∧
    -Real.log (168311 / 200000) ≤ (172503909 / 1000000000) := by
  have h := checkLog_sound (w := (31689 / 368311)) (n := 12)
    (lo := (43125977 / 250000000)) (hi := (172503909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 168311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 168311) = 1/(168311 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9910 : Bounds (-172503909 / 1000000000) (-43125977 / 250000000) (Real.log (168311 / 200000)) := by
  have h := reflection_log_9910_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9911_neg : (25425319 / 1000000000) ≤ -Real.log (38995807279 / 40000000000) ∧
    -Real.log (38995807279 / 40000000000) ≤ (635633 / 25000000) := by
  have h := checkLog_sound (w := (1004192721 / 78995807279)) (n := 12)
    (lo := (25425319 / 1000000000)) (hi := (635633 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38995807279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38995807279) = 1/(38995807279 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9911 : Bounds (-635633 / 25000000) (-25425319 / 1000000000) (Real.log (38995807279 / 40000000000)) := by
  have h := reflection_log_9911_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9912_neg : (251553 / 10000000) ≤ -Real.log (60947403591 / 62500000000) ∧
    -Real.log (60947403591 / 62500000000) ≤ (25155301 / 1000000000) := by
  have h := checkLog_sound (w := (1552596409 / 123447403591)) (n := 12)
    (lo := (251553 / 10000000)) (hi := (25155301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60947403591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60947403591) = 1/(60947403591 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9912 : Bounds (-25155301 / 1000000000) (-251553 / 10000000) (Real.log (60947403591 / 62500000000)) := by
  have h := reflection_log_9912_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9913_neg : (12714953 / 40000000) ≤ -Real.log (250000000000 / 343550715347) ∧
    -Real.log (250000000000 / 343550715347) ≤ (158936913 / 500000000) := by
  have h := checkLog_sound (w := (93550715347 / 593550715347)) (n := 12)
    (lo := (12714953 / 40000000)) (hi := (158936913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343550715347 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343550715347 / 250000000000) = 1/(250000000000 / 343550715347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9913 : Bounds (12714953 / 40000000) (158936913 / 500000000) (Real.log (343550715347 / 250000000000)) := by
  have h := reflection_log_9913_neg
  have he : Real.log (343550715347 / 250000000000) = -Real.log (250000000000 / 343550715347) := by
    rw [show ((343550715347 / 250000000000) : ℝ) = ((250000000000 / 343550715347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9914_neg : (9986953 / 31250000) ≤ -Real.log (500000000000 / 688276464403) ∧
    -Real.log (500000000000 / 688276464403) ≤ (319582497 / 1000000000) := by
  have h := checkLog_sound (w := (188276464403 / 1188276464403)) (n := 12)
    (lo := (9986953 / 31250000)) (hi := (319582497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((688276464403 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(688276464403 / 500000000000) = 1/(500000000000 / 688276464403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9914 : Bounds (9986953 / 31250000) (319582497 / 1000000000) (Real.log (688276464403 / 500000000000)) := by
  have h := reflection_log_9914_neg
  have he : Real.log (688276464403 / 500000000000) = -Real.log (500000000000 / 688276464403) := by
    rw [show ((688276464403 / 500000000000) : ℝ) = ((500000000000 / 688276464403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9915_neg : (320545409 / 500000000) ≤ -Real.log (250000000000 / 474637681159) ∧
    -Real.log (250000000000 / 474637681159) ≤ (641090819 / 1000000000) := by
  have h := checkLog_sound (w := (224637681159 / 724637681159)) (n := 12)
    (lo := (320545409 / 500000000)) (hi := (641090819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((474637681159 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(474637681159 / 250000000000) = 1/(250000000000 / 474637681159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9915 : Bounds (320545409 / 500000000) (641090819 / 1000000000) (Real.log (474637681159 / 250000000000)) := by
  have h := reflection_log_9915_neg
  have he : Real.log (474637681159 / 250000000000) = -Real.log (250000000000 / 474637681159) := by
    rw [show ((474637681159 / 250000000000) : ℝ) = ((250000000000 / 474637681159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9916_neg : (160826053 / 250000000) ≤ -Real.log (50000000000 / 95137880987) ∧
    -Real.log (50000000000 / 95137880987) ≤ (643304213 / 1000000000) := by
  have h := checkLog_sound (w := (45137880987 / 145137880987)) (n := 12)
    (lo := (160826053 / 250000000)) (hi := (643304213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95137880987 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95137880987 / 50000000000) = 1/(50000000000 / 95137880987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9916 : Bounds (160826053 / 250000000) (643304213 / 1000000000) (Real.log (95137880987 / 50000000000)) := by
  have h := reflection_log_9916_neg
  have he : Real.log (95137880987 / 50000000000) = -Real.log (50000000000 / 95137880987) := by
    rw [show ((95137880987 / 50000000000) : ℝ) = ((50000000000 / 95137880987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9917_neg : (27155269 / 100000000) ≤ -Real.log (125 / 164) ∧
    -Real.log (125 / 164) ≤ (271552691 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 289)) (n := 12)
    (lo := (27155269 / 100000000)) (hi := (271552691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164 / 125) = 1/(125 / 164) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9917 : Bounds (27155269 / 100000000) (271552691 / 1000000000) (Real.log (164 / 125)) := by
  have h := reflection_log_9917_neg
  have he : Real.log (164 / 125) = -Real.log (125 / 164) := by
    rw [show ((164 / 125) : ℝ) = ((125 / 164) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9918_neg : (373966441 / 1000000000) ≤ -Real.log (86 / 125) ∧
    -Real.log (86 / 125) ≤ (186983221 / 500000000) := by
  have h := checkLog_sound (w := (39 / 211)) (n := 12)
    (lo := (373966441 / 1000000000)) (hi := (186983221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 86) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 86) = 1/(86 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9918 : Bounds (-186983221 / 500000000) (-373966441 / 1000000000) (Real.log (86 / 125)) := by
  have h := reflection_log_9918_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9919_neg : (311951 / 1000000000) ≤ -Real.log (125000 / 125039) ∧
    -Real.log (125000 / 125039) ≤ (19497 / 62500000) := by
  have h := checkLog_sound (w := (39 / 250039)) (n := 12)
    (lo := (311951 / 1000000000)) (hi := (19497 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125039 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125039 / 125000) = 1/(125000 / 125039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9919 : Bounds (311951 / 1000000000) (19497 / 62500000) (Real.log (125039 / 125000)) := by
  have h := reflection_log_9919_neg
  have he : Real.log (125039 / 125000) = -Real.log (125000 / 125039) := by
    rw [show ((125039 / 125000) : ℝ) = ((125000 / 125039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0155 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9920_neg : (19503 / 62500000) ≤ -Real.log (124961 / 125000) ∧
    -Real.log (124961 / 125000) ≤ (312049 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 249961)) (n := 12)
    (lo := (19503 / 62500000)) (hi := (312049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124961) = 1/(124961 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9920 : Bounds (-312049 / 1000000000) (-19503 / 62500000) (Real.log (124961 / 125000)) := by
  have h := reflection_log_9920_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9921_neg : (73407203 / 500000000) ≤ -Real.log (1000000 / 1158139) ∧
    -Real.log (1000000 / 1158139) ≤ (146814407 / 1000000000) := by
  have h := checkLog_sound (w := (158139 / 2158139)) (n := 12)
    (lo := (73407203 / 500000000)) (hi := (146814407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1158139 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1158139 / 1000000) = 1/(1000000 / 1158139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9921 : Bounds (73407203 / 500000000) (146814407 / 1000000000) (Real.log (1158139 / 1000000)) := by
  have h := reflection_log_9921_neg
  have he : Real.log (1158139 / 1000000) = -Real.log (1000000 / 1158139) := by
    rw [show ((1158139 / 1000000) : ℝ) = ((1000000 / 1158139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9922_neg : (172140361 / 1000000000) ≤ -Real.log (841861 / 1000000) ∧
    -Real.log (841861 / 1000000) ≤ (86070181 / 500000000) := by
  have h := checkLog_sound (w := (158139 / 1841861)) (n := 12)
    (lo := (172140361 / 1000000000)) (hi := (86070181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 841861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 841861) = 1/(841861 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9922 : Bounds (-86070181 / 500000000) (-172140361 / 1000000000) (Real.log (841861 / 1000000)) := by
  have h := reflection_log_9922_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9923_neg : (36883567 / 250000000) ≤ -Real.log (1000000 / 1158973) ∧
    -Real.log (1000000 / 1158973) ≤ (147534269 / 1000000000) := by
  have h := checkLog_sound (w := (158973 / 2158973)) (n := 12)
    (lo := (36883567 / 250000000)) (hi := (147534269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1158973 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1158973 / 1000000) = 1/(1000000 / 1158973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9923 : Bounds (36883567 / 250000000) (147534269 / 1000000000) (Real.log (1158973 / 1000000)) := by
  have h := reflection_log_9923_neg
  have he : Real.log (1158973 / 1000000) = -Real.log (1000000 / 1158973) := by
    rw [show ((1158973 / 1000000) : ℝ) = ((1000000 / 1158973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9924_neg : (86565757 / 500000000) ≤ -Real.log (841027 / 1000000) ∧
    -Real.log (841027 / 1000000) ≤ (34626303 / 200000000) := by
  have h := checkLog_sound (w := (158973 / 1841027)) (n := 12)
    (lo := (86565757 / 500000000)) (hi := (34626303 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 841027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 841027) = 1/(841027 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9924 : Bounds (-34626303 / 200000000) (-86565757 / 500000000) (Real.log (841027 / 1000000)) := by
  have h := reflection_log_9924_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9925_neg : (12798623 / 500000000) ≤ -Real.log (974727585271 / 1000000000000) ∧
    -Real.log (974727585271 / 1000000000000) ≤ (25597247 / 1000000000) := by
  have h := checkLog_sound (w := (25272414729 / 1974727585271)) (n := 12)
    (lo := (12798623 / 500000000)) (hi := (25597247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974727585271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974727585271) = 1/(974727585271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9925 : Bounds (-25597247 / 1000000000) (-12798623 / 500000000) (Real.log (974727585271 / 1000000000000)) := by
  have h := reflection_log_9925_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9926_neg : (5065191 / 200000000) ≤ -Real.log (974992056679 / 1000000000000) ∧
    -Real.log (974992056679 / 1000000000000) ≤ (6331489 / 250000000) := by
  have h := checkLog_sound (w := (25007943321 / 1974992056679)) (n := 12)
    (lo := (5065191 / 200000000)) (hi := (6331489 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974992056679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974992056679) = 1/(974992056679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9926 : Bounds (-6331489 / 250000000) (-5065191 / 200000000) (Real.log (974992056679 / 1000000000000)) := by
  have h := reflection_log_9926_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9927_neg : (318954767 / 1000000000) ≤ -Real.log (500000000000 / 687844549159) ∧
    -Real.log (500000000000 / 687844549159) ≤ (19934673 / 62500000) := by
  have h := checkLog_sound (w := (187844549159 / 1187844549159)) (n := 12)
    (lo := (318954767 / 1000000000)) (hi := (19934673 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687844549159 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687844549159 / 500000000000) = 1/(500000000000 / 687844549159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9927 : Bounds (318954767 / 1000000000) (19934673 / 62500000) (Real.log (687844549159 / 500000000000)) := by
  have h := reflection_log_9927_neg
  have he : Real.log (687844549159 / 500000000000) = -Real.log (500000000000 / 687844549159) := by
    rw [show ((687844549159 / 500000000000) : ℝ) = ((500000000000 / 687844549159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9928_neg : (320665783 / 1000000000) ≤ -Real.log (250000000000 / 344511234479) ∧
    -Real.log (250000000000 / 344511234479) ≤ (40083223 / 125000000) := by
  have h := checkLog_sound (w := (94511234479 / 594511234479)) (n := 12)
    (lo := (320665783 / 1000000000)) (hi := (40083223 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((344511234479 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(344511234479 / 250000000000) = 1/(250000000000 / 344511234479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9928 : Bounds (320665783 / 1000000000) (40083223 / 125000000) (Real.log (344511234479 / 250000000000)) := by
  have h := reflection_log_9928_neg
  have he : Real.log (344511234479 / 250000000000) = -Real.log (250000000000 / 344511234479) := by
    rw [show ((344511234479 / 250000000000) : ℝ) = ((250000000000 / 344511234479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9929_neg : (160826053 / 250000000) ≤ -Real.log (500000000000 / 951378809869) ∧
    -Real.log (500000000000 / 951378809869) ≤ (643304213 / 1000000000) := by
  have h := checkLog_sound (w := (451378809869 / 1451378809869)) (n := 12)
    (lo := (160826053 / 250000000)) (hi := (643304213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((951378809869 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(951378809869 / 500000000000) = 1/(500000000000 / 951378809869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9929 : Bounds (160826053 / 250000000) (643304213 / 1000000000) (Real.log (951378809869 / 500000000000)) := by
  have h := reflection_log_9929_neg
  have he : Real.log (951378809869 / 500000000000) = -Real.log (500000000000 / 951378809869) := by
    rw [show ((951378809869 / 500000000000) : ℝ) = ((500000000000 / 951378809869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9930_neg : (645519131 / 1000000000) ≤ -Real.log (250000000000 / 476744186047) ∧
    -Real.log (250000000000 / 476744186047) ≤ (161379783 / 250000000) := by
  have h := checkLog_sound (w := (226744186047 / 726744186047)) (n := 12)
    (lo := (645519131 / 1000000000)) (hi := (161379783 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((476744186047 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(476744186047 / 250000000000) = 1/(250000000000 / 476744186047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9930 : Bounds (645519131 / 1000000000) (161379783 / 250000000) (Real.log (476744186047 / 250000000000)) := by
  have h := reflection_log_9930_neg
  have he : Real.log (476744186047 / 250000000000) = -Real.log (250000000000 / 476744186047) := by
    rw [show ((476744186047 / 250000000000) : ℝ) = ((250000000000 / 476744186047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9931_neg : (54462919 / 200000000) ≤ -Real.log (1000 / 1313) ∧
    -Real.log (1000 / 1313) ≤ (68078649 / 250000000) := by
  have h := checkLog_sound (w := (313 / 2313)) (n := 12)
    (lo := (54462919 / 200000000)) (hi := (68078649 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1313 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1313 / 1000) = 1/(1000 / 1313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9931 : Bounds (54462919 / 200000000) (68078649 / 250000000) (Real.log (1313 / 1000)) := by
  have h := reflection_log_9931_neg
  have he : Real.log (1313 / 1000) = -Real.log (1000 / 1313) := by
    rw [show ((1313 / 1000) : ℝ) = ((1000 / 1313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9932_neg : (187710493 / 500000000) ≤ -Real.log (687 / 1000) ∧
    -Real.log (687 / 1000) ≤ (375420987 / 1000000000) := by
  have h := checkLog_sound (w := (313 / 1687)) (n := 12)
    (lo := (187710493 / 500000000)) (hi := (375420987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 687) = 1/(687 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9932 : Bounds (-375420987 / 1000000000) (-187710493 / 500000000) (Real.log (687 / 1000)) := by
  have h := reflection_log_9932_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9933_neg : (312951 / 1000000000) ≤ -Real.log (1000000 / 1000313) ∧
    -Real.log (1000000 / 1000313) ≤ (39119 / 125000000) := by
  have h := checkLog_sound (w := (313 / 2000313)) (n := 12)
    (lo := (312951 / 1000000000)) (hi := (39119 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000313 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000313 / 1000000) = 1/(1000000 / 1000313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9933 : Bounds (312951 / 1000000000) (39119 / 125000000) (Real.log (1000313 / 1000000)) := by
  have h := reflection_log_9933_neg
  have he : Real.log (1000313 / 1000000) = -Real.log (1000000 / 1000313) := by
    rw [show ((1000313 / 1000000) : ℝ) = ((1000000 / 1000313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9934_neg : (39131 / 125000000) ≤ -Real.log (999687 / 1000000) ∧
    -Real.log (999687 / 1000000) ≤ (313049 / 1000000000) := by
  have h := checkLog_sound (w := (313 / 1999687)) (n := 12)
    (lo := (39131 / 125000000)) (hi := (313049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999687) = 1/(999687 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9934 : Bounds (-313049 / 1000000000) (-39131 / 125000000) (Real.log (999687 / 1000000)) := by
  have h := reflection_log_9934_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9935_neg : (147269343 / 1000000000) ≤ -Real.log (500000 / 579333) ∧
    -Real.log (500000 / 579333) ≤ (4602167 / 31250000) := by
  have h := checkLog_sound (w := (79333 / 1079333)) (n := 12)
    (lo := (147269343 / 1000000000)) (hi := (4602167 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((579333 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(579333 / 500000) = 1/(500000 / 579333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9935 : Bounds (147269343 / 1000000000) (4602167 / 31250000) (Real.log (579333 / 500000)) := by
  have h := reflection_log_9935_neg
  have he : Real.log (579333 / 500000) = -Real.log (500000 / 579333) := by
    rw [show ((579333 / 500000) : ℝ) = ((500000 / 579333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9936_neg : (172766551 / 1000000000) ≤ -Real.log (420667 / 500000) ∧
    -Real.log (420667 / 500000) ≤ (21595819 / 125000000) := by
  have h := checkLog_sound (w := (79333 / 920667)) (n := 12)
    (lo := (172766551 / 1000000000)) (hi := (21595819 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 420667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 420667) = 1/(420667 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9936 : Bounds (-21595819 / 125000000) (-172766551 / 1000000000) (Real.log (420667 / 500000)) := by
  have h := reflection_log_9936_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9937_neg : (73995301 / 500000000) ≤ -Real.log (500000 / 579751) ∧
    -Real.log (500000 / 579751) ≤ (147990603 / 1000000000) := by
  have h := checkLog_sound (w := (79751 / 1079751)) (n := 12)
    (lo := (73995301 / 500000000)) (hi := (147990603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((579751 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(579751 / 500000) = 1/(500000 / 579751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9937 : Bounds (73995301 / 500000000) (147990603 / 1000000000) (Real.log (579751 / 500000)) := by
  have h := reflection_log_9937_neg
  have he : Real.log (579751 / 500000) = -Real.log (500000 / 579751) := by
    rw [show ((579751 / 500000) : ℝ) = ((500000 / 579751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9938_neg : (34752141 / 200000000) ≤ -Real.log (420249 / 500000) ∧
    -Real.log (420249 / 500000) ≤ (86880353 / 500000000) := by
  have h := checkLog_sound (w := (79751 / 920249)) (n := 12)
    (lo := (34752141 / 200000000)) (hi := (86880353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 420249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 420249) = 1/(420249 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9938 : Bounds (-86880353 / 500000000) (-34752141 / 200000000) (Real.log (420249 / 500000)) := by
  have h := reflection_log_9938_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9939_neg : (25770103 / 1000000000) ≤ -Real.log (243639777999 / 250000000000) ∧
    -Real.log (243639777999 / 250000000000) ≤ (3221263 / 125000000) := by
  have h := checkLog_sound (w := (6360222001 / 493639777999)) (n := 12)
    (lo := (25770103 / 1000000000)) (hi := (3221263 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243639777999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243639777999) = 1/(243639777999 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9939 : Bounds (-3221263 / 125000000) (-25770103 / 1000000000) (Real.log (243639777999 / 250000000000)) := by
  have h := reflection_log_9939_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9940_neg : (3187151 / 125000000) ≤ -Real.log (243706275111 / 250000000000) ∧
    -Real.log (243706275111 / 250000000000) ≤ (25497209 / 1000000000) := by
  have h := checkLog_sound (w := (6293724889 / 493706275111)) (n := 12)
    (lo := (3187151 / 125000000)) (hi := (25497209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243706275111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243706275111) = 1/(243706275111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9940 : Bounds (-25497209 / 1000000000) (-3187151 / 125000000) (Real.log (243706275111 / 250000000000)) := by
  have h := reflection_log_9940_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9941_neg : (160017947 / 500000000) ≤ -Real.log (250000000000 / 344294299291) ∧
    -Real.log (250000000000 / 344294299291) ≤ (64007179 / 200000000) := by
  have h := checkLog_sound (w := (94294299291 / 594294299291)) (n := 12)
    (lo := (160017947 / 500000000)) (hi := (64007179 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((344294299291 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(344294299291 / 250000000000) = 1/(250000000000 / 344294299291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9941 : Bounds (160017947 / 500000000) (64007179 / 200000000) (Real.log (344294299291 / 250000000000)) := by
  have h := reflection_log_9941_neg
  have he : Real.log (344294299291 / 250000000000) = -Real.log (250000000000 / 344294299291) := by
    rw [show ((344294299291 / 250000000000) : ℝ) = ((250000000000 / 344294299291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9942_neg : (80437827 / 250000000) ≤ -Real.log (62500000000 / 86221353293) ∧
    -Real.log (62500000000 / 86221353293) ≤ (321751309 / 1000000000) := by
  have h := checkLog_sound (w := (23721353293 / 148721353293)) (n := 12)
    (lo := (80437827 / 250000000)) (hi := (321751309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86221353293 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86221353293 / 62500000000) = 1/(62500000000 / 86221353293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9942 : Bounds (80437827 / 250000000) (321751309 / 1000000000) (Real.log (86221353293 / 62500000000)) := by
  have h := reflection_log_9942_neg
  have he : Real.log (86221353293 / 62500000000) = -Real.log (62500000000 / 86221353293) := by
    rw [show ((86221353293 / 62500000000) : ℝ) = ((62500000000 / 86221353293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9943_neg : (645519131 / 1000000000) ≤ -Real.log (500000000000 / 953488372093) ∧
    -Real.log (500000000000 / 953488372093) ≤ (161379783 / 250000000) := by
  have h := checkLog_sound (w := (453488372093 / 1453488372093)) (n := 12)
    (lo := (645519131 / 1000000000)) (hi := (161379783 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((953488372093 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(953488372093 / 500000000000) = 1/(500000000000 / 953488372093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9943 : Bounds (645519131 / 1000000000) (161379783 / 250000000) (Real.log (953488372093 / 500000000000)) := by
  have h := reflection_log_9943_neg
  have he : Real.log (953488372093 / 500000000000) = -Real.log (500000000000 / 953488372093) := by
    rw [show ((953488372093 / 500000000000) : ℝ) = ((500000000000 / 953488372093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9944_neg : (323867791 / 500000000) ≤ -Real.log (125000000000 / 238901018923) ∧
    -Real.log (125000000000 / 238901018923) ≤ (647735583 / 1000000000) := by
  have h := checkLog_sound (w := (113901018923 / 363901018923)) (n := 12)
    (lo := (323867791 / 500000000)) (hi := (647735583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((238901018923 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(238901018923 / 125000000000) = 1/(125000000000 / 238901018923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9944 : Bounds (323867791 / 500000000) (647735583 / 1000000000) (Real.log (238901018923 / 125000000000)) := by
  have h := reflection_log_9944_neg
  have he : Real.log (238901018923 / 125000000000) = -Real.log (125000000000 / 238901018923) := by
    rw [show ((238901018923 / 125000000000) : ℝ) = ((125000000000 / 238901018923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9945_neg : (3413449 / 12500000) ≤ -Real.log (500 / 657) ∧
    -Real.log (500 / 657) ≤ (273075921 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 1157)) (n := 12)
    (lo := (3413449 / 12500000)) (hi := (273075921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657 / 500) = 1/(500 / 657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9945 : Bounds (3413449 / 12500000) (273075921 / 1000000000) (Real.log (657 / 500)) := by
  have h := reflection_log_9945_neg
  have he : Real.log (657 / 500) = -Real.log (500 / 657) := by
    rw [show ((657 / 500) : ℝ) = ((500 / 657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9946_neg : (376877651 / 1000000000) ≤ -Real.log (343 / 500) ∧
    -Real.log (343 / 500) ≤ (94219413 / 250000000) := by
  have h := checkLog_sound (w := (157 / 843)) (n := 12)
    (lo := (376877651 / 1000000000)) (hi := (94219413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 343) = 1/(343 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9946 : Bounds (-94219413 / 250000000) (-376877651 / 1000000000) (Real.log (343 / 500)) := by
  have h := reflection_log_9946_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9947_neg : (6279 / 20000000) ≤ -Real.log (500000 / 500157) ∧
    -Real.log (500000 / 500157) ≤ (313951 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 1000157)) (n := 12)
    (lo := (6279 / 20000000)) (hi := (313951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500157 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500157 / 500000) = 1/(500000 / 500157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9947 : Bounds (6279 / 20000000) (313951 / 1000000000) (Real.log (500157 / 500000)) := by
  have h := reflection_log_9947_neg
  have he : Real.log (500157 / 500000) = -Real.log (500000 / 500157) := by
    rw [show ((500157 / 500000) : ℝ) = ((500000 / 500157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9948_neg : (314049 / 1000000000) ≤ -Real.log (499843 / 500000) ∧
    -Real.log (499843 / 500000) ≤ (6281 / 20000000) := by
  have h := checkLog_sound (w := (157 / 999843)) (n := 12)
    (lo := (314049 / 1000000000)) (hi := (6281 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499843) = 1/(499843 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9948 : Bounds (-6281 / 20000000) (-314049 / 1000000000) (Real.log (499843 / 500000)) := by
  have h := reflection_log_9948_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9949_neg : (147724073 / 1000000000) ≤ -Real.log (1000000 / 1159193) ∧
    -Real.log (1000000 / 1159193) ≤ (73862037 / 500000000) := by
  have h := checkLog_sound (w := (159193 / 2159193)) (n := 12)
    (lo := (147724073 / 1000000000)) (hi := (73862037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1159193 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1159193 / 1000000) = 1/(1000000 / 1159193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9949 : Bounds (147724073 / 1000000000) (73862037 / 500000000) (Real.log (1159193 / 1000000)) := by
  have h := reflection_log_9949_neg
  have he : Real.log (1159193 / 1000000) = -Real.log (1000000 / 1159193) := by
    rw [show ((1159193 / 1000000) : ℝ) = ((1000000 / 1159193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9950_neg : (86696567 / 500000000) ≤ -Real.log (840807 / 1000000) ∧
    -Real.log (840807 / 1000000) ≤ (34678627 / 200000000) := by
  have h := checkLog_sound (w := (159193 / 1840807)) (n := 12)
    (lo := (86696567 / 500000000)) (hi := (34678627 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 840807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 840807) = 1/(840807 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9950 : Bounds (-34678627 / 200000000) (-86696567 / 500000000) (Real.log (840807 / 1000000)) := by
  have h := reflection_log_9950_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9951_neg : (74222933 / 500000000) ≤ -Real.log (100000 / 116003) ∧
    -Real.log (100000 / 116003) ≤ (148445867 / 1000000000) := by
  have h := checkLog_sound (w := (16003 / 216003)) (n := 12)
    (lo := (74222933 / 500000000)) (hi := (148445867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116003 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(116003 / 100000) = 1/(100000 / 116003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9951 : Bounds (74222933 / 500000000) (148445867 / 1000000000) (Real.log (116003 / 100000)) := by
  have h := reflection_log_9951_neg
  have he : Real.log (116003 / 100000) = -Real.log (100000 / 116003) := by
    rw [show ((116003 / 100000) : ℝ) = ((100000 / 116003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9952_neg : (87194551 / 500000000) ≤ -Real.log (83997 / 100000) ∧
    -Real.log (83997 / 100000) ≤ (174389103 / 1000000000) := by
  have h := checkLog_sound (w := (16003 / 183997)) (n := 12)
    (lo := (87194551 / 500000000)) (hi := (174389103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 83997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 83997) = 1/(83997 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9952 : Bounds (-174389103 / 1000000000) (-87194551 / 500000000) (Real.log (83997 / 100000)) := by
  have h := reflection_log_9952_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9953_neg : (5188647 / 200000000) ≤ -Real.log (9743903991 / 10000000000) ∧
    -Real.log (9743903991 / 10000000000) ≤ (6485809 / 250000000) := by
  have h := checkLog_sound (w := (256096009 / 19743903991)) (n := 12)
    (lo := (5188647 / 200000000)) (hi := (6485809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9743903991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9743903991) = 1/(9743903991 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9953 : Bounds (-6485809 / 250000000) (-5188647 / 200000000) (Real.log (9743903991 / 10000000000)) := by
  have h := reflection_log_9953_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9954_neg : (1283453 / 50000000) ≤ -Real.log (974657588751 / 1000000000000) ∧
    -Real.log (974657588751 / 1000000000000) ≤ (25669061 / 1000000000) := by
  have h := checkLog_sound (w := (25342411249 / 1974657588751)) (n := 12)
    (lo := (1283453 / 50000000)) (hi := (25669061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974657588751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974657588751) = 1/(974657588751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9954 : Bounds (-25669061 / 1000000000) (-1283453 / 50000000) (Real.log (974657588751 / 1000000000000)) := by
  have h := reflection_log_9954_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9955_neg : (321117207 / 1000000000) ≤ -Real.log (250000000000 / 344666790357) ∧
    -Real.log (250000000000 / 344666790357) ≤ (40139651 / 125000000) := by
  have h := checkLog_sound (w := (94666790357 / 594666790357)) (n := 12)
    (lo := (321117207 / 1000000000)) (hi := (40139651 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((344666790357 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(344666790357 / 250000000000) = 1/(250000000000 / 344666790357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9955 : Bounds (321117207 / 1000000000) (40139651 / 125000000) (Real.log (344666790357 / 250000000000)) := by
  have h := reflection_log_9955_neg
  have he : Real.log (344666790357 / 250000000000) = -Real.log (250000000000 / 344666790357) := by
    rw [show ((344666790357 / 250000000000) : ℝ) = ((250000000000 / 344666790357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9956_neg : (40354371 / 125000000) ≤ -Real.log (250000000000 / 345259354501) ∧
    -Real.log (250000000000 / 345259354501) ≤ (322834969 / 1000000000) := by
  have h := checkLog_sound (w := (95259354501 / 595259354501)) (n := 12)
    (lo := (40354371 / 125000000)) (hi := (322834969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((345259354501 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(345259354501 / 250000000000) = 1/(250000000000 / 345259354501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9956 : Bounds (40354371 / 125000000) (322834969 / 1000000000) (Real.log (345259354501 / 250000000000)) := by
  have h := reflection_log_9956_neg
  have he : Real.log (345259354501 / 250000000000) = -Real.log (250000000000 / 345259354501) := by
    rw [show ((345259354501 / 250000000000) : ℝ) = ((250000000000 / 345259354501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9957_neg : (323867791 / 500000000) ≤ -Real.log (500000000000 / 955604075691) ∧
    -Real.log (500000000000 / 955604075691) ≤ (647735583 / 1000000000) := by
  have h := checkLog_sound (w := (455604075691 / 1455604075691)) (n := 12)
    (lo := (323867791 / 500000000)) (hi := (647735583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((955604075691 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(955604075691 / 500000000000) = 1/(500000000000 / 955604075691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9957 : Bounds (323867791 / 500000000) (647735583 / 1000000000) (Real.log (955604075691 / 500000000000)) := by
  have h := reflection_log_9957_neg
  have he : Real.log (955604075691 / 500000000000) = -Real.log (500000000000 / 955604075691) := by
    rw [show ((955604075691 / 500000000000) : ℝ) = ((500000000000 / 955604075691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9958_neg : (649953571 / 1000000000) ≤ -Real.log (250000000000 / 478862973761) ∧
    -Real.log (250000000000 / 478862973761) ≤ (162488393 / 250000000) := by
  have h := checkLog_sound (w := (228862973761 / 728862973761)) (n := 12)
    (lo := (649953571 / 1000000000)) (hi := (162488393 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((478862973761 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(478862973761 / 250000000000) = 1/(250000000000 / 478862973761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9958 : Bounds (649953571 / 1000000000) (162488393 / 250000000) (Real.log (478862973761 / 250000000000)) := by
  have h := reflection_log_9958_neg
  have he : Real.log (478862973761 / 250000000000) = -Real.log (250000000000 / 478862973761) := by
    rw [show ((478862973761 / 250000000000) : ℝ) = ((250000000000 / 478862973761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9959_neg : (54767333 / 200000000) ≤ -Real.log (200 / 263) ∧
    -Real.log (200 / 263) ≤ (136918333 / 500000000) := by
  have h := checkLog_sound (w := (63 / 463)) (n := 12)
    (lo := (54767333 / 200000000)) (hi := (136918333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((263 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(263 / 200) = 1/(200 / 263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9959 : Bounds (54767333 / 200000000) (136918333 / 500000000) (Real.log (263 / 200)) := by
  have h := reflection_log_9959_neg
  have he : Real.log (263 / 200) = -Real.log (200 / 263) := by
    rw [show ((263 / 200) : ℝ) = ((200 / 263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9960_neg : (9458411 / 25000000) ≤ -Real.log (137 / 200) ∧
    -Real.log (137 / 200) ≤ (378336441 / 1000000000) := by
  have h := checkLog_sound (w := (63 / 337)) (n := 12)
    (lo := (9458411 / 25000000)) (hi := (378336441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 137) = 1/(137 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9960 : Bounds (-378336441 / 1000000000) (-9458411 / 25000000) (Real.log (137 / 200)) := by
  have h := reflection_log_9960_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9961_neg : (6299 / 20000000) ≤ -Real.log (200000 / 200063) ∧
    -Real.log (200000 / 200063) ≤ (314951 / 1000000000) := by
  have h := checkLog_sound (w := (63 / 400063)) (n := 12)
    (lo := (6299 / 20000000)) (hi := (314951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200063 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200063 / 200000) = 1/(200000 / 200063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9961 : Bounds (6299 / 20000000) (314951 / 1000000000) (Real.log (200063 / 200000)) := by
  have h := reflection_log_9961_neg
  have he : Real.log (200063 / 200000) = -Real.log (200000 / 200063) := by
    rw [show ((200063 / 200000) : ℝ) = ((200000 / 200063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9962_neg : (315049 / 1000000000) ≤ -Real.log (199937 / 200000) ∧
    -Real.log (199937 / 200000) ≤ (6301 / 20000000) := by
  have h := checkLog_sound (w := (63 / 399937)) (n := 12)
    (lo := (315049 / 1000000000)) (hi := (6301 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199937) = 1/(199937 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9962 : Bounds (-6301 / 20000000) (-315049 / 1000000000) (Real.log (199937 / 200000)) := by
  have h := reflection_log_9962_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9963_neg : (74089729 / 500000000) ≤ -Real.log (1000000 / 1159721) ∧
    -Real.log (1000000 / 1159721) ≤ (148179459 / 1000000000) := by
  have h := checkLog_sound (w := (159721 / 2159721)) (n := 12)
    (lo := (74089729 / 500000000)) (hi := (148179459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1159721 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1159721 / 1000000) = 1/(1000000 / 1159721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9963 : Bounds (74089729 / 500000000) (148179459 / 1000000000) (Real.log (1159721 / 1000000)) := by
  have h := reflection_log_9963_neg
  have he : Real.log (1159721 / 1000000) = -Real.log (1000000 / 1159721) := by
    rw [show ((1159721 / 1000000) : ℝ) = ((1000000 / 1159721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9964_neg : (174021299 / 1000000000) ≤ -Real.log (840279 / 1000000) ∧
    -Real.log (840279 / 1000000) ≤ (1740213 / 10000000) := by
  have h := checkLog_sound (w := (159721 / 1840279)) (n := 12)
    (lo := (174021299 / 1000000000)) (hi := (1740213 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 840279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 840279) = 1/(840279 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9964 : Bounds (-1740213 / 10000000) (-174021299 / 1000000000) (Real.log (840279 / 1000000)) := by
  have h := reflection_log_9964_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9965_neg : (29780357 / 200000000) ≤ -Real.log (1000000 / 1160559) ∧
    -Real.log (1000000 / 1160559) ≤ (74450893 / 500000000) := by
  have h := checkLog_sound (w := (160559 / 2160559)) (n := 12)
    (lo := (29780357 / 200000000)) (hi := (74450893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1160559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1160559 / 1000000) = 1/(1000000 / 1160559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9965 : Bounds (29780357 / 200000000) (74450893 / 500000000) (Real.log (1160559 / 1000000)) := by
  have h := reflection_log_9965_neg
  have he : Real.log (1160559 / 1000000) = -Real.log (1000000 / 1160559) := by
    rw [show ((1160559 / 1000000) : ℝ) = ((1000000 / 1160559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9966_neg : (43754771 / 250000000) ≤ -Real.log (839441 / 1000000) ∧
    -Real.log (839441 / 1000000) ≤ (35003817 / 200000000) := by
  have h := checkLog_sound (w := (160559 / 1839441)) (n := 12)
    (lo := (43754771 / 250000000)) (hi := (35003817 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 839441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 839441) = 1/(839441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9966 : Bounds (-35003817 / 200000000) (-43754771 / 250000000) (Real.log (839441 / 1000000)) := by
  have h := reflection_log_9966_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9967_neg : (26117299 / 1000000000) ≤ -Real.log (974220807519 / 1000000000000) ∧
    -Real.log (974220807519 / 1000000000000) ≤ (261173 / 10000000) := by
  have h := checkLog_sound (w := (25779192481 / 1974220807519)) (n := 12)
    (lo := (26117299 / 1000000000)) (hi := (261173 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974220807519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974220807519) = 1/(974220807519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9967 : Bounds (-261173 / 10000000) (-26117299 / 1000000000) (Real.log (974220807519 / 1000000000000)) := by
  have h := reflection_log_9967_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9968_neg : (323023 / 12500000) ≤ -Real.log (974489202159 / 1000000000000) ∧
    -Real.log (974489202159 / 1000000000000) ≤ (25841841 / 1000000000) := by
  have h := checkLog_sound (w := (25510797841 / 1974489202159)) (n := 12)
    (lo := (323023 / 12500000)) (hi := (25841841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974489202159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974489202159) = 1/(974489202159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9968 : Bounds (-25841841 / 1000000000) (-323023 / 12500000) (Real.log (974489202159 / 1000000000000)) := by
  have h := reflection_log_9968_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9969_neg : (161100379 / 500000000) ≤ -Real.log (500000000000 / 690080913601) ∧
    -Real.log (500000000000 / 690080913601) ≤ (322200759 / 1000000000) := by
  have h := checkLog_sound (w := (190080913601 / 1190080913601)) (n := 12)
    (lo := (161100379 / 500000000)) (hi := (322200759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((690080913601 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(690080913601 / 500000000000) = 1/(500000000000 / 690080913601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9969 : Bounds (161100379 / 500000000) (322200759 / 1000000000) (Real.log (690080913601 / 500000000000)) := by
  have h := reflection_log_9969_neg
  have he : Real.log (690080913601 / 500000000000) = -Real.log (500000000000 / 690080913601) := by
    rw [show ((690080913601 / 500000000000) : ℝ) = ((500000000000 / 690080913601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9970_neg : (32392087 / 100000000) ≤ -Real.log (1250000000 / 1728172379) ∧
    -Real.log (1250000000 / 1728172379) ≤ (323920871 / 1000000000) := by
  have h := checkLog_sound (w := (478172379 / 2978172379)) (n := 12)
    (lo := (32392087 / 100000000)) (hi := (323920871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1728172379 / 1250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1728172379 / 1250000000) = 1/(1250000000 / 1728172379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9970 : Bounds (32392087 / 100000000) (323920871 / 1000000000) (Real.log (1728172379 / 1250000000)) := by
  have h := reflection_log_9970_neg
  have he : Real.log (1728172379 / 1250000000) = -Real.log (1250000000 / 1728172379) := by
    rw [show ((1728172379 / 1250000000) : ℝ) = ((1250000000 / 1728172379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9971_neg : (649953571 / 1000000000) ≤ -Real.log (500000000000 / 957725947521) ∧
    -Real.log (500000000000 / 957725947521) ≤ (162488393 / 250000000) := by
  have h := checkLog_sound (w := (457725947521 / 1457725947521)) (n := 12)
    (lo := (649953571 / 1000000000)) (hi := (162488393 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((957725947521 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(957725947521 / 500000000000) = 1/(500000000000 / 957725947521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9971 : Bounds (649953571 / 1000000000) (162488393 / 250000000) (Real.log (957725947521 / 500000000000)) := by
  have h := reflection_log_9971_neg
  have he : Real.log (957725947521 / 500000000000) = -Real.log (500000000000 / 957725947521) := by
    rw [show ((957725947521 / 500000000000) : ℝ) = ((500000000000 / 957725947521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9972_neg : (326086553 / 500000000) ≤ -Real.log (500000000000 / 959854014599) ∧
    -Real.log (500000000000 / 959854014599) ≤ (652173107 / 1000000000) := by
  have h := checkLog_sound (w := (459854014599 / 1459854014599)) (n := 12)
    (lo := (326086553 / 500000000)) (hi := (652173107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((959854014599 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(959854014599 / 500000000000) = 1/(500000000000 / 959854014599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9972 : Bounds (326086553 / 500000000) (652173107 / 1000000000) (Real.log (959854014599 / 500000000000)) := by
  have h := reflection_log_9972_neg
  have he : Real.log (959854014599 / 500000000000) = -Real.log (500000000000 / 959854014599) := by
    rw [show ((959854014599 / 500000000000) : ℝ) = ((500000000000 / 959854014599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9973_neg : (8581151 / 31250000) ≤ -Real.log (250 / 329) ∧
    -Real.log (250 / 329) ≤ (274596833 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 579)) (n := 12)
    (lo := (8581151 / 31250000)) (hi := (274596833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329 / 250) = 1/(250 / 329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9973 : Bounds (8581151 / 31250000) (274596833 / 1000000000) (Real.log (329 / 250)) := by
  have h := reflection_log_9973_neg
  have he : Real.log (329 / 250) = -Real.log (250 / 329) := by
    rw [show ((329 / 250) : ℝ) = ((250 / 329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9974_neg : (379797361 / 1000000000) ≤ -Real.log (171 / 250) ∧
    -Real.log (171 / 250) ≤ (189898681 / 500000000) := by
  have h := checkLog_sound (w := (79 / 421)) (n := 12)
    (lo := (379797361 / 1000000000)) (hi := (189898681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 171) = 1/(171 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9974 : Bounds (-189898681 / 500000000) (-379797361 / 1000000000) (Real.log (171 / 250)) := by
  have h := reflection_log_9974_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9975_neg : (6319 / 20000000) ≤ -Real.log (250000 / 250079) ∧
    -Real.log (250000 / 250079) ≤ (315951 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 500079)) (n := 12)
    (lo := (6319 / 20000000)) (hi := (315951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250079 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250079 / 250000) = 1/(250000 / 250079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9975 : Bounds (6319 / 20000000) (315951 / 1000000000) (Real.log (250079 / 250000)) := by
  have h := reflection_log_9975_neg
  have he : Real.log (250079 / 250000) = -Real.log (250000 / 250079) := by
    rw [show ((250079 / 250000) : ℝ) = ((250000 / 250079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9976_neg : (316049 / 1000000000) ≤ -Real.log (249921 / 250000) ∧
    -Real.log (249921 / 250000) ≤ (6321 / 20000000) := by
  have h := checkLog_sound (w := (79 / 499921)) (n := 12)
    (lo := (316049 / 1000000000)) (hi := (6321 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249921) = 1/(249921 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9976 : Bounds (-6321 / 20000000) (-316049 / 1000000000) (Real.log (249921 / 250000)) := by
  have h := reflection_log_9976_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9977_neg : (148634637 / 1000000000) ≤ -Real.log (1000000 / 1160249) ∧
    -Real.log (1000000 / 1160249) ≤ (74317319 / 500000000) := by
  have h := checkLog_sound (w := (160249 / 2160249)) (n := 12)
    (lo := (148634637 / 1000000000)) (hi := (74317319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1160249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1160249 / 1000000) = 1/(1000000 / 1160249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9977 : Bounds (148634637 / 1000000000) (74317319 / 500000000) (Real.log (1160249 / 1000000)) := by
  have h := reflection_log_9977_neg
  have he : Real.log (1160249 / 1000000) = -Real.log (1000000 / 1160249) := by
    rw [show ((1160249 / 1000000) : ℝ) = ((1000000 / 1160249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9978_neg : (174649859 / 1000000000) ≤ -Real.log (839751 / 1000000) ∧
    -Real.log (839751 / 1000000) ≤ (8732493 / 50000000) := by
  have h := checkLog_sound (w := (160249 / 1839751)) (n := 12)
    (lo := (174649859 / 1000000000)) (hi := (8732493 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 839751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 839751) = 1/(839751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9978 : Bounds (-8732493 / 50000000) (-174649859 / 1000000000) (Real.log (839751 / 1000000)) := by
  have h := reflection_log_9978_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9979_neg : (29871327 / 200000000) ≤ -Real.log (1000000 / 1161087) ∧
    -Real.log (1000000 / 1161087) ≤ (37339159 / 250000000) := by
  have h := checkLog_sound (w := (161087 / 2161087)) (n := 12)
    (lo := (29871327 / 200000000)) (hi := (37339159 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161087 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1161087 / 1000000) = 1/(1000000 / 1161087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9979 : Bounds (29871327 / 200000000) (37339159 / 250000000) (Real.log (1161087 / 1000000)) := by
  have h := reflection_log_9979_neg
  have he : Real.log (1161087 / 1000000) = -Real.log (1000000 / 1161087) := by
    rw [show ((1161087 / 1000000) : ℝ) = ((1000000 / 1161087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9980_neg : (10978017 / 62500000) ≤ -Real.log (838913 / 1000000) ∧
    -Real.log (838913 / 1000000) ≤ (175648273 / 1000000000) := by
  have h := checkLog_sound (w := (161087 / 1838913)) (n := 12)
    (lo := (10978017 / 62500000)) (hi := (175648273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 838913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 838913) = 1/(838913 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9980 : Bounds (-175648273 / 1000000000) (-10978017 / 62500000) (Real.log (838913 / 1000000)) := by
  have h := reflection_log_9980_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9981_neg : (26291637 / 1000000000) ≤ -Real.log (974050978431 / 1000000000000) ∧
    -Real.log (974050978431 / 1000000000000) ≤ (13145819 / 500000000) := by
  have h := checkLog_sound (w := (25949021569 / 1974050978431)) (n := 12)
    (lo := (26291637 / 1000000000)) (hi := (13145819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974050978431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974050978431) = 1/(974050978431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9981 : Bounds (-13145819 / 500000000) (-26291637 / 1000000000) (Real.log (974050978431 / 1000000000000)) := by
  have h := reflection_log_9981_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9982_neg : (13007611 / 500000000) ≤ -Real.log (974320257999 / 1000000000000) ∧
    -Real.log (974320257999 / 1000000000000) ≤ (26015223 / 1000000000) := by
  have h := checkLog_sound (w := (25679742001 / 1974320257999)) (n := 12)
    (lo := (13007611 / 500000000)) (hi := (26015223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974320257999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974320257999) = 1/(974320257999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9982 : Bounds (-26015223 / 1000000000) (-13007611 / 500000000) (Real.log (974320257999 / 1000000000000)) := by
  have h := reflection_log_9982_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9983_neg : (20205281 / 62500000) ≤ -Real.log (50000000000 / 69082918627) ∧
    -Real.log (50000000000 / 69082918627) ≤ (323284497 / 1000000000) := by
  have h := checkLog_sound (w := (19082918627 / 119082918627)) (n := 12)
    (lo := (20205281 / 62500000)) (hi := (323284497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69082918627 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69082918627 / 50000000000) = 1/(50000000000 / 69082918627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9983 : Bounds (20205281 / 62500000) (323284497 / 1000000000) (Real.log (69082918627 / 50000000000)) := by
  have h := reflection_log_9983_neg
  have he : Real.log (69082918627 / 50000000000) = -Real.log (50000000000 / 69082918627) := by
    rw [show ((69082918627 / 50000000000) : ℝ) = ((50000000000 / 69082918627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0156 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9984_neg : (81251227 / 250000000) ≤ -Real.log (250000000000 / 346009359731) ∧
    -Real.log (250000000000 / 346009359731) ≤ (325004909 / 1000000000) := by
  have h := checkLog_sound (w := (96009359731 / 596009359731)) (n := 12)
    (lo := (81251227 / 250000000)) (hi := (325004909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((346009359731 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(346009359731 / 250000000000) = 1/(250000000000 / 346009359731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9984 : Bounds (81251227 / 250000000) (325004909 / 1000000000) (Real.log (346009359731 / 250000000000)) := by
  have h := reflection_log_9984_neg
  have he : Real.log (346009359731 / 250000000000) = -Real.log (250000000000 / 346009359731) := by
    rw [show ((346009359731 / 250000000000) : ℝ) = ((250000000000 / 346009359731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9985_neg : (326086553 / 500000000) ≤ -Real.log (250000000000 / 479927007299) ∧
    -Real.log (250000000000 / 479927007299) ≤ (652173107 / 1000000000) := by
  have h := checkLog_sound (w := (229927007299 / 729927007299)) (n := 12)
    (lo := (326086553 / 500000000)) (hi := (652173107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((479927007299 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(479927007299 / 250000000000) = 1/(250000000000 / 479927007299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9985 : Bounds (326086553 / 500000000) (652173107 / 1000000000) (Real.log (479927007299 / 250000000000)) := by
  have h := reflection_log_9985_neg
  have he : Real.log (479927007299 / 250000000000) = -Real.log (250000000000 / 479927007299) := by
    rw [show ((479927007299 / 250000000000) : ℝ) = ((250000000000 / 479927007299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9986_neg : (327197097 / 500000000) ≤ -Real.log (250000000000 / 480994152047) ∧
    -Real.log (250000000000 / 480994152047) ≤ (130878839 / 200000000) := by
  have h := checkLog_sound (w := (230994152047 / 730994152047)) (n := 12)
    (lo := (327197097 / 500000000)) (hi := (130878839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((480994152047 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(480994152047 / 250000000000) = 1/(250000000000 / 480994152047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9986 : Bounds (327197097 / 500000000) (130878839 / 200000000) (Real.log (480994152047 / 250000000000)) := by
  have h := reflection_log_9986_neg
  have he : Real.log (480994152047 / 250000000000) = -Real.log (250000000000 / 480994152047) := by
    rw [show ((480994152047 / 250000000000) : ℝ) = ((250000000000 / 480994152047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9987_neg : (137678211 / 500000000) ≤ -Real.log (1000 / 1317) ∧
    -Real.log (1000 / 1317) ≤ (275356423 / 1000000000) := by
  have h := checkLog_sound (w := (317 / 2317)) (n := 12)
    (lo := (137678211 / 500000000)) (hi := (275356423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1317 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1317 / 1000) = 1/(1000 / 1317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9987 : Bounds (137678211 / 500000000) (275356423 / 1000000000) (Real.log (1317 / 1000)) := by
  have h := reflection_log_9987_neg
  have he : Real.log (1317 / 1000) = -Real.log (1000 / 1317) := by
    rw [show ((1317 / 1000) : ℝ) = ((1000 / 1317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9988_neg : (381260419 / 1000000000) ≤ -Real.log (683 / 1000) ∧
    -Real.log (683 / 1000) ≤ (19063021 / 50000000) := by
  have h := checkLog_sound (w := (317 / 1683)) (n := 12)
    (lo := (381260419 / 1000000000)) (hi := (19063021 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 683) = 1/(683 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9988 : Bounds (-19063021 / 50000000) (-381260419 / 1000000000) (Real.log (683 / 1000)) := by
  have h := reflection_log_9988_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9989_neg : (316949 / 1000000000) ≤ -Real.log (1000000 / 1000317) ∧
    -Real.log (1000000 / 1000317) ≤ (6339 / 20000000) := by
  have h := checkLog_sound (w := (317 / 2000317)) (n := 12)
    (lo := (316949 / 1000000000)) (hi := (6339 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000317 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000317 / 1000000) = 1/(1000000 / 1000317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9989 : Bounds (316949 / 1000000000) (6339 / 20000000) (Real.log (1000317 / 1000000)) := by
  have h := reflection_log_9989_neg
  have he : Real.log (1000317 / 1000000) = -Real.log (1000000 / 1000317) := by
    rw [show ((1000317 / 1000000) : ℝ) = ((1000000 / 1000317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9990_neg : (6341 / 20000000) ≤ -Real.log (999683 / 1000000) ∧
    -Real.log (999683 / 1000000) ≤ (317051 / 1000000000) := by
  have h := checkLog_sound (w := (317 / 1999683)) (n := 12)
    (lo := (6341 / 20000000)) (hi := (317051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999683) = 1/(999683 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9990 : Bounds (-317051 / 1000000000) (-6341 / 20000000) (Real.log (999683 / 1000000)) := by
  have h := reflection_log_9990_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9991_neg : (74544373 / 500000000) ≤ -Real.log (125000 / 145097) ∧
    -Real.log (125000 / 145097) ≤ (149088747 / 1000000000) := by
  have h := checkLog_sound (w := (20097 / 270097)) (n := 12)
    (lo := (74544373 / 500000000)) (hi := (149088747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145097 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145097 / 125000) = 1/(125000 / 145097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9991 : Bounds (74544373 / 500000000) (149088747 / 1000000000) (Real.log (145097 / 125000)) := by
  have h := reflection_log_9991_neg
  have he : Real.log (145097 / 125000) = -Real.log (125000 / 145097) := by
    rw [show ((145097 / 125000) : ℝ) = ((125000 / 145097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9992_neg : (175277623 / 1000000000) ≤ -Real.log (104903 / 125000) ∧
    -Real.log (104903 / 125000) ≤ (21909703 / 125000000) := by
  have h := checkLog_sound (w := (20097 / 229903)) (n := 12)
    (lo := (175277623 / 1000000000)) (hi := (21909703 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 104903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 104903) = 1/(104903 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9992 : Bounds (-21909703 / 125000000) (-175277623 / 1000000000) (Real.log (104903 / 125000)) := by
  have h := reflection_log_9992_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9993_neg : (149812999 / 1000000000) ≤ -Real.log (1000000 / 1161617) ∧
    -Real.log (1000000 / 1161617) ≤ (149813 / 1000000) := by
  have h := checkLog_sound (w := (161617 / 2161617)) (n := 12)
    (lo := (149812999 / 1000000000)) (hi := (149813 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161617 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1161617 / 1000000) = 1/(1000000 / 1161617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9993 : Bounds (149812999 / 1000000000) (149813 / 1000000) (Real.log (1161617 / 1000000)) := by
  have h := reflection_log_9993_neg
  have he : Real.log (1161617 / 1000000) = -Real.log (1000000 / 1161617) := by
    rw [show ((1161617 / 1000000) : ℝ) = ((1000000 / 1161617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9994_neg : (88140121 / 500000000) ≤ -Real.log (838383 / 1000000) ∧
    -Real.log (838383 / 1000000) ≤ (176280243 / 1000000000) := by
  have h := checkLog_sound (w := (161617 / 1838383)) (n := 12)
    (lo := (88140121 / 500000000)) (hi := (176280243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 838383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 838383) = 1/(838383 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9994 : Bounds (-176280243 / 1000000000) (-88140121 / 500000000) (Real.log (838383 / 1000000)) := by
  have h := reflection_log_9994_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9995_neg : (13233621 / 500000000) ≤ -Real.log (973879945311 / 1000000000000) ∧
    -Real.log (973879945311 / 1000000000000) ≤ (26467243 / 1000000000) := by
  have h := checkLog_sound (w := (26120054689 / 1973879945311)) (n := 12)
    (lo := (13233621 / 500000000)) (hi := (26467243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973879945311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973879945311) = 1/(973879945311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9995 : Bounds (-26467243 / 1000000000) (-13233621 / 500000000) (Real.log (973879945311 / 1000000000000)) := by
  have h := reflection_log_9995_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9996_neg : (6547219 / 250000000) ≤ -Real.log (15221110591 / 15625000000) ∧
    -Real.log (15221110591 / 15625000000) ≤ (26188877 / 1000000000) := by
  have h := checkLog_sound (w := (403889409 / 30846110591)) (n := 12)
    (lo := (6547219 / 250000000)) (hi := (26188877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15221110591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15221110591) = 1/(15221110591 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9996 : Bounds (-26188877 / 1000000000) (-6547219 / 250000000) (Real.log (15221110591 / 15625000000)) := by
  have h := reflection_log_9996_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9997_neg : (32436637 / 100000000) ≤ -Real.log (500000000000 / 691576980639) ∧
    -Real.log (500000000000 / 691576980639) ≤ (324366371 / 1000000000) := by
  have h := checkLog_sound (w := (191576980639 / 1191576980639)) (n := 12)
    (lo := (32436637 / 100000000)) (hi := (324366371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691576980639 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691576980639 / 500000000000) = 1/(500000000000 / 691576980639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9997 : Bounds (32436637 / 100000000) (324366371 / 1000000000) (Real.log (691576980639 / 500000000000)) := by
  have h := reflection_log_9997_neg
  have he : Real.log (691576980639 / 500000000000) = -Real.log (500000000000 / 691576980639) := by
    rw [show ((691576980639 / 500000000000) : ℝ) = ((500000000000 / 691576980639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9998_neg : (163046621 / 500000000) ≤ -Real.log (50000000000 / 69277227711) ∧
    -Real.log (50000000000 / 69277227711) ≤ (326093243 / 1000000000) := by
  have h := checkLog_sound (w := (19277227711 / 119277227711)) (n := 12)
    (lo := (163046621 / 500000000)) (hi := (326093243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69277227711 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69277227711 / 50000000000) = 1/(50000000000 / 69277227711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9998 : Bounds (163046621 / 500000000) (326093243 / 1000000000) (Real.log (69277227711 / 50000000000)) := by
  have h := reflection_log_9998_neg
  have he : Real.log (69277227711 / 50000000000) = -Real.log (50000000000 / 69277227711) := by
    rw [show ((69277227711 / 50000000000) : ℝ) = ((50000000000 / 69277227711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9999_neg : (327197097 / 500000000) ≤ -Real.log (500000000000 / 961988304093) ∧
    -Real.log (500000000000 / 961988304093) ≤ (130878839 / 200000000) := by
  have h := checkLog_sound (w := (461988304093 / 1461988304093)) (n := 12)
    (lo := (327197097 / 500000000)) (hi := (130878839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((961988304093 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(961988304093 / 500000000000) = 1/(500000000000 / 961988304093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9999 : Bounds (327197097 / 500000000) (130878839 / 200000000) (Real.log (961988304093 / 500000000000)) := by
  have h := reflection_log_9999_neg
  have he : Real.log (961988304093 / 500000000000) = -Real.log (500000000000 / 961988304093) := by
    rw [show ((961988304093 / 500000000000) : ℝ) = ((500000000000 / 961988304093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10000_neg : (328308421 / 500000000) ≤ -Real.log (500000000000 / 964128843339) ∧
    -Real.log (500000000000 / 964128843339) ≤ (656616843 / 1000000000) := by
  have h := checkLog_sound (w := (464128843339 / 1464128843339)) (n := 12)
    (lo := (328308421 / 500000000)) (hi := (656616843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((964128843339 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(964128843339 / 500000000000) = 1/(500000000000 / 964128843339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10000 : Bounds (328308421 / 500000000) (656616843 / 1000000000) (Real.log (964128843339 / 500000000000)) := by
  have h := reflection_log_10000_neg
  have he : Real.log (964128843339 / 500000000000) = -Real.log (500000000000 / 964128843339) := by
    rw [show ((964128843339 / 500000000000) : ℝ) = ((500000000000 / 964128843339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10001_neg : (69028859 / 250000000) ≤ -Real.log (500 / 659) ∧
    -Real.log (500 / 659) ≤ (276115437 / 1000000000) := by
  have h := checkLog_sound (w := (159 / 1159)) (n := 12)
    (lo := (69028859 / 250000000)) (hi := (276115437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((659 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(659 / 500) = 1/(500 / 659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10001 : Bounds (69028859 / 250000000) (276115437 / 1000000000) (Real.log (659 / 500)) := by
  have h := reflection_log_10001_neg
  have he : Real.log (659 / 500) = -Real.log (500 / 659) := by
    rw [show ((659 / 500) : ℝ) = ((500 / 659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10002_neg : (382725621 / 1000000000) ≤ -Real.log (341 / 500) ∧
    -Real.log (341 / 500) ≤ (191362811 / 500000000) := by
  have h := checkLog_sound (w := (159 / 841)) (n := 12)
    (lo := (382725621 / 1000000000)) (hi := (191362811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 341) = 1/(341 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10002 : Bounds (-191362811 / 500000000) (-382725621 / 1000000000) (Real.log (341 / 500)) := by
  have h := reflection_log_10002_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10003_neg : (317949 / 1000000000) ≤ -Real.log (500000 / 500159) ∧
    -Real.log (500000 / 500159) ≤ (6359 / 20000000) := by
  have h := checkLog_sound (w := (159 / 1000159)) (n := 12)
    (lo := (317949 / 1000000000)) (hi := (6359 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500159 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500159 / 500000) = 1/(500000 / 500159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10003 : Bounds (317949 / 1000000000) (6359 / 20000000) (Real.log (500159 / 500000)) := by
  have h := reflection_log_10003_neg
  have he : Real.log (500159 / 500000) = -Real.log (500000 / 500159) := by
    rw [show ((500159 / 500000) : ℝ) = ((500000 / 500159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10004_neg : (6361 / 20000000) ≤ -Real.log (499841 / 500000) ∧
    -Real.log (499841 / 500000) ≤ (318051 / 1000000000) := by
  have h := checkLog_sound (w := (159 / 999841)) (n := 12)
    (lo := (6361 / 20000000)) (hi := (318051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499841) = 1/(499841 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10004 : Bounds (-318051 / 1000000000) (-6361 / 20000000) (Real.log (499841 / 500000)) := by
  have h := reflection_log_10004_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10005_neg : (149543511 / 1000000000) ≤ -Real.log (125000 / 145163) ∧
    -Real.log (125000 / 145163) ≤ (18692939 / 125000000) := by
  have h := checkLog_sound (w := (20163 / 270163)) (n := 12)
    (lo := (149543511 / 1000000000)) (hi := (18692939 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145163 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145163 / 125000) = 1/(125000 / 145163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10005 : Bounds (149543511 / 1000000000) (18692939 / 125000000) (Real.log (145163 / 125000)) := by
  have h := reflection_log_10005_neg
  have he : Real.log (145163 / 125000) = -Real.log (125000 / 145163) := by
    rw [show ((145163 / 125000) : ℝ) = ((125000 / 145163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10006_neg : (87953487 / 500000000) ≤ -Real.log (104837 / 125000) ∧
    -Real.log (104837 / 125000) ≤ (7036279 / 40000000) := by
  have h := checkLog_sound (w := (20163 / 229837)) (n := 12)
    (lo := (87953487 / 500000000)) (hi := (7036279 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 104837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 104837) = 1/(104837 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10006 : Bounds (-7036279 / 40000000) (-87953487 / 500000000) (Real.log (104837 / 125000)) := by
  have h := reflection_log_10006_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10007_neg : (30053659 / 200000000) ≤ -Real.log (500000 / 581073) ∧
    -Real.log (500000 / 581073) ≤ (18783537 / 125000000) := by
  have h := checkLog_sound (w := (81073 / 1081073)) (n := 12)
    (lo := (30053659 / 200000000)) (hi := (18783537 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581073 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581073 / 500000) = 1/(500000 / 581073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10007 : Bounds (30053659 / 200000000) (18783537 / 125000000) (Real.log (581073 / 500000)) := by
  have h := reflection_log_10007_neg
  have he : Real.log (581073 / 500000) = -Real.log (500000 / 581073) := by
    rw [show ((581073 / 500000) : ℝ) = ((500000 / 581073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10008_neg : (88455709 / 500000000) ≤ -Real.log (418927 / 500000) ∧
    -Real.log (418927 / 500000) ≤ (176911419 / 1000000000) := by
  have h := checkLog_sound (w := (81073 / 918927)) (n := 12)
    (lo := (88455709 / 500000000)) (hi := (176911419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 418927) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 418927) = 1/(418927 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10008 : Bounds (-176911419 / 1000000000) (-88455709 / 500000000) (Real.log (418927 / 500000)) := by
  have h := reflection_log_10008_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10009_neg : (13321561 / 500000000) ≤ -Real.log (243427168671 / 250000000000) ∧
    -Real.log (243427168671 / 250000000000) ≤ (26643123 / 1000000000) := by
  have h := checkLog_sound (w := (6572831329 / 493427168671)) (n := 12)
    (lo := (13321561 / 500000000)) (hi := (26643123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243427168671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243427168671) = 1/(243427168671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10009 : Bounds (-26643123 / 1000000000) (-13321561 / 500000000) (Real.log (243427168671 / 250000000000)) := by
  have h := reflection_log_10009_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10010_neg : (13181731 / 500000000) ≤ -Real.log (15218453431 / 15625000000) ∧
    -Real.log (15218453431 / 15625000000) ≤ (26363463 / 1000000000) := by
  have h := checkLog_sound (w := (406546569 / 30843453431)) (n := 12)
    (lo := (13181731 / 500000000)) (hi := (26363463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15218453431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15218453431) = 1/(15218453431 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10010 : Bounds (-26363463 / 1000000000) (-13181731 / 500000000) (Real.log (15218453431 / 15625000000)) := by
  have h := reflection_log_10010_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10011_neg : (65090097 / 200000000) ≤ -Real.log (500000000000 / 692327136411) ∧
    -Real.log (500000000000 / 692327136411) ≤ (162725243 / 500000000) := by
  have h := checkLog_sound (w := (192327136411 / 1192327136411)) (n := 12)
    (lo := (65090097 / 200000000)) (hi := (162725243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((692327136411 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(692327136411 / 500000000000) = 1/(500000000000 / 692327136411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10011 : Bounds (65090097 / 200000000) (162725243 / 500000000) (Real.log (692327136411 / 500000000000)) := by
  have h := reflection_log_10011_neg
  have he : Real.log (692327136411 / 500000000000) = -Real.log (500000000000 / 692327136411) := by
    rw [show ((692327136411 / 500000000000) : ℝ) = ((500000000000 / 692327136411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10012_neg : (327179713 / 1000000000) ≤ -Real.log (62500000000 / 86690670451) ∧
    -Real.log (62500000000 / 86690670451) ≤ (163589857 / 500000000) := by
  have h := checkLog_sound (w := (24190670451 / 149190670451)) (n := 12)
    (lo := (327179713 / 1000000000)) (hi := (163589857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86690670451 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86690670451 / 62500000000) = 1/(62500000000 / 86690670451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10012 : Bounds (327179713 / 1000000000) (163589857 / 500000000) (Real.log (86690670451 / 62500000000)) := by
  have h := reflection_log_10012_neg
  have he : Real.log (86690670451 / 62500000000) = -Real.log (62500000000 / 86690670451) := by
    rw [show ((86690670451 / 62500000000) : ℝ) = ((62500000000 / 86690670451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10013_neg : (328308421 / 500000000) ≤ -Real.log (250000000000 / 482064421669) ∧
    -Real.log (250000000000 / 482064421669) ≤ (656616843 / 1000000000) := by
  have h := checkLog_sound (w := (232064421669 / 732064421669)) (n := 12)
    (lo := (328308421 / 500000000)) (hi := (656616843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((482064421669 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(482064421669 / 250000000000) = 1/(250000000000 / 482064421669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10013 : Bounds (328308421 / 500000000) (656616843 / 1000000000) (Real.log (482064421669 / 250000000000)) := by
  have h := reflection_log_10013_neg
  have he : Real.log (482064421669 / 250000000000) = -Real.log (250000000000 / 482064421669) := by
    rw [show ((482064421669 / 250000000000) : ℝ) = ((250000000000 / 482064421669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10014_neg : (658841057 / 1000000000) ≤ -Real.log (20000000000 / 38651026393) ∧
    -Real.log (20000000000 / 38651026393) ≤ (329420529 / 500000000) := by
  have h := checkLog_sound (w := (18651026393 / 58651026393)) (n := 12)
    (lo := (658841057 / 1000000000)) (hi := (329420529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38651026393 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38651026393 / 20000000000) = 1/(20000000000 / 38651026393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10014 : Bounds (658841057 / 1000000000) (329420529 / 500000000) (Real.log (38651026393 / 20000000000)) := by
  have h := reflection_log_10014_neg
  have he : Real.log (38651026393 / 20000000000) = -Real.log (20000000000 / 38651026393) := by
    rw [show ((38651026393 / 20000000000) : ℝ) = ((20000000000 / 38651026393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10015_neg : (276873873 / 1000000000) ≤ -Real.log (1000 / 1319) ∧
    -Real.log (1000 / 1319) ≤ (138436937 / 500000000) := by
  have h := checkLog_sound (w := (319 / 2319)) (n := 12)
    (lo := (276873873 / 1000000000)) (hi := (138436937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1319 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1319 / 1000) = 1/(1000 / 1319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10015 : Bounds (276873873 / 1000000000) (138436937 / 500000000) (Real.log (1319 / 1000)) := by
  have h := reflection_log_10015_neg
  have he : Real.log (1319 / 1000) = -Real.log (1000 / 1319) := by
    rw [show ((1319 / 1000) : ℝ) = ((1000 / 1319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10016_neg : (96048243 / 250000000) ≤ -Real.log (681 / 1000) ∧
    -Real.log (681 / 1000) ≤ (384192973 / 1000000000) := by
  have h := checkLog_sound (w := (319 / 1681)) (n := 12)
    (lo := (96048243 / 250000000)) (hi := (384192973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 681) = 1/(681 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10016 : Bounds (-384192973 / 1000000000) (-96048243 / 250000000) (Real.log (681 / 1000)) := by
  have h := reflection_log_10016_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10017_neg : (318949 / 1000000000) ≤ -Real.log (1000000 / 1000319) ∧
    -Real.log (1000000 / 1000319) ≤ (6379 / 20000000) := by
  have h := checkLog_sound (w := (319 / 2000319)) (n := 12)
    (lo := (318949 / 1000000000)) (hi := (6379 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000319 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000319 / 1000000) = 1/(1000000 / 1000319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10017 : Bounds (318949 / 1000000000) (6379 / 20000000) (Real.log (1000319 / 1000000)) := by
  have h := reflection_log_10017_neg
  have he : Real.log (1000319 / 1000000) = -Real.log (1000000 / 1000319) := by
    rw [show ((1000319 / 1000000) : ℝ) = ((1000000 / 1000319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10018_neg : (6381 / 20000000) ≤ -Real.log (999681 / 1000000) ∧
    -Real.log (999681 / 1000000) ≤ (319051 / 1000000000) := by
  have h := checkLog_sound (w := (319 / 1999681)) (n := 12)
    (lo := (6381 / 20000000)) (hi := (319051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999681) = 1/(999681 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10018 : Bounds (-319051 / 1000000000) (-6381 / 20000000) (Real.log (999681 / 1000000)) := by
  have h := reflection_log_10018_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10019_neg : (14999893 / 100000000) ≤ -Real.log (1000000 / 1161833) ∧
    -Real.log (1000000 / 1161833) ≤ (149998931 / 1000000000) := by
  have h := checkLog_sound (w := (161833 / 2161833)) (n := 12)
    (lo := (14999893 / 100000000)) (hi := (149998931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161833 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1161833 / 1000000) = 1/(1000000 / 1161833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10019 : Bounds (14999893 / 100000000) (149998931 / 1000000000) (Real.log (1161833 / 1000000)) := by
  have h := reflection_log_10019_neg
  have he : Real.log (1161833 / 1000000) = -Real.log (1000000 / 1161833) := by
    rw [show ((1161833 / 1000000) : ℝ) = ((1000000 / 1161833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10020_neg : (88268957 / 500000000) ≤ -Real.log (838167 / 1000000) ∧
    -Real.log (838167 / 1000000) ≤ (35307583 / 200000000) := by
  have h := checkLog_sound (w := (161833 / 1838167)) (n := 12)
    (lo := (88268957 / 500000000)) (hi := (35307583 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 838167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 838167) = 1/(838167 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10020 : Bounds (-35307583 / 200000000) (-88268957 / 500000000) (Real.log (838167 / 1000000)) := by
  have h := reflection_log_10020_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10021_neg : (18840423 / 125000000) ≤ -Real.log (40000 / 46507) ∧
    -Real.log (40000 / 46507) ≤ (30144677 / 200000000) := by
  have h := checkLog_sound (w := (6507 / 86507)) (n := 12)
    (lo := (18840423 / 125000000)) (hi := (30144677 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46507 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46507 / 40000) = 1/(40000 / 46507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10021 : Bounds (18840423 / 125000000) (30144677 / 200000000) (Real.log (46507 / 40000)) := by
  have h := reflection_log_10021_neg
  have he : Real.log (46507 / 40000) = -Real.log (40000 / 46507) := by
    rw [show ((46507 / 40000) : ℝ) = ((40000 / 46507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10022_neg : (11096437 / 62500000) ≤ -Real.log (33493 / 40000) ∧
    -Real.log (33493 / 40000) ≤ (177542993 / 1000000000) := by
  have h := checkLog_sound (w := (6507 / 73493)) (n := 12)
    (lo := (11096437 / 62500000)) (hi := (177542993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 33493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 33493) = 1/(33493 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10022 : Bounds (-177542993 / 1000000000) (-11096437 / 62500000) (Real.log (33493 / 40000)) := by
  have h := reflection_log_10022_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10023_neg : (26819607 / 1000000000) ≤ -Real.log (1557658951 / 1600000000) ∧
    -Real.log (1557658951 / 1600000000) ≤ (3352451 / 125000000) := by
  have h := checkLog_sound (w := (42341049 / 3157658951)) (n := 12)
    (lo := (26819607 / 1000000000)) (hi := (3352451 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1557658951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1557658951) = 1/(1557658951 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10023 : Bounds (-3352451 / 125000000) (-26819607 / 1000000000) (Real.log (1557658951 / 1600000000)) := by
  have h := reflection_log_10023_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10024_neg : (26538983 / 1000000000) ≤ -Real.log (973810080111 / 1000000000000) ∧
    -Real.log (973810080111 / 1000000000000) ≤ (3317373 / 125000000) := by
  have h := checkLog_sound (w := (26189919889 / 1973810080111)) (n := 12)
    (lo := (26538983 / 1000000000)) (hi := (3317373 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973810080111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973810080111) = 1/(973810080111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10024 : Bounds (-3317373 / 125000000) (-26538983 / 1000000000) (Real.log (973810080111 / 1000000000000)) := by
  have h := reflection_log_10024_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10025_neg : (81634211 / 250000000) ≤ -Real.log (100000000000 / 138615932147) ∧
    -Real.log (100000000000 / 138615932147) ≤ (65307369 / 200000000) := by
  have h := checkLog_sound (w := (38615932147 / 238615932147)) (n := 12)
    (lo := (81634211 / 250000000)) (hi := (65307369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138615932147 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(138615932147 / 100000000000) = 1/(100000000000 / 138615932147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10025 : Bounds (81634211 / 250000000) (65307369 / 200000000) (Real.log (138615932147 / 100000000000)) := by
  have h := reflection_log_10025_neg
  have he : Real.log (138615932147 / 100000000000) = -Real.log (100000000000 / 138615932147) := by
    rw [show ((138615932147 / 100000000000) : ℝ) = ((100000000000 / 138615932147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10026_neg : (328266377 / 1000000000) ≤ -Real.log (500000000000 / 694279401667) ∧
    -Real.log (500000000000 / 694279401667) ≤ (164133189 / 500000000) := by
  have h := checkLog_sound (w := (194279401667 / 1194279401667)) (n := 12)
    (lo := (328266377 / 1000000000)) (hi := (164133189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694279401667 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694279401667 / 500000000000) = 1/(500000000000 / 694279401667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10026 : Bounds (328266377 / 1000000000) (164133189 / 500000000) (Real.log (694279401667 / 500000000000)) := by
  have h := reflection_log_10026_neg
  have he : Real.log (694279401667 / 500000000000) = -Real.log (500000000000 / 694279401667) := by
    rw [show ((694279401667 / 500000000000) : ℝ) = ((500000000000 / 694279401667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10027_neg : (658841057 / 1000000000) ≤ -Real.log (31250000000 / 60392228739) ∧
    -Real.log (31250000000 / 60392228739) ≤ (329420529 / 500000000) := by
  have h := checkLog_sound (w := (29142228739 / 91642228739)) (n := 12)
    (lo := (658841057 / 1000000000)) (hi := (329420529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60392228739 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60392228739 / 31250000000) = 1/(31250000000 / 60392228739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10027 : Bounds (658841057 / 1000000000) (329420529 / 500000000) (Real.log (60392228739 / 31250000000)) := by
  have h := reflection_log_10027_neg
  have he : Real.log (60392228739 / 31250000000) = -Real.log (31250000000 / 60392228739) := by
    rw [show ((60392228739 / 31250000000) : ℝ) = ((31250000000 / 60392228739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10028_neg : (330533423 / 500000000) ≤ -Real.log (100000000000 / 193685756241) ∧
    -Real.log (100000000000 / 193685756241) ≤ (661066847 / 1000000000) := by
  have h := checkLog_sound (w := (93685756241 / 293685756241)) (n := 12)
    (lo := (330533423 / 500000000)) (hi := (661066847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((193685756241 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(193685756241 / 100000000000) = 1/(100000000000 / 193685756241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10028 : Bounds (330533423 / 500000000) (661066847 / 1000000000) (Real.log (193685756241 / 100000000000)) := by
  have h := reflection_log_10028_neg
  have he : Real.log (193685756241 / 100000000000) = -Real.log (100000000000 / 193685756241) := by
    rw [show ((193685756241 / 100000000000) : ℝ) = ((100000000000 / 193685756241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10029_neg : (34703967 / 125000000) ≤ -Real.log (25 / 33) ∧
    -Real.log (25 / 33) ≤ (277631737 / 1000000000) := by
  have h := checkLog_sound (w := (4 / 29)) (n := 12)
    (lo := (34703967 / 125000000)) (hi := (277631737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33 / 25) = 1/(25 / 33) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10029 : Bounds (34703967 / 125000000) (277631737 / 1000000000) (Real.log (33 / 25)) := by
  have h := reflection_log_10029_neg
  have he : Real.log (33 / 25) = -Real.log (25 / 33) := by
    rw [show ((33 / 25) : ℝ) = ((25 / 33) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10030_neg : (4820781 / 12500000) ≤ -Real.log (17 / 25) ∧
    -Real.log (17 / 25) ≤ (385662481 / 1000000000) := by
  have h := checkLog_sound (w := (4 / 21)) (n := 12)
    (lo := (4820781 / 12500000)) (hi := (385662481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 17) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25 / 17) = 1/(17 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10030 : Bounds (-385662481 / 1000000000) (-4820781 / 12500000) (Real.log (17 / 25)) := by
  have h := reflection_log_10030_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10031_neg : (79987 / 250000000) ≤ -Real.log (3125 / 3126) ∧
    -Real.log (3125 / 3126) ≤ (319949 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 6251)) (n := 12)
    (lo := (79987 / 250000000)) (hi := (319949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3126 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3126 / 3125) = 1/(3125 / 3126) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10031 : Bounds (79987 / 250000000) (319949 / 1000000000) (Real.log (3126 / 3125)) := by
  have h := reflection_log_10031_neg
  have he : Real.log (3126 / 3125) = -Real.log (3125 / 3126) := by
    rw [show ((3126 / 3125) : ℝ) = ((3125 / 3126) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10032_neg : (320051 / 1000000000) ≤ -Real.log (3124 / 3125) ∧
    -Real.log (3124 / 3125) ≤ (80013 / 250000000) := by
  have h := checkLog_sound (w := (1 / 6249)) (n := 12)
    (lo := (320051 / 1000000000)) (hi := (80013 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 3124) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 3124) = 1/(3124 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10032 : Bounds (-80013 / 250000000) (-320051 / 1000000000) (Real.log (3124 / 3125)) := by
  have h := reflection_log_10032_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10033_neg : (150453281 / 1000000000) ≤ -Real.log (1000000 / 1162361) ∧
    -Real.log (1000000 / 1162361) ≤ (75226641 / 500000000) := by
  have h := checkLog_sound (w := (162361 / 2162361)) (n := 12)
    (lo := (150453281 / 1000000000)) (hi := (75226641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1162361 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1162361 / 1000000) = 1/(1000000 / 1162361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10033 : Bounds (150453281 / 1000000000) (75226641 / 500000000) (Real.log (1162361 / 1000000)) := by
  have h := reflection_log_10033_neg
  have he : Real.log (1162361 / 1000000) = -Real.log (1000000 / 1162361) := by
    rw [show ((1162361 / 1000000) : ℝ) = ((1000000 / 1162361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10034_neg : (88584029 / 500000000) ≤ -Real.log (837639 / 1000000) ∧
    -Real.log (837639 / 1000000) ≤ (177168059 / 1000000000) := by
  have h := checkLog_sound (w := (162361 / 1837639)) (n := 12)
    (lo := (88584029 / 500000000)) (hi := (177168059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 837639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 837639) = 1/(837639 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10034 : Bounds (-177168059 / 1000000000) (-88584029 / 500000000) (Real.log (837639 / 1000000)) := by
  have h := reflection_log_10034_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10035_neg : (75589133 / 500000000) ≤ -Real.log (250000 / 290801) ∧
    -Real.log (250000 / 290801) ≤ (151178267 / 1000000000) := by
  have h := checkLog_sound (w := (40801 / 540801)) (n := 12)
    (lo := (75589133 / 500000000)) (hi := (151178267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((290801 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(290801 / 250000) = 1/(250000 / 290801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10035 : Bounds (75589133 / 500000000) (151178267 / 1000000000) (Real.log (290801 / 250000)) := by
  have h := reflection_log_10035_neg
  have he : Real.log (290801 / 250000) = -Real.log (250000 / 290801) := by
    rw [show ((290801 / 250000) : ℝ) = ((250000 / 290801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10036_neg : (35634993 / 200000000) ≤ -Real.log (209199 / 250000) ∧
    -Real.log (209199 / 250000) ≤ (89087483 / 500000000) := by
  have h := checkLog_sound (w := (40801 / 459199)) (n := 12)
    (lo := (35634993 / 200000000)) (hi := (89087483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 209199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 209199) = 1/(209199 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10036 : Bounds (-89087483 / 500000000) (-35634993 / 200000000) (Real.log (209199 / 250000)) := by
  have h := reflection_log_10036_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10037_neg : (26996699 / 1000000000) ≤ -Real.log (60835278399 / 62500000000) ∧
    -Real.log (60835278399 / 62500000000) ≤ (269967 / 10000000) := by
  have h := checkLog_sound (w := (1664721601 / 123335278399)) (n := 12)
    (lo := (26996699 / 1000000000)) (hi := (269967 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60835278399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60835278399) = 1/(60835278399 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10037 : Bounds (-269967 / 10000000) (-26996699 / 1000000000) (Real.log (60835278399 / 62500000000)) := by
  have h := reflection_log_10037_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10038_neg : (26714777 / 1000000000) ≤ -Real.log (973638905679 / 1000000000000) ∧
    -Real.log (973638905679 / 1000000000000) ≤ (13357389 / 500000000) := by
  have h := checkLog_sound (w := (26361094321 / 1973638905679)) (n := 12)
    (lo := (26714777 / 1000000000)) (hi := (13357389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973638905679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973638905679) = 1/(973638905679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10038 : Bounds (-13357389 / 500000000) (-26714777 / 1000000000) (Real.log (973638905679 / 1000000000000)) := by
  have h := reflection_log_10038_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10039_neg : (16381067 / 50000000) ≤ -Real.log (500000000000 / 693831710319) ∧
    -Real.log (500000000000 / 693831710319) ≤ (327621341 / 1000000000) := by
  have h := checkLog_sound (w := (193831710319 / 1193831710319)) (n := 12)
    (lo := (16381067 / 50000000)) (hi := (327621341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693831710319 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693831710319 / 500000000000) = 1/(500000000000 / 693831710319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10039 : Bounds (16381067 / 50000000) (327621341 / 1000000000) (Real.log (693831710319 / 500000000000)) := by
  have h := reflection_log_10039_neg
  have he : Real.log (693831710319 / 500000000000) = -Real.log (500000000000 / 693831710319) := by
    rw [show ((693831710319 / 500000000000) : ℝ) = ((500000000000 / 693831710319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10040_neg : (20584577 / 62500000) ≤ -Real.log (50000000000 / 69503439309) ∧
    -Real.log (50000000000 / 69503439309) ≤ (329353233 / 1000000000) := by
  have h := checkLog_sound (w := (19503439309 / 119503439309)) (n := 12)
    (lo := (20584577 / 62500000)) (hi := (329353233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69503439309 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69503439309 / 50000000000) = 1/(50000000000 / 69503439309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10040 : Bounds (20584577 / 62500000) (329353233 / 1000000000) (Real.log (69503439309 / 50000000000)) := by
  have h := reflection_log_10040_neg
  have he : Real.log (69503439309 / 50000000000) = -Real.log (50000000000 / 69503439309) := by
    rw [show ((69503439309 / 50000000000) : ℝ) = ((50000000000 / 69503439309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10041_neg : (330533423 / 500000000) ≤ -Real.log (125000000000 / 242107195301) ∧
    -Real.log (125000000000 / 242107195301) ≤ (661066847 / 1000000000) := by
  have h := checkLog_sound (w := (117107195301 / 367107195301)) (n := 12)
    (lo := (330533423 / 500000000)) (hi := (661066847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242107195301 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242107195301 / 125000000000) = 1/(125000000000 / 242107195301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10041 : Bounds (330533423 / 500000000) (661066847 / 1000000000) (Real.log (242107195301 / 125000000000)) := by
  have h := reflection_log_10041_neg
  have he : Real.log (242107195301 / 125000000000) = -Real.log (125000000000 / 242107195301) := by
    rw [show ((242107195301 / 125000000000) : ℝ) = ((125000000000 / 242107195301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10042_neg : (663294217 / 1000000000) ≤ -Real.log (100000000000 / 194117647059) ∧
    -Real.log (100000000000 / 194117647059) ≤ (331647109 / 500000000) := by
  have h := checkLog_sound (w := (94117647059 / 294117647059)) (n := 12)
    (lo := (663294217 / 1000000000)) (hi := (331647109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((194117647059 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(194117647059 / 100000000000) = 1/(100000000000 / 194117647059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10042 : Bounds (663294217 / 1000000000) (331647109 / 500000000) (Real.log (194117647059 / 100000000000)) := by
  have h := reflection_log_10042_neg
  have he : Real.log (194117647059 / 100000000000) = -Real.log (100000000000 / 194117647059) := by
    rw [show ((194117647059 / 100000000000) : ℝ) = ((100000000000 / 194117647059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10043_neg : (11135561 / 40000000) ≤ -Real.log (1000 / 1321) ∧
    -Real.log (1000 / 1321) ≤ (139194513 / 500000000) := by
  have h := checkLog_sound (w := (321 / 2321)) (n := 12)
    (lo := (11135561 / 40000000)) (hi := (139194513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1321 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1321 / 1000) = 1/(1000 / 1321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10043 : Bounds (11135561 / 40000000) (139194513 / 500000000) (Real.log (1321 / 1000)) := by
  have h := reflection_log_10043_neg
  have he : Real.log (1321 / 1000) = -Real.log (1000 / 1321) := by
    rw [show ((1321 / 1000) : ℝ) = ((1000 / 1321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10044_neg : (387134151 / 1000000000) ≤ -Real.log (679 / 1000) ∧
    -Real.log (679 / 1000) ≤ (48391769 / 125000000) := by
  have h := checkLog_sound (w := (321 / 1679)) (n := 12)
    (lo := (387134151 / 1000000000)) (hi := (48391769 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 679) = 1/(679 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10044 : Bounds (-48391769 / 125000000) (-387134151 / 1000000000) (Real.log (679 / 1000)) := by
  have h := reflection_log_10044_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10045_neg : (80237 / 250000000) ≤ -Real.log (1000000 / 1000321) ∧
    -Real.log (1000000 / 1000321) ≤ (320949 / 1000000000) := by
  have h := checkLog_sound (w := (321 / 2000321)) (n := 12)
    (lo := (80237 / 250000000)) (hi := (320949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000321 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000321 / 1000000) = 1/(1000000 / 1000321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10045 : Bounds (80237 / 250000000) (320949 / 1000000000) (Real.log (1000321 / 1000000)) := by
  have h := reflection_log_10045_neg
  have he : Real.log (1000321 / 1000000) = -Real.log (1000000 / 1000321) := by
    rw [show ((1000321 / 1000000) : ℝ) = ((1000000 / 1000321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10046_neg : (321051 / 1000000000) ≤ -Real.log (999679 / 1000000) ∧
    -Real.log (999679 / 1000000) ≤ (80263 / 250000000) := by
  have h := checkLog_sound (w := (321 / 1999679)) (n := 12)
    (lo := (321051 / 1000000000)) (hi := (80263 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999679) = 1/(999679 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10046 : Bounds (-80263 / 250000000) (-321051 / 1000000000) (Real.log (999679 / 1000000)) := by
  have h := reflection_log_10046_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10047_neg : (75454143 / 500000000) ≤ -Real.log (100000 / 116289) ∧
    -Real.log (100000 / 116289) ≤ (150908287 / 1000000000) := by
  have h := checkLog_sound (w := (16289 / 216289)) (n := 12)
    (lo := (75454143 / 500000000)) (hi := (150908287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116289 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(116289 / 100000) = 1/(100000 / 116289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10047 : Bounds (75454143 / 500000000) (150908287 / 1000000000) (Real.log (116289 / 100000)) := by
  have h := reflection_log_10047_neg
  have he : Real.log (116289 / 100000) = -Real.log (100000 / 116289) := by
    rw [show ((116289 / 100000) : ℝ) = ((100000 / 116289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


