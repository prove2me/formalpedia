-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0187__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0187__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T07:11:46.96647+00:00
-- url     : https://prove2.me/theorems/9e393882-6b75-4cdf-b4ea-620eefea38ec
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0187 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0188, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0187 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0188, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0189)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0187 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0188, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0189)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0187 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0188, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0189) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0187 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0188, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0189).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0187 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11968_neg : (9599 / 15625) ≤ -Real.log (541 / 1000) ∧
    -Real.log (541 / 1000) ≤ (614336001 / 1000000000) := by
  have h := checkLog_sound (w := (459 / 1541)) (n := 12)
    (lo := (9599 / 15625)) (hi := (614336001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 541) = 1/(541 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11968 : Bounds (-614336001 / 1000000000) (-9599 / 15625) (Real.log (541 / 1000)) := by
  have h := reflection_log_11968_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11969_neg : (229447 / 500000000) ≤ -Real.log (1000000 / 1000459) ∧
    -Real.log (1000000 / 1000459) ≤ (91779 / 200000000) := by
  have h := checkLog_sound (w := (459 / 2000459)) (n := 12)
    (lo := (229447 / 500000000)) (hi := (91779 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000459 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000459 / 1000000) = 1/(1000000 / 1000459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11969 : Bounds (229447 / 500000000) (91779 / 200000000) (Real.log (1000459 / 1000000)) := by
  have h := reflection_log_11969_neg
  have he : Real.log (1000459 / 1000000) = -Real.log (1000000 / 1000459) := by
    rw [show ((1000459 / 1000000) : ℝ) = ((1000000 / 1000459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11970_neg : (91821 / 200000000) ≤ -Real.log (999541 / 1000000) ∧
    -Real.log (999541 / 1000000) ≤ (229553 / 500000000) := by
  have h := checkLog_sound (w := (459 / 1999541)) (n := 12)
    (lo := (91821 / 200000000)) (hi := (229553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999541) = 1/(999541 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11970 : Bounds (-229553 / 500000000) (-91821 / 200000000) (Real.log (999541 / 1000000)) := by
  have h := reflection_log_11970_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11971_neg : (213519791 / 1000000000) ≤ -Real.log (250000 / 309507) ∧
    -Real.log (250000 / 309507) ≤ (13344987 / 62500000) := by
  have h := checkLog_sound (w := (59507 / 559507)) (n := 12)
    (lo := (213519791 / 1000000000)) (hi := (13344987 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((309507 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(309507 / 250000) = 1/(250000 / 309507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11971 : Bounds (213519791 / 1000000000) (13344987 / 62500000) (Real.log (309507 / 250000)) := by
  have h := reflection_log_11971_neg
  have he : Real.log (309507 / 250000) = -Real.log (250000 / 309507) := by
    rw [show ((309507 / 250000) : ℝ) = ((250000 / 309507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11972_neg : (271845469 / 1000000000) ≤ -Real.log (190493 / 250000) ∧
    -Real.log (190493 / 250000) ≤ (27184547 / 100000000) := by
  have h := checkLog_sound (w := (59507 / 440493)) (n := 12)
    (lo := (271845469 / 1000000000)) (hi := (27184547 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 190493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 190493) = 1/(190493 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11972 : Bounds (-27184547 / 100000000) (-271845469 / 1000000000) (Real.log (190493 / 250000)) := by
  have h := reflection_log_11972_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11973_neg : (107164811 / 500000000) ≤ -Real.log (1000000 / 1239031) ∧
    -Real.log (1000000 / 1239031) ≤ (214329623 / 1000000000) := by
  have h := checkLog_sound (w := (239031 / 2239031)) (n := 12)
    (lo := (107164811 / 500000000)) (hi := (214329623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1239031 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1239031 / 1000000) = 1/(1000000 / 1239031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11973 : Bounds (107164811 / 500000000) (214329623 / 1000000000) (Real.log (1239031 / 1000000)) := by
  have h := reflection_log_11973_neg
  have he : Real.log (1239031 / 1000000) = -Real.log (1000000 / 1239031) := by
    rw [show ((1239031 / 1000000) : ℝ) = ((1000000 / 1239031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11974_neg : (273162657 / 1000000000) ≤ -Real.log (760969 / 1000000) ∧
    -Real.log (760969 / 1000000) ≤ (136581329 / 500000000) := by
  have h := checkLog_sound (w := (239031 / 1760969)) (n := 12)
    (lo := (273162657 / 1000000000)) (hi := (136581329 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 760969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 760969) = 1/(760969 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11974 : Bounds (-136581329 / 500000000) (-273162657 / 1000000000) (Real.log (760969 / 1000000)) := by
  have h := reflection_log_11974_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11975_neg : (11766607 / 200000000) ≤ -Real.log (942864181039 / 1000000000000) ∧
    -Real.log (942864181039 / 1000000000000) ≤ (14708259 / 250000000) := by
  have h := checkLog_sound (w := (57135818961 / 1942864181039)) (n := 12)
    (lo := (11766607 / 200000000)) (hi := (14708259 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 942864181039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 942864181039) = 1/(942864181039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11975 : Bounds (-14708259 / 250000000) (-11766607 / 200000000) (Real.log (942864181039 / 1000000000000)) := by
  have h := reflection_log_11975_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11976_neg : (29162839 / 500000000) ≤ -Real.log (58958916951 / 62500000000) ∧
    -Real.log (58958916951 / 62500000000) ≤ (58325679 / 1000000000) := by
  have h := checkLog_sound (w := (3541083049 / 121458916951)) (n := 12)
    (lo := (29162839 / 500000000)) (hi := (58325679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 58958916951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 58958916951) = 1/(58958916951 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11976 : Bounds (-58325679 / 1000000000) (-29162839 / 500000000) (Real.log (58958916951 / 62500000000)) := by
  have h := reflection_log_11976_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11977_neg : (24268263 / 50000000) ≤ -Real.log (100000000000 / 162476836419) ∧
    -Real.log (100000000000 / 162476836419) ≤ (485365261 / 1000000000) := by
  have h := checkLog_sound (w := (62476836419 / 262476836419)) (n := 12)
    (lo := (24268263 / 50000000)) (hi := (485365261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162476836419 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162476836419 / 100000000000) = 1/(100000000000 / 162476836419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11977 : Bounds (24268263 / 50000000) (485365261 / 1000000000) (Real.log (162476836419 / 100000000000)) := by
  have h := reflection_log_11977_neg
  have he : Real.log (162476836419 / 100000000000) = -Real.log (100000000000 / 162476836419) := by
    rw [show ((162476836419 / 100000000000) : ℝ) = ((100000000000 / 162476836419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11978_neg : (12187307 / 25000000) ≤ -Real.log (250000000000 / 407056989181) ∧
    -Real.log (250000000000 / 407056989181) ≤ (487492281 / 1000000000) := by
  have h := checkLog_sound (w := (157056989181 / 657056989181)) (n := 12)
    (lo := (12187307 / 25000000)) (hi := (487492281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((407056989181 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(407056989181 / 250000000000) = 1/(250000000000 / 407056989181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11978 : Bounds (12187307 / 25000000) (487492281 / 1000000000) (Real.log (407056989181 / 250000000000)) := by
  have h := reflection_log_11978_neg
  have he : Real.log (407056989181 / 250000000000) = -Real.log (250000000000 / 407056989181) := by
    rw [show ((407056989181 / 250000000000) : ℝ) = ((250000000000 / 407056989181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11979_neg : (98955491 / 100000000) ≤ -Real.log (62500000000 / 168127306273) ∧
    -Real.log (62500000000 / 168127306273) ≤ (30923591 / 31250000) := by
  have h := checkLog_sound (w := (43127306273 / 293127306273)) (n := 12)
    (lo := (29640773 / 100000000)) (hi := (296407731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168127306273 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(168127306273 / 125000000000) = 1/(62500000000 / 168127306273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11979 : Bounds (98955491 / 100000000) (30923591 / 31250000) (Real.log (168127306273 / 62500000000)) := by
  have h := reflection_log_11979_neg
  have he : Real.log (168127306273 / 62500000000) = -Real.log (62500000000 / 168127306273) := by
    rw [show ((168127306273 / 62500000000) : ℝ) = ((62500000000 / 168127306273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11980_neg : (992087269 / 1000000000) ≤ -Real.log (50000000000 / 134842883549) ∧
    -Real.log (50000000000 / 134842883549) ≤ (992087271 / 1000000000) := by
  have h := checkLog_sound (w := (34842883549 / 234842883549)) (n := 12)
    (lo := (298940089 / 1000000000)) (hi := (29894009 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134842883549 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(134842883549 / 100000000000) = 1/(50000000000 / 134842883549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11980 : Bounds (992087269 / 1000000000) (992087271 / 1000000000) (Real.log (134842883549 / 50000000000)) := by
  have h := reflection_log_11980_neg
  have he : Real.log (134842883549 / 50000000000) = -Real.log (50000000000 / 134842883549) := by
    rw [show ((134842883549 / 50000000000) : ℝ) = ((50000000000 / 134842883549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11981_neg : (75687287 / 200000000) ≤ -Real.log (50 / 73) ∧
    -Real.log (50 / 73) ≤ (94609109 / 250000000) := by
  have h := checkLog_sound (w := (23 / 123)) (n := 12)
    (lo := (75687287 / 200000000)) (hi := (94609109 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73 / 50) = 1/(50 / 73) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11981 : Bounds (75687287 / 200000000) (94609109 / 250000000) (Real.log (73 / 50)) := by
  have h := reflection_log_11981_neg
  have he : Real.log (73 / 50) = -Real.log (50 / 73) := by
    rw [show ((73 / 50) : ℝ) = ((50 / 73) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11982_neg : (616186139 / 1000000000) ≤ -Real.log (27 / 50) ∧
    -Real.log (27 / 50) ≤ (30809307 / 50000000) := by
  have h := checkLog_sound (w := (23 / 77)) (n := 12)
    (lo := (616186139 / 1000000000)) (hi := (30809307 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 27) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50 / 27) = 1/(27 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11982 : Bounds (-30809307 / 50000000) (-616186139 / 1000000000) (Real.log (27 / 50)) := by
  have h := reflection_log_11982_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11983_neg : (229947 / 500000000) ≤ -Real.log (50000 / 50023) ∧
    -Real.log (50000 / 50023) ≤ (91979 / 200000000) := by
  have h := checkLog_sound (w := (23 / 100023)) (n := 12)
    (lo := (229947 / 500000000)) (hi := (91979 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50023 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50023 / 50000) = 1/(50000 / 50023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11983 : Bounds (229947 / 500000000) (91979 / 200000000) (Real.log (50023 / 50000)) := by
  have h := reflection_log_11983_neg
  have he : Real.log (50023 / 50000) = -Real.log (50000 / 50023) := by
    rw [show ((50023 / 50000) : ℝ) = ((50000 / 50023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11984_neg : (92021 / 200000000) ≤ -Real.log (49977 / 50000) ∧
    -Real.log (49977 / 50000) ≤ (230053 / 500000000) := by
  have h := checkLog_sound (w := (23 / 99977)) (n := 12)
    (lo := (92021 / 200000000)) (hi := (230053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 49977) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 49977) = 1/(49977 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11984 : Bounds (-230053 / 500000000) (-92021 / 200000000) (Real.log (49977 / 50000)) := by
  have h := reflection_log_11984_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11985_neg : (213974443 / 1000000000) ≤ -Real.log (1000000 / 1238591) ∧
    -Real.log (1000000 / 1238591) ≤ (53493611 / 250000000) := by
  have h := checkLog_sound (w := (238591 / 2238591)) (n := 12)
    (lo := (213974443 / 1000000000)) (hi := (53493611 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1238591 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1238591 / 1000000) = 1/(1000000 / 1238591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11985 : Bounds (213974443 / 1000000000) (53493611 / 250000000) (Real.log (1238591 / 1000000)) := by
  have h := reflection_log_11985_neg
  have he : Real.log (1238591 / 1000000) = -Real.log (1000000 / 1238591) := by
    rw [show ((1238591 / 1000000) : ℝ) = ((1000000 / 1238591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11986_neg : (136292307 / 500000000) ≤ -Real.log (761409 / 1000000) ∧
    -Real.log (761409 / 1000000) ≤ (54516923 / 200000000) := by
  have h := checkLog_sound (w := (238591 / 1761409)) (n := 12)
    (lo := (136292307 / 500000000)) (hi := (54516923 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 761409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 761409) = 1/(761409 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11986 : Bounds (-54516923 / 200000000) (-136292307 / 500000000) (Real.log (761409 / 1000000)) := by
  have h := reflection_log_11986_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11987_neg : (2684819 / 12500000) ≤ -Real.log (250000 / 309899) ∧
    -Real.log (250000 / 309899) ≤ (214785521 / 1000000000) := by
  have h := checkLog_sound (w := (59899 / 559899)) (n := 12)
    (lo := (2684819 / 12500000)) (hi := (214785521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((309899 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(309899 / 250000) = 1/(250000 / 309899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11987 : Bounds (2684819 / 12500000) (214785521 / 1000000000) (Real.log (309899 / 250000)) := by
  have h := reflection_log_11987_neg
  have he : Real.log (309899 / 250000) = -Real.log (250000 / 309899) := by
    rw [show ((309899 / 250000) : ℝ) = ((250000 / 309899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11988_neg : (273905407 / 1000000000) ≤ -Real.log (190101 / 250000) ∧
    -Real.log (190101 / 250000) ≤ (1069943 / 3906250) := by
  have h := checkLog_sound (w := (59899 / 440101)) (n := 12)
    (lo := (273905407 / 1000000000)) (hi := (1069943 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 190101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 190101) = 1/(190101 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11988 : Bounds (-1069943 / 3906250) (-273905407 / 1000000000) (Real.log (190101 / 250000)) := by
  have h := reflection_log_11988_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11989_neg : (59119887 / 1000000000) ≤ -Real.log (58912109799 / 62500000000) ∧
    -Real.log (58912109799 / 62500000000) ≤ (3694993 / 62500000) := by
  have h := checkLog_sound (w := (3587890201 / 121412109799)) (n := 12)
    (lo := (59119887 / 1000000000)) (hi := (3694993 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 58912109799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 58912109799) = 1/(58912109799 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11989 : Bounds (-3694993 / 62500000) (-59119887 / 1000000000) (Real.log (58912109799 / 62500000000)) := by
  have h := reflection_log_11989_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11990_neg : (58610171 / 1000000000) ≤ -Real.log (943074334719 / 1000000000000) ∧
    -Real.log (943074334719 / 1000000000000) ≤ (14652543 / 250000000) := by
  have h := checkLog_sound (w := (56925665281 / 1943074334719)) (n := 12)
    (lo := (58610171 / 1000000000)) (hi := (14652543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 943074334719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 943074334719) = 1/(943074334719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11990 : Bounds (-14652543 / 250000000) (-58610171 / 1000000000) (Real.log (943074334719 / 1000000000000)) := by
  have h := reflection_log_11990_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11991_neg : (486559057 / 1000000000) ≤ -Real.log (50000000000 / 81335458341) ∧
    -Real.log (50000000000 / 81335458341) ≤ (243279529 / 500000000) := by
  have h := checkLog_sound (w := (31335458341 / 131335458341)) (n := 12)
    (lo := (486559057 / 1000000000)) (hi := (243279529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81335458341 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81335458341 / 50000000000) = 1/(50000000000 / 81335458341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11991 : Bounds (486559057 / 1000000000) (243279529 / 500000000) (Real.log (81335458341 / 50000000000)) := by
  have h := reflection_log_11991_neg
  have he : Real.log (81335458341 / 50000000000) = -Real.log (50000000000 / 81335458341) := by
    rw [show ((81335458341 / 50000000000) : ℝ) = ((50000000000 / 81335458341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11992_neg : (30543183 / 62500000) ≤ -Real.log (100000000000 / 163018079863) ∧
    -Real.log (100000000000 / 163018079863) ≤ (488690929 / 1000000000) := by
  have h := checkLog_sound (w := (63018079863 / 263018079863)) (n := 12)
    (lo := (30543183 / 62500000)) (hi := (488690929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163018079863 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163018079863 / 100000000000) = 1/(100000000000 / 163018079863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11992 : Bounds (30543183 / 62500000) (488690929 / 1000000000) (Real.log (163018079863 / 100000000000)) := by
  have h := reflection_log_11992_neg
  have he : Real.log (163018079863 / 100000000000) = -Real.log (100000000000 / 163018079863) := by
    rw [show ((163018079863 / 100000000000) : ℝ) = ((100000000000 / 163018079863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11993_neg : (992087269 / 1000000000) ≤ -Real.log (500000000000 / 1348428835489) ∧
    -Real.log (500000000000 / 1348428835489) ≤ (992087271 / 1000000000) := by
  have h := checkLog_sound (w := (348428835489 / 2348428835489)) (n := 12)
    (lo := (298940089 / 1000000000)) (hi := (29894009 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1348428835489 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1348428835489 / 1000000000000) = 1/(500000000000 / 1348428835489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11993 : Bounds (992087269 / 1000000000) (992087271 / 1000000000) (Real.log (1348428835489 / 500000000000)) := by
  have h := reflection_log_11993_neg
  have he : Real.log (1348428835489 / 500000000000) = -Real.log (500000000000 / 1348428835489) := by
    rw [show ((1348428835489 / 500000000000) : ℝ) = ((500000000000 / 1348428835489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11994_neg : (497311287 / 500000000) ≤ -Real.log (125000000000 / 337962962963) ∧
    -Real.log (125000000000 / 337962962963) ≤ (62163911 / 62500000) := by
  have h := checkLog_sound (w := (87962962963 / 587962962963)) (n := 12)
    (lo := (150737697 / 500000000)) (hi := (60295079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((337962962963 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(337962962963 / 250000000000) = 1/(125000000000 / 337962962963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11994 : Bounds (497311287 / 500000000) (62163911 / 62500000) (Real.log (337962962963 / 125000000000)) := by
  have h := reflection_log_11994_neg
  have he : Real.log (337962962963 / 125000000000) = -Real.log (125000000000 / 337962962963) := by
    rw [show ((337962962963 / 125000000000) : ℝ) = ((125000000000 / 337962962963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11995_neg : (94780283 / 250000000) ≤ -Real.log (1000 / 1461) ∧
    -Real.log (1000 / 1461) ≤ (379121133 / 1000000000) := by
  have h := checkLog_sound (w := (461 / 2461)) (n := 12)
    (lo := (94780283 / 250000000)) (hi := (379121133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1461 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1461 / 1000) = 1/(1000 / 1461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11995 : Bounds (94780283 / 250000000) (379121133 / 1000000000) (Real.log (1461 / 1000)) := by
  have h := reflection_log_11995_neg
  have he : Real.log (1461 / 1000) = -Real.log (1000 / 1461) := by
    rw [show ((1461 / 1000) : ℝ) = ((1000 / 1461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11996_neg : (154509927 / 250000000) ≤ -Real.log (539 / 1000) ∧
    -Real.log (539 / 1000) ≤ (618039709 / 1000000000) := by
  have h := checkLog_sound (w := (461 / 1539)) (n := 12)
    (lo := (154509927 / 250000000)) (hi := (618039709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 539) = 1/(539 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11996 : Bounds (-618039709 / 1000000000) (-154509927 / 250000000) (Real.log (539 / 1000)) := by
  have h := reflection_log_11996_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11997_neg : (460893 / 1000000000) ≤ -Real.log (1000000 / 1000461) ∧
    -Real.log (1000000 / 1000461) ≤ (230447 / 500000000) := by
  have h := checkLog_sound (w := (461 / 2000461)) (n := 12)
    (lo := (460893 / 1000000000)) (hi := (230447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000461 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000461 / 1000000) = 1/(1000000 / 1000461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11997 : Bounds (460893 / 1000000000) (230447 / 500000000) (Real.log (1000461 / 1000000)) := by
  have h := reflection_log_11997_neg
  have he : Real.log (1000461 / 1000000) = -Real.log (1000000 / 1000461) := by
    rw [show ((1000461 / 1000000) : ℝ) = ((1000000 / 1000461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11998_neg : (230553 / 500000000) ≤ -Real.log (999539 / 1000000) ∧
    -Real.log (999539 / 1000000) ≤ (461107 / 1000000000) := by
  have h := checkLog_sound (w := (461 / 1999539)) (n := 12)
    (lo := (230553 / 500000000)) (hi := (461107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999539) = 1/(999539 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11998 : Bounds (-461107 / 1000000000) (-230553 / 500000000) (Real.log (999539 / 1000000)) := by
  have h := reflection_log_11998_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11999_neg : (42885939 / 200000000) ≤ -Real.log (200000 / 247831) ∧
    -Real.log (200000 / 247831) ≤ (418808 / 1953125) := by
  have h := checkLog_sound (w := (47831 / 447831)) (n := 12)
    (lo := (42885939 / 200000000)) (hi := (418808 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247831 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247831 / 200000) = 1/(200000 / 247831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11999 : Bounds (42885939 / 200000000) (418808 / 1953125) (Real.log (247831 / 200000)) := by
  have h := reflection_log_11999_neg
  have he : Real.log (247831 / 200000) = -Real.log (200000 / 247831) := by
    rw [show ((247831 / 200000) : ℝ) = ((200000 / 247831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12000_neg : (273325621 / 1000000000) ≤ -Real.log (152169 / 200000) ∧
    -Real.log (152169 / 200000) ≤ (136662811 / 500000000) := by
  have h := checkLog_sound (w := (47831 / 352169)) (n := 12)
    (lo := (273325621 / 1000000000)) (hi := (136662811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 152169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 152169) = 1/(152169 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12000 : Bounds (-136662811 / 500000000) (-273325621 / 1000000000) (Real.log (152169 / 200000)) := by
  have h := reflection_log_12000_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12001_neg : (215240403 / 1000000000) ≤ -Real.log (6250 / 7751) ∧
    -Real.log (6250 / 7751) ≤ (53810101 / 250000000) := by
  have h := checkLog_sound (w := (1501 / 14001)) (n := 12)
    (lo := (215240403 / 1000000000)) (hi := (53810101 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7751 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7751 / 6250) = 1/(6250 / 7751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12001 : Bounds (215240403 / 1000000000) (53810101 / 250000000) (Real.log (7751 / 6250)) := by
  have h := reflection_log_12001_neg
  have he : Real.log (7751 / 6250) = -Real.log (6250 / 7751) := by
    rw [show ((7751 / 6250) : ℝ) = ((6250 / 7751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12002_neg : (137323697 / 500000000) ≤ -Real.log (4749 / 6250) ∧
    -Real.log (4749 / 6250) ≤ (54929479 / 200000000) := by
  have h := checkLog_sound (w := (1501 / 10999)) (n := 12)
    (lo := (137323697 / 500000000)) (hi := (54929479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 4749) = 1/(4749 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12002 : Bounds (-54929479 / 200000000) (-137323697 / 500000000) (Real.log (4749 / 6250)) := by
  have h := reflection_log_12002_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12003_neg : (5940699 / 100000000) ≤ -Real.log (36809499 / 39062500) ∧
    -Real.log (36809499 / 39062500) ≤ (59406991 / 1000000000) := by
  have h := checkLog_sound (w := (2253001 / 75871999)) (n := 12)
    (lo := (5940699 / 100000000)) (hi := (59406991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39062500 / 36809499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39062500 / 36809499) = 1/(36809499 / 39062500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12003 : Bounds (-59406991 / 1000000000) (-5940699 / 100000000) (Real.log (36809499 / 39062500)) := by
  have h := reflection_log_12003_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12004_neg : (2355837 / 40000000) ≤ -Real.log (37712195439 / 40000000000) ∧
    -Real.log (37712195439 / 40000000000) ≤ (29447963 / 500000000) := by
  have h := checkLog_sound (w := (2287804561 / 77712195439)) (n := 12)
    (lo := (2355837 / 40000000)) (hi := (29447963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37712195439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37712195439) = 1/(37712195439 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12004 : Bounds (-29447963 / 500000000) (-2355837 / 40000000) (Real.log (37712195439 / 40000000000)) := by
  have h := reflection_log_12004_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12005_neg : (121938829 / 250000000) ≤ -Real.log (125000000000 / 203582037077) ∧
    -Real.log (125000000000 / 203582037077) ≤ (487755317 / 1000000000) := by
  have h := checkLog_sound (w := (78582037077 / 328582037077)) (n := 12)
    (lo := (121938829 / 250000000)) (hi := (487755317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((203582037077 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(203582037077 / 125000000000) = 1/(125000000000 / 203582037077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12005 : Bounds (121938829 / 250000000) (487755317 / 1000000000) (Real.log (203582037077 / 125000000000)) := by
  have h := reflection_log_12005_neg
  have he : Real.log (203582037077 / 125000000000) = -Real.log (125000000000 / 203582037077) := by
    rw [show ((203582037077 / 125000000000) : ℝ) = ((125000000000 / 203582037077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12006_neg : (489887797 / 1000000000) ≤ -Real.log (20000000000 / 32642661613) ∧
    -Real.log (20000000000 / 32642661613) ≤ (244943899 / 500000000) := by
  have h := checkLog_sound (w := (12642661613 / 52642661613)) (n := 12)
    (lo := (489887797 / 1000000000)) (hi := (244943899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32642661613 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32642661613 / 20000000000) = 1/(20000000000 / 32642661613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12006 : Bounds (489887797 / 1000000000) (244943899 / 500000000) (Real.log (32642661613 / 20000000000)) := by
  have h := reflection_log_12006_neg
  have he : Real.log (32642661613 / 20000000000) = -Real.log (20000000000 / 32642661613) := by
    rw [show ((32642661613 / 20000000000) : ℝ) = ((20000000000 / 32642661613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12007_neg : (497311287 / 500000000) ≤ -Real.log (500000000000 / 1351851851851) ∧
    -Real.log (500000000000 / 1351851851851) ≤ (62163911 / 62500000) := by
  have h := checkLog_sound (w := (351851851851 / 2351851851851)) (n := 12)
    (lo := (150737697 / 500000000)) (hi := (60295079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1351851851851 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1351851851851 / 1000000000000) = 1/(500000000000 / 1351851851851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12007 : Bounds (497311287 / 500000000) (62163911 / 62500000) (Real.log (1351851851851 / 500000000000)) := by
  have h := reflection_log_12007_neg
  have he : Real.log (1351851851851 / 500000000000) = -Real.log (500000000000 / 1351851851851) := by
    rw [show ((1351851851851 / 500000000000) : ℝ) = ((500000000000 / 1351851851851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12008_neg : (24929021 / 25000000) ≤ -Real.log (250000000000 / 677643784787) ∧
    -Real.log (250000000000 / 677643784787) ≤ (498580421 / 500000000) := by
  have h := checkLog_sound (w := (177643784787 / 1177643784787)) (n := 12)
    (lo := (15200683 / 50000000)) (hi := (304013661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677643784787 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(677643784787 / 500000000000) = 1/(250000000000 / 677643784787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12008 : Bounds (24929021 / 25000000) (498580421 / 500000000) (Real.log (677643784787 / 250000000000)) := by
  have h := reflection_log_12008_neg
  have he : Real.log (677643784787 / 250000000000) = -Real.log (250000000000 / 677643784787) := by
    rw [show ((677643784787 / 250000000000) : ℝ) = ((250000000000 / 677643784787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12009_neg : (379805361 / 1000000000) ≤ -Real.log (500 / 731) ∧
    -Real.log (500 / 731) ≤ (189902681 / 500000000) := by
  have h := checkLog_sound (w := (231 / 1231)) (n := 12)
    (lo := (379805361 / 1000000000)) (hi := (189902681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731 / 500) = 1/(500 / 731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12009 : Bounds (379805361 / 1000000000) (189902681 / 500000000) (Real.log (731 / 500)) := by
  have h := reflection_log_12009_neg
  have he : Real.log (731 / 500) = -Real.log (500 / 731) := by
    rw [show ((731 / 500) : ℝ) = ((500 / 731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12010_neg : (309948359 / 500000000) ≤ -Real.log (269 / 500) ∧
    -Real.log (269 / 500) ≤ (619896719 / 1000000000) := by
  have h := checkLog_sound (w := (231 / 769)) (n := 12)
    (lo := (309948359 / 500000000)) (hi := (619896719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 269) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 269) = 1/(269 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12010 : Bounds (-619896719 / 1000000000) (-309948359 / 500000000) (Real.log (269 / 500)) := by
  have h := reflection_log_12010_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12011_neg : (461893 / 1000000000) ≤ -Real.log (500000 / 500231) ∧
    -Real.log (500000 / 500231) ≤ (230947 / 500000000) := by
  have h := checkLog_sound (w := (231 / 1000231)) (n := 12)
    (lo := (461893 / 1000000000)) (hi := (230947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500231 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500231 / 500000) = 1/(500000 / 500231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12011 : Bounds (461893 / 1000000000) (230947 / 500000000) (Real.log (500231 / 500000)) := by
  have h := reflection_log_12011_neg
  have he : Real.log (500231 / 500000) = -Real.log (500000 / 500231) := by
    rw [show ((500231 / 500000) : ℝ) = ((500000 / 500231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12012_neg : (231053 / 500000000) ≤ -Real.log (499769 / 500000) ∧
    -Real.log (499769 / 500000) ≤ (462107 / 1000000000) := by
  have h := checkLog_sound (w := (231 / 999769)) (n := 12)
    (lo := (231053 / 500000000)) (hi := (462107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499769) = 1/(499769 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12012 : Bounds (-462107 / 1000000000) (-231053 / 500000000) (Real.log (499769 / 500000)) := by
  have h := reflection_log_12012_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12013_neg : (107441967 / 500000000) ≤ -Real.log (500000 / 619859) ∧
    -Real.log (500000 / 619859) ≤ (42976787 / 200000000) := by
  have h := checkLog_sound (w := (119859 / 1119859)) (n := 12)
    (lo := (107441967 / 500000000)) (hi := (42976787 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619859 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(619859 / 500000) = 1/(500000 / 619859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12013 : Bounds (107441967 / 500000000) (42976787 / 200000000) (Real.log (619859 / 500000)) := by
  have h := reflection_log_12013_neg
  have he : Real.log (619859 / 500000) = -Real.log (500000 / 619859) := by
    rw [show ((619859 / 500000) : ℝ) = ((500000 / 619859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12014_neg : (274065861 / 1000000000) ≤ -Real.log (380141 / 500000) ∧
    -Real.log (380141 / 500000) ≤ (137032931 / 500000000) := by
  have h := checkLog_sound (w := (119859 / 880141)) (n := 12)
    (lo := (274065861 / 1000000000)) (hi := (137032931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 380141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 380141) = 1/(380141 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12014 : Bounds (-137032931 / 500000000) (-274065861 / 1000000000) (Real.log (380141 / 500000)) := by
  have h := reflection_log_12014_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12015_neg : (107847943 / 500000000) ≤ -Real.log (40000 / 49629) ∧
    -Real.log (40000 / 49629) ≤ (215695887 / 1000000000) := by
  have h := checkLog_sound (w := (9629 / 89629)) (n := 12)
    (lo := (107847943 / 500000000)) (hi := (215695887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49629 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49629 / 40000) = 1/(40000 / 49629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12015 : Bounds (107847943 / 500000000) (215695887 / 1000000000) (Real.log (49629 / 40000)) := by
  have h := reflection_log_12015_neg
  have he : Real.log (49629 / 40000) = -Real.log (40000 / 49629) := by
    rw [show ((49629 / 40000) : ℝ) = ((40000 / 49629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12016_neg : (17211953 / 62500000) ≤ -Real.log (30371 / 40000) ∧
    -Real.log (30371 / 40000) ≤ (275391249 / 1000000000) := by
  have h := checkLog_sound (w := (9629 / 70371)) (n := 12)
    (lo := (17211953 / 62500000)) (hi := (275391249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 30371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 30371) = 1/(30371 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12016 : Bounds (-275391249 / 1000000000) (-17211953 / 62500000) (Real.log (30371 / 40000)) := by
  have h := reflection_log_12016_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12017_neg : (29847681 / 500000000) ≤ -Real.log (1507282359 / 1600000000) ∧
    -Real.log (1507282359 / 1600000000) ≤ (59695363 / 1000000000) := by
  have h := checkLog_sound (w := (92717641 / 3107282359)) (n := 12)
    (lo := (29847681 / 500000000)) (hi := (59695363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1507282359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1507282359) = 1/(1507282359 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12017 : Bounds (-59695363 / 1000000000) (-29847681 / 500000000) (Real.log (1507282359 / 1600000000)) := by
  have h := reflection_log_12017_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12018_neg : (59181927 / 1000000000) ≤ -Real.log (235633820119 / 250000000000) ∧
    -Real.log (235633820119 / 250000000000) ≤ (7397741 / 125000000) := by
  have h := checkLog_sound (w := (14366179881 / 485633820119)) (n := 12)
    (lo := (59181927 / 1000000000)) (hi := (7397741 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 235633820119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 235633820119) = 1/(235633820119 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12018 : Bounds (-7397741 / 125000000) (-59181927 / 1000000000) (Real.log (235633820119 / 250000000000)) := by
  have h := reflection_log_12018_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12019_neg : (122237449 / 250000000) ≤ -Real.log (125000000000 / 203825356907) ∧
    -Real.log (125000000000 / 203825356907) ≤ (488949797 / 1000000000) := by
  have h := checkLog_sound (w := (78825356907 / 328825356907)) (n := 12)
    (lo := (122237449 / 250000000)) (hi := (488949797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((203825356907 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(203825356907 / 125000000000) = 1/(125000000000 / 203825356907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12019 : Bounds (122237449 / 250000000) (488949797 / 1000000000) (Real.log (203825356907 / 125000000000)) := by
  have h := reflection_log_12019_neg
  have he : Real.log (203825356907 / 125000000000) = -Real.log (125000000000 / 203825356907) := by
    rw [show ((203825356907 / 125000000000) : ℝ) = ((125000000000 / 203825356907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12020_neg : (245543567 / 500000000) ≤ -Real.log (500000000000 / 817045866123) ∧
    -Real.log (500000000000 / 817045866123) ≤ (98217427 / 200000000) := by
  have h := checkLog_sound (w := (317045866123 / 1317045866123)) (n := 12)
    (lo := (245543567 / 500000000)) (hi := (98217427 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((817045866123 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(817045866123 / 500000000000) = 1/(500000000000 / 817045866123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12020 : Bounds (245543567 / 500000000) (98217427 / 200000000) (Real.log (817045866123 / 500000000000)) := by
  have h := reflection_log_12020_neg
  have he : Real.log (817045866123 / 500000000000) = -Real.log (500000000000 / 817045866123) := by
    rw [show ((817045866123 / 500000000000) : ℝ) = ((500000000000 / 817045866123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12021_neg : (24929021 / 25000000) ≤ -Real.log (500000000000 / 1355287569573) ∧
    -Real.log (500000000000 / 1355287569573) ≤ (498580421 / 500000000) := by
  have h := checkLog_sound (w := (355287569573 / 2355287569573)) (n := 12)
    (lo := (15200683 / 50000000)) (hi := (304013661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1355287569573 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1355287569573 / 1000000000000) = 1/(500000000000 / 1355287569573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12021 : Bounds (24929021 / 25000000) (498580421 / 500000000) (Real.log (1355287569573 / 500000000000)) := by
  have h := reflection_log_12021_neg
  have he : Real.log (1355287569573 / 500000000000) = -Real.log (500000000000 / 1355287569573) := by
    rw [show ((1355287569573 / 500000000000) : ℝ) = ((500000000000 / 1355287569573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12022_neg : (999702079 / 1000000000) ≤ -Real.log (12500000000 / 33968401487) ∧
    -Real.log (12500000000 / 33968401487) ≤ (999702081 / 1000000000) := by
  have h := checkLog_sound (w := (8968401487 / 58968401487)) (n := 12)
    (lo := (306554899 / 1000000000)) (hi := (3065549 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33968401487 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(33968401487 / 25000000000) = 1/(12500000000 / 33968401487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12022 : Bounds (999702079 / 1000000000) (999702081 / 1000000000) (Real.log (33968401487 / 12500000000)) := by
  have h := reflection_log_12022_neg
  have he : Real.log (33968401487 / 12500000000) = -Real.log (12500000000 / 33968401487) := by
    rw [show ((33968401487 / 12500000000) : ℝ) = ((12500000000 / 33968401487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12023_neg : (190244561 / 500000000) ≤ -Real.log (1000 / 1463) ∧
    -Real.log (1000 / 1463) ≤ (380489123 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 2463)) (n := 12)
    (lo := (190244561 / 500000000)) (hi := (380489123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1463 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1463 / 1000) = 1/(1000 / 1463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12023 : Bounds (190244561 / 500000000) (380489123 / 1000000000) (Real.log (1463 / 1000)) := by
  have h := reflection_log_12023_neg
  have he : Real.log (1463 / 1000) = -Real.log (1000 / 1463) := by
    rw [show ((1463 / 1000) : ℝ) = ((1000 / 1463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12024_neg : (2428739 / 3906250) ≤ -Real.log (537 / 1000) ∧
    -Real.log (537 / 1000) ≤ (124351437 / 200000000) := by
  have h := checkLog_sound (w := (463 / 1537)) (n := 12)
    (lo := (2428739 / 3906250)) (hi := (124351437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 537) = 1/(537 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12024 : Bounds (-124351437 / 200000000) (-2428739 / 3906250) (Real.log (537 / 1000)) := by
  have h := reflection_log_12024_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12025_neg : (115723 / 250000000) ≤ -Real.log (1000000 / 1000463) ∧
    -Real.log (1000000 / 1000463) ≤ (462893 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 2000463)) (n := 12)
    (lo := (115723 / 250000000)) (hi := (462893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000463 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000463 / 1000000) = 1/(1000000 / 1000463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12025 : Bounds (115723 / 250000000) (462893 / 1000000000) (Real.log (1000463 / 1000000)) := by
  have h := reflection_log_12025_neg
  have he : Real.log (1000463 / 1000000) = -Real.log (1000000 / 1000463) := by
    rw [show ((1000463 / 1000000) : ℝ) = ((1000000 / 1000463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12026_neg : (463107 / 1000000000) ≤ -Real.log (999537 / 1000000) ∧
    -Real.log (999537 / 1000000) ≤ (115777 / 250000000) := by
  have h := checkLog_sound (w := (463 / 1999537)) (n := 12)
    (lo := (463107 / 1000000000)) (hi := (115777 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999537) = 1/(999537 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12026 : Bounds (-115777 / 250000000) (-463107 / 1000000000) (Real.log (999537 / 1000000)) := by
  have h := reflection_log_12026_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12027_neg : (215338773 / 1000000000) ≤ -Real.log (500000 / 620141) ∧
    -Real.log (500000 / 620141) ≤ (107669387 / 500000000) := by
  have h := checkLog_sound (w := (120141 / 1120141)) (n := 12)
    (lo := (215338773 / 1000000000)) (hi := (107669387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((620141 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(620141 / 500000) = 1/(500000 / 620141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12027 : Bounds (215338773 / 1000000000) (107669387 / 500000000) (Real.log (620141 / 500000)) := by
  have h := reflection_log_12027_neg
  have he : Real.log (620141 / 500000) = -Real.log (500000 / 620141) := by
    rw [show ((620141 / 500000) : ℝ) = ((500000 / 620141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12028_neg : (274807967 / 1000000000) ≤ -Real.log (379859 / 500000) ∧
    -Real.log (379859 / 500000) ≤ (8587749 / 31250000) := by
  have h := checkLog_sound (w := (120141 / 879859)) (n := 12)
    (lo := (274807967 / 1000000000)) (hi := (8587749 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 379859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 379859) = 1/(379859 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12028 : Bounds (-8587749 / 31250000) (-274807967 / 1000000000) (Real.log (379859 / 500000)) := by
  have h := reflection_log_12028_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12029_neg : (216151161 / 1000000000) ≤ -Real.log (100000 / 124129) ∧
    -Real.log (100000 / 124129) ≤ (108075581 / 500000000) := by
  have h := checkLog_sound (w := (24129 / 224129)) (n := 12)
    (lo := (216151161 / 1000000000)) (hi := (108075581 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((124129 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(124129 / 100000) = 1/(100000 / 124129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12029 : Bounds (216151161 / 1000000000) (108075581 / 500000000) (Real.log (124129 / 100000)) := by
  have h := reflection_log_12029_neg
  have he : Real.log (124129 / 100000) = -Real.log (100000 / 124129) := by
    rw [show ((124129 / 100000) : ℝ) = ((100000 / 124129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12030_neg : (34516957 / 125000000) ≤ -Real.log (75871 / 100000) ∧
    -Real.log (75871 / 100000) ≤ (276135657 / 1000000000) := by
  have h := checkLog_sound (w := (24129 / 175871)) (n := 12)
    (lo := (34516957 / 125000000)) (hi := (276135657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 75871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 75871) = 1/(75871 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12030 : Bounds (-276135657 / 1000000000) (-34516957 / 125000000) (Real.log (75871 / 100000)) := by
  have h := reflection_log_12030_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12031_neg : (29992247 / 500000000) ≤ -Real.log (9417791359 / 10000000000) ∧
    -Real.log (9417791359 / 10000000000) ≤ (11996899 / 200000000) := by
  have h := checkLog_sound (w := (582208641 / 19417791359)) (n := 12)
    (lo := (29992247 / 500000000)) (hi := (11996899 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9417791359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9417791359) = 1/(9417791359 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12031 : Bounds (-11996899 / 200000000) (-29992247 / 500000000) (Real.log (9417791359 / 10000000000)) := by
  have h := reflection_log_12031_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0188 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12032_neg : (29734597 / 500000000) ≤ -Real.log (235566140119 / 250000000000) ∧
    -Real.log (235566140119 / 250000000000) ≤ (11893839 / 200000000) := by
  have h := checkLog_sound (w := (14433859881 / 485566140119)) (n := 12)
    (lo := (29734597 / 500000000)) (hi := (11893839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 235566140119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 235566140119) = 1/(235566140119 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12032 : Bounds (-11893839 / 200000000) (-29734597 / 500000000) (Real.log (235566140119 / 250000000000)) := by
  have h := reflection_log_12032_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12033_neg : (24507337 / 50000000) ≤ -Real.log (62500000000 / 102034735257) ∧
    -Real.log (62500000000 / 102034735257) ≤ (490146741 / 1000000000) := by
  have h := checkLog_sound (w := (39534735257 / 164534735257)) (n := 12)
    (lo := (24507337 / 50000000)) (hi := (490146741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102034735257 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102034735257 / 62500000000) = 1/(62500000000 / 102034735257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12033 : Bounds (24507337 / 50000000) (490146741 / 1000000000) (Real.log (102034735257 / 62500000000)) := by
  have h := reflection_log_12033_neg
  have he : Real.log (102034735257 / 62500000000) = -Real.log (62500000000 / 102034735257) := by
    rw [show ((102034735257 / 62500000000) : ℝ) = ((62500000000 / 102034735257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12034_neg : (492286817 / 1000000000) ≤ -Real.log (500000000000 / 818026650499) ∧
    -Real.log (500000000000 / 818026650499) ≤ (246143409 / 500000000) := by
  have h := checkLog_sound (w := (318026650499 / 1318026650499)) (n := 12)
    (lo := (492286817 / 1000000000)) (hi := (246143409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((818026650499 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(818026650499 / 500000000000) = 1/(500000000000 / 818026650499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12034 : Bounds (492286817 / 1000000000) (246143409 / 500000000) (Real.log (818026650499 / 500000000000)) := by
  have h := reflection_log_12034_neg
  have he : Real.log (818026650499 / 500000000000) = -Real.log (500000000000 / 818026650499) := by
    rw [show ((818026650499 / 500000000000) : ℝ) = ((500000000000 / 818026650499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12035_neg : (999702079 / 1000000000) ≤ -Real.log (500000000000 / 1358736059479) ∧
    -Real.log (500000000000 / 1358736059479) ≤ (999702081 / 1000000000) := by
  have h := checkLog_sound (w := (358736059479 / 2358736059479)) (n := 12)
    (lo := (306554899 / 1000000000)) (hi := (3065549 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1358736059479 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1358736059479 / 1000000000000) = 1/(500000000000 / 1358736059479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12035 : Bounds (999702079 / 1000000000) (999702081 / 1000000000) (Real.log (1358736059479 / 500000000000)) := by
  have h := reflection_log_12035_neg
  have he : Real.log (1358736059479 / 500000000000) = -Real.log (500000000000 / 1358736059479) := by
    rw [show ((1358736059479 / 500000000000) : ℝ) = ((500000000000 / 1358736059479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12036_neg : (200449261 / 200000000) ≤ -Real.log (125000000000 / 340549348231) ∧
    -Real.log (125000000000 / 340549348231) ≤ (1002246307 / 1000000000) := by
  have h := checkLog_sound (w := (90549348231 / 590549348231)) (n := 12)
    (lo := (2472793 / 8000000)) (hi := (154549563 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340549348231 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(340549348231 / 250000000000) = 1/(125000000000 / 340549348231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12036 : Bounds (200449261 / 200000000) (1002246307 / 1000000000) (Real.log (340549348231 / 125000000000)) := by
  have h := reflection_log_12036_neg
  have he : Real.log (340549348231 / 125000000000) = -Real.log (125000000000 / 340549348231) := by
    rw [show ((340549348231 / 125000000000) : ℝ) = ((125000000000 / 340549348231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12037_neg : (76234483 / 200000000) ≤ -Real.log (125 / 183) ∧
    -Real.log (125 / 183) ≤ (5955819 / 15625000) := by
  have h := checkLog_sound (w := (29 / 154)) (n := 12)
    (lo := (76234483 / 200000000)) (hi := (5955819 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183 / 125) = 1/(125 / 183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12037 : Bounds (76234483 / 200000000) (5955819 / 15625000) (Real.log (183 / 125)) := by
  have h := reflection_log_12037_neg
  have he : Real.log (183 / 125) = -Real.log (125 / 183) := by
    rw [show ((183 / 125) : ℝ) = ((125 / 183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12038_neg : (623621117 / 1000000000) ≤ -Real.log (67 / 125) ∧
    -Real.log (67 / 125) ≤ (311810559 / 500000000) := by
  have h := checkLog_sound (w := (29 / 96)) (n := 12)
    (lo := (623621117 / 1000000000)) (hi := (311810559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 67) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 67) = 1/(67 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12038 : Bounds (-311810559 / 500000000) (-623621117 / 1000000000) (Real.log (67 / 125)) := by
  have h := reflection_log_12038_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12039_neg : (115973 / 250000000) ≤ -Real.log (62500 / 62529) ∧
    -Real.log (62500 / 62529) ≤ (463893 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 125029)) (n := 12)
    (lo := (115973 / 250000000)) (hi := (463893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62529 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62529 / 62500) = 1/(62500 / 62529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12039 : Bounds (115973 / 250000000) (463893 / 1000000000) (Real.log (62529 / 62500)) := by
  have h := reflection_log_12039_neg
  have he : Real.log (62529 / 62500) = -Real.log (62500 / 62529) := by
    rw [show ((62529 / 62500) : ℝ) = ((62500 / 62529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12040_neg : (464107 / 1000000000) ≤ -Real.log (62471 / 62500) ∧
    -Real.log (62471 / 62500) ≤ (116027 / 250000000) := by
  have h := checkLog_sound (w := (29 / 124971)) (n := 12)
    (lo := (464107 / 1000000000)) (hi := (116027 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62471) = 1/(62471 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12040 : Bounds (-116027 / 250000000) (-464107 / 1000000000) (Real.log (62471 / 62500)) := by
  have h := reflection_log_12040_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12041_neg : (21579421 / 100000000) ≤ -Real.log (1000000 / 1240847) ∧
    -Real.log (1000000 / 1240847) ≤ (215794211 / 1000000000) := by
  have h := checkLog_sound (w := (240847 / 2240847)) (n := 12)
    (lo := (21579421 / 100000000)) (hi := (215794211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1240847 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1240847 / 1000000) = 1/(1000000 / 1240847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12041 : Bounds (21579421 / 100000000) (215794211 / 1000000000) (Real.log (1240847 / 1000000)) := by
  have h := reflection_log_12041_neg
  have he : Real.log (1240847 / 1000000) = -Real.log (1000000 / 1240847) := by
    rw [show ((1240847 / 1000000) : ℝ) = ((1000000 / 1240847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12042_neg : (13777597 / 50000000) ≤ -Real.log (759153 / 1000000) ∧
    -Real.log (759153 / 1000000) ≤ (275551941 / 1000000000) := by
  have h := checkLog_sound (w := (240847 / 1759153)) (n := 12)
    (lo := (13777597 / 50000000)) (hi := (275551941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 759153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 759153) = 1/(759153 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12042 : Bounds (-275551941 / 1000000000) (-13777597 / 50000000) (Real.log (759153 / 1000000)) := by
  have h := reflection_log_12042_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12043_neg : (108303517 / 500000000) ≤ -Real.log (15625 / 19404) ∧
    -Real.log (15625 / 19404) ≤ (43321407 / 200000000) := by
  have h := checkLog_sound (w := (3779 / 35029)) (n := 12)
    (lo := (108303517 / 500000000)) (hi := (43321407 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19404 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19404 / 15625) = 1/(15625 / 19404) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12043 : Bounds (108303517 / 500000000) (43321407 / 200000000) (Real.log (19404 / 15625)) := by
  have h := reflection_log_12043_neg
  have he : Real.log (19404 / 15625) = -Real.log (15625 / 19404) := by
    rw [show ((19404 / 15625) : ℝ) = ((15625 / 19404) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12044_neg : (276881937 / 1000000000) ≤ -Real.log (11846 / 15625) ∧
    -Real.log (11846 / 15625) ≤ (138440969 / 500000000) := by
  have h := checkLog_sound (w := (3779 / 27471)) (n := 12)
    (lo := (276881937 / 1000000000)) (hi := (138440969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11846) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11846) = 1/(11846 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12044 : Bounds (-138440969 / 500000000) (-276881937 / 1000000000) (Real.log (11846 / 15625)) := by
  have h := reflection_log_12044_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12045_neg : (60274903 / 1000000000) ≤ -Real.log (229859784 / 244140625) ∧
    -Real.log (229859784 / 244140625) ≤ (7534363 / 125000000) := by
  have h := checkLog_sound (w := (14280841 / 474000409)) (n := 12)
    (lo := (60274903 / 1000000000)) (hi := (7534363 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 229859784) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 229859784) = 1/(229859784 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12045 : Bounds (-7534363 / 125000000) (-60274903 / 1000000000) (Real.log (229859784 / 244140625)) := by
  have h := reflection_log_12045_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12046_neg : (59757729 / 1000000000) ≤ -Real.log (941992722591 / 1000000000000) ∧
    -Real.log (941992722591 / 1000000000000) ≤ (5975773 / 100000000) := by
  have h := checkLog_sound (w := (58007277409 / 1941992722591)) (n := 12)
    (lo := (59757729 / 1000000000)) (hi := (5975773 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 941992722591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 941992722591) = 1/(941992722591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12046 : Bounds (-5975773 / 100000000) (-59757729 / 1000000000) (Real.log (941992722591 / 1000000000000)) := by
  have h := reflection_log_12046_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12047_neg : (491346151 / 1000000000) ≤ -Real.log (15625000000 / 25539297579) ∧
    -Real.log (15625000000 / 25539297579) ≤ (61418269 / 125000000) := by
  have h := checkLog_sound (w := (9914297579 / 41164297579)) (n := 12)
    (lo := (491346151 / 1000000000)) (hi := (61418269 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25539297579 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25539297579 / 15625000000) = 1/(15625000000 / 25539297579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12047 : Bounds (491346151 / 1000000000) (61418269 / 125000000) (Real.log (25539297579 / 15625000000)) := by
  have h := reflection_log_12047_neg
  have he : Real.log (25539297579 / 15625000000) = -Real.log (15625000000 / 25539297579) := by
    rw [show ((25539297579 / 15625000000) : ℝ) = ((15625000000 / 25539297579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12048_neg : (123372243 / 250000000) ≤ -Real.log (250000000000 / 409505318251) ∧
    -Real.log (250000000000 / 409505318251) ≤ (493488973 / 1000000000) := by
  have h := checkLog_sound (w := (159505318251 / 659505318251)) (n := 12)
    (lo := (123372243 / 250000000)) (hi := (493488973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((409505318251 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(409505318251 / 250000000000) = 1/(250000000000 / 409505318251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12048 : Bounds (123372243 / 250000000) (493488973 / 1000000000) (Real.log (409505318251 / 250000000000)) := by
  have h := reflection_log_12048_neg
  have he : Real.log (409505318251 / 250000000000) = -Real.log (250000000000 / 409505318251) := by
    rw [show ((409505318251 / 250000000000) : ℝ) = ((250000000000 / 409505318251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12049_neg : (200449261 / 200000000) ≤ -Real.log (500000000000 / 1362197392923) ∧
    -Real.log (500000000000 / 1362197392923) ≤ (1002246307 / 1000000000) := by
  have h := checkLog_sound (w := (362197392923 / 2362197392923)) (n := 12)
    (lo := (2472793 / 8000000)) (hi := (154549563 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1362197392923 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1362197392923 / 1000000000000) = 1/(500000000000 / 1362197392923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12049 : Bounds (200449261 / 200000000) (1002246307 / 1000000000) (Real.log (1362197392923 / 500000000000)) := by
  have h := reflection_log_12049_neg
  have he : Real.log (1362197392923 / 500000000000) = -Real.log (500000000000 / 1362197392923) := by
    rw [show ((1362197392923 / 500000000000) : ℝ) = ((500000000000 / 1362197392923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12050_neg : (251198383 / 250000000) ≤ -Real.log (7812500000 / 21338619403) ∧
    -Real.log (7812500000 / 21338619403) ≤ (502396767 / 500000000) := by
  have h := checkLog_sound (w := (5713619403 / 36963619403)) (n := 12)
    (lo := (19477897 / 62500000)) (hi := (311646353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21338619403 / 15625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(21338619403 / 15625000000) = 1/(7812500000 / 21338619403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12050 : Bounds (251198383 / 250000000) (502396767 / 500000000) (Real.log (21338619403 / 7812500000)) := by
  have h := reflection_log_12050_neg
  have he : Real.log (21338619403 / 7812500000) = -Real.log (7812500000 / 21338619403) := by
    rw [show ((21338619403 / 7812500000) : ℝ) = ((7812500000 / 21338619403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12051_neg : (190927621 / 500000000) ≤ -Real.log (200 / 293) ∧
    -Real.log (200 / 293) ≤ (381855243 / 1000000000) := by
  have h := checkLog_sound (w := (93 / 493)) (n := 12)
    (lo := (190927621 / 500000000)) (hi := (381855243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293 / 200) = 1/(200 / 293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12051 : Bounds (190927621 / 500000000) (381855243 / 1000000000) (Real.log (293 / 200)) := by
  have h := reflection_log_12051_neg
  have he : Real.log (293 / 200) = -Real.log (200 / 293) := by
    rw [show ((293 / 200) : ℝ) = ((200 / 293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12052_neg : (156372133 / 250000000) ≤ -Real.log (107 / 200) ∧
    -Real.log (107 / 200) ≤ (625488533 / 1000000000) := by
  have h := checkLog_sound (w := (93 / 307)) (n := 12)
    (lo := (156372133 / 250000000)) (hi := (625488533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 107) = 1/(107 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12052 : Bounds (-625488533 / 1000000000) (-156372133 / 250000000) (Real.log (107 / 200)) := by
  have h := reflection_log_12052_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12053_neg : (464891 / 1000000000) ≤ -Real.log (200000 / 200093) ∧
    -Real.log (200000 / 200093) ≤ (116223 / 250000000) := by
  have h := checkLog_sound (w := (93 / 400093)) (n := 12)
    (lo := (464891 / 1000000000)) (hi := (116223 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200093 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200093 / 200000) = 1/(200000 / 200093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12053 : Bounds (464891 / 1000000000) (116223 / 250000000) (Real.log (200093 / 200000)) := by
  have h := reflection_log_12053_neg
  have he : Real.log (200093 / 200000) = -Real.log (200000 / 200093) := by
    rw [show ((200093 / 200000) : ℝ) = ((200000 / 200093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12054_neg : (116277 / 250000000) ≤ -Real.log (199907 / 200000) ∧
    -Real.log (199907 / 200000) ≤ (465109 / 1000000000) := by
  have h := checkLog_sound (w := (93 / 399907)) (n := 12)
    (lo := (116277 / 250000000)) (hi := (465109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199907) = 1/(199907 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12054 : Bounds (-465109 / 1000000000) (-116277 / 250000000) (Real.log (199907 / 200000)) := by
  have h := reflection_log_12054_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12055_neg : (43249727 / 200000000) ≤ -Real.log (1000000 / 1241411) ∧
    -Real.log (1000000 / 1241411) ≤ (54062159 / 250000000) := by
  have h := checkLog_sound (w := (241411 / 2241411)) (n := 12)
    (lo := (43249727 / 200000000)) (hi := (54062159 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1241411 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1241411 / 1000000) = 1/(1000000 / 1241411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12055 : Bounds (43249727 / 200000000) (54062159 / 250000000) (Real.log (1241411 / 1000000)) := by
  have h := reflection_log_12055_neg
  have he : Real.log (1241411 / 1000000) = -Real.log (1000000 / 1241411) := by
    rw [show ((1241411 / 1000000) : ℝ) = ((1000000 / 1241411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12056_neg : (5525903 / 20000000) ≤ -Real.log (758589 / 1000000) ∧
    -Real.log (758589 / 1000000) ≤ (276295151 / 1000000000) := by
  have h := checkLog_sound (w := (241411 / 1758589)) (n := 12)
    (lo := (5525903 / 20000000)) (hi := (276295151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 758589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 758589) = 1/(758589 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12056 : Bounds (-276295151 / 1000000000) (-5525903 / 20000000) (Real.log (758589 / 1000000)) := by
  have h := reflection_log_12056_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12057_neg : (2170627 / 10000000) ≤ -Real.log (500000 / 621211) ∧
    -Real.log (500000 / 621211) ≤ (217062701 / 1000000000) := by
  have h := checkLog_sound (w := (121211 / 1121211)) (n := 12)
    (lo := (2170627 / 10000000)) (hi := (217062701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621211 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(621211 / 500000) = 1/(500000 / 621211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12057 : Bounds (2170627 / 10000000) (217062701 / 1000000000) (Real.log (621211 / 500000)) := by
  have h := reflection_log_12057_neg
  have he : Real.log (621211 / 500000) = -Real.log (500000 / 621211) := by
    rw [show ((621211 / 500000) : ℝ) = ((500000 / 621211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12058_neg : (34703597 / 125000000) ≤ -Real.log (378789 / 500000) ∧
    -Real.log (378789 / 500000) ≤ (277628777 / 1000000000) := by
  have h := checkLog_sound (w := (121211 / 878789)) (n := 12)
    (lo := (34703597 / 125000000)) (hi := (277628777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 378789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 378789) = 1/(378789 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12058 : Bounds (-277628777 / 1000000000) (-34703597 / 125000000) (Real.log (378789 / 500000)) := by
  have h := reflection_log_12058_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12059_neg : (15141519 / 250000000) ≤ -Real.log (235307893479 / 250000000000) ∧
    -Real.log (235307893479 / 250000000000) ≤ (60566077 / 1000000000) := by
  have h := checkLog_sound (w := (14692106521 / 485307893479)) (n := 12)
    (lo := (15141519 / 250000000)) (hi := (60566077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 235307893479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 235307893479) = 1/(235307893479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12059 : Bounds (-60566077 / 1000000000) (-15141519 / 250000000) (Real.log (235307893479 / 250000000000)) := by
  have h := reflection_log_12059_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12060_neg : (30023257 / 500000000) ≤ -Real.log (941720729079 / 1000000000000) ∧
    -Real.log (941720729079 / 1000000000000) ≤ (12009303 / 200000000) := by
  have h := checkLog_sound (w := (58279270921 / 1941720729079)) (n := 12)
    (lo := (30023257 / 500000000)) (hi := (12009303 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 941720729079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 941720729079) = 1/(941720729079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12060 : Bounds (-12009303 / 200000000) (-30023257 / 500000000) (Real.log (941720729079 / 1000000000000)) := by
  have h := reflection_log_12060_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12061_neg : (246271893 / 500000000) ≤ -Real.log (500000000000 / 818236884531) ∧
    -Real.log (500000000000 / 818236884531) ≤ (492543787 / 1000000000) := by
  have h := checkLog_sound (w := (318236884531 / 1318236884531)) (n := 12)
    (lo := (246271893 / 500000000)) (hi := (492543787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((818236884531 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(818236884531 / 500000000000) = 1/(500000000000 / 818236884531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12061 : Bounds (246271893 / 500000000) (492543787 / 1000000000) (Real.log (818236884531 / 500000000000)) := by
  have h := reflection_log_12061_neg
  have he : Real.log (818236884531 / 500000000000) = -Real.log (500000000000 / 818236884531) := by
    rw [show ((818236884531 / 500000000000) : ℝ) = ((500000000000 / 818236884531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12062_neg : (123672869 / 250000000) ≤ -Real.log (125000000000 / 204999023203) ∧
    -Real.log (125000000000 / 204999023203) ≤ (494691477 / 1000000000) := by
  have h := checkLog_sound (w := (79999023203 / 329999023203)) (n := 12)
    (lo := (123672869 / 250000000)) (hi := (494691477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204999023203 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204999023203 / 125000000000) = 1/(125000000000 / 204999023203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12062 : Bounds (123672869 / 250000000) (494691477 / 1000000000) (Real.log (204999023203 / 125000000000)) := by
  have h := reflection_log_12062_neg
  have he : Real.log (204999023203 / 125000000000) = -Real.log (125000000000 / 204999023203) := by
    rw [show ((204999023203 / 125000000000) : ℝ) = ((125000000000 / 204999023203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12063_neg : (251198383 / 250000000) ≤ -Real.log (500000000000 / 1365671641791) ∧
    -Real.log (500000000000 / 1365671641791) ≤ (502396767 / 500000000) := by
  have h := checkLog_sound (w := (365671641791 / 2365671641791)) (n := 12)
    (lo := (19477897 / 62500000)) (hi := (311646353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1365671641791 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1365671641791 / 1000000000000) = 1/(500000000000 / 1365671641791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12063 : Bounds (251198383 / 250000000) (502396767 / 500000000) (Real.log (1365671641791 / 500000000000)) := by
  have h := reflection_log_12063_neg
  have he : Real.log (1365671641791 / 500000000000) = -Real.log (500000000000 / 1365671641791) := by
    rw [show ((1365671641791 / 500000000000) : ℝ) = ((500000000000 / 1365671641791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12064_neg : (1007343773 / 1000000000) ≤ -Real.log (100000000000 / 273831775701) ∧
    -Real.log (100000000000 / 273831775701) ≤ (40293751 / 40000000) := by
  have h := checkLog_sound (w := (73831775701 / 473831775701)) (n := 12)
    (lo := (314196593 / 1000000000)) (hi := (157098297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273831775701 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(273831775701 / 200000000000) = 1/(100000000000 / 273831775701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12064 : Bounds (1007343773 / 1000000000) (40293751 / 40000000) (Real.log (273831775701 / 100000000000)) := by
  have h := reflection_log_12064_neg
  have he : Real.log (273831775701 / 100000000000) = -Real.log (100000000000 / 273831775701) := by
    rw [show ((273831775701 / 100000000000) : ℝ) = ((100000000000 / 273831775701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12065_neg : (382537603 / 1000000000) ≤ -Real.log (500 / 733) ∧
    -Real.log (500 / 733) ≤ (95634401 / 250000000) := by
  have h := checkLog_sound (w := (233 / 1233)) (n := 12)
    (lo := (382537603 / 1000000000)) (hi := (95634401 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((733 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(733 / 500) = 1/(500 / 733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12065 : Bounds (382537603 / 1000000000) (95634401 / 250000000) (Real.log (733 / 500)) := by
  have h := reflection_log_12065_neg
  have he : Real.log (733 / 500) = -Real.log (500 / 733) := by
    rw [show ((733 / 500) : ℝ) = ((500 / 733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12066_neg : (7841993 / 12500000) ≤ -Real.log (267 / 500) ∧
    -Real.log (267 / 500) ≤ (627359441 / 1000000000) := by
  have h := checkLog_sound (w := (233 / 767)) (n := 12)
    (lo := (7841993 / 12500000)) (hi := (627359441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 267) = 1/(267 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12066 : Bounds (-627359441 / 1000000000) (-7841993 / 12500000) (Real.log (267 / 500)) := by
  have h := reflection_log_12066_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12067_neg : (465891 / 1000000000) ≤ -Real.log (500000 / 500233) ∧
    -Real.log (500000 / 500233) ≤ (116473 / 250000000) := by
  have h := checkLog_sound (w := (233 / 1000233)) (n := 12)
    (lo := (465891 / 1000000000)) (hi := (116473 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500233 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500233 / 500000) = 1/(500000 / 500233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12067 : Bounds (465891 / 1000000000) (116473 / 250000000) (Real.log (500233 / 500000)) := by
  have h := reflection_log_12067_neg
  have he : Real.log (500233 / 500000) = -Real.log (500000 / 500233) := by
    rw [show ((500233 / 500000) : ℝ) = ((500000 / 500233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12068_neg : (116527 / 250000000) ≤ -Real.log (499767 / 500000) ∧
    -Real.log (499767 / 500000) ≤ (466109 / 1000000000) := by
  have h := checkLog_sound (w := (233 / 999767)) (n := 12)
    (lo := (116527 / 250000000)) (hi := (466109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499767) = 1/(499767 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12068 : Bounds (-466109 / 1000000000) (-116527 / 250000000) (Real.log (499767 / 500000)) := by
  have h := reflection_log_12068_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12069_neg : (216703659 / 1000000000) ≤ -Real.log (125000 / 155247) ∧
    -Real.log (125000 / 155247) ≤ (10835183 / 50000000) := by
  have h := checkLog_sound (w := (30247 / 280247)) (n := 12)
    (lo := (216703659 / 1000000000)) (hi := (10835183 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155247 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155247 / 125000) = 1/(125000 / 155247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12069 : Bounds (216703659 / 1000000000) (10835183 / 50000000) (Real.log (155247 / 125000)) := by
  have h := reflection_log_12069_neg
  have he : Real.log (155247 / 125000) = -Real.log (125000 / 155247) := by
    rw [show ((155247 / 125000) : ℝ) = ((125000 / 155247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12070_neg : (277040231 / 1000000000) ≤ -Real.log (94753 / 125000) ∧
    -Real.log (94753 / 125000) ≤ (34630029 / 125000000) := by
  have h := checkLog_sound (w := (30247 / 219753)) (n := 12)
    (lo := (277040231 / 1000000000)) (hi := (34630029 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 94753) = 1/(94753 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12070 : Bounds (-34630029 / 125000000) (-277040231 / 1000000000) (Real.log (94753 / 125000)) := by
  have h := reflection_log_12070_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12071_neg : (108759079 / 500000000) ≤ -Real.log (250000 / 310747) ∧
    -Real.log (250000 / 310747) ≤ (217518159 / 1000000000) := by
  have h := checkLog_sound (w := (60747 / 560747)) (n := 12)
    (lo := (108759079 / 500000000)) (hi := (217518159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((310747 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(310747 / 250000) = 1/(250000 / 310747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12071 : Bounds (108759079 / 500000000) (217518159 / 1000000000) (Real.log (310747 / 250000)) := by
  have h := reflection_log_12071_neg
  have he : Real.log (310747 / 250000) = -Real.log (250000 / 310747) := by
    rw [show ((310747 / 250000) : ℝ) = ((250000 / 310747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12072_neg : (278376173 / 1000000000) ≤ -Real.log (189253 / 250000) ∧
    -Real.log (189253 / 250000) ≤ (139188087 / 500000000) := by
  have h := checkLog_sound (w := (60747 / 439253)) (n := 12)
    (lo := (278376173 / 1000000000)) (hi := (139188087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 189253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 189253) = 1/(189253 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12072 : Bounds (-139188087 / 500000000) (-278376173 / 1000000000) (Real.log (189253 / 250000)) := by
  have h := reflection_log_12072_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12073_neg : (12171603 / 200000000) ≤ -Real.log (58809801991 / 62500000000) ∧
    -Real.log (58809801991 / 62500000000) ≤ (1901813 / 31250000) := by
  have h := checkLog_sound (w := (3690198009 / 121309801991)) (n := 12)
    (lo := (12171603 / 200000000)) (hi := (1901813 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 58809801991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 58809801991) = 1/(58809801991 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12073 : Bounds (-1901813 / 31250000) (-12171603 / 200000000) (Real.log (58809801991 / 62500000000)) := by
  have h := reflection_log_12073_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12074_neg : (60336571 / 1000000000) ≤ -Real.log (14710118991 / 15625000000) ∧
    -Real.log (14710118991 / 15625000000) ≤ (15084143 / 250000000) := by
  have h := checkLog_sound (w := (914881009 / 30335118991)) (n := 12)
    (lo := (60336571 / 1000000000)) (hi := (15084143 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14710118991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14710118991) = 1/(14710118991 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12074 : Bounds (-15084143 / 250000000) (-60336571 / 1000000000) (Real.log (14710118991 / 15625000000)) := by
  have h := reflection_log_12074_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12075_neg : (493743891 / 1000000000) ≤ -Real.log (500000000000 / 819219444239) ∧
    -Real.log (500000000000 / 819219444239) ≤ (123435973 / 250000000) := by
  have h := checkLog_sound (w := (319219444239 / 1319219444239)) (n := 12)
    (lo := (493743891 / 1000000000)) (hi := (123435973 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819219444239 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819219444239 / 500000000000) = 1/(500000000000 / 819219444239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12075 : Bounds (493743891 / 1000000000) (123435973 / 250000000) (Real.log (819219444239 / 500000000000)) := by
  have h := reflection_log_12075_neg
  have he : Real.log (819219444239 / 500000000000) = -Real.log (500000000000 / 819219444239) := by
    rw [show ((819219444239 / 500000000000) : ℝ) = ((500000000000 / 819219444239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12076_neg : (123973583 / 250000000) ≤ -Real.log (500000000000 / 820983022727) ∧
    -Real.log (500000000000 / 820983022727) ≤ (495894333 / 1000000000) := by
  have h := checkLog_sound (w := (320983022727 / 1320983022727)) (n := 12)
    (lo := (123973583 / 250000000)) (hi := (495894333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((820983022727 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(820983022727 / 500000000000) = 1/(500000000000 / 820983022727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12076 : Bounds (123973583 / 250000000) (495894333 / 1000000000) (Real.log (820983022727 / 500000000000)) := by
  have h := reflection_log_12076_neg
  have he : Real.log (820983022727 / 500000000000) = -Real.log (500000000000 / 820983022727) := by
    rw [show ((820983022727 / 500000000000) : ℝ) = ((500000000000 / 820983022727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12077_neg : (1007343773 / 1000000000) ≤ -Real.log (62500000000 / 171144859813) ∧
    -Real.log (62500000000 / 171144859813) ≤ (40293751 / 40000000) := by
  have h := checkLog_sound (w := (46144859813 / 296144859813)) (n := 12)
    (lo := (314196593 / 1000000000)) (hi := (157098297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171144859813 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(171144859813 / 125000000000) = 1/(62500000000 / 171144859813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12077 : Bounds (1007343773 / 1000000000) (40293751 / 40000000) (Real.log (171144859813 / 62500000000)) := by
  have h := reflection_log_12077_neg
  have he : Real.log (171144859813 / 62500000000) = -Real.log (62500000000 / 171144859813) := by
    rw [show ((171144859813 / 62500000000) : ℝ) = ((62500000000 / 171144859813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12078_neg : (504948521 / 500000000) ≤ -Real.log (50000000000 / 137265917603) ∧
    -Real.log (50000000000 / 137265917603) ≤ (252474261 / 250000000) := by
  have h := checkLog_sound (w := (37265917603 / 237265917603)) (n := 12)
    (lo := (158374931 / 500000000)) (hi := (316749863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137265917603 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(137265917603 / 100000000000) = 1/(50000000000 / 137265917603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12078 : Bounds (504948521 / 500000000) (252474261 / 250000000) (Real.log (137265917603 / 50000000000)) := by
  have h := reflection_log_12078_neg
  have he : Real.log (137265917603 / 50000000000) = -Real.log (50000000000 / 137265917603) := by
    rw [show ((137265917603 / 50000000000) : ℝ) = ((50000000000 / 137265917603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12079_neg : (383219499 / 1000000000) ≤ -Real.log (1000 / 1467) ∧
    -Real.log (1000 / 1467) ≤ (766439 / 2000000) := by
  have h := checkLog_sound (w := (467 / 2467)) (n := 12)
    (lo := (383219499 / 1000000000)) (hi := (766439 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1467 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1467 / 1000) = 1/(1000 / 1467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12079 : Bounds (383219499 / 1000000000) (766439 / 2000000) (Real.log (1467 / 1000)) := by
  have h := reflection_log_12079_neg
  have he : Real.log (1467 / 1000) = -Real.log (1000 / 1467) := by
    rw [show ((1467 / 1000) : ℝ) = ((1000 / 1467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12080_neg : (314616927 / 500000000) ≤ -Real.log (533 / 1000) ∧
    -Real.log (533 / 1000) ≤ (125846771 / 200000000) := by
  have h := checkLog_sound (w := (467 / 1533)) (n := 12)
    (lo := (314616927 / 500000000)) (hi := (125846771 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 533) = 1/(533 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12080 : Bounds (-125846771 / 200000000) (-314616927 / 500000000) (Real.log (533 / 1000)) := by
  have h := reflection_log_12080_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12081_neg : (46689 / 100000000) ≤ -Real.log (1000000 / 1000467) ∧
    -Real.log (1000000 / 1000467) ≤ (466891 / 1000000000) := by
  have h := checkLog_sound (w := (467 / 2000467)) (n := 12)
    (lo := (46689 / 100000000)) (hi := (466891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000467 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000467 / 1000000) = 1/(1000000 / 1000467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12081 : Bounds (46689 / 100000000) (466891 / 1000000000) (Real.log (1000467 / 1000000)) := by
  have h := reflection_log_12081_neg
  have he : Real.log (1000467 / 1000000) = -Real.log (1000000 / 1000467) := by
    rw [show ((1000467 / 1000000) : ℝ) = ((1000000 / 1000467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12082_neg : (467109 / 1000000000) ≤ -Real.log (999533 / 1000000) ∧
    -Real.log (999533 / 1000000) ≤ (46711 / 100000000) := by
  have h := checkLog_sound (w := (467 / 1999533)) (n := 12)
    (lo := (467109 / 1000000000)) (hi := (46711 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999533) = 1/(999533 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12082 : Bounds (-46711 / 100000000) (-467109 / 1000000000) (Real.log (999533 / 1000000)) := by
  have h := reflection_log_12082_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12083_neg : (217159281 / 1000000000) ≤ -Real.log (500000 / 621271) ∧
    -Real.log (500000 / 621271) ≤ (108579641 / 500000000) := by
  have h := checkLog_sound (w := (121271 / 1121271)) (n := 12)
    (lo := (217159281 / 1000000000)) (hi := (108579641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621271 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(621271 / 500000) = 1/(500000 / 621271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12083 : Bounds (217159281 / 1000000000) (108579641 / 500000000) (Real.log (621271 / 500000)) := by
  have h := reflection_log_12083_neg
  have he : Real.log (621271 / 500000) = -Real.log (500000 / 621271) := by
    rw [show ((621271 / 500000) : ℝ) = ((500000 / 621271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12084_neg : (69446797 / 250000000) ≤ -Real.log (378729 / 500000) ∧
    -Real.log (378729 / 500000) ≤ (277787189 / 1000000000) := by
  have h := checkLog_sound (w := (121271 / 878729)) (n := 12)
    (lo := (69446797 / 250000000)) (hi := (277787189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 378729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 378729) = 1/(378729 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12084 : Bounds (-277787189 / 1000000000) (-69446797 / 250000000) (Real.log (378729 / 500000)) := by
  have h := reflection_log_12084_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12085_neg : (217973409 / 1000000000) ≤ -Real.log (500000 / 621777) ∧
    -Real.log (500000 / 621777) ≤ (21797341 / 100000000) := by
  have h := checkLog_sound (w := (121777 / 1121777)) (n := 12)
    (lo := (217973409 / 1000000000)) (hi := (21797341 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621777 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(621777 / 500000) = 1/(500000 / 621777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12085 : Bounds (217973409 / 1000000000) (21797341 / 100000000) (Real.log (621777 / 500000)) := by
  have h := reflection_log_12085_neg
  have he : Real.log (621777 / 500000) = -Real.log (500000 / 621777) := by
    rw [show ((621777 / 500000) : ℝ) = ((500000 / 621777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12086_neg : (279124129 / 1000000000) ≤ -Real.log (378223 / 500000) ∧
    -Real.log (378223 / 500000) ≤ (27912413 / 100000000) := by
  have h := checkLog_sound (w := (121777 / 878223)) (n := 12)
    (lo := (279124129 / 1000000000)) (hi := (27912413 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 378223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 378223) = 1/(378223 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12086 : Bounds (-27912413 / 100000000) (-279124129 / 1000000000) (Real.log (378223 / 500000)) := by
  have h := reflection_log_12086_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12087_neg : (23887 / 390625) ≤ -Real.log (235170362271 / 250000000000) ∧
    -Real.log (235170362271 / 250000000000) ≤ (61150721 / 1000000000) := by
  have h := checkLog_sound (w := (14829637729 / 485170362271)) (n := 12)
    (lo := (23887 / 390625)) (hi := (61150721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 235170362271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 235170362271) = 1/(235170362271 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12087 : Bounds (-61150721 / 1000000000) (-23887 / 390625) (Real.log (235170362271 / 250000000000)) := by
  have h := reflection_log_12087_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12088_neg : (60627907 / 1000000000) ≤ -Real.log (235293344559 / 250000000000) ∧
    -Real.log (235293344559 / 250000000000) ≤ (15156977 / 250000000) := by
  have h := checkLog_sound (w := (14706655441 / 485293344559)) (n := 12)
    (lo := (60627907 / 1000000000)) (hi := (15156977 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 235293344559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 235293344559) = 1/(235293344559 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12088 : Bounds (-15156977 / 250000000) (-60627907 / 1000000000) (Real.log (235293344559 / 250000000000)) := by
  have h := reflection_log_12088_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12089_neg : (494946469 / 1000000000) ≤ -Real.log (250000000000 / 410102606349) ∧
    -Real.log (250000000000 / 410102606349) ≤ (49494647 / 100000000) := by
  have h := checkLog_sound (w := (160102606349 / 660102606349)) (n := 12)
    (lo := (494946469 / 1000000000)) (hi := (49494647 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((410102606349 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(410102606349 / 250000000000) = 1/(250000000000 / 410102606349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12089 : Bounds (494946469 / 1000000000) (49494647 / 100000000) (Real.log (410102606349 / 250000000000)) := by
  have h := reflection_log_12089_neg
  have he : Real.log (410102606349 / 250000000000) = -Real.log (250000000000 / 410102606349) := by
    rw [show ((410102606349 / 250000000000) : ℝ) = ((250000000000 / 410102606349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12090_neg : (248548769 / 500000000) ≤ -Real.log (250000000000 / 410985714777) ∧
    -Real.log (250000000000 / 410985714777) ≤ (497097539 / 1000000000) := by
  have h := checkLog_sound (w := (160985714777 / 660985714777)) (n := 12)
    (lo := (248548769 / 500000000)) (hi := (497097539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((410985714777 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(410985714777 / 250000000000) = 1/(250000000000 / 410985714777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12090 : Bounds (248548769 / 500000000) (497097539 / 1000000000) (Real.log (410985714777 / 250000000000)) := by
  have h := reflection_log_12090_neg
  have he : Real.log (410985714777 / 250000000000) = -Real.log (250000000000 / 410985714777) := by
    rw [show ((410985714777 / 250000000000) : ℝ) = ((250000000000 / 410985714777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12091_neg : (504948521 / 500000000) ≤ -Real.log (500000000000 / 1372659176029) ∧
    -Real.log (500000000000 / 1372659176029) ≤ (252474261 / 250000000) := by
  have h := checkLog_sound (w := (372659176029 / 2372659176029)) (n := 12)
    (lo := (158374931 / 500000000)) (hi := (316749863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1372659176029 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1372659176029 / 1000000000000) = 1/(500000000000 / 1372659176029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12091 : Bounds (504948521 / 500000000) (252474261 / 250000000) (Real.log (1372659176029 / 500000000000)) := by
  have h := reflection_log_12091_neg
  have he : Real.log (1372659176029 / 500000000000) = -Real.log (500000000000 / 1372659176029) := by
    rw [show ((1372659176029 / 500000000000) : ℝ) = ((500000000000 / 1372659176029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12092_neg : (1012453353 / 1000000000) ≤ -Real.log (12500000000 / 34404315197) ∧
    -Real.log (12500000000 / 34404315197) ≤ (202490671 / 200000000) := by
  have h := checkLog_sound (w := (9404315197 / 59404315197)) (n := 12)
    (lo := (319306173 / 1000000000)) (hi := (159653087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34404315197 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(34404315197 / 25000000000) = 1/(12500000000 / 34404315197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12092 : Bounds (1012453353 / 1000000000) (202490671 / 200000000) (Real.log (34404315197 / 12500000000)) := by
  have h := reflection_log_12092_neg
  have he : Real.log (34404315197 / 12500000000) = -Real.log (12500000000 / 34404315197) := by
    rw [show ((34404315197 / 12500000000) : ℝ) = ((12500000000 / 34404315197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12093_neg : (38390093 / 100000000) ≤ -Real.log (250 / 367) ∧
    -Real.log (250 / 367) ≤ (383900931 / 1000000000) := by
  have h := checkLog_sound (w := (117 / 617)) (n := 12)
    (lo := (38390093 / 100000000)) (hi := (383900931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((367 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(367 / 250) = 1/(250 / 367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12093 : Bounds (38390093 / 100000000) (383900931 / 1000000000) (Real.log (367 / 250)) := by
  have h := reflection_log_12093_neg
  have he : Real.log (367 / 250) = -Real.log (250 / 367) := by
    rw [show ((367 / 250) : ℝ) = ((250 / 367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12094_neg : (631111789 / 1000000000) ≤ -Real.log (133 / 250) ∧
    -Real.log (133 / 250) ≤ (63111179 / 100000000) := by
  have h := checkLog_sound (w := (117 / 383)) (n := 12)
    (lo := (631111789 / 1000000000)) (hi := (63111179 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 133) = 1/(133 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12094 : Bounds (-63111179 / 100000000) (-631111789 / 1000000000) (Real.log (133 / 250)) := by
  have h := reflection_log_12094_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12095_neg : (46789 / 100000000) ≤ -Real.log (250000 / 250117) ∧
    -Real.log (250000 / 250117) ≤ (467891 / 1000000000) := by
  have h := checkLog_sound (w := (117 / 500117)) (n := 12)
    (lo := (46789 / 100000000)) (hi := (467891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250117 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250117 / 250000) = 1/(250000 / 250117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12095 : Bounds (46789 / 100000000) (467891 / 1000000000) (Real.log (250117 / 250000)) := by
  have h := reflection_log_12095_neg
  have he : Real.log (250117 / 250000) = -Real.log (250000 / 250117) := by
    rw [show ((250117 / 250000) : ℝ) = ((250000 / 250117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0189 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12096_neg : (468109 / 1000000000) ≤ -Real.log (249883 / 250000) ∧
    -Real.log (249883 / 250000) ≤ (46811 / 100000000) := by
  have h := checkLog_sound (w := (117 / 499883)) (n := 12)
    (lo := (468109 / 1000000000)) (hi := (46811 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249883) = 1/(249883 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12096 : Bounds (-46811 / 100000000) (-468109 / 1000000000) (Real.log (249883 / 250000)) := by
  have h := reflection_log_12096_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12097_neg : (21761389 / 100000000) ≤ -Real.log (1000000 / 1243107) ∧
    -Real.log (1000000 / 1243107) ≤ (217613891 / 1000000000) := by
  have h := checkLog_sound (w := (243107 / 2243107)) (n := 12)
    (lo := (21761389 / 100000000)) (hi := (217613891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1243107 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1243107 / 1000000) = 1/(1000000 / 1243107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12097 : Bounds (21761389 / 100000000) (217613891 / 1000000000) (Real.log (1243107 / 1000000)) := by
  have h := reflection_log_12097_neg
  have he : Real.log (1243107 / 1000000) = -Real.log (1000000 / 1243107) := by
    rw [show ((1243107 / 1000000) : ℝ) = ((1000000 / 1243107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12098_neg : (139266691 / 500000000) ≤ -Real.log (756893 / 1000000) ∧
    -Real.log (756893 / 1000000) ≤ (278533383 / 1000000000) := by
  have h := checkLog_sound (w := (243107 / 1756893)) (n := 12)
    (lo := (139266691 / 500000000)) (hi := (278533383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 756893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 756893) = 1/(756893 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12098 : Bounds (-278533383 / 1000000000) (-139266691 / 500000000) (Real.log (756893 / 1000000)) := by
  have h := reflection_log_12098_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12099_neg : (27303657 / 125000000) ≤ -Real.log (1000000 / 1244121) ∧
    -Real.log (1000000 / 1244121) ≤ (218429257 / 1000000000) := by
  have h := checkLog_sound (w := (244121 / 2244121)) (n := 12)
    (lo := (27303657 / 125000000)) (hi := (218429257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1244121 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1244121 / 1000000) = 1/(1000000 / 1244121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12099 : Bounds (27303657 / 125000000) (218429257 / 1000000000) (Real.log (1244121 / 1000000)) := by
  have h := reflection_log_12099_neg
  have he : Real.log (1244121 / 1000000) = -Real.log (1000000 / 1244121) := by
    rw [show ((1244121 / 1000000) : ℝ) = ((1000000 / 1244121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12100_neg : (17492123 / 62500000) ≤ -Real.log (755879 / 1000000) ∧
    -Real.log (755879 / 1000000) ≤ (279873969 / 1000000000) := by
  have h := checkLog_sound (w := (244121 / 1755879)) (n := 12)
    (lo := (17492123 / 62500000)) (hi := (279873969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 755879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 755879) = 1/(755879 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12100 : Bounds (-279873969 / 1000000000) (-17492123 / 62500000) (Real.log (755879 / 1000000)) := by
  have h := reflection_log_12100_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12101_neg : (7680589 / 125000000) ≤ -Real.log (940404937359 / 1000000000000) ∧
    -Real.log (940404937359 / 1000000000000) ≤ (61444713 / 1000000000) := by
  have h := checkLog_sound (w := (59595062641 / 1940404937359)) (n := 12)
    (lo := (7680589 / 125000000)) (hi := (61444713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 940404937359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 940404937359) = 1/(940404937359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12101 : Bounds (-61444713 / 1000000000) (-7680589 / 125000000) (Real.log (940404937359 / 1000000000000)) := by
  have h := reflection_log_12101_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12102_neg : (15229873 / 250000000) ≤ -Real.log (940898986551 / 1000000000000) ∧
    -Real.log (940898986551 / 1000000000000) ≤ (60919493 / 1000000000) := by
  have h := checkLog_sound (w := (59101013449 / 1940898986551)) (n := 12)
    (lo := (15229873 / 250000000)) (hi := (60919493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 940898986551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 940898986551) = 1/(940898986551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12102 : Bounds (-60919493 / 1000000000) (-15229873 / 250000000) (Real.log (940898986551 / 1000000000000)) := by
  have h := reflection_log_12102_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12103_neg : (496147273 / 1000000000) ≤ -Real.log (100000000000 / 164238141983) ∧
    -Real.log (100000000000 / 164238141983) ≤ (248073637 / 500000000) := by
  have h := checkLog_sound (w := (64238141983 / 264238141983)) (n := 12)
    (lo := (496147273 / 1000000000)) (hi := (248073637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164238141983 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164238141983 / 100000000000) = 1/(100000000000 / 164238141983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12103 : Bounds (496147273 / 1000000000) (248073637 / 500000000) (Real.log (164238141983 / 100000000000)) := by
  have h := reflection_log_12103_neg
  have he : Real.log (164238141983 / 100000000000) = -Real.log (100000000000 / 164238141983) := by
    rw [show ((164238141983 / 100000000000) : ℝ) = ((100000000000 / 164238141983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12104_neg : (62287903 / 125000000) ≤ -Real.log (500000000000 / 822963066841) ∧
    -Real.log (500000000000 / 822963066841) ≤ (19932129 / 40000000) := by
  have h := checkLog_sound (w := (322963066841 / 1322963066841)) (n := 12)
    (lo := (62287903 / 125000000)) (hi := (19932129 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((822963066841 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(822963066841 / 500000000000) = 1/(500000000000 / 822963066841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12104 : Bounds (62287903 / 125000000) (19932129 / 40000000) (Real.log (822963066841 / 500000000000)) := by
  have h := reflection_log_12104_neg
  have he : Real.log (822963066841 / 500000000000) = -Real.log (500000000000 / 822963066841) := by
    rw [show ((822963066841 / 500000000000) : ℝ) = ((500000000000 / 822963066841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12105_neg : (1012453353 / 1000000000) ≤ -Real.log (500000000000 / 1376172607879) ∧
    -Real.log (500000000000 / 1376172607879) ≤ (202490671 / 200000000) := by
  have h := checkLog_sound (w := (376172607879 / 2376172607879)) (n := 12)
    (lo := (319306173 / 1000000000)) (hi := (159653087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1376172607879 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1376172607879 / 1000000000000) = 1/(500000000000 / 1376172607879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12105 : Bounds (1012453353 / 1000000000) (202490671 / 200000000) (Real.log (1376172607879 / 500000000000)) := by
  have h := reflection_log_12105_neg
  have he : Real.log (1376172607879 / 500000000000) = -Real.log (500000000000 / 1376172607879) := by
    rw [show ((1376172607879 / 500000000000) : ℝ) = ((500000000000 / 1376172607879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12106_neg : (1015012719 / 1000000000) ≤ -Real.log (500000000000 / 1379699248121) ∧
    -Real.log (500000000000 / 1379699248121) ≤ (1015012721 / 1000000000) := by
  have h := checkLog_sound (w := (379699248121 / 2379699248121)) (n := 12)
    (lo := (321865539 / 1000000000)) (hi := (16093277 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1379699248121 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1379699248121 / 1000000000000) = 1/(500000000000 / 1379699248121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12106 : Bounds (1015012719 / 1000000000) (1015012721 / 1000000000) (Real.log (1379699248121 / 500000000000)) := by
  have h := reflection_log_12106_neg
  have he : Real.log (1379699248121 / 500000000000) = -Real.log (500000000000 / 1379699248121) := by
    rw [show ((1379699248121 / 500000000000) : ℝ) = ((500000000000 / 1379699248121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12107_neg : (384581897 / 1000000000) ≤ -Real.log (1000 / 1469) ∧
    -Real.log (1000 / 1469) ≤ (192290949 / 500000000) := by
  have h := checkLog_sound (w := (469 / 2469)) (n := 12)
    (lo := (384581897 / 1000000000)) (hi := (192290949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1469 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1469 / 1000) = 1/(1000 / 1469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12107 : Bounds (384581897 / 1000000000) (192290949 / 500000000) (Real.log (1469 / 1000)) := by
  have h := reflection_log_12107_neg
  have he : Real.log (1469 / 1000) = -Real.log (1000 / 1469) := by
    rw [show ((1469 / 1000) : ℝ) = ((1000 / 1469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12108_neg : (632993257 / 1000000000) ≤ -Real.log (531 / 1000) ∧
    -Real.log (531 / 1000) ≤ (316496629 / 500000000) := by
  have h := checkLog_sound (w := (469 / 1531)) (n := 12)
    (lo := (632993257 / 1000000000)) (hi := (316496629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 531) = 1/(531 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12108 : Bounds (-316496629 / 500000000) (-632993257 / 1000000000) (Real.log (531 / 1000)) := by
  have h := reflection_log_12108_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12109_neg : (46889 / 100000000) ≤ -Real.log (1000000 / 1000469) ∧
    -Real.log (1000000 / 1000469) ≤ (468891 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 2000469)) (n := 12)
    (lo := (46889 / 100000000)) (hi := (468891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000469 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000469 / 1000000) = 1/(1000000 / 1000469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12109 : Bounds (46889 / 100000000) (468891 / 1000000000) (Real.log (1000469 / 1000000)) := by
  have h := reflection_log_12109_neg
  have he : Real.log (1000469 / 1000000) = -Real.log (1000000 / 1000469) := by
    rw [show ((1000469 / 1000000) : ℝ) = ((1000000 / 1000469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12110_neg : (46911 / 100000000) ≤ -Real.log (999531 / 1000000) ∧
    -Real.log (999531 / 1000000) ≤ (469111 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 1999531)) (n := 12)
    (lo := (46911 / 100000000)) (hi := (469111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999531) = 1/(999531 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12110 : Bounds (-469111 / 1000000000) (-46911 / 100000000) (Real.log (999531 / 1000000)) := by
  have h := reflection_log_12110_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12111_neg : (109034549 / 500000000) ≤ -Real.log (1000000 / 1243673) ∧
    -Real.log (1000000 / 1243673) ≤ (218069099 / 1000000000) := by
  have h := checkLog_sound (w := (243673 / 2243673)) (n := 12)
    (lo := (109034549 / 500000000)) (hi := (218069099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1243673 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1243673 / 1000000) = 1/(1000000 / 1243673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12111 : Bounds (109034549 / 500000000) (218069099 / 1000000000) (Real.log (1243673 / 1000000)) := by
  have h := reflection_log_12111_neg
  have he : Real.log (1243673 / 1000000) = -Real.log (1000000 / 1243673) := by
    rw [show ((1243673 / 1000000) : ℝ) = ((1000000 / 1243673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12112_neg : (17455091 / 62500000) ≤ -Real.log (756327 / 1000000) ∧
    -Real.log (756327 / 1000000) ≤ (279281457 / 1000000000) := by
  have h := checkLog_sound (w := (243673 / 1756327)) (n := 12)
    (lo := (17455091 / 62500000)) (hi := (279281457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 756327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 756327) = 1/(756327 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12112 : Bounds (-279281457 / 1000000000) (-17455091 / 62500000) (Real.log (756327 / 1000000)) := by
  have h := reflection_log_12112_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12113_neg : (6840153 / 31250000) ≤ -Real.log (62500 / 77793) ∧
    -Real.log (62500 / 77793) ≤ (218884897 / 1000000000) := by
  have h := checkLog_sound (w := (15293 / 140293)) (n := 12)
    (lo := (6840153 / 31250000)) (hi := (218884897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77793 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77793 / 62500) = 1/(62500 / 77793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12113 : Bounds (6840153 / 31250000) (218884897 / 1000000000) (Real.log (77793 / 62500)) := by
  have h := reflection_log_12113_neg
  have he : Real.log (77793 / 62500) = -Real.log (62500 / 77793) := by
    rw [show ((77793 / 62500) : ℝ) = ((62500 / 77793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12114_neg : (28062437 / 100000000) ≤ -Real.log (47207 / 62500) ∧
    -Real.log (47207 / 62500) ≤ (280624371 / 1000000000) := by
  have h := checkLog_sound (w := (15293 / 109707)) (n := 12)
    (lo := (28062437 / 100000000)) (hi := (280624371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 47207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 47207) = 1/(47207 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12114 : Bounds (-280624371 / 1000000000) (-28062437 / 100000000) (Real.log (47207 / 62500)) := by
  have h := reflection_log_12114_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12115_neg : (61739473 / 1000000000) ≤ -Real.log (3672374151 / 3906250000) ∧
    -Real.log (3672374151 / 3906250000) ≤ (30869737 / 500000000) := by
  have h := checkLog_sound (w := (233875849 / 7578624151)) (n := 12)
    (lo := (61739473 / 1000000000)) (hi := (30869737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3672374151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3672374151) = 1/(3672374151 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12115 : Bounds (-30869737 / 500000000) (-61739473 / 1000000000) (Real.log (3672374151 / 3906250000)) := by
  have h := reflection_log_12115_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12116_neg : (30606179 / 500000000) ≤ -Real.log (940623469071 / 1000000000000) ∧
    -Real.log (940623469071 / 1000000000000) ≤ (61212359 / 1000000000) := by
  have h := checkLog_sound (w := (59376530929 / 1940623469071)) (n := 12)
    (lo := (30606179 / 500000000)) (hi := (61212359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 940623469071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 940623469071) = 1/(940623469071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12116 : Bounds (-61212359 / 1000000000) (-30606179 / 500000000) (Real.log (940623469071 / 1000000000000)) := by
  have h := reflection_log_12116_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12117_neg : (248675277 / 500000000) ≤ -Real.log (500000000000 / 822179427681) ∧
    -Real.log (500000000000 / 822179427681) ≤ (99470111 / 200000000) := by
  have h := checkLog_sound (w := (322179427681 / 1322179427681)) (n := 12)
    (lo := (248675277 / 500000000)) (hi := (99470111 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((822179427681 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(822179427681 / 500000000000) = 1/(500000000000 / 822179427681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12117 : Bounds (248675277 / 500000000) (99470111 / 200000000) (Real.log (822179427681 / 500000000000)) := by
  have h := reflection_log_12117_neg
  have he : Real.log (822179427681 / 500000000000) = -Real.log (500000000000 / 822179427681) := by
    rw [show ((822179427681 / 500000000000) : ℝ) = ((500000000000 / 822179427681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12118_neg : (249754633 / 500000000) ≤ -Real.log (250000000000 / 411978096469) ∧
    -Real.log (250000000000 / 411978096469) ≤ (499509267 / 1000000000) := by
  have h := checkLog_sound (w := (161978096469 / 661978096469)) (n := 12)
    (lo := (249754633 / 500000000)) (hi := (499509267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((411978096469 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(411978096469 / 250000000000) = 1/(250000000000 / 411978096469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12118 : Bounds (249754633 / 500000000) (499509267 / 1000000000) (Real.log (411978096469 / 250000000000)) := by
  have h := reflection_log_12118_neg
  have he : Real.log (411978096469 / 250000000000) = -Real.log (250000000000 / 411978096469) := by
    rw [show ((411978096469 / 250000000000) : ℝ) = ((250000000000 / 411978096469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12119_neg : (1015012719 / 1000000000) ≤ -Real.log (12500000000 / 34492481203) ∧
    -Real.log (12500000000 / 34492481203) ≤ (1015012721 / 1000000000) := by
  have h := checkLog_sound (w := (9492481203 / 59492481203)) (n := 12)
    (lo := (321865539 / 1000000000)) (hi := (16093277 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34492481203 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(34492481203 / 25000000000) = 1/(12500000000 / 34492481203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12119 : Bounds (1015012719 / 1000000000) (1015012721 / 1000000000) (Real.log (34492481203 / 12500000000)) := by
  have h := reflection_log_12119_neg
  have he : Real.log (34492481203 / 12500000000) = -Real.log (12500000000 / 34492481203) := by
    rw [show ((34492481203 / 12500000000) : ℝ) = ((12500000000 / 34492481203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12120_neg : (508787577 / 500000000) ≤ -Real.log (4000000000 / 11065913371) ∧
    -Real.log (4000000000 / 11065913371) ≤ (254393789 / 250000000) := by
  have h := checkLog_sound (w := (3065913371 / 19065913371)) (n := 12)
    (lo := (162213987 / 500000000)) (hi := (12977119 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11065913371 / 8000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(11065913371 / 8000000000) = 1/(4000000000 / 11065913371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12120 : Bounds (508787577 / 500000000) (254393789 / 250000000) (Real.log (11065913371 / 4000000000)) := by
  have h := reflection_log_12120_neg
  have he : Real.log (11065913371 / 4000000000) = -Real.log (4000000000 / 11065913371) := by
    rw [show ((11065913371 / 4000000000) : ℝ) = ((4000000000 / 11065913371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12121_neg : (240789 / 625000) ≤ -Real.log (100 / 147) ∧
    -Real.log (100 / 147) ≤ (385262401 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 247)) (n := 12)
    (lo := (240789 / 625000)) (hi := (385262401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147 / 100) = 1/(100 / 147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12121 : Bounds (240789 / 625000) (385262401 / 1000000000) (Real.log (147 / 100)) := by
  have h := reflection_log_12121_neg
  have he : Real.log (147 / 100) = -Real.log (100 / 147) := by
    rw [show ((147 / 100) : ℝ) = ((100 / 147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12122_neg : (9919973 / 15625000) ≤ -Real.log (53 / 100) ∧
    -Real.log (53 / 100) ≤ (634878273 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 153)) (n := 12)
    (lo := (9919973 / 15625000)) (hi := (634878273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 53) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 53) = 1/(53 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12122 : Bounds (-634878273 / 1000000000) (-9919973 / 15625000) (Real.log (53 / 100)) := by
  have h := reflection_log_12122_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12123_neg : (469889 / 1000000000) ≤ -Real.log (100000 / 100047) ∧
    -Real.log (100000 / 100047) ≤ (46989 / 100000000) := by
  have h := checkLog_sound (w := (47 / 200047)) (n := 12)
    (lo := (469889 / 1000000000)) (hi := (46989 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100047 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100047 / 100000) = 1/(100000 / 100047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12123 : Bounds (469889 / 1000000000) (46989 / 100000000) (Real.log (100047 / 100000)) := by
  have h := reflection_log_12123_neg
  have he : Real.log (100047 / 100000) = -Real.log (100000 / 100047) := by
    rw [show ((100047 / 100000) : ℝ) = ((100000 / 100047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12124_neg : (47011 / 100000000) ≤ -Real.log (99953 / 100000) ∧
    -Real.log (99953 / 100000) ≤ (470111 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 199953)) (n := 12)
    (lo := (47011 / 100000000)) (hi := (470111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99953) = 1/(99953 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12124 : Bounds (-470111 / 1000000000) (-47011 / 100000000) (Real.log (99953 / 100000)) := by
  have h := reflection_log_12124_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12125_neg : (218524901 / 1000000000) ≤ -Real.log (12500 / 15553) ∧
    -Real.log (12500 / 15553) ≤ (109262451 / 500000000) := by
  have h := checkLog_sound (w := (3053 / 28053)) (n := 12)
    (lo := (218524901 / 1000000000)) (hi := (109262451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15553 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15553 / 12500) = 1/(12500 / 15553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12125 : Bounds (218524901 / 1000000000) (109262451 / 500000000) (Real.log (15553 / 12500)) := by
  have h := reflection_log_12125_neg
  have he : Real.log (15553 / 12500) = -Real.log (12500 / 15553) := by
    rw [show ((15553 / 12500) : ℝ) = ((12500 / 15553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12126_neg : (280031413 / 1000000000) ≤ -Real.log (9447 / 12500) ∧
    -Real.log (9447 / 12500) ≤ (140015707 / 500000000) := by
  have h := checkLog_sound (w := (3053 / 21947)) (n := 12)
    (lo := (280031413 / 1000000000)) (hi := (140015707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 9447) = 1/(9447 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12126 : Bounds (-140015707 / 500000000) (-280031413 / 1000000000) (Real.log (9447 / 12500)) := by
  have h := reflection_log_12126_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12127_neg : (219341131 / 1000000000) ≤ -Real.log (125000 / 155657) ∧
    -Real.log (125000 / 155657) ≤ (54835283 / 250000000) := by
  have h := checkLog_sound (w := (30657 / 280657)) (n := 12)
    (lo := (219341131 / 1000000000)) (hi := (54835283 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155657 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155657 / 125000) = 1/(125000 / 155657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12127 : Bounds (219341131 / 1000000000) (54835283 / 250000000) (Real.log (155657 / 125000)) := by
  have h := reflection_log_12127_neg
  have he : Real.log (155657 / 125000) = -Real.log (125000 / 155657) := by
    rw [show ((155657 / 125000) : ℝ) = ((125000 / 155657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12128_neg : (14068833 / 50000000) ≤ -Real.log (94343 / 125000) ∧
    -Real.log (94343 / 125000) ≤ (281376661 / 1000000000) := by
  have h := checkLog_sound (w := (30657 / 219343)) (n := 12)
    (lo := (14068833 / 50000000)) (hi := (281376661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 94343) = 1/(94343 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12128 : Bounds (-281376661 / 1000000000) (-14068833 / 50000000) (Real.log (94343 / 125000)) := by
  have h := reflection_log_12128_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12129_neg : (7754441 / 125000000) ≤ -Real.log (14685148351 / 15625000000) ∧
    -Real.log (14685148351 / 15625000000) ≤ (62035529 / 1000000000) := by
  have h := checkLog_sound (w := (939851649 / 30310148351)) (n := 12)
    (lo := (7754441 / 125000000)) (hi := (62035529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14685148351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14685148351) = 1/(14685148351 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12129 : Bounds (-62035529 / 1000000000) (-7754441 / 125000000) (Real.log (14685148351 / 15625000000)) := by
  have h := reflection_log_12129_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12130_neg : (61506511 / 1000000000) ≤ -Real.log (146929191 / 156250000) ∧
    -Real.log (146929191 / 156250000) ≤ (3844157 / 62500000) := by
  have h := checkLog_sound (w := (9320809 / 303179191)) (n := 12)
    (lo := (61506511 / 1000000000)) (hi := (3844157 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 146929191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 146929191) = 1/(146929191 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12130 : Bounds (-3844157 / 62500000) (-61506511 / 1000000000) (Real.log (146929191 / 156250000)) := by
  have h := reflection_log_12130_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12131_neg : (99711263 / 200000000) ≤ -Real.log (125000000000 / 205792844289) ∧
    -Real.log (125000000000 / 205792844289) ≤ (124639079 / 250000000) := by
  have h := checkLog_sound (w := (80792844289 / 330792844289)) (n := 12)
    (lo := (99711263 / 200000000)) (hi := (124639079 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((205792844289 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(205792844289 / 125000000000) = 1/(125000000000 / 205792844289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12131 : Bounds (99711263 / 200000000) (124639079 / 250000000) (Real.log (205792844289 / 125000000000)) := by
  have h := reflection_log_12131_neg
  have he : Real.log (205792844289 / 125000000000) = -Real.log (125000000000 / 205792844289) := by
    rw [show ((205792844289 / 125000000000) : ℝ) = ((125000000000 / 205792844289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12132_neg : (500717791 / 1000000000) ≤ -Real.log (500000000000 / 824952566699) ∧
    -Real.log (500000000000 / 824952566699) ≤ (15647431 / 31250000) := by
  have h := checkLog_sound (w := (324952566699 / 1324952566699)) (n := 12)
    (lo := (500717791 / 1000000000)) (hi := (15647431 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((824952566699 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(824952566699 / 500000000000) = 1/(500000000000 / 824952566699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12132 : Bounds (500717791 / 1000000000) (15647431 / 31250000) (Real.log (824952566699 / 500000000000)) := by
  have h := reflection_log_12132_neg
  have he : Real.log (824952566699 / 500000000000) = -Real.log (500000000000 / 824952566699) := by
    rw [show ((824952566699 / 500000000000) : ℝ) = ((500000000000 / 824952566699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12133_neg : (508787577 / 500000000) ≤ -Real.log (250000000000 / 691619585687) ∧
    -Real.log (250000000000 / 691619585687) ≤ (254393789 / 250000000) := by
  have h := checkLog_sound (w := (191619585687 / 1191619585687)) (n := 12)
    (lo := (162213987 / 500000000)) (hi := (12977119 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691619585687 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(691619585687 / 500000000000) = 1/(250000000000 / 691619585687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12133 : Bounds (508787577 / 500000000) (254393789 / 250000000) (Real.log (691619585687 / 250000000000)) := by
  have h := reflection_log_12133_neg
  have he : Real.log (691619585687 / 250000000000) = -Real.log (250000000000 / 691619585687) := by
    rw [show ((691619585687 / 250000000000) : ℝ) = ((250000000000 / 691619585687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12134_neg : (7969849 / 7812500) ≤ -Real.log (500000000000 / 1386792452831) ∧
    -Real.log (500000000000 / 1386792452831) ≤ (510070337 / 500000000) := by
  have h := checkLog_sound (w := (386792452831 / 2386792452831)) (n := 12)
    (lo := (81748373 / 250000000)) (hi := (326993493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1386792452831 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1386792452831 / 1000000000000) = 1/(500000000000 / 1386792452831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12134 : Bounds (7969849 / 7812500) (510070337 / 500000000) (Real.log (1386792452831 / 500000000000)) := by
  have h := reflection_log_12134_neg
  have he : Real.log (1386792452831 / 500000000000) = -Real.log (500000000000 / 1386792452831) := by
    rw [show ((1386792452831 / 500000000000) : ℝ) = ((500000000000 / 1386792452831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12135_neg : (385942441 / 1000000000) ≤ -Real.log (1000 / 1471) ∧
    -Real.log (1000 / 1471) ≤ (192971221 / 500000000) := by
  have h := checkLog_sound (w := (471 / 2471)) (n := 12)
    (lo := (385942441 / 1000000000)) (hi := (192971221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1471 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1471 / 1000) = 1/(1000 / 1471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12135 : Bounds (385942441 / 1000000000) (192971221 / 500000000) (Real.log (1471 / 1000)) := by
  have h := reflection_log_12135_neg
  have he : Real.log (1471 / 1000) = -Real.log (1000 / 1471) := by
    rw [show ((1471 / 1000) : ℝ) = ((1000 / 1471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12136_neg : (636766847 / 1000000000) ≤ -Real.log (529 / 1000) ∧
    -Real.log (529 / 1000) ≤ (4974741 / 7812500) := by
  have h := checkLog_sound (w := (471 / 1529)) (n := 12)
    (lo := (636766847 / 1000000000)) (hi := (4974741 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 529) = 1/(529 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12136 : Bounds (-4974741 / 7812500) (-636766847 / 1000000000) (Real.log (529 / 1000)) := by
  have h := reflection_log_12136_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12137_neg : (470889 / 1000000000) ≤ -Real.log (1000000 / 1000471) ∧
    -Real.log (1000000 / 1000471) ≤ (47089 / 100000000) := by
  have h := checkLog_sound (w := (471 / 2000471)) (n := 12)
    (lo := (470889 / 1000000000)) (hi := (47089 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000471 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000471 / 1000000) = 1/(1000000 / 1000471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12137 : Bounds (470889 / 1000000000) (47089 / 100000000) (Real.log (1000471 / 1000000)) := by
  have h := reflection_log_12137_neg
  have he : Real.log (1000471 / 1000000) = -Real.log (1000000 / 1000471) := by
    rw [show ((1000471 / 1000000) : ℝ) = ((1000000 / 1000471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12138_neg : (47111 / 100000000) ≤ -Real.log (999529 / 1000000) ∧
    -Real.log (999529 / 1000000) ≤ (471111 / 1000000000) := by
  have h := checkLog_sound (w := (471 / 1999529)) (n := 12)
    (lo := (47111 / 100000000)) (hi := (471111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999529) = 1/(999529 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12138 : Bounds (-471111 / 1000000000) (-47111 / 100000000) (Real.log (999529 / 1000000)) := by
  have h := reflection_log_12138_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12139_neg : (109489847 / 500000000) ≤ -Real.log (500000 / 622403) ∧
    -Real.log (500000 / 622403) ≤ (43795939 / 200000000) := by
  have h := checkLog_sound (w := (122403 / 1122403)) (n := 12)
    (lo := (109489847 / 500000000)) (hi := (43795939 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((622403 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(622403 / 500000) = 1/(500000 / 622403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12139 : Bounds (109489847 / 500000000) (43795939 / 200000000) (Real.log (622403 / 500000)) := by
  have h := reflection_log_12139_neg
  have he : Real.log (622403 / 500000) = -Real.log (500000 / 622403) := by
    rw [show ((622403 / 500000) : ℝ) = ((500000 / 622403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12140_neg : (280780609 / 1000000000) ≤ -Real.log (377597 / 500000) ∧
    -Real.log (377597 / 500000) ≤ (28078061 / 100000000) := by
  have h := checkLog_sound (w := (122403 / 877597)) (n := 12)
    (lo := (280780609 / 1000000000)) (hi := (28078061 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 377597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 377597) = 1/(377597 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12140 : Bounds (-28078061 / 100000000) (-280780609 / 1000000000) (Real.log (377597 / 500000)) := by
  have h := reflection_log_12140_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12141_neg : (109898579 / 500000000) ≤ -Real.log (15625 / 19466) ∧
    -Real.log (15625 / 19466) ≤ (219797159 / 1000000000) := by
  have h := checkLog_sound (w := (3841 / 35091)) (n := 12)
    (lo := (109898579 / 500000000)) (hi := (219797159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19466 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19466 / 15625) = 1/(15625 / 19466) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12141 : Bounds (109898579 / 500000000) (219797159 / 1000000000) (Real.log (19466 / 15625)) := by
  have h := reflection_log_12141_neg
  have he : Real.log (19466 / 15625) = -Real.log (15625 / 19466) := by
    rw [show ((19466 / 15625) : ℝ) = ((15625 / 19466) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12142_neg : (70532379 / 250000000) ≤ -Real.log (11784 / 15625) ∧
    -Real.log (11784 / 15625) ≤ (282129517 / 1000000000) := by
  have h := checkLog_sound (w := (3841 / 27409)) (n := 12)
    (lo := (70532379 / 250000000)) (hi := (282129517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11784) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11784) = 1/(11784 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12142 : Bounds (-282129517 / 1000000000) (-70532379 / 250000000) (Real.log (11784 / 15625)) := by
  have h := reflection_log_12142_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12143_neg : (31166179 / 500000000) ≤ -Real.log (229387344 / 244140625) ∧
    -Real.log (229387344 / 244140625) ≤ (62332359 / 1000000000) := by
  have h := checkLog_sound (w := (14753281 / 473527969)) (n := 12)
    (lo := (31166179 / 500000000)) (hi := (62332359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 229387344) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 229387344) = 1/(229387344 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12143 : Bounds (-62332359 / 1000000000) (-31166179 / 500000000) (Real.log (229387344 / 244140625)) := by
  have h := reflection_log_12143_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12144_neg : (30900457 / 500000000) ≤ -Real.log (235017505591 / 250000000000) ∧
    -Real.log (235017505591 / 250000000000) ≤ (12360183 / 200000000) := by
  have h := checkLog_sound (w := (14982494409 / 485017505591)) (n := 12)
    (lo := (30900457 / 500000000)) (hi := (12360183 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 235017505591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 235017505591) = 1/(235017505591 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12144 : Bounds (-12360183 / 200000000) (-30900457 / 500000000) (Real.log (235017505591 / 250000000000)) := by
  have h := reflection_log_12144_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12145_neg : (499760303 / 1000000000) ≤ -Real.log (31250000000 / 51510191421) ∧
    -Real.log (31250000000 / 51510191421) ≤ (31235019 / 62500000) := by
  have h := checkLog_sound (w := (20260191421 / 82760191421)) (n := 12)
    (lo := (499760303 / 1000000000)) (hi := (31235019 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51510191421 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51510191421 / 31250000000) = 1/(31250000000 / 51510191421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12145 : Bounds (499760303 / 1000000000) (31235019 / 62500000) (Real.log (51510191421 / 31250000000)) := by
  have h := reflection_log_12145_neg
  have he : Real.log (51510191421 / 31250000000) = -Real.log (31250000000 / 51510191421) := by
    rw [show ((51510191421 / 31250000000) : ℝ) = ((31250000000 / 51510191421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12146_neg : (250963337 / 500000000) ≤ -Real.log (500000000000 / 825950441277) ∧
    -Real.log (500000000000 / 825950441277) ≤ (20077067 / 40000000) := by
  have h := checkLog_sound (w := (325950441277 / 1325950441277)) (n := 12)
    (lo := (250963337 / 500000000)) (hi := (20077067 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((825950441277 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(825950441277 / 500000000000) = 1/(500000000000 / 825950441277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12146 : Bounds (250963337 / 500000000) (20077067 / 40000000) (Real.log (825950441277 / 500000000000)) := by
  have h := reflection_log_12146_neg
  have he : Real.log (825950441277 / 500000000000) = -Real.log (500000000000 / 825950441277) := by
    rw [show ((825950441277 / 500000000000) : ℝ) = ((500000000000 / 825950441277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12147_neg : (7969849 / 7812500) ≤ -Real.log (50000000000 / 138679245283) ∧
    -Real.log (50000000000 / 138679245283) ≤ (510070337 / 500000000) := by
  have h := checkLog_sound (w := (38679245283 / 238679245283)) (n := 12)
    (lo := (81748373 / 250000000)) (hi := (326993493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138679245283 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(138679245283 / 100000000000) = 1/(50000000000 / 138679245283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12147 : Bounds (7969849 / 7812500) (510070337 / 500000000) (Real.log (138679245283 / 50000000000)) := by
  have h := reflection_log_12147_neg
  have he : Real.log (138679245283 / 50000000000) = -Real.log (50000000000 / 138679245283) := by
    rw [show ((138679245283 / 50000000000) : ℝ) = ((50000000000 / 138679245283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12148_neg : (127838661 / 125000000) ≤ -Real.log (250000000000 / 695179584121) ∧
    -Real.log (250000000000 / 695179584121) ≤ (102270929 / 100000000) := by
  have h := checkLog_sound (w := (195179584121 / 1195179584121)) (n := 12)
    (lo := (82390527 / 250000000)) (hi := (329562109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695179584121 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(695179584121 / 500000000000) = 1/(250000000000 / 695179584121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12148 : Bounds (127838661 / 125000000) (102270929 / 100000000) (Real.log (695179584121 / 250000000000)) := by
  have h := reflection_log_12148_neg
  have he : Real.log (695179584121 / 250000000000) = -Real.log (250000000000 / 695179584121) := by
    rw [show ((695179584121 / 250000000000) : ℝ) = ((250000000000 / 695179584121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12149_neg : (19331101 / 50000000) ≤ -Real.log (125 / 184) ∧
    -Real.log (125 / 184) ≤ (386622021 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 309)) (n := 12)
    (lo := (19331101 / 50000000)) (hi := (386622021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184 / 125) = 1/(125 / 184) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12149 : Bounds (19331101 / 50000000) (386622021 / 1000000000) (Real.log (184 / 125)) := by
  have h := reflection_log_12149_neg
  have he : Real.log (184 / 125) = -Real.log (125 / 184) := by
    rw [show ((184 / 125) : ℝ) = ((125 / 184) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12150_neg : (127731799 / 200000000) ≤ -Real.log (66 / 125) ∧
    -Real.log (66 / 125) ≤ (159664749 / 250000000) := by
  have h := checkLog_sound (w := (59 / 191)) (n := 12)
    (lo := (127731799 / 200000000)) (hi := (159664749 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 66) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 66) = 1/(66 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12150 : Bounds (-159664749 / 250000000) (-127731799 / 200000000) (Real.log (66 / 125)) := by
  have h := reflection_log_12150_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12151_neg : (29493 / 62500000) ≤ -Real.log (125000 / 125059) ∧
    -Real.log (125000 / 125059) ≤ (471889 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 250059)) (n := 12)
    (lo := (29493 / 62500000)) (hi := (471889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125059 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125059 / 125000) = 1/(125000 / 125059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12151 : Bounds (29493 / 62500000) (471889 / 1000000000) (Real.log (125059 / 125000)) := by
  have h := reflection_log_12151_neg
  have he : Real.log (125059 / 125000) = -Real.log (125000 / 125059) := by
    rw [show ((125059 / 125000) : ℝ) = ((125000 / 125059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12152_neg : (472111 / 1000000000) ≤ -Real.log (124941 / 125000) ∧
    -Real.log (124941 / 125000) ≤ (29507 / 62500000) := by
  have h := checkLog_sound (w := (59 / 249941)) (n := 12)
    (lo := (472111 / 1000000000)) (hi := (29507 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124941) = 1/(124941 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12152 : Bounds (-29507 / 62500000) (-472111 / 1000000000) (Real.log (124941 / 125000)) := by
  have h := reflection_log_12152_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12153_neg : (219435083 / 1000000000) ≤ -Real.log (1000000 / 1245373) ∧
    -Real.log (1000000 / 1245373) ≤ (54858771 / 250000000) := by
  have h := checkLog_sound (w := (245373 / 2245373)) (n := 12)
    (lo := (219435083 / 1000000000)) (hi := (54858771 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1245373 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1245373 / 1000000) = 1/(1000000 / 1245373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12153 : Bounds (219435083 / 1000000000) (54858771 / 250000000) (Real.log (1245373 / 1000000)) := by
  have h := reflection_log_12153_neg
  have he : Real.log (1245373 / 1000000) = -Real.log (1000000 / 1245373) := by
    rw [show ((1245373 / 1000000) : ℝ) = ((1000000 / 1245373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12154_neg : (281531691 / 1000000000) ≤ -Real.log (754627 / 1000000) ∧
    -Real.log (754627 / 1000000) ≤ (70382923 / 250000000) := by
  have h := checkLog_sound (w := (245373 / 1754627)) (n := 12)
    (lo := (281531691 / 1000000000)) (hi := (70382923 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 754627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 754627) = 1/(754627 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12154 : Bounds (-70382923 / 250000000) (-281531691 / 1000000000) (Real.log (754627 / 1000000)) := by
  have h := reflection_log_12154_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12155_neg : (220252977 / 1000000000) ≤ -Real.log (125000 / 155799) ∧
    -Real.log (125000 / 155799) ≤ (110126489 / 500000000) := by
  have h := checkLog_sound (w := (30799 / 280799)) (n := 12)
    (lo := (220252977 / 1000000000)) (hi := (110126489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155799 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155799 / 125000) = 1/(125000 / 155799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12155 : Bounds (220252977 / 1000000000) (110126489 / 500000000) (Real.log (155799 / 125000)) := by
  have h := reflection_log_12155_neg
  have he : Real.log (155799 / 125000) = -Real.log (125000 / 155799) := by
    rw [show ((155799 / 125000) : ℝ) = ((125000 / 155799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12156_neg : (14144147 / 50000000) ≤ -Real.log (94201 / 125000) ∧
    -Real.log (94201 / 125000) ≤ (282882941 / 1000000000) := by
  have h := checkLog_sound (w := (30799 / 219201)) (n := 12)
    (lo := (14144147 / 50000000)) (hi := (282882941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 94201) = 1/(94201 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12156 : Bounds (-282882941 / 1000000000) (-14144147 / 50000000) (Real.log (94201 / 125000)) := by
  have h := reflection_log_12156_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12157_neg : (31314981 / 500000000) ≤ -Real.log (14676421599 / 15625000000) ∧
    -Real.log (14676421599 / 15625000000) ≤ (62629963 / 1000000000) := by
  have h := checkLog_sound (w := (948578401 / 30301421599)) (n := 12)
    (lo := (31314981 / 500000000)) (hi := (62629963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14676421599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14676421599) = 1/(14676421599 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12157 : Bounds (-62629963 / 1000000000) (-31314981 / 500000000) (Real.log (14676421599 / 15625000000)) := by
  have h := reflection_log_12157_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12158_neg : (1940519 / 31250000) ≤ -Real.log (939792090871 / 1000000000000) ∧
    -Real.log (939792090871 / 1000000000000) ≤ (62096609 / 1000000000) := by
  have h := checkLog_sound (w := (60207909129 / 1939792090871)) (n := 12)
    (lo := (1940519 / 31250000)) (hi := (62096609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 939792090871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 939792090871) = 1/(939792090871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12158 : Bounds (-62096609 / 1000000000) (-1940519 / 31250000) (Real.log (939792090871 / 1000000000000)) := by
  have h := reflection_log_12158_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12159_neg : (250483387 / 500000000) ≤ -Real.log (500000000000 / 825157991961) ∧
    -Real.log (500000000000 / 825157991961) ≤ (20038671 / 40000000) := by
  have h := checkLog_sound (w := (325157991961 / 1325157991961)) (n := 12)
    (lo := (250483387 / 500000000)) (hi := (20038671 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((825157991961 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(825157991961 / 500000000000) = 1/(500000000000 / 825157991961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12159 : Bounds (250483387 / 500000000) (20038671 / 40000000) (Real.log (825157991961 / 500000000000)) := by
  have h := reflection_log_12159_neg
  have he : Real.log (825157991961 / 500000000000) = -Real.log (500000000000 / 825157991961) := by
    rw [show ((825157991961 / 500000000000) : ℝ) = ((500000000000 / 825157991961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


