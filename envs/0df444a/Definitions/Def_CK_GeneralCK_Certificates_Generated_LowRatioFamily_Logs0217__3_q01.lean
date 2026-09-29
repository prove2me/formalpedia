-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0217__3_q01
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0217__3_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T09:51:36.618672+00:00
-- url     : https://prove2.me/theorems/febeebfe-f461-46a8-8069-24aa26f3762e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0217 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0218, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0217 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0218, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0219) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0217 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0218, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0219) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0217 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0218, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0219) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0217 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0218, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0219) (piece 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0217__3_q00

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0218 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13952_neg : (1624551549 / 1000000000) ≤ -Real.log (197 / 1000) ∧
    -Real.log (197 / 1000) ≤ (12691809 / 7812500) := by
  have h := checkLog_sound (w := (53 / 447)) (n := 12)
    (lo := (238257189 / 1000000000)) (hi := (23825719 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 197) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 197) = 1/(197 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13952 : Bounds (-12691809 / 7812500) (-1624551549 / 1000000000) (Real.log (197 / 1000)) := by
  have h := reflection_log_13952_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13953_neg : (802677 / 1000000000) ≤ -Real.log (1000000 / 1000803) ∧
    -Real.log (1000000 / 1000803) ≤ (401339 / 500000000) := by
  have h := checkLog_sound (w := (803 / 2000803)) (n := 12)
    (lo := (802677 / 1000000000)) (hi := (401339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000803 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000803 / 1000000) = 1/(1000000 / 1000803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13953 : Bounds (802677 / 1000000000) (401339 / 500000000) (Real.log (1000803 / 1000000)) := by
  have h := reflection_log_13953_neg
  have he : Real.log (1000803 / 1000000) = -Real.log (1000000 / 1000803) := by
    rw [show ((1000803 / 1000000) : ℝ) = ((1000000 / 1000803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13954_neg : (401661 / 500000000) ≤ -Real.log (999197 / 1000000) ∧
    -Real.log (999197 / 1000000) ≤ (803323 / 1000000000) := by
  have h := checkLog_sound (w := (803 / 1999197)) (n := 12)
    (lo := (401661 / 500000000)) (hi := (803323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999197) = 1/(999197 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13954 : Bounds (-803323 / 1000000000) (-401661 / 500000000) (Real.log (999197 / 1000000)) := by
  have h := reflection_log_13954_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13955_neg : (188674429 / 500000000) ≤ -Real.log (1000000 / 1458413) ∧
    -Real.log (1000000 / 1458413) ≤ (377348859 / 1000000000) := by
  have h := checkLog_sound (w := (458413 / 2458413)) (n := 12)
    (lo := (188674429 / 500000000)) (hi := (377348859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1458413 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1458413 / 1000000) = 1/(1000000 / 1458413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13955 : Bounds (188674429 / 500000000) (377348859 / 1000000000) (Real.log (1458413 / 1000000)) := by
  have h := reflection_log_13955_neg
  have he : Real.log (1458413 / 1000000) = -Real.log (1000000 / 1458413) := by
    rw [show ((1458413 / 1000000) : ℝ) = ((1000000 / 1458413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13956_neg : (15331289 / 25000000) ≤ -Real.log (541587 / 1000000) ∧
    -Real.log (541587 / 1000000) ≤ (613251561 / 1000000000) := by
  have h := checkLog_sound (w := (458413 / 1541587)) (n := 12)
    (lo := (15331289 / 25000000)) (hi := (613251561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 541587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 541587) = 1/(541587 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13956 : Bounds (-613251561 / 1000000000) (-15331289 / 25000000) (Real.log (541587 / 1000000)) := by
  have h := reflection_log_13956_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13957_neg : (3793853 / 10000000) ≤ -Real.log (500000 / 730693) ∧
    -Real.log (500000 / 730693) ≤ (379385301 / 1000000000) := by
  have h := checkLog_sound (w := (230693 / 1230693)) (n := 12)
    (lo := (3793853 / 10000000)) (hi := (379385301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((730693 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(730693 / 500000) = 1/(500000 / 730693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13957 : Bounds (3793853 / 10000000) (379385301 / 1000000000) (Real.log (730693 / 500000)) := by
  have h := reflection_log_13957_neg
  have he : Real.log (730693 / 500000) = -Real.log (500000 / 730693) := by
    rw [show ((730693 / 500000) : ℝ) = ((500000 / 730693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13958_neg : (123751221 / 200000000) ≤ -Real.log (269307 / 500000) ∧
    -Real.log (269307 / 500000) ≤ (309378053 / 500000000) := by
  have h := checkLog_sound (w := (230693 / 769307)) (n := 12)
    (lo := (123751221 / 200000000)) (hi := (309378053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 269307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 269307) = 1/(269307 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13958 : Bounds (-309378053 / 500000000) (-123751221 / 200000000) (Real.log (269307 / 500000)) := by
  have h := reflection_log_13958_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13959_neg : (47874161 / 200000000) ≤ -Real.log (196780739751 / 250000000000) ∧
    -Real.log (196780739751 / 250000000000) ≤ (119685403 / 500000000) := by
  have h := checkLog_sound (w := (53219260249 / 446780739751)) (n := 12)
    (lo := (47874161 / 200000000)) (hi := (119685403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 196780739751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 196780739751) = 1/(196780739751 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13959 : Bounds (-119685403 / 500000000) (-47874161 / 200000000) (Real.log (196780739751 / 250000000000)) := by
  have h := reflection_log_13959_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13960_neg : (117951351 / 500000000) ≤ -Real.log (789857521431 / 1000000000000) ∧
    -Real.log (789857521431 / 1000000000000) ≤ (235902703 / 1000000000) := by
  have h := checkLog_sound (w := (210142478569 / 1789857521431)) (n := 12)
    (lo := (117951351 / 500000000)) (hi := (235902703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 789857521431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 789857521431) = 1/(789857521431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13960 : Bounds (-235902703 / 1000000000) (-117951351 / 500000000) (Real.log (789857521431 / 1000000000000)) := by
  have h := reflection_log_13960_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13961_neg : (495300209 / 500000000) ≤ -Real.log (250000000000 / 673212706361) ∧
    -Real.log (250000000000 / 673212706361) ≤ (49530021 / 50000000) := by
  have h := checkLog_sound (w := (173212706361 / 1173212706361)) (n := 12)
    (lo := (148726619 / 500000000)) (hi := (297453239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((673212706361 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(673212706361 / 500000000000) = 1/(250000000000 / 673212706361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13961 : Bounds (495300209 / 500000000) (49530021 / 50000000) (Real.log (673212706361 / 250000000000)) := by
  have h := reflection_log_13961_neg
  have he : Real.log (673212706361 / 250000000000) = -Real.log (250000000000 / 673212706361) := by
    rw [show ((673212706361 / 250000000000) : ℝ) = ((250000000000 / 673212706361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13962_neg : (199628281 / 200000000) ≤ -Real.log (500000000000 / 1356617169253) ∧
    -Real.log (500000000000 / 1356617169253) ≤ (998141407 / 1000000000) := by
  have h := checkLog_sound (w := (356617169253 / 2356617169253)) (n := 12)
    (lo := (12199769 / 40000000)) (hi := (152497113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1356617169253 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1356617169253 / 1000000000000) = 1/(500000000000 / 1356617169253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13962 : Bounds (199628281 / 200000000) (998141407 / 1000000000) (Real.log (1356617169253 / 500000000000)) := by
  have h := reflection_log_13962_neg
  have he : Real.log (1356617169253 / 500000000000) = -Real.log (500000000000 / 1356617169253) := by
    rw [show ((1356617169253 / 500000000000) : ℝ) = ((500000000000 / 1356617169253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13963_neg : (553500873 / 250000000) ≤ -Real.log (25000000000 / 228807106599) ∧
    -Real.log (25000000000 / 228807106599) ≤ (276750437 / 125000000) := by
  have h := checkLog_sound (w := (28807106599 / 428807106599)) (n := 12)
    (lo := (4205061 / 31250000)) (hi := (134561953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((228807106599 / 200000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(228807106599 / 200000000000) = 1/(25000000000 / 228807106599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13963 : Bounds (553500873 / 250000000) (276750437 / 125000000) (Real.log (228807106599 / 25000000000)) := by
  have h := reflection_log_13963_neg
  have he : Real.log (228807106599 / 25000000000) = -Real.log (25000000000 / 228807106599) := by
    rw [show ((228807106599 / 25000000000) : ℝ) = ((25000000000 / 228807106599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13964_neg : (295557227 / 500000000) ≤ -Real.log (500 / 903) ∧
    -Real.log (500 / 903) ≤ (118222891 / 200000000) := by
  have h := checkLog_sound (w := (403 / 1403)) (n := 12)
    (lo := (295557227 / 500000000)) (hi := (118222891 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((903 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(903 / 500) = 1/(500 / 903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13964 : Bounds (295557227 / 500000000) (118222891 / 200000000) (Real.log (903 / 500)) := by
  have h := reflection_log_13964_neg
  have he : Real.log (903 / 500) = -Real.log (500 / 903) := by
    rw [show ((903 / 500) : ℝ) = ((500 / 903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13965_neg : (819948559 / 500000000) ≤ -Real.log (97 / 500) ∧
    -Real.log (97 / 500) ≤ (1639897121 / 1000000000) := by
  have h := checkLog_sound (w := (14 / 111)) (n := 12)
    (lo := (126801379 / 500000000)) (hi := (253602759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 97) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 97) = 1/(97 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13965 : Bounds (-1639897121 / 1000000000) (-819948559 / 500000000) (Real.log (97 / 500)) := by
  have h := reflection_log_13965_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13966_neg : (32227 / 40000000) ≤ -Real.log (500000 / 500403) ∧
    -Real.log (500000 / 500403) ≤ (201419 / 250000000) := by
  have h := checkLog_sound (w := (403 / 1000403)) (n := 12)
    (lo := (32227 / 40000000)) (hi := (201419 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500403 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500403 / 500000) = 1/(500000 / 500403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13966 : Bounds (32227 / 40000000) (201419 / 250000000) (Real.log (500403 / 500000)) := by
  have h := reflection_log_13966_neg
  have he : Real.log (500403 / 500000) = -Real.log (500000 / 500403) := by
    rw [show ((500403 / 500000) : ℝ) = ((500000 / 500403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13967_neg : (201581 / 250000000) ≤ -Real.log (499597 / 500000) ∧
    -Real.log (499597 / 500000) ≤ (32253 / 40000000) := by
  have h := checkLog_sound (w := (403 / 999597)) (n := 12)
    (lo := (201581 / 250000000)) (hi := (32253 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499597) = 1/(499597 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13967 : Bounds (-32253 / 40000000) (-201581 / 250000000) (Real.log (499597 / 500000)) := by
  have h := reflection_log_13967_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13968_neg : (378932203 / 1000000000) ≤ -Real.log (250000 / 365181) ∧
    -Real.log (250000 / 365181) ≤ (94733051 / 250000000) := by
  have h := checkLog_sound (w := (115181 / 615181)) (n := 12)
    (lo := (378932203 / 1000000000)) (hi := (94733051 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((365181 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(365181 / 250000) = 1/(250000 / 365181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13968 : Bounds (378932203 / 1000000000) (94733051 / 250000000) (Real.log (365181 / 250000)) := by
  have h := reflection_log_13968_neg
  have he : Real.log (365181 / 250000) = -Real.log (250000 / 365181) := by
    rw [show ((365181 / 250000) : ℝ) = ((250000 / 365181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13969_neg : (617527779 / 1000000000) ≤ -Real.log (134819 / 250000) ∧
    -Real.log (134819 / 250000) ≤ (30876389 / 50000000) := by
  have h := checkLog_sound (w := (115181 / 384819)) (n := 12)
    (lo := (617527779 / 1000000000)) (hi := (30876389 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 134819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 134819) = 1/(134819 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13969 : Bounds (-30876389 / 50000000) (-617527779 / 1000000000) (Real.log (134819 / 250000)) := by
  have h := reflection_log_13969_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13970_neg : (3047789 / 8000000) ≤ -Real.log (1000000 / 1463709) ∧
    -Real.log (1000000 / 1463709) ≤ (190486813 / 500000000) := by
  have h := checkLog_sound (w := (463709 / 2463709)) (n := 12)
    (lo := (3047789 / 8000000)) (hi := (190486813 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1463709 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1463709 / 1000000) = 1/(1000000 / 1463709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13970 : Bounds (3047789 / 8000000) (190486813 / 500000000) (Real.log (1463709 / 1000000)) := by
  have h := reflection_log_13970_neg
  have he : Real.log (1463709 / 1000000) = -Real.log (1000000 / 1463709) := by
    rw [show ((1463709 / 1000000) : ℝ) = ((1000000 / 1463709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13971_neg : (311539177 / 500000000) ≤ -Real.log (536291 / 1000000) ∧
    -Real.log (536291 / 1000000) ≤ (124615671 / 200000000) := by
  have h := checkLog_sound (w := (463709 / 1536291)) (n := 12)
    (lo := (311539177 / 500000000)) (hi := (124615671 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 536291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 536291) = 1/(536291 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13971 : Bounds (-124615671 / 200000000) (-311539177 / 500000000) (Real.log (536291 / 1000000)) := by
  have h := reflection_log_13971_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13972_neg : (242104729 / 1000000000) ≤ -Real.log (784973963319 / 1000000000000) ∧
    -Real.log (784973963319 / 1000000000000) ≤ (24210473 / 100000000) := by
  have h := checkLog_sound (w := (215026036681 / 1784973963319)) (n := 12)
    (lo := (242104729 / 1000000000)) (hi := (24210473 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 784973963319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 784973963319) = 1/(784973963319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13972 : Bounds (-24210473 / 100000000) (-242104729 / 1000000000) (Real.log (784973963319 / 1000000000000)) := by
  have h := reflection_log_13972_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13973_neg : (29824447 / 125000000) ≤ -Real.log (49233337239 / 62500000000) ∧
    -Real.log (49233337239 / 62500000000) ≤ (238595577 / 1000000000) := by
  have h := checkLog_sound (w := (13266662761 / 111733337239)) (n := 12)
    (lo := (29824447 / 125000000)) (hi := (238595577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 49233337239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 49233337239) = 1/(49233337239 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13973 : Bounds (-238595577 / 1000000000) (-29824447 / 125000000) (Real.log (49233337239 / 62500000000)) := by
  have h := reflection_log_13973_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13974_neg : (498229991 / 500000000) ≤ -Real.log (500000000000 / 1354338038407) ∧
    -Real.log (500000000000 / 1354338038407) ≤ (62278749 / 62500000) := by
  have h := checkLog_sound (w := (354338038407 / 2354338038407)) (n := 12)
    (lo := (151656401 / 500000000)) (hi := (303312803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1354338038407 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1354338038407 / 1000000000000) = 1/(500000000000 / 1354338038407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13974 : Bounds (498229991 / 500000000) (62278749 / 62500000) (Real.log (1354338038407 / 500000000000)) := by
  have h := reflection_log_13974_neg
  have he : Real.log (1354338038407 / 500000000000) = -Real.log (500000000000 / 1354338038407) := by
    rw [show ((1354338038407 / 500000000000) : ℝ) = ((500000000000 / 1354338038407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13975_neg : (1004051979 / 1000000000) ≤ -Real.log (500000000000 / 1364659298777) ∧
    -Real.log (500000000000 / 1364659298777) ≤ (1004051981 / 1000000000) := by
  have h := checkLog_sound (w := (364659298777 / 2364659298777)) (n := 12)
    (lo := (310904799 / 1000000000)) (hi := (388631 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1364659298777 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1364659298777 / 1000000000000) = 1/(500000000000 / 1364659298777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13975 : Bounds (1004051979 / 1000000000) (1004051981 / 1000000000) (Real.log (1364659298777 / 500000000000)) := by
  have h := reflection_log_13975_neg
  have he : Real.log (1364659298777 / 500000000000) = -Real.log (500000000000 / 1364659298777) := by
    rw [show ((1364659298777 / 500000000000) : ℝ) = ((500000000000 / 1364659298777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13976_neg : (553500873 / 250000000) ≤ -Real.log (500000000000 / 4576142131979) ∧
    -Real.log (500000000000 / 4576142131979) ≤ (276750437 / 125000000) := by
  have h := checkLog_sound (w := (576142131979 / 8576142131979)) (n := 12)
    (lo := (4205061 / 31250000)) (hi := (134561953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4576142131979 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4576142131979 / 4000000000000) = 1/(500000000000 / 4576142131979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13976 : Bounds (553500873 / 250000000) (276750437 / 125000000) (Real.log (4576142131979 / 500000000000)) := by
  have h := reflection_log_13976_neg
  have he : Real.log (4576142131979 / 500000000000) = -Real.log (500000000000 / 4576142131979) := by
    rw [show ((4576142131979 / 500000000000) : ℝ) = ((500000000000 / 4576142131979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13977_neg : (2231011573 / 1000000000) ≤ -Real.log (250000000000 / 2327319587629) ∧
    -Real.log (250000000000 / 2327319587629) ≤ (2231011577 / 1000000000) := by
  have h := checkLog_sound (w := (327319587629 / 4327319587629)) (n := 12)
    (lo := (151570033 / 1000000000)) (hi := (75785017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2327319587629 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2327319587629 / 2000000000000) = 1/(250000000000 / 2327319587629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13977 : Bounds (2231011573 / 1000000000) (2231011577 / 1000000000) (Real.log (2327319587629 / 250000000000)) := by
  have h := reflection_log_13977_neg
  have he : Real.log (2327319587629 / 250000000000) = -Real.log (250000000000 / 2327319587629) := by
    rw [show ((2327319587629 / 250000000000) : ℝ) = ((250000000000 / 2327319587629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13978_neg : (296387103 / 500000000) ≤ -Real.log (1000 / 1809) ∧
    -Real.log (1000 / 1809) ≤ (592774207 / 1000000000) := by
  have h := checkLog_sound (w := (809 / 2809)) (n := 12)
    (lo := (296387103 / 500000000)) (hi := (592774207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1809 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1809 / 1000) = 1/(1000 / 1809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13978 : Bounds (296387103 / 500000000) (592774207 / 1000000000) (Real.log (1809 / 1000)) := by
  have h := reflection_log_13978_neg
  have he : Real.log (1809 / 1000) = -Real.log (1000 / 1809) := by
    rw [show ((1809 / 1000) : ℝ) = ((1000 / 1809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13979_neg : (1655481849 / 1000000000) ≤ -Real.log (191 / 1000) ∧
    -Real.log (191 / 1000) ≤ (413870463 / 250000000) := by
  have h := checkLog_sound (w := (59 / 441)) (n := 12)
    (lo := (269187489 / 1000000000)) (hi := (26918749 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 191) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 191) = 1/(191 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13979 : Bounds (-413870463 / 250000000) (-1655481849 / 1000000000) (Real.log (191 / 1000)) := by
  have h := reflection_log_13979_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13980_neg : (25271 / 31250000) ≤ -Real.log (1000000 / 1000809) ∧
    -Real.log (1000000 / 1000809) ≤ (808673 / 1000000000) := by
  have h := checkLog_sound (w := (809 / 2000809)) (n := 12)
    (lo := (25271 / 31250000)) (hi := (808673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000809 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000809 / 1000000) = 1/(1000000 / 1000809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13980 : Bounds (25271 / 31250000) (808673 / 1000000000) (Real.log (1000809 / 1000000)) := by
  have h := reflection_log_13980_neg
  have he : Real.log (1000809 / 1000000) = -Real.log (1000000 / 1000809) := by
    rw [show ((1000809 / 1000000) : ℝ) = ((1000000 / 1000809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13981_neg : (809327 / 1000000000) ≤ -Real.log (999191 / 1000000) ∧
    -Real.log (999191 / 1000000) ≤ (50583 / 62500000) := by
  have h := checkLog_sound (w := (809 / 1999191)) (n := 12)
    (lo := (809327 / 1000000000)) (hi := (50583 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999191) = 1/(999191 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13981 : Bounds (-50583 / 62500000) (-809327 / 1000000000) (Real.log (999191 / 1000000)) := by
  have h := reflection_log_13981_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13982_neg : (380520563 / 1000000000) ≤ -Real.log (500000 / 731523) ∧
    -Real.log (500000 / 731523) ≤ (95130141 / 250000000) := by
  have h := checkLog_sound (w := (231523 / 1231523)) (n := 12)
    (lo := (380520563 / 1000000000)) (hi := (95130141 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731523 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731523 / 500000) = 1/(500000 / 731523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13982 : Bounds (380520563 / 1000000000) (95130141 / 250000000) (Real.log (731523 / 500000)) := by
  have h := reflection_log_13982_neg
  have he : Real.log (731523 / 500000) = -Real.log (500000 / 731523) := by
    rw [show ((731523 / 500000) : ℝ) = ((500000 / 731523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13983_neg : (621842849 / 1000000000) ≤ -Real.log (268477 / 500000) ∧
    -Real.log (268477 / 500000) ≤ (12436857 / 20000000) := by
  have h := checkLog_sound (w := (231523 / 768477)) (n := 12)
    (lo := (621842849 / 1000000000)) (hi := (12436857 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 268477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 268477) = 1/(268477 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13983 : Bounds (-12436857 / 20000000) (-621842849 / 1000000000) (Real.log (268477 / 500000)) := by
  have h := reflection_log_13983_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13984_neg : (95641563 / 250000000) ≤ -Real.log (500000 / 733021) ∧
    -Real.log (500000 / 733021) ≤ (382566253 / 1000000000) := by
  have h := checkLog_sound (w := (233021 / 1233021)) (n := 12)
    (lo := (95641563 / 250000000)) (hi := (382566253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((733021 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(733021 / 500000) = 1/(500000 / 733021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13984 : Bounds (95641563 / 250000000) (382566253 / 1000000000) (Real.log (733021 / 500000)) := by
  have h := reflection_log_13984_neg
  have he : Real.log (733021 / 500000) = -Real.log (500000 / 733021) := by
    rw [show ((733021 / 500000) : ℝ) = ((500000 / 733021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13985_neg : (313719047 / 500000000) ≤ -Real.log (266979 / 500000) ∧
    -Real.log (266979 / 500000) ≤ (125487619 / 200000000) := by
  have h := checkLog_sound (w := (233021 / 766979)) (n := 12)
    (lo := (313719047 / 500000000)) (hi := (125487619 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 266979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 266979) = 1/(266979 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13985 : Bounds (-125487619 / 200000000) (-313719047 / 500000000) (Real.log (266979 / 500000)) := by
  have h := reflection_log_13985_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13986_neg : (122435921 / 500000000) ≤ -Real.log (195701213559 / 250000000000) ∧
    -Real.log (195701213559 / 250000000000) ≤ (244871843 / 1000000000) := by
  have h := checkLog_sound (w := (54298786441 / 445701213559)) (n := 12)
    (lo := (122435921 / 500000000)) (hi := (244871843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 195701213559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 195701213559) = 1/(195701213559 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13986 : Bounds (-244871843 / 1000000000) (-122435921 / 500000000) (Real.log (195701213559 / 250000000000)) := by
  have h := reflection_log_13986_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13987_neg : (48264457 / 200000000) ≤ -Real.log (196397100471 / 250000000000) ∧
    -Real.log (196397100471 / 250000000000) ≤ (120661143 / 500000000) := by
  have h := checkLog_sound (w := (53602899529 / 446397100471)) (n := 12)
    (lo := (48264457 / 200000000)) (hi := (120661143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 196397100471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 196397100471) = 1/(196397100471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13987 : Bounds (-120661143 / 500000000) (-48264457 / 200000000) (Real.log (196397100471 / 250000000000)) := by
  have h := reflection_log_13987_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13988_neg : (250590853 / 250000000) ≤ -Real.log (500000000000 / 1362356924429) ∧
    -Real.log (500000000000 / 1362356924429) ≤ (501181707 / 500000000) := by
  have h := checkLog_sound (w := (362356924429 / 2362356924429)) (n := 12)
    (lo := (38652029 / 125000000)) (hi := (309216233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1362356924429 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1362356924429 / 1000000000000) = 1/(500000000000 / 1362356924429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13988 : Bounds (250590853 / 250000000) (501181707 / 500000000) (Real.log (1362356924429 / 500000000000)) := by
  have h := reflection_log_13988_neg
  have he : Real.log (1362356924429 / 500000000000) = -Real.log (500000000000 / 1362356924429) := by
    rw [show ((1362356924429 / 500000000000) : ℝ) = ((500000000000 / 1362356924429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13989_neg : (505002173 / 500000000) ≤ -Real.log (62500000000 / 171600809427) ∧
    -Real.log (62500000000 / 171600809427) ≤ (252501087 / 250000000) := by
  have h := checkLog_sound (w := (46600809427 / 296600809427)) (n := 12)
    (lo := (158428583 / 500000000)) (hi := (316857167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171600809427 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(171600809427 / 125000000000) = 1/(62500000000 / 171600809427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13989 : Bounds (505002173 / 500000000) (252501087 / 250000000) (Real.log (171600809427 / 62500000000)) := by
  have h := reflection_log_13989_neg
  have he : Real.log (171600809427 / 62500000000) = -Real.log (62500000000 / 171600809427) := by
    rw [show ((171600809427 / 62500000000) : ℝ) = ((62500000000 / 171600809427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13990_neg : (2231011573 / 1000000000) ≤ -Real.log (500000000000 / 4654639175257) ∧
    -Real.log (500000000000 / 4654639175257) ≤ (2231011577 / 1000000000) := by
  have h := checkLog_sound (w := (654639175257 / 8654639175257)) (n := 12)
    (lo := (151570033 / 1000000000)) (hi := (75785017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4654639175257 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4654639175257 / 4000000000000) = 1/(500000000000 / 4654639175257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13990 : Bounds (2231011573 / 1000000000) (2231011577 / 1000000000) (Real.log (4654639175257 / 500000000000)) := by
  have h := reflection_log_13990_neg
  have he : Real.log (4654639175257 / 500000000000) = -Real.log (500000000000 / 4654639175257) := by
    rw [show ((4654639175257 / 500000000000) : ℝ) = ((500000000000 / 4654639175257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13991_neg : (449651211 / 200000000) ≤ -Real.log (500000000000 / 4735602094241) ∧
    -Real.log (500000000000 / 4735602094241) ≤ (2248256059 / 1000000000) := by
  have h := checkLog_sound (w := (735602094241 / 8735602094241)) (n := 12)
    (lo := (33762903 / 200000000)) (hi := (42203629 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4735602094241 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4735602094241 / 4000000000000) = 1/(500000000000 / 4735602094241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13991 : Bounds (449651211 / 200000000) (2248256059 / 1000000000) (Real.log (4735602094241 / 500000000000)) := by
  have h := reflection_log_13991_neg
  have he : Real.log (4735602094241 / 500000000000) = -Real.log (500000000000 / 4735602094241) := by
    rw [show ((4735602094241 / 500000000000) : ℝ) = ((500000000000 / 4735602094241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13992_neg : (594431207 / 1000000000) ≤ -Real.log (250 / 453) ∧
    -Real.log (250 / 453) ≤ (74303901 / 125000000) := by
  have h := checkLog_sound (w := (203 / 703)) (n := 12)
    (lo := (594431207 / 1000000000)) (hi := (74303901 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((453 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(453 / 250) = 1/(250 / 453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13992 : Bounds (594431207 / 1000000000) (74303901 / 125000000) (Real.log (453 / 250)) := by
  have h := reflection_log_13992_neg
  have he : Real.log (453 / 250) = -Real.log (250 / 453) := by
    rw [show ((453 / 250) : ℝ) = ((250 / 453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13993_neg : (334262663 / 200000000) ≤ -Real.log (47 / 250) ∧
    -Real.log (47 / 250) ≤ (835656659 / 500000000) := by
  have h := checkLog_sound (w := (31 / 219)) (n := 12)
    (lo := (57003791 / 200000000)) (hi := (71254739 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 94) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 94) = 1/(47 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13993 : Bounds (-835656659 / 500000000) (-334262663 / 200000000) (Real.log (47 / 250)) := by
  have h := reflection_log_13993_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13994_neg : (81167 / 100000000) ≤ -Real.log (250000 / 250203) ∧
    -Real.log (250000 / 250203) ≤ (811671 / 1000000000) := by
  have h := checkLog_sound (w := (203 / 500203)) (n := 12)
    (lo := (81167 / 100000000)) (hi := (811671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250203 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250203 / 250000) = 1/(250000 / 250203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13994 : Bounds (81167 / 100000000) (811671 / 1000000000) (Real.log (250203 / 250000)) := by
  have h := reflection_log_13994_neg
  have he : Real.log (250203 / 250000) = -Real.log (250000 / 250203) := by
    rw [show ((250203 / 250000) : ℝ) = ((250000 / 250203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13995_neg : (812329 / 1000000000) ≤ -Real.log (249797 / 250000) ∧
    -Real.log (249797 / 250000) ≤ (81233 / 100000000) := by
  have h := checkLog_sound (w := (203 / 499797)) (n := 12)
    (lo := (812329 / 1000000000)) (hi := (81233 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249797) = 1/(249797 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13995 : Bounds (-81233 / 100000000) (-812329 / 1000000000) (Real.log (249797 / 250000)) := by
  have h := reflection_log_13995_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13996_neg : (382113229 / 1000000000) ≤ -Real.log (500000 / 732689) ∧
    -Real.log (500000 / 732689) ≤ (38211323 / 100000000) := by
  have h := checkLog_sound (w := (232689 / 1232689)) (n := 12)
    (lo := (382113229 / 1000000000)) (hi := (38211323 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((732689 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(732689 / 500000) = 1/(500000 / 732689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13996 : Bounds (382113229 / 1000000000) (38211323 / 100000000) (Real.log (732689 / 500000)) := by
  have h := reflection_log_13996_neg
  have he : Real.log (732689 / 500000) = -Real.log (500000 / 732689) := by
    rw [show ((732689 / 500000) : ℝ) = ((500000 / 732689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13997_neg : (626195323 / 1000000000) ≤ -Real.log (267311 / 500000) ∧
    -Real.log (267311 / 500000) ≤ (156548831 / 250000000) := by
  have h := checkLog_sound (w := (232689 / 767311)) (n := 12)
    (lo := (626195323 / 1000000000)) (hi := (156548831 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 267311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 267311) = 1/(267311 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13997 : Bounds (-156548831 / 250000000) (-626195323 / 1000000000) (Real.log (267311 / 500000)) := by
  have h := reflection_log_13997_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13998_neg : (192081919 / 500000000) ≤ -Real.log (500000 / 734193) ∧
    -Real.log (500000 / 734193) ≤ (384163839 / 1000000000) := by
  have h := checkLog_sound (w := (234193 / 1234193)) (n := 12)
    (lo := (192081919 / 500000000)) (hi := (384163839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((734193 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(734193 / 500000) = 1/(500000 / 734193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13998 : Bounds (192081919 / 500000000) (384163839 / 1000000000) (Real.log (734193 / 500000)) := by
  have h := reflection_log_13998_neg
  have he : Real.log (734193 / 500000) = -Real.log (500000 / 734193) := by
    rw [show ((734193 / 500000) : ℝ) = ((500000 / 734193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13999_neg : (39489851 / 62500000) ≤ -Real.log (265807 / 500000) ∧
    -Real.log (265807 / 500000) ≤ (631837617 / 1000000000) := by
  have h := checkLog_sound (w := (234193 / 765807)) (n := 12)
    (lo := (39489851 / 62500000)) (hi := (631837617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 265807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 265807) = 1/(265807 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13999 : Bounds (-631837617 / 1000000000) (-39489851 / 62500000) (Real.log (265807 / 500000)) := by
  have h := reflection_log_13999_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14000_neg : (123836889 / 500000000) ≤ -Real.log (195153638751 / 250000000000) ∧
    -Real.log (195153638751 / 250000000000) ≤ (247673779 / 1000000000) := by
  have h := checkLog_sound (w := (54846361249 / 445153638751)) (n := 12)
    (lo := (123836889 / 500000000)) (hi := (247673779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 195153638751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 195153638751) = 1/(195153638751 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14000 : Bounds (-247673779 / 1000000000) (-123836889 / 500000000) (Real.log (195153638751 / 250000000000)) := by
  have h := reflection_log_14000_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14001_neg : (122041047 / 500000000) ≤ -Real.log (195855829279 / 250000000000) ∧
    -Real.log (195855829279 / 250000000000) ≤ (48816419 / 200000000) := by
  have h := checkLog_sound (w := (54144170721 / 445855829279)) (n := 12)
    (lo := (122041047 / 500000000)) (hi := (48816419 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 195855829279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 195855829279) = 1/(195855829279 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14001 : Bounds (-48816419 / 200000000) (-122041047 / 500000000) (Real.log (195855829279 / 250000000000)) := by
  have h := reflection_log_14001_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14002_neg : (126038569 / 125000000) ≤ -Real.log (62500000000 / 171310056451) ∧
    -Real.log (62500000000 / 171310056451) ≤ (504154277 / 500000000) := by
  have h := checkLog_sound (w := (46310056451 / 296310056451)) (n := 12)
    (lo := (78790343 / 250000000)) (hi := (315161373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171310056451 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(171310056451 / 125000000000) = 1/(62500000000 / 171310056451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14002 : Bounds (126038569 / 125000000) (504154277 / 500000000) (Real.log (171310056451 / 62500000000)) := by
  have h := reflection_log_14002_neg
  have he : Real.log (171310056451 / 62500000000) = -Real.log (62500000000 / 171310056451) := by
    rw [show ((171310056451 / 62500000000) : ℝ) = ((62500000000 / 171310056451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14003_neg : (508000727 / 500000000) ≤ -Real.log (500000000000 / 1381064080329) ∧
    -Real.log (500000000000 / 1381064080329) ≤ (63500091 / 62500000) := by
  have h := checkLog_sound (w := (381064080329 / 2381064080329)) (n := 12)
    (lo := (161427137 / 500000000)) (hi := (12914171 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1381064080329 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1381064080329 / 1000000000000) = 1/(500000000000 / 1381064080329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14003 : Bounds (508000727 / 500000000) (63500091 / 62500000) (Real.log (1381064080329 / 500000000000)) := by
  have h := reflection_log_14003_neg
  have he : Real.log (1381064080329 / 500000000000) = -Real.log (500000000000 / 1381064080329) := by
    rw [show ((1381064080329 / 500000000000) : ℝ) = ((500000000000 / 1381064080329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14004_neg : (449651211 / 200000000) ≤ -Real.log (3125000000 / 29597513089) ∧
    -Real.log (3125000000 / 29597513089) ≤ (2248256059 / 1000000000) := by
  have h := checkLog_sound (w := (4597513089 / 54597513089)) (n := 12)
    (lo := (33762903 / 200000000)) (hi := (42203629 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29597513089 / 25000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(29597513089 / 25000000000) = 1/(3125000000 / 29597513089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14004 : Bounds (449651211 / 200000000) (2248256059 / 1000000000) (Real.log (29597513089 / 3125000000)) := by
  have h := reflection_log_14004_neg
  have he : Real.log (29597513089 / 3125000000) = -Real.log (3125000000 / 29597513089) := by
    rw [show ((29597513089 / 3125000000) : ℝ) = ((3125000000 / 29597513089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14005_neg : (1132872261 / 500000000) ≤ -Real.log (500000000000 / 4819148936171) ∧
    -Real.log (500000000000 / 4819148936171) ≤ (1132872263 / 500000000) := by
  have h := checkLog_sound (w := (819148936171 / 8819148936171)) (n := 12)
    (lo := (93151491 / 500000000)) (hi := (186302983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4819148936171 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4819148936171 / 4000000000000) = 1/(500000000000 / 4819148936171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14005 : Bounds (1132872261 / 500000000) (1132872263 / 500000000) (Real.log (4819148936171 / 500000000000)) := by
  have h := reflection_log_14005_neg
  have he : Real.log (4819148936171 / 500000000000) = -Real.log (500000000000 / 4819148936171) := by
    rw [show ((4819148936171 / 500000000000) : ℝ) = ((500000000000 / 4819148936171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14006_neg : (596085467 / 1000000000) ≤ -Real.log (200 / 363) ∧
    -Real.log (200 / 363) ≤ (149021367 / 250000000) := by
  have h := checkLog_sound (w := (163 / 563)) (n := 12)
    (lo := (596085467 / 1000000000)) (hi := (149021367 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363 / 200) = 1/(200 / 363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14006 : Bounds (596085467 / 1000000000) (149021367 / 250000000) (Real.log (363 / 200)) := by
  have h := reflection_log_14006_neg
  have he : Real.log (363 / 200) = -Real.log (200 / 363) := by
    rw [show ((363 / 200) : ℝ) = ((200 / 363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14007_neg : (421849863 / 250000000) ≤ -Real.log (37 / 200) ∧
    -Real.log (37 / 200) ≤ (337479891 / 200000000) := by
  have h := checkLog_sound (w := (13 / 87)) (n := 12)
    (lo := (75276273 / 250000000)) (hi := (301105093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 37) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50 / 37) = 1/(37 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14007 : Bounds (-337479891 / 200000000) (-421849863 / 250000000) (Real.log (37 / 200)) := by
  have h := reflection_log_14007_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14008_neg : (203667 / 250000000) ≤ -Real.log (200000 / 200163) ∧
    -Real.log (200000 / 200163) ≤ (814669 / 1000000000) := by
  have h := checkLog_sound (w := (163 / 400163)) (n := 12)
    (lo := (203667 / 250000000)) (hi := (814669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200163 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200163 / 200000) = 1/(200000 / 200163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14008 : Bounds (203667 / 250000000) (814669 / 1000000000) (Real.log (200163 / 200000)) := by
  have h := reflection_log_14008_neg
  have he : Real.log (200163 / 200000) = -Real.log (200000 / 200163) := by
    rw [show ((200163 / 200000) : ℝ) = ((200000 / 200163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14009_neg : (203833 / 250000000) ≤ -Real.log (199837 / 200000) ∧
    -Real.log (199837 / 200000) ≤ (815333 / 1000000000) := by
  have h := checkLog_sound (w := (163 / 399837)) (n := 12)
    (lo := (203833 / 250000000)) (hi := (815333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199837) = 1/(199837 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14009 : Bounds (-815333 / 1000000000) (-203833 / 250000000) (Real.log (199837 / 200000)) := by
  have h := reflection_log_14009_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14010_neg : (383710857 / 1000000000) ≤ -Real.log (1000000 / 1467721) ∧
    -Real.log (1000000 / 1467721) ≤ (191855429 / 500000000) := by
  have h := checkLog_sound (w := (467721 / 2467721)) (n := 12)
    (lo := (383710857 / 1000000000)) (hi := (191855429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1467721 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1467721 / 1000000) = 1/(1000000 / 1467721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14010 : Bounds (383710857 / 1000000000) (191855429 / 500000000) (Real.log (1467721 / 1000000)) := by
  have h := reflection_log_14010_neg
  have he : Real.log (1467721 / 1000000) = -Real.log (1000000 / 1467721) := by
    rw [show ((1467721 / 1000000) : ℝ) = ((1000000 / 1467721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14011_neg : (630587491 / 1000000000) ≤ -Real.log (532279 / 1000000) ∧
    -Real.log (532279 / 1000000) ≤ (157646873 / 250000000) := by
  have h := checkLog_sound (w := (467721 / 1532279)) (n := 12)
    (lo := (630587491 / 1000000000)) (hi := (157646873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 532279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 532279) = 1/(532279 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14011 : Bounds (-157646873 / 250000000) (-630587491 / 1000000000) (Real.log (532279 / 1000000)) := by
  have h := reflection_log_14011_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14012_neg : (77153271 / 200000000) ≤ -Real.log (1000000 / 1470741) ∧
    -Real.log (1000000 / 1470741) ≤ (96441589 / 250000000) := by
  have h := checkLog_sound (w := (470741 / 2470741)) (n := 12)
    (lo := (77153271 / 200000000)) (hi := (96441589 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1470741 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1470741 / 1000000) = 1/(1000000 / 1470741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14012 : Bounds (77153271 / 200000000) (96441589 / 250000000) (Real.log (1470741 / 1000000)) := by
  have h := reflection_log_14012_neg
  have he : Real.log (1470741 / 1000000) = -Real.log (1000000 / 1470741) := by
    rw [show ((1470741 / 1000000) : ℝ) = ((1000000 / 1470741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14013_neg : (636277363 / 1000000000) ≤ -Real.log (529259 / 1000000) ∧
    -Real.log (529259 / 1000000) ≤ (159069341 / 250000000) := by
  have h := checkLog_sound (w := (470741 / 1529259)) (n := 12)
    (lo := (636277363 / 1000000000)) (hi := (159069341 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 529259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 529259) = 1/(529259 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14013 : Bounds (-159069341 / 250000000) (-636277363 / 1000000000) (Real.log (529259 / 1000000)) := by
  have h := reflection_log_14013_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14014_neg : (7828469 / 31250000) ≤ -Real.log (778402910919 / 1000000000000) ∧
    -Real.log (778402910919 / 1000000000000) ≤ (250511009 / 1000000000) := by
  have h := checkLog_sound (w := (221597089081 / 1778402910919)) (n := 12)
    (lo := (7828469 / 31250000)) (hi := (250511009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 778402910919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 778402910919) = 1/(778402910919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14014 : Bounds (-250511009 / 1000000000) (-7828469 / 31250000) (Real.log (778402910919 / 1000000000000)) := by
  have h := reflection_log_14014_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14015_neg : (246876633 / 1000000000) ≤ -Real.log (781237066159 / 1000000000000) ∧
    -Real.log (781237066159 / 1000000000000) ≤ (123438317 / 500000000) := by
  have h := checkLog_sound (w := (218762933841 / 1781237066159)) (n := 12)
    (lo := (246876633 / 1000000000)) (hi := (123438317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 781237066159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 781237066159) = 1/(781237066159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14015 : Bounds (-123438317 / 500000000) (-246876633 / 1000000000) (Real.log (781237066159 / 1000000000000)) := by
  have h := reflection_log_14015_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


