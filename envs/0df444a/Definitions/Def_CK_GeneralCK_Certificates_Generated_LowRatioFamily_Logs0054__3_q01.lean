-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0054__3_q01
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0054__3_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T09:20:23.225643+00:00
-- url     : https://prove2.me/theorems/7ee5adcc-179f-4706-b4f9-6e84472109e9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0054 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0055, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0054 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0055, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0056) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0054 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0055, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0056) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0054 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0055, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0056) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0054 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0055, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0056) (piece 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0054__3_q00

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0055 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_3520_neg : (11552657 / 125000000) ≤ -Real.log (911721 / 1000000) ∧
    -Real.log (911721 / 1000000) ≤ (92421257 / 1000000000) := by
  have h := checkLog_sound (w := (88279 / 1911721)) (n := 12)
    (lo := (11552657 / 125000000)) (hi := (92421257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 911721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 911721) = 1/(911721 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3520 : Bounds (-92421257 / 1000000000) (-11552657 / 125000000) (Real.log (911721 / 1000000)) := by
  have h := reflection_log_3520_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3521_neg : (7823707 / 1000000000) ≤ -Real.log (992206818159 / 1000000000000) ∧
    -Real.log (992206818159 / 1000000000000) ≤ (1955927 / 250000000) := by
  have h := checkLog_sound (w := (7793181841 / 1992206818159)) (n := 12)
    (lo := (7823707 / 1000000000)) (hi := (1955927 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992206818159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992206818159) = 1/(992206818159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3521 : Bounds (-1955927 / 250000000) (-7823707 / 1000000000) (Real.log (992206818159 / 1000000000000)) := by
  have h := reflection_log_3521_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3522_neg : (3891683 / 500000000) ≤ -Real.log (62015427831 / 62500000000) ∧
    -Real.log (62015427831 / 62500000000) ≤ (7783367 / 1000000000) := by
  have h := checkLog_sound (w := (484572169 / 124515427831)) (n := 12)
    (lo := (3891683 / 500000000)) (hi := (7783367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62015427831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62015427831) = 1/(62015427831 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3522 : Bounds (-7783367 / 1000000000) (-3891683 / 500000000) (Real.log (62015427831 / 62500000000)) := by
  have h := reflection_log_3522_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3523_neg : (176561249 / 1000000000) ≤ -Real.log (500000000000 / 596553750871) ∧
    -Real.log (500000000000 / 596553750871) ≤ (141249 / 800000) := by
  have h := checkLog_sound (w := (96553750871 / 1096553750871)) (n := 12)
    (lo := (176561249 / 1000000000)) (hi := (141249 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596553750871 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596553750871 / 500000000000) = 1/(500000000000 / 596553750871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3523 : Bounds (176561249 / 1000000000) (141249 / 800000) (Real.log (596553750871 / 500000000000)) := by
  have h := reflection_log_3523_neg
  have he : Real.log (596553750871 / 500000000000) = -Real.log (500000000000 / 596553750871) := by
    rw [show ((596553750871 / 500000000000) : ℝ) = ((500000000000 / 596553750871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3524_neg : (88509403 / 500000000) ≤ -Real.log (500000000000 / 596826770471) ∧
    -Real.log (500000000000 / 596826770471) ≤ (177018807 / 1000000000) := by
  have h := checkLog_sound (w := (96826770471 / 1096826770471)) (n := 12)
    (lo := (88509403 / 500000000)) (hi := (177018807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596826770471 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596826770471 / 500000000000) = 1/(500000000000 / 596826770471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3524 : Bounds (88509403 / 500000000) (177018807 / 1000000000) (Real.log (596826770471 / 500000000000)) := by
  have h := reflection_log_3524_neg
  have he : Real.log (596826770471 / 500000000000) = -Real.log (500000000000 / 596826770471) := by
    rw [show ((596826770471 / 500000000000) : ℝ) = ((500000000000 / 596826770471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3525_neg : (354259029 / 1000000000) ≤ -Real.log (500000000000 / 712562143809) ∧
    -Real.log (500000000000 / 712562143809) ≤ (35425903 / 100000000) := by
  have h := checkLog_sound (w := (212562143809 / 1212562143809)) (n := 12)
    (lo := (354259029 / 1000000000)) (hi := (35425903 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((712562143809 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(712562143809 / 500000000000) = 1/(500000000000 / 712562143809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3525 : Bounds (354259029 / 1000000000) (35425903 / 100000000) (Real.log (712562143809 / 500000000000)) := by
  have h := reflection_log_3525_neg
  have he : Real.log (712562143809 / 500000000000) = -Real.log (500000000000 / 712562143809) := by
    rw [show ((712562143809 / 500000000000) : ℝ) = ((500000000000 / 712562143809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3526_neg : (354465373 / 1000000000) ≤ -Real.log (31250000000 / 44544324521) ∧
    -Real.log (31250000000 / 44544324521) ≤ (177232687 / 500000000) := by
  have h := checkLog_sound (w := (13294324521 / 75794324521)) (n := 12)
    (lo := (354465373 / 1000000000)) (hi := (177232687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44544324521 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44544324521 / 31250000000) = 1/(31250000000 / 44544324521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3526 : Bounds (354465373 / 1000000000) (177232687 / 500000000) (Real.log (44544324521 / 31250000000)) := by
  have h := reflection_log_3526_neg
  have he : Real.log (44544324521 / 31250000000) = -Real.log (31250000000 / 44544324521) := by
    rw [show ((44544324521 / 31250000000) : ℝ) = ((31250000000 / 44544324521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3527_neg : (40423397 / 250000000) ≤ -Real.log (2000 / 2351) ∧
    -Real.log (2000 / 2351) ≤ (161693589 / 1000000000) := by
  have h := checkLog_sound (w := (351 / 4351)) (n := 12)
    (lo := (40423397 / 250000000)) (hi := (161693589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2351 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2351 / 2000) = 1/(2000 / 2351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3527 : Bounds (40423397 / 250000000) (161693589 / 1000000000) (Real.log (2351 / 2000)) := by
  have h := reflection_log_3527_neg
  have he : Real.log (2351 / 2000) = -Real.log (2000 / 2351) := by
    rw [show ((2351 / 2000) : ℝ) = ((2000 / 2351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3528_neg : (24122267 / 125000000) ≤ -Real.log (1649 / 2000) ∧
    -Real.log (1649 / 2000) ≤ (192978137 / 1000000000) := by
  have h := checkLog_sound (w := (351 / 3649)) (n := 12)
    (lo := (24122267 / 125000000)) (hi := (192978137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1649) = 1/(1649 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3528 : Bounds (-192978137 / 1000000000) (-24122267 / 125000000) (Real.log (1649 / 2000)) := by
  have h := reflection_log_3528_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3529_neg : (43871 / 250000000) ≤ -Real.log (2000000 / 2000351) ∧
    -Real.log (2000000 / 2000351) ≤ (35097 / 200000000) := by
  have h := checkLog_sound (w := (351 / 4000351)) (n := 12)
    (lo := (43871 / 250000000)) (hi := (35097 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000351 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000351 / 2000000) = 1/(2000000 / 2000351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3529 : Bounds (43871 / 250000000) (35097 / 200000000) (Real.log (2000351 / 2000000)) := by
  have h := reflection_log_3529_neg
  have he : Real.log (2000351 / 2000000) = -Real.log (2000000 / 2000351) := by
    rw [show ((2000351 / 2000000) : ℝ) = ((2000000 / 2000351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3530_neg : (35103 / 200000000) ≤ -Real.log (1999649 / 2000000) ∧
    -Real.log (1999649 / 2000000) ≤ (43879 / 250000000) := by
  have h := checkLog_sound (w := (351 / 3999649)) (n := 12)
    (lo := (35103 / 200000000)) (hi := (43879 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999649) = 1/(1999649 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3530 : Bounds (-43879 / 250000000) (-35103 / 200000000) (Real.log (1999649 / 2000000)) := by
  have h := reflection_log_3530_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3531_neg : (84435813 / 1000000000) ≤ -Real.log (1000000 / 1088103) ∧
    -Real.log (1000000 / 1088103) ≤ (42217907 / 500000000) := by
  have h := checkLog_sound (w := (88103 / 2088103)) (n := 12)
    (lo := (84435813 / 1000000000)) (hi := (42217907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1088103 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1088103 / 1000000) = 1/(1000000 / 1088103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3531 : Bounds (84435813 / 1000000000) (42217907 / 500000000) (Real.log (1088103 / 1000000)) := by
  have h := reflection_log_3531_neg
  have he : Real.log (1088103 / 1000000) = -Real.log (1000000 / 1088103) := by
    rw [show ((1088103 / 1000000) : ℝ) = ((1000000 / 1088103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3532_neg : (92228233 / 1000000000) ≤ -Real.log (911897 / 1000000) ∧
    -Real.log (911897 / 1000000) ≤ (46114117 / 500000000) := by
  have h := checkLog_sound (w := (88103 / 1911897)) (n := 12)
    (lo := (92228233 / 1000000000)) (hi := (46114117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 911897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 911897) = 1/(911897 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3532 : Bounds (-46114117 / 500000000) (-92228233 / 1000000000) (Real.log (911897 / 1000000)) := by
  have h := reflection_log_3532_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3533_neg : (84644411 / 1000000000) ≤ -Real.log (100000 / 108833) ∧
    -Real.log (100000 / 108833) ≤ (21161103 / 250000000) := by
  have h := checkLog_sound (w := (8833 / 208833)) (n := 12)
    (lo := (84644411 / 1000000000)) (hi := (21161103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108833 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108833 / 100000) = 1/(100000 / 108833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3533 : Bounds (84644411 / 1000000000) (21161103 / 250000000) (Real.log (108833 / 100000)) := by
  have h := reflection_log_3533_neg
  have he : Real.log (108833 / 100000) = -Real.log (100000 / 108833) := by
    rw [show ((108833 / 100000) : ℝ) = ((100000 / 108833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3534_neg : (23119299 / 250000000) ≤ -Real.log (91167 / 100000) ∧
    -Real.log (91167 / 100000) ≤ (92477197 / 1000000000) := by
  have h := checkLog_sound (w := (8833 / 191167)) (n := 12)
    (lo := (23119299 / 250000000)) (hi := (92477197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 91167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 91167) = 1/(91167 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3534 : Bounds (-92477197 / 1000000000) (-23119299 / 250000000) (Real.log (91167 / 100000)) := by
  have h := reflection_log_3534_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3535_neg : (1566557 / 200000000) ≤ -Real.log (9921978111 / 10000000000) ∧
    -Real.log (9921978111 / 10000000000) ≤ (3916393 / 500000000) := by
  have h := checkLog_sound (w := (78021889 / 19921978111)) (n := 12)
    (lo := (1566557 / 200000000)) (hi := (3916393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9921978111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9921978111) = 1/(9921978111 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3535 : Bounds (-3916393 / 500000000) (-1566557 / 200000000) (Real.log (9921978111 / 10000000000)) := by
  have h := reflection_log_3535_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3536_neg : (389621 / 50000000) ≤ -Real.log (992237861391 / 1000000000000) ∧
    -Real.log (992237861391 / 1000000000000) ≤ (7792421 / 1000000000) := by
  have h := checkLog_sound (w := (7762138609 / 1992237861391)) (n := 12)
    (lo := (389621 / 50000000)) (hi := (7792421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992237861391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992237861391) = 1/(992237861391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3536 : Bounds (-7792421 / 1000000000) (-389621 / 50000000) (Real.log (992237861391 / 1000000000000)) := by
  have h := reflection_log_3536_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3537_neg : (88332023 / 500000000) ≤ -Real.log (250000000000 / 298307539119) ∧
    -Real.log (250000000000 / 298307539119) ≤ (176664047 / 1000000000) := by
  have h := checkLog_sound (w := (48307539119 / 548307539119)) (n := 12)
    (lo := (88332023 / 500000000)) (hi := (176664047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298307539119 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298307539119 / 250000000000) = 1/(250000000000 / 298307539119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3537 : Bounds (88332023 / 500000000) (176664047 / 1000000000) (Real.log (298307539119 / 250000000000)) := by
  have h := reflection_log_3537_neg
  have he : Real.log (298307539119 / 250000000000) = -Real.log (250000000000 / 298307539119) := by
    rw [show ((298307539119 / 250000000000) : ℝ) = ((250000000000 / 298307539119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3538_neg : (177121607 / 1000000000) ≤ -Real.log (25000000000 / 29844406419) ∧
    -Real.log (25000000000 / 29844406419) ≤ (22140201 / 125000000) := by
  have h := checkLog_sound (w := (4844406419 / 54844406419)) (n := 12)
    (lo := (177121607 / 1000000000)) (hi := (22140201 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29844406419 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29844406419 / 25000000000) = 1/(25000000000 / 29844406419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3538 : Bounds (177121607 / 1000000000) (22140201 / 125000000) (Real.log (29844406419 / 25000000000)) := by
  have h := reflection_log_3538_neg
  have he : Real.log (29844406419 / 25000000000) = -Real.log (25000000000 / 29844406419) := by
    rw [show ((29844406419 / 25000000000) : ℝ) = ((25000000000 / 29844406419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3539_neg : (354465373 / 1000000000) ≤ -Real.log (100000000000 / 142541838467) ∧
    -Real.log (100000000000 / 142541838467) ≤ (177232687 / 500000000) := by
  have h := checkLog_sound (w := (42541838467 / 242541838467)) (n := 12)
    (lo := (354465373 / 1000000000)) (hi := (177232687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142541838467 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142541838467 / 100000000000) = 1/(100000000000 / 142541838467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3539 : Bounds (354465373 / 1000000000) (177232687 / 500000000) (Real.log (142541838467 / 100000000000)) := by
  have h := reflection_log_3539_neg
  have he : Real.log (142541838467 / 100000000000) = -Real.log (100000000000 / 142541838467) := by
    rw [show ((142541838467 / 100000000000) : ℝ) = ((100000000000 / 142541838467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3540_neg : (14186869 / 40000000) ≤ -Real.log (125000000000 / 178214069133) ∧
    -Real.log (125000000000 / 178214069133) ≤ (177335863 / 500000000) := by
  have h := checkLog_sound (w := (53214069133 / 303214069133)) (n := 12)
    (lo := (14186869 / 40000000)) (hi := (177335863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178214069133 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178214069133 / 125000000000) = 1/(125000000000 / 178214069133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3540 : Bounds (14186869 / 40000000) (177335863 / 500000000) (Real.log (178214069133 / 125000000000)) := by
  have h := reflection_log_3540_neg
  have he : Real.log (178214069133 / 125000000000) = -Real.log (125000000000 / 178214069133) := by
    rw [show ((178214069133 / 125000000000) : ℝ) = ((125000000000 / 178214069133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3541_neg : (32355731 / 200000000) ≤ -Real.log (2500 / 2939) ∧
    -Real.log (2500 / 2939) ≤ (5055583 / 31250000) := by
  have h := checkLog_sound (w := (439 / 5439)) (n := 12)
    (lo := (32355731 / 200000000)) (hi := (5055583 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2939 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2939 / 2500) = 1/(2500 / 2939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3541 : Bounds (32355731 / 200000000) (5055583 / 31250000) (Real.log (2939 / 2500)) := by
  have h := reflection_log_3541_neg
  have he : Real.log (2939 / 2500) = -Real.log (2500 / 2939) := by
    rw [show ((2939 / 2500) : ℝ) = ((2500 / 2939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3542_neg : (193099429 / 1000000000) ≤ -Real.log (2061 / 2500) ∧
    -Real.log (2061 / 2500) ≤ (19309943 / 100000000) := by
  have h := checkLog_sound (w := (439 / 4561)) (n := 12)
    (lo := (193099429 / 1000000000)) (hi := (19309943 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2061) = 1/(2061 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3542 : Bounds (-19309943 / 100000000) (-193099429 / 1000000000) (Real.log (2061 / 2500)) := by
  have h := reflection_log_3542_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3543_neg : (5487 / 31250000) ≤ -Real.log (2500000 / 2500439) ∧
    -Real.log (2500000 / 2500439) ≤ (35117 / 200000000) := by
  have h := checkLog_sound (w := (439 / 5000439)) (n := 12)
    (lo := (5487 / 31250000)) (hi := (35117 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500439 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500439 / 2500000) = 1/(2500000 / 2500439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3543 : Bounds (5487 / 31250000) (35117 / 200000000) (Real.log (2500439 / 2500000)) := by
  have h := reflection_log_3543_neg
  have he : Real.log (2500439 / 2500000) = -Real.log (2500000 / 2500439) := by
    rw [show ((2500439 / 2500000) : ℝ) = ((2500000 / 2500439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3544_neg : (35123 / 200000000) ≤ -Real.log (2499561 / 2500000) ∧
    -Real.log (2499561 / 2500000) ≤ (343 / 1953125) := by
  have h := checkLog_sound (w := (439 / 4999561)) (n := 12)
    (lo := (35123 / 200000000)) (hi := (343 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499561) = 1/(2499561 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3544 : Bounds (-343 / 1953125) (-35123 / 200000000) (Real.log (2499561 / 2500000)) := by
  have h := reflection_log_3544_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3545_neg : (42241341 / 500000000) ≤ -Real.log (500000 / 544077) ∧
    -Real.log (500000 / 544077) ≤ (84482683 / 1000000000) := by
  have h := checkLog_sound (w := (44077 / 1044077)) (n := 12)
    (lo := (42241341 / 500000000)) (hi := (84482683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((544077 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(544077 / 500000) = 1/(500000 / 544077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3545 : Bounds (42241341 / 500000000) (84482683 / 1000000000) (Real.log (544077 / 500000)) := by
  have h := reflection_log_3545_neg
  have he : Real.log (544077 / 500000) = -Real.log (500000 / 544077) := by
    rw [show ((544077 / 500000) : ℝ) = ((500000 / 544077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3546_neg : (46142081 / 500000000) ≤ -Real.log (455923 / 500000) ∧
    -Real.log (455923 / 500000) ≤ (92284163 / 1000000000) := by
  have h := checkLog_sound (w := (44077 / 955923)) (n := 12)
    (lo := (46142081 / 500000000)) (hi := (92284163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 455923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 455923) = 1/(455923 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3546 : Bounds (-92284163 / 1000000000) (-46142081 / 500000000) (Real.log (455923 / 500000)) := by
  have h := reflection_log_3546_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3547_neg : (5293147 / 62500000) ≤ -Real.log (50000 / 54419) ∧
    -Real.log (50000 / 54419) ≤ (84690353 / 1000000000) := by
  have h := checkLog_sound (w := (4419 / 104419)) (n := 12)
    (lo := (5293147 / 62500000)) (hi := (84690353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54419 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54419 / 50000) = 1/(50000 / 54419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3547 : Bounds (5293147 / 62500000) (84690353 / 1000000000) (Real.log (54419 / 50000)) := by
  have h := reflection_log_3547_neg
  have he : Real.log (54419 / 50000) = -Real.log (50000 / 54419) := by
    rw [show ((54419 / 50000) : ℝ) = ((50000 / 54419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3548_neg : (46266021 / 500000000) ≤ -Real.log (45581 / 50000) ∧
    -Real.log (45581 / 50000) ≤ (92532043 / 1000000000) := by
  have h := checkLog_sound (w := (4419 / 95581)) (n := 12)
    (lo := (46266021 / 500000000)) (hi := (92532043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45581) = 1/(45581 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3548 : Bounds (-92532043 / 1000000000) (-46266021 / 500000000) (Real.log (45581 / 50000)) := by
  have h := reflection_log_3548_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3549_neg : (784169 / 100000000) ≤ -Real.log (2480472439 / 2500000000) ∧
    -Real.log (2480472439 / 2500000000) ≤ (7841691 / 1000000000) := by
  have h := checkLog_sound (w := (19527561 / 4980472439)) (n := 12)
    (lo := (784169 / 100000000)) (hi := (7841691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2480472439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2480472439) = 1/(2480472439 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3549 : Bounds (-7841691 / 1000000000) (-784169 / 100000000) (Real.log (2480472439 / 2500000000)) := by
  have h := reflection_log_3549_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3550_neg : (195037 / 25000000) ≤ -Real.log (248057218071 / 250000000000) ∧
    -Real.log (248057218071 / 250000000000) ≤ (7801481 / 1000000000) := by
  have h := checkLog_sound (w := (1942781929 / 498057218071)) (n := 12)
    (lo := (195037 / 25000000)) (hi := (7801481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248057218071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248057218071) = 1/(248057218071 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3550 : Bounds (-7801481 / 1000000000) (-195037 / 25000000) (Real.log (248057218071 / 250000000000)) := by
  have h := reflection_log_3550_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3551_neg : (35353369 / 200000000) ≤ -Real.log (31250000000 / 37292275779) ∧
    -Real.log (31250000000 / 37292275779) ≤ (88383423 / 500000000) := by
  have h := checkLog_sound (w := (6042275779 / 68542275779)) (n := 12)
    (lo := (35353369 / 200000000)) (hi := (88383423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37292275779 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37292275779 / 31250000000) = 1/(31250000000 / 37292275779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3551 : Bounds (35353369 / 200000000) (88383423 / 500000000) (Real.log (37292275779 / 31250000000)) := by
  have h := reflection_log_3551_neg
  have he : Real.log (37292275779 / 31250000000) = -Real.log (31250000000 / 37292275779) := by
    rw [show ((37292275779 / 31250000000) : ℝ) = ((31250000000 / 37292275779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3552_neg : (88611197 / 500000000) ≤ -Real.log (250000000000 / 298474144929) ∧
    -Real.log (250000000000 / 298474144929) ≤ (35444479 / 200000000) := by
  have h := checkLog_sound (w := (48474144929 / 548474144929)) (n := 12)
    (lo := (88611197 / 500000000)) (hi := (35444479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298474144929 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298474144929 / 250000000000) = 1/(250000000000 / 298474144929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3552 : Bounds (88611197 / 500000000) (35444479 / 200000000) (Real.log (298474144929 / 250000000000)) := by
  have h := reflection_log_3552_neg
  have he : Real.log (298474144929 / 250000000000) = -Real.log (250000000000 / 298474144929) := by
    rw [show ((298474144929 / 250000000000) : ℝ) = ((250000000000 / 298474144929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3553_neg : (14186869 / 40000000) ≤ -Real.log (500000000000 / 712856276531) ∧
    -Real.log (500000000000 / 712856276531) ≤ (177335863 / 500000000) := by
  have h := checkLog_sound (w := (212856276531 / 1212856276531)) (n := 12)
    (lo := (14186869 / 40000000)) (hi := (177335863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((712856276531 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(712856276531 / 500000000000) = 1/(500000000000 / 712856276531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3553 : Bounds (14186869 / 40000000) (177335863 / 500000000) (Real.log (712856276531 / 500000000000)) := by
  have h := reflection_log_3553_neg
  have he : Real.log (712856276531 / 500000000000) = -Real.log (500000000000 / 712856276531) := by
    rw [show ((712856276531 / 500000000000) : ℝ) = ((500000000000 / 712856276531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3554_neg : (70975617 / 200000000) ≤ -Real.log (50000000000 / 71300339641) ∧
    -Real.log (50000000000 / 71300339641) ≤ (177439043 / 500000000) := by
  have h := checkLog_sound (w := (21300339641 / 121300339641)) (n := 12)
    (lo := (70975617 / 200000000)) (hi := (177439043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71300339641 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71300339641 / 50000000000) = 1/(50000000000 / 71300339641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3554 : Bounds (70975617 / 200000000) (177439043 / 500000000) (Real.log (71300339641 / 50000000000)) := by
  have h := reflection_log_3554_neg
  have he : Real.log (71300339641 / 50000000000) = -Real.log (50000000000 / 71300339641) := by
    rw [show ((71300339641 / 50000000000) : ℝ) = ((50000000000 / 71300339641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3555_neg : (80931857 / 500000000) ≤ -Real.log (10000 / 11757) ∧
    -Real.log (10000 / 11757) ≤ (32372743 / 200000000) := by
  have h := checkLog_sound (w := (1757 / 21757)) (n := 12)
    (lo := (80931857 / 500000000)) (hi := (32372743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11757 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11757 / 10000) = 1/(10000 / 11757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3555 : Bounds (80931857 / 500000000) (32372743 / 200000000) (Real.log (11757 / 10000)) := by
  have h := reflection_log_3555_neg
  have he : Real.log (11757 / 10000) = -Real.log (10000 / 11757) := by
    rw [show ((11757 / 10000) : ℝ) = ((10000 / 11757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3556_neg : (193220737 / 1000000000) ≤ -Real.log (8243 / 10000) ∧
    -Real.log (8243 / 10000) ≤ (96610369 / 500000000) := by
  have h := checkLog_sound (w := (1757 / 18243)) (n := 12)
    (lo := (193220737 / 1000000000)) (hi := (96610369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8243) = 1/(8243 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3556 : Bounds (-96610369 / 500000000) (-193220737 / 1000000000) (Real.log (8243 / 10000)) := by
  have h := reflection_log_3556_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3557_neg : (43921 / 250000000) ≤ -Real.log (10000000 / 10001757) ∧
    -Real.log (10000000 / 10001757) ≤ (35137 / 200000000) := by
  have h := checkLog_sound (w := (1757 / 20001757)) (n := 12)
    (lo := (43921 / 250000000)) (hi := (35137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001757 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001757 / 10000000) = 1/(10000000 / 10001757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3557 : Bounds (43921 / 250000000) (35137 / 200000000) (Real.log (10001757 / 10000000)) := by
  have h := reflection_log_3557_neg
  have he : Real.log (10001757 / 10000000) = -Real.log (10000000 / 10001757) := by
    rw [show ((10001757 / 10000000) : ℝ) = ((10000000 / 10001757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3558_neg : (35143 / 200000000) ≤ -Real.log (9998243 / 10000000) ∧
    -Real.log (9998243 / 10000000) ≤ (43929 / 250000000) := by
  have h := checkLog_sound (w := (1757 / 19998243)) (n := 12)
    (lo := (35143 / 200000000)) (hi := (43929 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998243) = 1/(9998243 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3558 : Bounds (-43929 / 250000000) (-35143 / 200000000) (Real.log (9998243 / 10000000)) := by
  have h := reflection_log_3558_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3559_neg : (84529549 / 1000000000) ≤ -Real.log (200000 / 217641) ∧
    -Real.log (200000 / 217641) ≤ (1690591 / 20000000) := by
  have h := checkLog_sound (w := (17641 / 417641)) (n := 12)
    (lo := (84529549 / 1000000000)) (hi := (1690591 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217641 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217641 / 200000) = 1/(200000 / 217641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3559 : Bounds (84529549 / 1000000000) (1690591 / 20000000) (Real.log (217641 / 200000)) := by
  have h := reflection_log_3559_neg
  have he : Real.log (217641 / 200000) = -Real.log (200000 / 217641) := by
    rw [show ((217641 / 200000) : ℝ) = ((200000 / 217641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3560_neg : (46170047 / 500000000) ≤ -Real.log (182359 / 200000) ∧
    -Real.log (182359 / 200000) ≤ (18468019 / 200000000) := by
  have h := checkLog_sound (w := (17641 / 382359)) (n := 12)
    (lo := (46170047 / 500000000)) (hi := (18468019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182359) = 1/(182359 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3560 : Bounds (-18468019 / 200000000) (-46170047 / 500000000) (Real.log (182359 / 200000)) := by
  have h := reflection_log_3560_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3561_neg : (84737209 / 1000000000) ≤ -Real.log (1000000 / 1088431) ∧
    -Real.log (1000000 / 1088431) ≤ (8473721 / 100000000) := by
  have h := checkLog_sound (w := (88431 / 2088431)) (n := 12)
    (lo := (84737209 / 1000000000)) (hi := (8473721 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1088431 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1088431 / 1000000) = 1/(1000000 / 1088431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3561 : Bounds (84737209 / 1000000000) (8473721 / 100000000) (Real.log (1088431 / 1000000)) := by
  have h := reflection_log_3561_neg
  have he : Real.log (1088431 / 1000000) = -Real.log (1000000 / 1088431) := by
    rw [show ((1088431 / 1000000) : ℝ) = ((1000000 / 1088431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3562_neg : (23146997 / 250000000) ≤ -Real.log (911569 / 1000000) ∧
    -Real.log (911569 / 1000000) ≤ (92587989 / 1000000000) := by
  have h := checkLog_sound (w := (88431 / 1911569)) (n := 12)
    (lo := (23146997 / 250000000)) (hi := (92587989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 911569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 911569) = 1/(911569 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3562 : Bounds (-92587989 / 1000000000) (-23146997 / 250000000) (Real.log (911569 / 1000000)) := by
  have h := reflection_log_3562_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3563_neg : (3925389 / 500000000) ≤ -Real.log (992179958239 / 1000000000000) ∧
    -Real.log (992179958239 / 1000000000000) ≤ (7850779 / 1000000000) := by
  have h := checkLog_sound (w := (7820041761 / 1992179958239)) (n := 12)
    (lo := (3925389 / 500000000)) (hi := (7850779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992179958239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992179958239) = 1/(992179958239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3563 : Bounds (-7850779 / 1000000000) (-3925389 / 500000000) (Real.log (992179958239 / 1000000000000)) := by
  have h := reflection_log_3563_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3564_neg : (1562109 / 200000000) ≤ -Real.log (39688795119 / 40000000000) ∧
    -Real.log (39688795119 / 40000000000) ≤ (3905273 / 500000000) := by
  have h := checkLog_sound (w := (311204881 / 79688795119)) (n := 12)
    (lo := (1562109 / 200000000)) (hi := (3905273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39688795119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39688795119) = 1/(39688795119 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3564 : Bounds (-3905273 / 500000000) (-1562109 / 200000000) (Real.log (39688795119 / 40000000000)) := by
  have h := reflection_log_3564_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3565_neg : (44217411 / 250000000) ≤ -Real.log (31250000000 / 37296109597) ∧
    -Real.log (31250000000 / 37296109597) ≤ (35373929 / 200000000) := by
  have h := checkLog_sound (w := (6046109597 / 68546109597)) (n := 12)
    (lo := (44217411 / 250000000)) (hi := (35373929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37296109597 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37296109597 / 31250000000) = 1/(31250000000 / 37296109597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3565 : Bounds (44217411 / 250000000) (35373929 / 200000000) (Real.log (37296109597 / 31250000000)) := by
  have h := reflection_log_3565_neg
  have he : Real.log (37296109597 / 31250000000) = -Real.log (31250000000 / 37296109597) := by
    rw [show ((37296109597 / 31250000000) : ℝ) = ((31250000000 / 37296109597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3566_neg : (88662599 / 500000000) ≤ -Real.log (100000000000 / 119401932273) ∧
    -Real.log (100000000000 / 119401932273) ≤ (177325199 / 1000000000) := by
  have h := checkLog_sound (w := (19401932273 / 219401932273)) (n := 12)
    (lo := (88662599 / 500000000)) (hi := (177325199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119401932273 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119401932273 / 100000000000) = 1/(100000000000 / 119401932273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3566 : Bounds (88662599 / 500000000) (177325199 / 1000000000) (Real.log (119401932273 / 100000000000)) := by
  have h := reflection_log_3566_neg
  have he : Real.log (119401932273 / 100000000000) = -Real.log (100000000000 / 119401932273) := by
    rw [show ((119401932273 / 100000000000) : ℝ) = ((100000000000 / 119401932273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3567_neg : (70975617 / 200000000) ≤ -Real.log (500000000000 / 713003396409) ∧
    -Real.log (500000000000 / 713003396409) ≤ (177439043 / 500000000) := by
  have h := checkLog_sound (w := (213003396409 / 1213003396409)) (n := 12)
    (lo := (70975617 / 200000000)) (hi := (177439043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((713003396409 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(713003396409 / 500000000000) = 1/(500000000000 / 713003396409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3567 : Bounds (70975617 / 200000000) (177439043 / 500000000) (Real.log (713003396409 / 500000000000)) := by
  have h := reflection_log_3567_neg
  have he : Real.log (713003396409 / 500000000000) = -Real.log (500000000000 / 713003396409) := by
    rw [show ((713003396409 / 500000000000) : ℝ) = ((500000000000 / 713003396409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3568_neg : (88771113 / 250000000) ≤ -Real.log (31250000000 / 44571909499) ∧
    -Real.log (31250000000 / 44571909499) ≤ (355084453 / 1000000000) := by
  have h := checkLog_sound (w := (13321909499 / 75821909499)) (n := 12)
    (lo := (88771113 / 250000000)) (hi := (355084453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44571909499 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44571909499 / 31250000000) = 1/(31250000000 / 44571909499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3568 : Bounds (88771113 / 250000000) (355084453 / 1000000000) (Real.log (44571909499 / 31250000000)) := by
  have h := reflection_log_3568_neg
  have he : Real.log (44571909499 / 31250000000) = -Real.log (31250000000 / 44571909499) := by
    rw [show ((44571909499 / 31250000000) : ℝ) = ((31250000000 / 44571909499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3569_neg : (80974383 / 500000000) ≤ -Real.log (5000 / 5879) ∧
    -Real.log (5000 / 5879) ≤ (161948767 / 1000000000) := by
  have h := checkLog_sound (w := (879 / 10879)) (n := 12)
    (lo := (80974383 / 500000000)) (hi := (161948767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5879 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5879 / 5000) = 1/(5000 / 5879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3569 : Bounds (80974383 / 500000000) (161948767 / 1000000000) (Real.log (5879 / 5000)) := by
  have h := reflection_log_3569_neg
  have he : Real.log (5879 / 5000) = -Real.log (5000 / 5879) := by
    rw [show ((5879 / 5000) : ℝ) = ((5000 / 5879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3570_neg : (9667103 / 50000000) ≤ -Real.log (4121 / 5000) ∧
    -Real.log (4121 / 5000) ≤ (193342061 / 1000000000) := by
  have h := checkLog_sound (w := (879 / 9121)) (n := 12)
    (lo := (9667103 / 50000000)) (hi := (193342061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4121) = 1/(4121 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3570 : Bounds (-193342061 / 1000000000) (-9667103 / 50000000) (Real.log (4121 / 5000)) := by
  have h := reflection_log_3570_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3571_neg : (21973 / 125000000) ≤ -Real.log (5000000 / 5000879) ∧
    -Real.log (5000000 / 5000879) ≤ (35157 / 200000000) := by
  have h := checkLog_sound (w := (879 / 10000879)) (n := 12)
    (lo := (21973 / 125000000)) (hi := (35157 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000879 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000879 / 5000000) = 1/(5000000 / 5000879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3571 : Bounds (21973 / 125000000) (35157 / 200000000) (Real.log (5000879 / 5000000)) := by
  have h := reflection_log_3571_neg
  have he : Real.log (5000879 / 5000000) = -Real.log (5000000 / 5000879) := by
    rw [show ((5000879 / 5000000) : ℝ) = ((5000000 / 5000879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3572_neg : (35163 / 200000000) ≤ -Real.log (4999121 / 5000000) ∧
    -Real.log (4999121 / 5000000) ≤ (21977 / 125000000) := by
  have h := checkLog_sound (w := (879 / 9999121)) (n := 12)
    (lo := (35163 / 200000000)) (hi := (21977 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999121) = 1/(4999121 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3572 : Bounds (-21977 / 125000000) (-35163 / 200000000) (Real.log (4999121 / 5000000)) := by
  have h := reflection_log_3572_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3573_neg : (42288207 / 500000000) ≤ -Real.log (15625 / 17004) ∧
    -Real.log (15625 / 17004) ≤ (16915283 / 200000000) := by
  have h := checkLog_sound (w := (1379 / 32629)) (n := 12)
    (lo := (42288207 / 500000000)) (hi := (16915283 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17004 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17004 / 15625) = 1/(15625 / 17004) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3573 : Bounds (42288207 / 500000000) (16915283 / 200000000) (Real.log (17004 / 15625)) := by
  have h := reflection_log_3573_neg
  have he : Real.log (17004 / 15625) = -Real.log (15625 / 17004) := by
    rw [show ((17004 / 15625) : ℝ) = ((15625 / 17004) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3574_neg : (9239603 / 100000000) ≤ -Real.log (14246 / 15625) ∧
    -Real.log (14246 / 15625) ≤ (92396031 / 1000000000) := by
  have h := checkLog_sound (w := (1379 / 29871)) (n := 12)
    (lo := (9239603 / 100000000)) (hi := (92396031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14246) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 14246) = 1/(14246 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3574 : Bounds (-92396031 / 1000000000) (-9239603 / 100000000) (Real.log (14246 / 15625)) := by
  have h := reflection_log_3574_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3575_neg : (16956813 / 200000000) ≤ -Real.log (500000 / 544241) ∧
    -Real.log (500000 / 544241) ≤ (42392033 / 500000000) := by
  have h := checkLog_sound (w := (44241 / 1044241)) (n := 12)
    (lo := (16956813 / 200000000)) (hi := (42392033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((544241 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(544241 / 500000) = 1/(500000 / 544241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3575 : Bounds (16956813 / 200000000) (42392033 / 500000000) (Real.log (544241 / 500000)) := by
  have h := reflection_log_3575_neg
  have he : Real.log (544241 / 500000) = -Real.log (500000 / 544241) := by
    rw [show ((544241 / 500000) : ℝ) = ((500000 / 544241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3576_neg : (92643937 / 1000000000) ≤ -Real.log (455759 / 500000) ∧
    -Real.log (455759 / 500000) ≤ (46321969 / 500000000) := by
  have h := checkLog_sound (w := (44241 / 955759)) (n := 12)
    (lo := (92643937 / 1000000000)) (hi := (46321969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 455759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 455759) = 1/(455759 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3576 : Bounds (-46321969 / 500000000) (-92643937 / 1000000000) (Real.log (455759 / 500000)) := by
  have h := reflection_log_3576_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3577_neg : (245621 / 31250000) ≤ -Real.log (248042733919 / 250000000000) ∧
    -Real.log (248042733919 / 250000000000) ≤ (7859873 / 1000000000) := by
  have h := checkLog_sound (w := (1957266081 / 498042733919)) (n := 12)
    (lo := (245621 / 31250000)) (hi := (7859873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248042733919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248042733919) = 1/(248042733919 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3577 : Bounds (-7859873 / 1000000000) (-245621 / 31250000) (Real.log (248042733919 / 250000000000)) := by
  have h := reflection_log_3577_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3578_neg : (1563923 / 200000000) ≤ -Real.log (242238984 / 244140625) ∧
    -Real.log (242238984 / 244140625) ≤ (244363 / 31250000) := by
  have h := checkLog_sound (w := (1901641 / 486379609)) (n := 12)
    (lo := (1563923 / 200000000)) (hi := (244363 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 242238984) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 242238984) = 1/(242238984 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3578 : Bounds (-244363 / 31250000) (-1563923 / 200000000) (Real.log (242238984 / 244140625)) := by
  have h := reflection_log_3578_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3579_neg : (44243111 / 250000000) ≤ -Real.log (250000000000 / 298399550751) ∧
    -Real.log (250000000000 / 298399550751) ≤ (35394489 / 200000000) := by
  have h := checkLog_sound (w := (48399550751 / 548399550751)) (n := 12)
    (lo := (44243111 / 250000000)) (hi := (35394489 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298399550751 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298399550751 / 250000000000) = 1/(250000000000 / 298399550751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3579 : Bounds (44243111 / 250000000) (35394489 / 200000000) (Real.log (298399550751 / 250000000000)) := by
  have h := reflection_log_3579_neg
  have he : Real.log (298399550751 / 250000000000) = -Real.log (250000000000 / 298399550751) := by
    rw [show ((298399550751 / 250000000000) : ℝ) = ((250000000000 / 298399550751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3580_neg : (88714001 / 500000000) ≤ -Real.log (500000000000 / 597071039739) ∧
    -Real.log (500000000000 / 597071039739) ≤ (177428003 / 1000000000) := by
  have h := checkLog_sound (w := (97071039739 / 1097071039739)) (n := 12)
    (lo := (88714001 / 500000000)) (hi := (177428003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597071039739 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597071039739 / 500000000000) = 1/(500000000000 / 597071039739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3580 : Bounds (88714001 / 500000000) (177428003 / 1000000000) (Real.log (597071039739 / 500000000000)) := by
  have h := reflection_log_3580_neg
  have he : Real.log (597071039739 / 500000000000) = -Real.log (500000000000 / 597071039739) := by
    rw [show ((597071039739 / 500000000000) : ℝ) = ((500000000000 / 597071039739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3581_neg : (88771113 / 250000000) ≤ -Real.log (500000000000 / 713150551983) ∧
    -Real.log (500000000000 / 713150551983) ≤ (355084453 / 1000000000) := by
  have h := checkLog_sound (w := (213150551983 / 1213150551983)) (n := 12)
    (lo := (88771113 / 250000000)) (hi := (355084453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((713150551983 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(713150551983 / 500000000000) = 1/(500000000000 / 713150551983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3581 : Bounds (88771113 / 250000000) (355084453 / 1000000000) (Real.log (713150551983 / 500000000000)) := by
  have h := reflection_log_3581_neg
  have he : Real.log (713150551983 / 500000000000) = -Real.log (500000000000 / 713150551983) := by
    rw [show ((713150551983 / 500000000000) : ℝ) = ((500000000000 / 713150551983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3582_neg : (355290827 / 1000000000) ≤ -Real.log (500000000000 / 713297743267) ∧
    -Real.log (500000000000 / 713297743267) ≤ (88822707 / 250000000) := by
  have h := checkLog_sound (w := (213297743267 / 1213297743267)) (n := 12)
    (lo := (355290827 / 1000000000)) (hi := (88822707 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((713297743267 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(713297743267 / 500000000000) = 1/(500000000000 / 713297743267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3582 : Bounds (355290827 / 1000000000) (88822707 / 250000000) (Real.log (713297743267 / 500000000000)) := by
  have h := reflection_log_3582_neg
  have he : Real.log (713297743267 / 500000000000) = -Real.log (500000000000 / 713297743267) := by
    rw [show ((713297743267 / 500000000000) : ℝ) = ((500000000000 / 713297743267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3583_neg : (162033811 / 1000000000) ≤ -Real.log (10000 / 11759) ∧
    -Real.log (10000 / 11759) ≤ (40508453 / 250000000) := by
  have h := checkLog_sound (w := (1759 / 21759)) (n := 12)
    (lo := (162033811 / 1000000000)) (hi := (40508453 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11759 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11759 / 10000) = 1/(10000 / 11759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3583 : Bounds (162033811 / 1000000000) (40508453 / 250000000) (Real.log (11759 / 10000)) := by
  have h := reflection_log_3583_neg
  have he : Real.log (11759 / 10000) = -Real.log (10000 / 11759) := by
    rw [show ((11759 / 10000) : ℝ) = ((10000 / 11759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


