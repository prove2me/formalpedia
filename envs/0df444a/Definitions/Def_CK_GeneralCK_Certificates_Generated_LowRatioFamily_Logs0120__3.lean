-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0120__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0120__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T06:12:44.326119+00:00
-- url     : https://prove2.me/theorems/5b9d5976-00a4-45f5-be3f-01567e89909c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0120 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0121, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0120 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0121, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0122)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0120 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0121, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0122)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0120 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0121, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0122) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0120 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0121, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0122).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0120 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7680_neg : (114408577 / 500000000) ≤ -Real.log (500000000000 / 628556080209) ∧
    -Real.log (500000000000 / 628556080209) ≤ (45763431 / 200000000) := by
  have h := checkLog_sound (w := (128556080209 / 1128556080209)) (n := 12)
    (lo := (114408577 / 500000000)) (hi := (45763431 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((628556080209 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(628556080209 / 500000000000) = 1/(500000000000 / 628556080209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7680 : Bounds (114408577 / 500000000) (45763431 / 200000000) (Real.log (628556080209 / 500000000000)) := by
  have h := reflection_log_7680_neg
  have he : Real.log (628556080209 / 500000000000) = -Real.log (500000000000 / 628556080209) := by
    rw [show ((628556080209 / 500000000000) : ℝ) = ((500000000000 / 628556080209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7681_neg : (457833093 / 1000000000) ≤ -Real.log (100000000000 / 158064516129) ∧
    -Real.log (100000000000 / 158064516129) ≤ (228916547 / 500000000) := by
  have h := checkLog_sound (w := (58064516129 / 258064516129)) (n := 12)
    (lo := (457833093 / 1000000000)) (hi := (228916547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158064516129 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(158064516129 / 100000000000) = 1/(100000000000 / 158064516129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7681 : Bounds (457833093 / 1000000000) (228916547 / 500000000) (Real.log (158064516129 / 100000000000)) := by
  have h := reflection_log_7681_neg
  have he : Real.log (158064516129 / 100000000000) = -Real.log (100000000000 / 158064516129) := by
    rw [show ((158064516129 / 100000000000) : ℝ) = ((100000000000 / 158064516129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7682_neg : (458886543 / 1000000000) ≤ -Real.log (62500000000 / 98894448031) ∧
    -Real.log (62500000000 / 98894448031) ≤ (28680409 / 62500000) := by
  have h := checkLog_sound (w := (36394448031 / 161394448031)) (n := 12)
    (lo := (458886543 / 1000000000)) (hi := (28680409 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98894448031 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98894448031 / 62500000000) = 1/(62500000000 / 98894448031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7682 : Bounds (458886543 / 1000000000) (28680409 / 62500000) (Real.log (98894448031 / 62500000000)) := by
  have h := reflection_log_7682_neg
  have he : Real.log (98894448031 / 62500000000) = -Real.log (62500000000 / 98894448031) := by
    rw [show ((98894448031 / 62500000000) : ℝ) = ((62500000000 / 98894448031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7683_neg : (203756837 / 1000000000) ≤ -Real.log (500 / 613) ∧
    -Real.log (500 / 613) ≤ (101878419 / 500000000) := by
  have h := checkLog_sound (w := (113 / 1113)) (n := 12)
    (lo := (203756837 / 1000000000)) (hi := (101878419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613 / 500) = 1/(500 / 613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7683 : Bounds (203756837 / 1000000000) (101878419 / 500000000) (Real.log (613 / 500)) := by
  have h := reflection_log_7683_neg
  have he : Real.log (613 / 500) = -Real.log (500 / 613) := by
    rw [show ((613 / 500) : ℝ) = ((500 / 613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7684_neg : (51236681 / 200000000) ≤ -Real.log (387 / 500) ∧
    -Real.log (387 / 500) ≤ (128091703 / 500000000) := by
  have h := checkLog_sound (w := (113 / 887)) (n := 12)
    (lo := (51236681 / 200000000)) (hi := (128091703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 387) = 1/(387 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7684 : Bounds (-128091703 / 500000000) (-51236681 / 200000000) (Real.log (387 / 500)) := by
  have h := reflection_log_7684_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7685_neg : (112987 / 500000000) ≤ -Real.log (500000 / 500113) ∧
    -Real.log (500000 / 500113) ≤ (9039 / 40000000) := by
  have h := checkLog_sound (w := (113 / 1000113)) (n := 12)
    (lo := (112987 / 500000000)) (hi := (9039 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500113 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500113 / 500000) = 1/(500000 / 500113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7685 : Bounds (112987 / 500000000) (9039 / 40000000) (Real.log (500113 / 500000)) := by
  have h := reflection_log_7685_neg
  have he : Real.log (500113 / 500000) = -Real.log (500000 / 500113) := by
    rw [show ((500113 / 500000) : ℝ) = ((500000 / 500113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7686_neg : (9041 / 40000000) ≤ -Real.log (499887 / 500000) ∧
    -Real.log (499887 / 500000) ≤ (113013 / 500000000) := by
  have h := checkLog_sound (w := (113 / 999887)) (n := 12)
    (lo := (9041 / 40000000)) (hi := (113013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499887) = 1/(499887 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7686 : Bounds (-113013 / 500000000) (-9041 / 40000000) (Real.log (499887 / 500000)) := by
  have h := reflection_log_7686_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7687_neg : (26919033 / 250000000) ≤ -Real.log (1000000 / 1113687) ∧
    -Real.log (1000000 / 1113687) ≤ (107676133 / 1000000000) := by
  have h := checkLog_sound (w := (113687 / 2113687)) (n := 12)
    (lo := (26919033 / 250000000)) (hi := (107676133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1113687 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1113687 / 1000000) = 1/(1000000 / 1113687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7687 : Bounds (26919033 / 250000000) (107676133 / 1000000000) (Real.log (1113687 / 1000000)) := by
  have h := reflection_log_7687_neg
  have he : Real.log (1113687 / 1000000) = -Real.log (1000000 / 1113687) := by
    rw [show ((1113687 / 1000000) : ℝ) = ((1000000 / 1113687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7688_neg : (120685117 / 1000000000) ≤ -Real.log (886313 / 1000000) ∧
    -Real.log (886313 / 1000000) ≤ (60342559 / 500000000) := by
  have h := checkLog_sound (w := (113687 / 1886313)) (n := 12)
    (lo := (120685117 / 1000000000)) (hi := (60342559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 886313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 886313) = 1/(886313 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7688 : Bounds (-60342559 / 500000000) (-120685117 / 1000000000) (Real.log (886313 / 1000000)) := by
  have h := reflection_log_7688_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7689_neg : (21621767 / 200000000) ≤ -Real.log (1000000 / 1114169) ∧
    -Real.log (1000000 / 1114169) ≤ (27027209 / 250000000) := by
  have h := checkLog_sound (w := (114169 / 2114169)) (n := 12)
    (lo := (21621767 / 200000000)) (hi := (27027209 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1114169 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1114169 / 1000000) = 1/(1000000 / 1114169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7689 : Bounds (21621767 / 200000000) (27027209 / 250000000) (Real.log (1114169 / 1000000)) := by
  have h := reflection_log_7689_neg
  have he : Real.log (1114169 / 1000000) = -Real.log (1000000 / 1114169) := by
    rw [show ((1114169 / 1000000) : ℝ) = ((1000000 / 1114169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7690_neg : (121229091 / 1000000000) ≤ -Real.log (885831 / 1000000) ∧
    -Real.log (885831 / 1000000) ≤ (30307273 / 250000000) := by
  have h := checkLog_sound (w := (114169 / 1885831)) (n := 12)
    (lo := (121229091 / 1000000000)) (hi := (30307273 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 885831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 885831) = 1/(885831 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7690 : Bounds (-30307273 / 250000000) (-121229091 / 1000000000) (Real.log (885831 / 1000000)) := by
  have h := reflection_log_7690_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7691_neg : (2624051 / 200000000) ≤ -Real.log (986965439439 / 1000000000000) ∧
    -Real.log (986965439439 / 1000000000000) ≤ (51251 / 3906250) := by
  have h := checkLog_sound (w := (13034560561 / 1986965439439)) (n := 12)
    (lo := (2624051 / 200000000)) (hi := (51251 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986965439439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986965439439) = 1/(986965439439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7691 : Bounds (-51251 / 3906250) (-2624051 / 200000000) (Real.log (986965439439 / 1000000000000)) := by
  have h := reflection_log_7691_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7692_neg : (2601797 / 200000000) ≤ -Real.log (987075266031 / 1000000000000) ∧
    -Real.log (987075266031 / 1000000000000) ≤ (6504493 / 500000000) := by
  have h := checkLog_sound (w := (12924733969 / 1987075266031)) (n := 12)
    (lo := (2601797 / 200000000)) (hi := (6504493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987075266031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987075266031) = 1/(987075266031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7692 : Bounds (-6504493 / 500000000) (-2601797 / 200000000) (Real.log (987075266031 / 1000000000000)) := by
  have h := reflection_log_7692_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7693_neg : (182689 / 800000) ≤ -Real.log (500000000000 / 628269584221) ∧
    -Real.log (500000000000 / 628269584221) ≤ (228361251 / 1000000000) := by
  have h := checkLog_sound (w := (128269584221 / 1128269584221)) (n := 12)
    (lo := (182689 / 800000)) (hi := (228361251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((628269584221 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(628269584221 / 500000000000) = 1/(500000000000 / 628269584221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7693 : Bounds (182689 / 800000) (228361251 / 1000000000) (Real.log (628269584221 / 500000000000)) := by
  have h := reflection_log_7693_neg
  have he : Real.log (628269584221 / 500000000000) = -Real.log (500000000000 / 628269584221) := by
    rw [show ((628269584221 / 500000000000) : ℝ) = ((500000000000 / 628269584221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7694_neg : (229337927 / 1000000000) ≤ -Real.log (7812500000 / 9826304693) ∧
    -Real.log (7812500000 / 9826304693) ≤ (28667241 / 125000000) := by
  have h := checkLog_sound (w := (2013804693 / 17638804693)) (n := 12)
    (lo := (229337927 / 1000000000)) (hi := (28667241 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9826304693 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9826304693 / 7812500000) = 1/(7812500000 / 9826304693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7694 : Bounds (229337927 / 1000000000) (28667241 / 125000000) (Real.log (9826304693 / 7812500000)) := by
  have h := reflection_log_7694_neg
  have he : Real.log (9826304693 / 7812500000) = -Real.log (7812500000 / 9826304693) := by
    rw [show ((9826304693 / 7812500000) : ℝ) = ((7812500000 / 9826304693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7695_neg : (458886543 / 1000000000) ≤ -Real.log (500000000000 / 791155584247) ∧
    -Real.log (500000000000 / 791155584247) ≤ (28680409 / 62500000) := by
  have h := checkLog_sound (w := (291155584247 / 1291155584247)) (n := 12)
    (lo := (458886543 / 1000000000)) (hi := (28680409 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((791155584247 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(791155584247 / 500000000000) = 1/(500000000000 / 791155584247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7695 : Bounds (458886543 / 1000000000) (28680409 / 62500000) (Real.log (791155584247 / 500000000000)) := by
  have h := reflection_log_7695_neg
  have he : Real.log (791155584247 / 500000000000) = -Real.log (500000000000 / 791155584247) := by
    rw [show ((791155584247 / 500000000000) : ℝ) = ((500000000000 / 791155584247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7696_neg : (229970121 / 500000000) ≤ -Real.log (500000000000 / 791989664083) ∧
    -Real.log (500000000000 / 791989664083) ≤ (459940243 / 1000000000) := by
  have h := checkLog_sound (w := (291989664083 / 1291989664083)) (n := 12)
    (lo := (229970121 / 500000000)) (hi := (459940243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((791989664083 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(791989664083 / 500000000000) = 1/(500000000000 / 791989664083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7696 : Bounds (229970121 / 500000000) (459940243 / 1000000000) (Real.log (791989664083 / 500000000000)) := by
  have h := reflection_log_7696_neg
  have he : Real.log (791989664083 / 500000000000) = -Real.log (500000000000 / 791989664083) := by
    rw [show ((791989664083 / 500000000000) : ℝ) = ((500000000000 / 791989664083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7697_neg : (25520573 / 125000000) ≤ -Real.log (2000 / 2453) ∧
    -Real.log (2000 / 2453) ≤ (40832917 / 200000000) := by
  have h := checkLog_sound (w := (453 / 4453)) (n := 12)
    (lo := (25520573 / 125000000)) (hi := (40832917 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2453 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2453 / 2000) = 1/(2000 / 2453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7697 : Bounds (25520573 / 125000000) (40832917 / 200000000) (Real.log (2453 / 2000)) := by
  have h := reflection_log_7697_neg
  have he : Real.log (2453 / 2000) = -Real.log (2000 / 2453) := by
    rw [show ((2453 / 2000) : ℝ) = ((2000 / 2453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7698_neg : (32103701 / 125000000) ≤ -Real.log (1547 / 2000) ∧
    -Real.log (1547 / 2000) ≤ (256829609 / 1000000000) := by
  have h := checkLog_sound (w := (453 / 3547)) (n := 12)
    (lo := (32103701 / 125000000)) (hi := (256829609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1547) = 1/(1547 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7698 : Bounds (-256829609 / 1000000000) (-32103701 / 125000000) (Real.log (1547 / 2000)) := by
  have h := reflection_log_7698_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7699_neg : (113237 / 500000000) ≤ -Real.log (2000000 / 2000453) ∧
    -Real.log (2000000 / 2000453) ≤ (9059 / 40000000) := by
  have h := checkLog_sound (w := (453 / 4000453)) (n := 12)
    (lo := (113237 / 500000000)) (hi := (9059 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000453 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000453 / 2000000) = 1/(2000000 / 2000453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7699 : Bounds (113237 / 500000000) (9059 / 40000000) (Real.log (2000453 / 2000000)) := by
  have h := reflection_log_7699_neg
  have he : Real.log (2000453 / 2000000) = -Real.log (2000000 / 2000453) := by
    rw [show ((2000453 / 2000000) : ℝ) = ((2000000 / 2000453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7700_neg : (9061 / 40000000) ≤ -Real.log (1999547 / 2000000) ∧
    -Real.log (1999547 / 2000000) ≤ (113263 / 500000000) := by
  have h := checkLog_sound (w := (453 / 3999547)) (n := 12)
    (lo := (9061 / 40000000)) (hi := (113263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999547) = 1/(1999547 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7700 : Bounds (-113263 / 500000000) (-9061 / 40000000) (Real.log (1999547 / 2000000)) := by
  have h := reflection_log_7700_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7701_neg : (10790687 / 100000000) ≤ -Real.log (125000 / 139243) ∧
    -Real.log (125000 / 139243) ≤ (107906871 / 1000000000) := by
  have h := checkLog_sound (w := (14243 / 264243)) (n := 12)
    (lo := (10790687 / 100000000)) (hi := (107906871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139243 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139243 / 125000) = 1/(125000 / 139243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7701 : Bounds (10790687 / 100000000) (107906871 / 1000000000) (Real.log (139243 / 125000)) := by
  have h := reflection_log_7701_neg
  have he : Real.log (139243 / 125000) = -Real.log (125000 / 139243) := by
    rw [show ((139243 / 125000) : ℝ) = ((125000 / 139243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7702_neg : (30243781 / 250000000) ≤ -Real.log (110757 / 125000) ∧
    -Real.log (110757 / 125000) ≤ (967801 / 8000000) := by
  have h := checkLog_sound (w := (14243 / 235757)) (n := 12)
    (lo := (30243781 / 250000000)) (hi := (967801 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 110757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 110757) = 1/(110757 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7702 : Bounds (-967801 / 8000000) (-30243781 / 250000000) (Real.log (110757 / 125000)) := by
  have h := reflection_log_7702_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7703_neg : (54169737 / 500000000) ≤ -Real.log (500000 / 557213) ∧
    -Real.log (500000 / 557213) ≤ (4333579 / 40000000) := by
  have h := checkLog_sound (w := (57213 / 1057213)) (n := 12)
    (lo := (54169737 / 500000000)) (hi := (4333579 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((557213 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(557213 / 500000) = 1/(500000 / 557213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7703 : Bounds (54169737 / 500000000) (4333579 / 40000000) (Real.log (557213 / 500000)) := by
  have h := reflection_log_7703_neg
  have he : Real.log (557213 / 500000) = -Real.log (500000 / 557213) := by
    rw [show ((557213 / 500000) : ℝ) = ((500000 / 557213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7704_neg : (15189907 / 125000000) ≤ -Real.log (442787 / 500000) ∧
    -Real.log (442787 / 500000) ≤ (121519257 / 1000000000) := by
  have h := checkLog_sound (w := (57213 / 942787)) (n := 12)
    (lo := (15189907 / 125000000)) (hi := (121519257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 442787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 442787) = 1/(442787 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7704 : Bounds (-121519257 / 1000000000) (-15189907 / 125000000) (Real.log (442787 / 500000)) := by
  have h := reflection_log_7704_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7705_neg : (6589891 / 500000000) ≤ -Real.log (246726672631 / 250000000000) ∧
    -Real.log (246726672631 / 250000000000) ≤ (13179783 / 1000000000) := by
  have h := checkLog_sound (w := (3273327369 / 496726672631)) (n := 12)
    (lo := (6589891 / 500000000)) (hi := (13179783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246726672631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246726672631) = 1/(246726672631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7705 : Bounds (-13179783 / 1000000000) (-6589891 / 500000000) (Real.log (246726672631 / 250000000000)) := by
  have h := reflection_log_7705_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7706_neg : (6534127 / 500000000) ≤ -Real.log (15422136951 / 15625000000) ∧
    -Real.log (15422136951 / 15625000000) ≤ (2613651 / 200000000) := by
  have h := checkLog_sound (w := (202863049 / 31047136951)) (n := 12)
    (lo := (6534127 / 500000000)) (hi := (2613651 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15422136951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15422136951) = 1/(15422136951 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7706 : Bounds (-2613651 / 200000000) (-6534127 / 500000000) (Real.log (15422136951 / 15625000000)) := by
  have h := reflection_log_7706_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7707_neg : (45776399 / 200000000) ≤ -Real.log (500000000000 / 628596838123) ∧
    -Real.log (500000000000 / 628596838123) ≤ (57220499 / 250000000) := by
  have h := checkLog_sound (w := (128596838123 / 1128596838123)) (n := 12)
    (lo := (45776399 / 200000000)) (hi := (57220499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((628596838123 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(628596838123 / 500000000000) = 1/(500000000000 / 628596838123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7707 : Bounds (45776399 / 200000000) (57220499 / 250000000) (Real.log (628596838123 / 500000000000)) := by
  have h := reflection_log_7707_neg
  have he : Real.log (628596838123 / 500000000000) = -Real.log (500000000000 / 628596838123) := by
    rw [show ((628596838123 / 500000000000) : ℝ) = ((500000000000 / 628596838123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7708_neg : (22985873 / 100000000) ≤ -Real.log (250000000000 / 314605555267) ∧
    -Real.log (250000000000 / 314605555267) ≤ (229858731 / 1000000000) := by
  have h := checkLog_sound (w := (64605555267 / 564605555267)) (n := 12)
    (lo := (22985873 / 100000000)) (hi := (229858731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((314605555267 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(314605555267 / 250000000000) = 1/(250000000000 / 314605555267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7708 : Bounds (22985873 / 100000000) (229858731 / 1000000000) (Real.log (314605555267 / 250000000000)) := by
  have h := reflection_log_7708_neg
  have he : Real.log (314605555267 / 250000000000) = -Real.log (250000000000 / 314605555267) := by
    rw [show ((314605555267 / 250000000000) : ℝ) = ((250000000000 / 314605555267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7709_neg : (229970121 / 500000000) ≤ -Real.log (250000000000 / 395994832041) ∧
    -Real.log (250000000000 / 395994832041) ≤ (459940243 / 1000000000) := by
  have h := checkLog_sound (w := (145994832041 / 645994832041)) (n := 12)
    (lo := (229970121 / 500000000)) (hi := (459940243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395994832041 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395994832041 / 250000000000) = 1/(250000000000 / 395994832041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7709 : Bounds (229970121 / 500000000) (459940243 / 1000000000) (Real.log (395994832041 / 250000000000)) := by
  have h := reflection_log_7709_neg
  have he : Real.log (395994832041 / 250000000000) = -Real.log (250000000000 / 395994832041) := by
    rw [show ((395994832041 / 250000000000) : ℝ) = ((250000000000 / 395994832041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7710_neg : (460994193 / 1000000000) ≤ -Real.log (500000000000 / 792824822237) ∧
    -Real.log (500000000000 / 792824822237) ≤ (230497097 / 500000000) := by
  have h := checkLog_sound (w := (292824822237 / 1292824822237)) (n := 12)
    (lo := (460994193 / 1000000000)) (hi := (230497097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((792824822237 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(792824822237 / 500000000000) = 1/(500000000000 / 792824822237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7710 : Bounds (460994193 / 1000000000) (230497097 / 500000000) (Real.log (792824822237 / 500000000000)) := by
  have h := reflection_log_7710_neg
  have he : Real.log (792824822237 / 500000000000) = -Real.log (500000000000 / 792824822237) := by
    rw [show ((792824822237 / 500000000000) : ℝ) = ((500000000000 / 792824822237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7711_neg : (40914433 / 200000000) ≤ -Real.log (1000 / 1227) ∧
    -Real.log (1000 / 1227) ≤ (102286083 / 500000000) := by
  have h := checkLog_sound (w := (227 / 2227)) (n := 12)
    (lo := (40914433 / 200000000)) (hi := (102286083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1227 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1227 / 1000) = 1/(1000 / 1227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7711 : Bounds (40914433 / 200000000) (102286083 / 500000000) (Real.log (1227 / 1000)) := by
  have h := reflection_log_7711_neg
  have he : Real.log (1227 / 1000) = -Real.log (1000 / 1227) := by
    rw [show ((1227 / 1000) : ℝ) = ((1000 / 1227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7712_neg : (25747623 / 100000000) ≤ -Real.log (773 / 1000) ∧
    -Real.log (773 / 1000) ≤ (257476231 / 1000000000) := by
  have h := checkLog_sound (w := (227 / 1773)) (n := 12)
    (lo := (25747623 / 100000000)) (hi := (257476231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 773) = 1/(773 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7712 : Bounds (-257476231 / 1000000000) (-25747623 / 100000000) (Real.log (773 / 1000)) := by
  have h := reflection_log_7712_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7713_neg : (113487 / 500000000) ≤ -Real.log (1000000 / 1000227) ∧
    -Real.log (1000000 / 1000227) ≤ (9079 / 40000000) := by
  have h := checkLog_sound (w := (227 / 2000227)) (n := 12)
    (lo := (113487 / 500000000)) (hi := (9079 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000227 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000227 / 1000000) = 1/(1000000 / 1000227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7713 : Bounds (113487 / 500000000) (9079 / 40000000) (Real.log (1000227 / 1000000)) := by
  have h := reflection_log_7713_neg
  have he : Real.log (1000227 / 1000000) = -Real.log (1000000 / 1000227) := by
    rw [show ((1000227 / 1000000) : ℝ) = ((1000000 / 1000227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7714_neg : (9081 / 40000000) ≤ -Real.log (999773 / 1000000) ∧
    -Real.log (999773 / 1000000) ≤ (113513 / 500000000) := by
  have h := checkLog_sound (w := (227 / 1999773)) (n := 12)
    (lo := (9081 / 40000000)) (hi := (113513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999773) = 1/(999773 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7714 : Bounds (-113513 / 500000000) (-9081 / 40000000) (Real.log (999773 / 1000000)) := by
  have h := reflection_log_7714_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7715_neg : (27034389 / 250000000) ≤ -Real.log (1000000 / 1114201) ∧
    -Real.log (1000000 / 1114201) ≤ (108137557 / 1000000000) := by
  have h := checkLog_sound (w := (114201 / 2114201)) (n := 12)
    (lo := (27034389 / 250000000)) (hi := (108137557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1114201 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1114201 / 1000000) = 1/(1000000 / 1114201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7715 : Bounds (27034389 / 250000000) (108137557 / 1000000000) (Real.log (1114201 / 1000000)) := by
  have h := reflection_log_7715_neg
  have he : Real.log (1114201 / 1000000) = -Real.log (1000000 / 1114201) := by
    rw [show ((1114201 / 1000000) : ℝ) = ((1000000 / 1114201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7716_neg : (1894769 / 15625000) ≤ -Real.log (885799 / 1000000) ∧
    -Real.log (885799 / 1000000) ≤ (121265217 / 1000000000) := by
  have h := checkLog_sound (w := (114201 / 1885799)) (n := 12)
    (lo := (1894769 / 15625000)) (hi := (121265217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 885799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 885799) = 1/(885799 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7716 : Bounds (-121265217 / 1000000000) (-1894769 / 15625000) (Real.log (885799 / 1000000)) := by
  have h := reflection_log_7716_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7717_neg : (27142739 / 250000000) ≤ -Real.log (250000 / 278671) ∧
    -Real.log (250000 / 278671) ≤ (108570957 / 1000000000) := by
  have h := checkLog_sound (w := (28671 / 528671)) (n := 12)
    (lo := (27142739 / 250000000)) (hi := (108570957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((278671 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(278671 / 250000) = 1/(250000 / 278671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7717 : Bounds (27142739 / 250000000) (108570957 / 1000000000) (Real.log (278671 / 250000)) := by
  have h := reflection_log_7717_neg
  have he : Real.log (278671 / 250000) = -Real.log (250000 / 278671) := by
    rw [show ((278671 / 250000) : ℝ) = ((250000 / 278671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7718_neg : (24362127 / 200000000) ≤ -Real.log (221329 / 250000) ∧
    -Real.log (221329 / 250000) ≤ (30452659 / 250000000) := by
  have h := checkLog_sound (w := (28671 / 471329)) (n := 12)
    (lo := (24362127 / 200000000)) (hi := (30452659 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 221329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 221329) = 1/(221329 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7718 : Bounds (-30452659 / 250000000) (-24362127 / 200000000) (Real.log (221329 / 250000)) := by
  have h := reflection_log_7718_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7719_neg : (6619839 / 500000000) ≤ -Real.log (61677973759 / 62500000000) ∧
    -Real.log (61677973759 / 62500000000) ≤ (13239679 / 1000000000) := by
  have h := checkLog_sound (w := (822026241 / 124177973759)) (n := 12)
    (lo := (6619839 / 500000000)) (hi := (13239679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61677973759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61677973759) = 1/(61677973759 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7719 : Bounds (-13239679 / 1000000000) (-6619839 / 500000000) (Real.log (61677973759 / 62500000000)) := by
  have h := reflection_log_7719_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7720_neg : (656383 / 50000000) ≤ -Real.log (986958131599 / 1000000000000) ∧
    -Real.log (986958131599 / 1000000000000) ≤ (13127661 / 1000000000) := by
  have h := checkLog_sound (w := (13041868401 / 1986958131599)) (n := 12)
    (lo := (656383 / 50000000)) (hi := (13127661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986958131599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986958131599) = 1/(986958131599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7720 : Bounds (-13127661 / 1000000000) (-656383 / 50000000) (Real.log (986958131599 / 1000000000000)) := by
  have h := reflection_log_7720_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7721_neg : (57350693 / 250000000) ≤ -Real.log (500000000000 / 628924281919) ∧
    -Real.log (500000000000 / 628924281919) ≤ (229402773 / 1000000000) := by
  have h := checkLog_sound (w := (128924281919 / 1128924281919)) (n := 12)
    (lo := (57350693 / 250000000)) (hi := (229402773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((628924281919 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(628924281919 / 500000000000) = 1/(500000000000 / 628924281919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7721 : Bounds (57350693 / 250000000) (229402773 / 1000000000) (Real.log (628924281919 / 500000000000)) := by
  have h := reflection_log_7721_neg
  have he : Real.log (628924281919 / 500000000000) = -Real.log (500000000000 / 628924281919) := by
    rw [show ((628924281919 / 500000000000) : ℝ) = ((500000000000 / 628924281919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7722_neg : (28797699 / 125000000) ≤ -Real.log (500000000000 / 629540186781) ∧
    -Real.log (500000000000 / 629540186781) ≤ (230381593 / 1000000000) := by
  have h := checkLog_sound (w := (129540186781 / 1129540186781)) (n := 12)
    (lo := (28797699 / 125000000)) (hi := (230381593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((629540186781 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(629540186781 / 500000000000) = 1/(500000000000 / 629540186781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7722 : Bounds (28797699 / 125000000) (230381593 / 1000000000) (Real.log (629540186781 / 500000000000)) := by
  have h := reflection_log_7722_neg
  have he : Real.log (629540186781 / 500000000000) = -Real.log (500000000000 / 629540186781) := by
    rw [show ((629540186781 / 500000000000) : ℝ) = ((500000000000 / 629540186781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7723_neg : (460994193 / 1000000000) ≤ -Real.log (125000000000 / 198206205559) ∧
    -Real.log (125000000000 / 198206205559) ≤ (230497097 / 500000000) := by
  have h := checkLog_sound (w := (73206205559 / 323206205559)) (n := 12)
    (lo := (460994193 / 1000000000)) (hi := (230497097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198206205559 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198206205559 / 125000000000) = 1/(125000000000 / 198206205559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7723 : Bounds (460994193 / 1000000000) (230497097 / 500000000) (Real.log (198206205559 / 125000000000)) := by
  have h := reflection_log_7723_neg
  have he : Real.log (198206205559 / 125000000000) = -Real.log (125000000000 / 198206205559) := by
    rw [show ((198206205559 / 125000000000) : ℝ) = ((125000000000 / 198206205559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7724_neg : (115512099 / 250000000) ≤ -Real.log (500000000000 / 793661060803) ∧
    -Real.log (500000000000 / 793661060803) ≤ (462048397 / 1000000000) := by
  have h := checkLog_sound (w := (293661060803 / 1293661060803)) (n := 12)
    (lo := (115512099 / 250000000)) (hi := (462048397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((793661060803 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(793661060803 / 500000000000) = 1/(500000000000 / 793661060803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7724 : Bounds (115512099 / 250000000) (462048397 / 1000000000) (Real.log (793661060803 / 500000000000)) := by
  have h := reflection_log_7724_neg
  have he : Real.log (793661060803 / 500000000000) = -Real.log (500000000000 / 793661060803) := by
    rw [show ((793661060803 / 500000000000) : ℝ) = ((500000000000 / 793661060803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7725_neg : (10248979 / 50000000) ≤ -Real.log (400 / 491) ∧
    -Real.log (400 / 491) ≤ (204979581 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 891)) (n := 12)
    (lo := (10248979 / 50000000)) (hi := (204979581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491 / 400) = 1/(400 / 491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7725 : Bounds (10248979 / 50000000) (204979581 / 1000000000) (Real.log (491 / 400)) := by
  have h := reflection_log_7725_neg
  have he : Real.log (491 / 400) = -Real.log (400 / 491) := by
    rw [show ((491 / 400) : ℝ) = ((400 / 491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7726_neg : (25812327 / 100000000) ≤ -Real.log (309 / 400) ∧
    -Real.log (309 / 400) ≤ (258123271 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 709)) (n := 12)
    (lo := (25812327 / 100000000)) (hi := (258123271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 309) = 1/(309 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7726 : Bounds (-258123271 / 1000000000) (-25812327 / 100000000) (Real.log (309 / 400)) := by
  have h := reflection_log_7726_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7727_neg : (113737 / 500000000) ≤ -Real.log (400000 / 400091) ∧
    -Real.log (400000 / 400091) ≤ (9099 / 40000000) := by
  have h := checkLog_sound (w := (91 / 800091)) (n := 12)
    (lo := (113737 / 500000000)) (hi := (9099 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400091 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400091 / 400000) = 1/(400000 / 400091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7727 : Bounds (113737 / 500000000) (9099 / 40000000) (Real.log (400091 / 400000)) := by
  have h := reflection_log_7727_neg
  have he : Real.log (400091 / 400000) = -Real.log (400000 / 400091) := by
    rw [show ((400091 / 400000) : ℝ) = ((400000 / 400091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7728_neg : (9101 / 40000000) ≤ -Real.log (399909 / 400000) ∧
    -Real.log (399909 / 400000) ≤ (113763 / 500000000) := by
  have h := checkLog_sound (w := (91 / 799909)) (n := 12)
    (lo := (9101 / 40000000)) (hi := (113763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399909) = 1/(399909 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7728 : Bounds (-113763 / 500000000) (-9101 / 40000000) (Real.log (399909 / 400000)) := by
  have h := reflection_log_7728_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7729_neg : (27092047 / 250000000) ≤ -Real.log (500000 / 557229) ∧
    -Real.log (500000 / 557229) ≤ (108368189 / 1000000000) := by
  have h := checkLog_sound (w := (57229 / 1057229)) (n := 12)
    (lo := (27092047 / 250000000)) (hi := (108368189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((557229 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(557229 / 500000) = 1/(500000 / 557229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7729 : Bounds (27092047 / 250000000) (108368189 / 1000000000) (Real.log (557229 / 500000)) := by
  have h := reflection_log_7729_neg
  have he : Real.log (557229 / 500000) = -Real.log (500000 / 557229) := by
    rw [show ((557229 / 500000) : ℝ) = ((500000 / 557229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7730_neg : (1899303 / 15625000) ≤ -Real.log (442771 / 500000) ∧
    -Real.log (442771 / 500000) ≤ (121555393 / 1000000000) := by
  have h := checkLog_sound (w := (57229 / 942771)) (n := 12)
    (lo := (1899303 / 15625000)) (hi := (121555393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 442771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 442771) = 1/(442771 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7730 : Bounds (-121555393 / 1000000000) (-1899303 / 15625000) (Real.log (442771 / 500000)) := by
  have h := reflection_log_7730_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7731_neg : (6800093 / 62500000) ≤ -Real.log (1000000 / 1114941) ∧
    -Real.log (1000000 / 1114941) ≤ (108801489 / 1000000000) := by
  have h := checkLog_sound (w := (114941 / 2114941)) (n := 12)
    (lo := (6800093 / 62500000)) (hi := (108801489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1114941 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1114941 / 1000000) = 1/(1000000 / 1114941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7731 : Bounds (6800093 / 62500000) (108801489 / 1000000000) (Real.log (1114941 / 1000000)) := by
  have h := reflection_log_7731_neg
  have he : Real.log (1114941 / 1000000) = -Real.log (1000000 / 1114941) := by
    rw [show ((1114941 / 1000000) : ℝ) = ((1000000 / 1114941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7732_neg : (122100969 / 1000000000) ≤ -Real.log (885059 / 1000000) ∧
    -Real.log (885059 / 1000000) ≤ (12210097 / 100000000) := by
  have h := checkLog_sound (w := (114941 / 1885059)) (n := 12)
    (lo := (122100969 / 1000000000)) (hi := (12210097 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 885059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 885059) = 1/(885059 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7732 : Bounds (-12210097 / 100000000) (-122100969 / 1000000000) (Real.log (885059 / 1000000)) := by
  have h := reflection_log_7732_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7733_neg : (332487 / 25000000) ≤ -Real.log (986788566519 / 1000000000000) ∧
    -Real.log (986788566519 / 1000000000000) ≤ (13299481 / 1000000000) := by
  have h := checkLog_sound (w := (13211433481 / 1986788566519)) (n := 12)
    (lo := (332487 / 25000000)) (hi := (13299481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986788566519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986788566519) = 1/(986788566519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7733 : Bounds (-13299481 / 1000000000) (-332487 / 25000000) (Real.log (986788566519 / 1000000000000)) := by
  have h := reflection_log_7733_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7734_neg : (13187203 / 1000000000) ≤ -Real.log (246724841559 / 250000000000) ∧
    -Real.log (246724841559 / 250000000000) ≤ (3296801 / 250000000) := by
  have h := checkLog_sound (w := (3275158441 / 496724841559)) (n := 12)
    (lo := (13187203 / 1000000000)) (hi := (3296801 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246724841559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246724841559) = 1/(246724841559 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7734 : Bounds (-3296801 / 250000000) (-13187203 / 1000000000) (Real.log (246724841559 / 250000000000)) := by
  have h := reflection_log_7734_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7735_neg : (11496179 / 50000000) ≤ -Real.log (20000000000 / 25170076631) ∧
    -Real.log (20000000000 / 25170076631) ≤ (229923581 / 1000000000) := by
  have h := checkLog_sound (w := (5170076631 / 45170076631)) (n := 12)
    (lo := (11496179 / 50000000)) (hi := (229923581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25170076631 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25170076631 / 20000000000) = 1/(20000000000 / 25170076631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7735 : Bounds (11496179 / 50000000) (229923581 / 1000000000) (Real.log (25170076631 / 20000000000)) := by
  have h := reflection_log_7735_neg
  have he : Real.log (25170076631 / 20000000000) = -Real.log (20000000000 / 25170076631) := by
    rw [show ((25170076631 / 20000000000) : ℝ) = ((20000000000 / 25170076631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7736_neg : (115451229 / 500000000) ≤ -Real.log (12500000000 / 15746704457) ∧
    -Real.log (12500000000 / 15746704457) ≤ (230902459 / 1000000000) := by
  have h := checkLog_sound (w := (3246704457 / 28246704457)) (n := 12)
    (lo := (115451229 / 500000000)) (hi := (230902459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15746704457 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15746704457 / 12500000000) = 1/(12500000000 / 15746704457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7736 : Bounds (115451229 / 500000000) (230902459 / 1000000000) (Real.log (15746704457 / 12500000000)) := by
  have h := reflection_log_7736_neg
  have he : Real.log (15746704457 / 12500000000) = -Real.log (12500000000 / 15746704457) := by
    rw [show ((15746704457 / 12500000000) : ℝ) = ((12500000000 / 15746704457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7737_neg : (115512099 / 250000000) ≤ -Real.log (250000000000 / 396830530401) ∧
    -Real.log (250000000000 / 396830530401) ≤ (462048397 / 1000000000) := by
  have h := checkLog_sound (w := (146830530401 / 646830530401)) (n := 12)
    (lo := (115512099 / 250000000)) (hi := (462048397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((396830530401 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(396830530401 / 250000000000) = 1/(250000000000 / 396830530401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7737 : Bounds (115512099 / 250000000) (462048397 / 1000000000) (Real.log (396830530401 / 250000000000)) := by
  have h := reflection_log_7737_neg
  have he : Real.log (396830530401 / 250000000000) = -Real.log (250000000000 / 396830530401) := by
    rw [show ((396830530401 / 250000000000) : ℝ) = ((250000000000 / 396830530401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7738_neg : (9262057 / 20000000) ≤ -Real.log (250000000000 / 397249190939) ∧
    -Real.log (250000000000 / 397249190939) ≤ (463102851 / 1000000000) := by
  have h := checkLog_sound (w := (147249190939 / 647249190939)) (n := 12)
    (lo := (9262057 / 20000000)) (hi := (463102851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((397249190939 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(397249190939 / 250000000000) = 1/(250000000000 / 397249190939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7738 : Bounds (9262057 / 20000000) (463102851 / 1000000000) (Real.log (397249190939 / 250000000000)) := by
  have h := reflection_log_7738_neg
  have he : Real.log (397249190939 / 250000000000) = -Real.log (250000000000 / 397249190939) := by
    rw [show ((397249190939 / 250000000000) : ℝ) = ((250000000000 / 397249190939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7739_neg : (205386829 / 1000000000) ≤ -Real.log (250 / 307) ∧
    -Real.log (250 / 307) ≤ (20538683 / 100000000) := by
  have h := checkLog_sound (w := (57 / 557)) (n := 12)
    (lo := (205386829 / 1000000000)) (hi := (20538683 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307 / 250) = 1/(250 / 307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7739 : Bounds (205386829 / 1000000000) (20538683 / 100000000) (Real.log (307 / 250)) := by
  have h := reflection_log_7739_neg
  have he : Real.log (307 / 250) = -Real.log (250 / 307) := by
    rw [show ((307 / 250) : ℝ) = ((250 / 307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7740_neg : (32346341 / 125000000) ≤ -Real.log (193 / 250) ∧
    -Real.log (193 / 250) ≤ (258770729 / 1000000000) := by
  have h := checkLog_sound (w := (57 / 443)) (n := 12)
    (lo := (32346341 / 125000000)) (hi := (258770729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 193) = 1/(193 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7740 : Bounds (-258770729 / 1000000000) (-32346341 / 125000000) (Real.log (193 / 250)) := by
  have h := reflection_log_7740_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7741_neg : (113987 / 500000000) ≤ -Real.log (250000 / 250057) ∧
    -Real.log (250000 / 250057) ≤ (9119 / 40000000) := by
  have h := checkLog_sound (w := (57 / 500057)) (n := 12)
    (lo := (113987 / 500000000)) (hi := (9119 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250057 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250057 / 250000) = 1/(250000 / 250057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7741 : Bounds (113987 / 500000000) (9119 / 40000000) (Real.log (250057 / 250000)) := by
  have h := reflection_log_7741_neg
  have he : Real.log (250057 / 250000) = -Real.log (250000 / 250057) := by
    rw [show ((250057 / 250000) : ℝ) = ((250000 / 250057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7742_neg : (9121 / 40000000) ≤ -Real.log (249943 / 250000) ∧
    -Real.log (249943 / 250000) ≤ (114013 / 500000000) := by
  have h := checkLog_sound (w := (57 / 499943)) (n := 12)
    (lo := (9121 / 40000000)) (hi := (114013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249943) = 1/(249943 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7742 : Bounds (-114013 / 500000000) (-9121 / 40000000) (Real.log (249943 / 250000)) := by
  have h := reflection_log_7742_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7743_neg : (54299383 / 500000000) ≤ -Real.log (200000 / 222943) ∧
    -Real.log (200000 / 222943) ≤ (108598767 / 1000000000) := by
  have h := checkLog_sound (w := (22943 / 422943)) (n := 12)
    (lo := (54299383 / 500000000)) (hi := (108598767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((222943 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(222943 / 200000) = 1/(200000 / 222943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7743 : Bounds (54299383 / 500000000) (108598767 / 1000000000) (Real.log (222943 / 200000)) := by
  have h := reflection_log_7743_neg
  have he : Real.log (222943 / 200000) = -Real.log (200000 / 222943) := by
    rw [show ((222943 / 200000) : ℝ) = ((200000 / 222943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0121 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7744_neg : (121845651 / 1000000000) ≤ -Real.log (177057 / 200000) ∧
    -Real.log (177057 / 200000) ≤ (30461413 / 250000000) := by
  have h := checkLog_sound (w := (22943 / 377057)) (n := 12)
    (lo := (121845651 / 1000000000)) (hi := (30461413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 177057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 177057) = 1/(177057 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7744 : Bounds (-30461413 / 250000000) (-121845651 / 1000000000) (Real.log (177057 / 200000)) := by
  have h := reflection_log_7744_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7745_neg : (3407277 / 31250000) ≤ -Real.log (1000000 / 1115199) ∧
    -Real.log (1000000 / 1115199) ≤ (21806573 / 200000000) := by
  have h := checkLog_sound (w := (115199 / 2115199)) (n := 12)
    (lo := (3407277 / 31250000)) (hi := (21806573 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1115199 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1115199 / 1000000) = 1/(1000000 / 1115199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7745 : Bounds (3407277 / 31250000) (21806573 / 200000000) (Real.log (1115199 / 1000000)) := by
  have h := reflection_log_7745_neg
  have he : Real.log (1115199 / 1000000) = -Real.log (1000000 / 1115199) := by
    rw [show ((1115199 / 1000000) : ℝ) = ((1000000 / 1115199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7746_neg : (61196259 / 500000000) ≤ -Real.log (884801 / 1000000) ∧
    -Real.log (884801 / 1000000) ≤ (122392519 / 1000000000) := by
  have h := checkLog_sound (w := (115199 / 1884801)) (n := 12)
    (lo := (61196259 / 500000000)) (hi := (122392519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 884801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 884801) = 1/(884801 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7746 : Bounds (-122392519 / 1000000000) (-61196259 / 500000000) (Real.log (884801 / 1000000)) := by
  have h := reflection_log_7746_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7747_neg : (13359653 / 1000000000) ≤ -Real.log (986729190399 / 1000000000000) ∧
    -Real.log (986729190399 / 1000000000000) ≤ (6679827 / 500000000) := by
  have h := checkLog_sound (w := (13270809601 / 1986729190399)) (n := 12)
    (lo := (13359653 / 1000000000)) (hi := (6679827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986729190399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986729190399) = 1/(986729190399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7747 : Bounds (-6679827 / 500000000) (-13359653 / 1000000000) (Real.log (986729190399 / 1000000000000)) := by
  have h := reflection_log_7747_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7748_neg : (2649377 / 200000000) ≤ -Real.log (39473618751 / 40000000000) ∧
    -Real.log (39473618751 / 40000000000) ≤ (6623443 / 500000000) := by
  have h := checkLog_sound (w := (526381249 / 79473618751)) (n := 12)
    (lo := (2649377 / 200000000)) (hi := (6623443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39473618751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39473618751) = 1/(39473618751 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7748 : Bounds (-6623443 / 500000000) (-2649377 / 200000000) (Real.log (39473618751 / 40000000000)) := by
  have h := reflection_log_7748_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7749_neg : (115222209 / 500000000) ≤ -Real.log (500000000000 / 629579739857) ∧
    -Real.log (500000000000 / 629579739857) ≤ (230444419 / 1000000000) := by
  have h := checkLog_sound (w := (129579739857 / 1129579739857)) (n := 12)
    (lo := (115222209 / 500000000)) (hi := (230444419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((629579739857 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(629579739857 / 500000000000) = 1/(500000000000 / 629579739857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7749 : Bounds (115222209 / 500000000) (230444419 / 1000000000) (Real.log (629579739857 / 500000000000)) := by
  have h := reflection_log_7749_neg
  have he : Real.log (629579739857 / 500000000000) = -Real.log (500000000000 / 629579739857) := by
    rw [show ((629579739857 / 500000000000) : ℝ) = ((500000000000 / 629579739857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7750_neg : (115712691 / 500000000) ≤ -Real.log (500000000000 / 630197637661) ∧
    -Real.log (500000000000 / 630197637661) ≤ (231425383 / 1000000000) := by
  have h := checkLog_sound (w := (130197637661 / 1130197637661)) (n := 12)
    (lo := (115712691 / 500000000)) (hi := (231425383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630197637661 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(630197637661 / 500000000000) = 1/(500000000000 / 630197637661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7750 : Bounds (115712691 / 500000000) (231425383 / 1000000000) (Real.log (630197637661 / 500000000000)) := by
  have h := reflection_log_7750_neg
  have he : Real.log (630197637661 / 500000000000) = -Real.log (500000000000 / 630197637661) := by
    rw [show ((630197637661 / 500000000000) : ℝ) = ((500000000000 / 630197637661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7751_neg : (9262057 / 20000000) ≤ -Real.log (500000000000 / 794498381877) ∧
    -Real.log (500000000000 / 794498381877) ≤ (463102851 / 1000000000) := by
  have h := checkLog_sound (w := (294498381877 / 1294498381877)) (n := 12)
    (lo := (9262057 / 20000000)) (hi := (463102851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((794498381877 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(794498381877 / 500000000000) = 1/(500000000000 / 794498381877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7751 : Bounds (9262057 / 20000000) (463102851 / 1000000000) (Real.log (794498381877 / 500000000000)) := by
  have h := reflection_log_7751_neg
  have he : Real.log (794498381877 / 500000000000) = -Real.log (500000000000 / 794498381877) := by
    rw [show ((794498381877 / 500000000000) : ℝ) = ((500000000000 / 794498381877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7752_neg : (232078779 / 500000000) ≤ -Real.log (100000000000 / 159067357513) ∧
    -Real.log (100000000000 / 159067357513) ≤ (464157559 / 1000000000) := by
  have h := checkLog_sound (w := (59067357513 / 259067357513)) (n := 12)
    (lo := (232078779 / 500000000)) (hi := (464157559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159067357513 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159067357513 / 100000000000) = 1/(100000000000 / 159067357513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7752 : Bounds (232078779 / 500000000) (464157559 / 1000000000) (Real.log (159067357513 / 100000000000)) := by
  have h := reflection_log_7752_neg
  have he : Real.log (159067357513 / 100000000000) = -Real.log (100000000000 / 159067357513) := by
    rw [show ((159067357513 / 100000000000) : ℝ) = ((100000000000 / 159067357513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7753_neg : (25724239 / 125000000) ≤ -Real.log (2000 / 2457) ∧
    -Real.log (2000 / 2457) ≤ (205793913 / 1000000000) := by
  have h := checkLog_sound (w := (457 / 4457)) (n := 12)
    (lo := (25724239 / 125000000)) (hi := (205793913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2457 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2457 / 2000) = 1/(2000 / 2457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7753 : Bounds (25724239 / 125000000) (205793913 / 1000000000) (Real.log (2457 / 2000)) := by
  have h := reflection_log_7753_neg
  have he : Real.log (2457 / 2000) = -Real.log (2000 / 2457) := by
    rw [show ((2457 / 2000) : ℝ) = ((2000 / 2457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7754_neg : (259418607 / 1000000000) ≤ -Real.log (1543 / 2000) ∧
    -Real.log (1543 / 2000) ≤ (16213663 / 62500000) := by
  have h := checkLog_sound (w := (457 / 3543)) (n := 12)
    (lo := (259418607 / 1000000000)) (hi := (16213663 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1543) = 1/(1543 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7754 : Bounds (-16213663 / 62500000) (-259418607 / 1000000000) (Real.log (1543 / 2000)) := by
  have h := reflection_log_7754_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7755_neg : (228473 / 1000000000) ≤ -Real.log (2000000 / 2000457) ∧
    -Real.log (2000000 / 2000457) ≤ (114237 / 500000000) := by
  have h := checkLog_sound (w := (457 / 4000457)) (n := 12)
    (lo := (228473 / 1000000000)) (hi := (114237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000457 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000457 / 2000000) = 1/(2000000 / 2000457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7755 : Bounds (228473 / 1000000000) (114237 / 500000000) (Real.log (2000457 / 2000000)) := by
  have h := reflection_log_7755_neg
  have he : Real.log (2000457 / 2000000) = -Real.log (2000000 / 2000457) := by
    rw [show ((2000457 / 2000000) : ℝ) = ((2000000 / 2000457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7756_neg : (114263 / 500000000) ≤ -Real.log (1999543 / 2000000) ∧
    -Real.log (1999543 / 2000000) ≤ (228527 / 1000000000) := by
  have h := checkLog_sound (w := (457 / 3999543)) (n := 12)
    (lo := (114263 / 500000000)) (hi := (228527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999543) = 1/(1999543 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7756 : Bounds (-228527 / 1000000000) (-114263 / 500000000) (Real.log (1999543 / 2000000)) := by
  have h := reflection_log_7756_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7757_neg : (27207323 / 250000000) ≤ -Real.log (250000 / 278743) ∧
    -Real.log (250000 / 278743) ≤ (108829293 / 1000000000) := by
  have h := checkLog_sound (w := (28743 / 528743)) (n := 12)
    (lo := (27207323 / 250000000)) (hi := (108829293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((278743 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(278743 / 250000) = 1/(250000 / 278743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7757 : Bounds (27207323 / 250000000) (108829293 / 1000000000) (Real.log (278743 / 250000)) := by
  have h := reflection_log_7757_neg
  have he : Real.log (278743 / 250000) = -Real.log (250000 / 278743) := by
    rw [show ((278743 / 250000) : ℝ) = ((250000 / 278743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7758_neg : (30533999 / 250000000) ≤ -Real.log (221257 / 250000) ∧
    -Real.log (221257 / 250000) ≤ (122135997 / 1000000000) := by
  have h := checkLog_sound (w := (28743 / 471257)) (n := 12)
    (lo := (30533999 / 250000000)) (hi := (122135997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 221257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 221257) = 1/(221257 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7758 : Bounds (-122135997 / 1000000000) (-30533999 / 250000000) (Real.log (221257 / 250000)) := by
  have h := reflection_log_7758_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7759_neg : (109263289 / 1000000000) ≤ -Real.log (15625 / 17429) ∧
    -Real.log (15625 / 17429) ≤ (10926329 / 100000000) := by
  have h := checkLog_sound (w := (902 / 16527)) (n := 12)
    (lo := (109263289 / 1000000000)) (hi := (10926329 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17429 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17429 / 15625) = 1/(15625 / 17429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7759 : Bounds (109263289 / 1000000000) (10926329 / 100000000) (Real.log (17429 / 15625)) := by
  have h := reflection_log_7759_neg
  have he : Real.log (17429 / 15625) = -Real.log (15625 / 17429) := by
    rw [show ((17429 / 15625) : ℝ) = ((15625 / 17429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7760_neg : (122683021 / 1000000000) ≤ -Real.log (13821 / 15625) ∧
    -Real.log (13821 / 15625) ≤ (61341511 / 500000000) := by
  have h := checkLog_sound (w := (902 / 14723)) (n := 12)
    (lo := (122683021 / 1000000000)) (hi := (61341511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 13821) = 1/(13821 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7760 : Bounds (-61341511 / 500000000) (-122683021 / 1000000000) (Real.log (13821 / 15625)) := by
  have h := reflection_log_7760_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7761_neg : (13419731 / 1000000000) ≤ -Real.log (240886209 / 244140625) ∧
    -Real.log (240886209 / 244140625) ≤ (3354933 / 250000000) := by
  have h := checkLog_sound (w := (1627208 / 242513417)) (n := 12)
    (lo := (13419731 / 1000000000)) (hi := (3354933 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 240886209) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 240886209) = 1/(240886209 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7761 : Bounds (-3354933 / 250000000) (-13419731 / 1000000000) (Real.log (240886209 / 244140625)) := by
  have h := reflection_log_7761_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7762_neg : (13306703 / 1000000000) ≤ -Real.log (61673839951 / 62500000000) ∧
    -Real.log (61673839951 / 62500000000) ≤ (831669 / 62500000) := by
  have h := checkLog_sound (w := (826160049 / 124173839951)) (n := 12)
    (lo := (13306703 / 1000000000)) (hi := (831669 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61673839951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61673839951) = 1/(61673839951 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7762 : Bounds (-831669 / 62500000) (-13306703 / 1000000000) (Real.log (61673839951 / 62500000000)) := by
  have h := reflection_log_7762_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7763_neg : (28870661 / 125000000) ≤ -Real.log (50000000000 / 62990775433) ∧
    -Real.log (50000000000 / 62990775433) ≤ (230965289 / 1000000000) := by
  have h := checkLog_sound (w := (12990775433 / 112990775433)) (n := 12)
    (lo := (28870661 / 125000000)) (hi := (230965289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62990775433 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62990775433 / 50000000000) = 1/(50000000000 / 62990775433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7763 : Bounds (28870661 / 125000000) (230965289 / 1000000000) (Real.log (62990775433 / 50000000000)) := by
  have h := reflection_log_7763_neg
  have he : Real.log (62990775433 / 50000000000) = -Real.log (50000000000 / 62990775433) := by
    rw [show ((62990775433 / 50000000000) : ℝ) = ((50000000000 / 62990775433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7764_neg : (23194631 / 100000000) ≤ -Real.log (500000000000 / 630526011143) ∧
    -Real.log (500000000000 / 630526011143) ≤ (231946311 / 1000000000) := by
  have h := checkLog_sound (w := (130526011143 / 1130526011143)) (n := 12)
    (lo := (23194631 / 100000000)) (hi := (231946311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630526011143 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(630526011143 / 500000000000) = 1/(500000000000 / 630526011143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7764 : Bounds (23194631 / 100000000) (231946311 / 1000000000) (Real.log (630526011143 / 500000000000)) := by
  have h := reflection_log_7764_neg
  have he : Real.log (630526011143 / 500000000000) = -Real.log (500000000000 / 630526011143) := by
    rw [show ((630526011143 / 500000000000) : ℝ) = ((500000000000 / 630526011143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7765_neg : (232078779 / 500000000) ≤ -Real.log (125000000000 / 198834196891) ∧
    -Real.log (125000000000 / 198834196891) ≤ (464157559 / 1000000000) := by
  have h := checkLog_sound (w := (73834196891 / 323834196891)) (n := 12)
    (lo := (232078779 / 500000000)) (hi := (464157559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198834196891 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198834196891 / 125000000000) = 1/(125000000000 / 198834196891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7765 : Bounds (232078779 / 500000000) (464157559 / 1000000000) (Real.log (198834196891 / 125000000000)) := by
  have h := reflection_log_7765_neg
  have he : Real.log (198834196891 / 125000000000) = -Real.log (125000000000 / 198834196891) := by
    rw [show ((198834196891 / 125000000000) : ℝ) = ((125000000000 / 198834196891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7766_neg : (11630313 / 25000000) ≤ -Real.log (20000000000 / 31847051199) ∧
    -Real.log (20000000000 / 31847051199) ≤ (465212521 / 1000000000) := by
  have h := checkLog_sound (w := (11847051199 / 51847051199)) (n := 12)
    (lo := (11630313 / 25000000)) (hi := (465212521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31847051199 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31847051199 / 20000000000) = 1/(20000000000 / 31847051199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7766 : Bounds (11630313 / 25000000) (465212521 / 1000000000) (Real.log (31847051199 / 20000000000)) := by
  have h := reflection_log_7766_neg
  have he : Real.log (31847051199 / 20000000000) = -Real.log (20000000000 / 31847051199) := by
    rw [show ((31847051199 / 20000000000) : ℝ) = ((20000000000 / 31847051199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7767_neg : (20620083 / 100000000) ≤ -Real.log (1000 / 1229) ∧
    -Real.log (1000 / 1229) ≤ (206200831 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 2229)) (n := 12)
    (lo := (20620083 / 100000000)) (hi := (206200831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1229 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1229 / 1000) = 1/(1000 / 1229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7767 : Bounds (20620083 / 100000000) (206200831 / 1000000000) (Real.log (1229 / 1000)) := by
  have h := reflection_log_7767_neg
  have he : Real.log (1229 / 1000) = -Real.log (1000 / 1229) := by
    rw [show ((1229 / 1000) : ℝ) = ((1000 / 1229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7768_neg : (52013381 / 200000000) ≤ -Real.log (771 / 1000) ∧
    -Real.log (771 / 1000) ≤ (130033453 / 500000000) := by
  have h := checkLog_sound (w := (229 / 1771)) (n := 12)
    (lo := (52013381 / 200000000)) (hi := (130033453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 771) = 1/(771 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7768 : Bounds (-130033453 / 500000000) (-52013381 / 200000000) (Real.log (771 / 1000)) := by
  have h := reflection_log_7768_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7769_neg : (228973 / 1000000000) ≤ -Real.log (1000000 / 1000229) ∧
    -Real.log (1000000 / 1000229) ≤ (114487 / 500000000) := by
  have h := checkLog_sound (w := (229 / 2000229)) (n := 12)
    (lo := (228973 / 1000000000)) (hi := (114487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000229 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000229 / 1000000) = 1/(1000000 / 1000229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7769 : Bounds (228973 / 1000000000) (114487 / 500000000) (Real.log (1000229 / 1000000)) := by
  have h := reflection_log_7769_neg
  have he : Real.log (1000229 / 1000000) = -Real.log (1000000 / 1000229) := by
    rw [show ((1000229 / 1000000) : ℝ) = ((1000000 / 1000229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7770_neg : (114513 / 500000000) ≤ -Real.log (999771 / 1000000) ∧
    -Real.log (999771 / 1000000) ≤ (229027 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 1999771)) (n := 12)
    (lo := (114513 / 500000000)) (hi := (229027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999771) = 1/(999771 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7770 : Bounds (-229027 / 1000000000) (-114513 / 500000000) (Real.log (999771 / 1000000)) := by
  have h := reflection_log_7770_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7771_neg : (27264941 / 250000000) ≤ -Real.log (1000000 / 1115229) ∧
    -Real.log (1000000 / 1115229) ≤ (21811953 / 200000000) := by
  have h := checkLog_sound (w := (115229 / 2115229)) (n := 12)
    (lo := (27264941 / 250000000)) (hi := (21811953 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1115229 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1115229 / 1000000) = 1/(1000000 / 1115229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7771 : Bounds (27264941 / 250000000) (21811953 / 200000000) (Real.log (1115229 / 1000000)) := by
  have h := reflection_log_7771_neg
  have he : Real.log (1115229 / 1000000) = -Real.log (1000000 / 1115229) := by
    rw [show ((1115229 / 1000000) : ℝ) = ((1000000 / 1115229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7772_neg : (15303303 / 125000000) ≤ -Real.log (884771 / 1000000) ∧
    -Real.log (884771 / 1000000) ≤ (4897057 / 40000000) := by
  have h := checkLog_sound (w := (115229 / 1884771)) (n := 12)
    (lo := (15303303 / 125000000)) (hi := (4897057 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 884771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 884771) = 1/(884771 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7772 : Bounds (-4897057 / 40000000) (-15303303 / 125000000) (Real.log (884771 / 1000000)) := by
  have h := reflection_log_7772_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7773_neg : (54747279 / 500000000) ≤ -Real.log (500000 / 557857) ∧
    -Real.log (500000 / 557857) ≤ (109494559 / 1000000000) := by
  have h := checkLog_sound (w := (57857 / 1057857)) (n := 12)
    (lo := (54747279 / 500000000)) (hi := (109494559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((557857 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(557857 / 500000) = 1/(500000 / 557857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7773 : Bounds (54747279 / 500000000) (109494559 / 1000000000) (Real.log (557857 / 500000)) := by
  have h := reflection_log_7773_neg
  have he : Real.log (557857 / 500000) = -Real.log (500000 / 557857) := by
    rw [show ((557857 / 500000) : ℝ) = ((500000 / 557857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7774_neg : (122974739 / 1000000000) ≤ -Real.log (442143 / 500000) ∧
    -Real.log (442143 / 500000) ≤ (6148737 / 50000000) := by
  have h := checkLog_sound (w := (57857 / 942143)) (n := 12)
    (lo := (122974739 / 1000000000)) (hi := (6148737 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 442143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 442143) = 1/(442143 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7774 : Bounds (-6148737 / 50000000) (-122974739 / 1000000000) (Real.log (442143 / 500000)) := by
  have h := reflection_log_7774_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7775_neg : (674009 / 50000000) ≤ -Real.log (246652567551 / 250000000000) ∧
    -Real.log (246652567551 / 250000000000) ≤ (13480181 / 1000000000) := by
  have h := checkLog_sound (w := (3347432449 / 496652567551)) (n := 12)
    (lo := (674009 / 50000000)) (hi := (13480181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246652567551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246652567551) = 1/(246652567551 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7775 : Bounds (-13480181 / 1000000000) (-674009 / 50000000) (Real.log (246652567551 / 250000000000)) := by
  have h := reflection_log_7775_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7776_neg : (13366659 / 1000000000) ≤ -Real.log (986722277559 / 1000000000000) ∧
    -Real.log (986722277559 / 1000000000000) ≤ (668333 / 50000000) := by
  have h := checkLog_sound (w := (13277722441 / 1986722277559)) (n := 12)
    (lo := (13366659 / 1000000000)) (hi := (668333 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986722277559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986722277559) = 1/(986722277559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7776 : Bounds (-668333 / 50000000) (-13366659 / 1000000000) (Real.log (986722277559 / 1000000000000)) := by
  have h := reflection_log_7776_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7777_neg : (231486189 / 1000000000) ≤ -Real.log (500000000000 / 630235959361) ∧
    -Real.log (500000000000 / 630235959361) ≤ (23148619 / 100000000) := by
  have h := checkLog_sound (w := (130235959361 / 1130235959361)) (n := 12)
    (lo := (231486189 / 1000000000)) (hi := (23148619 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630235959361 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(630235959361 / 500000000000) = 1/(500000000000 / 630235959361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7777 : Bounds (231486189 / 1000000000) (23148619 / 100000000) (Real.log (630235959361 / 500000000000)) := by
  have h := reflection_log_7777_neg
  have he : Real.log (630235959361 / 500000000000) = -Real.log (500000000000 / 630235959361) := by
    rw [show ((630235959361 / 500000000000) : ℝ) = ((500000000000 / 630235959361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7778_neg : (232469297 / 1000000000) ≤ -Real.log (62500000000 / 78856981791) ∧
    -Real.log (62500000000 / 78856981791) ≤ (116234649 / 500000000) := by
  have h := checkLog_sound (w := (16356981791 / 141356981791)) (n := 12)
    (lo := (232469297 / 1000000000)) (hi := (116234649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78856981791 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78856981791 / 62500000000) = 1/(62500000000 / 78856981791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7778 : Bounds (232469297 / 1000000000) (116234649 / 500000000) (Real.log (78856981791 / 62500000000)) := by
  have h := reflection_log_7778_neg
  have he : Real.log (78856981791 / 62500000000) = -Real.log (62500000000 / 78856981791) := by
    rw [show ((78856981791 / 62500000000) : ℝ) = ((62500000000 / 78856981791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7779_neg : (11630313 / 25000000) ≤ -Real.log (250000000000 / 398088139987) ∧
    -Real.log (250000000000 / 398088139987) ≤ (465212521 / 1000000000) := by
  have h := checkLog_sound (w := (148088139987 / 648088139987)) (n := 12)
    (lo := (11630313 / 25000000)) (hi := (465212521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((398088139987 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(398088139987 / 250000000000) = 1/(250000000000 / 398088139987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7779 : Bounds (11630313 / 25000000) (465212521 / 1000000000) (Real.log (398088139987 / 250000000000)) := by
  have h := reflection_log_7779_neg
  have he : Real.log (398088139987 / 250000000000) = -Real.log (250000000000 / 398088139987) := by
    rw [show ((398088139987 / 250000000000) : ℝ) = ((250000000000 / 398088139987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7780_neg : (58283467 / 125000000) ≤ -Real.log (25000000000 / 39850843061) ∧
    -Real.log (25000000000 / 39850843061) ≤ (466267737 / 1000000000) := by
  have h := checkLog_sound (w := (14850843061 / 64850843061)) (n := 12)
    (lo := (58283467 / 125000000)) (hi := (466267737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39850843061 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39850843061 / 25000000000) = 1/(25000000000 / 39850843061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7780 : Bounds (58283467 / 125000000) (466267737 / 1000000000) (Real.log (39850843061 / 25000000000)) := by
  have h := reflection_log_7780_neg
  have he : Real.log (39850843061 / 25000000000) = -Real.log (25000000000 / 39850843061) := by
    rw [show ((39850843061 / 25000000000) : ℝ) = ((25000000000 / 39850843061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7781_neg : (103303791 / 500000000) ≤ -Real.log (2000 / 2459) ∧
    -Real.log (2000 / 2459) ≤ (206607583 / 1000000000) := by
  have h := checkLog_sound (w := (459 / 4459)) (n := 12)
    (lo := (103303791 / 500000000)) (hi := (206607583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2459 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2459 / 2000) = 1/(2000 / 2459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7781 : Bounds (103303791 / 500000000) (206607583 / 1000000000) (Real.log (2459 / 2000)) := by
  have h := reflection_log_7781_neg
  have he : Real.log (2459 / 2000) = -Real.log (2000 / 2459) := by
    rw [show ((2459 / 2000) : ℝ) = ((2000 / 2459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7782_neg : (32589453 / 125000000) ≤ -Real.log (1541 / 2000) ∧
    -Real.log (1541 / 2000) ≤ (83429 / 320000) := by
  have h := checkLog_sound (w := (459 / 3541)) (n := 12)
    (lo := (32589453 / 125000000)) (hi := (83429 / 320000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1541) = 1/(1541 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7782 : Bounds (-83429 / 320000) (-32589453 / 125000000) (Real.log (1541 / 2000)) := by
  have h := reflection_log_7782_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7783_neg : (229473 / 1000000000) ≤ -Real.log (2000000 / 2000459) ∧
    -Real.log (2000000 / 2000459) ≤ (114737 / 500000000) := by
  have h := checkLog_sound (w := (459 / 4000459)) (n := 12)
    (lo := (229473 / 1000000000)) (hi := (114737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000459 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000459 / 2000000) = 1/(2000000 / 2000459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7783 : Bounds (229473 / 1000000000) (114737 / 500000000) (Real.log (2000459 / 2000000)) := by
  have h := reflection_log_7783_neg
  have he : Real.log (2000459 / 2000000) = -Real.log (2000000 / 2000459) := by
    rw [show ((2000459 / 2000000) : ℝ) = ((2000000 / 2000459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7784_neg : (114763 / 500000000) ≤ -Real.log (1999541 / 2000000) ∧
    -Real.log (1999541 / 2000000) ≤ (229527 / 1000000000) := by
  have h := checkLog_sound (w := (459 / 3999541)) (n := 12)
    (lo := (114763 / 500000000)) (hi := (229527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999541) = 1/(1999541 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7784 : Bounds (-229527 / 1000000000) (-114763 / 500000000) (Real.log (1999541 / 2000000)) := by
  have h := reflection_log_7784_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7785_neg : (13661273 / 125000000) ≤ -Real.log (500000 / 557743) ∧
    -Real.log (500000 / 557743) ≤ (21858037 / 200000000) := by
  have h := checkLog_sound (w := (57743 / 1057743)) (n := 12)
    (lo := (13661273 / 125000000)) (hi := (21858037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((557743 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(557743 / 500000) = 1/(500000 / 557743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7785 : Bounds (13661273 / 125000000) (21858037 / 200000000) (Real.log (557743 / 500000)) := by
  have h := reflection_log_7785_neg
  have he : Real.log (557743 / 500000) = -Real.log (500000 / 557743) := by
    rw [show ((557743 / 500000) : ℝ) = ((500000 / 557743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7786_neg : (122716937 / 1000000000) ≤ -Real.log (442257 / 500000) ∧
    -Real.log (442257 / 500000) ≤ (61358469 / 500000000) := by
  have h := checkLog_sound (w := (57743 / 942257)) (n := 12)
    (lo := (122716937 / 1000000000)) (hi := (61358469 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 442257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 442257) = 1/(442257 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7786 : Bounds (-61358469 / 500000000) (-122716937 / 1000000000) (Real.log (442257 / 500000)) := by
  have h := reflection_log_7786_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7787_neg : (109724877 / 1000000000) ≤ -Real.log (1000000 / 1115971) ∧
    -Real.log (1000000 / 1115971) ≤ (54862439 / 500000000) := by
  have h := checkLog_sound (w := (115971 / 2115971)) (n := 12)
    (lo := (109724877 / 1000000000)) (hi := (54862439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1115971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1115971 / 1000000) = 1/(1000000 / 1115971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7787 : Bounds (109724877 / 1000000000) (54862439 / 500000000) (Real.log (1115971 / 1000000)) := by
  have h := reflection_log_7787_neg
  have he : Real.log (1115971 / 1000000) = -Real.log (1000000 / 1115971) := by
    rw [show ((1115971 / 1000000) : ℝ) = ((1000000 / 1115971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7788_neg : (123265411 / 1000000000) ≤ -Real.log (884029 / 1000000) ∧
    -Real.log (884029 / 1000000) ≤ (30816353 / 250000000) := by
  have h := checkLog_sound (w := (115971 / 1884029)) (n := 12)
    (lo := (123265411 / 1000000000)) (hi := (30816353 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 884029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 884029) = 1/(884029 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7788 : Bounds (-30816353 / 250000000) (-123265411 / 1000000000) (Real.log (884029 / 1000000)) := by
  have h := reflection_log_7788_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7789_neg : (13540533 / 1000000000) ≤ -Real.log (986550727159 / 1000000000000) ∧
    -Real.log (986550727159 / 1000000000000) ≤ (6770267 / 500000000) := by
  have h := checkLog_sound (w := (13449272841 / 1986550727159)) (n := 12)
    (lo := (13540533 / 1000000000)) (hi := (6770267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986550727159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986550727159) = 1/(986550727159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7789 : Bounds (-6770267 / 500000000) (-13540533 / 1000000000) (Real.log (986550727159 / 1000000000000)) := by
  have h := reflection_log_7789_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7790_neg : (209793 / 15625000) ≤ -Real.log (246665745951 / 250000000000) ∧
    -Real.log (246665745951 / 250000000000) ≤ (13426753 / 1000000000) := by
  have h := checkLog_sound (w := (3334254049 / 496665745951)) (n := 12)
    (lo := (209793 / 15625000)) (hi := (13426753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246665745951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246665745951) = 1/(246665745951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7790 : Bounds (-13426753 / 1000000000) (-209793 / 15625000) (Real.log (246665745951 / 250000000000)) := by
  have h := reflection_log_7790_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7791_neg : (232007121 / 1000000000) ≤ -Real.log (250000000000 / 315282177557) ∧
    -Real.log (250000000000 / 315282177557) ≤ (116003561 / 500000000) := by
  have h := checkLog_sound (w := (65282177557 / 565282177557)) (n := 12)
    (lo := (232007121 / 1000000000)) (hi := (116003561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((315282177557 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(315282177557 / 250000000000) = 1/(250000000000 / 315282177557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7791 : Bounds (232007121 / 1000000000) (116003561 / 500000000) (Real.log (315282177557 / 250000000000)) := by
  have h := reflection_log_7791_neg
  have he : Real.log (315282177557 / 250000000000) = -Real.log (250000000000 / 315282177557) := by
    rw [show ((315282177557 / 250000000000) : ℝ) = ((250000000000 / 315282177557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7792_neg : (232990289 / 1000000000) ≤ -Real.log (25000000000 / 31559230523) ∧
    -Real.log (25000000000 / 31559230523) ≤ (23299029 / 100000000) := by
  have h := checkLog_sound (w := (6559230523 / 56559230523)) (n := 12)
    (lo := (232990289 / 1000000000)) (hi := (23299029 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31559230523 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31559230523 / 25000000000) = 1/(25000000000 / 31559230523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7792 : Bounds (232990289 / 1000000000) (23299029 / 100000000) (Real.log (31559230523 / 25000000000)) := by
  have h := reflection_log_7792_neg
  have he : Real.log (31559230523 / 25000000000) = -Real.log (25000000000 / 31559230523) := by
    rw [show ((31559230523 / 25000000000) : ℝ) = ((25000000000 / 31559230523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7793_neg : (58283467 / 125000000) ≤ -Real.log (500000000000 / 797016861219) ∧
    -Real.log (500000000000 / 797016861219) ≤ (466267737 / 1000000000) := by
  have h := checkLog_sound (w := (297016861219 / 1297016861219)) (n := 12)
    (lo := (58283467 / 125000000)) (hi := (466267737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((797016861219 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(797016861219 / 500000000000) = 1/(500000000000 / 797016861219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7793 : Bounds (58283467 / 125000000) (466267737 / 1000000000) (Real.log (797016861219 / 500000000000)) := by
  have h := reflection_log_7793_neg
  have he : Real.log (797016861219 / 500000000000) = -Real.log (500000000000 / 797016861219) := by
    rw [show ((797016861219 / 500000000000) : ℝ) = ((500000000000 / 797016861219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7794_neg : (233661603 / 500000000) ≤ -Real.log (25000000000 / 39892926671) ∧
    -Real.log (25000000000 / 39892926671) ≤ (467323207 / 1000000000) := by
  have h := checkLog_sound (w := (14892926671 / 64892926671)) (n := 12)
    (lo := (233661603 / 500000000)) (hi := (467323207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39892926671 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39892926671 / 25000000000) = 1/(25000000000 / 39892926671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7794 : Bounds (233661603 / 500000000) (467323207 / 1000000000) (Real.log (39892926671 / 25000000000)) := by
  have h := reflection_log_7794_neg
  have he : Real.log (39892926671 / 25000000000) = -Real.log (25000000000 / 39892926671) := by
    rw [show ((39892926671 / 25000000000) : ℝ) = ((25000000000 / 39892926671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7795_neg : (207014169 / 1000000000) ≤ -Real.log (100 / 123) ∧
    -Real.log (100 / 123) ≤ (20701417 / 100000000) := by
  have h := checkLog_sound (w := (23 / 223)) (n := 12)
    (lo := (207014169 / 1000000000)) (hi := (20701417 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123 / 100) = 1/(100 / 123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7795 : Bounds (207014169 / 1000000000) (20701417 / 100000000) (Real.log (123 / 100)) := by
  have h := reflection_log_7795_neg
  have he : Real.log (123 / 100) = -Real.log (100 / 123) := by
    rw [show ((123 / 100) : ℝ) = ((100 / 123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7796_neg : (65341191 / 250000000) ≤ -Real.log (77 / 100) ∧
    -Real.log (77 / 100) ≤ (52272953 / 200000000) := by
  have h := checkLog_sound (w := (23 / 177)) (n := 12)
    (lo := (65341191 / 250000000)) (hi := (52272953 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 77) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 77) = 1/(77 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7796 : Bounds (-52272953 / 200000000) (-65341191 / 250000000) (Real.log (77 / 100)) := by
  have h := reflection_log_7796_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7797_neg : (229973 / 1000000000) ≤ -Real.log (100000 / 100023) ∧
    -Real.log (100000 / 100023) ≤ (114987 / 500000000) := by
  have h := checkLog_sound (w := (23 / 200023)) (n := 12)
    (lo := (229973 / 1000000000)) (hi := (114987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100023 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100023 / 100000) = 1/(100000 / 100023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7797 : Bounds (229973 / 1000000000) (114987 / 500000000) (Real.log (100023 / 100000)) := by
  have h := reflection_log_7797_neg
  have he : Real.log (100023 / 100000) = -Real.log (100000 / 100023) := by
    rw [show ((100023 / 100000) : ℝ) = ((100000 / 100023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7798_neg : (115013 / 500000000) ≤ -Real.log (99977 / 100000) ∧
    -Real.log (99977 / 100000) ≤ (230027 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 199977)) (n := 12)
    (lo := (115013 / 500000000)) (hi := (230027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99977) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99977) = 1/(99977 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7798 : Bounds (-230027 / 1000000000) (-115013 / 500000000) (Real.log (99977 / 100000)) := by
  have h := reflection_log_7798_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7799_neg : (2190411 / 20000000) ≤ -Real.log (1000000 / 1115743) ∧
    -Real.log (1000000 / 1115743) ≤ (109520551 / 1000000000) := by
  have h := checkLog_sound (w := (115743 / 2115743)) (n := 12)
    (lo := (2190411 / 20000000)) (hi := (109520551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1115743 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1115743 / 1000000) = 1/(1000000 / 1115743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7799 : Bounds (2190411 / 20000000) (109520551 / 1000000000) (Real.log (1115743 / 1000000)) := by
  have h := reflection_log_7799_neg
  have he : Real.log (1115743 / 1000000) = -Real.log (1000000 / 1115743) := by
    rw [show ((1115743 / 1000000) : ℝ) = ((1000000 / 1115743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7800_neg : (61503767 / 500000000) ≤ -Real.log (884257 / 1000000) ∧
    -Real.log (884257 / 1000000) ≤ (24601507 / 200000000) := by
  have h := checkLog_sound (w := (115743 / 1884257)) (n := 12)
    (lo := (61503767 / 500000000)) (hi := (24601507 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 884257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 884257) = 1/(884257 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7800 : Bounds (-24601507 / 200000000) (-61503767 / 500000000) (Real.log (884257 / 1000000)) := by
  have h := reflection_log_7800_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7801_neg : (2748901 / 25000000) ≤ -Real.log (1000000 / 1116229) ∧
    -Real.log (1000000 / 1116229) ≤ (109956041 / 1000000000) := by
  have h := checkLog_sound (w := (116229 / 2116229)) (n := 12)
    (lo := (2748901 / 25000000)) (hi := (109956041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1116229 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1116229 / 1000000) = 1/(1000000 / 1116229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7801 : Bounds (2748901 / 25000000) (109956041 / 1000000000) (Real.log (1116229 / 1000000)) := by
  have h := reflection_log_7801_neg
  have he : Real.log (1116229 / 1000000) = -Real.log (1000000 / 1116229) := by
    rw [show ((1116229 / 1000000) : ℝ) = ((1000000 / 1116229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7802_neg : (123557299 / 1000000000) ≤ -Real.log (883771 / 1000000) ∧
    -Real.log (883771 / 1000000) ≤ (1235573 / 10000000) := by
  have h := checkLog_sound (w := (116229 / 1883771)) (n := 12)
    (lo := (123557299 / 1000000000)) (hi := (1235573 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 883771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 883771) = 1/(883771 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7802 : Bounds (-1235573 / 10000000) (-123557299 / 1000000000) (Real.log (883771 / 1000000)) := by
  have h := reflection_log_7802_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7803_neg : (13601259 / 1000000000) ≤ -Real.log (986490819559 / 1000000000000) ∧
    -Real.log (986490819559 / 1000000000000) ≤ (680063 / 50000000) := by
  have h := checkLog_sound (w := (13509180441 / 1986490819559)) (n := 12)
    (lo := (13601259 / 1000000000)) (hi := (680063 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986490819559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986490819559) = 1/(986490819559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7803 : Bounds (-680063 / 50000000) (-13601259 / 1000000000) (Real.log (986490819559 / 1000000000000)) := by
  have h := reflection_log_7803_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7804_neg : (13486983 / 1000000000) ≤ -Real.log (986603557951 / 1000000000000) ∧
    -Real.log (986603557951 / 1000000000000) ≤ (1685873 / 125000000) := by
  have h := checkLog_sound (w := (13396442049 / 1986603557951)) (n := 12)
    (lo := (13486983 / 1000000000)) (hi := (1685873 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986603557951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986603557951) = 1/(986603557951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7804 : Bounds (-1685873 / 125000000) (-13486983 / 1000000000) (Real.log (986603557951 / 1000000000000)) := by
  have h := reflection_log_7804_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7805_neg : (46505617 / 200000000) ≤ -Real.log (500000000000 / 630892941757) ∧
    -Real.log (500000000000 / 630892941757) ≤ (116264043 / 500000000) := by
  have h := checkLog_sound (w := (130892941757 / 1130892941757)) (n := 12)
    (lo := (46505617 / 200000000)) (hi := (116264043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630892941757 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(630892941757 / 500000000000) = 1/(500000000000 / 630892941757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7805 : Bounds (46505617 / 200000000) (116264043 / 500000000) (Real.log (630892941757 / 500000000000)) := by
  have h := reflection_log_7805_neg
  have he : Real.log (630892941757 / 500000000000) = -Real.log (500000000000 / 630892941757) := by
    rw [show ((630892941757 / 500000000000) : ℝ) = ((500000000000 / 630892941757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7806_neg : (233513339 / 1000000000) ≤ -Real.log (12500000000 / 15787870953) ∧
    -Real.log (12500000000 / 15787870953) ≤ (11675667 / 50000000) := by
  have h := checkLog_sound (w := (3287870953 / 28287870953)) (n := 12)
    (lo := (233513339 / 1000000000)) (hi := (11675667 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15787870953 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15787870953 / 12500000000) = 1/(12500000000 / 15787870953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7806 : Bounds (233513339 / 1000000000) (11675667 / 50000000) (Real.log (15787870953 / 12500000000)) := by
  have h := reflection_log_7806_neg
  have he : Real.log (15787870953 / 12500000000) = -Real.log (12500000000 / 15787870953) := by
    rw [show ((15787870953 / 12500000000) : ℝ) = ((12500000000 / 15787870953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7807_neg : (233661603 / 500000000) ≤ -Real.log (500000000000 / 797858533419) ∧
    -Real.log (500000000000 / 797858533419) ≤ (467323207 / 1000000000) := by
  have h := checkLog_sound (w := (297858533419 / 1297858533419)) (n := 12)
    (lo := (233661603 / 500000000)) (hi := (467323207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((797858533419 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(797858533419 / 500000000000) = 1/(500000000000 / 797858533419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7807 : Bounds (233661603 / 500000000) (467323207 / 1000000000) (Real.log (797858533419 / 500000000000)) := by
  have h := reflection_log_7807_neg
  have he : Real.log (797858533419 / 500000000000) = -Real.log (500000000000 / 797858533419) := by
    rw [show ((797858533419 / 500000000000) : ℝ) = ((500000000000 / 797858533419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0122 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7808_neg : (468378933 / 1000000000) ≤ -Real.log (250000000000 / 399350649351) ∧
    -Real.log (250000000000 / 399350649351) ≤ (234189467 / 500000000) := by
  have h := checkLog_sound (w := (149350649351 / 649350649351)) (n := 12)
    (lo := (468378933 / 1000000000)) (hi := (234189467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399350649351 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399350649351 / 250000000000) = 1/(250000000000 / 399350649351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7808 : Bounds (468378933 / 1000000000) (234189467 / 500000000) (Real.log (399350649351 / 250000000000)) := by
  have h := reflection_log_7808_neg
  have he : Real.log (399350649351 / 250000000000) = -Real.log (250000000000 / 399350649351) := by
    rw [show ((399350649351 / 250000000000) : ℝ) = ((250000000000 / 399350649351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7809_neg : (20742059 / 100000000) ≤ -Real.log (2000 / 2461) ∧
    -Real.log (2000 / 2461) ≤ (207420591 / 1000000000) := by
  have h := checkLog_sound (w := (461 / 4461)) (n := 12)
    (lo := (20742059 / 100000000)) (hi := (207420591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2461 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2461 / 2000) = 1/(2000 / 2461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7809 : Bounds (20742059 / 100000000) (207420591 / 1000000000) (Real.log (2461 / 2000)) := by
  have h := reflection_log_7809_neg
  have he : Real.log (2461 / 2000) = -Real.log (2000 / 2461) := by
    rw [show ((2461 / 2000) : ℝ) = ((2000 / 2461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7810_neg : (10480573 / 40000000) ≤ -Real.log (1539 / 2000) ∧
    -Real.log (1539 / 2000) ≤ (131007163 / 500000000) := by
  have h := checkLog_sound (w := (461 / 3539)) (n := 12)
    (lo := (10480573 / 40000000)) (hi := (131007163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1539) = 1/(1539 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7810 : Bounds (-131007163 / 500000000) (-10480573 / 40000000) (Real.log (1539 / 2000)) := by
  have h := reflection_log_7810_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7811_neg : (230473 / 1000000000) ≤ -Real.log (2000000 / 2000461) ∧
    -Real.log (2000000 / 2000461) ≤ (115237 / 500000000) := by
  have h := checkLog_sound (w := (461 / 4000461)) (n := 12)
    (lo := (230473 / 1000000000)) (hi := (115237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000461 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000461 / 2000000) = 1/(2000000 / 2000461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7811 : Bounds (230473 / 1000000000) (115237 / 500000000) (Real.log (2000461 / 2000000)) := by
  have h := reflection_log_7811_neg
  have he : Real.log (2000461 / 2000000) = -Real.log (2000000 / 2000461) := by
    rw [show ((2000461 / 2000000) : ℝ) = ((2000000 / 2000461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7812_neg : (115263 / 500000000) ≤ -Real.log (1999539 / 2000000) ∧
    -Real.log (1999539 / 2000000) ≤ (230527 / 1000000000) := by
  have h := checkLog_sound (w := (461 / 3999539)) (n := 12)
    (lo := (115263 / 500000000)) (hi := (230527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999539) = 1/(1999539 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7812 : Bounds (-230527 / 1000000000) (-115263 / 500000000) (Real.log (1999539 / 2000000)) := by
  have h := reflection_log_7812_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7813_neg : (109750863 / 1000000000) ≤ -Real.log (250 / 279) ∧
    -Real.log (250 / 279) ≤ (6859429 / 62500000) := by
  have h := checkLog_sound (w := (29 / 529)) (n := 12)
    (lo := (109750863 / 1000000000)) (hi := (6859429 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(279 / 250) = 1/(250 / 279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7813 : Bounds (109750863 / 1000000000) (6859429 / 62500000) (Real.log (279 / 250)) := by
  have h := reflection_log_7813_neg
  have he : Real.log (279 / 250) = -Real.log (250 / 279) := by
    rw [show ((279 / 250) : ℝ) = ((250 / 279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7814_neg : (15412277 / 125000000) ≤ -Real.log (221 / 250) ∧
    -Real.log (221 / 250) ≤ (123298217 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 471)) (n := 12)
    (lo := (15412277 / 125000000)) (hi := (123298217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 221) = 1/(221 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7814 : Bounds (-123298217 / 1000000000) (-15412277 / 125000000) (Real.log (221 / 250)) := by
  have h := reflection_log_7814_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7815_neg : (110186253 / 1000000000) ≤ -Real.log (500000 / 558243) ∧
    -Real.log (500000 / 558243) ≤ (55093127 / 500000000) := by
  have h := checkLog_sound (w := (58243 / 1058243)) (n := 12)
    (lo := (110186253 / 1000000000)) (hi := (55093127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((558243 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(558243 / 500000) = 1/(500000 / 558243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7815 : Bounds (110186253 / 1000000000) (55093127 / 500000000) (Real.log (558243 / 500000)) := by
  have h := reflection_log_7815_neg
  have he : Real.log (558243 / 500000) = -Real.log (500000 / 558243) := by
    rw [show ((558243 / 500000) : ℝ) = ((500000 / 558243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7816_neg : (123848141 / 1000000000) ≤ -Real.log (441757 / 500000) ∧
    -Real.log (441757 / 500000) ≤ (61924071 / 500000000) := by
  have h := checkLog_sound (w := (58243 / 941757)) (n := 12)
    (lo := (123848141 / 1000000000)) (hi := (61924071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 441757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 441757) = 1/(441757 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7816 : Bounds (-61924071 / 500000000) (-123848141 / 1000000000) (Real.log (441757 / 500000)) := by
  have h := reflection_log_7816_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7817_neg : (213467 / 15625000) ≤ -Real.log (246607752951 / 250000000000) ∧
    -Real.log (246607752951 / 250000000000) ≤ (13661889 / 1000000000) := by
  have h := checkLog_sound (w := (3392247049 / 496607752951)) (n := 12)
    (lo := (213467 / 15625000)) (hi := (13661889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246607752951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246607752951) = 1/(246607752951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7817 : Bounds (-13661889 / 1000000000) (-213467 / 15625000) (Real.log (246607752951 / 250000000000)) := by
  have h := reflection_log_7817_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7818_neg : (1693419 / 125000000) ≤ -Real.log (61659 / 62500) ∧
    -Real.log (61659 / 62500) ≤ (13547353 / 1000000000) := by
  have h := checkLog_sound (w := (841 / 124159)) (n := 12)
    (lo := (1693419 / 125000000)) (hi := (13547353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 61659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 61659) = 1/(61659 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7818 : Bounds (-13547353 / 1000000000) (-1693419 / 125000000) (Real.log (61659 / 62500)) := by
  have h := reflection_log_7818_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7819_neg : (5826227 / 25000000) ≤ -Real.log (500000000000 / 631221719457) ∧
    -Real.log (500000000000 / 631221719457) ≤ (233049081 / 1000000000) := by
  have h := checkLog_sound (w := (131221719457 / 1131221719457)) (n := 12)
    (lo := (5826227 / 25000000)) (hi := (233049081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((631221719457 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(631221719457 / 500000000000) = 1/(500000000000 / 631221719457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7819 : Bounds (5826227 / 25000000) (233049081 / 1000000000) (Real.log (631221719457 / 500000000000)) := by
  have h := reflection_log_7819_neg
  have he : Real.log (631221719457 / 500000000000) = -Real.log (500000000000 / 631221719457) := by
    rw [show ((631221719457 / 500000000000) : ℝ) = ((500000000000 / 631221719457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7820_neg : (117017197 / 500000000) ≤ -Real.log (125000000000 / 157960994393) ∧
    -Real.log (125000000000 / 157960994393) ≤ (46806879 / 200000000) := by
  have h := checkLog_sound (w := (32960994393 / 282960994393)) (n := 12)
    (lo := (117017197 / 500000000)) (hi := (46806879 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157960994393 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157960994393 / 125000000000) = 1/(125000000000 / 157960994393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7820 : Bounds (117017197 / 500000000) (46806879 / 200000000) (Real.log (157960994393 / 125000000000)) := by
  have h := reflection_log_7820_neg
  have he : Real.log (157960994393 / 125000000000) = -Real.log (125000000000 / 157960994393) := by
    rw [show ((157960994393 / 125000000000) : ℝ) = ((125000000000 / 157960994393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7821_neg : (468378933 / 1000000000) ≤ -Real.log (500000000000 / 798701298701) ∧
    -Real.log (500000000000 / 798701298701) ≤ (234189467 / 500000000) := by
  have h := checkLog_sound (w := (298701298701 / 1298701298701)) (n := 12)
    (lo := (468378933 / 1000000000)) (hi := (234189467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((798701298701 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(798701298701 / 500000000000) = 1/(500000000000 / 798701298701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7821 : Bounds (468378933 / 1000000000) (234189467 / 500000000) (Real.log (798701298701 / 500000000000)) := by
  have h := reflection_log_7821_neg
  have he : Real.log (798701298701 / 500000000000) = -Real.log (500000000000 / 798701298701) := by
    rw [show ((798701298701 / 500000000000) : ℝ) = ((500000000000 / 798701298701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7822_neg : (117358729 / 250000000) ≤ -Real.log (100000000000 / 159909031839) ∧
    -Real.log (100000000000 / 159909031839) ≤ (469434917 / 1000000000) := by
  have h := checkLog_sound (w := (59909031839 / 259909031839)) (n := 12)
    (lo := (117358729 / 250000000)) (hi := (469434917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159909031839 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159909031839 / 100000000000) = 1/(100000000000 / 159909031839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7822 : Bounds (117358729 / 250000000) (469434917 / 1000000000) (Real.log (159909031839 / 100000000000)) := by
  have h := reflection_log_7822_neg
  have he : Real.log (159909031839 / 100000000000) = -Real.log (100000000000 / 159909031839) := by
    rw [show ((159909031839 / 100000000000) : ℝ) = ((100000000000 / 159909031839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7823_neg : (207826847 / 1000000000) ≤ -Real.log (1000 / 1231) ∧
    -Real.log (1000 / 1231) ≤ (6494589 / 31250000) := by
  have h := checkLog_sound (w := (231 / 2231)) (n := 12)
    (lo := (207826847 / 1000000000)) (hi := (6494589 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1231 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1231 / 1000) = 1/(1000 / 1231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7823 : Bounds (207826847 / 1000000000) (6494589 / 31250000) (Real.log (1231 / 1000)) := by
  have h := reflection_log_7823_neg
  have he : Real.log (1231 / 1000) = -Real.log (1000 / 1231) := by
    rw [show ((1231 / 1000) : ℝ) = ((1000 / 1231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7824_neg : (262664309 / 1000000000) ≤ -Real.log (769 / 1000) ∧
    -Real.log (769 / 1000) ≤ (26266431 / 100000000) := by
  have h := checkLog_sound (w := (231 / 1769)) (n := 12)
    (lo := (262664309 / 1000000000)) (hi := (26266431 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 769) = 1/(769 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7824 : Bounds (-26266431 / 100000000) (-262664309 / 1000000000) (Real.log (769 / 1000)) := by
  have h := reflection_log_7824_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7825_neg : (230973 / 1000000000) ≤ -Real.log (1000000 / 1000231) ∧
    -Real.log (1000000 / 1000231) ≤ (115487 / 500000000) := by
  have h := checkLog_sound (w := (231 / 2000231)) (n := 12)
    (lo := (230973 / 1000000000)) (hi := (115487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000231 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000231 / 1000000) = 1/(1000000 / 1000231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7825 : Bounds (230973 / 1000000000) (115487 / 500000000) (Real.log (1000231 / 1000000)) := by
  have h := reflection_log_7825_neg
  have he : Real.log (1000231 / 1000000) = -Real.log (1000000 / 1000231) := by
    rw [show ((1000231 / 1000000) : ℝ) = ((1000000 / 1000231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7826_neg : (115513 / 500000000) ≤ -Real.log (999769 / 1000000) ∧
    -Real.log (999769 / 1000000) ≤ (231027 / 1000000000) := by
  have h := checkLog_sound (w := (231 / 1999769)) (n := 12)
    (lo := (115513 / 500000000)) (hi := (231027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999769) = 1/(999769 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7826 : Bounds (-231027 / 1000000000) (-115513 / 500000000) (Real.log (999769 / 1000000)) := by
  have h := reflection_log_7826_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7827_neg : (27495281 / 250000000) ≤ -Real.log (1000000 / 1116257) ∧
    -Real.log (1000000 / 1116257) ≤ (879849 / 8000000) := by
  have h := checkLog_sound (w := (116257 / 2116257)) (n := 12)
    (lo := (27495281 / 250000000)) (hi := (879849 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1116257 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1116257 / 1000000) = 1/(1000000 / 1116257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7827 : Bounds (27495281 / 250000000) (879849 / 8000000) (Real.log (1116257 / 1000000)) := by
  have h := reflection_log_7827_neg
  have he : Real.log (1116257 / 1000000) = -Real.log (1000000 / 1116257) := by
    rw [show ((1116257 / 1000000) : ℝ) = ((1000000 / 1116257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7828_neg : (61794491 / 500000000) ≤ -Real.log (883743 / 1000000) ∧
    -Real.log (883743 / 1000000) ≤ (123588983 / 1000000000) := by
  have h := checkLog_sound (w := (116257 / 1883743)) (n := 12)
    (lo := (61794491 / 500000000)) (hi := (123588983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 883743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 883743) = 1/(883743 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7828 : Bounds (-123588983 / 1000000000) (-61794491 / 500000000) (Real.log (883743 / 1000000)) := by
  have h := reflection_log_7828_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7829_neg : (27604327 / 250000000) ≤ -Real.log (125000 / 139593) ∧
    -Real.log (125000 / 139593) ≤ (110417309 / 1000000000) := by
  have h := checkLog_sound (w := (14593 / 264593)) (n := 12)
    (lo := (27604327 / 250000000)) (hi := (110417309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139593 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139593 / 125000) = 1/(125000 / 139593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7829 : Bounds (27604327 / 250000000) (110417309 / 1000000000) (Real.log (139593 / 125000)) := by
  have h := reflection_log_7829_neg
  have he : Real.log (139593 / 125000) = -Real.log (125000 / 139593) := by
    rw [show ((139593 / 125000) : ℝ) = ((125000 / 139593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7830_neg : (124140199 / 1000000000) ≤ -Real.log (110407 / 125000) ∧
    -Real.log (110407 / 125000) ≤ (620701 / 5000000) := by
  have h := checkLog_sound (w := (14593 / 235407)) (n := 12)
    (lo := (124140199 / 1000000000)) (hi := (620701 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 110407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 110407) = 1/(110407 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7830 : Bounds (-620701 / 5000000) (-124140199 / 1000000000) (Real.log (110407 / 125000)) := by
  have h := reflection_log_7830_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7831_neg : (13722891 / 1000000000) ≤ -Real.log (15412044351 / 15625000000) ∧
    -Real.log (15412044351 / 15625000000) ≤ (3430723 / 250000000) := by
  have h := checkLog_sound (w := (212955649 / 31037044351)) (n := 12)
    (lo := (13722891 / 1000000000)) (hi := (3430723 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15412044351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15412044351) = 1/(15412044351 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7831 : Bounds (-3430723 / 250000000) (-13722891 / 1000000000) (Real.log (15412044351 / 15625000000)) := by
  have h := reflection_log_7831_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7832_neg : (6803929 / 500000000) ≤ -Real.log (986484309951 / 1000000000000) ∧
    -Real.log (986484309951 / 1000000000000) ≤ (13607859 / 1000000000) := by
  have h := checkLog_sound (w := (13515690049 / 1986484309951)) (n := 12)
    (lo := (6803929 / 500000000)) (hi := (13607859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986484309951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986484309951) = 1/(986484309951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7832 : Bounds (-13607859 / 1000000000) (-6803929 / 500000000) (Real.log (986484309951 / 1000000000000)) := by
  have h := reflection_log_7832_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7833_neg : (116785053 / 500000000) ≤ -Real.log (250000000000 / 315775344189) ∧
    -Real.log (250000000000 / 315775344189) ≤ (233570107 / 1000000000) := by
  have h := checkLog_sound (w := (65775344189 / 565775344189)) (n := 12)
    (lo := (116785053 / 500000000)) (hi := (233570107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((315775344189 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(315775344189 / 250000000000) = 1/(250000000000 / 315775344189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7833 : Bounds (116785053 / 500000000) (233570107 / 1000000000) (Real.log (315775344189 / 250000000000)) := by
  have h := reflection_log_7833_neg
  have he : Real.log (315775344189 / 250000000000) = -Real.log (250000000000 / 315775344189) := by
    rw [show ((315775344189 / 250000000000) : ℝ) = ((250000000000 / 315775344189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7834_neg : (58639377 / 250000000) ≤ -Real.log (25000000000 / 31608729519) ∧
    -Real.log (25000000000 / 31608729519) ≤ (234557509 / 1000000000) := by
  have h := checkLog_sound (w := (6608729519 / 56608729519)) (n := 12)
    (lo := (58639377 / 250000000)) (hi := (234557509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31608729519 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31608729519 / 25000000000) = 1/(25000000000 / 31608729519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7834 : Bounds (58639377 / 250000000) (234557509 / 1000000000) (Real.log (31608729519 / 25000000000)) := by
  have h := reflection_log_7834_neg
  have he : Real.log (31608729519 / 25000000000) = -Real.log (25000000000 / 31608729519) := by
    rw [show ((31608729519 / 25000000000) : ℝ) = ((25000000000 / 31608729519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7835_neg : (117358729 / 250000000) ≤ -Real.log (250000000000 / 399772579597) ∧
    -Real.log (250000000000 / 399772579597) ≤ (469434917 / 1000000000) := by
  have h := checkLog_sound (w := (149772579597 / 649772579597)) (n := 12)
    (lo := (117358729 / 250000000)) (hi := (469434917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399772579597 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399772579597 / 250000000000) = 1/(250000000000 / 399772579597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7835 : Bounds (117358729 / 250000000) (469434917 / 1000000000) (Real.log (399772579597 / 250000000000)) := by
  have h := reflection_log_7835_neg
  have he : Real.log (399772579597 / 250000000000) = -Real.log (250000000000 / 399772579597) := by
    rw [show ((399772579597 / 250000000000) : ℝ) = ((250000000000 / 399772579597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7836_neg : (117622789 / 250000000) ≤ -Real.log (125000000000 / 200097529259) ∧
    -Real.log (125000000000 / 200097529259) ≤ (470491157 / 1000000000) := by
  have h := checkLog_sound (w := (75097529259 / 325097529259)) (n := 12)
    (lo := (117622789 / 250000000)) (hi := (470491157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200097529259 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200097529259 / 125000000000) = 1/(125000000000 / 200097529259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7836 : Bounds (117622789 / 250000000) (470491157 / 1000000000) (Real.log (200097529259 / 125000000000)) := by
  have h := reflection_log_7836_neg
  have he : Real.log (200097529259 / 125000000000) = -Real.log (125000000000 / 200097529259) := by
    rw [show ((200097529259 / 125000000000) : ℝ) = ((125000000000 / 200097529259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7837_neg : (104116469 / 500000000) ≤ -Real.log (2000 / 2463) ∧
    -Real.log (2000 / 2463) ≤ (208232939 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 4463)) (n := 12)
    (lo := (104116469 / 500000000)) (hi := (208232939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2463 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2463 / 2000) = 1/(2000 / 2463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7837 : Bounds (104116469 / 500000000) (208232939 / 1000000000) (Real.log (2463 / 2000)) := by
  have h := reflection_log_7837_neg
  have he : Real.log (2463 / 2000) = -Real.log (2000 / 2463) := by
    rw [show ((2463 / 2000) : ℝ) = ((2000 / 2463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7838_neg : (65828679 / 250000000) ≤ -Real.log (1537 / 2000) ∧
    -Real.log (1537 / 2000) ≤ (263314717 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 3537)) (n := 12)
    (lo := (65828679 / 250000000)) (hi := (263314717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1537) = 1/(1537 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7838 : Bounds (-263314717 / 1000000000) (-65828679 / 250000000) (Real.log (1537 / 2000)) := by
  have h := reflection_log_7838_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7839_neg : (231473 / 1000000000) ≤ -Real.log (2000000 / 2000463) ∧
    -Real.log (2000000 / 2000463) ≤ (115737 / 500000000) := by
  have h := checkLog_sound (w := (463 / 4000463)) (n := 12)
    (lo := (231473 / 1000000000)) (hi := (115737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000463 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000463 / 2000000) = 1/(2000000 / 2000463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7839 : Bounds (231473 / 1000000000) (115737 / 500000000) (Real.log (2000463 / 2000000)) := by
  have h := reflection_log_7839_neg
  have he : Real.log (2000463 / 2000000) = -Real.log (2000000 / 2000463) := by
    rw [show ((2000463 / 2000000) : ℝ) = ((2000000 / 2000463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7840_neg : (115763 / 500000000) ≤ -Real.log (1999537 / 2000000) ∧
    -Real.log (1999537 / 2000000) ≤ (231527 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 3999537)) (n := 12)
    (lo := (115763 / 500000000)) (hi := (231527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999537) = 1/(1999537 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7840 : Bounds (-231527 / 1000000000) (-115763 / 500000000) (Real.log (1999537 / 2000000)) := by
  have h := reflection_log_7840_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7841_neg : (110211331 / 1000000000) ≤ -Real.log (500000 / 558257) ∧
    -Real.log (500000 / 558257) ≤ (27552833 / 250000000) := by
  have h := checkLog_sound (w := (58257 / 1058257)) (n := 12)
    (lo := (110211331 / 1000000000)) (hi := (27552833 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((558257 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(558257 / 500000) = 1/(500000 / 558257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7841 : Bounds (110211331 / 1000000000) (27552833 / 250000000) (Real.log (558257 / 500000)) := by
  have h := reflection_log_7841_neg
  have he : Real.log (558257 / 500000) = -Real.log (500000 / 558257) := by
    rw [show ((558257 / 500000) : ℝ) = ((500000 / 558257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7842_neg : (123879833 / 1000000000) ≤ -Real.log (441743 / 500000) ∧
    -Real.log (441743 / 500000) ≤ (61939917 / 500000000) := by
  have h := checkLog_sound (w := (58257 / 941743)) (n := 12)
    (lo := (123879833 / 1000000000)) (hi := (61939917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 441743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 441743) = 1/(441743 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7842 : Bounds (-61939917 / 500000000) (-123879833 / 1000000000) (Real.log (441743 / 500000)) := by
  have h := reflection_log_7842_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7843_neg : (11064831 / 100000000) ≤ -Real.log (500000 / 558501) ∧
    -Real.log (500000 / 558501) ≤ (110648311 / 1000000000) := by
  have h := checkLog_sound (w := (58501 / 1058501)) (n := 12)
    (lo := (11064831 / 100000000)) (hi := (110648311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((558501 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(558501 / 500000) = 1/(500000 / 558501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7843 : Bounds (11064831 / 100000000) (110648311 / 1000000000) (Real.log (558501 / 500000)) := by
  have h := reflection_log_7843_neg
  have he : Real.log (558501 / 500000) = -Real.log (500000 / 558501) := by
    rw [show ((558501 / 500000) : ℝ) = ((500000 / 558501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7844_neg : (124432343 / 1000000000) ≤ -Real.log (441499 / 500000) ∧
    -Real.log (441499 / 500000) ≤ (15554043 / 125000000) := by
  have h := checkLog_sound (w := (58501 / 941499)) (n := 12)
    (lo := (124432343 / 1000000000)) (hi := (15554043 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 441499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 441499) = 1/(441499 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7844 : Bounds (-15554043 / 125000000) (-124432343 / 1000000000) (Real.log (441499 / 500000)) := by
  have h := reflection_log_7844_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7845_neg : (430751 / 31250000) ≤ -Real.log (246577632999 / 250000000000) ∧
    -Real.log (246577632999 / 250000000000) ≤ (13784033 / 1000000000) := by
  have h := checkLog_sound (w := (3422367001 / 496577632999)) (n := 12)
    (lo := (430751 / 31250000)) (hi := (13784033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246577632999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246577632999) = 1/(246577632999 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7845 : Bounds (-13784033 / 1000000000) (-430751 / 31250000) (Real.log (246577632999 / 250000000000)) := by
  have h := reflection_log_7845_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7846_neg : (6834251 / 500000000) ≤ -Real.log (246606121951 / 250000000000) ∧
    -Real.log (246606121951 / 250000000000) ≤ (13668503 / 1000000000) := by
  have h := checkLog_sound (w := (3393878049 / 496606121951)) (n := 12)
    (lo := (6834251 / 500000000)) (hi := (13668503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246606121951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246606121951) = 1/(246606121951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7846 : Bounds (-13668503 / 1000000000) (-6834251 / 500000000) (Real.log (246606121951 / 250000000000)) := by
  have h := reflection_log_7846_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7847_neg : (58522791 / 250000000) ≤ -Real.log (50000000000 / 63187984869) ∧
    -Real.log (50000000000 / 63187984869) ≤ (46818233 / 200000000) := by
  have h := checkLog_sound (w := (13187984869 / 113187984869)) (n := 12)
    (lo := (58522791 / 250000000)) (hi := (46818233 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63187984869 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63187984869 / 50000000000) = 1/(50000000000 / 63187984869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7847 : Bounds (58522791 / 250000000) (46818233 / 200000000) (Real.log (63187984869 / 50000000000)) := by
  have h := reflection_log_7847_neg
  have he : Real.log (63187984869 / 50000000000) = -Real.log (50000000000 / 63187984869) := by
    rw [show ((63187984869 / 50000000000) : ℝ) = ((50000000000 / 63187984869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7848_neg : (235080653 / 1000000000) ≤ -Real.log (500000000000 / 632505396389) ∧
    -Real.log (500000000000 / 632505396389) ≤ (117540327 / 500000000) := by
  have h := checkLog_sound (w := (132505396389 / 1132505396389)) (n := 12)
    (lo := (235080653 / 1000000000)) (hi := (117540327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((632505396389 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(632505396389 / 500000000000) = 1/(500000000000 / 632505396389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7848 : Bounds (235080653 / 1000000000) (117540327 / 500000000) (Real.log (632505396389 / 500000000000)) := by
  have h := reflection_log_7848_neg
  have he : Real.log (632505396389 / 500000000000) = -Real.log (500000000000 / 632505396389) := by
    rw [show ((632505396389 / 500000000000) : ℝ) = ((500000000000 / 632505396389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7849_neg : (117622789 / 250000000) ≤ -Real.log (100000000000 / 160078023407) ∧
    -Real.log (100000000000 / 160078023407) ≤ (470491157 / 1000000000) := by
  have h := checkLog_sound (w := (60078023407 / 260078023407)) (n := 12)
    (lo := (117622789 / 250000000)) (hi := (470491157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160078023407 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160078023407 / 100000000000) = 1/(100000000000 / 160078023407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7849 : Bounds (117622789 / 250000000) (470491157 / 1000000000) (Real.log (160078023407 / 100000000000)) := by
  have h := reflection_log_7849_neg
  have he : Real.log (160078023407 / 100000000000) = -Real.log (100000000000 / 160078023407) := by
    rw [show ((160078023407 / 100000000000) : ℝ) = ((100000000000 / 160078023407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7850_neg : (235773827 / 500000000) ≤ -Real.log (250000000000 / 400618087183) ∧
    -Real.log (250000000000 / 400618087183) ≤ (94309531 / 200000000) := by
  have h := checkLog_sound (w := (150618087183 / 650618087183)) (n := 12)
    (lo := (235773827 / 500000000)) (hi := (94309531 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400618087183 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400618087183 / 250000000000) = 1/(250000000000 / 400618087183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7850 : Bounds (235773827 / 500000000) (94309531 / 200000000) (Real.log (400618087183 / 250000000000)) := by
  have h := reflection_log_7850_neg
  have he : Real.log (400618087183 / 250000000000) = -Real.log (250000000000 / 400618087183) := by
    rw [show ((400618087183 / 250000000000) : ℝ) = ((250000000000 / 400618087183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7851_neg : (41727773 / 200000000) ≤ -Real.log (125 / 154) ∧
    -Real.log (125 / 154) ≤ (104319433 / 500000000) := by
  have h := checkLog_sound (w := (29 / 279)) (n := 12)
    (lo := (41727773 / 200000000)) (hi := (104319433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154 / 125) = 1/(125 / 154) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7851 : Bounds (41727773 / 200000000) (104319433 / 500000000) (Real.log (154 / 125)) := by
  have h := reflection_log_7851_neg
  have he : Real.log (154 / 125) = -Real.log (125 / 154) := by
    rw [show ((154 / 125) : ℝ) = ((125 / 154) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7852_neg : (52793109 / 200000000) ≤ -Real.log (96 / 125) ∧
    -Real.log (96 / 125) ≤ (131982773 / 500000000) := by
  have h := checkLog_sound (w := (29 / 221)) (n := 12)
    (lo := (52793109 / 200000000)) (hi := (131982773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 96) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 96) = 1/(96 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7852 : Bounds (-131982773 / 500000000) (-52793109 / 200000000) (Real.log (96 / 125)) := by
  have h := reflection_log_7852_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7853_neg : (231973 / 1000000000) ≤ -Real.log (125000 / 125029) ∧
    -Real.log (125000 / 125029) ≤ (115987 / 500000000) := by
  have h := checkLog_sound (w := (29 / 250029)) (n := 12)
    (lo := (231973 / 1000000000)) (hi := (115987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125029 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125029 / 125000) = 1/(125000 / 125029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7853 : Bounds (231973 / 1000000000) (115987 / 500000000) (Real.log (125029 / 125000)) := by
  have h := reflection_log_7853_neg
  have he : Real.log (125029 / 125000) = -Real.log (125000 / 125029) := by
    rw [show ((125029 / 125000) : ℝ) = ((125000 / 125029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7854_neg : (116013 / 500000000) ≤ -Real.log (124971 / 125000) ∧
    -Real.log (124971 / 125000) ≤ (232027 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 249971)) (n := 12)
    (lo := (116013 / 500000000)) (hi := (232027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124971) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124971) = 1/(124971 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7854 : Bounds (-232027 / 1000000000) (-116013 / 500000000) (Real.log (124971 / 125000)) := by
  have h := reflection_log_7854_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7855_neg : (22088297 / 200000000) ≤ -Real.log (1000000 / 1116771) ∧
    -Real.log (1000000 / 1116771) ≤ (55220743 / 500000000) := by
  have h := checkLog_sound (w := (116771 / 2116771)) (n := 12)
    (lo := (22088297 / 200000000)) (hi := (55220743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1116771 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1116771 / 1000000) = 1/(1000000 / 1116771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7855 : Bounds (22088297 / 200000000) (55220743 / 500000000) (Real.log (1116771 / 1000000)) := by
  have h := reflection_log_7855_neg
  have he : Real.log (1116771 / 1000000) = -Real.log (1000000 / 1116771) := by
    rw [show ((1116771 / 1000000) : ℝ) = ((1000000 / 1116771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7856_neg : (7760673 / 62500000) ≤ -Real.log (883229 / 1000000) ∧
    -Real.log (883229 / 1000000) ≤ (124170769 / 1000000000) := by
  have h := checkLog_sound (w := (116771 / 1883229)) (n := 12)
    (lo := (7760673 / 62500000)) (hi := (124170769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 883229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 883229) = 1/(883229 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7856 : Bounds (-124170769 / 1000000000) (-7760673 / 62500000) (Real.log (883229 / 1000000)) := by
  have h := reflection_log_7856_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7857_neg : (27719591 / 250000000) ≤ -Real.log (1000000 / 1117259) ∧
    -Real.log (1000000 / 1117259) ≤ (22175673 / 200000000) := by
  have h := checkLog_sound (w := (117259 / 2117259)) (n := 12)
    (lo := (27719591 / 250000000)) (hi := (22175673 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1117259 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1117259 / 1000000) = 1/(1000000 / 1117259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7857 : Bounds (27719591 / 250000000) (22175673 / 200000000) (Real.log (1117259 / 1000000)) := by
  have h := reflection_log_7857_neg
  have he : Real.log (1117259 / 1000000) = -Real.log (1000000 / 1117259) := by
    rw [show ((1117259 / 1000000) : ℝ) = ((1000000 / 1117259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7858_neg : (124723439 / 1000000000) ≤ -Real.log (882741 / 1000000) ∧
    -Real.log (882741 / 1000000) ≤ (1559043 / 12500000) := by
  have h := checkLog_sound (w := (117259 / 1882741)) (n := 12)
    (lo := (124723439 / 1000000000)) (hi := (1559043 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 882741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 882741) = 1/(882741 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7858 : Bounds (-1559043 / 12500000) (-124723439 / 1000000000) (Real.log (882741 / 1000000)) := by
  have h := reflection_log_7858_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7859_neg : (553803 / 40000000) ≤ -Real.log (986250326919 / 1000000000000) ∧
    -Real.log (986250326919 / 1000000000000) ≤ (3461269 / 250000000) := by
  have h := checkLog_sound (w := (13749673081 / 1986250326919)) (n := 12)
    (lo := (553803 / 40000000)) (hi := (3461269 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986250326919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986250326919) = 1/(986250326919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7859 : Bounds (-3461269 / 250000000) (-553803 / 40000000) (Real.log (986250326919 / 1000000000000)) := by
  have h := reflection_log_7859_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7860_neg : (13729283 / 1000000000) ≤ -Real.log (986364533559 / 1000000000000) ∧
    -Real.log (986364533559 / 1000000000000) ≤ (3432321 / 250000000) := by
  have h := checkLog_sound (w := (13635466441 / 1986364533559)) (n := 12)
    (lo := (13729283 / 1000000000)) (hi := (3432321 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986364533559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986364533559) = 1/(986364533559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7860 : Bounds (-3432321 / 250000000) (-13729283 / 1000000000) (Real.log (986364533559 / 1000000000000)) := by
  have h := reflection_log_7860_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7861_neg : (117306127 / 500000000) ≤ -Real.log (250000000000 / 316104600279) ∧
    -Real.log (250000000000 / 316104600279) ≤ (46922451 / 200000000) := by
  have h := checkLog_sound (w := (66104600279 / 566104600279)) (n := 12)
    (lo := (117306127 / 500000000)) (hi := (46922451 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((316104600279 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(316104600279 / 250000000000) = 1/(250000000000 / 316104600279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7861 : Bounds (117306127 / 500000000) (46922451 / 200000000) (Real.log (316104600279 / 250000000000)) := by
  have h := reflection_log_7861_neg
  have he : Real.log (316104600279 / 250000000000) = -Real.log (250000000000 / 316104600279) := by
    rw [show ((316104600279 / 250000000000) : ℝ) = ((250000000000 / 316104600279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7862_neg : (235601803 / 1000000000) ≤ -Real.log (500000000000 / 632835112451) ∧
    -Real.log (500000000000 / 632835112451) ≤ (58900451 / 250000000) := by
  have h := checkLog_sound (w := (132835112451 / 1132835112451)) (n := 12)
    (lo := (235601803 / 1000000000)) (hi := (58900451 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((632835112451 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(632835112451 / 500000000000) = 1/(500000000000 / 632835112451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7862 : Bounds (235601803 / 1000000000) (58900451 / 250000000) (Real.log (632835112451 / 500000000000)) := by
  have h := reflection_log_7862_neg
  have he : Real.log (632835112451 / 500000000000) = -Real.log (500000000000 / 632835112451) := by
    rw [show ((632835112451 / 500000000000) : ℝ) = ((500000000000 / 632835112451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7863_neg : (235773827 / 500000000) ≤ -Real.log (100000000000 / 160247234873) ∧
    -Real.log (100000000000 / 160247234873) ≤ (94309531 / 200000000) := by
  have h := checkLog_sound (w := (60247234873 / 260247234873)) (n := 12)
    (lo := (235773827 / 500000000)) (hi := (94309531 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160247234873 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160247234873 / 100000000000) = 1/(100000000000 / 160247234873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7863 : Bounds (235773827 / 500000000) (94309531 / 200000000) (Real.log (160247234873 / 100000000000)) := by
  have h := reflection_log_7863_neg
  have he : Real.log (160247234873 / 100000000000) = -Real.log (100000000000 / 160247234873) := by
    rw [show ((160247234873 / 100000000000) : ℝ) = ((100000000000 / 160247234873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7864_neg : (47260441 / 100000000) ≤ -Real.log (250000000000 / 401041666667) ∧
    -Real.log (250000000000 / 401041666667) ≤ (472604411 / 1000000000) := by
  have h := checkLog_sound (w := (151041666667 / 651041666667)) (n := 12)
    (lo := (47260441 / 100000000)) (hi := (472604411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((401041666667 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(401041666667 / 250000000000) = 1/(250000000000 / 401041666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7864 : Bounds (47260441 / 100000000) (472604411 / 1000000000) (Real.log (401041666667 / 250000000000)) := by
  have h := reflection_log_7864_neg
  have he : Real.log (401041666667 / 250000000000) = -Real.log (250000000000 / 401041666667) := by
    rw [show ((401041666667 / 250000000000) : ℝ) = ((250000000000 / 401041666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7865_neg : (104522313 / 500000000) ≤ -Real.log (400 / 493) ∧
    -Real.log (400 / 493) ≤ (209044627 / 1000000000) := by
  have h := checkLog_sound (w := (93 / 893)) (n := 12)
    (lo := (104522313 / 500000000)) (hi := (209044627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493 / 400) = 1/(400 / 493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7865 : Bounds (104522313 / 500000000) (209044627 / 1000000000) (Real.log (493 / 400)) := by
  have h := reflection_log_7865_neg
  have he : Real.log (493 / 400) = -Real.log (400 / 493) := by
    rw [show ((493 / 400) : ℝ) = ((400 / 493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7866_neg : (264616799 / 1000000000) ≤ -Real.log (307 / 400) ∧
    -Real.log (307 / 400) ≤ (330771 / 1250000) := by
  have h := checkLog_sound (w := (93 / 707)) (n := 12)
    (lo := (264616799 / 1000000000)) (hi := (330771 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 307) = 1/(307 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7866 : Bounds (-330771 / 1250000) (-264616799 / 1000000000) (Real.log (307 / 400)) := by
  have h := reflection_log_7866_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7867_neg : (29059 / 125000000) ≤ -Real.log (400000 / 400093) ∧
    -Real.log (400000 / 400093) ≤ (232473 / 1000000000) := by
  have h := checkLog_sound (w := (93 / 800093)) (n := 12)
    (lo := (29059 / 125000000)) (hi := (232473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400093 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400093 / 400000) = 1/(400000 / 400093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7867 : Bounds (29059 / 125000000) (232473 / 1000000000) (Real.log (400093 / 400000)) := by
  have h := reflection_log_7867_neg
  have he : Real.log (400093 / 400000) = -Real.log (400000 / 400093) := by
    rw [show ((400093 / 400000) : ℝ) = ((400000 / 400093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7868_neg : (232527 / 1000000000) ≤ -Real.log (399907 / 400000) ∧
    -Real.log (399907 / 400000) ≤ (14533 / 62500000) := by
  have h := checkLog_sound (w := (93 / 799907)) (n := 12)
    (lo := (232527 / 1000000000)) (hi := (14533 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399907) = 1/(399907 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7868 : Bounds (-14533 / 62500000) (-232527 / 1000000000) (Real.log (399907 / 400000)) := by
  have h := reflection_log_7868_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7869_neg : (55336241 / 500000000) ≤ -Real.log (1000000 / 1117029) ∧
    -Real.log (1000000 / 1117029) ≤ (110672483 / 1000000000) := by
  have h := checkLog_sound (w := (117029 / 2117029)) (n := 12)
    (lo := (55336241 / 500000000)) (hi := (110672483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1117029 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1117029 / 1000000) = 1/(1000000 / 1117029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7869 : Bounds (55336241 / 500000000) (110672483 / 1000000000) (Real.log (1117029 / 1000000)) := by
  have h := reflection_log_7869_neg
  have he : Real.log (1117029 / 1000000) = -Real.log (1000000 / 1117029) := by
    rw [show ((1117029 / 1000000) : ℝ) = ((1000000 / 1117029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7870_neg : (124462921 / 1000000000) ≤ -Real.log (882971 / 1000000) ∧
    -Real.log (882971 / 1000000) ≤ (62231461 / 500000000) := by
  have h := checkLog_sound (w := (117029 / 1882971)) (n := 12)
    (lo := (124462921 / 1000000000)) (hi := (62231461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 882971) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 882971) = 1/(882971 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7870 : Bounds (-62231461 / 500000000) (-124462921 / 1000000000) (Real.log (882971 / 1000000)) := by
  have h := reflection_log_7870_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7871_neg : (111109259 / 1000000000) ≤ -Real.log (1000000 / 1117517) ∧
    -Real.log (1000000 / 1117517) ≤ (5555463 / 50000000) := by
  have h := checkLog_sound (w := (117517 / 2117517)) (n := 12)
    (lo := (111109259 / 1000000000)) (hi := (5555463 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1117517 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1117517 / 1000000) = 1/(1000000 / 1117517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7871 : Bounds (111109259 / 1000000000) (5555463 / 50000000) (Real.log (1117517 / 1000000)) := by
  have h := reflection_log_7871_neg
  have he : Real.log (1117517 / 1000000) = -Real.log (1000000 / 1117517) := by
    rw [show ((1117517 / 1000000) : ℝ) = ((1000000 / 1117517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


