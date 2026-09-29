-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0184__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0184__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T01:46:25.390903+00:00
-- url     : https://prove2.me/theorems/973cc00b-3f8c-4bf2-9247-01049e71dab4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0184 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0185, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0184 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0185, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0186)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0184 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0185, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0186)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0184 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0185, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0186) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0184 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0185, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0186).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0184 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11776_neg : (261593361 / 1000000000) ≤ -Real.log (24057 / 31250) ∧
    -Real.log (24057 / 31250) ≤ (130796681 / 500000000) := by
  have h := checkLog_sound (w := (7193 / 55307)) (n := 12)
    (lo := (261593361 / 1000000000)) (hi := (130796681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 24057) = 1/(24057 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11776 : Bounds (-130796681 / 500000000) (-261593361 / 1000000000) (Real.log (24057 / 31250)) := by
  have h := reflection_log_11776_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11777_neg : (207959251 / 1000000000) ≤ -Real.log (1000000 / 1231163) ∧
    -Real.log (1000000 / 1231163) ≤ (51989813 / 250000000) := by
  have h := checkLog_sound (w := (231163 / 2231163)) (n := 12)
    (lo := (207959251 / 1000000000)) (hi := (51989813 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1231163 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1231163 / 1000000) = 1/(1000000 / 1231163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11777 : Bounds (207959251 / 1000000000) (51989813 / 250000000) (Real.log (1231163 / 1000000)) := by
  have h := reflection_log_11777_neg
  have he : Real.log (1231163 / 1000000) = -Real.log (1000000 / 1231163) := by
    rw [show ((1231163 / 1000000) : ℝ) = ((1000000 / 1231163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11778_neg : (52575259 / 200000000) ≤ -Real.log (768837 / 1000000) ∧
    -Real.log (768837 / 1000000) ≤ (32859537 / 125000000) := by
  have h := checkLog_sound (w := (231163 / 1768837)) (n := 12)
    (lo := (52575259 / 200000000)) (hi := (32859537 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 768837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 768837) = 1/(768837 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11778 : Bounds (-32859537 / 125000000) (-52575259 / 200000000) (Real.log (768837 / 1000000)) := by
  have h := reflection_log_11778_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11779_neg : (13729261 / 250000000) ≤ -Real.log (946563667431 / 1000000000000) ∧
    -Real.log (946563667431 / 1000000000000) ≤ (10983409 / 200000000) := by
  have h := checkLog_sound (w := (53436332569 / 1946563667431)) (n := 12)
    (lo := (13729261 / 250000000)) (hi := (10983409 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 946563667431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 946563667431) = 1/(946563667431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11779 : Bounds (-10983409 / 200000000) (-13729261 / 250000000) (Real.log (946563667431 / 1000000000000)) := by
  have h := reflection_log_11779_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11780_neg : (54436113 / 1000000000) ≤ -Real.log (924823251 / 976562500) ∧
    -Real.log (924823251 / 976562500) ≤ (27218057 / 500000000) := by
  have h := checkLog_sound (w := (51739249 / 1901385751)) (n := 12)
    (lo := (54436113 / 1000000000)) (hi := (27218057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 924823251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 924823251) = 1/(924823251 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11780 : Bounds (-27218057 / 500000000) (-54436113 / 1000000000) (Real.log (924823251 / 976562500)) := by
  have h := reflection_log_11780_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11781_neg : (46875061 / 100000000) ≤ -Real.log (250000000000 / 399499106289) ∧
    -Real.log (250000000000 / 399499106289) ≤ (468750611 / 1000000000) := by
  have h := checkLog_sound (w := (149499106289 / 649499106289)) (n := 12)
    (lo := (46875061 / 100000000)) (hi := (468750611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399499106289 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399499106289 / 250000000000) = 1/(250000000000 / 399499106289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11781 : Bounds (46875061 / 100000000) (468750611 / 1000000000) (Real.log (399499106289 / 250000000000)) := by
  have h := reflection_log_11781_neg
  have he : Real.log (399499106289 / 250000000000) = -Real.log (250000000000 / 399499106289) := by
    rw [show ((399499106289 / 250000000000) : ℝ) = ((250000000000 / 399499106289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11782_neg : (235417773 / 500000000) ≤ -Real.log (500000000000 / 800665810829) ∧
    -Real.log (500000000000 / 800665810829) ≤ (470835547 / 1000000000) := by
  have h := checkLog_sound (w := (300665810829 / 1300665810829)) (n := 12)
    (lo := (235417773 / 500000000)) (hi := (470835547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800665810829 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800665810829 / 500000000000) = 1/(500000000000 / 800665810829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11782 : Bounds (235417773 / 500000000) (470835547 / 1000000000) (Real.log (800665810829 / 500000000000)) := by
  have h := reflection_log_11782_neg
  have he : Real.log (800665810829 / 500000000000) = -Real.log (500000000000 / 800665810829) := by
    rw [show ((800665810829 / 500000000000) : ℝ) = ((500000000000 / 800665810829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11783_neg : (119300503 / 125000000) ≤ -Real.log (500000000000 / 1298561151079) ∧
    -Real.log (500000000000 / 1298561151079) ≤ (477202013 / 500000000) := by
  have h := checkLog_sound (w := (298561151079 / 2298561151079)) (n := 12)
    (lo := (65314211 / 250000000)) (hi := (52251369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1298561151079 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1298561151079 / 1000000000000) = 1/(500000000000 / 1298561151079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11783 : Bounds (119300503 / 125000000) (477202013 / 500000000) (Real.log (1298561151079 / 500000000000)) := by
  have h := reflection_log_11783_neg
  have he : Real.log (1298561151079 / 500000000000) = -Real.log (500000000000 / 1298561151079) := by
    rw [show ((1298561151079 / 500000000000) : ℝ) = ((500000000000 / 1298561151079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11784_neg : (478448243 / 500000000) ≤ -Real.log (250000000000 / 650900900901) ∧
    -Real.log (250000000000 / 650900900901) ≤ (119612061 / 125000000) := by
  have h := checkLog_sound (w := (150900900901 / 1150900900901)) (n := 12)
    (lo := (131874653 / 500000000)) (hi := (263749307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((650900900901 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(650900900901 / 500000000000) = 1/(250000000000 / 650900900901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11784 : Bounds (478448243 / 500000000) (119612061 / 125000000) (Real.log (650900900901 / 250000000000)) := by
  have h := reflection_log_11784_neg
  have he : Real.log (650900900901 / 250000000000) = -Real.log (250000000000 / 650900900901) := by
    rw [show ((650900900901 / 250000000000) : ℝ) = ((250000000000 / 650900900901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11785_neg : (368801123 / 1000000000) ≤ -Real.log (500 / 723) ∧
    -Real.log (500 / 723) ≤ (92200281 / 250000000) := by
  have h := checkLog_sound (w := (223 / 1223)) (n := 12)
    (lo := (368801123 / 1000000000)) (hi := (92200281 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((723 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(723 / 500) = 1/(500 / 723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11785 : Bounds (368801123 / 1000000000) (92200281 / 250000000) (Real.log (723 / 500)) := by
  have h := reflection_log_11785_neg
  have he : Real.log (723 / 500) = -Real.log (500 / 723) := by
    rw [show ((723 / 500) : ℝ) = ((500 / 723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11786_neg : (4613989 / 7812500) ≤ -Real.log (277 / 500) ∧
    -Real.log (277 / 500) ≤ (590590593 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 777)) (n := 12)
    (lo := (4613989 / 7812500)) (hi := (590590593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 277) = 1/(277 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11786 : Bounds (-590590593 / 1000000000) (-4613989 / 7812500) (Real.log (277 / 500)) := by
  have h := reflection_log_11786_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11787_neg : (4459 / 10000000) ≤ -Real.log (500000 / 500223) ∧
    -Real.log (500000 / 500223) ≤ (445901 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 1000223)) (n := 12)
    (lo := (4459 / 10000000)) (hi := (445901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500223 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500223 / 500000) = 1/(500000 / 500223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11787 : Bounds (4459 / 10000000) (445901 / 1000000000) (Real.log (500223 / 500000)) := by
  have h := reflection_log_11787_neg
  have he : Real.log (500223 / 500000) = -Real.log (500000 / 500223) := by
    rw [show ((500223 / 500000) : ℝ) = ((500000 / 500223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11788_neg : (446099 / 1000000000) ≤ -Real.log (499777 / 500000) ∧
    -Real.log (499777 / 500000) ≤ (4461 / 10000000) := by
  have h := checkLog_sound (w := (223 / 999777)) (n := 12)
    (lo := (446099 / 1000000000)) (hi := (4461 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499777) = 1/(499777 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11788 : Bounds (-4461 / 10000000) (-446099 / 1000000000) (Real.log (499777 / 500000)) := by
  have h := reflection_log_11788_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11789_neg : (207611551 / 1000000000) ≤ -Real.log (200000 / 246147) ∧
    -Real.log (200000 / 246147) ≤ (6487861 / 31250000) := by
  have h := checkLog_sound (w := (46147 / 446147)) (n := 12)
    (lo := (207611551 / 1000000000)) (hi := (6487861 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246147 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246147 / 200000) = 1/(200000 / 246147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11789 : Bounds (207611551 / 1000000000) (6487861 / 31250000) (Real.log (246147 / 200000)) := by
  have h := reflection_log_11789_neg
  have he : Real.log (246147 / 200000) = -Real.log (200000 / 246147) := by
    rw [show ((246147 / 200000) : ℝ) = ((200000 / 246147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11790_neg : (52463953 / 200000000) ≤ -Real.log (153853 / 200000) ∧
    -Real.log (153853 / 200000) ≤ (131159883 / 500000000) := by
  have h := checkLog_sound (w := (46147 / 353853)) (n := 12)
    (lo := (52463953 / 200000000)) (hi := (131159883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 153853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 153853) = 1/(153853 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11790 : Bounds (-131159883 / 500000000) (-52463953 / 200000000) (Real.log (153853 / 200000)) := by
  have h := reflection_log_11790_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11791_neg : (104207001 / 500000000) ≤ -Real.log (1000000 / 1231723) ∧
    -Real.log (1000000 / 1231723) ≤ (208414003 / 1000000000) := by
  have h := checkLog_sound (w := (231723 / 2231723)) (n := 12)
    (lo := (104207001 / 500000000)) (hi := (208414003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1231723 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1231723 / 1000000) = 1/(1000000 / 1231723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11791 : Bounds (104207001 / 500000000) (208414003 / 1000000000) (Real.log (1231723 / 1000000)) := by
  have h := reflection_log_11791_neg
  have he : Real.log (1231723 / 1000000) = -Real.log (1000000 / 1231723) := by
    rw [show ((1231723 / 1000000) : ℝ) = ((1000000 / 1231723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11792_neg : (263604933 / 1000000000) ≤ -Real.log (768277 / 1000000) ∧
    -Real.log (768277 / 1000000) ≤ (131802467 / 500000000) := by
  have h := checkLog_sound (w := (231723 / 1768277)) (n := 12)
    (lo := (263604933 / 1000000000)) (hi := (131802467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 768277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 768277) = 1/(768277 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11792 : Bounds (-131802467 / 500000000) (-263604933 / 1000000000) (Real.log (768277 / 1000000)) := by
  have h := reflection_log_11792_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11793_neg : (55190931 / 1000000000) ≤ -Real.log (946304451271 / 1000000000000) ∧
    -Real.log (946304451271 / 1000000000000) ≤ (13797733 / 250000000) := by
  have h := checkLog_sound (w := (53695548729 / 1946304451271)) (n := 12)
    (lo := (55190931 / 1000000000)) (hi := (13797733 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 946304451271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 946304451271) = 1/(946304451271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11793 : Bounds (-13797733 / 250000000) (-55190931 / 1000000000) (Real.log (946304451271 / 1000000000000)) := by
  have h := reflection_log_11793_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11794_neg : (54708213 / 1000000000) ≤ -Real.log (37870454391 / 40000000000) ∧
    -Real.log (37870454391 / 40000000000) ≤ (27354107 / 500000000) := by
  have h := checkLog_sound (w := (2129545609 / 77870454391)) (n := 12)
    (lo := (54708213 / 1000000000)) (hi := (27354107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37870454391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37870454391) = 1/(37870454391 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11794 : Bounds (-27354107 / 500000000) (-54708213 / 1000000000) (Real.log (37870454391 / 40000000000)) := by
  have h := reflection_log_11794_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11795_neg : (469931317 / 1000000000) ≤ -Real.log (250000000000 / 399971076287) ∧
    -Real.log (250000000000 / 399971076287) ≤ (234965659 / 500000000) := by
  have h := checkLog_sound (w := (149971076287 / 649971076287)) (n := 12)
    (lo := (469931317 / 1000000000)) (hi := (234965659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399971076287 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399971076287 / 250000000000) = 1/(250000000000 / 399971076287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11795 : Bounds (469931317 / 1000000000) (234965659 / 500000000) (Real.log (399971076287 / 250000000000)) := by
  have h := reflection_log_11795_neg
  have he : Real.log (399971076287 / 250000000000) = -Real.log (250000000000 / 399971076287) := by
    rw [show ((399971076287 / 250000000000) : ℝ) = ((250000000000 / 399971076287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11796_neg : (94403787 / 200000000) ≤ -Real.log (500000000000 / 801613871039) ∧
    -Real.log (500000000000 / 801613871039) ≤ (59002367 / 125000000) := by
  have h := checkLog_sound (w := (301613871039 / 1301613871039)) (n := 12)
    (lo := (94403787 / 200000000)) (hi := (59002367 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((801613871039 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(801613871039 / 500000000000) = 1/(500000000000 / 801613871039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11796 : Bounds (94403787 / 200000000) (59002367 / 125000000) (Real.log (801613871039 / 500000000000)) := by
  have h := reflection_log_11796_neg
  have he : Real.log (801613871039 / 500000000000) = -Real.log (500000000000 / 801613871039) := by
    rw [show ((801613871039 / 500000000000) : ℝ) = ((500000000000 / 801613871039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11797_neg : (478448243 / 500000000) ≤ -Real.log (500000000000 / 1301801801801) ∧
    -Real.log (500000000000 / 1301801801801) ≤ (119612061 / 125000000) := by
  have h := checkLog_sound (w := (301801801801 / 2301801801801)) (n := 12)
    (lo := (131874653 / 500000000)) (hi := (263749307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1301801801801 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1301801801801 / 1000000000000) = 1/(500000000000 / 1301801801801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11797 : Bounds (478448243 / 500000000) (119612061 / 125000000) (Real.log (1301801801801 / 500000000000)) := by
  have h := reflection_log_11797_neg
  have he : Real.log (1301801801801 / 500000000000) = -Real.log (500000000000 / 1301801801801) := by
    rw [show ((1301801801801 / 500000000000) : ℝ) = ((500000000000 / 1301801801801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11798_neg : (191878343 / 200000000) ≤ -Real.log (4000000000 / 10440433213) ∧
    -Real.log (4000000000 / 10440433213) ≤ (959391717 / 1000000000) := by
  have h := checkLog_sound (w := (2440433213 / 18440433213)) (n := 12)
    (lo := (53248907 / 200000000)) (hi := (33280567 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10440433213 / 8000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(10440433213 / 8000000000) = 1/(4000000000 / 10440433213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11798 : Bounds (191878343 / 200000000) (959391717 / 1000000000) (Real.log (10440433213 / 4000000000)) := by
  have h := reflection_log_11798_neg
  have he : Real.log (10440433213 / 4000000000) = -Real.log (4000000000 / 10440433213) := by
    rw [show ((10440433213 / 4000000000) : ℝ) = ((4000000000 / 10440433213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11799_neg : (369492447 / 1000000000) ≤ -Real.log (1000 / 1447) ∧
    -Real.log (1000 / 1447) ≤ (11546639 / 31250000) := by
  have h := checkLog_sound (w := (447 / 2447)) (n := 12)
    (lo := (369492447 / 1000000000)) (hi := (11546639 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1447 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1447 / 1000) = 1/(1000 / 1447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11799 : Bounds (369492447 / 1000000000) (11546639 / 31250000) (Real.log (1447 / 1000)) := by
  have h := reflection_log_11799_neg
  have he : Real.log (1447 / 1000) = -Real.log (1000 / 1447) := by
    rw [show ((1447 / 1000) : ℝ) = ((1000 / 1447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11800_neg : (592397277 / 1000000000) ≤ -Real.log (553 / 1000) ∧
    -Real.log (553 / 1000) ≤ (296198639 / 500000000) := by
  have h := checkLog_sound (w := (447 / 1553)) (n := 12)
    (lo := (592397277 / 1000000000)) (hi := (296198639 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 553) = 1/(553 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11800 : Bounds (-296198639 / 500000000) (-592397277 / 1000000000) (Real.log (553 / 1000)) := by
  have h := reflection_log_11800_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11801_neg : (4469 / 10000000) ≤ -Real.log (1000000 / 1000447) ∧
    -Real.log (1000000 / 1000447) ≤ (446901 / 1000000000) := by
  have h := checkLog_sound (w := (447 / 2000447)) (n := 12)
    (lo := (4469 / 10000000)) (hi := (446901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000447 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000447 / 1000000) = 1/(1000000 / 1000447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11801 : Bounds (4469 / 10000000) (446901 / 1000000000) (Real.log (1000447 / 1000000)) := by
  have h := reflection_log_11801_neg
  have he : Real.log (1000447 / 1000000) = -Real.log (1000000 / 1000447) := by
    rw [show ((1000447 / 1000000) : ℝ) = ((1000000 / 1000447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11802_neg : (447099 / 1000000000) ≤ -Real.log (999553 / 1000000) ∧
    -Real.log (999553 / 1000000) ≤ (4471 / 10000000) := by
  have h := checkLog_sound (w := (447 / 1999553)) (n := 12)
    (lo := (447099 / 1000000000)) (hi := (4471 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999553) = 1/(999553 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11802 : Bounds (-4471 / 10000000) (-447099 / 1000000000) (Real.log (999553 / 1000000)) := by
  have h := reflection_log_11802_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11803_neg : (13004103 / 62500000) ≤ -Real.log (500000 / 615647) ∧
    -Real.log (500000 / 615647) ≤ (208065649 / 1000000000) := by
  have h := checkLog_sound (w := (115647 / 1115647)) (n := 12)
    (lo := (13004103 / 62500000)) (hi := (208065649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((615647 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(615647 / 500000) = 1/(500000 / 615647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11803 : Bounds (13004103 / 62500000) (208065649 / 1000000000) (Real.log (615647 / 500000)) := by
  have h := reflection_log_11803_neg
  have he : Real.log (615647 / 500000) = -Real.log (500000 / 615647) := by
    rw [show ((615647 / 500000) : ℝ) = ((500000 / 615647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11804_neg : (263046697 / 1000000000) ≤ -Real.log (384353 / 500000) ∧
    -Real.log (384353 / 500000) ≤ (131523349 / 500000000) := by
  have h := checkLog_sound (w := (115647 / 884353)) (n := 12)
    (lo := (263046697 / 1000000000)) (hi := (131523349 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 384353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 384353) = 1/(384353 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11804 : Bounds (-131523349 / 500000000) (-263046697 / 1000000000) (Real.log (384353 / 500000)) := by
  have h := reflection_log_11804_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11805_neg : (104434679 / 500000000) ≤ -Real.log (250000 / 308071) ∧
    -Real.log (250000 / 308071) ≤ (208869359 / 1000000000) := by
  have h := checkLog_sound (w := (58071 / 558071)) (n := 12)
    (lo := (104434679 / 500000000)) (hi := (208869359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308071 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(308071 / 250000) = 1/(250000 / 308071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11805 : Bounds (104434679 / 500000000) (208869359 / 1000000000) (Real.log (308071 / 250000)) := by
  have h := reflection_log_11805_neg
  have he : Real.log (308071 / 250000) = -Real.log (250000 / 308071) := by
    rw [show ((308071 / 250000) : ℝ) = ((250000 / 308071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11806_neg : (52867081 / 200000000) ≤ -Real.log (191929 / 250000) ∧
    -Real.log (191929 / 250000) ≤ (132167703 / 500000000) := by
  have h := checkLog_sound (w := (58071 / 441929)) (n := 12)
    (lo := (52867081 / 200000000)) (hi := (132167703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 191929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 191929) = 1/(191929 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11806 : Bounds (-132167703 / 500000000) (-52867081 / 200000000) (Real.log (191929 / 250000)) := by
  have h := reflection_log_11806_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11807_neg : (55466047 / 1000000000) ≤ -Real.log (59127758959 / 62500000000) ∧
    -Real.log (59127758959 / 62500000000) ≤ (866657 / 15625000) := by
  have h := checkLog_sound (w := (3372241041 / 121627758959)) (n := 12)
    (lo := (55466047 / 1000000000)) (hi := (866657 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59127758959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59127758959) = 1/(59127758959 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11807 : Bounds (-866657 / 15625000) (-55466047 / 1000000000) (Real.log (59127758959 / 62500000000)) := by
  have h := reflection_log_11807_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11808_neg : (6872631 / 125000000) ≤ -Real.log (236625771391 / 250000000000) ∧
    -Real.log (236625771391 / 250000000000) ≤ (54981049 / 1000000000) := by
  have h := checkLog_sound (w := (13374228609 / 486625771391)) (n := 12)
    (lo := (6872631 / 125000000)) (hi := (54981049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 236625771391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 236625771391) = 1/(236625771391 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11808 : Bounds (-54981049 / 1000000000) (-6872631 / 125000000) (Real.log (236625771391 / 250000000000)) := by
  have h := reflection_log_11808_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11809_neg : (235556173 / 500000000) ≤ -Real.log (125000000000 / 200221866357) ∧
    -Real.log (125000000000 / 200221866357) ≤ (471112347 / 1000000000) := by
  have h := checkLog_sound (w := (75221866357 / 325221866357)) (n := 12)
    (lo := (235556173 / 500000000)) (hi := (471112347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200221866357 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200221866357 / 125000000000) = 1/(125000000000 / 200221866357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11809 : Bounds (235556173 / 500000000) (471112347 / 1000000000) (Real.log (200221866357 / 125000000000)) := by
  have h := reflection_log_11809_neg
  have he : Real.log (200221866357 / 125000000000) = -Real.log (125000000000 / 200221866357) := by
    rw [show ((200221866357 / 125000000000) : ℝ) = ((125000000000 / 200221866357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11810_neg : (473204763 / 1000000000) ≤ -Real.log (25000000000 / 40128250551) ∧
    -Real.log (25000000000 / 40128250551) ≤ (118301191 / 250000000) := by
  have h := checkLog_sound (w := (15128250551 / 65128250551)) (n := 12)
    (lo := (473204763 / 1000000000)) (hi := (118301191 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40128250551 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40128250551 / 25000000000) = 1/(25000000000 / 40128250551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11810 : Bounds (473204763 / 1000000000) (118301191 / 250000000) (Real.log (40128250551 / 25000000000)) := by
  have h := reflection_log_11810_neg
  have he : Real.log (40128250551 / 25000000000) = -Real.log (25000000000 / 40128250551) := by
    rw [show ((40128250551 / 25000000000) : ℝ) = ((25000000000 / 40128250551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11811_neg : (191878343 / 200000000) ≤ -Real.log (62500000000 / 163131768953) ∧
    -Real.log (62500000000 / 163131768953) ≤ (959391717 / 1000000000) := by
  have h := checkLog_sound (w := (38131768953 / 288131768953)) (n := 12)
    (lo := (53248907 / 200000000)) (hi := (33280567 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163131768953 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(163131768953 / 125000000000) = 1/(62500000000 / 163131768953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11811 : Bounds (191878343 / 200000000) (959391717 / 1000000000) (Real.log (163131768953 / 62500000000)) := by
  have h := reflection_log_11811_neg
  have he : Real.log (163131768953 / 62500000000) = -Real.log (62500000000 / 163131768953) := by
    rw [show ((163131768953 / 62500000000) : ℝ) = ((62500000000 / 163131768953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11812_neg : (240472431 / 250000000) ≤ -Real.log (100000000000 / 261663652803) ∧
    -Real.log (100000000000 / 261663652803) ≤ (480944863 / 500000000) := by
  have h := checkLog_sound (w := (61663652803 / 461663652803)) (n := 12)
    (lo := (16796409 / 62500000)) (hi := (53748509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((261663652803 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(261663652803 / 200000000000) = 1/(100000000000 / 261663652803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11812 : Bounds (240472431 / 250000000) (480944863 / 500000000) (Real.log (261663652803 / 100000000000)) := by
  have h := reflection_log_11812_neg
  have he : Real.log (261663652803 / 100000000000) = -Real.log (100000000000 / 261663652803) := by
    rw [show ((261663652803 / 100000000000) : ℝ) = ((100000000000 / 261663652803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11813_neg : (370183293 / 1000000000) ≤ -Real.log (125 / 181) ∧
    -Real.log (125 / 181) ≤ (185091647 / 500000000) := by
  have h := checkLog_sound (w := (28 / 153)) (n := 12)
    (lo := (370183293 / 1000000000)) (hi := (185091647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181 / 125) = 1/(125 / 181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11813 : Bounds (370183293 / 1000000000) (185091647 / 500000000) (Real.log (181 / 125)) := by
  have h := reflection_log_11813_neg
  have he : Real.log (181 / 125) = -Real.log (125 / 181) := by
    rw [show ((181 / 125) : ℝ) = ((125 / 181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11814_neg : (1160561 / 1953125) ≤ -Real.log (69 / 125) ∧
    -Real.log (69 / 125) ≤ (594207233 / 1000000000) := by
  have h := checkLog_sound (w := (28 / 97)) (n := 12)
    (lo := (1160561 / 1953125)) (hi := (594207233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 69) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 69) = 1/(69 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11814 : Bounds (-594207233 / 1000000000) (-1160561 / 1953125) (Real.log (69 / 125)) := by
  have h := reflection_log_11814_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11815_neg : (447899 / 1000000000) ≤ -Real.log (15625 / 15632) ∧
    -Real.log (15625 / 15632) ≤ (4479 / 10000000) := by
  have h := checkLog_sound (w := (7 / 31257)) (n := 12)
    (lo := (447899 / 1000000000)) (hi := (4479 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15632 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15632 / 15625) = 1/(15625 / 15632) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11815 : Bounds (447899 / 1000000000) (4479 / 10000000) (Real.log (15632 / 15625)) := by
  have h := reflection_log_11815_neg
  have he : Real.log (15632 / 15625) = -Real.log (15625 / 15632) := by
    rw [show ((15632 / 15625) : ℝ) = ((15625 / 15632) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11816_neg : (4481 / 10000000) ≤ -Real.log (15618 / 15625) ∧
    -Real.log (15618 / 15625) ≤ (448101 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 31243)) (n := 12)
    (lo := (4481 / 10000000)) (hi := (448101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15618) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 15618) = 1/(15618 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11816 : Bounds (-448101 / 1000000000) (-4481 / 10000000) (Real.log (15618 / 15625)) := by
  have h := reflection_log_11816_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11817_neg : (208520351 / 1000000000) ≤ -Real.log (500000 / 615927) ∧
    -Real.log (500000 / 615927) ≤ (6516261 / 31250000) := by
  have h := checkLog_sound (w := (115927 / 1115927)) (n := 12)
    (lo := (208520351 / 1000000000)) (hi := (6516261 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((615927 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(615927 / 500000) = 1/(500000 / 615927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11817 : Bounds (208520351 / 1000000000) (6516261 / 31250000) (Real.log (615927 / 500000)) := by
  have h := reflection_log_11817_neg
  have he : Real.log (615927 / 500000) = -Real.log (500000 / 615927) := by
    rw [show ((615927 / 500000) : ℝ) = ((500000 / 615927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11818_neg : (263775459 / 1000000000) ≤ -Real.log (384073 / 500000) ∧
    -Real.log (384073 / 500000) ≤ (13188773 / 50000000) := by
  have h := checkLog_sound (w := (115927 / 884073)) (n := 12)
    (lo := (263775459 / 1000000000)) (hi := (13188773 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 384073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 384073) = 1/(384073 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11818 : Bounds (-13188773 / 50000000) (-263775459 / 1000000000) (Real.log (384073 / 500000)) := by
  have h := reflection_log_11818_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11819_neg : (41864739 / 200000000) ≤ -Real.log (250000 / 308211) ∧
    -Real.log (250000 / 308211) ≤ (13082731 / 62500000) := by
  have h := checkLog_sound (w := (58211 / 558211)) (n := 12)
    (lo := (41864739 / 200000000)) (hi := (13082731 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308211 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(308211 / 250000) = 1/(250000 / 308211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11819 : Bounds (41864739 / 200000000) (13082731 / 62500000) (Real.log (308211 / 250000)) := by
  have h := reflection_log_11819_neg
  have he : Real.log (308211 / 250000) = -Real.log (250000 / 308211) := by
    rw [show ((308211 / 250000) : ℝ) = ((250000 / 308211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11820_neg : (66266277 / 250000000) ≤ -Real.log (191789 / 250000) ∧
    -Real.log (191789 / 250000) ≤ (265065109 / 1000000000) := by
  have h := checkLog_sound (w := (58211 / 441789)) (n := 12)
    (lo := (66266277 / 250000000)) (hi := (265065109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 191789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 191789) = 1/(191789 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11820 : Bounds (-265065109 / 1000000000) (-66266277 / 250000000) (Real.log (191789 / 250000)) := by
  have h := reflection_log_11820_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11821_neg : (13935353 / 250000000) ≤ -Real.log (59111479479 / 62500000000) ∧
    -Real.log (59111479479 / 62500000000) ≤ (55741413 / 1000000000) := by
  have h := checkLog_sound (w := (3388520521 / 121611479479)) (n := 12)
    (lo := (13935353 / 250000000)) (hi := (55741413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59111479479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59111479479) = 1/(59111479479 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11821 : Bounds (-55741413 / 1000000000) (-13935353 / 250000000) (Real.log (59111479479 / 62500000000)) := by
  have h := reflection_log_11821_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11822_neg : (13813777 / 250000000) ≤ -Real.log (236560930671 / 250000000000) ∧
    -Real.log (236560930671 / 250000000000) ≤ (55255109 / 1000000000) := by
  have h := checkLog_sound (w := (13439069329 / 486560930671)) (n := 12)
    (lo := (13813777 / 250000000)) (hi := (55255109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 236560930671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 236560930671) = 1/(236560930671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11822 : Bounds (-55255109 / 1000000000) (-13813777 / 250000000) (Real.log (236560930671 / 250000000000)) := by
  have h := reflection_log_11822_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11823_neg : (472295811 / 1000000000) ≤ -Real.log (250000000000 / 400917924457) ∧
    -Real.log (250000000000 / 400917924457) ≤ (118073953 / 250000000) := by
  have h := checkLog_sound (w := (150917924457 / 650917924457)) (n := 12)
    (lo := (472295811 / 1000000000)) (hi := (118073953 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400917924457 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400917924457 / 250000000000) = 1/(250000000000 / 400917924457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11823 : Bounds (472295811 / 1000000000) (118073953 / 250000000) (Real.log (400917924457 / 250000000000)) := by
  have h := reflection_log_11823_neg
  have he : Real.log (400917924457 / 250000000000) = -Real.log (250000000000 / 400917924457) := by
    rw [show ((400917924457 / 250000000000) : ℝ) = ((250000000000 / 400917924457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11824_neg : (474388803 / 1000000000) ≤ -Real.log (125000000000 / 200878960733) ∧
    -Real.log (125000000000 / 200878960733) ≤ (118597201 / 250000000) := by
  have h := checkLog_sound (w := (75878960733 / 325878960733)) (n := 12)
    (lo := (474388803 / 1000000000)) (hi := (118597201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200878960733 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200878960733 / 125000000000) = 1/(125000000000 / 200878960733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11824 : Bounds (474388803 / 1000000000) (118597201 / 250000000) (Real.log (200878960733 / 125000000000)) := by
  have h := reflection_log_11824_neg
  have he : Real.log (200878960733 / 125000000000) = -Real.log (125000000000 / 200878960733) := by
    rw [show ((200878960733 / 125000000000) : ℝ) = ((125000000000 / 200878960733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11825_neg : (240472431 / 250000000) ≤ -Real.log (250000000000 / 654159132007) ∧
    -Real.log (250000000000 / 654159132007) ≤ (480944863 / 500000000) := by
  have h := checkLog_sound (w := (154159132007 / 1154159132007)) (n := 12)
    (lo := (16796409 / 62500000)) (hi := (53748509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((654159132007 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(654159132007 / 500000000000) = 1/(250000000000 / 654159132007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11825 : Bounds (240472431 / 250000000) (480944863 / 500000000) (Real.log (654159132007 / 250000000000)) := by
  have h := reflection_log_11825_neg
  have he : Real.log (654159132007 / 250000000000) = -Real.log (250000000000 / 654159132007) := by
    rw [show ((654159132007 / 250000000000) : ℝ) = ((250000000000 / 654159132007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11826_neg : (482195263 / 500000000) ≤ -Real.log (500000000000 / 1311594202899) ∧
    -Real.log (500000000000 / 1311594202899) ≤ (7534301 / 7812500) := by
  have h := checkLog_sound (w := (311594202899 / 2311594202899)) (n := 12)
    (lo := (135621673 / 500000000)) (hi := (271243347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1311594202899 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1311594202899 / 1000000000000) = 1/(500000000000 / 1311594202899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11826 : Bounds (482195263 / 500000000) (7534301 / 7812500) (Real.log (1311594202899 / 500000000000)) := by
  have h := reflection_log_11826_neg
  have he : Real.log (1311594202899 / 500000000000) = -Real.log (500000000000 / 1311594202899) := by
    rw [show ((1311594202899 / 500000000000) : ℝ) = ((500000000000 / 1311594202899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11827_neg : (370873663 / 1000000000) ≤ -Real.log (1000 / 1449) ∧
    -Real.log (1000 / 1449) ≤ (5794901 / 15625000) := by
  have h := checkLog_sound (w := (449 / 2449)) (n := 12)
    (lo := (370873663 / 1000000000)) (hi := (5794901 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1449 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1449 / 1000) = 1/(1000 / 1449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11827 : Bounds (370873663 / 1000000000) (5794901 / 15625000) (Real.log (1449 / 1000)) := by
  have h := reflection_log_11827_neg
  have he : Real.log (1449 / 1000) = -Real.log (1000 / 1449) := by
    rw [show ((1449 / 1000) : ℝ) = ((1000 / 1449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11828_neg : (596020469 / 1000000000) ≤ -Real.log (551 / 1000) ∧
    -Real.log (551 / 1000) ≤ (59602047 / 100000000) := by
  have h := checkLog_sound (w := (449 / 1551)) (n := 12)
    (lo := (596020469 / 1000000000)) (hi := (59602047 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 551) = 1/(551 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11828 : Bounds (-59602047 / 100000000) (-596020469 / 1000000000) (Real.log (551 / 1000)) := by
  have h := reflection_log_11828_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11829_neg : (448899 / 1000000000) ≤ -Real.log (1000000 / 1000449) ∧
    -Real.log (1000000 / 1000449) ≤ (4489 / 10000000) := by
  have h := checkLog_sound (w := (449 / 2000449)) (n := 12)
    (lo := (448899 / 1000000000)) (hi := (4489 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000449 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000449 / 1000000) = 1/(1000000 / 1000449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11829 : Bounds (448899 / 1000000000) (4489 / 10000000) (Real.log (1000449 / 1000000)) := by
  have h := reflection_log_11829_neg
  have he : Real.log (1000449 / 1000000) = -Real.log (1000000 / 1000449) := by
    rw [show ((1000449 / 1000000) : ℝ) = ((1000000 / 1000449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11830_neg : (4491 / 10000000) ≤ -Real.log (999551 / 1000000) ∧
    -Real.log (999551 / 1000000) ≤ (449101 / 1000000000) := by
  have h := checkLog_sound (w := (449 / 1999551)) (n := 12)
    (lo := (4491 / 10000000)) (hi := (449101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999551) = 1/(999551 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11830 : Bounds (-449101 / 1000000000) (-4491 / 10000000) (Real.log (999551 / 1000000)) := by
  have h := reflection_log_11830_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11831_neg : (208974847 / 1000000000) ≤ -Real.log (500000 / 616207) ∧
    -Real.log (500000 / 616207) ≤ (408154 / 1953125) := by
  have h := checkLog_sound (w := (116207 / 1116207)) (n := 12)
    (lo := (208974847 / 1000000000)) (hi := (408154 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((616207 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(616207 / 500000) = 1/(500000 / 616207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11831 : Bounds (208974847 / 1000000000) (408154 / 1953125) (Real.log (616207 / 500000)) := by
  have h := reflection_log_11831_neg
  have he : Real.log (616207 / 500000) = -Real.log (500000 / 616207) := by
    rw [show ((616207 / 500000) : ℝ) = ((500000 / 616207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11832_neg : (264504753 / 1000000000) ≤ -Real.log (383793 / 500000) ∧
    -Real.log (383793 / 500000) ≤ (132252377 / 500000000) := by
  have h := checkLog_sound (w := (116207 / 883793)) (n := 12)
    (lo := (264504753 / 1000000000)) (hi := (132252377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 383793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 383793) = 1/(383793 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11832 : Bounds (-132252377 / 500000000) (-264504753 / 1000000000) (Real.log (383793 / 500000)) := by
  have h := reflection_log_11832_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11833_neg : (209778637 / 1000000000) ≤ -Real.log (200000 / 246681) ∧
    -Real.log (200000 / 246681) ≤ (104889319 / 500000000) := by
  have h := checkLog_sound (w := (46681 / 446681)) (n := 12)
    (lo := (209778637 / 1000000000)) (hi := (104889319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246681 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246681 / 200000) = 1/(200000 / 246681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11833 : Bounds (209778637 / 1000000000) (104889319 / 500000000) (Real.log (246681 / 200000)) := by
  have h := reflection_log_11833_neg
  have he : Real.log (246681 / 200000) = -Real.log (200000 / 246681) := by
    rw [show ((246681 / 200000) : ℝ) = ((200000 / 246681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11834_neg : (33224581 / 125000000) ≤ -Real.log (153319 / 200000) ∧
    -Real.log (153319 / 200000) ≤ (265796649 / 1000000000) := by
  have h := checkLog_sound (w := (46681 / 353319)) (n := 12)
    (lo := (33224581 / 125000000)) (hi := (265796649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 153319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 153319) = 1/(153319 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11834 : Bounds (-265796649 / 1000000000) (-33224581 / 125000000) (Real.log (153319 / 200000)) := by
  have h := reflection_log_11834_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11835_neg : (5601801 / 100000000) ≤ -Real.log (37820884239 / 40000000000) ∧
    -Real.log (37820884239 / 40000000000) ≤ (56018011 / 1000000000) := by
  have h := checkLog_sound (w := (2179115761 / 77820884239)) (n := 12)
    (lo := (5601801 / 100000000)) (hi := (56018011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37820884239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37820884239) = 1/(37820884239 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11835 : Bounds (-56018011 / 1000000000) (-5601801 / 100000000) (Real.log (37820884239 / 40000000000)) := by
  have h := reflection_log_11835_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11836_neg : (27764953 / 500000000) ≤ -Real.log (236495933151 / 250000000000) ∧
    -Real.log (236495933151 / 250000000000) ≤ (55529907 / 1000000000) := by
  have h := checkLog_sound (w := (13504066849 / 486495933151)) (n := 12)
    (lo := (27764953 / 500000000)) (hi := (55529907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 236495933151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 236495933151) = 1/(236495933151 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11836 : Bounds (-55529907 / 1000000000) (-27764953 / 500000000) (Real.log (236495933151 / 250000000000)) := by
  have h := reflection_log_11836_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11837_neg : (473479601 / 1000000000) ≤ -Real.log (125000000000 / 200696404051) ∧
    -Real.log (125000000000 / 200696404051) ≤ (236739801 / 500000000) := by
  have h := checkLog_sound (w := (75696404051 / 325696404051)) (n := 12)
    (lo := (473479601 / 1000000000)) (hi := (236739801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200696404051 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200696404051 / 125000000000) = 1/(125000000000 / 200696404051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11837 : Bounds (473479601 / 1000000000) (236739801 / 500000000) (Real.log (200696404051 / 125000000000)) := by
  have h := reflection_log_11837_neg
  have he : Real.log (200696404051 / 125000000000) = -Real.log (125000000000 / 200696404051) := by
    rw [show ((200696404051 / 125000000000) : ℝ) = ((125000000000 / 200696404051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11838_neg : (95115057 / 200000000) ≤ -Real.log (500000000000 / 804469765653) ∧
    -Real.log (500000000000 / 804469765653) ≤ (237787643 / 500000000) := by
  have h := checkLog_sound (w := (304469765653 / 1304469765653)) (n := 12)
    (lo := (95115057 / 200000000)) (hi := (237787643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((804469765653 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(804469765653 / 500000000000) = 1/(500000000000 / 804469765653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11838 : Bounds (95115057 / 200000000) (237787643 / 500000000) (Real.log (804469765653 / 500000000000)) := by
  have h := reflection_log_11838_neg
  have he : Real.log (804469765653 / 500000000000) = -Real.log (500000000000 / 804469765653) := by
    rw [show ((804469765653 / 500000000000) : ℝ) = ((500000000000 / 804469765653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11839_neg : (482195263 / 500000000) ≤ -Real.log (250000000000 / 655797101449) ∧
    -Real.log (250000000000 / 655797101449) ≤ (7534301 / 7812500) := by
  have h := checkLog_sound (w := (155797101449 / 1155797101449)) (n := 12)
    (lo := (135621673 / 500000000)) (hi := (271243347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((655797101449 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(655797101449 / 500000000000) = 1/(250000000000 / 655797101449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11839 : Bounds (482195263 / 500000000) (7534301 / 7812500) (Real.log (655797101449 / 250000000000)) := by
  have h := reflection_log_11839_neg
  have he : Real.log (655797101449 / 250000000000) = -Real.log (250000000000 / 655797101449) := by
    rw [show ((655797101449 / 250000000000) : ℝ) = ((250000000000 / 655797101449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0185 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11840_neg : (241723533 / 250000000) ≤ -Real.log (125000000000 / 328720508167) ∧
    -Real.log (125000000000 / 328720508167) ≤ (483447067 / 500000000) := by
  have h := checkLog_sound (w := (78720508167 / 578720508167)) (n := 12)
    (lo := (34218369 / 125000000)) (hi := (273746953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328720508167 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(328720508167 / 250000000000) = 1/(125000000000 / 328720508167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11840 : Bounds (241723533 / 250000000) (483447067 / 500000000) (Real.log (328720508167 / 125000000000)) := by
  have h := reflection_log_11840_neg
  have he : Real.log (328720508167 / 125000000000) = -Real.log (125000000000 / 328720508167) := by
    rw [show ((328720508167 / 125000000000) : ℝ) = ((125000000000 / 328720508167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11841_neg : (92890889 / 250000000) ≤ -Real.log (20 / 29) ∧
    -Real.log (20 / 29) ≤ (371563557 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 49)) (n := 12)
    (lo := (92890889 / 250000000)) (hi := (371563557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29 / 20) = 1/(20 / 29) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11841 : Bounds (92890889 / 250000000) (371563557 / 1000000000) (Real.log (29 / 20)) := by
  have h := reflection_log_11841_neg
  have he : Real.log (29 / 20) = -Real.log (20 / 29) := by
    rw [show ((29 / 20) : ℝ) = ((20 / 29) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11842_neg : (597837 / 1000000) ≤ -Real.log (11 / 20) ∧
    -Real.log (11 / 20) ≤ (597837001 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 31)) (n := 12)
    (lo := (597837 / 1000000)) (hi := (597837001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 11) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20 / 11) = 1/(11 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11842 : Bounds (-597837001 / 1000000000) (-597837 / 1000000) (Real.log (11 / 20)) := by
  have h := reflection_log_11842_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11843_neg : (224949 / 500000000) ≤ -Real.log (20000 / 20009) ∧
    -Real.log (20000 / 20009) ≤ (449899 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 40009)) (n := 12)
    (lo := (224949 / 500000000)) (hi := (449899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20009 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20009 / 20000) = 1/(20000 / 20009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11843 : Bounds (224949 / 500000000) (449899 / 1000000000) (Real.log (20009 / 20000)) := by
  have h := reflection_log_11843_neg
  have he : Real.log (20009 / 20000) = -Real.log (20000 / 20009) := by
    rw [show ((20009 / 20000) : ℝ) = ((20000 / 20009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11844_neg : (450101 / 1000000000) ≤ -Real.log (19991 / 20000) ∧
    -Real.log (19991 / 20000) ≤ (225051 / 500000000) := by
  have h := checkLog_sound (w := (9 / 39991)) (n := 12)
    (lo := (450101 / 1000000000)) (hi := (225051 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 19991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 19991) = 1/(19991 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11844 : Bounds (-225051 / 500000000) (-450101 / 1000000000) (Real.log (19991 / 20000)) := by
  have h := reflection_log_11844_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11845_neg : (209429137 / 1000000000) ≤ -Real.log (500000 / 616487) ∧
    -Real.log (500000 / 616487) ≤ (104714569 / 500000000) := by
  have h := checkLog_sound (w := (116487 / 1116487)) (n := 12)
    (lo := (209429137 / 1000000000)) (hi := (104714569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((616487 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(616487 / 500000) = 1/(500000 / 616487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11845 : Bounds (209429137 / 1000000000) (104714569 / 500000000) (Real.log (616487 / 500000)) := by
  have h := reflection_log_11845_neg
  have he : Real.log (616487 / 500000) = -Real.log (500000 / 616487) := by
    rw [show ((616487 / 500000) : ℝ) = ((500000 / 616487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11846_neg : (265234579 / 1000000000) ≤ -Real.log (383513 / 500000) ∧
    -Real.log (383513 / 500000) ≤ (13261729 / 50000000) := by
  have h := checkLog_sound (w := (116487 / 883513)) (n := 12)
    (lo := (265234579 / 1000000000)) (hi := (13261729 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 383513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 383513) = 1/(383513 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11846 : Bounds (-13261729 / 50000000) (-265234579 / 1000000000) (Real.log (383513 / 500000)) := by
  have h := reflection_log_11846_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11847_neg : (52558343 / 250000000) ≤ -Real.log (500000 / 616983) ∧
    -Real.log (500000 / 616983) ≤ (210233373 / 1000000000) := by
  have h := checkLog_sound (w := (116983 / 1116983)) (n := 12)
    (lo := (52558343 / 250000000)) (hi := (210233373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((616983 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(616983 / 500000) = 1/(500000 / 616983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11847 : Bounds (52558343 / 250000000) (210233373 / 1000000000) (Real.log (616983 / 500000)) := by
  have h := reflection_log_11847_neg
  have he : Real.log (616983 / 500000) = -Real.log (500000 / 616983) := by
    rw [show ((616983 / 500000) : ℝ) = ((500000 / 616983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11848_neg : (266528723 / 1000000000) ≤ -Real.log (383017 / 500000) ∧
    -Real.log (383017 / 500000) ≤ (66632181 / 250000000) := by
  have h := checkLog_sound (w := (116983 / 883017)) (n := 12)
    (lo := (266528723 / 1000000000)) (hi := (66632181 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 383017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 383017) = 1/(383017 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11848 : Bounds (-66632181 / 250000000) (-266528723 / 1000000000) (Real.log (383017 / 500000)) := by
  have h := reflection_log_11848_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11849_neg : (56295351 / 1000000000) ≤ -Real.log (236314977711 / 250000000000) ∧
    -Real.log (236314977711 / 250000000000) ≤ (7036919 / 125000000) := by
  have h := checkLog_sound (w := (13685022289 / 486314977711)) (n := 12)
    (lo := (56295351 / 1000000000)) (hi := (7036919 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 236314977711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 236314977711) = 1/(236314977711 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11849 : Bounds (-7036919 / 125000000) (-56295351 / 1000000000) (Real.log (236314977711 / 250000000000)) := by
  have h := reflection_log_11849_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11850_neg : (27902721 / 500000000) ≤ -Real.log (236430778831 / 250000000000) ∧
    -Real.log (236430778831 / 250000000000) ≤ (55805443 / 1000000000) := by
  have h := checkLog_sound (w := (13569221169 / 486430778831)) (n := 12)
    (lo := (27902721 / 500000000)) (hi := (55805443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 236430778831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 236430778831) = 1/(236430778831 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11850 : Bounds (-55805443 / 1000000000) (-27902721 / 500000000) (Real.log (236430778831 / 250000000000)) := by
  have h := reflection_log_11850_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11851_neg : (474663717 / 1000000000) ≤ -Real.log (500000000000 / 803736770331) ∧
    -Real.log (500000000000 / 803736770331) ≤ (237331859 / 500000000) := by
  have h := checkLog_sound (w := (303736770331 / 1303736770331)) (n := 12)
    (lo := (474663717 / 1000000000)) (hi := (237331859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((803736770331 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(803736770331 / 500000000000) = 1/(500000000000 / 803736770331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11851 : Bounds (474663717 / 1000000000) (237331859 / 500000000) (Real.log (803736770331 / 500000000000)) := by
  have h := reflection_log_11851_neg
  have he : Real.log (803736770331 / 500000000000) = -Real.log (500000000000 / 803736770331) := by
    rw [show ((803736770331 / 500000000000) : ℝ) = ((500000000000 / 803736770331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11852_neg : (29797631 / 62500000) ≤ -Real.log (500000000000 / 805425085571) ∧
    -Real.log (500000000000 / 805425085571) ≤ (476762097 / 1000000000) := by
  have h := checkLog_sound (w := (305425085571 / 1305425085571)) (n := 12)
    (lo := (29797631 / 62500000)) (hi := (476762097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((805425085571 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(805425085571 / 500000000000) = 1/(500000000000 / 805425085571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11852 : Bounds (29797631 / 62500000) (476762097 / 1000000000) (Real.log (805425085571 / 500000000000)) := by
  have h := reflection_log_11852_neg
  have he : Real.log (805425085571 / 500000000000) = -Real.log (500000000000 / 805425085571) := by
    rw [show ((805425085571 / 500000000000) : ℝ) = ((500000000000 / 805425085571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11853_neg : (241723533 / 250000000) ≤ -Real.log (500000000000 / 1314882032667) ∧
    -Real.log (500000000000 / 1314882032667) ≤ (483447067 / 500000000) := by
  have h := checkLog_sound (w := (314882032667 / 2314882032667)) (n := 12)
    (lo := (34218369 / 125000000)) (hi := (273746953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1314882032667 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1314882032667 / 1000000000000) = 1/(500000000000 / 1314882032667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11853 : Bounds (241723533 / 250000000) (483447067 / 500000000) (Real.log (1314882032667 / 500000000000)) := by
  have h := reflection_log_11853_neg
  have he : Real.log (1314882032667 / 500000000000) = -Real.log (500000000000 / 1314882032667) := by
    rw [show ((1314882032667 / 500000000000) : ℝ) = ((500000000000 / 1314882032667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11854_neg : (242350139 / 250000000) ≤ -Real.log (250000000000 / 659090909091) ∧
    -Real.log (250000000000 / 659090909091) ≤ (484700279 / 500000000) := by
  have h := checkLog_sound (w := (159090909091 / 1159090909091)) (n := 12)
    (lo := (4316459 / 15625000)) (hi := (276253377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((659090909091 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(659090909091 / 500000000000) = 1/(250000000000 / 659090909091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11854 : Bounds (242350139 / 250000000) (484700279 / 500000000) (Real.log (659090909091 / 250000000000)) := by
  have h := reflection_log_11854_neg
  have he : Real.log (659090909091 / 250000000000) = -Real.log (250000000000 / 659090909091) := by
    rw [show ((659090909091 / 250000000000) : ℝ) = ((250000000000 / 659090909091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11855_neg : (372252973 / 1000000000) ≤ -Real.log (1000 / 1451) ∧
    -Real.log (1000 / 1451) ≤ (186126487 / 500000000) := by
  have h := checkLog_sound (w := (451 / 2451)) (n := 12)
    (lo := (372252973 / 1000000000)) (hi := (186126487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1451 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1451 / 1000) = 1/(1000 / 1451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11855 : Bounds (372252973 / 1000000000) (186126487 / 500000000) (Real.log (1451 / 1000)) := by
  have h := reflection_log_11855_neg
  have he : Real.log (1451 / 1000) = -Real.log (1000 / 1451) := by
    rw [show ((1451 / 1000) : ℝ) = ((1000 / 1451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11856_neg : (599656837 / 1000000000) ≤ -Real.log (549 / 1000) ∧
    -Real.log (549 / 1000) ≤ (299828419 / 500000000) := by
  have h := checkLog_sound (w := (451 / 1549)) (n := 12)
    (lo := (599656837 / 1000000000)) (hi := (299828419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 549) = 1/(549 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11856 : Bounds (-299828419 / 500000000) (-599656837 / 1000000000) (Real.log (549 / 1000)) := by
  have h := reflection_log_11856_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11857_neg : (225449 / 500000000) ≤ -Real.log (1000000 / 1000451) ∧
    -Real.log (1000000 / 1000451) ≤ (450899 / 1000000000) := by
  have h := checkLog_sound (w := (451 / 2000451)) (n := 12)
    (lo := (225449 / 500000000)) (hi := (450899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000451 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000451 / 1000000) = 1/(1000000 / 1000451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11857 : Bounds (225449 / 500000000) (450899 / 1000000000) (Real.log (1000451 / 1000000)) := by
  have h := reflection_log_11857_neg
  have he : Real.log (1000451 / 1000000) = -Real.log (1000000 / 1000451) := by
    rw [show ((1000451 / 1000000) : ℝ) = ((1000000 / 1000451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11858_neg : (451101 / 1000000000) ≤ -Real.log (999549 / 1000000) ∧
    -Real.log (999549 / 1000000) ≤ (225551 / 500000000) := by
  have h := checkLog_sound (w := (451 / 1999549)) (n := 12)
    (lo := (451101 / 1000000000)) (hi := (225551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999549) = 1/(999549 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11858 : Bounds (-225551 / 500000000) (-451101 / 1000000000) (Real.log (999549 / 1000000)) := by
  have h := reflection_log_11858_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11859_neg : (10494161 / 50000000) ≤ -Real.log (500000 / 616767) ∧
    -Real.log (500000 / 616767) ≤ (209883221 / 1000000000) := by
  have h := checkLog_sound (w := (116767 / 1116767)) (n := 12)
    (lo := (10494161 / 50000000)) (hi := (209883221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((616767 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(616767 / 500000) = 1/(500000 / 616767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11859 : Bounds (10494161 / 50000000) (209883221 / 1000000000) (Real.log (616767 / 500000)) := by
  have h := reflection_log_11859_neg
  have he : Real.log (616767 / 500000) = -Real.log (500000 / 616767) := by
    rw [show ((616767 / 500000) : ℝ) = ((500000 / 616767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11860_neg : (265964939 / 1000000000) ≤ -Real.log (383233 / 500000) ∧
    -Real.log (383233 / 500000) ≤ (13298247 / 50000000) := by
  have h := checkLog_sound (w := (116767 / 883233)) (n := 12)
    (lo := (265964939 / 1000000000)) (hi := (13298247 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 383233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 383233) = 1/(383233 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11860 : Bounds (-13298247 / 50000000) (-265964939 / 1000000000) (Real.log (383233 / 500000)) := by
  have h := reflection_log_11860_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11861_neg : (21068871 / 100000000) ≤ -Real.log (31250 / 38579) ∧
    -Real.log (31250 / 38579) ≤ (210688711 / 1000000000) := by
  have h := checkLog_sound (w := (7329 / 69829)) (n := 12)
    (lo := (21068871 / 100000000)) (hi := (210688711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38579 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38579 / 31250) = 1/(31250 / 38579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11861 : Bounds (21068871 / 100000000) (210688711 / 1000000000) (Real.log (38579 / 31250)) := by
  have h := reflection_log_11861_neg
  have he : Real.log (38579 / 31250) = -Real.log (31250 / 38579) := by
    rw [show ((38579 / 31250) : ℝ) = ((31250 / 38579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11862_neg : (267262641 / 1000000000) ≤ -Real.log (23921 / 31250) ∧
    -Real.log (23921 / 31250) ≤ (133631321 / 500000000) := by
  have h := checkLog_sound (w := (7329 / 55171)) (n := 12)
    (lo := (267262641 / 1000000000)) (hi := (133631321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 23921) = 1/(23921 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11862 : Bounds (-133631321 / 500000000) (-267262641 / 1000000000) (Real.log (23921 / 31250)) := by
  have h := reflection_log_11862_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11863_neg : (56573931 / 1000000000) ≤ -Real.log (922848259 / 976562500) ∧
    -Real.log (922848259 / 976562500) ≤ (14143483 / 250000000) := by
  have h := checkLog_sound (w := (53714241 / 1899410759)) (n := 12)
    (lo := (56573931 / 1000000000)) (hi := (14143483 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 922848259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 922848259) = 1/(922848259 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11863 : Bounds (-14143483 / 250000000) (-56573931 / 1000000000) (Real.log (922848259 / 976562500)) := by
  have h := reflection_log_11863_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11864_neg : (28040859 / 500000000) ≤ -Real.log (236365467711 / 250000000000) ∧
    -Real.log (236365467711 / 250000000000) ≤ (56081719 / 1000000000) := by
  have h := checkLog_sound (w := (13634532289 / 486365467711)) (n := 12)
    (lo := (28040859 / 500000000)) (hi := (56081719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 236365467711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 236365467711) = 1/(236365467711 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11864 : Bounds (-56081719 / 1000000000) (-28040859 / 500000000) (Real.log (236365467711 / 250000000000)) := by
  have h := reflection_log_11864_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11865_neg : (475848159 / 1000000000) ≤ -Real.log (500000000000 / 804689314333) ∧
    -Real.log (500000000000 / 804689314333) ≤ (2974051 / 6250000) := by
  have h := checkLog_sound (w := (304689314333 / 1304689314333)) (n := 12)
    (lo := (475848159 / 1000000000)) (hi := (2974051 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((804689314333 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(804689314333 / 500000000000) = 1/(500000000000 / 804689314333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11865 : Bounds (475848159 / 1000000000) (2974051 / 6250000) (Real.log (804689314333 / 500000000000)) := by
  have h := reflection_log_11865_neg
  have he : Real.log (804689314333 / 500000000000) = -Real.log (500000000000 / 804689314333) := by
    rw [show ((804689314333 / 500000000000) : ℝ) = ((500000000000 / 804689314333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11866_neg : (59743919 / 125000000) ≤ -Real.log (100000000000 / 161276702479) ∧
    -Real.log (100000000000 / 161276702479) ≤ (477951353 / 1000000000) := by
  have h := checkLog_sound (w := (61276702479 / 261276702479)) (n := 12)
    (lo := (59743919 / 125000000)) (hi := (477951353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161276702479 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161276702479 / 100000000000) = 1/(100000000000 / 161276702479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11866 : Bounds (59743919 / 125000000) (477951353 / 1000000000) (Real.log (161276702479 / 100000000000)) := by
  have h := reflection_log_11866_neg
  have he : Real.log (161276702479 / 100000000000) = -Real.log (100000000000 / 161276702479) := by
    rw [show ((161276702479 / 100000000000) : ℝ) = ((100000000000 / 161276702479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11867_neg : (242350139 / 250000000) ≤ -Real.log (500000000000 / 1318181818181) ∧
    -Real.log (500000000000 / 1318181818181) ≤ (484700279 / 500000000) := by
  have h := checkLog_sound (w := (318181818181 / 2318181818181)) (n := 12)
    (lo := (4316459 / 15625000)) (hi := (276253377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1318181818181 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1318181818181 / 1000000000000) = 1/(500000000000 / 1318181818181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11867 : Bounds (242350139 / 250000000) (484700279 / 500000000) (Real.log (1318181818181 / 500000000000)) := by
  have h := reflection_log_11867_neg
  have he : Real.log (1318181818181 / 500000000000) = -Real.log (500000000000 / 1318181818181) := by
    rw [show ((1318181818181 / 500000000000) : ℝ) = ((500000000000 / 1318181818181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11868_neg : (97190981 / 100000000) ≤ -Real.log (500000000000 / 1321493624773) ∧
    -Real.log (500000000000 / 1321493624773) ≤ (242977453 / 250000000) := by
  have h := checkLog_sound (w := (321493624773 / 2321493624773)) (n := 12)
    (lo := (27876263 / 100000000)) (hi := (278762631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1321493624773 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1321493624773 / 1000000000000) = 1/(500000000000 / 1321493624773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11868 : Bounds (97190981 / 100000000) (242977453 / 250000000) (Real.log (1321493624773 / 500000000000)) := by
  have h := reflection_log_11868_neg
  have he : Real.log (1321493624773 / 500000000000) = -Real.log (500000000000 / 1321493624773) := by
    rw [show ((1321493624773 / 500000000000) : ℝ) = ((500000000000 / 1321493624773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11869_neg : (93235479 / 250000000) ≤ -Real.log (250 / 363) ∧
    -Real.log (250 / 363) ≤ (372941917 / 1000000000) := by
  have h := checkLog_sound (w := (113 / 613)) (n := 12)
    (lo := (93235479 / 250000000)) (hi := (372941917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363 / 250) = 1/(250 / 363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11869 : Bounds (93235479 / 250000000) (372941917 / 1000000000) (Real.log (363 / 250)) := by
  have h := reflection_log_11869_neg
  have he : Real.log (363 / 250) = -Real.log (250 / 363) := by
    rw [show ((363 / 250) : ℝ) = ((250 / 363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11870_neg : (75184999 / 125000000) ≤ -Real.log (137 / 250) ∧
    -Real.log (137 / 250) ≤ (601479993 / 1000000000) := by
  have h := checkLog_sound (w := (113 / 387)) (n := 12)
    (lo := (75184999 / 125000000)) (hi := (601479993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 137) = 1/(137 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11870 : Bounds (-601479993 / 1000000000) (-75184999 / 125000000) (Real.log (137 / 250)) := by
  have h := reflection_log_11870_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11871_neg : (451897 / 1000000000) ≤ -Real.log (250000 / 250113) ∧
    -Real.log (250000 / 250113) ≤ (225949 / 500000000) := by
  have h := checkLog_sound (w := (113 / 500113)) (n := 12)
    (lo := (451897 / 1000000000)) (hi := (225949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250113 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250113 / 250000) = 1/(250000 / 250113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11871 : Bounds (451897 / 1000000000) (225949 / 500000000) (Real.log (250113 / 250000)) := by
  have h := reflection_log_11871_neg
  have he : Real.log (250113 / 250000) = -Real.log (250000 / 250113) := by
    rw [show ((250113 / 250000) : ℝ) = ((250000 / 250113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11872_neg : (226051 / 500000000) ≤ -Real.log (249887 / 250000) ∧
    -Real.log (249887 / 250000) ≤ (452103 / 1000000000) := by
  have h := checkLog_sound (w := (113 / 499887)) (n := 12)
    (lo := (226051 / 500000000)) (hi := (452103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249887) = 1/(249887 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11872 : Bounds (-452103 / 1000000000) (-226051 / 500000000) (Real.log (249887 / 250000)) := by
  have h := reflection_log_11872_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11873_neg : (210337907 / 1000000000) ≤ -Real.log (200000 / 246819) ∧
    -Real.log (200000 / 246819) ≤ (52584477 / 250000000) := by
  have h := checkLog_sound (w := (46819 / 446819)) (n := 12)
    (lo := (210337907 / 1000000000)) (hi := (52584477 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246819 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246819 / 200000) = 1/(200000 / 246819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11873 : Bounds (210337907 / 1000000000) (52584477 / 250000000) (Real.log (246819 / 200000)) := by
  have h := reflection_log_11873_neg
  have he : Real.log (246819 / 200000) = -Real.log (200000 / 246819) := by
    rw [show ((246819 / 200000) : ℝ) = ((200000 / 246819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11874_neg : (266697137 / 1000000000) ≤ -Real.log (153181 / 200000) ∧
    -Real.log (153181 / 200000) ≤ (133348569 / 500000000) := by
  have h := checkLog_sound (w := (46819 / 353181)) (n := 12)
    (lo := (266697137 / 1000000000)) (hi := (133348569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 153181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 153181) = 1/(153181 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11874 : Bounds (-133348569 / 500000000) (-266697137 / 1000000000) (Real.log (153181 / 200000)) := by
  have h := reflection_log_11874_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11875_neg : (211143841 / 1000000000) ≤ -Real.log (100000 / 123509) ∧
    -Real.log (100000 / 123509) ≤ (105571921 / 500000000) := by
  have h := checkLog_sound (w := (23509 / 223509)) (n := 12)
    (lo := (211143841 / 1000000000)) (hi := (105571921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123509 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123509 / 100000) = 1/(100000 / 123509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11875 : Bounds (211143841 / 1000000000) (105571921 / 500000000) (Real.log (123509 / 100000)) := by
  have h := reflection_log_11875_neg
  have he : Real.log (123509 / 100000) = -Real.log (100000 / 123509) := by
    rw [show ((123509 / 100000) : ℝ) = ((100000 / 123509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11876_neg : (267997099 / 1000000000) ≤ -Real.log (76491 / 100000) ∧
    -Real.log (76491 / 100000) ≤ (2679971 / 10000000) := by
  have h := checkLog_sound (w := (23509 / 176491)) (n := 12)
    (lo := (267997099 / 1000000000)) (hi := (2679971 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 76491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 76491) = 1/(76491 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11876 : Bounds (-2679971 / 10000000) (-267997099 / 1000000000) (Real.log (76491 / 100000)) := by
  have h := reflection_log_11876_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11877_neg : (56853257 / 1000000000) ≤ -Real.log (9447326919 / 10000000000) ∧
    -Real.log (9447326919 / 10000000000) ≤ (28426629 / 500000000) := by
  have h := checkLog_sound (w := (552673081 / 19447326919)) (n := 12)
    (lo := (56853257 / 1000000000)) (hi := (28426629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9447326919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9447326919) = 1/(9447326919 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11877 : Bounds (-28426629 / 500000000) (-56853257 / 1000000000) (Real.log (9447326919 / 10000000000)) := by
  have h := reflection_log_11877_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11878_neg : (56359229 / 1000000000) ≤ -Real.log (37807981239 / 40000000000) ∧
    -Real.log (37807981239 / 40000000000) ≤ (5635923 / 100000000) := by
  have h := checkLog_sound (w := (2192018761 / 77807981239)) (n := 12)
    (lo := (56359229 / 1000000000)) (hi := (5635923 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37807981239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37807981239) = 1/(37807981239 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11878 : Bounds (-5635923 / 100000000) (-56359229 / 1000000000) (Real.log (37807981239 / 40000000000)) := by
  have h := reflection_log_11878_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11879_neg : (95407009 / 200000000) ≤ -Real.log (500000000000 / 805644955967) ∧
    -Real.log (500000000000 / 805644955967) ≤ (238517523 / 500000000) := by
  have h := checkLog_sound (w := (305644955967 / 1305644955967)) (n := 12)
    (lo := (95407009 / 200000000)) (hi := (238517523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((805644955967 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(805644955967 / 500000000000) = 1/(500000000000 / 805644955967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11879 : Bounds (95407009 / 200000000) (238517523 / 500000000) (Real.log (805644955967 / 500000000000)) := by
  have h := reflection_log_11879_neg
  have he : Real.log (805644955967 / 500000000000) = -Real.log (500000000000 / 805644955967) := by
    rw [show ((805644955967 / 500000000000) : ℝ) = ((500000000000 / 805644955967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11880_neg : (479140941 / 1000000000) ≤ -Real.log (3906250000 / 6307369903) ∧
    -Real.log (3906250000 / 6307369903) ≤ (239570471 / 500000000) := by
  have h := checkLog_sound (w := (2401119903 / 10213619903)) (n := 12)
    (lo := (479140941 / 1000000000)) (hi := (239570471 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6307369903 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6307369903 / 3906250000) = 1/(3906250000 / 6307369903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11880 : Bounds (479140941 / 1000000000) (239570471 / 500000000) (Real.log (6307369903 / 3906250000)) := by
  have h := reflection_log_11880_neg
  have he : Real.log (6307369903 / 3906250000) = -Real.log (3906250000 / 6307369903) := by
    rw [show ((6307369903 / 3906250000) : ℝ) = ((3906250000 / 6307369903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11881_neg : (97190981 / 100000000) ≤ -Real.log (125000000000 / 330373406193) ∧
    -Real.log (125000000000 / 330373406193) ≤ (242977453 / 250000000) := by
  have h := checkLog_sound (w := (80373406193 / 580373406193)) (n := 12)
    (lo := (27876263 / 100000000)) (hi := (278762631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330373406193 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(330373406193 / 250000000000) = 1/(125000000000 / 330373406193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11881 : Bounds (97190981 / 100000000) (242977453 / 250000000) (Real.log (330373406193 / 125000000000)) := by
  have h := reflection_log_11881_neg
  have he : Real.log (330373406193 / 125000000000) = -Real.log (125000000000 / 330373406193) := by
    rw [show ((330373406193 / 125000000000) : ℝ) = ((125000000000 / 330373406193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11882_neg : (974421907 / 1000000000) ≤ -Real.log (500000000000 / 1324817518249) ∧
    -Real.log (500000000000 / 1324817518249) ≤ (974421909 / 1000000000) := by
  have h := checkLog_sound (w := (324817518249 / 2324817518249)) (n := 12)
    (lo := (281274727 / 1000000000)) (hi := (35159341 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1324817518249 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1324817518249 / 1000000000000) = 1/(500000000000 / 1324817518249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11882 : Bounds (974421907 / 1000000000) (974421909 / 1000000000) (Real.log (1324817518249 / 500000000000)) := by
  have h := reflection_log_11882_neg
  have he : Real.log (1324817518249 / 500000000000) = -Real.log (500000000000 / 1324817518249) := by
    rw [show ((1324817518249 / 500000000000) : ℝ) = ((500000000000 / 1324817518249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11883_neg : (23351899 / 62500000) ≤ -Real.log (1000 / 1453) ∧
    -Real.log (1000 / 1453) ≤ (74726077 / 200000000) := by
  have h := checkLog_sound (w := (453 / 2453)) (n := 12)
    (lo := (23351899 / 62500000)) (hi := (74726077 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1453 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1453 / 1000) = 1/(1000 / 1453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11883 : Bounds (23351899 / 62500000) (74726077 / 200000000) (Real.log (1453 / 1000)) := by
  have h := reflection_log_11883_neg
  have he : Real.log (1453 / 1000) = -Real.log (1000 / 1453) := by
    rw [show ((1453 / 1000) : ℝ) = ((1000 / 1453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11884_neg : (150826619 / 250000000) ≤ -Real.log (547 / 1000) ∧
    -Real.log (547 / 1000) ≤ (603306477 / 1000000000) := by
  have h := checkLog_sound (w := (453 / 1547)) (n := 12)
    (lo := (150826619 / 250000000)) (hi := (603306477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 547) = 1/(547 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11884 : Bounds (-603306477 / 1000000000) (-150826619 / 250000000) (Real.log (547 / 1000)) := by
  have h := reflection_log_11884_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11885_neg : (452897 / 1000000000) ≤ -Real.log (1000000 / 1000453) ∧
    -Real.log (1000000 / 1000453) ≤ (226449 / 500000000) := by
  have h := checkLog_sound (w := (453 / 2000453)) (n := 12)
    (lo := (452897 / 1000000000)) (hi := (226449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000453 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000453 / 1000000) = 1/(1000000 / 1000453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11885 : Bounds (452897 / 1000000000) (226449 / 500000000) (Real.log (1000453 / 1000000)) := by
  have h := reflection_log_11885_neg
  have he : Real.log (1000453 / 1000000) = -Real.log (1000000 / 1000453) := by
    rw [show ((1000453 / 1000000) : ℝ) = ((1000000 / 1000453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11886_neg : (226551 / 500000000) ≤ -Real.log (999547 / 1000000) ∧
    -Real.log (999547 / 1000000) ≤ (453103 / 1000000000) := by
  have h := checkLog_sound (w := (453 / 1999547)) (n := 12)
    (lo := (226551 / 500000000)) (hi := (453103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999547) = 1/(999547 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11886 : Bounds (-453103 / 1000000000) (-226551 / 500000000) (Real.log (999547 / 1000000)) := by
  have h := reflection_log_11886_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11887_neg : (52698097 / 250000000) ≤ -Real.log (31250 / 38583) ∧
    -Real.log (31250 / 38583) ≤ (210792389 / 1000000000) := by
  have h := checkLog_sound (w := (7333 / 69833)) (n := 12)
    (lo := (52698097 / 250000000)) (hi := (210792389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38583 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38583 / 31250) = 1/(31250 / 38583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11887 : Bounds (52698097 / 250000000) (210792389 / 1000000000) (Real.log (38583 / 31250)) := by
  have h := reflection_log_11887_neg
  have he : Real.log (38583 / 31250) = -Real.log (31250 / 38583) := by
    rw [show ((38583 / 31250) : ℝ) = ((31250 / 38583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11888_neg : (267429873 / 1000000000) ≤ -Real.log (23917 / 31250) ∧
    -Real.log (23917 / 31250) ≤ (133714937 / 500000000) := by
  have h := checkLog_sound (w := (7333 / 55167)) (n := 12)
    (lo := (267429873 / 1000000000)) (hi := (133714937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 23917) = 1/(23917 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11888 : Bounds (-133714937 / 500000000) (-267429873 / 1000000000) (Real.log (23917 / 31250)) := by
  have h := reflection_log_11888_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11889_neg : (42319753 / 200000000) ≤ -Real.log (250000 / 308913) ∧
    -Real.log (250000 / 308913) ≤ (105799383 / 500000000) := by
  have h := checkLog_sound (w := (58913 / 558913)) (n := 12)
    (lo := (42319753 / 200000000)) (hi := (105799383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308913 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(308913 / 250000) = 1/(250000 / 308913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11889 : Bounds (42319753 / 200000000) (105799383 / 500000000) (Real.log (308913 / 250000)) := by
  have h := reflection_log_11889_neg
  have he : Real.log (308913 / 250000) = -Real.log (250000 / 308913) := by
    rw [show ((308913 / 250000) : ℝ) = ((250000 / 308913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11890_neg : (4198939 / 15625000) ≤ -Real.log (191087 / 250000) ∧
    -Real.log (191087 / 250000) ≤ (268732097 / 1000000000) := by
  have h := checkLog_sound (w := (58913 / 441087)) (n := 12)
    (lo := (4198939 / 15625000)) (hi := (268732097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 191087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 191087) = 1/(191087 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11890 : Bounds (-268732097 / 1000000000) (-4198939 / 15625000) (Real.log (191087 / 250000)) := by
  have h := reflection_log_11890_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11891_neg : (5713333 / 100000000) ≤ -Real.log (59029258431 / 62500000000) ∧
    -Real.log (59029258431 / 62500000000) ≤ (57133331 / 1000000000) := by
  have h := checkLog_sound (w := (3470741569 / 121529258431)) (n := 12)
    (lo := (5713333 / 100000000)) (hi := (57133331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59029258431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59029258431) = 1/(59029258431 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11891 : Bounds (-57133331 / 1000000000) (-5713333 / 100000000) (Real.log (59029258431 / 62500000000)) := by
  have h := reflection_log_11891_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11892_neg : (14159371 / 250000000) ≤ -Real.log (922789611 / 976562500) ∧
    -Real.log (922789611 / 976562500) ≤ (11327497 / 200000000) := by
  have h := checkLog_sound (w := (53772889 / 1899352111)) (n := 12)
    (lo := (14159371 / 250000000)) (hi := (11327497 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 922789611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 922789611) = 1/(922789611 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11892 : Bounds (-11327497 / 200000000) (-14159371 / 250000000) (Real.log (922789611 / 976562500)) := by
  have h := reflection_log_11892_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11893_neg : (478222261 / 1000000000) ≤ -Real.log (250000000000 / 403300999289) ∧
    -Real.log (250000000000 / 403300999289) ≤ (239111131 / 500000000) := by
  have h := checkLog_sound (w := (153300999289 / 653300999289)) (n := 12)
    (lo := (478222261 / 1000000000)) (hi := (239111131 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((403300999289 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(403300999289 / 250000000000) = 1/(250000000000 / 403300999289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11893 : Bounds (478222261 / 1000000000) (239111131 / 500000000) (Real.log (403300999289 / 250000000000)) := by
  have h := reflection_log_11893_neg
  have he : Real.log (403300999289 / 250000000000) = -Real.log (250000000000 / 403300999289) := by
    rw [show ((403300999289 / 250000000000) : ℝ) = ((250000000000 / 403300999289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11894_neg : (240165431 / 500000000) ≤ -Real.log (500000000000 / 808304594243) ∧
    -Real.log (500000000000 / 808304594243) ≤ (480330863 / 1000000000) := by
  have h := checkLog_sound (w := (308304594243 / 1308304594243)) (n := 12)
    (lo := (240165431 / 500000000)) (hi := (480330863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((808304594243 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(808304594243 / 500000000000) = 1/(500000000000 / 808304594243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11894 : Bounds (240165431 / 500000000) (480330863 / 1000000000) (Real.log (808304594243 / 500000000000)) := by
  have h := reflection_log_11894_neg
  have he : Real.log (808304594243 / 500000000000) = -Real.log (500000000000 / 808304594243) := by
    rw [show ((808304594243 / 500000000000) : ℝ) = ((500000000000 / 808304594243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11895_neg : (974421907 / 1000000000) ≤ -Real.log (62500000000 / 165602189781) ∧
    -Real.log (62500000000 / 165602189781) ≤ (974421909 / 1000000000) := by
  have h := checkLog_sound (w := (40602189781 / 290602189781)) (n := 12)
    (lo := (281274727 / 1000000000)) (hi := (35159341 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165602189781 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(165602189781 / 125000000000) = 1/(62500000000 / 165602189781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11895 : Bounds (974421907 / 1000000000) (974421909 / 1000000000) (Real.log (165602189781 / 62500000000)) := by
  have h := reflection_log_11895_neg
  have he : Real.log (165602189781 / 62500000000) = -Real.log (62500000000 / 165602189781) := by
    rw [show ((165602189781 / 62500000000) : ℝ) = ((62500000000 / 165602189781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11896_neg : (48846843 / 50000000) ≤ -Real.log (5000000000 / 13281535649) ∧
    -Real.log (5000000000 / 13281535649) ≤ (488468431 / 500000000) := by
  have h := checkLog_sound (w := (3281535649 / 23281535649)) (n := 12)
    (lo := (3547371 / 12500000)) (hi := (283789681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13281535649 / 10000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(13281535649 / 10000000000) = 1/(5000000000 / 13281535649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11896 : Bounds (48846843 / 50000000) (488468431 / 500000000) (Real.log (13281535649 / 5000000000)) := by
  have h := reflection_log_11896_neg
  have he : Real.log (13281535649 / 5000000000) = -Real.log (5000000000 / 13281535649) := by
    rw [show ((13281535649 / 5000000000) : ℝ) = ((5000000000 / 13281535649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11897_neg : (374318379 / 1000000000) ≤ -Real.log (500 / 727) ∧
    -Real.log (500 / 727) ≤ (18715919 / 50000000) := by
  have h := checkLog_sound (w := (227 / 1227)) (n := 12)
    (lo := (374318379 / 1000000000)) (hi := (18715919 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727 / 500) = 1/(500 / 727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11897 : Bounds (374318379 / 1000000000) (18715919 / 50000000) (Real.log (727 / 500)) := by
  have h := reflection_log_11897_neg
  have he : Real.log (727 / 500) = -Real.log (500 / 727) := by
    rw [show ((727 / 500) : ℝ) = ((500 / 727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11898_neg : (605136303 / 1000000000) ≤ -Real.log (273 / 500) ∧
    -Real.log (273 / 500) ≤ (37821019 / 62500000) := by
  have h := checkLog_sound (w := (227 / 773)) (n := 12)
    (lo := (605136303 / 1000000000)) (hi := (37821019 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 273) = 1/(273 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11898 : Bounds (-37821019 / 62500000) (-605136303 / 1000000000) (Real.log (273 / 500)) := by
  have h := reflection_log_11898_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11899_neg : (56737 / 125000000) ≤ -Real.log (500000 / 500227) ∧
    -Real.log (500000 / 500227) ≤ (453897 / 1000000000) := by
  have h := checkLog_sound (w := (227 / 1000227)) (n := 12)
    (lo := (56737 / 125000000)) (hi := (453897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500227 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500227 / 500000) = 1/(500000 / 500227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11899 : Bounds (56737 / 125000000) (453897 / 1000000000) (Real.log (500227 / 500000)) := by
  have h := reflection_log_11899_neg
  have he : Real.log (500227 / 500000) = -Real.log (500000 / 500227) := by
    rw [show ((500227 / 500000) : ℝ) = ((500000 / 500227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11900_neg : (454103 / 1000000000) ≤ -Real.log (499773 / 500000) ∧
    -Real.log (499773 / 500000) ≤ (56763 / 125000000) := by
  have h := checkLog_sound (w := (227 / 999773)) (n := 12)
    (lo := (454103 / 1000000000)) (hi := (56763 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499773) = 1/(499773 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11900 : Bounds (-56763 / 125000000) (-454103 / 1000000000) (Real.log (499773 / 500000)) := by
  have h := reflection_log_11900_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11901_neg : (211246663 / 1000000000) ≤ -Real.log (1000000 / 1235217) ∧
    -Real.log (1000000 / 1235217) ≤ (26405833 / 125000000) := by
  have h := checkLog_sound (w := (235217 / 2235217)) (n := 12)
    (lo := (211246663 / 1000000000)) (hi := (26405833 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1235217 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1235217 / 1000000) = 1/(1000000 / 1235217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11901 : Bounds (211246663 / 1000000000) (26405833 / 125000000) (Real.log (1235217 / 1000000)) := by
  have h := reflection_log_11901_neg
  have he : Real.log (1235217 / 1000000) = -Real.log (1000000 / 1235217) := by
    rw [show ((1235217 / 1000000) : ℝ) = ((1000000 / 1235217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11902_neg : (53632629 / 200000000) ≤ -Real.log (764783 / 1000000) ∧
    -Real.log (764783 / 1000000) ≤ (134081573 / 500000000) := by
  have h := checkLog_sound (w := (235217 / 1764783)) (n := 12)
    (lo := (53632629 / 200000000)) (hi := (134081573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 764783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 764783) = 1/(764783 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11902 : Bounds (-134081573 / 500000000) (-53632629 / 200000000) (Real.log (764783 / 1000000)) := by
  have h := reflection_log_11902_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11903_neg : (212053483 / 1000000000) ≤ -Real.log (500000 / 618107) ∧
    -Real.log (500000 / 618107) ≤ (53013371 / 250000000) := by
  have h := checkLog_sound (w := (118107 / 1118107)) (n := 12)
    (lo := (212053483 / 1000000000)) (hi := (53013371 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((618107 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(618107 / 500000) = 1/(500000 / 618107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11903 : Bounds (212053483 / 1000000000) (53013371 / 250000000) (Real.log (618107 / 500000)) := by
  have h := reflection_log_11903_neg
  have he : Real.log (618107 / 500000) = -Real.log (500000 / 618107) := by
    rw [show ((618107 / 500000) : ℝ) = ((500000 / 618107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0186 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11904_neg : (269467633 / 1000000000) ≤ -Real.log (381893 / 500000) ∧
    -Real.log (381893 / 500000) ≤ (134733817 / 500000000) := by
  have h := checkLog_sound (w := (118107 / 881893)) (n := 12)
    (lo := (269467633 / 1000000000)) (hi := (134733817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 381893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 381893) = 1/(381893 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11904 : Bounds (-134733817 / 500000000) (-269467633 / 1000000000) (Real.log (381893 / 500000)) := by
  have h := reflection_log_11904_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11905_neg : (1148283 / 20000000) ≤ -Real.log (236050736551 / 250000000000) ∧
    -Real.log (236050736551 / 250000000000) ≤ (57414151 / 1000000000) := by
  have h := checkLog_sound (w := (13949263449 / 486050736551)) (n := 12)
    (lo := (1148283 / 20000000)) (hi := (57414151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 236050736551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 236050736551) = 1/(236050736551 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11905 : Bounds (-57414151 / 1000000000) (-1148283 / 20000000) (Real.log (236050736551 / 250000000000)) := by
  have h := reflection_log_11905_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11906_neg : (28458241 / 500000000) ≤ -Real.log (944672962911 / 1000000000000) ∧
    -Real.log (944672962911 / 1000000000000) ≤ (56916483 / 1000000000) := by
  have h := checkLog_sound (w := (55327037089 / 1944672962911)) (n := 12)
    (lo := (28458241 / 500000000)) (hi := (56916483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 944672962911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 944672962911) = 1/(944672962911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11906 : Bounds (-56916483 / 1000000000) (-28458241 / 500000000) (Real.log (944672962911 / 1000000000000)) := by
  have h := reflection_log_11906_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11907_neg : (29963113 / 62500000) ≤ -Real.log (2000000000 / 3230241781) ∧
    -Real.log (2000000000 / 3230241781) ≤ (479409809 / 1000000000) := by
  have h := checkLog_sound (w := (1230241781 / 5230241781)) (n := 12)
    (lo := (29963113 / 62500000)) (hi := (479409809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3230241781 / 2000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3230241781 / 2000000000) = 1/(2000000000 / 3230241781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11907 : Bounds (29963113 / 62500000) (479409809 / 1000000000) (Real.log (3230241781 / 2000000000)) := by
  have h := reflection_log_11907_neg
  have he : Real.log (3230241781 / 2000000000) = -Real.log (2000000000 / 3230241781) := by
    rw [show ((3230241781 / 2000000000) : ℝ) = ((2000000000 / 3230241781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11908_neg : (120380279 / 250000000) ≤ -Real.log (7812500000 / 12644800867) ∧
    -Real.log (7812500000 / 12644800867) ≤ (481521117 / 1000000000) := by
  have h := checkLog_sound (w := (4832300867 / 20457300867)) (n := 12)
    (lo := (120380279 / 250000000)) (hi := (481521117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12644800867 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12644800867 / 7812500000) = 1/(7812500000 / 12644800867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11908 : Bounds (120380279 / 250000000) (481521117 / 1000000000) (Real.log (12644800867 / 7812500000)) := by
  have h := reflection_log_11908_neg
  have he : Real.log (12644800867 / 7812500000) = -Real.log (7812500000 / 12644800867) := by
    rw [show ((12644800867 / 7812500000) : ℝ) = ((7812500000 / 12644800867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11909_neg : (48846843 / 50000000) ≤ -Real.log (500000000000 / 1328153564899) ∧
    -Real.log (500000000000 / 1328153564899) ≤ (488468431 / 500000000) := by
  have h := checkLog_sound (w := (328153564899 / 2328153564899)) (n := 12)
    (lo := (3547371 / 12500000)) (hi := (283789681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1328153564899 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1328153564899 / 1000000000000) = 1/(500000000000 / 1328153564899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11909 : Bounds (48846843 / 50000000) (488468431 / 500000000) (Real.log (1328153564899 / 500000000000)) := by
  have h := reflection_log_11909_neg
  have he : Real.log (1328153564899 / 500000000000) = -Real.log (500000000000 / 1328153564899) := by
    rw [show ((1328153564899 / 500000000000) : ℝ) = ((500000000000 / 1328153564899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11910_neg : (979454681 / 1000000000) ≤ -Real.log (250000000000 / 665750915751) ∧
    -Real.log (250000000000 / 665750915751) ≤ (979454683 / 1000000000) := by
  have h := checkLog_sound (w := (165750915751 / 1165750915751)) (n := 12)
    (lo := (286307501 / 1000000000)) (hi := (143153751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((665750915751 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(665750915751 / 500000000000) = 1/(250000000000 / 665750915751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11910 : Bounds (979454681 / 1000000000) (979454683 / 1000000000) (Real.log (665750915751 / 250000000000)) := by
  have h := reflection_log_11910_neg
  have he : Real.log (665750915751 / 250000000000) = -Real.log (250000000000 / 665750915751) := by
    rw [show ((665750915751 / 250000000000) : ℝ) = ((250000000000 / 665750915751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11911_neg : (3750059 / 10000000) ≤ -Real.log (200 / 291) ∧
    -Real.log (200 / 291) ≤ (375005901 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 491)) (n := 12)
    (lo := (3750059 / 10000000)) (hi := (375005901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291 / 200) = 1/(200 / 291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11911 : Bounds (3750059 / 10000000) (375005901 / 1000000000) (Real.log (291 / 200)) := by
  have h := reflection_log_11911_neg
  have he : Real.log (291 / 200) = -Real.log (200 / 291) := by
    rw [show ((291 / 200) : ℝ) = ((200 / 291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11912_neg : (151742371 / 250000000) ≤ -Real.log (109 / 200) ∧
    -Real.log (109 / 200) ≤ (121393897 / 200000000) := by
  have h := checkLog_sound (w := (91 / 309)) (n := 12)
    (lo := (151742371 / 250000000)) (hi := (121393897 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 109) = 1/(109 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11912 : Bounds (-121393897 / 200000000) (-151742371 / 250000000) (Real.log (109 / 200)) := by
  have h := reflection_log_11912_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11913_neg : (28431 / 62500000) ≤ -Real.log (200000 / 200091) ∧
    -Real.log (200000 / 200091) ≤ (454897 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 400091)) (n := 12)
    (lo := (28431 / 62500000)) (hi := (454897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200091 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200091 / 200000) = 1/(200000 / 200091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11913 : Bounds (28431 / 62500000) (454897 / 1000000000) (Real.log (200091 / 200000)) := by
  have h := reflection_log_11913_neg
  have he : Real.log (200091 / 200000) = -Real.log (200000 / 200091) := by
    rw [show ((200091 / 200000) : ℝ) = ((200000 / 200091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11914_neg : (455103 / 1000000000) ≤ -Real.log (199909 / 200000) ∧
    -Real.log (199909 / 200000) ≤ (7111 / 15625000) := by
  have h := checkLog_sound (w := (91 / 399909)) (n := 12)
    (lo := (455103 / 1000000000)) (hi := (7111 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199909) = 1/(199909 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11914 : Bounds (-7111 / 15625000) (-455103 / 1000000000) (Real.log (199909 / 200000)) := by
  have h := reflection_log_11914_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11915_neg : (10585077 / 50000000) ≤ -Real.log (1000000 / 1235779) ∧
    -Real.log (1000000 / 1235779) ≤ (211701541 / 1000000000) := by
  have h := checkLog_sound (w := (235779 / 2235779)) (n := 12)
    (lo := (10585077 / 50000000)) (hi := (211701541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1235779 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1235779 / 1000000) = 1/(1000000 / 1235779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11915 : Bounds (10585077 / 50000000) (211701541 / 1000000000) (Real.log (1235779 / 1000000)) := by
  have h := reflection_log_11915_neg
  have he : Real.log (1235779 / 1000000) = -Real.log (1000000 / 1235779) := by
    rw [show ((1235779 / 1000000) : ℝ) = ((1000000 / 1235779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11916_neg : (33612283 / 125000000) ≤ -Real.log (764221 / 1000000) ∧
    -Real.log (764221 / 1000000) ≤ (53779653 / 200000000) := by
  have h := checkLog_sound (w := (235779 / 1764221)) (n := 12)
    (lo := (33612283 / 125000000)) (hi := (53779653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 764221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 764221) = 1/(764221 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11916 : Bounds (-53779653 / 200000000) (-33612283 / 125000000) (Real.log (764221 / 1000000)) := by
  have h := reflection_log_11916_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11917_neg : (106254401 / 500000000) ≤ -Real.log (1000000 / 1236777) ∧
    -Real.log (1000000 / 1236777) ≤ (212508803 / 1000000000) := by
  have h := checkLog_sound (w := (236777 / 2236777)) (n := 12)
    (lo := (106254401 / 500000000)) (hi := (212508803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1236777 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1236777 / 1000000) = 1/(1000000 / 1236777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11917 : Bounds (106254401 / 500000000) (212508803 / 1000000000) (Real.log (1236777 / 1000000)) := by
  have h := reflection_log_11917_neg
  have he : Real.log (1236777 / 1000000) = -Real.log (1000000 / 1236777) := by
    rw [show ((1236777 / 1000000) : ℝ) = ((1000000 / 1236777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11918_neg : (270205023 / 1000000000) ≤ -Real.log (763223 / 1000000) ∧
    -Real.log (763223 / 1000000) ≤ (8443907 / 31250000) := by
  have h := checkLog_sound (w := (236777 / 1763223)) (n := 12)
    (lo := (270205023 / 1000000000)) (hi := (8443907 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 763223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 763223) = 1/(763223 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11918 : Bounds (-8443907 / 31250000) (-270205023 / 1000000000) (Real.log (763223 / 1000000)) := by
  have h := reflection_log_11918_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11919_neg : (2884811 / 50000000) ≤ -Real.log (943936652271 / 1000000000000) ∧
    -Real.log (943936652271 / 1000000000000) ≤ (57696221 / 1000000000) := by
  have h := checkLog_sound (w := (56063347729 / 1943936652271)) (n := 12)
    (lo := (2884811 / 50000000)) (hi := (57696221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 943936652271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 943936652271) = 1/(943936652271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11919 : Bounds (-57696221 / 1000000000) (-2884811 / 50000000) (Real.log (943936652271 / 1000000000000)) := by
  have h := reflection_log_11919_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11920_neg : (14299181 / 250000000) ≤ -Real.log (944408263159 / 1000000000000) ∧
    -Real.log (944408263159 / 1000000000000) ≤ (2287869 / 40000000) := by
  have h := checkLog_sound (w := (55591736841 / 1944408263159)) (n := 12)
    (lo := (14299181 / 250000000)) (hi := (2287869 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 944408263159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 944408263159) = 1/(944408263159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11920 : Bounds (-2287869 / 40000000) (-14299181 / 250000000) (Real.log (944408263159 / 1000000000000)) := by
  have h := reflection_log_11920_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11921_neg : (96119961 / 200000000) ≤ -Real.log (500000000000 / 808522011303) ∧
    -Real.log (500000000000 / 808522011303) ≤ (240299903 / 500000000) := by
  have h := checkLog_sound (w := (308522011303 / 1308522011303)) (n := 12)
    (lo := (96119961 / 200000000)) (hi := (240299903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((808522011303 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(808522011303 / 500000000000) = 1/(500000000000 / 808522011303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11921 : Bounds (96119961 / 200000000) (240299903 / 500000000) (Real.log (808522011303 / 500000000000)) := by
  have h := reflection_log_11921_neg
  have he : Real.log (808522011303 / 500000000000) = -Real.log (500000000000 / 808522011303) := by
    rw [show ((808522011303 / 500000000000) : ℝ) = ((500000000000 / 808522011303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11922_neg : (19308553 / 40000000) ≤ -Real.log (500000000000 / 810233051153) ∧
    -Real.log (500000000000 / 810233051153) ≤ (241356913 / 500000000) := by
  have h := checkLog_sound (w := (310233051153 / 1310233051153)) (n := 12)
    (lo := (19308553 / 40000000)) (hi := (241356913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((810233051153 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(810233051153 / 500000000000) = 1/(500000000000 / 810233051153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11922 : Bounds (19308553 / 40000000) (241356913 / 500000000) (Real.log (810233051153 / 500000000000)) := by
  have h := reflection_log_11922_neg
  have he : Real.log (810233051153 / 500000000000) = -Real.log (500000000000 / 810233051153) := by
    rw [show ((810233051153 / 500000000000) : ℝ) = ((500000000000 / 810233051153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11923_neg : (979454681 / 1000000000) ≤ -Real.log (500000000000 / 1331501831501) ∧
    -Real.log (500000000000 / 1331501831501) ≤ (979454683 / 1000000000) := by
  have h := checkLog_sound (w := (331501831501 / 2331501831501)) (n := 12)
    (lo := (286307501 / 1000000000)) (hi := (143153751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1331501831501 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1331501831501 / 1000000000000) = 1/(500000000000 / 1331501831501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11923 : Bounds (979454681 / 1000000000) (979454683 / 1000000000) (Real.log (1331501831501 / 500000000000)) := by
  have h := reflection_log_11923_neg
  have he : Real.log (1331501831501 / 500000000000) = -Real.log (500000000000 / 1331501831501) := by
    rw [show ((1331501831501 / 500000000000) : ℝ) = ((500000000000 / 1331501831501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11924_neg : (122746923 / 125000000) ≤ -Real.log (250000000000 / 667431192661) ∧
    -Real.log (250000000000 / 667431192661) ≤ (490987693 / 500000000) := by
  have h := checkLog_sound (w := (167431192661 / 1167431192661)) (n := 12)
    (lo := (72207051 / 250000000)) (hi := (57765641 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667431192661 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(667431192661 / 500000000000) = 1/(250000000000 / 667431192661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11924 : Bounds (122746923 / 125000000) (490987693 / 500000000) (Real.log (667431192661 / 250000000000)) := by
  have h := reflection_log_11924_neg
  have he : Real.log (667431192661 / 250000000000) = -Real.log (250000000000 / 667431192661) := by
    rw [show ((667431192661 / 250000000000) : ℝ) = ((250000000000 / 667431192661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11925_neg : (375692949 / 1000000000) ≤ -Real.log (125 / 182) ∧
    -Real.log (125 / 182) ≤ (7513859 / 20000000) := by
  have h := checkLog_sound (w := (57 / 307)) (n := 12)
    (lo := (375692949 / 1000000000)) (hi := (7513859 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182 / 125) = 1/(125 / 182) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11925 : Bounds (375692949 / 1000000000) (7513859 / 20000000) (Real.log (182 / 125)) := by
  have h := reflection_log_11925_neg
  have he : Real.log (182 / 125) = -Real.log (125 / 182) := by
    rw [show ((182 / 125) : ℝ) = ((125 / 182) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11926_neg : (38050377 / 62500000) ≤ -Real.log (68 / 125) ∧
    -Real.log (68 / 125) ≤ (608806033 / 1000000000) := by
  have h := checkLog_sound (w := (57 / 193)) (n := 12)
    (lo := (38050377 / 62500000)) (hi := (608806033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 68) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 68) = 1/(68 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11926 : Bounds (-608806033 / 1000000000) (-38050377 / 62500000) (Real.log (68 / 125)) := by
  have h := reflection_log_11926_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11927_neg : (56987 / 125000000) ≤ -Real.log (125000 / 125057) ∧
    -Real.log (125000 / 125057) ≤ (455897 / 1000000000) := by
  have h := checkLog_sound (w := (57 / 250057)) (n := 12)
    (lo := (56987 / 125000000)) (hi := (455897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125057 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125057 / 125000) = 1/(125000 / 125057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11927 : Bounds (56987 / 125000000) (455897 / 1000000000) (Real.log (125057 / 125000)) := by
  have h := reflection_log_11927_neg
  have he : Real.log (125057 / 125000) = -Real.log (125000 / 125057) := by
    rw [show ((125057 / 125000) : ℝ) = ((125000 / 125057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11928_neg : (456103 / 1000000000) ≤ -Real.log (124943 / 125000) ∧
    -Real.log (124943 / 125000) ≤ (57013 / 125000000) := by
  have h := checkLog_sound (w := (57 / 249943)) (n := 12)
    (lo := (456103 / 1000000000)) (hi := (57013 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124943) = 1/(124943 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11928 : Bounds (-57013 / 125000000) (-456103 / 1000000000) (Real.log (124943 / 125000)) := by
  have h := reflection_log_11928_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11929_neg : (106077701 / 500000000) ≤ -Real.log (50000 / 61817) ∧
    -Real.log (50000 / 61817) ≤ (212155403 / 1000000000) := by
  have h := checkLog_sound (w := (11817 / 111817)) (n := 12)
    (lo := (106077701 / 500000000)) (hi := (212155403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61817 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61817 / 50000) = 1/(50000 / 61817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11929 : Bounds (106077701 / 500000000) (212155403 / 1000000000) (Real.log (61817 / 50000)) := by
  have h := reflection_log_11929_neg
  have he : Real.log (61817 / 50000) = -Real.log (50000 / 61817) := by
    rw [show ((61817 / 50000) : ℝ) = ((50000 / 61817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11930_neg : (53926523 / 200000000) ≤ -Real.log (38183 / 50000) ∧
    -Real.log (38183 / 50000) ≤ (33704077 / 125000000) := by
  have h := checkLog_sound (w := (11817 / 88183)) (n := 12)
    (lo := (53926523 / 200000000)) (hi := (33704077 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 38183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 38183) = 1/(38183 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11930 : Bounds (-33704077 / 125000000) (-53926523 / 200000000) (Real.log (38183 / 50000)) := by
  have h := reflection_log_11930_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11931_neg : (106481957 / 500000000) ≤ -Real.log (50000 / 61867) ∧
    -Real.log (50000 / 61867) ≤ (42592783 / 200000000) := by
  have h := checkLog_sound (w := (11867 / 111867)) (n := 12)
    (lo := (106481957 / 500000000)) (hi := (42592783 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61867 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61867 / 50000) = 1/(50000 / 61867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11931 : Bounds (106481957 / 500000000) (42592783 / 200000000) (Real.log (61867 / 50000)) := by
  have h := reflection_log_11931_neg
  have he : Real.log (61867 / 50000) = -Real.log (50000 / 61867) := by
    rw [show ((61867 / 50000) : ℝ) = ((50000 / 61867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11932_neg : (67735739 / 250000000) ≤ -Real.log (38133 / 50000) ∧
    -Real.log (38133 / 50000) ≤ (270942957 / 1000000000) := by
  have h := checkLog_sound (w := (11867 / 88133)) (n := 12)
    (lo := (67735739 / 250000000)) (hi := (270942957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 38133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 38133) = 1/(38133 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11932 : Bounds (-270942957 / 1000000000) (-67735739 / 250000000) (Real.log (38133 / 50000)) := by
  have h := reflection_log_11932_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11933_neg : (28989521 / 500000000) ≤ -Real.log (2359174311 / 2500000000) ∧
    -Real.log (2359174311 / 2500000000) ≤ (57979043 / 1000000000) := by
  have h := checkLog_sound (w := (140825689 / 4859174311)) (n := 12)
    (lo := (28989521 / 500000000)) (hi := (57979043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2359174311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2359174311) = 1/(2359174311 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11933 : Bounds (-57979043 / 1000000000) (-28989521 / 500000000) (Real.log (2359174311 / 2500000000)) := by
  have h := reflection_log_11933_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11934_neg : (14369303 / 250000000) ≤ -Real.log (2360358511 / 2500000000) ∧
    -Real.log (2360358511 / 2500000000) ≤ (57477213 / 1000000000) := by
  have h := checkLog_sound (w := (139641489 / 4860358511)) (n := 12)
    (lo := (14369303 / 250000000)) (hi := (57477213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2360358511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2360358511) = 1/(2360358511 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11934 : Bounds (-57477213 / 1000000000) (-14369303 / 250000000) (Real.log (2360358511 / 2500000000)) := by
  have h := reflection_log_11934_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11935_neg : (481788017 / 1000000000) ≤ -Real.log (250000000000 / 404741638949) ∧
    -Real.log (250000000000 / 404741638949) ≤ (240894009 / 500000000) := by
  have h := checkLog_sound (w := (154741638949 / 654741638949)) (n := 12)
    (lo := (481788017 / 1000000000)) (hi := (240894009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((404741638949 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(404741638949 / 250000000000) = 1/(250000000000 / 404741638949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11935 : Bounds (481788017 / 1000000000) (240894009 / 500000000) (Real.log (404741638949 / 250000000000)) := by
  have h := reflection_log_11935_neg
  have he : Real.log (404741638949 / 250000000000) = -Real.log (250000000000 / 404741638949) := by
    rw [show ((404741638949 / 250000000000) : ℝ) = ((250000000000 / 404741638949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11936_neg : (48390687 / 100000000) ≤ -Real.log (50000000000 / 81120027273) ∧
    -Real.log (50000000000 / 81120027273) ≤ (483906871 / 1000000000) := by
  have h := checkLog_sound (w := (31120027273 / 131120027273)) (n := 12)
    (lo := (48390687 / 100000000)) (hi := (483906871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81120027273 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81120027273 / 50000000000) = 1/(50000000000 / 81120027273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11936 : Bounds (48390687 / 100000000) (483906871 / 1000000000) (Real.log (81120027273 / 50000000000)) := by
  have h := reflection_log_11936_neg
  have he : Real.log (81120027273 / 50000000000) = -Real.log (50000000000 / 81120027273) := by
    rw [show ((81120027273 / 50000000000) : ℝ) = ((50000000000 / 81120027273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11937_neg : (122746923 / 125000000) ≤ -Real.log (500000000000 / 1334862385321) ∧
    -Real.log (500000000000 / 1334862385321) ≤ (490987693 / 500000000) := by
  have h := checkLog_sound (w := (334862385321 / 2334862385321)) (n := 12)
    (lo := (72207051 / 250000000)) (hi := (57765641 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1334862385321 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1334862385321 / 1000000000000) = 1/(500000000000 / 1334862385321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11937 : Bounds (122746923 / 125000000) (490987693 / 500000000) (Real.log (1334862385321 / 500000000000)) := by
  have h := reflection_log_11937_neg
  have he : Real.log (1334862385321 / 500000000000) = -Real.log (500000000000 / 1334862385321) := by
    rw [show ((1334862385321 / 500000000000) : ℝ) = ((500000000000 / 1334862385321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11938_neg : (984498981 / 1000000000) ≤ -Real.log (250000000000 / 669117647059) ∧
    -Real.log (250000000000 / 669117647059) ≤ (984498983 / 1000000000) := by
  have h := checkLog_sound (w := (169117647059 / 1169117647059)) (n := 12)
    (lo := (291351801 / 1000000000)) (hi := (145675901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((669117647059 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(669117647059 / 500000000000) = 1/(250000000000 / 669117647059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11938 : Bounds (984498981 / 1000000000) (984498983 / 1000000000) (Real.log (669117647059 / 250000000000)) := by
  have h := reflection_log_11938_neg
  have he : Real.log (669117647059 / 250000000000) = -Real.log (250000000000 / 669117647059) := by
    rw [show ((669117647059 / 250000000000) : ℝ) = ((250000000000 / 669117647059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11939_neg : (376379527 / 1000000000) ≤ -Real.log (1000 / 1457) ∧
    -Real.log (1000 / 1457) ≤ (47047441 / 125000000) := by
  have h := checkLog_sound (w := (457 / 2457)) (n := 12)
    (lo := (376379527 / 1000000000)) (hi := (47047441 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1457 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1457 / 1000) = 1/(1000 / 1457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11939 : Bounds (376379527 / 1000000000) (47047441 / 125000000) (Real.log (1457 / 1000)) := by
  have h := reflection_log_11939_neg
  have he : Real.log (1457 / 1000) = -Real.log (1000 / 1457) := by
    rw [show ((1457 / 1000) : ℝ) = ((1000 / 1457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11940_neg : (610645959 / 1000000000) ≤ -Real.log (543 / 1000) ∧
    -Real.log (543 / 1000) ≤ (15266149 / 25000000) := by
  have h := checkLog_sound (w := (457 / 1543)) (n := 12)
    (lo := (610645959 / 1000000000)) (hi := (15266149 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 543) = 1/(543 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11940 : Bounds (-15266149 / 25000000) (-610645959 / 1000000000) (Real.log (543 / 1000)) := by
  have h := reflection_log_11940_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11941_neg : (91379 / 200000000) ≤ -Real.log (1000000 / 1000457) ∧
    -Real.log (1000000 / 1000457) ≤ (7139 / 15625000) := by
  have h := checkLog_sound (w := (457 / 2000457)) (n := 12)
    (lo := (91379 / 200000000)) (hi := (7139 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000457 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000457 / 1000000) = 1/(1000000 / 1000457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11941 : Bounds (91379 / 200000000) (7139 / 15625000) (Real.log (1000457 / 1000000)) := by
  have h := reflection_log_11941_neg
  have he : Real.log (1000457 / 1000000) = -Real.log (1000000 / 1000457) := by
    rw [show ((1000457 / 1000000) : ℝ) = ((1000000 / 1000457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11942_neg : (28569 / 62500000) ≤ -Real.log (999543 / 1000000) ∧
    -Real.log (999543 / 1000000) ≤ (91421 / 200000000) := by
  have h := checkLog_sound (w := (457 / 1999543)) (n := 12)
    (lo := (28569 / 62500000)) (hi := (91421 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999543) = 1/(999543 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11942 : Bounds (-91421 / 200000000) (-28569 / 62500000) (Real.log (999543 / 1000000)) := by
  have h := reflection_log_11942_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11943_neg : (106305337 / 500000000) ≤ -Real.log (1000000 / 1236903) ∧
    -Real.log (1000000 / 1236903) ≤ (8504427 / 40000000) := by
  have h := checkLog_sound (w := (236903 / 2236903)) (n := 12)
    (lo := (106305337 / 500000000)) (hi := (8504427 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1236903 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1236903 / 1000000) = 1/(1000000 / 1236903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11943 : Bounds (106305337 / 500000000) (8504427 / 40000000) (Real.log (1236903 / 1000000)) := by
  have h := reflection_log_11943_neg
  have he : Real.log (1236903 / 1000000) = -Real.log (1000000 / 1236903) := by
    rw [show ((1236903 / 1000000) : ℝ) = ((1000000 / 1236903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11944_neg : (135185063 / 500000000) ≤ -Real.log (763097 / 1000000) ∧
    -Real.log (763097 / 1000000) ≤ (270370127 / 1000000000) := by
  have h := checkLog_sound (w := (236903 / 1763097)) (n := 12)
    (lo := (135185063 / 500000000)) (hi := (270370127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 763097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 763097) = 1/(763097 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11944 : Bounds (-270370127 / 1000000000) (-135185063 / 500000000) (Real.log (763097 / 1000000)) := by
  have h := reflection_log_11944_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11945_neg : (106709813 / 500000000) ≤ -Real.log (62500 / 77369) ∧
    -Real.log (62500 / 77369) ≤ (213419627 / 1000000000) := by
  have h := checkLog_sound (w := (14869 / 139869)) (n := 12)
    (lo := (106709813 / 500000000)) (hi := (213419627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77369 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77369 / 62500) = 1/(62500 / 77369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11945 : Bounds (106709813 / 500000000) (213419627 / 1000000000) (Real.log (77369 / 62500)) := by
  have h := reflection_log_11945_neg
  have he : Real.log (77369 / 62500) = -Real.log (62500 / 77369) := by
    rw [show ((77369 / 62500) : ℝ) = ((62500 / 77369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11946_neg : (135841373 / 500000000) ≤ -Real.log (47631 / 62500) ∧
    -Real.log (47631 / 62500) ≤ (271682747 / 1000000000) := by
  have h := checkLog_sound (w := (14869 / 110131)) (n := 12)
    (lo := (135841373 / 500000000)) (hi := (271682747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 47631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 47631) = 1/(47631 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11946 : Bounds (-271682747 / 1000000000) (-135841373 / 500000000) (Real.log (47631 / 62500)) := by
  have h := reflection_log_11946_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11947_neg : (728289 / 12500000) ≤ -Real.log (3685162839 / 3906250000) ∧
    -Real.log (3685162839 / 3906250000) ≤ (58263121 / 1000000000) := by
  have h := checkLog_sound (w := (221087161 / 7591412839)) (n := 12)
    (lo := (728289 / 12500000)) (hi := (58263121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3685162839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3685162839) = 1/(3685162839 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11947 : Bounds (-58263121 / 1000000000) (-728289 / 12500000) (Real.log (3685162839 / 3906250000)) := by
  have h := reflection_log_11947_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11948_neg : (57759451 / 1000000000) ≤ -Real.log (943876968591 / 1000000000000) ∧
    -Real.log (943876968591 / 1000000000000) ≤ (14439863 / 250000000) := by
  have h := checkLog_sound (w := (56123031409 / 1943876968591)) (n := 12)
    (lo := (57759451 / 1000000000)) (hi := (14439863 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 943876968591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 943876968591) = 1/(943876968591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11948 : Bounds (-14439863 / 250000000) (-57759451 / 1000000000) (Real.log (943876968591 / 1000000000000)) := by
  have h := reflection_log_11948_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11949_neg : (301863 / 625000) ≤ -Real.log (50000000000 / 81044939241) ∧
    -Real.log (50000000000 / 81044939241) ≤ (482980801 / 1000000000) := by
  have h := checkLog_sound (w := (31044939241 / 131044939241)) (n := 12)
    (lo := (301863 / 625000)) (hi := (482980801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81044939241 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81044939241 / 50000000000) = 1/(50000000000 / 81044939241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11949 : Bounds (301863 / 625000) (482980801 / 1000000000) (Real.log (81044939241 / 50000000000)) := by
  have h := reflection_log_11949_neg
  have he : Real.log (81044939241 / 50000000000) = -Real.log (50000000000 / 81044939241) := by
    rw [show ((81044939241 / 50000000000) : ℝ) = ((50000000000 / 81044939241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11950_neg : (485102373 / 1000000000) ≤ -Real.log (500000000000 / 812170645169) ∧
    -Real.log (500000000000 / 812170645169) ≤ (242551187 / 500000000) := by
  have h := checkLog_sound (w := (312170645169 / 1312170645169)) (n := 12)
    (lo := (485102373 / 1000000000)) (hi := (242551187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((812170645169 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(812170645169 / 500000000000) = 1/(500000000000 / 812170645169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11950 : Bounds (485102373 / 1000000000) (242551187 / 500000000) (Real.log (812170645169 / 500000000000)) := by
  have h := reflection_log_11950_neg
  have he : Real.log (812170645169 / 500000000000) = -Real.log (500000000000 / 812170645169) := by
    rw [show ((812170645169 / 500000000000) : ℝ) = ((500000000000 / 812170645169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11951_neg : (984498981 / 1000000000) ≤ -Real.log (500000000000 / 1338235294117) ∧
    -Real.log (500000000000 / 1338235294117) ≤ (984498983 / 1000000000) := by
  have h := checkLog_sound (w := (338235294117 / 2338235294117)) (n := 12)
    (lo := (291351801 / 1000000000)) (hi := (145675901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1338235294117 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1338235294117 / 1000000000000) = 1/(500000000000 / 1338235294117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11951 : Bounds (984498981 / 1000000000) (984498983 / 1000000000) (Real.log (1338235294117 / 500000000000)) := by
  have h := reflection_log_11951_neg
  have he : Real.log (1338235294117 / 500000000000) = -Real.log (500000000000 / 1338235294117) := by
    rw [show ((1338235294117 / 500000000000) : ℝ) = ((500000000000 / 1338235294117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11952_neg : (197405097 / 200000000) ≤ -Real.log (62500000000 / 167702578269) ∧
    -Real.log (62500000000 / 167702578269) ≤ (987025487 / 1000000000) := by
  have h := checkLog_sound (w := (42702578269 / 292702578269)) (n := 12)
    (lo := (58775661 / 200000000)) (hi := (146939153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((167702578269 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(167702578269 / 125000000000) = 1/(62500000000 / 167702578269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11952 : Bounds (197405097 / 200000000) (987025487 / 1000000000) (Real.log (167702578269 / 62500000000)) := by
  have h := reflection_log_11952_neg
  have he : Real.log (167702578269 / 62500000000) = -Real.log (62500000000 / 167702578269) := by
    rw [show ((167702578269 / 62500000000) : ℝ) = ((62500000000 / 167702578269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11953_neg : (377065633 / 1000000000) ≤ -Real.log (500 / 729) ∧
    -Real.log (500 / 729) ≤ (188532817 / 500000000) := by
  have h := checkLog_sound (w := (229 / 1229)) (n := 12)
    (lo := (377065633 / 1000000000)) (hi := (188532817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729 / 500) = 1/(500 / 729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11953 : Bounds (377065633 / 1000000000) (188532817 / 500000000) (Real.log (729 / 500)) := by
  have h := reflection_log_11953_neg
  have he : Real.log (729 / 500) = -Real.log (500 / 729) := by
    rw [show ((729 / 500) : ℝ) = ((500 / 729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11954_neg : (612489277 / 1000000000) ≤ -Real.log (271 / 500) ∧
    -Real.log (271 / 500) ≤ (306244639 / 500000000) := by
  have h := checkLog_sound (w := (229 / 771)) (n := 12)
    (lo := (612489277 / 1000000000)) (hi := (306244639 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 271) = 1/(271 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11954 : Bounds (-306244639 / 500000000) (-612489277 / 1000000000) (Real.log (271 / 500)) := by
  have h := reflection_log_11954_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11955_neg : (91579 / 200000000) ≤ -Real.log (500000 / 500229) ∧
    -Real.log (500000 / 500229) ≤ (57237 / 125000000) := by
  have h := checkLog_sound (w := (229 / 1000229)) (n := 12)
    (lo := (91579 / 200000000)) (hi := (57237 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500229 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500229 / 500000) = 1/(500000 / 500229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11955 : Bounds (91579 / 200000000) (57237 / 125000000) (Real.log (500229 / 500000)) := by
  have h := reflection_log_11955_neg
  have he : Real.log (500229 / 500000) = -Real.log (500000 / 500229) := by
    rw [show ((500229 / 500000) : ℝ) = ((500000 / 500229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11956_neg : (57263 / 125000000) ≤ -Real.log (499771 / 500000) ∧
    -Real.log (499771 / 500000) ≤ (91621 / 200000000) := by
  have h := checkLog_sound (w := (229 / 999771)) (n := 12)
    (lo := (57263 / 125000000)) (hi := (91621 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499771) = 1/(499771 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11956 : Bounds (-91621 / 200000000) (-57263 / 125000000) (Real.log (499771 / 500000)) := by
  have h := reflection_log_11956_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11957_neg : (53266233 / 250000000) ≤ -Real.log (200000 / 247493) ∧
    -Real.log (200000 / 247493) ≤ (213064933 / 1000000000) := by
  have h := checkLog_sound (w := (47493 / 447493)) (n := 12)
    (lo := (53266233 / 250000000)) (hi := (213064933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247493 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247493 / 200000) = 1/(200000 / 247493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11957 : Bounds (53266233 / 250000000) (213064933 / 1000000000) (Real.log (247493 / 200000)) := by
  have h := reflection_log_11957_neg
  have he : Real.log (247493 / 200000) = -Real.log (200000 / 247493) := by
    rw [show ((247493 / 200000) : ℝ) = ((200000 / 247493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11958_neg : (271106869 / 1000000000) ≤ -Real.log (152507 / 200000) ∧
    -Real.log (152507 / 200000) ≤ (27110687 / 100000000) := by
  have h := checkLog_sound (w := (47493 / 352507)) (n := 12)
    (lo := (271106869 / 1000000000)) (hi := (27110687 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 152507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 152507) = 1/(152507 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11958 : Bounds (-27110687 / 100000000) (-271106869 / 1000000000) (Real.log (152507 / 200000)) := by
  have h := reflection_log_11958_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11959_neg : (53468581 / 250000000) ≤ -Real.log (1000000 / 1238467) ∧
    -Real.log (1000000 / 1238467) ≤ (8554973 / 40000000) := by
  have h := checkLog_sound (w := (238467 / 2238467)) (n := 12)
    (lo := (53468581 / 250000000)) (hi := (8554973 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1238467 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1238467 / 1000000) = 1/(1000000 / 1238467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11959 : Bounds (53468581 / 250000000) (8554973 / 40000000) (Real.log (1238467 / 1000000)) := by
  have h := reflection_log_11959_neg
  have he : Real.log (1238467 / 1000000) = -Real.log (1000000 / 1238467) := by
    rw [show ((1238467 / 1000000) : ℝ) = ((1000000 / 1238467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11960_neg : (68105443 / 250000000) ≤ -Real.log (761533 / 1000000) ∧
    -Real.log (761533 / 1000000) ≤ (272421773 / 1000000000) := by
  have h := checkLog_sound (w := (238467 / 1761533)) (n := 12)
    (lo := (68105443 / 250000000)) (hi := (272421773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 761533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 761533) = 1/(761533 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11960 : Bounds (-272421773 / 1000000000) (-68105443 / 250000000) (Real.log (761533 / 1000000)) := by
  have h := reflection_log_11960_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11961_neg : (58547447 / 1000000000) ≤ -Real.log (943133489911 / 1000000000000) ∧
    -Real.log (943133489911 / 1000000000000) ≤ (7318431 / 125000000) := by
  have h := checkLog_sound (w := (56866510089 / 1943133489911)) (n := 12)
    (lo := (58547447 / 1000000000)) (hi := (7318431 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 943133489911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 943133489911) = 1/(943133489911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11961 : Bounds (-7318431 / 125000000) (-58547447 / 1000000000) (Real.log (943133489911 / 1000000000000)) := by
  have h := reflection_log_11961_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11962_neg : (58041937 / 1000000000) ≤ -Real.log (37744414951 / 40000000000) ∧
    -Real.log (37744414951 / 40000000000) ≤ (29020969 / 500000000) := by
  have h := checkLog_sound (w := (2255585049 / 77744414951)) (n := 12)
    (lo := (58041937 / 1000000000)) (hi := (29020969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37744414951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37744414951) = 1/(37744414951 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11962 : Bounds (-29020969 / 500000000) (-58041937 / 1000000000) (Real.log (37744414951 / 40000000000)) := by
  have h := reflection_log_11962_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11963_neg : (242085901 / 500000000) ≤ -Real.log (500000000000 / 811415213727) ∧
    -Real.log (500000000000 / 811415213727) ≤ (484171803 / 1000000000) := by
  have h := checkLog_sound (w := (311415213727 / 1311415213727)) (n := 12)
    (lo := (242085901 / 500000000)) (hi := (484171803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((811415213727 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(811415213727 / 500000000000) = 1/(500000000000 / 811415213727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11963 : Bounds (242085901 / 500000000) (484171803 / 1000000000) (Real.log (811415213727 / 500000000000)) := by
  have h := reflection_log_11963_neg
  have he : Real.log (811415213727 / 500000000000) = -Real.log (500000000000 / 811415213727) := by
    rw [show ((811415213727 / 500000000000) : ℝ) = ((500000000000 / 811415213727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11964_neg : (15196753 / 31250000) ≤ -Real.log (250000000000 / 406570365303) ∧
    -Real.log (250000000000 / 406570365303) ≤ (486296097 / 1000000000) := by
  have h := checkLog_sound (w := (156570365303 / 656570365303)) (n := 12)
    (lo := (15196753 / 31250000)) (hi := (486296097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((406570365303 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(406570365303 / 250000000000) = 1/(250000000000 / 406570365303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11964 : Bounds (15196753 / 31250000) (486296097 / 1000000000) (Real.log (406570365303 / 250000000000)) := by
  have h := reflection_log_11964_neg
  have he : Real.log (406570365303 / 250000000000) = -Real.log (250000000000 / 406570365303) := by
    rw [show ((406570365303 / 250000000000) : ℝ) = ((250000000000 / 406570365303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11965_neg : (197405097 / 200000000) ≤ -Real.log (500000000000 / 1341620626151) ∧
    -Real.log (500000000000 / 1341620626151) ≤ (987025487 / 1000000000) := by
  have h := checkLog_sound (w := (341620626151 / 2341620626151)) (n := 12)
    (lo := (58775661 / 200000000)) (hi := (146939153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1341620626151 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1341620626151 / 1000000000000) = 1/(500000000000 / 1341620626151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11965 : Bounds (197405097 / 200000000) (987025487 / 1000000000) (Real.log (1341620626151 / 500000000000)) := by
  have h := reflection_log_11965_neg
  have he : Real.log (1341620626151 / 500000000000) = -Real.log (500000000000 / 1341620626151) := by
    rw [show ((1341620626151 / 500000000000) : ℝ) = ((500000000000 / 1341620626151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11966_neg : (98955491 / 100000000) ≤ -Real.log (100000000000 / 269003690037) ∧
    -Real.log (100000000000 / 269003690037) ≤ (30923591 / 31250000) := by
  have h := checkLog_sound (w := (69003690037 / 469003690037)) (n := 12)
    (lo := (29640773 / 100000000)) (hi := (296407731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269003690037 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(269003690037 / 200000000000) = 1/(100000000000 / 269003690037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11966 : Bounds (98955491 / 100000000) (30923591 / 31250000) (Real.log (269003690037 / 100000000000)) := by
  have h := reflection_log_11966_neg
  have he : Real.log (269003690037 / 100000000000) = -Real.log (100000000000 / 269003690037) := by
    rw [show ((269003690037 / 100000000000) : ℝ) = ((100000000000 / 269003690037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11967_neg : (377751269 / 1000000000) ≤ -Real.log (1000 / 1459) ∧
    -Real.log (1000 / 1459) ≤ (37775127 / 100000000) := by
  have h := checkLog_sound (w := (459 / 2459)) (n := 12)
    (lo := (377751269 / 1000000000)) (hi := (37775127 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1459 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1459 / 1000) = 1/(1000 / 1459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11967 : Bounds (377751269 / 1000000000) (37775127 / 100000000) (Real.log (1459 / 1000)) := by
  have h := reflection_log_11967_neg
  have he : Real.log (1459 / 1000) = -Real.log (1000 / 1459) := by
    rw [show ((1459 / 1000) : ℝ) = ((1000 / 1459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


