-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0211__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0211__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T08:36:31.744983+00:00
-- url     : https://prove2.me/theorems/32c88075-249b-4685-b12e-506448f861f5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0211 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0212, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0211 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0212, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0213)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0211 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0212, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0213)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0211 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0212, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0213) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0211 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0212, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0213).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0211 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13504_neg : (1227582669 / 1000000000) ≤ -Real.log (293 / 1000) ∧
    -Real.log (293 / 1000) ≤ (1227582671 / 1000000000) := by
  have h := checkLog_sound (w := (207 / 793)) (n := 12)
    (lo := (534435489 / 1000000000)) (hi := (53443549 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 293) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 293) = 1/(293 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13504 : Bounds (-1227582671 / 1000000000) (-1227582669 / 1000000000) (Real.log (293 / 1000)) := by
  have h := reflection_log_13504_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13505_neg : (2827 / 4000000) ≤ -Real.log (1000000 / 1000707) ∧
    -Real.log (1000000 / 1000707) ≤ (706751 / 1000000000) := by
  have h := checkLog_sound (w := (707 / 2000707)) (n := 12)
    (lo := (2827 / 4000000)) (hi := (706751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000707 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000707 / 1000000) = 1/(1000000 / 1000707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13505 : Bounds (2827 / 4000000) (706751 / 1000000000) (Real.log (1000707 / 1000000)) := by
  have h := reflection_log_13505_neg
  have he : Real.log (1000707 / 1000000) = -Real.log (1000000 / 1000707) := by
    rw [show ((1000707 / 1000000) : ℝ) = ((1000000 / 1000707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13506_neg : (2829 / 4000000) ≤ -Real.log (999293 / 1000000) ∧
    -Real.log (999293 / 1000000) ≤ (707251 / 1000000000) := by
  have h := checkLog_sound (w := (707 / 1999293)) (n := 12)
    (lo := (2829 / 4000000)) (hi := (707251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999293) = 1/(999293 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13506 : Bounds (-707251 / 1000000000) (-2829 / 4000000) (Real.log (999293 / 1000000)) := by
  have h := reflection_log_13506_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13507_neg : (41081467 / 125000000) ≤ -Real.log (500000 / 694547) ∧
    -Real.log (500000 / 694547) ≤ (328651737 / 1000000000) := by
  have h := checkLog_sound (w := (194547 / 1194547)) (n := 12)
    (lo := (41081467 / 125000000)) (hi := (328651737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694547 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694547 / 500000) = 1/(500000 / 694547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13507 : Bounds (41081467 / 125000000) (328651737 / 1000000000) (Real.log (694547 / 500000)) := by
  have h := reflection_log_13507_neg
  have he : Real.log (694547 / 500000) = -Real.log (500000 / 694547) := by
    rw [show ((694547 / 500000) : ℝ) = ((500000 / 694547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13508_neg : (492812177 / 1000000000) ≤ -Real.log (305453 / 500000) ∧
    -Real.log (305453 / 500000) ≤ (246406089 / 500000000) := by
  have h := checkLog_sound (w := (194547 / 805453)) (n := 12)
    (lo := (492812177 / 1000000000)) (hi := (246406089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 305453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 305453) = 1/(305453 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13508 : Bounds (-246406089 / 500000000) (-492812177 / 1000000000) (Real.log (305453 / 500000)) := by
  have h := reflection_log_13508_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13509_neg : (330572007 / 1000000000) ≤ -Real.log (250000 / 347941) ∧
    -Real.log (250000 / 347941) ≤ (41321501 / 125000000) := by
  have h := checkLog_sound (w := (97941 / 597941)) (n := 12)
    (lo := (330572007 / 1000000000)) (hi := (41321501 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347941 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(347941 / 250000) = 1/(250000 / 347941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13509 : Bounds (330572007 / 1000000000) (41321501 / 125000000) (Real.log (347941 / 250000)) := by
  have h := reflection_log_13509_neg
  have he : Real.log (347941 / 250000) = -Real.log (250000 / 347941) := by
    rw [show ((347941 / 250000) : ℝ) = ((250000 / 347941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13510_neg : (248596157 / 500000000) ≤ -Real.log (152059 / 250000) ∧
    -Real.log (152059 / 250000) ≤ (99438463 / 200000000) := by
  have h := checkLog_sound (w := (97941 / 402059)) (n := 12)
    (lo := (248596157 / 500000000)) (hi := (99438463 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 152059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 152059) = 1/(152059 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13510 : Bounds (-99438463 / 200000000) (-248596157 / 500000000) (Real.log (152059 / 250000)) := by
  have h := reflection_log_13510_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13511_neg : (166620307 / 1000000000) ≤ -Real.log (52907560519 / 62500000000) ∧
    -Real.log (52907560519 / 62500000000) ≤ (41655077 / 250000000) := by
  have h := checkLog_sound (w := (9592439481 / 115407560519)) (n := 12)
    (lo := (166620307 / 1000000000)) (hi := (41655077 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 52907560519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 52907560519) = 1/(52907560519 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13511 : Bounds (-41655077 / 250000000) (-166620307 / 1000000000) (Real.log (52907560519 / 62500000000)) := by
  have h := reflection_log_13511_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13512_neg : (164160441 / 1000000000) ≤ -Real.log (212151464791 / 250000000000) ∧
    -Real.log (212151464791 / 250000000000) ≤ (82080221 / 500000000) := by
  have h := checkLog_sound (w := (37848535209 / 462151464791)) (n := 12)
    (lo := (164160441 / 1000000000)) (hi := (82080221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 212151464791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 212151464791) = 1/(212151464791 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13512 : Bounds (-82080221 / 500000000) (-164160441 / 1000000000) (Real.log (212151464791 / 250000000000)) := by
  have h := reflection_log_13512_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13513_neg : (821463913 / 1000000000) ≤ -Real.log (100000000000 / 227382608781) ∧
    -Real.log (100000000000 / 227382608781) ≤ (164292783 / 200000000) := by
  have h := checkLog_sound (w := (27382608781 / 427382608781)) (n := 12)
    (lo := (128316733 / 1000000000)) (hi := (64158367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((227382608781 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(227382608781 / 200000000000) = 1/(100000000000 / 227382608781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13513 : Bounds (821463913 / 1000000000) (164292783 / 200000000) (Real.log (227382608781 / 100000000000)) := by
  have h := reflection_log_13513_neg
  have he : Real.log (227382608781 / 100000000000) = -Real.log (100000000000 / 227382608781) := by
    rw [show ((227382608781 / 100000000000) : ℝ) = ((100000000000 / 227382608781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13514_neg : (827764321 / 1000000000) ≤ -Real.log (250000000000 / 572049336113) ∧
    -Real.log (250000000000 / 572049336113) ≤ (827764323 / 1000000000) := by
  have h := checkLog_sound (w := (72049336113 / 1072049336113)) (n := 12)
    (lo := (134617141 / 1000000000)) (hi := (67308571 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((572049336113 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(572049336113 / 500000000000) = 1/(250000000000 / 572049336113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13514 : Bounds (827764321 / 1000000000) (827764323 / 1000000000) (Real.log (572049336113 / 250000000000)) := by
  have h := reflection_log_13514_neg
  have he : Real.log (572049336113 / 250000000000) = -Real.log (250000000000 / 572049336113) := by
    rw [show ((572049336113 / 250000000000) : ℝ) = ((250000000000 / 572049336113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13515_neg : (1750374251 / 1000000000) ≤ -Real.log (250000000000 / 1439189189189) ∧
    -Real.log (250000000000 / 1439189189189) ≤ (875187127 / 500000000) := by
  have h := checkLog_sound (w := (439189189189 / 2439189189189)) (n := 12)
    (lo := (364079891 / 1000000000)) (hi := (91019973 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1439189189189 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1439189189189 / 1000000000000) = 1/(250000000000 / 1439189189189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13515 : Bounds (1750374251 / 1000000000) (875187127 / 500000000) (Real.log (1439189189189 / 250000000000)) := by
  have h := reflection_log_13515_neg
  have he : Real.log (1439189189189 / 250000000000) = -Real.log (250000000000 / 1439189189189) := by
    rw [show ((1439189189189 / 250000000000) : ℝ) = ((250000000000 / 1439189189189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13516_neg : (110145007 / 62500000) ≤ -Real.log (500000000000 / 2912969283277) ∧
    -Real.log (500000000000 / 2912969283277) ≤ (352464023 / 200000000) := by
  have h := checkLog_sound (w := (912969283277 / 4912969283277)) (n := 12)
    (lo := (47003219 / 125000000)) (hi := (376025753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2912969283277 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2912969283277 / 2000000000000) = 1/(500000000000 / 2912969283277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13516 : Bounds (110145007 / 62500000) (352464023 / 200000000) (Real.log (2912969283277 / 500000000000)) := by
  have h := reflection_log_13516_neg
  have he : Real.log (2912969283277 / 500000000000) = -Real.log (500000000000 / 2912969283277) := by
    rw [show ((2912969283277 / 500000000000) : ℝ) = ((500000000000 / 2912969283277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13517_neg : (53649337 / 100000000) ≤ -Real.log (100 / 171) ∧
    -Real.log (100 / 171) ≤ (536493371 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 271)) (n := 12)
    (lo := (53649337 / 100000000)) (hi := (536493371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171 / 100) = 1/(100 / 171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13517 : Bounds (53649337 / 100000000) (536493371 / 1000000000) (Real.log (171 / 100)) := by
  have h := reflection_log_13517_neg
  have he : Real.log (171 / 100) = -Real.log (100 / 171) := by
    rw [show ((171 / 100) : ℝ) = ((100 / 171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13518_neg : (247574871 / 200000000) ≤ -Real.log (29 / 100) ∧
    -Real.log (29 / 100) ≤ (1237874357 / 1000000000) := by
  have h := checkLog_sound (w := (21 / 79)) (n := 12)
    (lo := (21789087 / 40000000)) (hi := (68090897 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 29) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50 / 29) = 1/(29 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13518 : Bounds (-1237874357 / 1000000000) (-247574871 / 200000000) (Real.log (29 / 100)) := by
  have h := reflection_log_13518_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13519_neg : (177437 / 250000000) ≤ -Real.log (100000 / 100071) ∧
    -Real.log (100000 / 100071) ≤ (709749 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 200071)) (n := 12)
    (lo := (177437 / 250000000)) (hi := (709749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100071 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100071 / 100000) = 1/(100000 / 100071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13519 : Bounds (177437 / 250000000) (709749 / 1000000000) (Real.log (100071 / 100000)) := by
  have h := reflection_log_13519_neg
  have he : Real.log (100071 / 100000) = -Real.log (100000 / 100071) := by
    rw [show ((100071 / 100000) : ℝ) = ((100000 / 100071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13520_neg : (177563 / 250000000) ≤ -Real.log (99929 / 100000) ∧
    -Real.log (99929 / 100000) ≤ (710253 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 199929)) (n := 12)
    (lo := (177563 / 250000000)) (hi := (710253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99929) = 1/(99929 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13520 : Bounds (-710253 / 1000000000) (-177563 / 250000000) (Real.log (99929 / 100000)) := by
  have h := reflection_log_13520_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13521_neg : (330125711 / 1000000000) ≤ -Real.log (1000000 / 1391143) ∧
    -Real.log (1000000 / 1391143) ≤ (20632857 / 62500000) := by
  have h := checkLog_sound (w := (391143 / 2391143)) (n := 12)
    (lo := (330125711 / 1000000000)) (hi := (20632857 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1391143 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1391143 / 1000000) = 1/(1000000 / 1391143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13521 : Bounds (330125711 / 1000000000) (20632857 / 62500000) (Real.log (1391143 / 1000000)) := by
  have h := reflection_log_13521_neg
  have he : Real.log (1391143 / 1000000) = -Real.log (1000000 / 1391143) := by
    rw [show ((1391143 / 1000000) : ℝ) = ((1000000 / 1391143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13522_neg : (9923437 / 20000000) ≤ -Real.log (608857 / 1000000) ∧
    -Real.log (608857 / 1000000) ≤ (496171851 / 1000000000) := by
  have h := checkLog_sound (w := (391143 / 1608857)) (n := 12)
    (lo := (9923437 / 20000000)) (hi := (496171851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 608857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 608857) = 1/(608857 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13522 : Bounds (-496171851 / 1000000000) (-9923437 / 20000000) (Real.log (608857 / 1000000)) := by
  have h := reflection_log_13522_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13523_neg : (648533 / 1953125) ≤ -Real.log (1000000 / 1393821) ∧
    -Real.log (1000000 / 1393821) ≤ (332048897 / 1000000000) := by
  have h := checkLog_sound (w := (393821 / 2393821)) (n := 12)
    (lo := (648533 / 1953125)) (hi := (332048897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1393821 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1393821 / 1000000) = 1/(1000000 / 1393821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13523 : Bounds (648533 / 1953125) (332048897 / 1000000000) (Real.log (1393821 / 1000000)) := by
  have h := reflection_log_13523_neg
  have he : Real.log (1393821 / 1000000) = -Real.log (1000000 / 1393821) := by
    rw [show ((1393821 / 1000000) : ℝ) = ((1000000 / 1393821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13524_neg : (125144989 / 250000000) ≤ -Real.log (606179 / 1000000) ∧
    -Real.log (606179 / 1000000) ≤ (500579957 / 1000000000) := by
  have h := checkLog_sound (w := (393821 / 1606179)) (n := 12)
    (lo := (125144989 / 250000000)) (hi := (500579957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 606179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 606179) = 1/(606179 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13524 : Bounds (-500579957 / 1000000000) (-125144989 / 250000000) (Real.log (606179 / 1000000)) := by
  have h := reflection_log_13524_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13525_neg : (8426553 / 50000000) ≤ -Real.log (844905019959 / 1000000000000) ∧
    -Real.log (844905019959 / 1000000000000) ≤ (168531061 / 1000000000) := by
  have h := checkLog_sound (w := (155094980041 / 1844905019959)) (n := 12)
    (lo := (8426553 / 50000000)) (hi := (168531061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 844905019959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 844905019959) = 1/(844905019959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13525 : Bounds (-168531061 / 1000000000) (-8426553 / 50000000) (Real.log (844905019959 / 1000000000000)) := by
  have h := reflection_log_13525_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13526_neg : (83023069 / 500000000) ≤ -Real.log (847007153551 / 1000000000000) ∧
    -Real.log (847007153551 / 1000000000000) ≤ (166046139 / 1000000000) := by
  have h := checkLog_sound (w := (152992846449 / 1847007153551)) (n := 12)
    (lo := (83023069 / 500000000)) (hi := (166046139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 847007153551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 847007153551) = 1/(847007153551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13526 : Bounds (-166046139 / 1000000000) (-83023069 / 500000000) (Real.log (847007153551 / 1000000000000)) := by
  have h := reflection_log_13526_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13527_neg : (20657439 / 25000000) ≤ -Real.log (62500000000 / 142802722971) ∧
    -Real.log (62500000000 / 142802722971) ≤ (413148781 / 500000000) := by
  have h := checkLog_sound (w := (17802722971 / 267802722971)) (n := 12)
    (lo := (6657519 / 50000000)) (hi := (133150381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142802722971 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(142802722971 / 125000000000) = 1/(62500000000 / 142802722971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13527 : Bounds (20657439 / 25000000) (413148781 / 500000000) (Real.log (142802722971 / 62500000000)) := by
  have h := reflection_log_13527_neg
  have he : Real.log (142802722971 / 62500000000) = -Real.log (62500000000 / 142802722971) := by
    rw [show ((142802722971 / 62500000000) : ℝ) = ((62500000000 / 142802722971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13528_neg : (832628853 / 1000000000) ≤ -Real.log (100000000000 / 229935547091) ∧
    -Real.log (100000000000 / 229935547091) ≤ (166525771 / 200000000) := by
  have h := checkLog_sound (w := (29935547091 / 429935547091)) (n := 12)
    (lo := (139481673 / 1000000000)) (hi := (69740837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229935547091 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(229935547091 / 200000000000) = 1/(100000000000 / 229935547091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13528 : Bounds (832628853 / 1000000000) (166525771 / 200000000) (Real.log (229935547091 / 100000000000)) := by
  have h := reflection_log_13528_neg
  have he : Real.log (229935547091 / 100000000000) = -Real.log (100000000000 / 229935547091) := by
    rw [show ((229935547091 / 100000000000) : ℝ) = ((100000000000 / 229935547091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13529_neg : (110145007 / 62500000) ≤ -Real.log (125000000000 / 728242320819) ∧
    -Real.log (125000000000 / 728242320819) ≤ (352464023 / 200000000) := by
  have h := checkLog_sound (w := (228242320819 / 1228242320819)) (n := 12)
    (lo := (47003219 / 125000000)) (hi := (376025753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((728242320819 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(728242320819 / 500000000000) = 1/(125000000000 / 728242320819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13529 : Bounds (110145007 / 62500000) (352464023 / 200000000) (Real.log (728242320819 / 125000000000)) := by
  have h := reflection_log_13529_neg
  have he : Real.log (728242320819 / 125000000000) = -Real.log (125000000000 / 728242320819) := by
    rw [show ((728242320819 / 125000000000) : ℝ) = ((125000000000 / 728242320819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13530_neg : (70974709 / 40000000) ≤ -Real.log (500000000000 / 2948275862069) ∧
    -Real.log (500000000000 / 2948275862069) ≤ (110897983 / 62500000) := by
  have h := checkLog_sound (w := (948275862069 / 4948275862069)) (n := 12)
    (lo := (77614673 / 200000000)) (hi := (194036683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2948275862069 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2948275862069 / 2000000000000) = 1/(500000000000 / 2948275862069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13530 : Bounds (70974709 / 40000000) (110897983 / 62500000) (Real.log (2948275862069 / 500000000000)) := by
  have h := reflection_log_13530_neg
  have he : Real.log (2948275862069 / 500000000000) = -Real.log (500000000000 / 2948275862069) := by
    rw [show ((2948275862069 / 500000000000) : ℝ) = ((500000000000 / 2948275862069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13531_neg : (538246219 / 1000000000) ≤ -Real.log (1000 / 1713) ∧
    -Real.log (1000 / 1713) ≤ (26912311 / 50000000) := by
  have h := checkLog_sound (w := (713 / 2713)) (n := 12)
    (lo := (538246219 / 1000000000)) (hi := (26912311 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1713 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1713 / 1000) = 1/(1000 / 1713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13531 : Bounds (538246219 / 1000000000) (26912311 / 50000000) (Real.log (1713 / 1000)) := by
  have h := reflection_log_13531_neg
  have he : Real.log (1713 / 1000) = -Real.log (1000 / 1713) := by
    rw [show ((1713 / 1000) : ℝ) = ((1000 / 1713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13532_neg : (624136531 / 500000000) ≤ -Real.log (287 / 1000) ∧
    -Real.log (287 / 1000) ≤ (156034133 / 125000000) := by
  have h := checkLog_sound (w := (213 / 787)) (n := 12)
    (lo := (277562941 / 500000000)) (hi := (555125883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 287) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 287) = 1/(287 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13532 : Bounds (-156034133 / 125000000) (-624136531 / 500000000) (Real.log (287 / 1000)) := by
  have h := reflection_log_13532_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13533_neg : (142549 / 200000000) ≤ -Real.log (1000000 / 1000713) ∧
    -Real.log (1000000 / 1000713) ≤ (356373 / 500000000) := by
  have h := checkLog_sound (w := (713 / 2000713)) (n := 12)
    (lo := (142549 / 200000000)) (hi := (356373 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000713 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000713 / 1000000) = 1/(1000000 / 1000713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13533 : Bounds (142549 / 200000000) (356373 / 500000000) (Real.log (1000713 / 1000000)) := by
  have h := reflection_log_13533_neg
  have he : Real.log (1000713 / 1000000) = -Real.log (1000000 / 1000713) := by
    rw [show ((1000713 / 1000000) : ℝ) = ((1000000 / 1000713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13534_neg : (356627 / 500000000) ≤ -Real.log (999287 / 1000000) ∧
    -Real.log (999287 / 1000000) ≤ (142651 / 200000000) := by
  have h := checkLog_sound (w := (713 / 1999287)) (n := 12)
    (lo := (356627 / 500000000)) (hi := (142651 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999287) = 1/(999287 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13534 : Bounds (-142651 / 200000000) (-356627 / 500000000) (Real.log (999287 / 1000000)) := by
  have h := reflection_log_13534_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13535_neg : (331601823 / 1000000000) ≤ -Real.log (500000 / 696599) ∧
    -Real.log (500000 / 696599) ≤ (10362557 / 31250000) := by
  have h := checkLog_sound (w := (196599 / 1196599)) (n := 12)
    (lo := (331601823 / 1000000000)) (hi := (10362557 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696599 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696599 / 500000) = 1/(500000 / 696599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13535 : Bounds (331601823 / 1000000000) (10362557 / 31250000) (Real.log (696599 / 500000)) := by
  have h := reflection_log_13535_neg
  have he : Real.log (696599 / 500000) = -Real.log (500000 / 696599) := by
    rw [show ((696599 / 500000) : ℝ) = ((500000 / 696599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13536_neg : (99910547 / 200000000) ≤ -Real.log (303401 / 500000) ∧
    -Real.log (303401 / 500000) ≤ (15611023 / 31250000) := by
  have h := checkLog_sound (w := (196599 / 803401)) (n := 12)
    (lo := (99910547 / 200000000)) (hi := (15611023 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 303401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 303401) = 1/(303401 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13536 : Bounds (-15611023 / 31250000) (-99910547 / 200000000) (Real.log (303401 / 500000)) := by
  have h := reflection_log_13536_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13537_neg : (166763953 / 500000000) ≤ -Real.log (250000 / 348971) ∧
    -Real.log (250000 / 348971) ≤ (333527907 / 1000000000) := by
  have h := checkLog_sound (w := (98971 / 598971)) (n := 12)
    (lo := (166763953 / 500000000)) (hi := (333527907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((348971 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(348971 / 250000) = 1/(250000 / 348971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13537 : Bounds (166763953 / 500000000) (333527907 / 1000000000) (Real.log (348971 / 250000)) := by
  have h := reflection_log_13537_neg
  have he : Real.log (348971 / 250000) = -Real.log (250000 / 348971) := by
    rw [show ((348971 / 250000) : ℝ) = ((250000 / 348971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13538_neg : (251994523 / 500000000) ≤ -Real.log (151029 / 250000) ∧
    -Real.log (151029 / 250000) ≤ (503989047 / 1000000000) := by
  have h := checkLog_sound (w := (98971 / 401029)) (n := 12)
    (lo := (251994523 / 500000000)) (hi := (503989047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 151029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 151029) = 1/(151029 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13538 : Bounds (-503989047 / 1000000000) (-251994523 / 500000000) (Real.log (151029 / 250000)) := by
  have h := reflection_log_13538_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13539_neg : (8523057 / 50000000) ≤ -Real.log (52704741159 / 62500000000) ∧
    -Real.log (52704741159 / 62500000000) ≤ (170461141 / 1000000000) := by
  have h := checkLog_sound (w := (9795258841 / 115204741159)) (n := 12)
    (lo := (8523057 / 50000000)) (hi := (170461141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 52704741159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 52704741159) = 1/(52704741159 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13539 : Bounds (-170461141 / 1000000000) (-8523057 / 50000000) (Real.log (52704741159 / 62500000000)) := by
  have h := reflection_log_13539_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13540_neg : (167950911 / 1000000000) ≤ -Real.log (211348833199 / 250000000000) ∧
    -Real.log (211348833199 / 250000000000) ≤ (2624233 / 15625000) := by
  have h := checkLog_sound (w := (38651166801 / 461348833199)) (n := 12)
    (lo := (167950911 / 1000000000)) (hi := (2624233 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 211348833199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 211348833199) = 1/(211348833199 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13540 : Bounds (-2624233 / 15625000) (-167950911 / 1000000000) (Real.log (211348833199 / 250000000000)) := by
  have h := reflection_log_13540_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13541_neg : (415577279 / 500000000) ≤ -Real.log (250000000000 / 573992010573) ∧
    -Real.log (250000000000 / 573992010573) ≤ (1298679 / 1562500) := by
  have h := checkLog_sound (w := (73992010573 / 1073992010573)) (n := 12)
    (lo := (69003689 / 500000000)) (hi := (138007379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((573992010573 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(573992010573 / 500000000000) = 1/(250000000000 / 573992010573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13541 : Bounds (415577279 / 500000000) (1298679 / 1562500) (Real.log (573992010573 / 250000000000)) := by
  have h := reflection_log_13541_neg
  have he : Real.log (573992010573 / 250000000000) = -Real.log (250000000000 / 573992010573) := by
    rw [show ((573992010573 / 250000000000) : ℝ) = ((250000000000 / 573992010573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13542_neg : (104689619 / 125000000) ≤ -Real.log (250000000000 / 577655615809) ∧
    -Real.log (250000000000 / 577655615809) ≤ (418758477 / 500000000) := by
  have h := checkLog_sound (w := (77655615809 / 1077655615809)) (n := 12)
    (lo := (36092443 / 250000000)) (hi := (144369773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((577655615809 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(577655615809 / 500000000000) = 1/(250000000000 / 577655615809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13542 : Bounds (104689619 / 125000000) (418758477 / 500000000) (Real.log (577655615809 / 250000000000)) := by
  have h := reflection_log_13542_neg
  have he : Real.log (577655615809 / 250000000000) = -Real.log (250000000000 / 577655615809) := by
    rw [show ((577655615809 / 250000000000) : ℝ) = ((250000000000 / 577655615809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13543_neg : (70974709 / 40000000) ≤ -Real.log (125000000000 / 737068965517) ∧
    -Real.log (125000000000 / 737068965517) ≤ (110897983 / 62500000) := by
  have h := checkLog_sound (w := (237068965517 / 1237068965517)) (n := 12)
    (lo := (77614673 / 200000000)) (hi := (194036683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737068965517 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(737068965517 / 500000000000) = 1/(125000000000 / 737068965517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13543 : Bounds (70974709 / 40000000) (110897983 / 62500000) (Real.log (737068965517 / 125000000000)) := by
  have h := reflection_log_13543_neg
  have he : Real.log (737068965517 / 125000000000) = -Real.log (125000000000 / 737068965517) := by
    rw [show ((737068965517 / 125000000000) : ℝ) = ((125000000000 / 737068965517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13544_neg : (1786519281 / 1000000000) ≤ -Real.log (125000000000 / 746080139373) ∧
    -Real.log (125000000000 / 746080139373) ≤ (446629821 / 250000000) := by
  have h := checkLog_sound (w := (246080139373 / 1246080139373)) (n := 12)
    (lo := (400224921 / 1000000000)) (hi := (200112461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746080139373 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(746080139373 / 500000000000) = 1/(125000000000 / 746080139373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13544 : Bounds (1786519281 / 1000000000) (446629821 / 250000000) (Real.log (746080139373 / 125000000000)) := by
  have h := reflection_log_13544_neg
  have he : Real.log (746080139373 / 125000000000) = -Real.log (125000000000 / 746080139373) := by
    rw [show ((746080139373 / 125000000000) : ℝ) = ((125000000000 / 746080139373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13545_neg : (539996001 / 1000000000) ≤ -Real.log (250 / 429) ∧
    -Real.log (250 / 429) ≤ (269998001 / 500000000) := by
  have h := checkLog_sound (w := (179 / 679)) (n := 12)
    (lo := (539996001 / 1000000000)) (hi := (269998001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((429 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(429 / 250) = 1/(250 / 429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13545 : Bounds (539996001 / 1000000000) (269998001 / 500000000) (Real.log (429 / 250)) := by
  have h := reflection_log_13545_neg
  have he : Real.log (429 / 250) = -Real.log (250 / 429) := by
    rw [show ((429 / 250) : ℝ) = ((250 / 429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13546_neg : (15734763 / 12500000) ≤ -Real.log (71 / 250) ∧
    -Real.log (71 / 250) ≤ (629390521 / 500000000) := by
  have h := checkLog_sound (w := (27 / 98)) (n := 12)
    (lo := (28281693 / 50000000)) (hi := (565633861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 71) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 71) = 1/(71 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13546 : Bounds (-629390521 / 500000000) (-15734763 / 12500000) (Real.log (71 / 250)) := by
  have h := reflection_log_13546_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13547_neg : (715743 / 1000000000) ≤ -Real.log (250000 / 250179) ∧
    -Real.log (250000 / 250179) ≤ (22367 / 31250000) := by
  have h := checkLog_sound (w := (179 / 500179)) (n := 12)
    (lo := (715743 / 1000000000)) (hi := (22367 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250179 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250179 / 250000) = 1/(250000 / 250179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13547 : Bounds (715743 / 1000000000) (22367 / 31250000) (Real.log (250179 / 250000)) := by
  have h := reflection_log_13547_neg
  have he : Real.log (250179 / 250000) = -Real.log (250000 / 250179) := by
    rw [show ((250179 / 250000) : ℝ) = ((250000 / 250179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13548_neg : (22383 / 31250000) ≤ -Real.log (249821 / 250000) ∧
    -Real.log (249821 / 250000) ≤ (716257 / 1000000000) := by
  have h := checkLog_sound (w := (179 / 499821)) (n := 12)
    (lo := (22383 / 31250000)) (hi := (716257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249821) = 1/(249821 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13548 : Bounds (-716257 / 1000000000) (-22383 / 31250000) (Real.log (249821 / 250000)) := by
  have h := reflection_log_13548_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13549_neg : (333080777 / 1000000000) ≤ -Real.log (50000 / 69763) ∧
    -Real.log (50000 / 69763) ≤ (166540389 / 500000000) := by
  have h := checkLog_sound (w := (19763 / 119763)) (n := 12)
    (lo := (333080777 / 1000000000)) (hi := (166540389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69763 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69763 / 50000) = 1/(50000 / 69763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13549 : Bounds (333080777 / 1000000000) (166540389 / 500000000) (Real.log (69763 / 50000)) := by
  have h := reflection_log_13549_neg
  have he : Real.log (69763 / 50000) = -Real.log (50000 / 69763) := by
    rw [show ((69763 / 50000) : ℝ) = ((50000 / 69763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13550_neg : (100591333 / 200000000) ≤ -Real.log (30237 / 50000) ∧
    -Real.log (30237 / 50000) ≤ (251478333 / 500000000) := by
  have h := checkLog_sound (w := (19763 / 80237)) (n := 12)
    (lo := (100591333 / 200000000)) (hi := (251478333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 30237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 30237) = 1/(30237 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13550 : Bounds (-251478333 / 500000000) (-100591333 / 200000000) (Real.log (30237 / 50000)) := by
  have h := reflection_log_13550_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13551_neg : (167505227 / 500000000) ≤ -Real.log (200000 / 279591) ∧
    -Real.log (200000 / 279591) ≤ (67002091 / 200000000) := by
  have h := checkLog_sound (w := (79591 / 479591)) (n := 12)
    (lo := (167505227 / 500000000)) (hi := (67002091 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279591 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(279591 / 200000) = 1/(200000 / 279591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13551 : Bounds (167505227 / 500000000) (67002091 / 200000000) (Real.log (279591 / 200000)) := by
  have h := reflection_log_13551_neg
  have he : Real.log (279591 / 200000) = -Real.log (200000 / 279591) := by
    rw [show ((279591 / 200000) : ℝ) = ((200000 / 279591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13552_neg : (101484617 / 200000000) ≤ -Real.log (120409 / 200000) ∧
    -Real.log (120409 / 200000) ≤ (253711543 / 500000000) := by
  have h := checkLog_sound (w := (79591 / 320409)) (n := 12)
    (lo := (101484617 / 200000000)) (hi := (253711543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 120409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 120409) = 1/(120409 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13552 : Bounds (-253711543 / 500000000) (-101484617 / 200000000) (Real.log (120409 / 200000)) := by
  have h := reflection_log_13552_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13553_neg : (172412631 / 1000000000) ≤ -Real.log (33665272719 / 40000000000) ∧
    -Real.log (33665272719 / 40000000000) ≤ (21551579 / 125000000) := by
  have h := checkLog_sound (w := (6334727281 / 73665272719)) (n := 12)
    (lo := (172412631 / 1000000000)) (hi := (21551579 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 33665272719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 33665272719) = 1/(33665272719 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13553 : Bounds (-21551579 / 125000000) (-172412631 / 1000000000) (Real.log (33665272719 / 40000000000)) := by
  have h := reflection_log_13553_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13554_neg : (169875887 / 1000000000) ≤ -Real.log (2109423831 / 2500000000) ∧
    -Real.log (2109423831 / 2500000000) ≤ (10617243 / 62500000) := by
  have h := checkLog_sound (w := (390576169 / 4609423831)) (n := 12)
    (lo := (169875887 / 1000000000)) (hi := (10617243 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2109423831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2109423831) = 1/(2109423831 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13554 : Bounds (-10617243 / 62500000) (-169875887 / 1000000000) (Real.log (2109423831 / 2500000000)) := by
  have h := reflection_log_13554_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13555_neg : (418018721 / 500000000) ≤ -Real.log (4000000000 / 9228825611) ∧
    -Real.log (4000000000 / 9228825611) ≤ (209009361 / 250000000) := by
  have h := checkLog_sound (w := (1228825611 / 17228825611)) (n := 12)
    (lo := (71445131 / 500000000)) (hi := (142890263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9228825611 / 8000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(9228825611 / 8000000000) = 1/(4000000000 / 9228825611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13555 : Bounds (418018721 / 500000000) (209009361 / 250000000) (Real.log (9228825611 / 4000000000)) := by
  have h := reflection_log_13555_neg
  have he : Real.log (9228825611 / 4000000000) = -Real.log (4000000000 / 9228825611) := by
    rw [show ((9228825611 / 4000000000) : ℝ) = ((4000000000 / 9228825611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13556_neg : (842433539 / 1000000000) ≤ -Real.log (500000000000 / 1161005406573) ∧
    -Real.log (500000000000 / 1161005406573) ≤ (842433541 / 1000000000) := by
  have h := checkLog_sound (w := (161005406573 / 2161005406573)) (n := 12)
    (lo := (149286359 / 1000000000)) (hi := (3732159 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161005406573 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1161005406573 / 1000000000000) = 1/(500000000000 / 1161005406573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13556 : Bounds (842433539 / 1000000000) (842433541 / 1000000000) (Real.log (1161005406573 / 500000000000)) := by
  have h := reflection_log_13556_neg
  have he : Real.log (1161005406573 / 500000000000) = -Real.log (500000000000 / 1161005406573) := by
    rw [show ((1161005406573 / 500000000000) : ℝ) = ((500000000000 / 1161005406573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13557_neg : (1786519281 / 1000000000) ≤ -Real.log (500000000000 / 2984320557491) ∧
    -Real.log (500000000000 / 2984320557491) ≤ (446629821 / 250000000) := by
  have h := checkLog_sound (w := (984320557491 / 4984320557491)) (n := 12)
    (lo := (400224921 / 1000000000)) (hi := (200112461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2984320557491 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2984320557491 / 2000000000000) = 1/(500000000000 / 2984320557491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13557 : Bounds (1786519281 / 1000000000) (446629821 / 250000000) (Real.log (2984320557491 / 500000000000)) := by
  have h := reflection_log_13557_neg
  have he : Real.log (2984320557491 / 500000000000) = -Real.log (500000000000 / 2984320557491) := by
    rw [show ((2984320557491 / 500000000000) : ℝ) = ((500000000000 / 2984320557491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13558_neg : (22484713 / 12500000) ≤ -Real.log (125000000000 / 755281690141) ∧
    -Real.log (125000000000 / 755281690141) ≤ (1798777043 / 1000000000) := by
  have h := checkLog_sound (w := (255281690141 / 1255281690141)) (n := 12)
    (lo := (10312067 / 25000000)) (hi := (412482681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((755281690141 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(755281690141 / 500000000000) = 1/(125000000000 / 755281690141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13558 : Bounds (22484713 / 12500000) (1798777043 / 1000000000) (Real.log (755281690141 / 125000000000)) := by
  have h := reflection_log_13558_neg
  have he : Real.log (755281690141 / 125000000000) = -Real.log (125000000000 / 755281690141) := by
    rw [show ((755281690141 / 125000000000) : ℝ) = ((125000000000 / 755281690141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13559_neg : (270871363 / 500000000) ≤ -Real.log (1000 / 1719) ∧
    -Real.log (1000 / 1719) ≤ (541742727 / 1000000000) := by
  have h := checkLog_sound (w := (719 / 2719)) (n := 12)
    (lo := (270871363 / 500000000)) (hi := (541742727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1719 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1719 / 1000) = 1/(1000 / 1719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13559 : Bounds (270871363 / 500000000) (541742727 / 1000000000) (Real.log (1719 / 1000)) := by
  have h := reflection_log_13559_neg
  have he : Real.log (1719 / 1000) = -Real.log (1000 / 1719) := by
    rw [show ((1719 / 1000) : ℝ) = ((1000 / 1719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13560_neg : (1269400609 / 1000000000) ≤ -Real.log (281 / 1000) ∧
    -Real.log (281 / 1000) ≤ (1269400611 / 1000000000) := by
  have h := checkLog_sound (w := (219 / 781)) (n := 12)
    (lo := (576253429 / 1000000000)) (hi := (57625343 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 281) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 281) = 1/(281 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13560 : Bounds (-1269400611 / 1000000000) (-1269400609 / 1000000000) (Real.log (281 / 1000)) := by
  have h := reflection_log_13560_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13561_neg : (718741 / 1000000000) ≤ -Real.log (1000000 / 1000719) ∧
    -Real.log (1000000 / 1000719) ≤ (359371 / 500000000) := by
  have h := checkLog_sound (w := (719 / 2000719)) (n := 12)
    (lo := (718741 / 1000000000)) (hi := (359371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000719 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000719 / 1000000) = 1/(1000000 / 1000719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13561 : Bounds (718741 / 1000000000) (359371 / 500000000) (Real.log (1000719 / 1000000)) := by
  have h := reflection_log_13561_neg
  have he : Real.log (1000719 / 1000000) = -Real.log (1000000 / 1000719) := by
    rw [show ((1000719 / 1000000) : ℝ) = ((1000000 / 1000719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13562_neg : (359629 / 500000000) ≤ -Real.log (999281 / 1000000) ∧
    -Real.log (999281 / 1000000) ≤ (719259 / 1000000000) := by
  have h := checkLog_sound (w := (719 / 1999281)) (n := 12)
    (lo := (359629 / 500000000)) (hi := (719259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999281) = 1/(999281 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13562 : Bounds (-719259 / 1000000000) (-359629 / 500000000) (Real.log (999281 / 1000000)) := by
  have h := reflection_log_13562_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13563_neg : (334562557 / 1000000000) ≤ -Real.log (1000000 / 1397329) ∧
    -Real.log (1000000 / 1397329) ≤ (167281279 / 500000000) := by
  have h := checkLog_sound (w := (397329 / 2397329)) (n := 12)
    (lo := (334562557 / 1000000000)) (hi := (167281279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1397329 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1397329 / 1000000) = 1/(1000000 / 1397329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13563 : Bounds (334562557 / 1000000000) (167281279 / 500000000) (Real.log (1397329 / 1000000)) := by
  have h := reflection_log_13563_neg
  have he : Real.log (1397329 / 1000000) = -Real.log (1000000 / 1397329) := by
    rw [show ((1397329 / 1000000) : ℝ) = ((1000000 / 1397329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13564_neg : (126595959 / 250000000) ≤ -Real.log (602671 / 1000000) ∧
    -Real.log (602671 / 1000000) ≤ (506383837 / 1000000000) := by
  have h := checkLog_sound (w := (397329 / 1602671)) (n := 12)
    (lo := (126595959 / 250000000)) (hi := (506383837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 602671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 602671) = 1/(602671 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13564 : Bounds (-506383837 / 1000000000) (-126595959 / 250000000) (Real.log (602671 / 1000000)) := by
  have h := reflection_log_13564_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13565_neg : (336495093 / 1000000000) ≤ -Real.log (31250 / 43751) ∧
    -Real.log (31250 / 43751) ≤ (168247547 / 500000000) := by
  have h := checkLog_sound (w := (12501 / 75001)) (n := 12)
    (lo := (336495093 / 1000000000)) (hi := (168247547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43751 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43751 / 31250) = 1/(31250 / 43751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13565 : Bounds (336495093 / 1000000000) (168247547 / 500000000) (Real.log (43751 / 31250)) := by
  have h := reflection_log_13565_neg
  have he : Real.log (43751 / 31250) = -Real.log (31250 / 43751) := by
    rw [show ((43751 / 31250) : ℝ) = ((31250 / 43751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13566_neg : (255439479 / 500000000) ≤ -Real.log (18749 / 31250) ∧
    -Real.log (18749 / 31250) ≤ (510878959 / 1000000000) := by
  have h := checkLog_sound (w := (12501 / 49999)) (n := 12)
    (lo := (255439479 / 500000000)) (hi := (510878959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 18749) = 1/(18749 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13566 : Bounds (-510878959 / 1000000000) (-255439479 / 500000000) (Real.log (18749 / 31250)) := by
  have h := reflection_log_13566_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13567_neg : (34876773 / 200000000) ≤ -Real.log (820287499 / 976562500) ∧
    -Real.log (820287499 / 976562500) ≤ (87191933 / 500000000) := by
  have h := checkLog_sound (w := (156275001 / 1796849999)) (n := 12)
    (lo := (34876773 / 200000000)) (hi := (87191933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 820287499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 820287499) = 1/(820287499 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13567 : Bounds (-87191933 / 500000000) (-34876773 / 200000000) (Real.log (820287499 / 976562500)) := by
  have h := reflection_log_13567_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0212 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13568_neg : (171821279 / 1000000000) ≤ -Real.log (842129665759 / 1000000000000) ∧
    -Real.log (842129665759 / 1000000000000) ≤ (1073883 / 6250000) := by
  have h := checkLog_sound (w := (157870334241 / 1842129665759)) (n := 12)
    (lo := (171821279 / 1000000000)) (hi := (1073883 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 842129665759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 842129665759) = 1/(842129665759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13568 : Bounds (-1073883 / 6250000) (-171821279 / 1000000000) (Real.log (842129665759 / 1000000000000)) := by
  have h := reflection_log_13568_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13569_neg : (840946393 / 1000000000) ≤ -Real.log (500000000000 / 1159280104733) ∧
    -Real.log (500000000000 / 1159280104733) ≤ (168189279 / 200000000) := by
  have h := checkLog_sound (w := (159280104733 / 2159280104733)) (n := 12)
    (lo := (147799213 / 1000000000)) (hi := (73899607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1159280104733 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1159280104733 / 1000000000000) = 1/(500000000000 / 1159280104733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13569 : Bounds (840946393 / 1000000000) (168189279 / 200000000) (Real.log (1159280104733 / 500000000000)) := by
  have h := reflection_log_13569_neg
  have he : Real.log (1159280104733 / 500000000000) = -Real.log (500000000000 / 1159280104733) := by
    rw [show ((1159280104733 / 500000000000) : ℝ) = ((500000000000 / 1159280104733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13570_neg : (847374051 / 1000000000) ≤ -Real.log (500000000000 / 1166755560297) ∧
    -Real.log (500000000000 / 1166755560297) ≤ (847374053 / 1000000000) := by
  have h := checkLog_sound (w := (166755560297 / 2166755560297)) (n := 12)
    (lo := (154226871 / 1000000000)) (hi := (19278359 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1166755560297 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1166755560297 / 1000000000000) = 1/(500000000000 / 1166755560297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13570 : Bounds (847374051 / 1000000000) (847374053 / 1000000000) (Real.log (1166755560297 / 500000000000)) := by
  have h := reflection_log_13570_neg
  have he : Real.log (1166755560297 / 500000000000) = -Real.log (500000000000 / 1166755560297) := by
    rw [show ((1166755560297 / 500000000000) : ℝ) = ((500000000000 / 1166755560297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13571_neg : (22484713 / 12500000) ≤ -Real.log (500000000000 / 3021126760563) ∧
    -Real.log (500000000000 / 3021126760563) ≤ (1798777043 / 1000000000) := by
  have h := checkLog_sound (w := (1021126760563 / 5021126760563)) (n := 12)
    (lo := (10312067 / 25000000)) (hi := (412482681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3021126760563 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3021126760563 / 2000000000000) = 1/(500000000000 / 3021126760563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13571 : Bounds (22484713 / 12500000) (1798777043 / 1000000000) (Real.log (3021126760563 / 500000000000)) := by
  have h := reflection_log_13571_neg
  have he : Real.log (3021126760563 / 500000000000) = -Real.log (500000000000 / 3021126760563) := by
    rw [show ((3021126760563 / 500000000000) : ℝ) = ((500000000000 / 3021126760563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13572_neg : (905571667 / 500000000) ≤ -Real.log (50000000000 / 305871886121) ∧
    -Real.log (50000000000 / 305871886121) ≤ (1811143337 / 1000000000) := by
  have h := checkLog_sound (w := (105871886121 / 505871886121)) (n := 12)
    (lo := (212424487 / 500000000)) (hi := (16993959 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305871886121 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(305871886121 / 200000000000) = 1/(50000000000 / 305871886121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13572 : Bounds (905571667 / 500000000) (1811143337 / 1000000000) (Real.log (305871886121 / 50000000000)) := by
  have h := reflection_log_13572_neg
  have he : Real.log (305871886121 / 50000000000) = -Real.log (50000000000 / 305871886121) := by
    rw [show ((305871886121 / 50000000000) : ℝ) = ((50000000000 / 305871886121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13573_neg : (271743203 / 500000000) ≤ -Real.log (500 / 861) ∧
    -Real.log (500 / 861) ≤ (543486407 / 1000000000) := by
  have h := checkLog_sound (w := (361 / 1361)) (n := 12)
    (lo := (271743203 / 500000000)) (hi := (543486407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((861 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(861 / 500) = 1/(500 / 861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13573 : Bounds (271743203 / 500000000) (543486407 / 1000000000) (Real.log (861 / 500)) := by
  have h := reflection_log_13573_neg
  have he : Real.log (861 / 500) = -Real.log (500 / 861) := by
    rw [show ((861 / 500) : ℝ) = ((500 / 861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13574_neg : (320033541 / 250000000) ≤ -Real.log (139 / 500) ∧
    -Real.log (139 / 500) ≤ (640067083 / 500000000) := by
  have h := checkLog_sound (w := (111 / 389)) (n := 12)
    (lo := (73373373 / 125000000)) (hi := (117397397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 139) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 139) = 1/(139 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13574 : Bounds (-640067083 / 500000000) (-320033541 / 250000000) (Real.log (139 / 500)) := by
  have h := reflection_log_13574_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13575_neg : (721739 / 1000000000) ≤ -Real.log (500000 / 500361) ∧
    -Real.log (500000 / 500361) ≤ (36087 / 50000000) := by
  have h := checkLog_sound (w := (361 / 1000361)) (n := 12)
    (lo := (721739 / 1000000000)) (hi := (36087 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500361 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500361 / 500000) = 1/(500000 / 500361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13575 : Bounds (721739 / 1000000000) (36087 / 50000000) (Real.log (500361 / 500000)) := by
  have h := reflection_log_13575_neg
  have he : Real.log (500361 / 500000) = -Real.log (500000 / 500361) := by
    rw [show ((500361 / 500000) : ℝ) = ((500000 / 500361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13576_neg : (36113 / 50000000) ≤ -Real.log (499639 / 500000) ∧
    -Real.log (499639 / 500000) ≤ (722261 / 1000000000) := by
  have h := checkLog_sound (w := (361 / 999639)) (n := 12)
    (lo := (36113 / 50000000)) (hi := (722261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499639) = 1/(499639 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13576 : Bounds (-722261 / 1000000000) (-36113 / 50000000) (Real.log (499639 / 500000)) := by
  have h := reflection_log_13576_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13577_neg : (168023573 / 500000000) ≤ -Real.log (200000 / 279881) ∧
    -Real.log (200000 / 279881) ≤ (336047147 / 1000000000) := by
  have h := checkLog_sound (w := (79881 / 479881)) (n := 12)
    (lo := (168023573 / 500000000)) (hi := (336047147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279881 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(279881 / 200000) = 1/(200000 / 279881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13577 : Bounds (168023573 / 500000000) (336047147 / 1000000000) (Real.log (279881 / 200000)) := by
  have h := reflection_log_13577_neg
  have he : Real.log (279881 / 200000) = -Real.log (200000 / 279881) := by
    rw [show ((279881 / 200000) : ℝ) = ((200000 / 279881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13578_neg : (31864653 / 62500000) ≤ -Real.log (120119 / 200000) ∧
    -Real.log (120119 / 200000) ≤ (509834449 / 1000000000) := by
  have h := checkLog_sound (w := (79881 / 320119)) (n := 12)
    (lo := (31864653 / 62500000)) (hi := (509834449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 120119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 120119) = 1/(120119 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13578 : Bounds (-509834449 / 1000000000) (-31864653 / 62500000) (Real.log (120119 / 200000)) := by
  have h := reflection_log_13578_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13579_neg : (84495631 / 250000000) ≤ -Real.log (250000 / 350529) ∧
    -Real.log (250000 / 350529) ≤ (13519301 / 40000000) := by
  have h := checkLog_sound (w := (100529 / 600529)) (n := 12)
    (lo := (84495631 / 250000000)) (hi := (13519301 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((350529 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(350529 / 250000) = 1/(250000 / 350529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13579 : Bounds (84495631 / 250000000) (13519301 / 40000000) (Real.log (350529 / 250000)) := by
  have h := reflection_log_13579_neg
  have he : Real.log (350529 / 250000) = -Real.log (250000 / 350529) := by
    rw [show ((350529 / 250000) : ℝ) = ((250000 / 350529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13580_neg : (514358523 / 1000000000) ≤ -Real.log (149471 / 250000) ∧
    -Real.log (149471 / 250000) ≤ (128589631 / 250000000) := by
  have h := checkLog_sound (w := (100529 / 399471)) (n := 12)
    (lo := (514358523 / 1000000000)) (hi := (128589631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 149471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 149471) = 1/(149471 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13580 : Bounds (-128589631 / 250000000) (-514358523 / 1000000000) (Real.log (149471 / 250000)) := by
  have h := reflection_log_13580_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13581_neg : (176375999 / 1000000000) ≤ -Real.log (52393920159 / 62500000000) ∧
    -Real.log (52393920159 / 62500000000) ≤ (22047 / 125000) := by
  have h := checkLog_sound (w := (10106079841 / 114893920159)) (n := 12)
    (lo := (176375999 / 1000000000)) (hi := (22047 / 125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 52393920159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 52393920159) = 1/(52393920159 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13581 : Bounds (-22047 / 125000) (-176375999 / 1000000000) (Real.log (52393920159 / 62500000000)) := by
  have h := reflection_log_13581_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13582_neg : (86893651 / 500000000) ≤ -Real.log (33619025839 / 40000000000) ∧
    -Real.log (33619025839 / 40000000000) ≤ (173787303 / 1000000000) := by
  have h := checkLog_sound (w := (6380974161 / 73619025839)) (n := 12)
    (lo := (86893651 / 500000000)) (hi := (173787303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 33619025839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 33619025839) = 1/(33619025839 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13582 : Bounds (-173787303 / 1000000000) (-86893651 / 500000000) (Real.log (33619025839 / 40000000000)) := by
  have h := reflection_log_13582_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13583_neg : (422940797 / 500000000) ≤ -Real.log (500000000000 / 1165015526269) ∧
    -Real.log (500000000000 / 1165015526269) ≤ (211470399 / 250000000) := by
  have h := checkLog_sound (w := (165015526269 / 2165015526269)) (n := 12)
    (lo := (76367207 / 500000000)) (hi := (30546883 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1165015526269 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1165015526269 / 1000000000000) = 1/(500000000000 / 1165015526269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13583 : Bounds (422940797 / 500000000) (211470399 / 250000000) (Real.log (1165015526269 / 500000000000)) := by
  have h := reflection_log_13583_neg
  have he : Real.log (1165015526269 / 500000000000) = -Real.log (500000000000 / 1165015526269) := by
    rw [show ((1165015526269 / 500000000000) : ℝ) = ((500000000000 / 1165015526269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13584_neg : (852341047 / 1000000000) ≤ -Real.log (500000000000 / 1172565246771) ∧
    -Real.log (500000000000 / 1172565246771) ≤ (852341049 / 1000000000) := by
  have h := checkLog_sound (w := (172565246771 / 2172565246771)) (n := 12)
    (lo := (159193867 / 1000000000)) (hi := (39798467 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1172565246771 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1172565246771 / 1000000000000) = 1/(500000000000 / 1172565246771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13584 : Bounds (852341047 / 1000000000) (852341049 / 1000000000) (Real.log (1172565246771 / 500000000000)) := by
  have h := reflection_log_13584_neg
  have he : Real.log (1172565246771 / 500000000000) = -Real.log (500000000000 / 1172565246771) := by
    rw [show ((1172565246771 / 500000000000) : ℝ) = ((500000000000 / 1172565246771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13585_neg : (905571667 / 500000000) ≤ -Real.log (500000000000 / 3058718861209) ∧
    -Real.log (500000000000 / 3058718861209) ≤ (1811143337 / 1000000000) := by
  have h := checkLog_sound (w := (1058718861209 / 5058718861209)) (n := 12)
    (lo := (212424487 / 500000000)) (hi := (16993959 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3058718861209 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3058718861209 / 2000000000000) = 1/(500000000000 / 3058718861209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13585 : Bounds (905571667 / 500000000) (1811143337 / 1000000000) (Real.log (3058718861209 / 500000000000)) := by
  have h := reflection_log_13585_neg
  have he : Real.log (3058718861209 / 500000000000) = -Real.log (500000000000 / 3058718861209) := by
    rw [show ((3058718861209 / 500000000000) : ℝ) = ((500000000000 / 3058718861209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13586_neg : (182362057 / 100000000) ≤ -Real.log (500000000000 / 3097122302159) ∧
    -Real.log (500000000000 / 3097122302159) ≤ (1823620573 / 1000000000) := by
  have h := checkLog_sound (w := (1097122302159 / 5097122302159)) (n := 12)
    (lo := (43732621 / 100000000)) (hi := (437326211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3097122302159 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3097122302159 / 2000000000000) = 1/(500000000000 / 3097122302159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13586 : Bounds (182362057 / 100000000) (1823620573 / 1000000000) (Real.log (3097122302159 / 500000000000)) := by
  have h := reflection_log_13586_neg
  have he : Real.log (3097122302159 / 500000000000) = -Real.log (500000000000 / 3097122302159) := by
    rw [show ((3097122302159 / 500000000000) : ℝ) = ((500000000000 / 3097122302159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13587_neg : (10904541 / 20000000) ≤ -Real.log (40 / 69) ∧
    -Real.log (40 / 69) ≤ (545227051 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 109)) (n := 12)
    (lo := (10904541 / 20000000)) (hi := (545227051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69 / 40) = 1/(40 / 69) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13587 : Bounds (10904541 / 20000000) (545227051 / 1000000000) (Real.log (69 / 40)) := by
  have h := reflection_log_13587_neg
  have he : Real.log (69 / 40) = -Real.log (40 / 69) := by
    rw [show ((69 / 40) : ℝ) = ((40 / 69) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13588_neg : (64549209 / 50000000) ≤ -Real.log (11 / 40) ∧
    -Real.log (11 / 40) ≤ (645492091 / 500000000) := by
  have h := checkLog_sound (w := (9 / 31)) (n := 12)
    (lo := (597837 / 1000000)) (hi := (597837001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 11) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20 / 11) = 1/(11 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13588 : Bounds (-645492091 / 500000000) (-64549209 / 50000000) (Real.log (11 / 40)) := by
  have h := reflection_log_13588_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13589_neg : (724737 / 1000000000) ≤ -Real.log (40000 / 40029) ∧
    -Real.log (40000 / 40029) ≤ (362369 / 500000000) := by
  have h := checkLog_sound (w := (29 / 80029)) (n := 12)
    (lo := (724737 / 1000000000)) (hi := (362369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40029 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40029 / 40000) = 1/(40000 / 40029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13589 : Bounds (724737 / 1000000000) (362369 / 500000000) (Real.log (40029 / 40000)) := by
  have h := reflection_log_13589_neg
  have he : Real.log (40029 / 40000) = -Real.log (40000 / 40029) := by
    rw [show ((40029 / 40000) : ℝ) = ((40000 / 40029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13590_neg : (362631 / 500000000) ≤ -Real.log (39971 / 40000) ∧
    -Real.log (39971 / 40000) ≤ (725263 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 79971)) (n := 12)
    (lo := (362631 / 500000000)) (hi := (725263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 39971) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 39971) = 1/(39971 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13590 : Bounds (-725263 / 1000000000) (-362631 / 500000000) (Real.log (39971 / 40000)) := by
  have h := reflection_log_13590_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13591_neg : (67506763 / 200000000) ≤ -Real.log (1000000 / 1401487) ∧
    -Real.log (1000000 / 1401487) ≤ (42191727 / 125000000) := by
  have h := checkLog_sound (w := (401487 / 2401487)) (n := 12)
    (lo := (67506763 / 200000000)) (hi := (42191727 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1401487 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1401487 / 1000000) = 1/(1000000 / 1401487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13591 : Bounds (67506763 / 200000000) (42191727 / 125000000) (Real.log (1401487 / 1000000)) := by
  have h := reflection_log_13591_neg
  have he : Real.log (1401487 / 1000000) = -Real.log (1000000 / 1401487) := by
    rw [show ((1401487 / 1000000) : ℝ) = ((1000000 / 1401487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13592_neg : (513307033 / 1000000000) ≤ -Real.log (598513 / 1000000) ∧
    -Real.log (598513 / 1000000) ≤ (256653517 / 500000000) := by
  have h := checkLog_sound (w := (401487 / 1598513)) (n := 12)
    (lo := (513307033 / 1000000000)) (hi := (256653517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 598513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 598513) = 1/(598513 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13592 : Bounds (-256653517 / 500000000) (-513307033 / 1000000000) (Real.log (598513 / 1000000)) := by
  have h := reflection_log_13592_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13593_neg : (33947273 / 100000000) ≤ -Real.log (1000000 / 1404207) ∧
    -Real.log (1000000 / 1404207) ≤ (339472731 / 1000000000) := by
  have h := checkLog_sound (w := (404207 / 2404207)) (n := 12)
    (lo := (33947273 / 100000000)) (hi := (339472731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1404207 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1404207 / 1000000) = 1/(1000000 / 1404207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13593 : Bounds (33947273 / 100000000) (339472731 / 1000000000) (Real.log (1404207 / 1000000)) := by
  have h := reflection_log_13593_neg
  have he : Real.log (1404207 / 1000000) = -Real.log (1000000 / 1404207) := by
    rw [show ((1404207 / 1000000) : ℝ) = ((1000000 / 1404207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13594_neg : (517861987 / 1000000000) ≤ -Real.log (595793 / 1000000) ∧
    -Real.log (595793 / 1000000) ≤ (129465497 / 250000000) := by
  have h := checkLog_sound (w := (404207 / 1595793)) (n := 12)
    (lo := (517861987 / 1000000000)) (hi := (129465497 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 595793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 595793) = 1/(595793 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13594 : Bounds (-129465497 / 250000000) (-517861987 / 1000000000) (Real.log (595793 / 1000000)) := by
  have h := reflection_log_13594_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13595_neg : (178389257 / 1000000000) ≤ -Real.log (836616701151 / 1000000000000) ∧
    -Real.log (836616701151 / 1000000000000) ≤ (89194629 / 500000000) := by
  have h := checkLog_sound (w := (163383298849 / 1836616701151)) (n := 12)
    (lo := (178389257 / 1000000000)) (hi := (89194629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 836616701151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 836616701151) = 1/(836616701151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13595 : Bounds (-89194629 / 500000000) (-178389257 / 1000000000) (Real.log (836616701151 / 1000000000000)) := by
  have h := reflection_log_13595_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13596_neg : (175773217 / 1000000000) ≤ -Real.log (838808188831 / 1000000000000) ∧
    -Real.log (838808188831 / 1000000000000) ≤ (87886609 / 500000000) := by
  have h := checkLog_sound (w := (161191811169 / 1838808188831)) (n := 12)
    (lo := (175773217 / 1000000000)) (hi := (87886609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 838808188831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 838808188831) = 1/(838808188831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13596 : Bounds (-87886609 / 500000000) (-175773217 / 1000000000) (Real.log (838808188831 / 1000000000000)) := by
  have h := reflection_log_13596_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13597_neg : (53177553 / 62500000) ≤ -Real.log (500000000000 / 1170807484549) ∧
    -Real.log (500000000000 / 1170807484549) ≤ (17016817 / 20000000) := by
  have h := checkLog_sound (w := (170807484549 / 2170807484549)) (n := 12)
    (lo := (39423417 / 250000000)) (hi := (157693669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1170807484549 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1170807484549 / 1000000000000) = 1/(500000000000 / 1170807484549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13597 : Bounds (53177553 / 62500000) (17016817 / 20000000) (Real.log (1170807484549 / 500000000000)) := by
  have h := reflection_log_13597_neg
  have he : Real.log (1170807484549 / 500000000000) = -Real.log (500000000000 / 1170807484549) := by
    rw [show ((1170807484549 / 500000000000) : ℝ) = ((500000000000 / 1170807484549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13598_neg : (857334717 / 1000000000) ≤ -Real.log (500000000000 / 1178435295481) ∧
    -Real.log (500000000000 / 1178435295481) ≤ (857334719 / 1000000000) := by
  have h := checkLog_sound (w := (178435295481 / 2178435295481)) (n := 12)
    (lo := (164187537 / 1000000000)) (hi := (82093769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1178435295481 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1178435295481 / 1000000000000) = 1/(500000000000 / 1178435295481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13598 : Bounds (857334717 / 1000000000) (857334719 / 1000000000) (Real.log (1178435295481 / 500000000000)) := by
  have h := reflection_log_13598_neg
  have he : Real.log (1178435295481 / 500000000000) = -Real.log (500000000000 / 1178435295481) := by
    rw [show ((1178435295481 / 500000000000) : ℝ) = ((500000000000 / 1178435295481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13599_neg : (182362057 / 100000000) ≤ -Real.log (250000000000 / 1548561151079) ∧
    -Real.log (250000000000 / 1548561151079) ≤ (1823620573 / 1000000000) := by
  have h := checkLog_sound (w := (548561151079 / 2548561151079)) (n := 12)
    (lo := (43732621 / 100000000)) (hi := (437326211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1548561151079 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1548561151079 / 1000000000000) = 1/(250000000000 / 1548561151079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13599 : Bounds (182362057 / 100000000) (1823620573 / 1000000000) (Real.log (1548561151079 / 250000000000)) := by
  have h := reflection_log_13599_neg
  have he : Real.log (1548561151079 / 250000000000) = -Real.log (250000000000 / 1548561151079) := by
    rw [show ((1548561151079 / 250000000000) : ℝ) = ((250000000000 / 1548561151079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13600_neg : (183621123 / 100000000) ≤ -Real.log (125000000000 / 784090909091) ∧
    -Real.log (125000000000 / 784090909091) ≤ (1836211233 / 1000000000) := by
  have h := checkLog_sound (w := (284090909091 / 1284090909091)) (n := 12)
    (lo := (44991687 / 100000000)) (hi := (449916871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((784090909091 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(784090909091 / 500000000000) = 1/(125000000000 / 784090909091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13600 : Bounds (183621123 / 100000000) (1836211233 / 1000000000) (Real.log (784090909091 / 125000000000)) := by
  have h := reflection_log_13600_neg
  have he : Real.log (784090909091 / 125000000000) = -Real.log (125000000000 / 784090909091) := by
    rw [show ((784090909091 / 125000000000) : ℝ) = ((125000000000 / 784090909091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13601_neg : (54696467 / 100000000) ≤ -Real.log (125 / 216) ∧
    -Real.log (125 / 216) ≤ (546964671 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 341)) (n := 12)
    (lo := (54696467 / 100000000)) (hi := (546964671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216 / 125) = 1/(125 / 216) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13601 : Bounds (54696467 / 100000000) (546964671 / 1000000000) (Real.log (216 / 125)) := by
  have h := reflection_log_13601_neg
  have he : Real.log (216 / 125) = -Real.log (125 / 216) := by
    rw [show ((216 / 125) : ℝ) = ((125 / 216) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13602_neg : (325488303 / 250000000) ≤ -Real.log (34 / 125) ∧
    -Real.log (34 / 125) ≤ (650976607 / 500000000) := by
  have h := checkLog_sound (w := (57 / 193)) (n := 12)
    (lo := (38050377 / 62500000)) (hi := (608806033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 68) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 68) = 1/(34 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13602 : Bounds (-650976607 / 500000000) (-325488303 / 250000000) (Real.log (34 / 125)) := by
  have h := reflection_log_13602_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13603_neg : (145547 / 200000000) ≤ -Real.log (125000 / 125091) ∧
    -Real.log (125000 / 125091) ≤ (90967 / 125000000) := by
  have h := checkLog_sound (w := (91 / 250091)) (n := 12)
    (lo := (145547 / 200000000)) (hi := (90967 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125091 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125091 / 125000) = 1/(125000 / 125091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13603 : Bounds (145547 / 200000000) (90967 / 125000000) (Real.log (125091 / 125000)) := by
  have h := reflection_log_13603_neg
  have he : Real.log (125091 / 125000) = -Real.log (125000 / 125091) := by
    rw [show ((125091 / 125000) : ℝ) = ((125000 / 125091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13604_neg : (145653 / 200000000) ≤ -Real.log (124909 / 125000) ∧
    -Real.log (124909 / 125000) ≤ (364133 / 500000000) := by
  have h := checkLog_sound (w := (91 / 249909)) (n := 12)
    (lo := (145653 / 200000000)) (hi := (364133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124909) = 1/(124909 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13604 : Bounds (-364133 / 500000000) (-145653 / 200000000) (Real.log (124909 / 125000)) := by
  have h := reflection_log_13604_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13605_neg : (169511989 / 500000000) ≤ -Real.log (1000000 / 1403577) ∧
    -Real.log (1000000 / 1403577) ≤ (339023979 / 1000000000) := by
  have h := checkLog_sound (w := (403577 / 2403577)) (n := 12)
    (lo := (169511989 / 500000000)) (hi := (339023979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1403577 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1403577 / 1000000) = 1/(1000000 / 1403577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13605 : Bounds (169511989 / 500000000) (339023979 / 1000000000) (Real.log (1403577 / 1000000)) := by
  have h := reflection_log_13605_neg
  have he : Real.log (1403577 / 1000000) = -Real.log (1000000 / 1403577) := by
    rw [show ((1403577 / 1000000) : ℝ) = ((1000000 / 1403577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13606_neg : (129201283 / 250000000) ≤ -Real.log (596423 / 1000000) ∧
    -Real.log (596423 / 1000000) ≤ (516805133 / 1000000000) := by
  have h := checkLog_sound (w := (403577 / 1596423)) (n := 12)
    (lo := (129201283 / 250000000)) (hi := (516805133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 596423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 596423) = 1/(596423 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13606 : Bounds (-516805133 / 1000000000) (-129201283 / 250000000) (Real.log (596423 / 1000000)) := by
  have h := reflection_log_13606_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13607_neg : (340965697 / 1000000000) ≤ -Real.log (200000 / 281261) ∧
    -Real.log (200000 / 281261) ≤ (170482849 / 500000000) := by
  have h := checkLog_sound (w := (81261 / 481261)) (n := 12)
    (lo := (340965697 / 1000000000)) (hi := (170482849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((281261 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(281261 / 200000) = 1/(200000 / 281261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13607 : Bounds (340965697 / 1000000000) (170482849 / 500000000) (Real.log (281261 / 200000)) := by
  have h := reflection_log_13607_neg
  have he : Real.log (281261 / 200000) = -Real.log (200000 / 281261) := by
    rw [show ((281261 / 200000) : ℝ) = ((200000 / 281261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13608_neg : (521389559 / 1000000000) ≤ -Real.log (118739 / 200000) ∧
    -Real.log (118739 / 200000) ≤ (13034739 / 25000000) := by
  have h := checkLog_sound (w := (81261 / 318739)) (n := 12)
    (lo := (521389559 / 1000000000)) (hi := (13034739 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 118739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 118739) = 1/(118739 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13608 : Bounds (-13034739 / 25000000) (-521389559 / 1000000000) (Real.log (118739 / 200000)) := by
  have h := reflection_log_13608_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13609_neg : (90211931 / 500000000) ≤ -Real.log (33396649879 / 40000000000) ∧
    -Real.log (33396649879 / 40000000000) ≤ (180423863 / 1000000000) := by
  have h := checkLog_sound (w := (6603350121 / 73396649879)) (n := 12)
    (lo := (90211931 / 500000000)) (hi := (180423863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 33396649879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 33396649879) = 1/(33396649879 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13609 : Bounds (-180423863 / 1000000000) (-90211931 / 500000000) (Real.log (33396649879 / 40000000000)) := by
  have h := reflection_log_13609_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13610_neg : (177781153 / 1000000000) ≤ -Real.log (837125605071 / 1000000000000) ∧
    -Real.log (837125605071 / 1000000000000) ≤ (88890577 / 500000000) := by
  have h := checkLog_sound (w := (162874394929 / 1837125605071)) (n := 12)
    (lo := (177781153 / 1000000000)) (hi := (88890577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 837125605071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 837125605071) = 1/(837125605071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13610 : Bounds (-88890577 / 500000000) (-177781153 / 1000000000) (Real.log (837125605071 / 1000000000000)) := by
  have h := reflection_log_13610_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13611_neg : (855829109 / 1000000000) ≤ -Real.log (250000000000 / 588331184411) ∧
    -Real.log (250000000000 / 588331184411) ≤ (855829111 / 1000000000) := by
  have h := checkLog_sound (w := (88331184411 / 1088331184411)) (n := 12)
    (lo := (162681929 / 1000000000)) (hi := (16268193 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588331184411 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(588331184411 / 500000000000) = 1/(250000000000 / 588331184411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13611 : Bounds (855829109 / 1000000000) (855829111 / 1000000000) (Real.log (588331184411 / 250000000000)) := by
  have h := reflection_log_13611_neg
  have he : Real.log (588331184411 / 250000000000) = -Real.log (250000000000 / 588331184411) := by
    rw [show ((588331184411 / 250000000000) : ℝ) = ((250000000000 / 588331184411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13612_neg : (107794407 / 125000000) ≤ -Real.log (10000000000 / 23687331037) ∧
    -Real.log (10000000000 / 23687331037) ≤ (431177629 / 500000000) := by
  have h := checkLog_sound (w := (3687331037 / 43687331037)) (n := 12)
    (lo := (42302019 / 250000000)) (hi := (169208077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23687331037 / 20000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(23687331037 / 20000000000) = 1/(10000000000 / 23687331037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13612 : Bounds (107794407 / 125000000) (431177629 / 500000000) (Real.log (23687331037 / 10000000000)) := by
  have h := reflection_log_13612_neg
  have he : Real.log (23687331037 / 10000000000) = -Real.log (10000000000 / 23687331037) := by
    rw [show ((23687331037 / 10000000000) : ℝ) = ((10000000000 / 23687331037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13613_neg : (183621123 / 100000000) ≤ -Real.log (500000000000 / 3136363636363) ∧
    -Real.log (500000000000 / 3136363636363) ≤ (1836211233 / 1000000000) := by
  have h := checkLog_sound (w := (1136363636363 / 5136363636363)) (n := 12)
    (lo := (44991687 / 100000000)) (hi := (449916871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3136363636363 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3136363636363 / 2000000000000) = 1/(500000000000 / 3136363636363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13613 : Bounds (183621123 / 100000000) (1836211233 / 1000000000) (Real.log (3136363636363 / 500000000000)) := by
  have h := reflection_log_13613_neg
  have he : Real.log (3136363636363 / 500000000000) = -Real.log (500000000000 / 3136363636363) := by
    rw [show ((3136363636363 / 500000000000) : ℝ) = ((500000000000 / 3136363636363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13614_neg : (1848917881 / 1000000000) ≤ -Real.log (125000000000 / 794117647059) ∧
    -Real.log (125000000000 / 794117647059) ≤ (462229471 / 250000000) := by
  have h := checkLog_sound (w := (294117647059 / 1294117647059)) (n := 12)
    (lo := (462623521 / 1000000000)) (hi := (231311761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((794117647059 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(794117647059 / 500000000000) = 1/(125000000000 / 794117647059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13614 : Bounds (1848917881 / 1000000000) (462229471 / 250000000) (Real.log (794117647059 / 125000000000)) := by
  have h := reflection_log_13614_neg
  have he : Real.log (794117647059 / 125000000000) = -Real.log (125000000000 / 794117647059) := by
    rw [show ((794117647059 / 125000000000) : ℝ) = ((125000000000 / 794117647059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13615_neg : (137174819 / 250000000) ≤ -Real.log (1000 / 1731) ∧
    -Real.log (1000 / 1731) ≤ (548699277 / 1000000000) := by
  have h := checkLog_sound (w := (731 / 2731)) (n := 12)
    (lo := (137174819 / 250000000)) (hi := (548699277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1731 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1731 / 1000) = 1/(1000 / 1731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13615 : Bounds (137174819 / 250000000) (548699277 / 1000000000) (Real.log (1731 / 1000)) := by
  have h := reflection_log_13615_neg
  have he : Real.log (1731 / 1000) = -Real.log (1000 / 1731) := by
    rw [show ((1731 / 1000) : ℝ) = ((1000 / 1731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13616_neg : (656521949 / 500000000) ≤ -Real.log (269 / 1000) ∧
    -Real.log (269 / 1000) ≤ (13130439 / 10000000) := by
  have h := checkLog_sound (w := (231 / 769)) (n := 12)
    (lo := (309948359 / 500000000)) (hi := (619896719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 269) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 269) = 1/(269 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13616 : Bounds (-13130439 / 10000000) (-656521949 / 500000000) (Real.log (269 / 1000)) := by
  have h := reflection_log_13616_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13617_neg : (182683 / 250000000) ≤ -Real.log (1000000 / 1000731) ∧
    -Real.log (1000000 / 1000731) ≤ (730733 / 1000000000) := by
  have h := checkLog_sound (w := (731 / 2000731)) (n := 12)
    (lo := (182683 / 250000000)) (hi := (730733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000731 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000731 / 1000000) = 1/(1000000 / 1000731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13617 : Bounds (182683 / 250000000) (730733 / 1000000000) (Real.log (1000731 / 1000000)) := by
  have h := reflection_log_13617_neg
  have he : Real.log (1000731 / 1000000) = -Real.log (1000000 / 1000731) := by
    rw [show ((1000731 / 1000000) : ℝ) = ((1000000 / 1000731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13618_neg : (731267 / 1000000000) ≤ -Real.log (999269 / 1000000) ∧
    -Real.log (999269 / 1000000) ≤ (182817 / 250000000) := by
  have h := checkLog_sound (w := (731 / 1999269)) (n := 12)
    (lo := (731267 / 1000000000)) (hi := (182817 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999269) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999269) = 1/(999269 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13618 : Bounds (-182817 / 250000000) (-731267 / 1000000000) (Real.log (999269 / 1000000)) := by
  have h := reflection_log_13618_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13619_neg : (340516903 / 1000000000) ≤ -Real.log (500000 / 702837) ∧
    -Real.log (500000 / 702837) ≤ (42564613 / 125000000) := by
  have h := checkLog_sound (w := (202837 / 1202837)) (n := 12)
    (lo := (340516903 / 1000000000)) (hi := (42564613 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((702837 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(702837 / 500000) = 1/(500000 / 702837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13619 : Bounds (340516903 / 1000000000) (42564613 / 125000000) (Real.log (702837 / 500000)) := by
  have h := reflection_log_13619_neg
  have he : Real.log (702837 / 500000) = -Real.log (500000 / 702837) := by
    rw [show ((702837 / 500000) : ℝ) = ((500000 / 702837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13620_neg : (65040911 / 125000000) ≤ -Real.log (297163 / 500000) ∧
    -Real.log (297163 / 500000) ≤ (520327289 / 1000000000) := by
  have h := checkLog_sound (w := (202837 / 797163)) (n := 12)
    (lo := (65040911 / 125000000)) (hi := (520327289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 297163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 297163) = 1/(297163 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13620 : Bounds (-520327289 / 1000000000) (-65040911 / 125000000) (Real.log (297163 / 500000)) := by
  have h := reflection_log_13620_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13621_neg : (171231059 / 500000000) ≤ -Real.log (1000000 / 1408411) ∧
    -Real.log (1000000 / 1408411) ≤ (342462119 / 1000000000) := by
  have h := checkLog_sound (w := (408411 / 2408411)) (n := 12)
    (lo := (171231059 / 500000000)) (hi := (342462119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1408411 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1408411 / 1000000) = 1/(1000000 / 1408411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13621 : Bounds (171231059 / 500000000) (342462119 / 1000000000) (Real.log (1408411 / 1000000)) := by
  have h := reflection_log_13621_neg
  have he : Real.log (1408411 / 1000000) = -Real.log (1000000 / 1408411) := by
    rw [show ((1408411 / 1000000) : ℝ) = ((1000000 / 1408411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13622_neg : (524943141 / 1000000000) ≤ -Real.log (591589 / 1000000) ∧
    -Real.log (591589 / 1000000) ≤ (262471571 / 500000000) := by
  have h := checkLog_sound (w := (408411 / 1591589)) (n := 12)
    (lo := (524943141 / 1000000000)) (hi := (262471571 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 591589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 591589) = 1/(591589 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13622 : Bounds (-262471571 / 500000000) (-524943141 / 1000000000) (Real.log (591589 / 1000000)) := by
  have h := reflection_log_13622_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13623_neg : (182481023 / 1000000000) ≤ -Real.log (833200455079 / 1000000000000) ∧
    -Real.log (833200455079 / 1000000000000) ≤ (1425633 / 7812500) := by
  have h := checkLog_sound (w := (166799544921 / 1833200455079)) (n := 12)
    (lo := (182481023 / 1000000000)) (hi := (1425633 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 833200455079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 833200455079) = 1/(833200455079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13623 : Bounds (-1425633 / 7812500) (-182481023 / 1000000000) (Real.log (833200455079 / 1000000000000)) := by
  have h := reflection_log_13623_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13624_neg : (35962077 / 200000000) ≤ -Real.log (208857151431 / 250000000000) ∧
    -Real.log (208857151431 / 250000000000) ≤ (89905193 / 500000000) := by
  have h := checkLog_sound (w := (41142848569 / 458857151431)) (n := 12)
    (lo := (35962077 / 200000000)) (hi := (89905193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 208857151431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 208857151431) = 1/(208857151431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13624 : Bounds (-89905193 / 500000000) (-35962077 / 200000000) (Real.log (208857151431 / 250000000000)) := by
  have h := reflection_log_13624_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13625_neg : (860844191 / 1000000000) ≤ -Real.log (500000000000 / 1182578248301) ∧
    -Real.log (500000000000 / 1182578248301) ≤ (860844193 / 1000000000) := by
  have h := checkLog_sound (w := (182578248301 / 2182578248301)) (n := 12)
    (lo := (167697011 / 1000000000)) (hi := (41924253 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1182578248301 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1182578248301 / 1000000000000) = 1/(500000000000 / 1182578248301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13625 : Bounds (860844191 / 1000000000) (860844193 / 1000000000) (Real.log (1182578248301 / 500000000000)) := by
  have h := reflection_log_13625_neg
  have he : Real.log (1182578248301 / 500000000000) = -Real.log (500000000000 / 1182578248301) := by
    rw [show ((1182578248301 / 500000000000) : ℝ) = ((500000000000 / 1182578248301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13626_neg : (867405259 / 1000000000) ≤ -Real.log (25000000000 / 59518136747) ∧
    -Real.log (25000000000 / 59518136747) ≤ (867405261 / 1000000000) := by
  have h := checkLog_sound (w := (9518136747 / 109518136747)) (n := 12)
    (lo := (174258079 / 1000000000)) (hi := (1089113 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59518136747 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(59518136747 / 50000000000) = 1/(25000000000 / 59518136747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13626 : Bounds (867405259 / 1000000000) (867405261 / 1000000000) (Real.log (59518136747 / 25000000000)) := by
  have h := reflection_log_13626_neg
  have he : Real.log (59518136747 / 25000000000) = -Real.log (25000000000 / 59518136747) := by
    rw [show ((59518136747 / 25000000000) : ℝ) = ((25000000000 / 59518136747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13627_neg : (1848917881 / 1000000000) ≤ -Real.log (100000000000 / 635294117647) ∧
    -Real.log (100000000000 / 635294117647) ≤ (462229471 / 250000000) := by
  have h := checkLog_sound (w := (235294117647 / 1035294117647)) (n := 12)
    (lo := (462623521 / 1000000000)) (hi := (231311761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((635294117647 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(635294117647 / 400000000000) = 1/(100000000000 / 635294117647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13627 : Bounds (1848917881 / 1000000000) (462229471 / 250000000) (Real.log (635294117647 / 100000000000)) := by
  have h := reflection_log_13627_neg
  have he : Real.log (635294117647 / 100000000000) = -Real.log (100000000000 / 635294117647) := by
    rw [show ((635294117647 / 100000000000) : ℝ) = ((100000000000 / 635294117647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13628_neg : (930871587 / 500000000) ≤ -Real.log (6250000000 / 40218401487) ∧
    -Real.log (6250000000 / 40218401487) ≤ (1861743177 / 1000000000) := by
  have h := checkLog_sound (w := (15218401487 / 65218401487)) (n := 12)
    (lo := (237724407 / 500000000)) (hi := (95089763 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40218401487 / 25000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(40218401487 / 25000000000) = 1/(6250000000 / 40218401487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13628 : Bounds (930871587 / 500000000) (1861743177 / 1000000000) (Real.log (40218401487 / 6250000000)) := by
  have h := reflection_log_13628_neg
  have he : Real.log (40218401487 / 6250000000) = -Real.log (6250000000 / 40218401487) := by
    rw [show ((40218401487 / 6250000000) : ℝ) = ((6250000000 / 40218401487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13629_neg : (275215439 / 500000000) ≤ -Real.log (500 / 867) ∧
    -Real.log (500 / 867) ≤ (550430879 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 1367)) (n := 12)
    (lo := (275215439 / 500000000)) (hi := (550430879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((867 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(867 / 500) = 1/(500 / 867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13629 : Bounds (275215439 / 500000000) (550430879 / 1000000000) (Real.log (867 / 500)) := by
  have h := reflection_log_13629_neg
  have he : Real.log (867 / 500) = -Real.log (500 / 867) := by
    rw [show ((867 / 500) : ℝ) = ((500 / 867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13630_neg : (1324258969 / 1000000000) ≤ -Real.log (133 / 500) ∧
    -Real.log (133 / 500) ≤ (1324258971 / 1000000000) := by
  have h := checkLog_sound (w := (117 / 383)) (n := 12)
    (lo := (631111789 / 1000000000)) (hi := (63111179 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 133) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 133) = 1/(133 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13630 : Bounds (-1324258971 / 1000000000) (-1324258969 / 1000000000) (Real.log (133 / 500)) := by
  have h := reflection_log_13630_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13631_neg : (73373 / 100000000) ≤ -Real.log (500000 / 500367) ∧
    -Real.log (500000 / 500367) ≤ (733731 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 1000367)) (n := 12)
    (lo := (73373 / 100000000)) (hi := (733731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500367 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500367 / 500000) = 1/(500000 / 500367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13631 : Bounds (73373 / 100000000) (733731 / 1000000000) (Real.log (500367 / 500000)) := by
  have h := reflection_log_13631_neg
  have he : Real.log (500367 / 500000) = -Real.log (500000 / 500367) := by
    rw [show ((500367 / 500000) : ℝ) = ((500000 / 500367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0213 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13632_neg : (734269 / 1000000000) ≤ -Real.log (499633 / 500000) ∧
    -Real.log (499633 / 500000) ≤ (73427 / 100000000) := by
  have h := checkLog_sound (w := (367 / 999633)) (n := 12)
    (lo := (734269 / 1000000000)) (hi := (73427 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499633) = 1/(499633 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13632 : Bounds (-73427 / 100000000) (-734269 / 1000000000) (Real.log (499633 / 500000)) := by
  have h := reflection_log_13632_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13633_neg : (171006287 / 500000000) ≤ -Real.log (500000 / 703889) ∧
    -Real.log (500000 / 703889) ≤ (13680503 / 40000000) := by
  have h := checkLog_sound (w := (203889 / 1203889)) (n := 12)
    (lo := (171006287 / 500000000)) (hi := (13680503 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703889 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703889 / 500000) = 1/(500000 / 703889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13633 : Bounds (171006287 / 500000000) (13680503 / 40000000) (Real.log (703889 / 500000)) := by
  have h := reflection_log_13633_neg
  have he : Real.log (703889 / 500000) = -Real.log (500000 / 703889) := by
    rw [show ((703889 / 500000) : ℝ) = ((500000 / 703889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13634_neg : (261936857 / 500000000) ≤ -Real.log (296111 / 500000) ∧
    -Real.log (296111 / 500000) ≤ (104774743 / 200000000) := by
  have h := checkLog_sound (w := (203889 / 796111)) (n := 12)
    (lo := (261936857 / 500000000)) (hi := (104774743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 296111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 296111) = 1/(296111 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13634 : Bounds (-104774743 / 200000000) (-261936857 / 500000000) (Real.log (296111 / 500000)) := by
  have h := reflection_log_13634_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13635_neg : (171980633 / 500000000) ≤ -Real.log (250000 / 352631) ∧
    -Real.log (250000 / 352631) ≤ (343961267 / 1000000000) := by
  have h := checkLog_sound (w := (102631 / 602631)) (n := 12)
    (lo := (171980633 / 500000000)) (hi := (343961267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352631 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352631 / 250000) = 1/(250000 / 352631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13635 : Bounds (171980633 / 500000000) (343961267 / 1000000000) (Real.log (352631 / 250000)) := by
  have h := reflection_log_13635_neg
  have he : Real.log (352631 / 250000) = -Real.log (250000 / 352631) := by
    rw [show ((352631 / 250000) : ℝ) = ((250000 / 352631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13636_neg : (66065159 / 125000000) ≤ -Real.log (147369 / 250000) ∧
    -Real.log (147369 / 250000) ≤ (528521273 / 1000000000) := by
  have h := checkLog_sound (w := (102631 / 397369)) (n := 12)
    (lo := (66065159 / 125000000)) (hi := (528521273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 147369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 147369) = 1/(147369 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13636 : Bounds (-528521273 / 1000000000) (-66065159 / 125000000) (Real.log (147369 / 250000)) := by
  have h := reflection_log_13636_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13637_neg : (36912001 / 200000000) ≤ -Real.log (51966877839 / 62500000000) ∧
    -Real.log (51966877839 / 62500000000) ≤ (92280003 / 500000000) := by
  have h := checkLog_sound (w := (10533122161 / 114466877839)) (n := 12)
    (lo := (36912001 / 200000000)) (hi := (92280003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 51966877839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 51966877839) = 1/(51966877839 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13637 : Bounds (-92280003 / 500000000) (-36912001 / 200000000) (Real.log (51966877839 / 62500000000)) := by
  have h := reflection_log_13637_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13638_neg : (181861139 / 1000000000) ≤ -Real.log (208429275679 / 250000000000) ∧
    -Real.log (208429275679 / 250000000000) ≤ (9093057 / 50000000) := by
  have h := checkLog_sound (w := (41570724321 / 458429275679)) (n := 12)
    (lo := (181861139 / 1000000000)) (hi := (9093057 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 208429275679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 208429275679) = 1/(208429275679 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13638 : Bounds (-9093057 / 50000000) (-181861139 / 1000000000) (Real.log (208429275679 / 250000000000)) := by
  have h := reflection_log_13638_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13639_neg : (54117893 / 62500000) ≤ -Real.log (62500000000 / 148569497587) ∧
    -Real.log (62500000000 / 148569497587) ≤ (86588629 / 100000000) := by
  have h := checkLog_sound (w := (23569497587 / 273569497587)) (n := 12)
    (lo := (43184777 / 250000000)) (hi := (172739109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148569497587 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(148569497587 / 125000000000) = 1/(62500000000 / 148569497587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13639 : Bounds (54117893 / 62500000) (86588629 / 100000000) (Real.log (148569497587 / 62500000000)) := by
  have h := reflection_log_13639_neg
  have he : Real.log (148569497587 / 62500000000) = -Real.log (62500000000 / 148569497587) := by
    rw [show ((148569497587 / 62500000000) : ℝ) = ((62500000000 / 148569497587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13640_neg : (436241269 / 500000000) ≤ -Real.log (250000000000 / 598210953457) ∧
    -Real.log (250000000000 / 598210953457) ≤ (43624127 / 50000000) := by
  have h := checkLog_sound (w := (98210953457 / 1098210953457)) (n := 12)
    (lo := (89667679 / 500000000)) (hi := (179335359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598210953457 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(598210953457 / 500000000000) = 1/(250000000000 / 598210953457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13640 : Bounds (436241269 / 500000000) (43624127 / 50000000) (Real.log (598210953457 / 250000000000)) := by
  have h := reflection_log_13640_neg
  have he : Real.log (598210953457 / 250000000000) = -Real.log (250000000000 / 598210953457) := by
    rw [show ((598210953457 / 250000000000) : ℝ) = ((250000000000 / 598210953457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13641_neg : (930871587 / 500000000) ≤ -Real.log (500000000000 / 3217472118959) ∧
    -Real.log (500000000000 / 3217472118959) ≤ (1861743177 / 1000000000) := by
  have h := checkLog_sound (w := (1217472118959 / 5217472118959)) (n := 12)
    (lo := (237724407 / 500000000)) (hi := (95089763 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3217472118959 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3217472118959 / 2000000000000) = 1/(500000000000 / 3217472118959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13641 : Bounds (930871587 / 500000000) (1861743177 / 1000000000) (Real.log (3217472118959 / 500000000000)) := by
  have h := reflection_log_13641_neg
  have he : Real.log (3217472118959 / 500000000000) = -Real.log (500000000000 / 3217472118959) := by
    rw [show ((3217472118959 / 500000000000) : ℝ) = ((500000000000 / 3217472118959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13642_neg : (1874689847 / 1000000000) ≤ -Real.log (500000000000 / 3259398496241) ∧
    -Real.log (500000000000 / 3259398496241) ≤ (37493797 / 20000000) := by
  have h := checkLog_sound (w := (1259398496241 / 5259398496241)) (n := 12)
    (lo := (488395487 / 1000000000)) (hi := (15262359 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3259398496241 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3259398496241 / 2000000000000) = 1/(500000000000 / 3259398496241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13642 : Bounds (1874689847 / 1000000000) (37493797 / 20000000) (Real.log (3259398496241 / 500000000000)) := by
  have h := reflection_log_13642_neg
  have he : Real.log (3259398496241 / 500000000000) = -Real.log (500000000000 / 3259398496241) := by
    rw [show ((3259398496241 / 500000000000) : ℝ) = ((500000000000 / 3259398496241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13643_neg : (552159487 / 1000000000) ≤ -Real.log (1000 / 1737) ∧
    -Real.log (1000 / 1737) ≤ (2156873 / 3906250) := by
  have h := checkLog_sound (w := (737 / 2737)) (n := 12)
    (lo := (552159487 / 1000000000)) (hi := (2156873 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1737 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1737 / 1000) = 1/(1000 / 1737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13643 : Bounds (552159487 / 1000000000) (2156873 / 3906250) (Real.log (1737 / 1000)) := by
  have h := reflection_log_13643_neg
  have he : Real.log (1737 / 1000) = -Real.log (1000 / 1737) := by
    rw [show ((1737 / 1000) : ℝ) = ((1000 / 1737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13644_neg : (667800623 / 500000000) ≤ -Real.log (263 / 1000) ∧
    -Real.log (263 / 1000) ≤ (41737539 / 31250000) := by
  have h := checkLog_sound (w := (237 / 763)) (n := 12)
    (lo := (321227033 / 500000000)) (hi := (642454067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 263) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 263) = 1/(263 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13644 : Bounds (-41737539 / 31250000) (-667800623 / 500000000) (Real.log (263 / 1000)) := by
  have h := reflection_log_13644_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13645_neg : (92091 / 125000000) ≤ -Real.log (1000000 / 1000737) ∧
    -Real.log (1000000 / 1000737) ≤ (736729 / 1000000000) := by
  have h := checkLog_sound (w := (737 / 2000737)) (n := 12)
    (lo := (92091 / 125000000)) (hi := (736729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000737 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000737 / 1000000) = 1/(1000000 / 1000737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13645 : Bounds (92091 / 125000000) (736729 / 1000000000) (Real.log (1000737 / 1000000)) := by
  have h := reflection_log_13645_neg
  have he : Real.log (1000737 / 1000000) = -Real.log (1000000 / 1000737) := by
    rw [show ((1000737 / 1000000) : ℝ) = ((1000000 / 1000737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13646_neg : (737271 / 1000000000) ≤ -Real.log (999263 / 1000000) ∧
    -Real.log (999263 / 1000000) ≤ (92159 / 125000000) := by
  have h := checkLog_sound (w := (737 / 1999263)) (n := 12)
    (lo := (737271 / 1000000000)) (hi := (92159 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999263) = 1/(999263 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13646 : Bounds (-92159 / 125000000) (-737271 / 1000000000) (Real.log (999263 / 1000000)) := by
  have h := reflection_log_13646_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13647_neg : (343510977 / 1000000000) ≤ -Real.log (1000000 / 1409889) ∧
    -Real.log (1000000 / 1409889) ≤ (171755489 / 500000000) := by
  have h := checkLog_sound (w := (409889 / 2409889)) (n := 12)
    (lo := (343510977 / 1000000000)) (hi := (171755489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1409889 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1409889 / 1000000) = 1/(1000000 / 1409889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13647 : Bounds (343510977 / 1000000000) (171755489 / 500000000) (Real.log (1409889 / 1000000)) := by
  have h := reflection_log_13647_neg
  have he : Real.log (1409889 / 1000000) = -Real.log (1000000 / 1409889) := by
    rw [show ((1409889 / 1000000) : ℝ) = ((1000000 / 1409889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13648_neg : (32965289 / 62500000) ≤ -Real.log (590111 / 1000000) ∧
    -Real.log (590111 / 1000000) ≤ (4219557 / 8000000) := by
  have h := checkLog_sound (w := (409889 / 1590111)) (n := 12)
    (lo := (32965289 / 62500000)) (hi := (4219557 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 590111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 590111) = 1/(590111 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13648 : Bounds (-4219557 / 8000000) (-32965289 / 62500000) (Real.log (590111 / 1000000)) := by
  have h := reflection_log_13648_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13649_neg : (552741 / 1600000) ≤ -Real.log (250000 / 353161) ∧
    -Real.log (250000 / 353161) ≤ (172731563 / 500000000) := by
  have h := checkLog_sound (w := (103161 / 603161)) (n := 12)
    (lo := (552741 / 1600000)) (hi := (172731563 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353161 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353161 / 250000) = 1/(250000 / 353161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13649 : Bounds (552741 / 1600000) (172731563 / 500000000) (Real.log (353161 / 250000)) := by
  have h := reflection_log_13649_neg
  have he : Real.log (353161 / 250000) = -Real.log (250000 / 353161) := by
    rw [show ((353161 / 250000) : ℝ) = ((250000 / 353161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13650_neg : (532124169 / 1000000000) ≤ -Real.log (146839 / 250000) ∧
    -Real.log (146839 / 250000) ≤ (53212417 / 100000000) := by
  have h := checkLog_sound (w := (103161 / 396839)) (n := 12)
    (lo := (532124169 / 1000000000)) (hi := (53212417 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 146839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 146839) = 1/(146839 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13650 : Bounds (-53212417 / 100000000) (-532124169 / 1000000000) (Real.log (146839 / 250000)) := by
  have h := reflection_log_13650_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13651_neg : (186661043 / 1000000000) ≤ -Real.log (51857808079 / 62500000000) ∧
    -Real.log (51857808079 / 62500000000) ≤ (46665261 / 250000000) := by
  have h := checkLog_sound (w := (10642191921 / 114357808079)) (n := 12)
    (lo := (186661043 / 1000000000)) (hi := (46665261 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 51857808079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 51857808079) = 1/(51857808079 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13651 : Bounds (-46665261 / 250000000) (-186661043 / 1000000000) (Real.log (51857808079 / 62500000000)) := by
  have h := reflection_log_13651_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13652_neg : (91966823 / 500000000) ≤ -Real.log (831991007679 / 1000000000000) ∧
    -Real.log (831991007679 / 1000000000000) ≤ (183933647 / 1000000000) := by
  have h := checkLog_sound (w := (168008992321 / 1831991007679)) (n := 12)
    (lo := (91966823 / 500000000)) (hi := (183933647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 831991007679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 831991007679) = 1/(831991007679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13652 : Bounds (-183933647 / 1000000000) (-91966823 / 500000000) (Real.log (831991007679 / 1000000000000)) := by
  have h := reflection_log_13652_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13653_neg : (870955601 / 1000000000) ≤ -Real.log (50000000000 / 119459644033) ∧
    -Real.log (50000000000 / 119459644033) ≤ (870955603 / 1000000000) := by
  have h := checkLog_sound (w := (19459644033 / 219459644033)) (n := 12)
    (lo := (177808421 / 1000000000)) (hi := (88904211 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119459644033 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(119459644033 / 100000000000) = 1/(50000000000 / 119459644033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13653 : Bounds (870955601 / 1000000000) (870955603 / 1000000000) (Real.log (119459644033 / 50000000000)) := by
  have h := reflection_log_13653_neg
  have he : Real.log (119459644033 / 50000000000) = -Real.log (50000000000 / 119459644033) := by
    rw [show ((119459644033 / 50000000000) : ℝ) = ((50000000000 / 119459644033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13654_neg : (438793647 / 500000000) ≤ -Real.log (500000000000 / 1202544964213) ∧
    -Real.log (500000000000 / 1202544964213) ≤ (27424603 / 31250000) := by
  have h := checkLog_sound (w := (202544964213 / 2202544964213)) (n := 12)
    (lo := (92220057 / 500000000)) (hi := (36888023 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1202544964213 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1202544964213 / 1000000000000) = 1/(500000000000 / 1202544964213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13654 : Bounds (438793647 / 500000000) (27424603 / 31250000) (Real.log (1202544964213 / 500000000000)) := by
  have h := reflection_log_13654_neg
  have he : Real.log (1202544964213 / 500000000000) = -Real.log (500000000000 / 1202544964213) := by
    rw [show ((1202544964213 / 500000000000) : ℝ) = ((500000000000 / 1202544964213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13655_neg : (1874689847 / 1000000000) ≤ -Real.log (6250000000 / 40742481203) ∧
    -Real.log (6250000000 / 40742481203) ≤ (37493797 / 20000000) := by
  have h := checkLog_sound (w := (15742481203 / 65742481203)) (n := 12)
    (lo := (488395487 / 1000000000)) (hi := (15262359 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40742481203 / 25000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(40742481203 / 25000000000) = 1/(6250000000 / 40742481203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13655 : Bounds (1874689847 / 1000000000) (37493797 / 20000000) (Real.log (40742481203 / 6250000000)) := by
  have h := reflection_log_13655_neg
  have he : Real.log (40742481203 / 6250000000) = -Real.log (6250000000 / 40742481203) := by
    rw [show ((40742481203 / 6250000000) : ℝ) = ((6250000000 / 40742481203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13656_neg : (471940183 / 250000000) ≤ -Real.log (250000000000 / 1651140684411) ∧
    -Real.log (250000000000 / 1651140684411) ≤ (377552147 / 200000000) := by
  have h := checkLog_sound (w := (651140684411 / 2651140684411)) (n := 12)
    (lo := (125366593 / 250000000)) (hi := (501466373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1651140684411 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1651140684411 / 1000000000000) = 1/(250000000000 / 1651140684411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13656 : Bounds (471940183 / 250000000) (377552147 / 200000000) (Real.log (1651140684411 / 250000000000)) := by
  have h := reflection_log_13656_neg
  have he : Real.log (1651140684411 / 250000000000) = -Real.log (250000000000 / 1651140684411) := by
    rw [show ((1651140684411 / 250000000000) : ℝ) = ((250000000000 / 1651140684411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13657_neg : (553885113 / 1000000000) ≤ -Real.log (50 / 87) ∧
    -Real.log (50 / 87) ≤ (276942557 / 500000000) := by
  have h := checkLog_sound (w := (37 / 137)) (n := 12)
    (lo := (553885113 / 1000000000)) (hi := (276942557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87 / 50) = 1/(50 / 87) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13657 : Bounds (553885113 / 1000000000) (276942557 / 500000000) (Real.log (87 / 50)) := by
  have h := reflection_log_13657_neg
  have he : Real.log (87 / 50) = -Real.log (50 / 87) := by
    rw [show ((87 / 50) : ℝ) = ((50 / 87) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13658_neg : (1347073647 / 1000000000) ≤ -Real.log (13 / 50) ∧
    -Real.log (13 / 50) ≤ (1347073649 / 1000000000) := by
  have h := checkLog_sound (w := (6 / 19)) (n := 12)
    (lo := (653926467 / 1000000000)) (hi := (163481617 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 13) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25 / 13) = 1/(13 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13658 : Bounds (-1347073649 / 1000000000) (-1347073647 / 1000000000) (Real.log (13 / 50)) := by
  have h := reflection_log_13658_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13659_neg : (369863 / 500000000) ≤ -Real.log (50000 / 50037) ∧
    -Real.log (50000 / 50037) ≤ (739727 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 100037)) (n := 12)
    (lo := (369863 / 500000000)) (hi := (739727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50037 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50037 / 50000) = 1/(50000 / 50037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13659 : Bounds (369863 / 500000000) (739727 / 1000000000) (Real.log (50037 / 50000)) := by
  have h := reflection_log_13659_neg
  have he : Real.log (50037 / 50000) = -Real.log (50000 / 50037) := by
    rw [show ((50037 / 50000) : ℝ) = ((50000 / 50037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13660_neg : (740273 / 1000000000) ≤ -Real.log (49963 / 50000) ∧
    -Real.log (49963 / 50000) ≤ (370137 / 500000000) := by
  have h := checkLog_sound (w := (37 / 99963)) (n := 12)
    (lo := (740273 / 1000000000)) (hi := (370137 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 49963) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 49963) = 1/(49963 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13660 : Bounds (-370137 / 500000000) (-740273 / 1000000000) (Real.log (49963 / 50000)) := by
  have h := reflection_log_13660_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13661_neg : (86253201 / 250000000) ≤ -Real.log (125000 / 176501) ∧
    -Real.log (125000 / 176501) ≤ (69002561 / 200000000) := by
  have h := checkLog_sound (w := (51501 / 301501)) (n := 12)
    (lo := (86253201 / 250000000)) (hi := (69002561 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176501 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176501 / 125000) = 1/(125000 / 176501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13661 : Bounds (86253201 / 250000000) (69002561 / 200000000) (Real.log (176501 / 125000)) := by
  have h := reflection_log_13661_neg
  have he : Real.log (176501 / 125000) = -Real.log (125000 / 176501) := by
    rw [show ((176501 / 125000) : ℝ) = ((125000 / 176501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13662_neg : (33190121 / 62500000) ≤ -Real.log (73499 / 125000) ∧
    -Real.log (73499 / 125000) ≤ (531041937 / 1000000000) := by
  have h := checkLog_sound (w := (51501 / 198499)) (n := 12)
    (lo := (33190121 / 62500000)) (hi := (531041937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 73499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 73499) = 1/(73499 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13662 : Bounds (-531041937 / 1000000000) (-33190121 / 62500000) (Real.log (73499 / 125000)) := by
  have h := reflection_log_13662_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13663_neg : (346968387 / 1000000000) ≤ -Real.log (250000 / 353693) ∧
    -Real.log (250000 / 353693) ≤ (86742097 / 250000000) := by
  have h := checkLog_sound (w := (103693 / 603693)) (n := 12)
    (lo := (346968387 / 1000000000)) (hi := (86742097 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353693 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353693 / 250000) = 1/(250000 / 353693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13663 : Bounds (346968387 / 1000000000) (86742097 / 250000000) (Real.log (353693 / 250000)) := by
  have h := reflection_log_13663_neg
  have he : Real.log (353693 / 250000) = -Real.log (250000 / 353693) := by
    rw [show ((353693 / 250000) : ℝ) = ((250000 / 353693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13664_neg : (133938441 / 250000000) ≤ -Real.log (146307 / 250000) ∧
    -Real.log (146307 / 250000) ≤ (107150753 / 200000000) := by
  have h := checkLog_sound (w := (103693 / 396307)) (n := 12)
    (lo := (133938441 / 250000000)) (hi := (107150753 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 146307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 146307) = 1/(146307 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13664 : Bounds (-107150753 / 200000000) (-133938441 / 250000000) (Real.log (146307 / 250000)) := by
  have h := reflection_log_13664_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13665_neg : (5899543 / 31250000) ≤ -Real.log (51747761751 / 62500000000) ∧
    -Real.log (51747761751 / 62500000000) ≤ (188785377 / 1000000000) := by
  have h := checkLog_sound (w := (10752238249 / 114247761751)) (n := 12)
    (lo := (5899543 / 31250000)) (hi := (188785377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 51747761751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 51747761751) = 1/(51747761751 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13665 : Bounds (-188785377 / 1000000000) (-5899543 / 31250000) (Real.log (51747761751 / 62500000000)) := by
  have h := reflection_log_13665_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13666_neg : (186029131 / 1000000000) ≤ -Real.log (12972646999 / 15625000000) ∧
    -Real.log (12972646999 / 15625000000) ≤ (46507283 / 250000000) := by
  have h := checkLog_sound (w := (2652353001 / 28597646999)) (n := 12)
    (lo := (186029131 / 1000000000)) (hi := (46507283 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 12972646999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 12972646999) = 1/(12972646999 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13666 : Bounds (-46507283 / 250000000) (-186029131 / 1000000000) (Real.log (12972646999 / 15625000000)) := by
  have h := reflection_log_13666_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13667_neg : (43802737 / 50000000) ≤ -Real.log (50000000000 / 120070341093) ∧
    -Real.log (50000000000 / 120070341093) ≤ (438027371 / 500000000) := by
  have h := checkLog_sound (w := (20070341093 / 220070341093)) (n := 12)
    (lo := (4572689 / 25000000)) (hi := (182907561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120070341093 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(120070341093 / 100000000000) = 1/(50000000000 / 120070341093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13667 : Bounds (43802737 / 50000000) (438027371 / 500000000) (Real.log (120070341093 / 50000000000)) := by
  have h := reflection_log_13667_neg
  have he : Real.log (120070341093 / 50000000000) = -Real.log (50000000000 / 120070341093) := by
    rw [show ((120070341093 / 50000000000) : ℝ) = ((50000000000 / 120070341093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13668_neg : (17654443 / 20000000) ≤ -Real.log (500000000000 / 1208735740601) ∧
    -Real.log (500000000000 / 1208735740601) ≤ (110340269 / 125000000) := by
  have h := checkLog_sound (w := (208735740601 / 2208735740601)) (n := 12)
    (lo := (18957497 / 100000000)) (hi := (189574971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1208735740601 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1208735740601 / 1000000000000) = 1/(500000000000 / 1208735740601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13668 : Bounds (17654443 / 20000000) (110340269 / 125000000) (Real.log (1208735740601 / 500000000000)) := by
  have h := reflection_log_13668_neg
  have he : Real.log (1208735740601 / 500000000000) = -Real.log (500000000000 / 1208735740601) := by
    rw [show ((1208735740601 / 500000000000) : ℝ) = ((500000000000 / 1208735740601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13669_neg : (471940183 / 250000000) ≤ -Real.log (500000000000 / 3302281368821) ∧
    -Real.log (500000000000 / 3302281368821) ≤ (377552147 / 200000000) := by
  have h := checkLog_sound (w := (1302281368821 / 5302281368821)) (n := 12)
    (lo := (125366593 / 250000000)) (hi := (501466373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3302281368821 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3302281368821 / 2000000000000) = 1/(500000000000 / 3302281368821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13669 : Bounds (471940183 / 250000000) (377552147 / 200000000) (Real.log (3302281368821 / 500000000000)) := by
  have h := reflection_log_13669_neg
  have he : Real.log (3302281368821 / 500000000000) = -Real.log (500000000000 / 3302281368821) := by
    rw [show ((3302281368821 / 500000000000) : ℝ) = ((500000000000 / 3302281368821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13670_neg : (47523969 / 25000000) ≤ -Real.log (250000000000 / 1673076923077) ∧
    -Real.log (250000000000 / 1673076923077) ≤ (1900958763 / 1000000000) := by
  have h := checkLog_sound (w := (673076923077 / 2673076923077)) (n := 12)
    (lo := (1286661 / 2500000)) (hi := (514664401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1673076923077 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1673076923077 / 1000000000000) = 1/(250000000000 / 1673076923077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13670 : Bounds (47523969 / 25000000) (1900958763 / 1000000000) (Real.log (1673076923077 / 250000000000)) := by
  have h := reflection_log_13670_neg
  have he : Real.log (1673076923077 / 250000000000) = -Real.log (250000000000 / 1673076923077) := by
    rw [show ((1673076923077 / 250000000000) : ℝ) = ((250000000000 / 1673076923077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13671_neg : (277803883 / 500000000) ≤ -Real.log (1000 / 1743) ∧
    -Real.log (1000 / 1743) ≤ (555607767 / 1000000000) := by
  have h := checkLog_sound (w := (743 / 2743)) (n := 12)
    (lo := (277803883 / 500000000)) (hi := (555607767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1743 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1743 / 1000) = 1/(1000 / 1743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13671 : Bounds (277803883 / 500000000) (555607767 / 1000000000) (Real.log (1743 / 1000)) := by
  have h := reflection_log_13671_neg
  have he : Real.log (1743 / 1000) = -Real.log (1000 / 1743) := by
    rw [show ((1743 / 1000) : ℝ) = ((1000 / 1743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13672_neg : (1358679193 / 1000000000) ≤ -Real.log (257 / 1000) ∧
    -Real.log (257 / 1000) ≤ (271735839 / 200000000) := by
  have h := checkLog_sound (w := (243 / 757)) (n := 12)
    (lo := (665532013 / 1000000000)) (hi := (332766007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 257) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 257) = 1/(257 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13672 : Bounds (-271735839 / 200000000) (-1358679193 / 1000000000) (Real.log (257 / 1000)) := by
  have h := reflection_log_13672_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13673_neg : (185681 / 250000000) ≤ -Real.log (1000000 / 1000743) ∧
    -Real.log (1000000 / 1000743) ≤ (29709 / 40000000) := by
  have h := checkLog_sound (w := (743 / 2000743)) (n := 12)
    (lo := (185681 / 250000000)) (hi := (29709 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000743 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000743 / 1000000) = 1/(1000000 / 1000743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13673 : Bounds (185681 / 250000000) (29709 / 40000000) (Real.log (1000743 / 1000000)) := by
  have h := reflection_log_13673_neg
  have he : Real.log (1000743 / 1000000) = -Real.log (1000000 / 1000743) := by
    rw [show ((1000743 / 1000000) : ℝ) = ((1000000 / 1000743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13674_neg : (185819 / 250000000) ≤ -Real.log (999257 / 1000000) ∧
    -Real.log (999257 / 1000000) ≤ (743277 / 1000000000) := by
  have h := checkLog_sound (w := (743 / 1999257)) (n := 12)
    (lo := (185819 / 250000000)) (hi := (743277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999257) = 1/(999257 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13674 : Bounds (-743277 / 1000000000) (-185819 / 250000000) (Real.log (999257 / 1000000)) := by
  have h := reflection_log_13674_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13675_neg : (346517329 / 1000000000) ≤ -Real.log (500000 / 707067) ∧
    -Real.log (500000 / 707067) ≤ (34651733 / 100000000) := by
  have h := checkLog_sound (w := (207067 / 1207067)) (n := 12)
    (lo := (346517329 / 1000000000)) (hi := (34651733 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((707067 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(707067 / 500000) = 1/(500000 / 707067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13675 : Bounds (346517329 / 1000000000) (34651733 / 100000000) (Real.log (707067 / 500000)) := by
  have h := reflection_log_13675_neg
  have he : Real.log (707067 / 500000) = -Real.log (500000 / 707067) := by
    rw [show ((707067 / 500000) : ℝ) = ((500000 / 707067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13676_neg : (66833023 / 125000000) ≤ -Real.log (292933 / 500000) ∧
    -Real.log (292933 / 500000) ≤ (106932837 / 200000000) := by
  have h := checkLog_sound (w := (207067 / 792933)) (n := 12)
    (lo := (66833023 / 125000000)) (hi := (106932837 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 292933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 292933) = 1/(292933 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13676 : Bounds (-106932837 / 200000000) (-66833023 / 125000000) (Real.log (292933 / 500000)) := by
  have h := reflection_log_13676_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13677_neg : (174238163 / 500000000) ≤ -Real.log (1000000 / 1416907) ∧
    -Real.log (1000000 / 1416907) ≤ (348476327 / 1000000000) := by
  have h := checkLog_sound (w := (416907 / 2416907)) (n := 12)
    (lo := (174238163 / 500000000)) (hi := (348476327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1416907 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1416907 / 1000000) = 1/(1000000 / 1416907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13677 : Bounds (174238163 / 500000000) (348476327 / 1000000000) (Real.log (1416907 / 1000000)) := by
  have h := reflection_log_13677_neg
  have he : Real.log (1416907 / 1000000) = -Real.log (1000000 / 1416907) := by
    rw [show ((1416907 / 1000000) : ℝ) = ((1000000 / 1416907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13678_neg : (107881717 / 200000000) ≤ -Real.log (583093 / 1000000) ∧
    -Real.log (583093 / 1000000) ≤ (269704293 / 500000000) := by
  have h := checkLog_sound (w := (416907 / 1583093)) (n := 12)
    (lo := (107881717 / 200000000)) (hi := (269704293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 583093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 583093) = 1/(583093 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13678 : Bounds (-269704293 / 500000000) (-107881717 / 200000000) (Real.log (583093 / 1000000)) := by
  have h := reflection_log_13678_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13679_neg : (95466129 / 500000000) ≤ -Real.log (826188553351 / 1000000000000) ∧
    -Real.log (826188553351 / 1000000000000) ≤ (190932259 / 1000000000) := by
  have h := checkLog_sound (w := (173811446649 / 1826188553351)) (n := 12)
    (lo := (95466129 / 500000000)) (hi := (190932259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 826188553351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 826188553351) = 1/(826188553351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13679 : Bounds (-190932259 / 1000000000) (-95466129 / 500000000) (Real.log (826188553351 / 1000000000000)) := by
  have h := reflection_log_13679_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13680_neg : (94073427 / 500000000) ≤ -Real.log (207123257511 / 250000000000) ∧
    -Real.log (207123257511 / 250000000000) ≤ (37629371 / 200000000) := by
  have h := checkLog_sound (w := (42876742489 / 457123257511)) (n := 12)
    (lo := (94073427 / 500000000)) (hi := (37629371 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 207123257511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 207123257511) = 1/(207123257511 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13680 : Bounds (-37629371 / 200000000) (-94073427 / 500000000) (Real.log (207123257511 / 250000000000)) := by
  have h := reflection_log_13680_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13681_neg : (881181513 / 1000000000) ≤ -Real.log (500000000000 / 1206874950927) ∧
    -Real.log (500000000000 / 1206874950927) ≤ (176236303 / 200000000) := by
  have h := checkLog_sound (w := (206874950927 / 2206874950927)) (n := 12)
    (lo := (188034333 / 1000000000)) (hi := (94017167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1206874950927 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1206874950927 / 1000000000000) = 1/(500000000000 / 1206874950927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13681 : Bounds (881181513 / 1000000000) (176236303 / 200000000) (Real.log (1206874950927 / 500000000000)) := by
  have h := reflection_log_13681_neg
  have he : Real.log (1206874950927 / 500000000000) = -Real.log (500000000000 / 1206874950927) := by
    rw [show ((1206874950927 / 500000000000) : ℝ) = ((500000000000 / 1206874950927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13682_neg : (55492807 / 62500000) ≤ -Real.log (50000000000 / 121499229111) ∧
    -Real.log (50000000000 / 121499229111) ≤ (443942457 / 500000000) := by
  have h := checkLog_sound (w := (21499229111 / 221499229111)) (n := 12)
    (lo := (48684433 / 250000000)) (hi := (194737733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121499229111 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(121499229111 / 100000000000) = 1/(50000000000 / 121499229111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13682 : Bounds (55492807 / 62500000) (443942457 / 500000000) (Real.log (121499229111 / 50000000000)) := by
  have h := reflection_log_13682_neg
  have he : Real.log (121499229111 / 50000000000) = -Real.log (50000000000 / 121499229111) := by
    rw [show ((121499229111 / 50000000000) : ℝ) = ((50000000000 / 121499229111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13683_neg : (47523969 / 25000000) ≤ -Real.log (500000000000 / 3346153846153) ∧
    -Real.log (500000000000 / 3346153846153) ≤ (1900958763 / 1000000000) := by
  have h := checkLog_sound (w := (1346153846153 / 5346153846153)) (n := 12)
    (lo := (1286661 / 2500000)) (hi := (514664401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3346153846153 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3346153846153 / 2000000000000) = 1/(500000000000 / 3346153846153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13683 : Bounds (47523969 / 25000000) (1900958763 / 1000000000) (Real.log (3346153846153 / 500000000000)) := by
  have h := reflection_log_13683_neg
  have he : Real.log (3346153846153 / 500000000000) = -Real.log (500000000000 / 3346153846153) := by
    rw [show ((3346153846153 / 500000000000) : ℝ) = ((500000000000 / 3346153846153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13684_neg : (1914286959 / 1000000000) ≤ -Real.log (250000000000 / 1695525291829) ∧
    -Real.log (250000000000 / 1695525291829) ≤ (957143481 / 500000000) := by
  have h := checkLog_sound (w := (695525291829 / 2695525291829)) (n := 12)
    (lo := (527992599 / 1000000000)) (hi := (2639963 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1695525291829 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1695525291829 / 1000000000000) = 1/(250000000000 / 1695525291829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13684 : Bounds (1914286959 / 1000000000) (957143481 / 500000000) (Real.log (1695525291829 / 250000000000)) := by
  have h := reflection_log_13684_neg
  have he : Real.log (1695525291829 / 250000000000) = -Real.log (250000000000 / 1695525291829) := by
    rw [show ((1695525291829 / 250000000000) : ℝ) = ((250000000000 / 1695525291829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13685_neg : (557327457 / 1000000000) ≤ -Real.log (500 / 873) ∧
    -Real.log (500 / 873) ≤ (278663729 / 500000000) := by
  have h := checkLog_sound (w := (373 / 1373)) (n := 12)
    (lo := (557327457 / 1000000000)) (hi := (278663729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((873 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(873 / 500) = 1/(500 / 873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13685 : Bounds (557327457 / 1000000000) (278663729 / 500000000) (Real.log (873 / 500)) := by
  have h := reflection_log_13685_neg
  have he : Real.log (873 / 500) = -Real.log (500 / 873) := by
    rw [show ((873 / 500) : ℝ) = ((500 / 873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13686_neg : (1370421011 / 1000000000) ≤ -Real.log (127 / 500) ∧
    -Real.log (127 / 500) ≤ (1370421013 / 1000000000) := by
  have h := checkLog_sound (w := (123 / 377)) (n := 12)
    (lo := (677273831 / 1000000000)) (hi := (84659229 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 127) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 127) = 1/(127 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13686 : Bounds (-1370421013 / 1000000000) (-1370421011 / 1000000000) (Real.log (127 / 500)) := by
  have h := reflection_log_13686_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13687_neg : (745721 / 1000000000) ≤ -Real.log (500000 / 500373) ∧
    -Real.log (500000 / 500373) ≤ (372861 / 500000000) := by
  have h := checkLog_sound (w := (373 / 1000373)) (n := 12)
    (lo := (745721 / 1000000000)) (hi := (372861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500373 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500373 / 500000) = 1/(500000 / 500373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13687 : Bounds (745721 / 1000000000) (372861 / 500000000) (Real.log (500373 / 500000)) := by
  have h := reflection_log_13687_neg
  have he : Real.log (500373 / 500000) = -Real.log (500000 / 500373) := by
    rw [show ((500373 / 500000) : ℝ) = ((500000 / 500373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13688_neg : (373139 / 500000000) ≤ -Real.log (499627 / 500000) ∧
    -Real.log (499627 / 500000) ≤ (746279 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 999627)) (n := 12)
    (lo := (373139 / 500000000)) (hi := (746279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499627) = 1/(499627 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13688 : Bounds (-746279 / 1000000000) (-373139 / 500000000) (Real.log (499627 / 500000)) := by
  have h := reflection_log_13688_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13689_neg : (174012621 / 500000000) ≤ -Real.log (250000 / 354067) ∧
    -Real.log (250000 / 354067) ≤ (348025243 / 1000000000) := by
  have h := checkLog_sound (w := (104067 / 604067)) (n := 12)
    (lo := (174012621 / 500000000)) (hi := (348025243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((354067 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(354067 / 250000) = 1/(250000 / 354067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13689 : Bounds (174012621 / 500000000) (348025243 / 1000000000) (Real.log (354067 / 250000)) := by
  have h := reflection_log_13689_neg
  have he : Real.log (354067 / 250000) = -Real.log (250000 / 354067) := by
    rw [show ((354067 / 250000) : ℝ) = ((250000 / 354067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13690_neg : (107662661 / 200000000) ≤ -Real.log (145933 / 250000) ∧
    -Real.log (145933 / 250000) ≤ (269156653 / 500000000) := by
  have h := checkLog_sound (w := (104067 / 395933)) (n := 12)
    (lo := (107662661 / 200000000)) (hi := (269156653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 145933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 145933) = 1/(145933 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13690 : Bounds (-269156653 / 500000000) (-107662661 / 200000000) (Real.log (145933 / 250000)) := by
  have h := reflection_log_13690_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13691_neg : (349987633 / 1000000000) ≤ -Real.log (20000 / 28381) ∧
    -Real.log (20000 / 28381) ≤ (174993817 / 500000000) := by
  have h := checkLog_sound (w := (8381 / 48381)) (n := 12)
    (lo := (349987633 / 1000000000)) (hi := (174993817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28381 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28381 / 20000) = 1/(20000 / 28381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13691 : Bounds (349987633 / 1000000000) (174993817 / 500000000) (Real.log (28381 / 20000)) := by
  have h := reflection_log_13691_neg
  have he : Real.log (28381 / 20000) = -Real.log (20000 / 28381) := by
    rw [show ((28381 / 20000) : ℝ) = ((20000 / 28381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13692_neg : (67886323 / 125000000) ≤ -Real.log (11619 / 20000) ∧
    -Real.log (11619 / 20000) ≤ (108618117 / 200000000) := by
  have h := checkLog_sound (w := (8381 / 31619)) (n := 12)
    (lo := (67886323 / 125000000)) (hi := (108618117 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 11619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 11619) = 1/(11619 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13692 : Bounds (-108618117 / 200000000) (-67886323 / 125000000) (Real.log (11619 / 20000)) := by
  have h := reflection_log_13692_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13693_neg : (3862059 / 20000000) ≤ -Real.log (329758839 / 400000000) ∧
    -Real.log (329758839 / 400000000) ≤ (193102951 / 1000000000) := by
  have h := checkLog_sound (w := (70241161 / 729758839)) (n := 12)
    (lo := (3862059 / 20000000)) (hi := (193102951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 329758839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 329758839) = 1/(329758839 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13693 : Bounds (-193102951 / 1000000000) (-3862059 / 20000000) (Real.log (329758839 / 400000000)) := by
  have h := reflection_log_13693_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13694_neg : (95144031 / 500000000) ≤ -Real.log (51670059511 / 62500000000) ∧
    -Real.log (51670059511 / 62500000000) ≤ (190288063 / 1000000000) := by
  have h := checkLog_sound (w := (10829940489 / 114170059511)) (n := 12)
    (lo := (95144031 / 500000000)) (hi := (190288063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 51670059511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 51670059511) = 1/(51670059511 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13694 : Bounds (-190288063 / 1000000000) (-95144031 / 500000000) (Real.log (51670059511 / 62500000000)) := by
  have h := reflection_log_13694_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13695_neg : (886338547 / 1000000000) ≤ -Real.log (500000000000 / 1213114922601) ∧
    -Real.log (500000000000 / 1213114922601) ≤ (886338549 / 1000000000) := by
  have h := checkLog_sound (w := (213114922601 / 2213114922601)) (n := 12)
    (lo := (193191367 / 1000000000)) (hi := (24148921 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1213114922601 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1213114922601 / 1000000000000) = 1/(500000000000 / 1213114922601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13695 : Bounds (886338547 / 1000000000) (886338549 / 1000000000) (Real.log (1213114922601 / 500000000000)) := by
  have h := reflection_log_13695_neg
  have he : Real.log (1213114922601 / 500000000000) = -Real.log (500000000000 / 1213114922601) := by
    rw [show ((1213114922601 / 500000000000) : ℝ) = ((500000000000 / 1213114922601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


