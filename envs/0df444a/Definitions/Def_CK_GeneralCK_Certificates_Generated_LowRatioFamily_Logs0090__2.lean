-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0090__2
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0090__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T23:47:35.271028+00:00
-- url     : https://prove2.me/theorems/9492d066-d949-4c66-9113-2cb04c1b4af0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0090 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0091)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0090 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0091)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0090 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0091)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0090 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0091) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0090 (+1 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0091).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0090 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5760_neg : (9343221 / 1000000000) ≤ -Real.log (39628011631 / 40000000000) ∧
    -Real.log (39628011631 / 40000000000) ≤ (4671611 / 500000000) := by
  have h := checkLog_sound (w := (371988369 / 79628011631)) (n := 12)
    (lo := (9343221 / 1000000000)) (hi := (4671611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39628011631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39628011631) = 1/(39628011631 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5760 : Bounds (-4671611 / 500000000) (-9343221 / 1000000000) (Real.log (39628011631 / 40000000000)) := by
  have h := reflection_log_5760_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5761_neg : (9296169 / 1000000000) ≤ -Real.log (990746906751 / 1000000000000) ∧
    -Real.log (990746906751 / 1000000000000) ≤ (929617 / 100000000) := by
  have h := checkLog_sound (w := (9253093249 / 1990746906751)) (n := 12)
    (lo := (9296169 / 1000000000)) (hi := (929617 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990746906751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990746906751) = 1/(990746906751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5761 : Bounds (-929617 / 100000000) (-9296169 / 1000000000) (Real.log (990746906751 / 1000000000000)) := by
  have h := reflection_log_5761_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5762_neg : (12061419 / 62500000) ≤ -Real.log (31250000000 / 37901931773) ∧
    -Real.log (31250000000 / 37901931773) ≤ (38596541 / 200000000) := by
  have h := checkLog_sound (w := (6651931773 / 69151931773)) (n := 12)
    (lo := (12061419 / 62500000)) (hi := (38596541 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37901931773 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37901931773 / 31250000000) = 1/(31250000000 / 37901931773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5762 : Bounds (12061419 / 62500000) (38596541 / 200000000) (Real.log (37901931773 / 31250000000)) := by
  have h := reflection_log_5762_neg
  have he : Real.log (37901931773 / 31250000000) = -Real.log (31250000000 / 37901931773) := by
    rw [show ((37901931773 / 31250000000) : ℝ) = ((31250000000 / 37901931773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5763_neg : (48367809 / 250000000) ≤ -Real.log (250000000000 / 303363620769) ∧
    -Real.log (250000000000 / 303363620769) ≤ (193471237 / 1000000000) := by
  have h := checkLog_sound (w := (53363620769 / 553363620769)) (n := 12)
    (lo := (48367809 / 250000000)) (hi := (193471237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303363620769 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303363620769 / 250000000000) = 1/(250000000000 / 303363620769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5763 : Bounds (48367809 / 250000000) (193471237 / 1000000000) (Real.log (303363620769 / 250000000000)) := by
  have h := reflection_log_5763_neg
  have he : Real.log (303363620769 / 250000000000) = -Real.log (250000000000 / 303363620769) := by
    rw [show ((303363620769 / 250000000000) : ℝ) = ((250000000000 / 303363620769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5764_neg : (193686203 / 500000000) ≤ -Real.log (500000000000 / 736552491653) ∧
    -Real.log (500000000000 / 736552491653) ≤ (387372407 / 1000000000) := by
  have h := checkLog_sound (w := (236552491653 / 1236552491653)) (n := 12)
    (lo := (193686203 / 500000000)) (hi := (387372407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736552491653 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736552491653 / 500000000000) = 1/(500000000000 / 736552491653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5764 : Bounds (193686203 / 500000000) (387372407 / 1000000000) (Real.log (736552491653 / 500000000000)) := by
  have h := reflection_log_5764_neg
  have he : Real.log (736552491653 / 500000000000) = -Real.log (500000000000 / 736552491653) := by
    rw [show ((736552491653 / 500000000000) : ℝ) = ((500000000000 / 736552491653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5765_neg : (387580007 / 1000000000) ≤ -Real.log (50000000000 / 73670541677) ∧
    -Real.log (50000000000 / 73670541677) ≤ (48447501 / 125000000) := by
  have h := checkLog_sound (w := (23670541677 / 123670541677)) (n := 12)
    (lo := (387580007 / 1000000000)) (hi := (48447501 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73670541677 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73670541677 / 50000000000) = 1/(50000000000 / 73670541677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5765 : Bounds (387580007 / 1000000000) (48447501 / 125000000) (Real.log (73670541677 / 50000000000)) := by
  have h := reflection_log_5765_neg
  have he : Real.log (73670541677 / 50000000000) = -Real.log (50000000000 / 73670541677) := by
    rw [show ((73670541677 / 50000000000) : ℝ) = ((50000000000 / 73670541677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5766_neg : (175213017 / 1000000000) ≤ -Real.log (2000 / 2383) ∧
    -Real.log (2000 / 2383) ≤ (87606509 / 500000000) := by
  have h := checkLog_sound (w := (383 / 4383)) (n := 12)
    (lo := (175213017 / 1000000000)) (hi := (87606509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2383 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2383 / 2000) = 1/(2000 / 2383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5766 : Bounds (175213017 / 1000000000) (87606509 / 500000000) (Real.log (2383 / 2000)) := by
  have h := reflection_log_5766_neg
  have he : Real.log (2383 / 2000) = -Real.log (2000 / 2383) := by
    rw [show ((2383 / 2000) : ℝ) = ((2000 / 2383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5767_neg : (212574599 / 1000000000) ≤ -Real.log (1617 / 2000) ∧
    -Real.log (1617 / 2000) ≤ (1062873 / 5000000) := by
  have h := checkLog_sound (w := (383 / 3617)) (n := 12)
    (lo := (212574599 / 1000000000)) (hi := (1062873 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1617) = 1/(1617 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5767 : Bounds (-1062873 / 5000000) (-212574599 / 1000000000) (Real.log (1617 / 2000)) := by
  have h := reflection_log_5767_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5768_neg : (191481 / 1000000000) ≤ -Real.log (2000000 / 2000383) ∧
    -Real.log (2000000 / 2000383) ≤ (95741 / 500000000) := by
  have h := checkLog_sound (w := (383 / 4000383)) (n := 12)
    (lo := (191481 / 1000000000)) (hi := (95741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000383 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000383 / 2000000) = 1/(2000000 / 2000383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5768 : Bounds (191481 / 1000000000) (95741 / 500000000) (Real.log (2000383 / 2000000)) := by
  have h := reflection_log_5768_neg
  have he : Real.log (2000383 / 2000000) = -Real.log (2000000 / 2000383) := by
    rw [show ((2000383 / 2000000) : ℝ) = ((2000000 / 2000383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5769_neg : (95759 / 500000000) ≤ -Real.log (1999617 / 2000000) ∧
    -Real.log (1999617 / 2000000) ≤ (191519 / 1000000000) := by
  have h := checkLog_sound (w := (383 / 3999617)) (n := 12)
    (lo := (95759 / 500000000)) (hi := (191519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999617) = 1/(1999617 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5769 : Bounds (-191519 / 1000000000) (-95759 / 500000000) (Real.log (1999617 / 2000000)) := by
  have h := reflection_log_5769_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5770_neg : (91889791 / 1000000000) ≤ -Real.log (250000 / 274061) ∧
    -Real.log (250000 / 274061) ≤ (717889 / 7812500) := by
  have h := checkLog_sound (w := (24061 / 524061)) (n := 12)
    (lo := (91889791 / 1000000000)) (hi := (717889 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274061 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274061 / 250000) = 1/(250000 / 274061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5770 : Bounds (91889791 / 1000000000) (717889 / 7812500) (Real.log (274061 / 250000)) := by
  have h := reflection_log_5770_neg
  have he : Real.log (274061 / 250000) = -Real.log (250000 / 274061) := by
    rw [show ((274061 / 250000) : ℝ) = ((250000 / 274061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5771_neg : (50597933 / 500000000) ≤ -Real.log (225939 / 250000) ∧
    -Real.log (225939 / 250000) ≤ (101195867 / 1000000000) := by
  have h := checkLog_sound (w := (24061 / 475939)) (n := 12)
    (lo := (50597933 / 500000000)) (hi := (101195867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225939) = 1/(225939 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5771 : Bounds (-101195867 / 1000000000) (-50597933 / 500000000) (Real.log (225939 / 250000)) := by
  have h := reflection_log_5771_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5772_neg : (2302763 / 25000000) ≤ -Real.log (500000 / 548243) ∧
    -Real.log (500000 / 548243) ≤ (92110521 / 1000000000) := by
  have h := checkLog_sound (w := (48243 / 1048243)) (n := 12)
    (lo := (2302763 / 25000000)) (hi := (92110521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548243 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548243 / 500000) = 1/(500000 / 548243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5772 : Bounds (2302763 / 25000000) (92110521 / 1000000000) (Real.log (548243 / 500000)) := by
  have h := reflection_log_5772_neg
  have he : Real.log (548243 / 500000) = -Real.log (500000 / 548243) := by
    rw [show ((548243 / 500000) : ℝ) = ((500000 / 548243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5773_neg : (101463673 / 1000000000) ≤ -Real.log (451757 / 500000) ∧
    -Real.log (451757 / 500000) ≤ (50731837 / 500000000) := by
  have h := checkLog_sound (w := (48243 / 951757)) (n := 12)
    (lo := (101463673 / 1000000000)) (hi := (50731837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451757) = 1/(451757 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5773 : Bounds (-50731837 / 500000000) (-101463673 / 1000000000) (Real.log (451757 / 500000)) := by
  have h := reflection_log_5773_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5774_neg : (146143 / 15625000) ≤ -Real.log (247672612951 / 250000000000) ∧
    -Real.log (247672612951 / 250000000000) ≤ (9353153 / 1000000000) := by
  have h := checkLog_sound (w := (2327387049 / 497672612951)) (n := 12)
    (lo := (146143 / 15625000)) (hi := (9353153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247672612951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247672612951) = 1/(247672612951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5774 : Bounds (-9353153 / 1000000000) (-146143 / 15625000) (Real.log (247672612951 / 250000000000)) := by
  have h := reflection_log_5774_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5775_neg : (372243 / 40000000) ≤ -Real.log (61921068279 / 62500000000) ∧
    -Real.log (61921068279 / 62500000000) ≤ (2326519 / 250000000) := by
  have h := checkLog_sound (w := (578931721 / 124421068279)) (n := 12)
    (lo := (372243 / 40000000)) (hi := (2326519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61921068279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61921068279) = 1/(61921068279 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5775 : Bounds (-2326519 / 250000000) (-372243 / 40000000) (Real.log (61921068279 / 62500000000)) := by
  have h := reflection_log_5775_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5776_neg : (96542829 / 500000000) ≤ -Real.log (500000000000 / 606493345549) ∧
    -Real.log (500000000000 / 606493345549) ≤ (193085659 / 1000000000) := by
  have h := checkLog_sound (w := (106493345549 / 1106493345549)) (n := 12)
    (lo := (96542829 / 500000000)) (hi := (193085659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606493345549 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606493345549 / 500000000000) = 1/(500000000000 / 606493345549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5776 : Bounds (96542829 / 500000000) (193085659 / 1000000000) (Real.log (606493345549 / 500000000000)) := by
  have h := reflection_log_5776_neg
  have he : Real.log (606493345549 / 500000000000) = -Real.log (500000000000 / 606493345549) := by
    rw [show ((606493345549 / 500000000000) : ℝ) = ((500000000000 / 606493345549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5777_neg : (96787097 / 500000000) ≤ -Real.log (500000000000 / 606789712169) ∧
    -Real.log (500000000000 / 606789712169) ≤ (38714839 / 200000000) := by
  have h := checkLog_sound (w := (106789712169 / 1106789712169)) (n := 12)
    (lo := (96787097 / 500000000)) (hi := (38714839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606789712169 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606789712169 / 500000000000) = 1/(500000000000 / 606789712169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5777 : Bounds (96787097 / 500000000) (38714839 / 200000000) (Real.log (606789712169 / 500000000000)) := by
  have h := reflection_log_5777_neg
  have he : Real.log (606789712169 / 500000000000) = -Real.log (500000000000 / 606789712169) := by
    rw [show ((606789712169 / 500000000000) : ℝ) = ((500000000000 / 606789712169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5778_neg : (387580007 / 1000000000) ≤ -Real.log (500000000000 / 736705416769) ∧
    -Real.log (500000000000 / 736705416769) ≤ (48447501 / 125000000) := by
  have h := checkLog_sound (w := (236705416769 / 1236705416769)) (n := 12)
    (lo := (387580007 / 1000000000)) (hi := (48447501 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736705416769 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736705416769 / 500000000000) = 1/(500000000000 / 736705416769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5778 : Bounds (387580007 / 1000000000) (48447501 / 125000000) (Real.log (736705416769 / 500000000000)) := by
  have h := reflection_log_5778_neg
  have he : Real.log (736705416769 / 500000000000) = -Real.log (500000000000 / 736705416769) := by
    rw [show ((736705416769 / 500000000000) : ℝ) = ((500000000000 / 736705416769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5779_neg : (387787617 / 1000000000) ≤ -Real.log (125000000000 / 184214594929) ∧
    -Real.log (125000000000 / 184214594929) ≤ (193893809 / 500000000) := by
  have h := checkLog_sound (w := (59214594929 / 309214594929)) (n := 12)
    (lo := (387787617 / 1000000000)) (hi := (193893809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184214594929 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184214594929 / 125000000000) = 1/(125000000000 / 184214594929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5779 : Bounds (387787617 / 1000000000) (193893809 / 500000000) (Real.log (184214594929 / 125000000000)) := by
  have h := reflection_log_5779_neg
  have he : Real.log (184214594929 / 125000000000) = -Real.log (125000000000 / 184214594929) := by
    rw [show ((184214594929 / 125000000000) : ℝ) = ((125000000000 / 184214594929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5780_neg : (175296941 / 1000000000) ≤ -Real.log (2500 / 2979) ∧
    -Real.log (2500 / 2979) ≤ (87648471 / 500000000) := by
  have h := checkLog_sound (w := (479 / 5479)) (n := 12)
    (lo := (175296941 / 1000000000)) (hi := (87648471 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2979 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2979 / 2500) = 1/(2500 / 2979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5780 : Bounds (175296941 / 1000000000) (87648471 / 500000000) (Real.log (2979 / 2500)) := by
  have h := reflection_log_5780_neg
  have he : Real.log (2979 / 2500) = -Real.log (2500 / 2979) := by
    rw [show ((2979 / 2500) : ℝ) = ((2500 / 2979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5781_neg : (212698293 / 1000000000) ≤ -Real.log (2021 / 2500) ∧
    -Real.log (2021 / 2500) ≤ (106349147 / 500000000) := by
  have h := checkLog_sound (w := (479 / 4521)) (n := 12)
    (lo := (212698293 / 1000000000)) (hi := (106349147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2021) = 1/(2021 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5781 : Bounds (-106349147 / 500000000) (-212698293 / 1000000000) (Real.log (2021 / 2500)) := by
  have h := reflection_log_5781_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5782_neg : (191581 / 1000000000) ≤ -Real.log (2500000 / 2500479) ∧
    -Real.log (2500000 / 2500479) ≤ (95791 / 500000000) := by
  have h := checkLog_sound (w := (479 / 5000479)) (n := 12)
    (lo := (191581 / 1000000000)) (hi := (95791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500479 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500479 / 2500000) = 1/(2500000 / 2500479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5782 : Bounds (191581 / 1000000000) (95791 / 500000000) (Real.log (2500479 / 2500000)) := by
  have h := reflection_log_5782_neg
  have he : Real.log (2500479 / 2500000) = -Real.log (2500000 / 2500479) := by
    rw [show ((2500479 / 2500000) : ℝ) = ((2500000 / 2500479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5783_neg : (95809 / 500000000) ≤ -Real.log (2499521 / 2500000) ∧
    -Real.log (2499521 / 2500000) ≤ (191619 / 1000000000) := by
  have h := checkLog_sound (w := (479 / 4999521)) (n := 12)
    (lo := (95809 / 500000000)) (hi := (191619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499521) = 1/(2499521 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5783 : Bounds (-191619 / 1000000000) (-95809 / 500000000) (Real.log (2499521 / 2500000)) := by
  have h := reflection_log_5783_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5784_neg : (11492039 / 125000000) ≤ -Real.log (200000 / 219259) ∧
    -Real.log (200000 / 219259) ≤ (91936313 / 1000000000) := by
  have h := checkLog_sound (w := (19259 / 419259)) (n := 12)
    (lo := (11492039 / 125000000)) (hi := (91936313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219259 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219259 / 200000) = 1/(200000 / 219259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5784 : Bounds (11492039 / 125000000) (91936313 / 1000000000) (Real.log (219259 / 200000)) := by
  have h := reflection_log_5784_neg
  have he : Real.log (219259 / 200000) = -Real.log (200000 / 219259) := by
    rw [show ((219259 / 200000) : ℝ) = ((200000 / 219259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5785_neg : (101252299 / 1000000000) ≤ -Real.log (180741 / 200000) ∧
    -Real.log (180741 / 200000) ≤ (1012523 / 10000000) := by
  have h := checkLog_sound (w := (19259 / 380741)) (n := 12)
    (lo := (101252299 / 1000000000)) (hi := (1012523 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180741) = 1/(180741 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5785 : Bounds (-1012523 / 10000000) (-101252299 / 1000000000) (Real.log (180741 / 200000)) := by
  have h := reflection_log_5785_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5786_neg : (11519629 / 125000000) ≤ -Real.log (1000000 / 1096537) ∧
    -Real.log (1000000 / 1096537) ≤ (92157033 / 1000000000) := by
  have h := checkLog_sound (w := (96537 / 2096537)) (n := 12)
    (lo := (11519629 / 125000000)) (hi := (92157033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096537 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096537 / 1000000) = 1/(1000000 / 1096537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5786 : Bounds (11519629 / 125000000) (92157033 / 1000000000) (Real.log (1096537 / 1000000)) := by
  have h := reflection_log_5786_neg
  have he : Real.log (1096537 / 1000000) = -Real.log (1000000 / 1096537) := by
    rw [show ((1096537 / 1000000) : ℝ) = ((1000000 / 1096537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5787_neg : (101520121 / 1000000000) ≤ -Real.log (903463 / 1000000) ∧
    -Real.log (903463 / 1000000) ≤ (50760061 / 500000000) := by
  have h := checkLog_sound (w := (96537 / 1903463)) (n := 12)
    (lo := (101520121 / 1000000000)) (hi := (50760061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903463) = 1/(903463 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5787 : Bounds (-50760061 / 500000000) (-101520121 / 1000000000) (Real.log (903463 / 1000000)) := by
  have h := reflection_log_5787_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5788_neg : (9363089 / 1000000000) ≤ -Real.log (990680607631 / 1000000000000) ∧
    -Real.log (990680607631 / 1000000000000) ≤ (936309 / 100000000) := by
  have h := checkLog_sound (w := (9319392369 / 1990680607631)) (n := 12)
    (lo := (9363089 / 1000000000)) (hi := (936309 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990680607631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990680607631) = 1/(990680607631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5788 : Bounds (-936309 / 100000000) (-9363089 / 1000000000) (Real.log (990680607631 / 1000000000000)) := by
  have h := reflection_log_5788_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5789_neg : (4657993 / 500000000) ≤ -Real.log (39629090919 / 40000000000) ∧
    -Real.log (39629090919 / 40000000000) ≤ (9315987 / 1000000000) := by
  have h := checkLog_sound (w := (370909081 / 79629090919)) (n := 12)
    (lo := (4657993 / 500000000)) (hi := (9315987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39629090919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39629090919) = 1/(39629090919 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5789 : Bounds (-9315987 / 1000000000) (-4657993 / 500000000) (Real.log (39629090919 / 40000000000)) := by
  have h := reflection_log_5789_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5790_neg : (48297153 / 250000000) ≤ -Real.log (31250000000 / 37909736861) ∧
    -Real.log (31250000000 / 37909736861) ≤ (193188613 / 1000000000) := by
  have h := checkLog_sound (w := (6659736861 / 69159736861)) (n := 12)
    (lo := (48297153 / 250000000)) (hi := (193188613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37909736861 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37909736861 / 31250000000) = 1/(31250000000 / 37909736861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5790 : Bounds (48297153 / 250000000) (193188613 / 1000000000) (Real.log (37909736861 / 31250000000)) := by
  have h := reflection_log_5790_neg
  have he : Real.log (37909736861 / 31250000000) = -Real.log (31250000000 / 37909736861) := by
    rw [show ((37909736861 / 31250000000) : ℝ) = ((31250000000 / 37909736861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5791_neg : (193677153 / 1000000000) ≤ -Real.log (125000000000 / 151713047463) ∧
    -Real.log (125000000000 / 151713047463) ≤ (96838577 / 500000000) := by
  have h := checkLog_sound (w := (26713047463 / 276713047463)) (n := 12)
    (lo := (193677153 / 1000000000)) (hi := (96838577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151713047463 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151713047463 / 125000000000) = 1/(125000000000 / 151713047463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5791 : Bounds (193677153 / 1000000000) (96838577 / 500000000) (Real.log (151713047463 / 125000000000)) := by
  have h := reflection_log_5791_neg
  have he : Real.log (151713047463 / 125000000000) = -Real.log (125000000000 / 151713047463) := by
    rw [show ((151713047463 / 125000000000) : ℝ) = ((125000000000 / 151713047463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5792_neg : (387787617 / 1000000000) ≤ -Real.log (100000000000 / 147371675943) ∧
    -Real.log (100000000000 / 147371675943) ≤ (193893809 / 500000000) := by
  have h := checkLog_sound (w := (47371675943 / 247371675943)) (n := 12)
    (lo := (387787617 / 1000000000)) (hi := (193893809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147371675943 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147371675943 / 100000000000) = 1/(100000000000 / 147371675943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5792 : Bounds (387787617 / 1000000000) (193893809 / 500000000) (Real.log (147371675943 / 100000000000)) := by
  have h := reflection_log_5792_neg
  have he : Real.log (147371675943 / 100000000000) = -Real.log (100000000000 / 147371675943) := by
    rw [show ((147371675943 / 100000000000) : ℝ) = ((100000000000 / 147371675943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5793_neg : (77599047 / 200000000) ≤ -Real.log (100000000000 / 147402276101) ∧
    -Real.log (100000000000 / 147402276101) ≤ (96998809 / 250000000) := by
  have h := checkLog_sound (w := (47402276101 / 247402276101)) (n := 12)
    (lo := (77599047 / 200000000)) (hi := (96998809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147402276101 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147402276101 / 100000000000) = 1/(100000000000 / 147402276101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5793 : Bounds (77599047 / 200000000) (96998809 / 250000000) (Real.log (147402276101 / 100000000000)) := by
  have h := reflection_log_5793_neg
  have he : Real.log (147402276101 / 100000000000) = -Real.log (100000000000 / 147402276101) := by
    rw [show ((147402276101 / 100000000000) : ℝ) = ((100000000000 / 147402276101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5794_neg : (175380859 / 1000000000) ≤ -Real.log (10000 / 11917) ∧
    -Real.log (10000 / 11917) ≤ (8769043 / 50000000) := by
  have h := checkLog_sound (w := (1917 / 21917)) (n := 12)
    (lo := (175380859 / 1000000000)) (hi := (8769043 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11917 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11917 / 10000) = 1/(10000 / 11917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5794 : Bounds (175380859 / 1000000000) (8769043 / 50000000) (Real.log (11917 / 10000)) := by
  have h := reflection_log_5794_neg
  have he : Real.log (11917 / 10000) = -Real.log (10000 / 11917) := by
    rw [show ((11917 / 10000) : ℝ) = ((10000 / 11917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5795_neg : (106411001 / 500000000) ≤ -Real.log (8083 / 10000) ∧
    -Real.log (8083 / 10000) ≤ (212822003 / 1000000000) := by
  have h := checkLog_sound (w := (1917 / 18083)) (n := 12)
    (lo := (106411001 / 500000000)) (hi := (212822003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8083) = 1/(8083 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5795 : Bounds (-212822003 / 1000000000) (-106411001 / 500000000) (Real.log (8083 / 10000)) := by
  have h := reflection_log_5795_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5796_neg : (191681 / 1000000000) ≤ -Real.log (10000000 / 10001917) ∧
    -Real.log (10000000 / 10001917) ≤ (95841 / 500000000) := by
  have h := checkLog_sound (w := (1917 / 20001917)) (n := 12)
    (lo := (191681 / 1000000000)) (hi := (95841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001917 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001917 / 10000000) = 1/(10000000 / 10001917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5796 : Bounds (191681 / 1000000000) (95841 / 500000000) (Real.log (10001917 / 10000000)) := by
  have h := reflection_log_5796_neg
  have he : Real.log (10001917 / 10000000) = -Real.log (10000000 / 10001917) := by
    rw [show ((10001917 / 10000000) : ℝ) = ((10000000 / 10001917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5797_neg : (95859 / 500000000) ≤ -Real.log (9998083 / 10000000) ∧
    -Real.log (9998083 / 10000000) ≤ (191719 / 1000000000) := by
  have h := checkLog_sound (w := (1917 / 19998083)) (n := 12)
    (lo := (95859 / 500000000)) (hi := (191719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998083) = 1/(9998083 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5797 : Bounds (-191719 / 1000000000) (-95859 / 500000000) (Real.log (9998083 / 10000000)) := by
  have h := reflection_log_5797_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5798_neg : (574887 / 6250000) ≤ -Real.log (200000 / 219269) ∧
    -Real.log (200000 / 219269) ≤ (91981921 / 1000000000) := by
  have h := checkLog_sound (w := (19269 / 419269)) (n := 12)
    (lo := (574887 / 6250000)) (hi := (91981921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219269 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219269 / 200000) = 1/(200000 / 219269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5798 : Bounds (574887 / 6250000) (91981921 / 1000000000) (Real.log (219269 / 200000)) := by
  have h := reflection_log_5798_neg
  have he : Real.log (219269 / 200000) = -Real.log (200000 / 219269) := by
    rw [show ((219269 / 200000) : ℝ) = ((200000 / 219269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5799_neg : (25326907 / 250000000) ≤ -Real.log (180731 / 200000) ∧
    -Real.log (180731 / 200000) ≤ (101307629 / 1000000000) := by
  have h := checkLog_sound (w := (19269 / 380731)) (n := 12)
    (lo := (25326907 / 250000000)) (hi := (101307629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180731) = 1/(180731 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5799 : Bounds (-101307629 / 1000000000) (-25326907 / 250000000) (Real.log (180731 / 200000)) := by
  have h := reflection_log_5799_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5800_neg : (92203541 / 1000000000) ≤ -Real.log (250000 / 274147) ∧
    -Real.log (250000 / 274147) ≤ (46101771 / 500000000) := by
  have h := checkLog_sound (w := (24147 / 524147)) (n := 12)
    (lo := (92203541 / 1000000000)) (hi := (46101771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274147 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274147 / 250000) = 1/(250000 / 274147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5800 : Bounds (92203541 / 1000000000) (46101771 / 500000000) (Real.log (274147 / 250000)) := by
  have h := reflection_log_5800_neg
  have he : Real.log (274147 / 250000) = -Real.log (250000 / 274147) := by
    rw [show ((274147 / 250000) : ℝ) = ((250000 / 274147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5801_neg : (25394143 / 250000000) ≤ -Real.log (225853 / 250000) ∧
    -Real.log (225853 / 250000) ≤ (101576573 / 1000000000) := by
  have h := checkLog_sound (w := (24147 / 475853)) (n := 12)
    (lo := (25394143 / 250000000)) (hi := (101576573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225853) = 1/(225853 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5801 : Bounds (-101576573 / 1000000000) (-25394143 / 250000000) (Real.log (225853 / 250000)) := by
  have h := reflection_log_5801_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5802_neg : (9373031 / 1000000000) ≤ -Real.log (61916922391 / 62500000000) ∧
    -Real.log (61916922391 / 62500000000) ≤ (1171629 / 125000000) := by
  have h := checkLog_sound (w := (583077609 / 124416922391)) (n := 12)
    (lo := (9373031 / 1000000000)) (hi := (1171629 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61916922391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61916922391) = 1/(61916922391 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5802 : Bounds (-1171629 / 125000000) (-9373031 / 1000000000) (Real.log (61916922391 / 62500000000)) := by
  have h := reflection_log_5802_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5803_neg : (2331427 / 250000000) ≤ -Real.log (39628705639 / 40000000000) ∧
    -Real.log (39628705639 / 40000000000) ≤ (9325709 / 1000000000) := by
  have h := checkLog_sound (w := (371294361 / 79628705639)) (n := 12)
    (lo := (2331427 / 250000000)) (hi := (9325709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39628705639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39628705639) = 1/(39628705639 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5803 : Bounds (-9325709 / 1000000000) (-2331427 / 250000000) (Real.log (39628705639 / 40000000000)) := by
  have h := reflection_log_5803_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5804_neg : (48322387 / 250000000) ≤ -Real.log (500000000000 / 606617016449) ∧
    -Real.log (500000000000 / 606617016449) ≤ (193289549 / 1000000000) := by
  have h := checkLog_sound (w := (106617016449 / 1106617016449)) (n := 12)
    (lo := (48322387 / 250000000)) (hi := (193289549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606617016449 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606617016449 / 500000000000) = 1/(500000000000 / 606617016449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5804 : Bounds (48322387 / 250000000) (193289549 / 1000000000) (Real.log (606617016449 / 500000000000)) := by
  have h := reflection_log_5804_neg
  have he : Real.log (606617016449 / 500000000000) = -Real.log (500000000000 / 606617016449) := by
    rw [show ((606617016449 / 500000000000) : ℝ) = ((500000000000 / 606617016449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5805_neg : (193780113 / 1000000000) ≤ -Real.log (50000000000 / 60691467459) ∧
    -Real.log (50000000000 / 60691467459) ≤ (96890057 / 500000000) := by
  have h := checkLog_sound (w := (10691467459 / 110691467459)) (n := 12)
    (lo := (193780113 / 1000000000)) (hi := (96890057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60691467459 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60691467459 / 50000000000) = 1/(50000000000 / 60691467459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5805 : Bounds (193780113 / 1000000000) (96890057 / 500000000) (Real.log (60691467459 / 50000000000)) := by
  have h := reflection_log_5805_neg
  have he : Real.log (60691467459 / 50000000000) = -Real.log (50000000000 / 60691467459) := by
    rw [show ((60691467459 / 50000000000) : ℝ) = ((50000000000 / 60691467459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5806_neg : (77599047 / 200000000) ≤ -Real.log (62500000000 / 92126422563) ∧
    -Real.log (62500000000 / 92126422563) ≤ (96998809 / 250000000) := by
  have h := checkLog_sound (w := (29626422563 / 154626422563)) (n := 12)
    (lo := (77599047 / 200000000)) (hi := (96998809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92126422563 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92126422563 / 62500000000) = 1/(62500000000 / 92126422563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5806 : Bounds (77599047 / 200000000) (96998809 / 250000000) (Real.log (92126422563 / 62500000000)) := by
  have h := reflection_log_5806_neg
  have he : Real.log (92126422563 / 62500000000) = -Real.log (62500000000 / 92126422563) := by
    rw [show ((92126422563 / 62500000000) : ℝ) = ((62500000000 / 92126422563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5807_neg : (388202861 / 1000000000) ≤ -Real.log (31250000000 / 46072776197) ∧
    -Real.log (31250000000 / 46072776197) ≤ (194101431 / 500000000) := by
  have h := checkLog_sound (w := (14822776197 / 77322776197)) (n := 12)
    (lo := (388202861 / 1000000000)) (hi := (194101431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46072776197 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46072776197 / 31250000000) = 1/(31250000000 / 46072776197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5807 : Bounds (388202861 / 1000000000) (194101431 / 500000000) (Real.log (46072776197 / 31250000000)) := by
  have h := reflection_log_5807_neg
  have he : Real.log (46072776197 / 31250000000) = -Real.log (31250000000 / 46072776197) := by
    rw [show ((46072776197 / 31250000000) : ℝ) = ((31250000000 / 46072776197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5808_neg : (175464769 / 1000000000) ≤ -Real.log (5000 / 5959) ∧
    -Real.log (5000 / 5959) ≤ (17546477 / 100000000) := by
  have h := checkLog_sound (w := (959 / 10959)) (n := 12)
    (lo := (175464769 / 1000000000)) (hi := (17546477 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5959 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5959 / 5000) = 1/(5000 / 5959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5808 : Bounds (175464769 / 1000000000) (17546477 / 100000000) (Real.log (5959 / 5000)) := by
  have h := reflection_log_5808_neg
  have he : Real.log (5959 / 5000) = -Real.log (5000 / 5959) := by
    rw [show ((5959 / 5000) : ℝ) = ((5000 / 5959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5809_neg : (106472863 / 500000000) ≤ -Real.log (4041 / 5000) ∧
    -Real.log (4041 / 5000) ≤ (212945727 / 1000000000) := by
  have h := checkLog_sound (w := (959 / 9041)) (n := 12)
    (lo := (106472863 / 500000000)) (hi := (212945727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4041) = 1/(4041 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5809 : Bounds (-212945727 / 1000000000) (-106472863 / 500000000) (Real.log (4041 / 5000)) := by
  have h := reflection_log_5809_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5810_neg : (191781 / 1000000000) ≤ -Real.log (5000000 / 5000959) ∧
    -Real.log (5000000 / 5000959) ≤ (95891 / 500000000) := by
  have h := checkLog_sound (w := (959 / 10000959)) (n := 12)
    (lo := (191781 / 1000000000)) (hi := (95891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000959 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000959 / 5000000) = 1/(5000000 / 5000959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5810 : Bounds (191781 / 1000000000) (95891 / 500000000) (Real.log (5000959 / 5000000)) := by
  have h := reflection_log_5810_neg
  have he : Real.log (5000959 / 5000000) = -Real.log (5000000 / 5000959) := by
    rw [show ((5000959 / 5000000) : ℝ) = ((5000000 / 5000959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5811_neg : (95909 / 500000000) ≤ -Real.log (4999041 / 5000000) ∧
    -Real.log (4999041 / 5000000) ≤ (191819 / 1000000000) := by
  have h := checkLog_sound (w := (959 / 9999041)) (n := 12)
    (lo := (95909 / 500000000)) (hi := (191819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999041) = 1/(4999041 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5811 : Bounds (-191819 / 1000000000) (-95909 / 500000000) (Real.log (4999041 / 5000000)) := by
  have h := reflection_log_5811_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5812_neg : (92028437 / 1000000000) ≤ -Real.log (250000 / 274099) ∧
    -Real.log (250000 / 274099) ≤ (46014219 / 500000000) := by
  have h := checkLog_sound (w := (24099 / 524099)) (n := 12)
    (lo := (92028437 / 1000000000)) (hi := (46014219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274099 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274099 / 250000) = 1/(250000 / 274099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5812 : Bounds (92028437 / 1000000000) (46014219 / 500000000) (Real.log (274099 / 250000)) := by
  have h := reflection_log_5812_neg
  have he : Real.log (274099 / 250000) = -Real.log (250000 / 274099) := by
    rw [show ((274099 / 250000) : ℝ) = ((250000 / 274099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5813_neg : (101364067 / 1000000000) ≤ -Real.log (225901 / 250000) ∧
    -Real.log (225901 / 250000) ≤ (25341017 / 250000000) := by
  have h := checkLog_sound (w := (24099 / 475901)) (n := 12)
    (lo := (101364067 / 1000000000)) (hi := (25341017 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225901) = 1/(225901 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5813 : Bounds (-25341017 / 250000000) (-101364067 / 1000000000) (Real.log (225901 / 250000)) := by
  have h := reflection_log_5813_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5814_neg : (92250047 / 1000000000) ≤ -Real.log (1000000 / 1096639) ∧
    -Real.log (1000000 / 1096639) ≤ (1441407 / 15625000) := by
  have h := checkLog_sound (w := (96639 / 2096639)) (n := 12)
    (lo := (92250047 / 1000000000)) (hi := (1441407 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096639 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096639 / 1000000) = 1/(1000000 / 1096639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5814 : Bounds (92250047 / 1000000000) (1441407 / 15625000) (Real.log (1096639 / 1000000)) := by
  have h := reflection_log_5814_neg
  have he : Real.log (1096639 / 1000000) = -Real.log (1000000 / 1096639) := by
    rw [show ((1096639 / 1000000) : ℝ) = ((1000000 / 1096639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5815_neg : (50816513 / 500000000) ≤ -Real.log (903361 / 1000000) ∧
    -Real.log (903361 / 1000000) ≤ (101633027 / 1000000000) := by
  have h := checkLog_sound (w := (96639 / 1903361)) (n := 12)
    (lo := (50816513 / 500000000)) (hi := (101633027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903361) = 1/(903361 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5815 : Bounds (-101633027 / 1000000000) (-50816513 / 500000000) (Real.log (903361 / 1000000)) := by
  have h := reflection_log_5815_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5816_neg : (9382979 / 1000000000) ≤ -Real.log (990660903679 / 1000000000000) ∧
    -Real.log (990660903679 / 1000000000000) ≤ (469149 / 50000000) := by
  have h := checkLog_sound (w := (9339096321 / 1990660903679)) (n := 12)
    (lo := (9382979 / 1000000000)) (hi := (469149 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990660903679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990660903679) = 1/(990660903679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5816 : Bounds (-469149 / 50000000) (-9382979 / 1000000000) (Real.log (990660903679 / 1000000000000)) := by
  have h := reflection_log_5816_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5817_neg : (933563 / 100000000) ≤ -Real.log (61919238199 / 62500000000) ∧
    -Real.log (61919238199 / 62500000000) ≤ (9335631 / 1000000000) := by
  have h := checkLog_sound (w := (580761801 / 124419238199)) (n := 12)
    (lo := (933563 / 100000000)) (hi := (9335631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61919238199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61919238199) = 1/(61919238199 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5817 : Bounds (-9335631 / 1000000000) (-933563 / 100000000) (Real.log (61919238199 / 62500000000)) := by
  have h := reflection_log_5817_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5818_neg : (24174063 / 125000000) ≤ -Real.log (500000000000 / 606679474637) ∧
    -Real.log (500000000000 / 606679474637) ≤ (38678501 / 200000000) := by
  have h := checkLog_sound (w := (106679474637 / 1106679474637)) (n := 12)
    (lo := (24174063 / 125000000)) (hi := (38678501 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606679474637 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606679474637 / 500000000000) = 1/(500000000000 / 606679474637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5818 : Bounds (24174063 / 125000000) (38678501 / 200000000) (Real.log (606679474637 / 500000000000)) := by
  have h := reflection_log_5818_neg
  have he : Real.log (606679474637 / 500000000000) = -Real.log (500000000000 / 606679474637) := by
    rw [show ((606679474637 / 500000000000) : ℝ) = ((500000000000 / 606679474637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5819_neg : (96941537 / 500000000) ≤ -Real.log (250000000000 / 303488583191) ∧
    -Real.log (250000000000 / 303488583191) ≤ (7755323 / 40000000) := by
  have h := checkLog_sound (w := (53488583191 / 553488583191)) (n := 12)
    (lo := (96941537 / 500000000)) (hi := (7755323 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303488583191 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303488583191 / 250000000000) = 1/(250000000000 / 303488583191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5819 : Bounds (96941537 / 500000000) (7755323 / 40000000) (Real.log (303488583191 / 250000000000)) := by
  have h := reflection_log_5819_neg
  have he : Real.log (303488583191 / 250000000000) = -Real.log (250000000000 / 303488583191) := by
    rw [show ((303488583191 / 250000000000) : ℝ) = ((250000000000 / 303488583191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5820_neg : (388202861 / 1000000000) ≤ -Real.log (500000000000 / 737164419151) ∧
    -Real.log (500000000000 / 737164419151) ≤ (194101431 / 500000000) := by
  have h := checkLog_sound (w := (237164419151 / 1237164419151)) (n := 12)
    (lo := (388202861 / 1000000000)) (hi := (194101431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737164419151 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(737164419151 / 500000000000) = 1/(500000000000 / 737164419151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5820 : Bounds (388202861 / 1000000000) (194101431 / 500000000) (Real.log (737164419151 / 500000000000)) := by
  have h := reflection_log_5820_neg
  have he : Real.log (737164419151 / 500000000000) = -Real.log (500000000000 / 737164419151) := by
    rw [show ((737164419151 / 500000000000) : ℝ) = ((500000000000 / 737164419151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5821_neg : (77682099 / 200000000) ≤ -Real.log (50000000000 / 73731749567) ∧
    -Real.log (50000000000 / 73731749567) ≤ (3034457 / 7812500) := by
  have h := checkLog_sound (w := (23731749567 / 123731749567)) (n := 12)
    (lo := (77682099 / 200000000)) (hi := (3034457 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73731749567 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73731749567 / 50000000000) = 1/(50000000000 / 73731749567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5821 : Bounds (77682099 / 200000000) (3034457 / 7812500) (Real.log (73731749567 / 50000000000)) := by
  have h := reflection_log_5821_neg
  have he : Real.log (73731749567 / 50000000000) = -Real.log (50000000000 / 73731749567) := by
    rw [show ((73731749567 / 50000000000) : ℝ) = ((50000000000 / 73731749567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5822_neg : (685737 / 3906250) ≤ -Real.log (10000 / 11919) ∧
    -Real.log (10000 / 11919) ≤ (175548673 / 1000000000) := by
  have h := checkLog_sound (w := (1919 / 21919)) (n := 12)
    (lo := (685737 / 3906250)) (hi := (175548673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11919 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11919 / 10000) = 1/(10000 / 11919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5822 : Bounds (685737 / 3906250) (175548673 / 1000000000) (Real.log (11919 / 10000)) := by
  have h := reflection_log_5822_neg
  have he : Real.log (11919 / 10000) = -Real.log (10000 / 11919) := by
    rw [show ((11919 / 10000) : ℝ) = ((10000 / 11919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5823_neg : (42613893 / 200000000) ≤ -Real.log (8081 / 10000) ∧
    -Real.log (8081 / 10000) ≤ (106534733 / 500000000) := by
  have h := checkLog_sound (w := (1919 / 18081)) (n := 12)
    (lo := (42613893 / 200000000)) (hi := (106534733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8081) = 1/(8081 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5823 : Bounds (-106534733 / 500000000) (-42613893 / 200000000) (Real.log (8081 / 10000)) := by
  have h := reflection_log_5823_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0091 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5824_neg : (191881 / 1000000000) ≤ -Real.log (10000000 / 10001919) ∧
    -Real.log (10000000 / 10001919) ≤ (95941 / 500000000) := by
  have h := checkLog_sound (w := (1919 / 20001919)) (n := 12)
    (lo := (191881 / 1000000000)) (hi := (95941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001919 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001919 / 10000000) = 1/(10000000 / 10001919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5824 : Bounds (191881 / 1000000000) (95941 / 500000000) (Real.log (10001919 / 10000000)) := by
  have h := reflection_log_5824_neg
  have he : Real.log (10001919 / 10000000) = -Real.log (10000000 / 10001919) := by
    rw [show ((10001919 / 10000000) : ℝ) = ((10000000 / 10001919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5825_neg : (95959 / 500000000) ≤ -Real.log (9998081 / 10000000) ∧
    -Real.log (9998081 / 10000000) ≤ (191919 / 1000000000) := by
  have h := checkLog_sound (w := (1919 / 19998081)) (n := 12)
    (lo := (95959 / 500000000)) (hi := (191919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998081) = 1/(9998081 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5825 : Bounds (-191919 / 1000000000) (-95959 / 500000000) (Real.log (9998081 / 10000000)) := by
  have h := reflection_log_5825_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5826_neg : (11509369 / 125000000) ≤ -Real.log (1000000 / 1096447) ∧
    -Real.log (1000000 / 1096447) ≤ (92074953 / 1000000000) := by
  have h := checkLog_sound (w := (96447 / 2096447)) (n := 12)
    (lo := (11509369 / 125000000)) (hi := (92074953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096447 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096447 / 1000000) = 1/(1000000 / 1096447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5826 : Bounds (11509369 / 125000000) (92074953 / 1000000000) (Real.log (1096447 / 1000000)) := by
  have h := reflection_log_5826_neg
  have he : Real.log (1096447 / 1000000) = -Real.log (1000000 / 1096447) := by
    rw [show ((1096447 / 1000000) : ℝ) = ((1000000 / 1096447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5827_neg : (101420509 / 1000000000) ≤ -Real.log (903553 / 1000000) ∧
    -Real.log (903553 / 1000000) ≤ (10142051 / 100000000) := by
  have h := checkLog_sound (w := (96447 / 1903553)) (n := 12)
    (lo := (101420509 / 1000000000)) (hi := (10142051 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903553) = 1/(903553 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5827 : Bounds (-10142051 / 100000000) (-101420509 / 1000000000) (Real.log (903553 / 1000000)) := by
  have h := reflection_log_5827_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5828_neg : (11537069 / 125000000) ≤ -Real.log (100000 / 109669) ∧
    -Real.log (100000 / 109669) ≤ (92296553 / 1000000000) := by
  have h := checkLog_sound (w := (9669 / 209669)) (n := 12)
    (lo := (11537069 / 125000000)) (hi := (92296553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109669 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109669 / 100000) = 1/(100000 / 109669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5828 : Bounds (11537069 / 125000000) (92296553 / 1000000000) (Real.log (109669 / 100000)) := by
  have h := reflection_log_5828_neg
  have he : Real.log (109669 / 100000) = -Real.log (100000 / 109669) := by
    rw [show ((109669 / 100000) : ℝ) = ((100000 / 109669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5829_neg : (25422371 / 250000000) ≤ -Real.log (90331 / 100000) ∧
    -Real.log (90331 / 100000) ≤ (20337897 / 200000000) := by
  have h := checkLog_sound (w := (9669 / 190331)) (n := 12)
    (lo := (25422371 / 250000000)) (hi := (20337897 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90331) = 1/(90331 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5829 : Bounds (-20337897 / 200000000) (-25422371 / 250000000) (Real.log (90331 / 100000)) := by
  have h := reflection_log_5829_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5830_neg : (9392931 / 1000000000) ≤ -Real.log (9906510439 / 10000000000) ∧
    -Real.log (9906510439 / 10000000000) ≤ (2348233 / 250000000) := by
  have h := checkLog_sound (w := (93489561 / 19906510439)) (n := 12)
    (lo := (9392931 / 1000000000)) (hi := (2348233 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9906510439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9906510439) = 1/(9906510439 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5830 : Bounds (-2348233 / 250000000) (-9392931 / 1000000000) (Real.log (9906510439 / 10000000000)) := by
  have h := reflection_log_5830_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5831_neg : (9345557 / 1000000000) ≤ -Real.log (990697976191 / 1000000000000) ∧
    -Real.log (990697976191 / 1000000000000) ≤ (4672779 / 500000000) := by
  have h := checkLog_sound (w := (9302023809 / 1990697976191)) (n := 12)
    (lo := (9345557 / 1000000000)) (hi := (4672779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990697976191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990697976191) = 1/(990697976191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5831 : Bounds (-4672779 / 500000000) (-9345557 / 1000000000) (Real.log (990697976191 / 1000000000000)) := by
  have h := reflection_log_5831_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5832_neg : (96747731 / 500000000) ≤ -Real.log (4000000000 / 4853935519) ∧
    -Real.log (4000000000 / 4853935519) ≤ (193495463 / 1000000000) := by
  have h := checkLog_sound (w := (853935519 / 8853935519)) (n := 12)
    (lo := (96747731 / 500000000)) (hi := (193495463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4853935519 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4853935519 / 4000000000) = 1/(4000000000 / 4853935519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5832 : Bounds (96747731 / 500000000) (193495463 / 1000000000) (Real.log (4853935519 / 4000000000)) := by
  have h := reflection_log_5832_neg
  have he : Real.log (4853935519 / 4000000000) = -Real.log (4000000000 / 4853935519) := by
    rw [show ((4853935519 / 4000000000) : ℝ) = ((4000000000 / 4853935519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5833_neg : (48496509 / 250000000) ≤ -Real.log (31250000000 / 37939979077) ∧
    -Real.log (31250000000 / 37939979077) ≤ (193986037 / 1000000000) := by
  have h := checkLog_sound (w := (6689979077 / 69189979077)) (n := 12)
    (lo := (48496509 / 250000000)) (hi := (193986037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37939979077 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37939979077 / 31250000000) = 1/(31250000000 / 37939979077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5833 : Bounds (48496509 / 250000000) (193986037 / 1000000000) (Real.log (37939979077 / 31250000000)) := by
  have h := reflection_log_5833_neg
  have he : Real.log (37939979077 / 31250000000) = -Real.log (31250000000 / 37939979077) := by
    rw [show ((37939979077 / 31250000000) : ℝ) = ((31250000000 / 37939979077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5834_neg : (77682099 / 200000000) ≤ -Real.log (500000000000 / 737317495669) ∧
    -Real.log (500000000000 / 737317495669) ≤ (3034457 / 7812500) := by
  have h := checkLog_sound (w := (237317495669 / 1237317495669)) (n := 12)
    (lo := (77682099 / 200000000)) (hi := (3034457 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737317495669 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(737317495669 / 500000000000) = 1/(500000000000 / 737317495669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5834 : Bounds (77682099 / 200000000) (3034457 / 7812500) (Real.log (737317495669 / 500000000000)) := by
  have h := reflection_log_5834_neg
  have he : Real.log (737317495669 / 500000000000) = -Real.log (500000000000 / 737317495669) := by
    rw [show ((737317495669 / 500000000000) : ℝ) = ((500000000000 / 737317495669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5835_neg : (194309069 / 500000000) ≤ -Real.log (250000000000 / 368735305037) ∧
    -Real.log (250000000000 / 368735305037) ≤ (388618139 / 1000000000) := by
  have h := checkLog_sound (w := (118735305037 / 618735305037)) (n := 12)
    (lo := (194309069 / 500000000)) (hi := (388618139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((368735305037 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(368735305037 / 250000000000) = 1/(250000000000 / 368735305037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5835 : Bounds (194309069 / 500000000) (388618139 / 1000000000) (Real.log (368735305037 / 250000000000)) := by
  have h := reflection_log_5835_neg
  have he : Real.log (368735305037 / 250000000000) = -Real.log (250000000000 / 368735305037) := by
    rw [show ((368735305037 / 250000000000) : ℝ) = ((250000000000 / 368735305037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5836_neg : (21954071 / 125000000) ≤ -Real.log (125 / 149) ∧
    -Real.log (125 / 149) ≤ (175632569 / 1000000000) := by
  have h := checkLog_sound (w := (12 / 137)) (n := 12)
    (lo := (21954071 / 125000000)) (hi := (175632569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149 / 125) = 1/(125 / 149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5836 : Bounds (21954071 / 125000000) (175632569 / 1000000000) (Real.log (149 / 125)) := by
  have h := reflection_log_5836_neg
  have he : Real.log (149 / 125) = -Real.log (125 / 149) := by
    rw [show ((149 / 125) : ℝ) = ((125 / 149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5837_neg : (10659661 / 50000000) ≤ -Real.log (101 / 125) ∧
    -Real.log (101 / 125) ≤ (213193221 / 1000000000) := by
  have h := checkLog_sound (w := (12 / 113)) (n := 12)
    (lo := (10659661 / 50000000)) (hi := (213193221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 101) = 1/(101 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5837 : Bounds (-213193221 / 1000000000) (-10659661 / 50000000) (Real.log (101 / 125)) := by
  have h := reflection_log_5837_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5838_neg : (191981 / 1000000000) ≤ -Real.log (15625 / 15628) ∧
    -Real.log (15625 / 15628) ≤ (95991 / 500000000) := by
  have h := checkLog_sound (w := (3 / 31253)) (n := 12)
    (lo := (191981 / 1000000000)) (hi := (95991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15628 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15628 / 15625) = 1/(15625 / 15628) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5838 : Bounds (191981 / 1000000000) (95991 / 500000000) (Real.log (15628 / 15625)) := by
  have h := reflection_log_5838_neg
  have he : Real.log (15628 / 15625) = -Real.log (15625 / 15628) := by
    rw [show ((15628 / 15625) : ℝ) = ((15625 / 15628) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5839_neg : (96009 / 500000000) ≤ -Real.log (15622 / 15625) ∧
    -Real.log (15622 / 15625) ≤ (192019 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 31247)) (n := 12)
    (lo := (96009 / 500000000)) (hi := (192019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15622) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 15622) = 1/(15622 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5839 : Bounds (-192019 / 1000000000) (-96009 / 500000000) (Real.log (15622 / 15625)) := by
  have h := reflection_log_5839_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5840_neg : (11515183 / 125000000) ≤ -Real.log (500000 / 548249) ∧
    -Real.log (500000 / 548249) ≤ (18424293 / 200000000) := by
  have h := checkLog_sound (w := (48249 / 1048249)) (n := 12)
    (lo := (11515183 / 125000000)) (hi := (18424293 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548249 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548249 / 500000) = 1/(500000 / 548249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5840 : Bounds (11515183 / 125000000) (18424293 / 200000000) (Real.log (548249 / 500000)) := by
  have h := reflection_log_5840_neg
  have he : Real.log (548249 / 500000) = -Real.log (500000 / 548249) := by
    rw [show ((548249 / 500000) : ℝ) = ((500000 / 548249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5841_neg : (20295391 / 200000000) ≤ -Real.log (451751 / 500000) ∧
    -Real.log (451751 / 500000) ≤ (25369239 / 250000000) := by
  have h := checkLog_sound (w := (48249 / 951751)) (n := 12)
    (lo := (20295391 / 200000000)) (hi := (25369239 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451751) = 1/(451751 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5841 : Bounds (-25369239 / 250000000) (-20295391 / 200000000) (Real.log (451751 / 500000)) := by
  have h := reflection_log_5841_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5842_neg : (46171527 / 500000000) ≤ -Real.log (1000000 / 1096741) ∧
    -Real.log (1000000 / 1096741) ≤ (18468611 / 200000000) := by
  have h := checkLog_sound (w := (96741 / 2096741)) (n := 12)
    (lo := (46171527 / 500000000)) (hi := (18468611 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096741 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096741 / 1000000) = 1/(1000000 / 1096741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5842 : Bounds (46171527 / 500000000) (18468611 / 200000000) (Real.log (1096741 / 1000000)) := by
  have h := reflection_log_5842_neg
  have he : Real.log (1096741 / 1000000) = -Real.log (1000000 / 1096741) := by
    rw [show ((1096741 / 1000000) : ℝ) = ((1000000 / 1096741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5843_neg : (12718243 / 125000000) ≤ -Real.log (903259 / 1000000) ∧
    -Real.log (903259 / 1000000) ≤ (20349189 / 200000000) := by
  have h := checkLog_sound (w := (96741 / 1903259)) (n := 12)
    (lo := (12718243 / 125000000)) (hi := (20349189 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903259) = 1/(903259 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5843 : Bounds (-20349189 / 200000000) (-12718243 / 125000000) (Real.log (903259 / 1000000)) := by
  have h := reflection_log_5843_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5844_neg : (940289 / 100000000) ≤ -Real.log (990641178919 / 1000000000000) ∧
    -Real.log (990641178919 / 1000000000000) ≤ (9402891 / 1000000000) := by
  have h := checkLog_sound (w := (9358821081 / 1990641178919)) (n := 12)
    (lo := (940289 / 100000000)) (hi := (9402891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990641178919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990641178919) = 1/(990641178919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5844 : Bounds (-9402891 / 1000000000) (-940289 / 100000000) (Real.log (990641178919 / 1000000000000)) := by
  have h := reflection_log_5844_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5845_neg : (935549 / 100000000) ≤ -Real.log (247672033999 / 250000000000) ∧
    -Real.log (247672033999 / 250000000000) ≤ (9355491 / 1000000000) := by
  have h := checkLog_sound (w := (2327966001 / 497672033999)) (n := 12)
    (lo := (935549 / 100000000)) (hi := (9355491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247672033999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247672033999) = 1/(247672033999 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5845 : Bounds (-9355491 / 1000000000) (-935549 / 100000000) (Real.log (247672033999 / 250000000000)) := by
  have h := reflection_log_5845_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5846_neg : (9679921 / 50000000) ≤ -Real.log (100000000000 / 121360882433) ∧
    -Real.log (100000000000 / 121360882433) ≤ (193598421 / 1000000000) := by
  have h := checkLog_sound (w := (21360882433 / 221360882433)) (n := 12)
    (lo := (9679921 / 50000000)) (hi := (193598421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121360882433 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121360882433 / 100000000000) = 1/(100000000000 / 121360882433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5846 : Bounds (9679921 / 50000000) (193598421 / 1000000000) (Real.log (121360882433 / 100000000000)) := by
  have h := reflection_log_5846_neg
  have he : Real.log (121360882433 / 100000000000) = -Real.log (100000000000 / 121360882433) := by
    rw [show ((121360882433 / 100000000000) : ℝ) = ((100000000000 / 121360882433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5847_neg : (194088999 / 1000000000) ≤ -Real.log (500000000000 / 607102171139) ∧
    -Real.log (500000000000 / 607102171139) ≤ (194089 / 1000000) := by
  have h := checkLog_sound (w := (107102171139 / 1107102171139)) (n := 12)
    (lo := (194088999 / 1000000000)) (hi := (194089 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607102171139 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607102171139 / 500000000000) = 1/(500000000000 / 607102171139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5847 : Bounds (194088999 / 1000000000) (194089 / 1000000) (Real.log (607102171139 / 500000000000)) := by
  have h := reflection_log_5847_neg
  have he : Real.log (607102171139 / 500000000000) = -Real.log (500000000000 / 607102171139) := by
    rw [show ((607102171139 / 500000000000) : ℝ) = ((500000000000 / 607102171139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5848_neg : (194309069 / 500000000) ≤ -Real.log (500000000000 / 737470610073) ∧
    -Real.log (500000000000 / 737470610073) ≤ (388618139 / 1000000000) := by
  have h := checkLog_sound (w := (237470610073 / 1237470610073)) (n := 12)
    (lo := (194309069 / 500000000)) (hi := (388618139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737470610073 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(737470610073 / 500000000000) = 1/(500000000000 / 737470610073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5848 : Bounds (194309069 / 500000000) (388618139 / 1000000000) (Real.log (737470610073 / 500000000000)) := by
  have h := reflection_log_5848_neg
  have he : Real.log (737470610073 / 500000000000) = -Real.log (500000000000 / 737470610073) := by
    rw [show ((737470610073 / 500000000000) : ℝ) = ((500000000000 / 737470610073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5849_neg : (388825789 / 1000000000) ≤ -Real.log (500000000000 / 737623762377) ∧
    -Real.log (500000000000 / 737623762377) ≤ (38882579 / 100000000) := by
  have h := checkLog_sound (w := (237623762377 / 1237623762377)) (n := 12)
    (lo := (388825789 / 1000000000)) (hi := (38882579 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737623762377 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(737623762377 / 500000000000) = 1/(500000000000 / 737623762377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5849 : Bounds (388825789 / 1000000000) (38882579 / 100000000) (Real.log (737623762377 / 500000000000)) := by
  have h := reflection_log_5849_neg
  have he : Real.log (737623762377 / 500000000000) = -Real.log (500000000000 / 737623762377) := by
    rw [show ((737623762377 / 500000000000) : ℝ) = ((500000000000 / 737623762377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5850_neg : (175716457 / 1000000000) ≤ -Real.log (10000 / 11921) ∧
    -Real.log (10000 / 11921) ≤ (87858229 / 500000000) := by
  have h := checkLog_sound (w := (1921 / 21921)) (n := 12)
    (lo := (175716457 / 1000000000)) (hi := (87858229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11921 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11921 / 10000) = 1/(10000 / 11921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5850 : Bounds (175716457 / 1000000000) (87858229 / 500000000) (Real.log (11921 / 10000)) := by
  have h := reflection_log_5850_neg
  have he : Real.log (11921 / 10000) = -Real.log (10000 / 11921) := by
    rw [show ((11921 / 10000) : ℝ) = ((10000 / 11921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5851_neg : (21331699 / 100000000) ≤ -Real.log (8079 / 10000) ∧
    -Real.log (8079 / 10000) ≤ (213316991 / 1000000000) := by
  have h := checkLog_sound (w := (1921 / 18079)) (n := 12)
    (lo := (21331699 / 100000000)) (hi := (213316991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8079) = 1/(8079 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5851 : Bounds (-213316991 / 1000000000) (-21331699 / 100000000) (Real.log (8079 / 10000)) := by
  have h := reflection_log_5851_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5852_neg : (192081 / 1000000000) ≤ -Real.log (10000000 / 10001921) ∧
    -Real.log (10000000 / 10001921) ≤ (96041 / 500000000) := by
  have h := checkLog_sound (w := (1921 / 20001921)) (n := 12)
    (lo := (192081 / 1000000000)) (hi := (96041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001921 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001921 / 10000000) = 1/(10000000 / 10001921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5852 : Bounds (192081 / 1000000000) (96041 / 500000000) (Real.log (10001921 / 10000000)) := by
  have h := reflection_log_5852_neg
  have he : Real.log (10001921 / 10000000) = -Real.log (10000000 / 10001921) := by
    rw [show ((10001921 / 10000000) : ℝ) = ((10000000 / 10001921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5853_neg : (96059 / 500000000) ≤ -Real.log (9998079 / 10000000) ∧
    -Real.log (9998079 / 10000000) ≤ (192119 / 1000000000) := by
  have h := checkLog_sound (w := (1921 / 19998079)) (n := 12)
    (lo := (96059 / 500000000)) (hi := (192119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998079) = 1/(9998079 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5853 : Bounds (-192119 / 1000000000) (-96059 / 500000000) (Real.log (9998079 / 10000000)) := by
  have h := reflection_log_5853_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5854_neg : (3686719 / 40000000) ≤ -Real.log (1000000 / 1096549) ∧
    -Real.log (1000000 / 1096549) ≤ (11520997 / 125000000) := by
  have h := checkLog_sound (w := (96549 / 2096549)) (n := 12)
    (lo := (3686719 / 40000000)) (hi := (11520997 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096549 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096549 / 1000000) = 1/(1000000 / 1096549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5854 : Bounds (3686719 / 40000000) (11520997 / 125000000) (Real.log (1096549 / 1000000)) := by
  have h := reflection_log_5854_neg
  have he : Real.log (1096549 / 1000000) = -Real.log (1000000 / 1096549) := by
    rw [show ((1096549 / 1000000) : ℝ) = ((1000000 / 1096549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5855_neg : (101533403 / 1000000000) ≤ -Real.log (903451 / 1000000) ∧
    -Real.log (903451 / 1000000) ≤ (25383351 / 250000000) := by
  have h := checkLog_sound (w := (96549 / 1903451)) (n := 12)
    (lo := (101533403 / 1000000000)) (hi := (25383351 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903451) = 1/(903451 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5855 : Bounds (-25383351 / 250000000) (-101533403 / 1000000000) (Real.log (903451 / 1000000)) := by
  have h := reflection_log_5855_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5856_neg : (18477911 / 200000000) ≤ -Real.log (125000 / 137099) ∧
    -Real.log (125000 / 137099) ≤ (23097389 / 250000000) := by
  have h := checkLog_sound (w := (12099 / 262099)) (n := 12)
    (lo := (18477911 / 200000000)) (hi := (23097389 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137099 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137099 / 125000) = 1/(125000 / 137099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5856 : Bounds (18477911 / 200000000) (23097389 / 250000000) (Real.log (137099 / 125000)) := by
  have h := reflection_log_5856_neg
  have he : Real.log (137099 / 125000) = -Real.log (125000 / 137099) := by
    rw [show ((137099 / 125000) : ℝ) = ((125000 / 137099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5857_neg : (12725301 / 125000000) ≤ -Real.log (112901 / 125000) ∧
    -Real.log (112901 / 125000) ≤ (101802409 / 1000000000) := by
  have h := checkLog_sound (w := (12099 / 237901)) (n := 12)
    (lo := (12725301 / 125000000)) (hi := (101802409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 112901) = 1/(112901 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5857 : Bounds (-101802409 / 1000000000) (-12725301 / 125000000) (Real.log (112901 / 125000)) := by
  have h := reflection_log_5857_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5858_neg : (9412853 / 1000000000) ≤ -Real.log (15478614199 / 15625000000) ∧
    -Real.log (15478614199 / 15625000000) ≤ (4706427 / 500000000) := by
  have h := checkLog_sound (w := (146385801 / 31103614199)) (n := 12)
    (lo := (9412853 / 1000000000)) (hi := (4706427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15478614199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15478614199) = 1/(15478614199 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5858 : Bounds (-4706427 / 500000000) (-9412853 / 1000000000) (Real.log (15478614199 / 15625000000)) := by
  have h := reflection_log_5858_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5859_neg : (2341357 / 250000000) ≤ -Real.log (990678290599 / 1000000000000) ∧
    -Real.log (990678290599 / 1000000000000) ≤ (9365429 / 1000000000) := by
  have h := checkLog_sound (w := (9321709401 / 1990678290599)) (n := 12)
    (lo := (2341357 / 250000000)) (hi := (9365429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990678290599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990678290599) = 1/(990678290599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5859 : Bounds (-9365429 / 1000000000) (-2341357 / 250000000) (Real.log (990678290599 / 1000000000000)) := by
  have h := reflection_log_5859_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5860_neg : (193701379 / 1000000000) ≤ -Real.log (125000000000 / 151716722877) ∧
    -Real.log (125000000000 / 151716722877) ≤ (9685069 / 50000000) := by
  have h := checkLog_sound (w := (26716722877 / 276716722877)) (n := 12)
    (lo := (193701379 / 1000000000)) (hi := (9685069 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151716722877 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151716722877 / 125000000000) = 1/(125000000000 / 151716722877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5860 : Bounds (193701379 / 1000000000) (9685069 / 50000000) (Real.log (151716722877 / 125000000000)) := by
  have h := reflection_log_5860_neg
  have he : Real.log (151716722877 / 125000000000) = -Real.log (125000000000 / 151716722877) := by
    rw [show ((151716722877 / 125000000000) : ℝ) = ((125000000000 / 151716722877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5861_neg : (48547991 / 250000000) ≤ -Real.log (62500000000 / 75895585513) ∧
    -Real.log (62500000000 / 75895585513) ≤ (38838393 / 200000000) := by
  have h := checkLog_sound (w := (13395585513 / 138395585513)) (n := 12)
    (lo := (48547991 / 250000000)) (hi := (38838393 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75895585513 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75895585513 / 62500000000) = 1/(62500000000 / 75895585513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5861 : Bounds (48547991 / 250000000) (38838393 / 200000000) (Real.log (75895585513 / 62500000000)) := by
  have h := reflection_log_5861_neg
  have he : Real.log (75895585513 / 62500000000) = -Real.log (62500000000 / 75895585513) := by
    rw [show ((75895585513 / 62500000000) : ℝ) = ((62500000000 / 75895585513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5862_neg : (388825789 / 1000000000) ≤ -Real.log (62500000000 / 92202970297) ∧
    -Real.log (62500000000 / 92202970297) ≤ (38882579 / 100000000) := by
  have h := checkLog_sound (w := (29702970297 / 154702970297)) (n := 12)
    (lo := (388825789 / 1000000000)) (hi := (38882579 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92202970297 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92202970297 / 62500000000) = 1/(62500000000 / 92202970297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5862 : Bounds (388825789 / 1000000000) (38882579 / 100000000) (Real.log (92202970297 / 62500000000)) := by
  have h := reflection_log_5862_neg
  have he : Real.log (92202970297 / 62500000000) = -Real.log (62500000000 / 92202970297) := by
    rw [show ((92202970297 / 62500000000) : ℝ) = ((62500000000 / 92202970297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5863_neg : (48629181 / 125000000) ≤ -Real.log (250000000000 / 368888476297) ∧
    -Real.log (250000000000 / 368888476297) ≤ (389033449 / 1000000000) := by
  have h := checkLog_sound (w := (118888476297 / 618888476297)) (n := 12)
    (lo := (48629181 / 125000000)) (hi := (389033449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((368888476297 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(368888476297 / 250000000000) = 1/(250000000000 / 368888476297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5863 : Bounds (48629181 / 125000000) (389033449 / 1000000000) (Real.log (368888476297 / 250000000000)) := by
  have h := reflection_log_5863_neg
  have he : Real.log (368888476297 / 250000000000) = -Real.log (250000000000 / 368888476297) := by
    rw [show ((368888476297 / 250000000000) : ℝ) = ((250000000000 / 368888476297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5864_neg : (175800339 / 1000000000) ≤ -Real.log (5000 / 5961) ∧
    -Real.log (5000 / 5961) ≤ (8790017 / 50000000) := by
  have h := checkLog_sound (w := (961 / 10961)) (n := 12)
    (lo := (175800339 / 1000000000)) (hi := (8790017 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5961 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5961 / 5000) = 1/(5000 / 5961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5864 : Bounds (175800339 / 1000000000) (8790017 / 50000000) (Real.log (5961 / 5000)) := by
  have h := reflection_log_5864_neg
  have he : Real.log (5961 / 5000) = -Real.log (5000 / 5961) := by
    rw [show ((5961 / 5000) : ℝ) = ((5000 / 5961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5865_neg : (8537631 / 40000000) ≤ -Real.log (4039 / 5000) ∧
    -Real.log (4039 / 5000) ≤ (26680097 / 125000000) := by
  have h := checkLog_sound (w := (961 / 9039)) (n := 12)
    (lo := (8537631 / 40000000)) (hi := (26680097 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4039) = 1/(4039 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5865 : Bounds (-26680097 / 125000000) (-8537631 / 40000000) (Real.log (4039 / 5000)) := by
  have h := reflection_log_5865_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5866_neg : (192181 / 1000000000) ≤ -Real.log (5000000 / 5000961) ∧
    -Real.log (5000000 / 5000961) ≤ (96091 / 500000000) := by
  have h := checkLog_sound (w := (961 / 10000961)) (n := 12)
    (lo := (192181 / 1000000000)) (hi := (96091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000961 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000961 / 5000000) = 1/(5000000 / 5000961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5866 : Bounds (192181 / 1000000000) (96091 / 500000000) (Real.log (5000961 / 5000000)) := by
  have h := reflection_log_5866_neg
  have he : Real.log (5000961 / 5000000) = -Real.log (5000000 / 5000961) := by
    rw [show ((5000961 / 5000000) : ℝ) = ((5000000 / 5000961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5867_neg : (96109 / 500000000) ≤ -Real.log (4999039 / 5000000) ∧
    -Real.log (4999039 / 5000000) ≤ (192219 / 1000000000) := by
  have h := checkLog_sound (w := (961 / 9999039)) (n := 12)
    (lo := (96109 / 500000000)) (hi := (192219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999039) = 1/(4999039 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5867 : Bounds (-192219 / 1000000000) (-96109 / 500000000) (Real.log (4999039 / 5000000)) := by
  have h := reflection_log_5867_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5868_neg : (92214483 / 1000000000) ≤ -Real.log (5000 / 5483) ∧
    -Real.log (5000 / 5483) ≤ (23053621 / 250000000) := by
  have h := checkLog_sound (w := (483 / 10483)) (n := 12)
    (lo := (92214483 / 1000000000)) (hi := (23053621 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5483 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5483 / 5000) = 1/(5000 / 5483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5868 : Bounds (92214483 / 1000000000) (23053621 / 250000000) (Real.log (5483 / 5000)) := by
  have h := reflection_log_5868_neg
  have he : Real.log (5483 / 5000) = -Real.log (5000 / 5483) := by
    rw [show ((5483 / 5000) : ℝ) = ((5000 / 5483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5869_neg : (20317971 / 200000000) ≤ -Real.log (4517 / 5000) ∧
    -Real.log (4517 / 5000) ≤ (3174683 / 31250000) := by
  have h := checkLog_sound (w := (483 / 9517)) (n := 12)
    (lo := (20317971 / 200000000)) (hi := (3174683 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4517) = 1/(4517 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5869 : Bounds (-3174683 / 31250000) (-20317971 / 200000000) (Real.log (4517 / 5000)) := by
  have h := reflection_log_5869_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5870_neg : (92436053 / 1000000000) ≤ -Real.log (1000000 / 1096843) ∧
    -Real.log (1000000 / 1096843) ≤ (46218027 / 500000000) := by
  have h := checkLog_sound (w := (96843 / 2096843)) (n := 12)
    (lo := (92436053 / 1000000000)) (hi := (46218027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096843 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096843 / 1000000) = 1/(1000000 / 1096843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5870 : Bounds (92436053 / 1000000000) (46218027 / 500000000) (Real.log (1096843 / 1000000)) := by
  have h := reflection_log_5870_neg
  have he : Real.log (1096843 / 1000000) = -Real.log (1000000 / 1096843) := by
    rw [show ((1096843 / 1000000) : ℝ) = ((1000000 / 1096843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5871_neg : (814871 / 8000000) ≤ -Real.log (903157 / 1000000) ∧
    -Real.log (903157 / 1000000) ≤ (25464719 / 250000000) := by
  have h := checkLog_sound (w := (96843 / 1903157)) (n := 12)
    (lo := (814871 / 8000000)) (hi := (25464719 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903157) = 1/(903157 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5871 : Bounds (-25464719 / 250000000) (-814871 / 8000000) (Real.log (903157 / 1000000)) := by
  have h := reflection_log_5871_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5872_neg : (4711411 / 500000000) ≤ -Real.log (990621433351 / 1000000000000) ∧
    -Real.log (990621433351 / 1000000000000) ≤ (9422823 / 1000000000) := by
  have h := checkLog_sound (w := (9378566649 / 1990621433351)) (n := 12)
    (lo := (4711411 / 500000000)) (hi := (9422823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990621433351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990621433351) = 1/(990621433351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5872 : Bounds (-9422823 / 1000000000) (-4711411 / 500000000) (Real.log (990621433351 / 1000000000000)) := by
  have h := reflection_log_5872_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5873_neg : (9375371 / 1000000000) ≤ -Real.log (24766711 / 25000000) ∧
    -Real.log (24766711 / 25000000) ≤ (2343843 / 250000000) := by
  have h := checkLog_sound (w := (233289 / 49766711)) (n := 12)
    (lo := (9375371 / 1000000000)) (hi := (2343843 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000000 / 24766711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000000 / 24766711) = 1/(24766711 / 25000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5873 : Bounds (-2343843 / 250000000) (-9375371 / 1000000000) (Real.log (24766711 / 25000000)) := by
  have h := reflection_log_5873_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5874_neg : (193804339 / 1000000000) ≤ -Real.log (100000000000 / 121385875581) ∧
    -Real.log (100000000000 / 121385875581) ≤ (9690217 / 50000000) := by
  have h := checkLog_sound (w := (21385875581 / 221385875581)) (n := 12)
    (lo := (193804339 / 1000000000)) (hi := (9690217 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121385875581 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121385875581 / 100000000000) = 1/(100000000000 / 121385875581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5874 : Bounds (193804339 / 1000000000) (9690217 / 50000000) (Real.log (121385875581 / 100000000000)) := by
  have h := reflection_log_5874_neg
  have he : Real.log (121385875581 / 100000000000) = -Real.log (100000000000 / 121385875581) := by
    rw [show ((121385875581 / 100000000000) : ℝ) = ((100000000000 / 121385875581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5875_neg : (194294929 / 1000000000) ≤ -Real.log (50000000000 / 60722720413) ∧
    -Real.log (50000000000 / 60722720413) ≤ (19429493 / 100000000) := by
  have h := checkLog_sound (w := (10722720413 / 110722720413)) (n := 12)
    (lo := (194294929 / 1000000000)) (hi := (19429493 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60722720413 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60722720413 / 50000000000) = 1/(50000000000 / 60722720413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5875 : Bounds (194294929 / 1000000000) (19429493 / 100000000) (Real.log (60722720413 / 50000000000)) := by
  have h := reflection_log_5875_neg
  have he : Real.log (60722720413 / 50000000000) = -Real.log (50000000000 / 60722720413) := by
    rw [show ((60722720413 / 50000000000) : ℝ) = ((50000000000 / 60722720413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5876_neg : (48629181 / 125000000) ≤ -Real.log (500000000000 / 737776952593) ∧
    -Real.log (500000000000 / 737776952593) ≤ (389033449 / 1000000000) := by
  have h := checkLog_sound (w := (237776952593 / 1237776952593)) (n := 12)
    (lo := (48629181 / 125000000)) (hi := (389033449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737776952593 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(737776952593 / 500000000000) = 1/(500000000000 / 737776952593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5876 : Bounds (48629181 / 125000000) (389033449 / 1000000000) (Real.log (737776952593 / 500000000000)) := by
  have h := reflection_log_5876_neg
  have he : Real.log (737776952593 / 500000000000) = -Real.log (500000000000 / 737776952593) := by
    rw [show ((737776952593 / 500000000000) : ℝ) = ((500000000000 / 737776952593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5877_neg : (77848223 / 200000000) ≤ -Real.log (250000000000 / 368965090369) ∧
    -Real.log (250000000000 / 368965090369) ≤ (97310279 / 250000000) := by
  have h := checkLog_sound (w := (118965090369 / 618965090369)) (n := 12)
    (lo := (77848223 / 200000000)) (hi := (97310279 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((368965090369 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(368965090369 / 250000000000) = 1/(250000000000 / 368965090369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5877 : Bounds (77848223 / 200000000) (97310279 / 250000000) (Real.log (368965090369 / 250000000000)) := by
  have h := reflection_log_5877_neg
  have he : Real.log (368965090369 / 250000000000) = -Real.log (250000000000 / 368965090369) := by
    rw [show ((368965090369 / 250000000000) : ℝ) = ((250000000000 / 368965090369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5878_neg : (87942107 / 500000000) ≤ -Real.log (10000 / 11923) ∧
    -Real.log (10000 / 11923) ≤ (35176843 / 200000000) := by
  have h := checkLog_sound (w := (1923 / 21923)) (n := 12)
    (lo := (87942107 / 500000000)) (hi := (35176843 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11923 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11923 / 10000) = 1/(10000 / 11923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5878 : Bounds (87942107 / 500000000) (35176843 / 200000000) (Real.log (11923 / 10000)) := by
  have h := reflection_log_5878_neg
  have he : Real.log (11923 / 10000) = -Real.log (10000 / 11923) := by
    rw [show ((11923 / 10000) : ℝ) = ((10000 / 11923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5879_neg : (6673893 / 31250000) ≤ -Real.log (8077 / 10000) ∧
    -Real.log (8077 / 10000) ≤ (213564577 / 1000000000) := by
  have h := checkLog_sound (w := (1923 / 18077)) (n := 12)
    (lo := (6673893 / 31250000)) (hi := (213564577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8077) = 1/(8077 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5879 : Bounds (-213564577 / 1000000000) (-6673893 / 31250000) (Real.log (8077 / 10000)) := by
  have h := reflection_log_5879_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5880_neg : (192281 / 1000000000) ≤ -Real.log (10000000 / 10001923) ∧
    -Real.log (10000000 / 10001923) ≤ (96141 / 500000000) := by
  have h := checkLog_sound (w := (1923 / 20001923)) (n := 12)
    (lo := (192281 / 1000000000)) (hi := (96141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001923 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001923 / 10000000) = 1/(10000000 / 10001923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5880 : Bounds (192281 / 1000000000) (96141 / 500000000) (Real.log (10001923 / 10000000)) := by
  have h := reflection_log_5880_neg
  have he : Real.log (10001923 / 10000000) = -Real.log (10000000 / 10001923) := by
    rw [show ((10001923 / 10000000) : ℝ) = ((10000000 / 10001923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5881_neg : (96159 / 500000000) ≤ -Real.log (9998077 / 10000000) ∧
    -Real.log (9998077 / 10000000) ≤ (192319 / 1000000000) := by
  have h := checkLog_sound (w := (1923 / 19998077)) (n := 12)
    (lo := (96159 / 500000000)) (hi := (192319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998077) = 1/(9998077 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5881 : Bounds (-192319 / 1000000000) (-96159 / 500000000) (Real.log (9998077 / 10000000)) := by
  have h := reflection_log_5881_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5882_neg : (9226099 / 100000000) ≤ -Real.log (1000000 / 1096651) ∧
    -Real.log (1000000 / 1096651) ≤ (92260991 / 1000000000) := by
  have h := checkLog_sound (w := (96651 / 2096651)) (n := 12)
    (lo := (9226099 / 100000000)) (hi := (92260991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096651 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096651 / 1000000) = 1/(1000000 / 1096651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5882 : Bounds (9226099 / 100000000) (92260991 / 1000000000) (Real.log (1096651 / 1000000)) := by
  have h := reflection_log_5882_neg
  have he : Real.log (1096651 / 1000000) = -Real.log (1000000 / 1096651) := by
    rw [show ((1096651 / 1000000) : ℝ) = ((1000000 / 1096651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5883_neg : (10164631 / 100000000) ≤ -Real.log (903349 / 1000000) ∧
    -Real.log (903349 / 1000000) ≤ (101646311 / 1000000000) := by
  have h := checkLog_sound (w := (96651 / 1903349)) (n := 12)
    (lo := (10164631 / 100000000)) (hi := (101646311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903349) = 1/(903349 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5883 : Bounds (-101646311 / 1000000000) (-10164631 / 100000000) (Real.log (903349 / 1000000)) := by
  have h := reflection_log_5883_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5884_neg : (92482549 / 1000000000) ≤ -Real.log (500000 / 548447) ∧
    -Real.log (500000 / 548447) ≤ (1849651 / 20000000) := by
  have h := checkLog_sound (w := (48447 / 1048447)) (n := 12)
    (lo := (92482549 / 1000000000)) (hi := (1849651 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548447 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548447 / 500000) = 1/(500000 / 548447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5884 : Bounds (92482549 / 1000000000) (1849651 / 20000000) (Real.log (548447 / 500000)) := by
  have h := reflection_log_5884_neg
  have he : Real.log (548447 / 500000) = -Real.log (500000 / 548447) := by
    rw [show ((548447 / 500000) : ℝ) = ((500000 / 548447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5885_neg : (20383069 / 200000000) ≤ -Real.log (451553 / 500000) ∧
    -Real.log (451553 / 500000) ≤ (50957673 / 500000000) := by
  have h := checkLog_sound (w := (48447 / 951553)) (n := 12)
    (lo := (20383069 / 200000000)) (hi := (50957673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451553) = 1/(451553 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5885 : Bounds (-50957673 / 500000000) (-20383069 / 200000000) (Real.log (451553 / 500000)) := by
  have h := reflection_log_5885_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5886_neg : (2358199 / 250000000) ≤ -Real.log (247652888191 / 250000000000) ∧
    -Real.log (247652888191 / 250000000000) ≤ (9432797 / 1000000000) := by
  have h := checkLog_sound (w := (2347111809 / 497652888191)) (n := 12)
    (lo := (2358199 / 250000000)) (hi := (9432797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247652888191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247652888191) = 1/(247652888191 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5886 : Bounds (-9432797 / 1000000000) (-2358199 / 250000000) (Real.log (247652888191 / 250000000000)) := by
  have h := reflection_log_5886_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5887_neg : (234633 / 25000000) ≤ -Real.log (990658584199 / 1000000000000) ∧
    -Real.log (990658584199 / 1000000000000) ≤ (9385321 / 1000000000) := by
  have h := checkLog_sound (w := (9341415801 / 1990658584199)) (n := 12)
    (lo := (234633 / 25000000)) (hi := (9385321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990658584199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990658584199) = 1/(990658584199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5887 : Bounds (-9385321 / 1000000000) (-234633 / 25000000) (Real.log (990658584199 / 1000000000000)) := by
  have h := reflection_log_5887_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


