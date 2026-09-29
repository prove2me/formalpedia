-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0138__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0138__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T09:07:30.865264+00:00
-- url     : https://prove2.me/theorems/fa24739d-a91a-4634-8d5e-6b7f0840c526
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0138 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0139, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0138 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0139, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0140)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0138 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0139, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0140)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0138 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0139, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0140) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0138 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0139, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0140).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0138 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8832_neg : (145470957 / 1000000000) ≤ -Real.log (172923 / 200000) ∧
    -Real.log (172923 / 200000) ≤ (72735479 / 500000000) := by
  have h := checkLog_sound (w := (27077 / 372923)) (n := 12)
    (lo := (145470957 / 1000000000)) (hi := (72735479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 172923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 172923) = 1/(172923 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8832 : Bounds (-72735479 / 500000000) (-145470957 / 1000000000) (Real.log (172923 / 200000)) := by
  have h := reflection_log_8832_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8833_neg : (18499157 / 1000000000) ≤ -Real.log (39266836071 / 40000000000) ∧
    -Real.log (39266836071 / 40000000000) ≤ (9249579 / 500000000) := by
  have h := checkLog_sound (w := (733163929 / 79266836071)) (n := 12)
    (lo := (18499157 / 1000000000)) (hi := (9249579 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39266836071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39266836071) = 1/(39266836071 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8833 : Bounds (-9249579 / 500000000) (-18499157 / 1000000000) (Real.log (39266836071 / 40000000000)) := by
  have h := reflection_log_8833_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8834_neg : (9177457 / 500000000) ≤ -Real.log (981812510679 / 1000000000000) ∧
    -Real.log (981812510679 / 1000000000000) ≤ (3670983 / 200000000) := by
  have h := checkLog_sound (w := (18187489321 / 1981812510679)) (n := 12)
    (lo := (9177457 / 500000000)) (hi := (3670983 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981812510679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981812510679) = 1/(981812510679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8834 : Bounds (-3670983 / 200000000) (-9177457 / 500000000) (Real.log (981812510679 / 1000000000000)) := by
  have h := reflection_log_8834_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8835_neg : (271375267 / 1000000000) ≤ -Real.log (500000000000 / 655883621013) ∧
    -Real.log (500000000000 / 655883621013) ≤ (67843817 / 250000000) := by
  have h := checkLog_sound (w := (155883621013 / 1155883621013)) (n := 12)
    (lo := (271375267 / 1000000000)) (hi := (67843817 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((655883621013 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(655883621013 / 500000000000) = 1/(500000000000 / 655883621013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8835 : Bounds (271375267 / 1000000000) (67843817 / 250000000) (Real.log (655883621013 / 500000000000)) := by
  have h := reflection_log_8835_neg
  have he : Real.log (655883621013 / 500000000000) = -Real.log (500000000000 / 655883621013) := by
    rw [show ((655883621013 / 500000000000) : ℝ) = ((500000000000 / 655883621013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8836_neg : (136221379 / 500000000) ≤ -Real.log (125000000000 / 164146036097) ∧
    -Real.log (125000000000 / 164146036097) ≤ (272442759 / 1000000000) := by
  have h := checkLog_sound (w := (39146036097 / 289146036097)) (n := 12)
    (lo := (136221379 / 500000000)) (hi := (272442759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164146036097 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164146036097 / 125000000000) = 1/(125000000000 / 164146036097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8836 : Bounds (136221379 / 500000000) (272442759 / 1000000000) (Real.log (164146036097 / 125000000000)) := by
  have h := reflection_log_8836_neg
  have he : Real.log (164146036097 / 125000000000) = -Real.log (125000000000 / 164146036097) := by
    rw [show ((164146036097 / 125000000000) : ℝ) = ((125000000000 / 164146036097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8837_neg : (546184871 / 1000000000) ≤ -Real.log (5000000000 / 8633265167) ∧
    -Real.log (5000000000 / 8633265167) ≤ (68273109 / 125000000) := by
  have h := checkLog_sound (w := (3633265167 / 13633265167)) (n := 12)
    (lo := (546184871 / 1000000000)) (hi := (68273109 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8633265167 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8633265167 / 5000000000) = 1/(5000000000 / 8633265167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8837 : Bounds (546184871 / 1000000000) (68273109 / 125000000) (Real.log (8633265167 / 5000000000)) := by
  have h := reflection_log_8837_neg
  have he : Real.log (8633265167 / 5000000000) = -Real.log (5000000000 / 8633265167) := by
    rw [show ((8633265167 / 5000000000) : ℝ) = ((5000000000 / 8633265167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8838_neg : (273630739 / 500000000) ≤ -Real.log (500000000000 / 864256480219) ∧
    -Real.log (500000000000 / 864256480219) ≤ (547261479 / 1000000000) := by
  have h := checkLog_sound (w := (364256480219 / 1364256480219)) (n := 12)
    (lo := (273630739 / 500000000)) (hi := (547261479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((864256480219 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(864256480219 / 500000000000) = 1/(500000000000 / 864256480219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8838 : Bounds (273630739 / 500000000) (547261479 / 1000000000) (Real.log (864256480219 / 500000000000)) := by
  have h := reflection_log_8838_neg
  have he : Real.log (864256480219 / 500000000000) = -Real.log (500000000000 / 864256480219) := by
    rw [show ((864256480219 / 500000000000) : ℝ) = ((500000000000 / 864256480219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8839_neg : (29630807 / 125000000) ≤ -Real.log (400 / 507) ∧
    -Real.log (400 / 507) ≤ (237046457 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 907)) (n := 12)
    (lo := (29630807 / 125000000)) (hi := (237046457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((507 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(507 / 400) = 1/(400 / 507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8839 : Bounds (29630807 / 125000000) (237046457 / 1000000000) (Real.log (507 / 400)) := by
  have h := reflection_log_8839_neg
  have he : Real.log (507 / 400) = -Real.log (400 / 507) := by
    rw [show ((507 / 400) : ℝ) = ((400 / 507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8840_neg : (155645969 / 500000000) ≤ -Real.log (293 / 400) ∧
    -Real.log (293 / 400) ≤ (311291939 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 693)) (n := 12)
    (lo := (155645969 / 500000000)) (hi := (311291939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 293) = 1/(293 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8840 : Bounds (-311291939 / 1000000000) (-155645969 / 500000000) (Real.log (293 / 400)) := by
  have h := reflection_log_8840_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8841_neg : (33433 / 125000000) ≤ -Real.log (400000 / 400107) ∧
    -Real.log (400000 / 400107) ≤ (53493 / 200000000) := by
  have h := checkLog_sound (w := (107 / 800107)) (n := 12)
    (lo := (33433 / 125000000)) (hi := (53493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400107 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400107 / 400000) = 1/(400000 / 400107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8841 : Bounds (33433 / 125000000) (53493 / 200000000) (Real.log (400107 / 400000)) := by
  have h := reflection_log_8841_neg
  have he : Real.log (400107 / 400000) = -Real.log (400000 / 400107) := by
    rw [show ((400107 / 400000) : ℝ) = ((400000 / 400107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8842_neg : (53507 / 200000000) ≤ -Real.log (399893 / 400000) ∧
    -Real.log (399893 / 400000) ≤ (16721 / 62500000) := by
  have h := checkLog_sound (w := (107 / 799893)) (n := 12)
    (lo := (53507 / 200000000)) (hi := (16721 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399893) = 1/(399893 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8842 : Bounds (-16721 / 62500000) (-53507 / 200000000) (Real.log (399893 / 400000)) := by
  have h := reflection_log_8842_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8843_neg : (126739253 / 1000000000) ≤ -Real.log (1000000 / 1135121) ∧
    -Real.log (1000000 / 1135121) ≤ (63369627 / 500000000) := by
  have h := checkLog_sound (w := (135121 / 2135121)) (n := 12)
    (lo := (126739253 / 1000000000)) (hi := (63369627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1135121 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1135121 / 1000000) = 1/(1000000 / 1135121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8843 : Bounds (126739253 / 1000000000) (63369627 / 500000000) (Real.log (1135121 / 1000000)) := by
  have h := reflection_log_8843_neg
  have he : Real.log (1135121 / 1000000) = -Real.log (1000000 / 1135121) := by
    rw [show ((1135121 / 1000000) : ℝ) = ((1000000 / 1135121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8844_neg : (72582833 / 500000000) ≤ -Real.log (864879 / 1000000) ∧
    -Real.log (864879 / 1000000) ≤ (145165667 / 1000000000) := by
  have h := checkLog_sound (w := (135121 / 1864879)) (n := 12)
    (lo := (72582833 / 500000000)) (hi := (145165667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 864879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 864879) = 1/(864879 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8844 : Bounds (-145165667 / 1000000000) (-72582833 / 500000000) (Real.log (864879 / 1000000)) := by
  have h := reflection_log_8844_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8845_neg : (31800413 / 250000000) ≤ -Real.log (500000 / 567823) ∧
    -Real.log (500000 / 567823) ≤ (127201653 / 1000000000) := by
  have h := checkLog_sound (w := (67823 / 1067823)) (n := 12)
    (lo := (31800413 / 250000000)) (hi := (127201653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((567823 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(567823 / 500000) = 1/(500000 / 567823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8845 : Bounds (31800413 / 250000000) (127201653 / 1000000000) (Real.log (567823 / 500000)) := by
  have h := reflection_log_8845_neg
  have he : Real.log (567823 / 500000) = -Real.log (500000 / 567823) := by
    rw [show ((567823 / 500000) : ℝ) = ((500000 / 567823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8846_neg : (145772871 / 1000000000) ≤ -Real.log (432177 / 500000) ∧
    -Real.log (432177 / 500000) ≤ (18221609 / 125000000) := by
  have h := checkLog_sound (w := (67823 / 932177)) (n := 12)
    (lo := (145772871 / 1000000000)) (hi := (18221609 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 432177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 432177) = 1/(432177 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8846 : Bounds (-18221609 / 125000000) (-145772871 / 1000000000) (Real.log (432177 / 500000)) := by
  have h := reflection_log_8846_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8847_neg : (18571219 / 1000000000) ≤ -Real.log (245400040671 / 250000000000) ∧
    -Real.log (245400040671 / 250000000000) ≤ (928561 / 50000000) := by
  have h := checkLog_sound (w := (4599959329 / 495400040671)) (n := 12)
    (lo := (18571219 / 1000000000)) (hi := (928561 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245400040671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245400040671) = 1/(245400040671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8847 : Bounds (-928561 / 50000000) (-18571219 / 1000000000) (Real.log (245400040671 / 250000000000)) := by
  have h := reflection_log_8847_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8848_neg : (18426413 / 1000000000) ≤ -Real.log (981742315359 / 1000000000000) ∧
    -Real.log (981742315359 / 1000000000000) ≤ (9213207 / 500000000) := by
  have h := checkLog_sound (w := (18257684641 / 1981742315359)) (n := 12)
    (lo := (18426413 / 1000000000)) (hi := (9213207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981742315359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981742315359) = 1/(981742315359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8848 : Bounds (-9213207 / 500000000) (-18426413 / 1000000000) (Real.log (981742315359 / 1000000000000)) := by
  have h := reflection_log_8848_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8849_neg : (271904919 / 1000000000) ≤ -Real.log (500000000000 / 656231102847) ∧
    -Real.log (500000000000 / 656231102847) ≤ (6797623 / 25000000) := by
  have h := checkLog_sound (w := (156231102847 / 1156231102847)) (n := 12)
    (lo := (271904919 / 1000000000)) (hi := (6797623 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((656231102847 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(656231102847 / 500000000000) = 1/(500000000000 / 656231102847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8849 : Bounds (271904919 / 1000000000) (6797623 / 25000000) (Real.log (656231102847 / 500000000000)) := by
  have h := reflection_log_8849_neg
  have he : Real.log (656231102847 / 500000000000) = -Real.log (500000000000 / 656231102847) := by
    rw [show ((656231102847 / 500000000000) : ℝ) = ((500000000000 / 656231102847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8850_neg : (272974523 / 1000000000) ≤ -Real.log (50000000000 / 65693338609) ∧
    -Real.log (50000000000 / 65693338609) ≤ (68243631 / 250000000) := by
  have h := checkLog_sound (w := (15693338609 / 115693338609)) (n := 12)
    (lo := (272974523 / 1000000000)) (hi := (68243631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65693338609 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(65693338609 / 50000000000) = 1/(50000000000 / 65693338609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8850 : Bounds (272974523 / 1000000000) (68243631 / 250000000) (Real.log (65693338609 / 50000000000)) := by
  have h := reflection_log_8850_neg
  have he : Real.log (65693338609 / 50000000000) = -Real.log (50000000000 / 65693338609) := by
    rw [show ((65693338609 / 50000000000) : ℝ) = ((50000000000 / 65693338609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8851_neg : (273630739 / 500000000) ≤ -Real.log (250000000000 / 432128240109) ∧
    -Real.log (250000000000 / 432128240109) ≤ (547261479 / 1000000000) := by
  have h := checkLog_sound (w := (182128240109 / 682128240109)) (n := 12)
    (lo := (273630739 / 500000000)) (hi := (547261479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((432128240109 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(432128240109 / 250000000000) = 1/(250000000000 / 432128240109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8851 : Bounds (273630739 / 500000000) (547261479 / 1000000000) (Real.log (432128240109 / 250000000000)) := by
  have h := reflection_log_8851_neg
  have he : Real.log (432128240109 / 250000000000) = -Real.log (250000000000 / 432128240109) := by
    rw [show ((432128240109 / 250000000000) : ℝ) = ((250000000000 / 432128240109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8852_neg : (274169197 / 500000000) ≤ -Real.log (500000000000 / 865187713311) ∧
    -Real.log (500000000000 / 865187713311) ≤ (109667679 / 200000000) := by
  have h := checkLog_sound (w := (365187713311 / 1365187713311)) (n := 12)
    (lo := (274169197 / 500000000)) (hi := (109667679 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((865187713311 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(865187713311 / 500000000000) = 1/(500000000000 / 865187713311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8852 : Bounds (274169197 / 500000000) (109667679 / 200000000) (Real.log (865187713311 / 500000000000)) := by
  have h := reflection_log_8852_neg
  have he : Real.log (865187713311 / 500000000000) = -Real.log (500000000000 / 865187713311) := by
    rw [show ((865187713311 / 500000000000) : ℝ) = ((500000000000 / 865187713311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8853_neg : (29680107 / 125000000) ≤ -Real.log (250 / 317) ∧
    -Real.log (250 / 317) ≤ (237440857 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 567)) (n := 12)
    (lo := (29680107 / 125000000)) (hi := (237440857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(317 / 250) = 1/(250 / 317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8853 : Bounds (29680107 / 125000000) (237440857 / 1000000000) (Real.log (317 / 250)) := by
  have h := reflection_log_8853_neg
  have he : Real.log (317 / 250) = -Real.log (250 / 317) := by
    rw [show ((317 / 250) : ℝ) = ((250 / 317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8854_neg : (62394953 / 200000000) ≤ -Real.log (183 / 250) ∧
    -Real.log (183 / 250) ≤ (155987383 / 500000000) := by
  have h := checkLog_sound (w := (67 / 433)) (n := 12)
    (lo := (62394953 / 200000000)) (hi := (155987383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 183) = 1/(183 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8854 : Bounds (-155987383 / 500000000) (-62394953 / 200000000) (Real.log (183 / 250)) := by
  have h := reflection_log_8854_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8855_neg : (66991 / 250000000) ≤ -Real.log (250000 / 250067) ∧
    -Real.log (250000 / 250067) ≤ (53593 / 200000000) := by
  have h := checkLog_sound (w := (67 / 500067)) (n := 12)
    (lo := (66991 / 250000000)) (hi := (53593 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250067 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250067 / 250000) = 1/(250000 / 250067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8855 : Bounds (66991 / 250000000) (53593 / 200000000) (Real.log (250067 / 250000)) := by
  have h := reflection_log_8855_neg
  have he : Real.log (250067 / 250000) = -Real.log (250000 / 250067) := by
    rw [show ((250067 / 250000) : ℝ) = ((250000 / 250067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8856_neg : (53607 / 200000000) ≤ -Real.log (249933 / 250000) ∧
    -Real.log (249933 / 250000) ≤ (67009 / 250000000) := by
  have h := checkLog_sound (w := (67 / 499933)) (n := 12)
    (lo := (53607 / 200000000)) (hi := (67009 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249933) = 1/(249933 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8856 : Bounds (-67009 / 250000000) (-53607 / 200000000) (Real.log (249933 / 250000)) := by
  have h := reflection_log_8856_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8857_neg : (126968277 / 1000000000) ≤ -Real.log (1000000 / 1135381) ∧
    -Real.log (1000000 / 1135381) ≤ (63484139 / 500000000) := by
  have h := checkLog_sound (w := (135381 / 2135381)) (n := 12)
    (lo := (126968277 / 1000000000)) (hi := (63484139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1135381 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1135381 / 1000000) = 1/(1000000 / 1135381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8857 : Bounds (126968277 / 1000000000) (63484139 / 500000000) (Real.log (1135381 / 1000000)) := by
  have h := reflection_log_8857_neg
  have he : Real.log (1135381 / 1000000) = -Real.log (1000000 / 1135381) := by
    rw [show ((1135381 / 1000000) : ℝ) = ((1000000 / 1135381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8858_neg : (145466331 / 1000000000) ≤ -Real.log (864619 / 1000000) ∧
    -Real.log (864619 / 1000000) ≤ (36366583 / 250000000) := by
  have h := checkLog_sound (w := (135381 / 1864619)) (n := 12)
    (lo := (145466331 / 1000000000)) (hi := (36366583 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 864619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 864619) = 1/(864619 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8858 : Bounds (-36366583 / 250000000) (-145466331 / 1000000000) (Real.log (864619 / 1000000)) := by
  have h := reflection_log_8858_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8859_neg : (12743057 / 100000000) ≤ -Real.log (500000 / 567953) ∧
    -Real.log (500000 / 567953) ≤ (127430571 / 1000000000) := by
  have h := checkLog_sound (w := (67953 / 1067953)) (n := 12)
    (lo := (12743057 / 100000000)) (hi := (127430571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((567953 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(567953 / 500000) = 1/(500000 / 567953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8859 : Bounds (12743057 / 100000000) (127430571 / 1000000000) (Real.log (567953 / 500000)) := by
  have h := reflection_log_8859_neg
  have he : Real.log (567953 / 500000) = -Real.log (500000 / 567953) := by
    rw [show ((567953 / 500000) : ℝ) = ((500000 / 567953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8860_neg : (146073719 / 1000000000) ≤ -Real.log (432047 / 500000) ∧
    -Real.log (432047 / 500000) ≤ (3651843 / 25000000) := by
  have h := checkLog_sound (w := (67953 / 932047)) (n := 12)
    (lo := (146073719 / 1000000000)) (hi := (3651843 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 432047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 432047) = 1/(432047 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8860 : Bounds (-3651843 / 25000000) (-146073719 / 1000000000) (Real.log (432047 / 500000)) := by
  have h := reflection_log_8860_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8861_neg : (18643149 / 1000000000) ≤ -Real.log (245382389791 / 250000000000) ∧
    -Real.log (245382389791 / 250000000000) ≤ (372863 / 20000000) := by
  have h := checkLog_sound (w := (4617610209 / 495382389791)) (n := 12)
    (lo := (18643149 / 1000000000)) (hi := (372863 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245382389791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245382389791) = 1/(245382389791 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8861 : Bounds (-372863 / 20000000) (-18643149 / 1000000000) (Real.log (245382389791 / 250000000000)) := by
  have h := reflection_log_8861_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8862_neg : (9249027 / 500000000) ≤ -Real.log (981671984839 / 1000000000000) ∧
    -Real.log (981671984839 / 1000000000000) ≤ (3699611 / 200000000) := by
  have h := checkLog_sound (w := (18328015161 / 1981671984839)) (n := 12)
    (lo := (9249027 / 500000000)) (hi := (3699611 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981671984839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981671984839) = 1/(981671984839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8862 : Bounds (-3699611 / 200000000) (-9249027 / 500000000) (Real.log (981671984839 / 1000000000000)) := by
  have h := reflection_log_8862_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8863_neg : (17027163 / 62500000) ≤ -Real.log (100000000000 / 131315758733) ∧
    -Real.log (100000000000 / 131315758733) ≤ (272434609 / 1000000000) := by
  have h := checkLog_sound (w := (31315758733 / 231315758733)) (n := 12)
    (lo := (17027163 / 62500000)) (hi := (272434609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131315758733 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(131315758733 / 100000000000) = 1/(100000000000 / 131315758733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8863 : Bounds (17027163 / 62500000) (272434609 / 1000000000) (Real.log (131315758733 / 100000000000)) := by
  have h := reflection_log_8863_neg
  have he : Real.log (131315758733 / 100000000000) = -Real.log (100000000000 / 131315758733) := by
    rw [show ((131315758733 / 100000000000) : ℝ) = ((100000000000 / 131315758733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8864_neg : (27350429 / 100000000) ≤ -Real.log (500000000000 / 657281499467) ∧
    -Real.log (500000000000 / 657281499467) ≤ (273504291 / 1000000000) := by
  have h := checkLog_sound (w := (157281499467 / 1157281499467)) (n := 12)
    (lo := (27350429 / 100000000)) (hi := (273504291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657281499467 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657281499467 / 500000000000) = 1/(500000000000 / 657281499467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8864 : Bounds (27350429 / 100000000) (273504291 / 1000000000) (Real.log (657281499467 / 500000000000)) := by
  have h := reflection_log_8864_neg
  have he : Real.log (657281499467 / 500000000000) = -Real.log (500000000000 / 657281499467) := by
    rw [show ((657281499467 / 500000000000) : ℝ) = ((500000000000 / 657281499467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8865_neg : (274169197 / 500000000) ≤ -Real.log (50000000000 / 86518771331) ∧
    -Real.log (50000000000 / 86518771331) ≤ (109667679 / 200000000) := by
  have h := checkLog_sound (w := (36518771331 / 136518771331)) (n := 12)
    (lo := (274169197 / 500000000)) (hi := (109667679 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86518771331 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86518771331 / 50000000000) = 1/(50000000000 / 86518771331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8865 : Bounds (274169197 / 500000000) (109667679 / 200000000) (Real.log (86518771331 / 50000000000)) := by
  have h := reflection_log_8865_neg
  have he : Real.log (86518771331 / 50000000000) = -Real.log (50000000000 / 86518771331) := by
    rw [show ((86518771331 / 50000000000) : ℝ) = ((50000000000 / 86518771331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8866_neg : (549415621 / 1000000000) ≤ -Real.log (25000000000 / 43306010929) ∧
    -Real.log (25000000000 / 43306010929) ≤ (274707811 / 500000000) := by
  have h := checkLog_sound (w := (18306010929 / 68306010929)) (n := 12)
    (lo := (549415621 / 1000000000)) (hi := (274707811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43306010929 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43306010929 / 25000000000) = 1/(25000000000 / 43306010929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8866 : Bounds (549415621 / 1000000000) (274707811 / 500000000) (Real.log (43306010929 / 25000000000)) := by
  have h := reflection_log_8866_neg
  have he : Real.log (43306010929 / 25000000000) = -Real.log (25000000000 / 43306010929) := by
    rw [show ((43306010929 / 25000000000) : ℝ) = ((25000000000 / 43306010929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8867_neg : (2378351 / 10000000) ≤ -Real.log (2000 / 2537) ∧
    -Real.log (2000 / 2537) ≤ (237835101 / 1000000000) := by
  have h := checkLog_sound (w := (537 / 4537)) (n := 12)
    (lo := (2378351 / 10000000)) (hi := (237835101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2537 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2537 / 2000) = 1/(2000 / 2537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8867 : Bounds (2378351 / 10000000) (237835101 / 1000000000) (Real.log (2537 / 2000)) := by
  have h := reflection_log_8867_neg
  have he : Real.log (2537 / 2000) = -Real.log (2000 / 2537) := by
    rw [show ((2537 / 2000) : ℝ) = ((2000 / 2537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8868_neg : (156329029 / 500000000) ≤ -Real.log (1463 / 2000) ∧
    -Real.log (1463 / 2000) ≤ (312658059 / 1000000000) := by
  have h := checkLog_sound (w := (537 / 3463)) (n := 12)
    (lo := (156329029 / 500000000)) (hi := (312658059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1463) = 1/(1463 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8868 : Bounds (-312658059 / 1000000000) (-156329029 / 500000000) (Real.log (1463 / 2000)) := by
  have h := reflection_log_8868_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8869_neg : (268463 / 1000000000) ≤ -Real.log (2000000 / 2000537) ∧
    -Real.log (2000000 / 2000537) ≤ (16779 / 62500000) := by
  have h := checkLog_sound (w := (537 / 4000537)) (n := 12)
    (lo := (268463 / 1000000000)) (hi := (16779 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000537 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000537 / 2000000) = 1/(2000000 / 2000537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8869 : Bounds (268463 / 1000000000) (16779 / 62500000) (Real.log (2000537 / 2000000)) := by
  have h := reflection_log_8869_neg
  have he : Real.log (2000537 / 2000000) = -Real.log (2000000 / 2000537) := by
    rw [show ((2000537 / 2000000) : ℝ) = ((2000000 / 2000537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8870_neg : (33567 / 125000000) ≤ -Real.log (1999463 / 2000000) ∧
    -Real.log (1999463 / 2000000) ≤ (268537 / 1000000000) := by
  have h := checkLog_sound (w := (537 / 3999463)) (n := 12)
    (lo := (33567 / 125000000)) (hi := (268537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999463) = 1/(1999463 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8870 : Bounds (-268537 / 1000000000) (-33567 / 125000000) (Real.log (1999463 / 2000000)) := by
  have h := reflection_log_8870_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8871_neg : (7949773 / 62500000) ≤ -Real.log (25000 / 28391) ∧
    -Real.log (25000 / 28391) ≤ (127196369 / 1000000000) := by
  have h := checkLog_sound (w := (3391 / 53391)) (n := 12)
    (lo := (7949773 / 62500000)) (hi := (127196369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28391 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28391 / 25000) = 1/(25000 / 28391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8871 : Bounds (7949773 / 62500000) (127196369 / 1000000000) (Real.log (28391 / 25000)) := by
  have h := reflection_log_8871_neg
  have he : Real.log (28391 / 25000) = -Real.log (25000 / 28391) := by
    rw [show ((28391 / 25000) : ℝ) = ((25000 / 28391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8872_neg : (14576593 / 100000000) ≤ -Real.log (21609 / 25000) ∧
    -Real.log (21609 / 25000) ≤ (145765931 / 1000000000) := by
  have h := checkLog_sound (w := (3391 / 46609)) (n := 12)
    (lo := (14576593 / 100000000)) (hi := (145765931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 21609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 21609) = 1/(21609 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8872 : Bounds (-145765931 / 1000000000) (-14576593 / 100000000) (Real.log (21609 / 25000)) := by
  have h := reflection_log_8872_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8873_neg : (31914859 / 250000000) ≤ -Real.log (500000 / 568083) ∧
    -Real.log (500000 / 568083) ≤ (127659437 / 1000000000) := by
  have h := checkLog_sound (w := (68083 / 1068083)) (n := 12)
    (lo := (31914859 / 250000000)) (hi := (127659437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((568083 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(568083 / 500000) = 1/(500000 / 568083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8873 : Bounds (31914859 / 250000000) (127659437 / 1000000000) (Real.log (568083 / 500000)) := by
  have h := reflection_log_8873_neg
  have he : Real.log (568083 / 500000) = -Real.log (500000 / 568083) := by
    rw [show ((568083 / 500000) : ℝ) = ((500000 / 568083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8874_neg : (73187329 / 500000000) ≤ -Real.log (431917 / 500000) ∧
    -Real.log (431917 / 500000) ≤ (146374659 / 1000000000) := by
  have h := checkLog_sound (w := (68083 / 931917)) (n := 12)
    (lo := (73187329 / 500000000)) (hi := (146374659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 431917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 431917) = 1/(431917 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8874 : Bounds (-146374659 / 1000000000) (-73187329 / 500000000) (Real.log (431917 / 500000)) := by
  have h := reflection_log_8874_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8875_neg : (18715221 / 1000000000) ≤ -Real.log (245364705111 / 250000000000) ∧
    -Real.log (245364705111 / 250000000000) ≤ (9357611 / 500000000) := by
  have h := checkLog_sound (w := (4635294889 / 495364705111)) (n := 12)
    (lo := (18715221 / 1000000000)) (hi := (9357611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245364705111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245364705111) = 1/(245364705111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8875 : Bounds (-9357611 / 500000000) (-18715221 / 1000000000) (Real.log (245364705111 / 250000000000)) := by
  have h := reflection_log_8875_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8876_neg : (18569561 / 1000000000) ≤ -Real.log (613501119 / 625000000) ∧
    -Real.log (613501119 / 625000000) ≤ (9284781 / 500000000) := by
  have h := checkLog_sound (w := (11498881 / 1238501119)) (n := 12)
    (lo := (18569561 / 1000000000)) (hi := (9284781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 613501119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 613501119) = 1/(613501119 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8876 : Bounds (-9284781 / 500000000) (-18569561 / 1000000000) (Real.log (613501119 / 625000000)) := by
  have h := reflection_log_8876_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8877_neg : (136481149 / 500000000) ≤ -Real.log (62500000000 / 82115669397) ∧
    -Real.log (62500000000 / 82115669397) ≤ (272962299 / 1000000000) := by
  have h := checkLog_sound (w := (19615669397 / 144615669397)) (n := 12)
    (lo := (136481149 / 500000000)) (hi := (272962299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82115669397 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82115669397 / 62500000000) = 1/(62500000000 / 82115669397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8877 : Bounds (136481149 / 500000000) (272962299 / 1000000000) (Real.log (82115669397 / 62500000000)) := by
  have h := reflection_log_8877_neg
  have he : Real.log (82115669397 / 62500000000) = -Real.log (62500000000 / 82115669397) := by
    rw [show ((82115669397 / 62500000000) : ℝ) = ((62500000000 / 82115669397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8878_neg : (137017047 / 500000000) ≤ -Real.log (500000000000 / 657629822397) ∧
    -Real.log (500000000000 / 657629822397) ≤ (54806819 / 200000000) := by
  have h := checkLog_sound (w := (157629822397 / 1157629822397)) (n := 12)
    (lo := (137017047 / 500000000)) (hi := (54806819 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657629822397 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657629822397 / 500000000000) = 1/(500000000000 / 657629822397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8878 : Bounds (137017047 / 500000000) (54806819 / 200000000) (Real.log (657629822397 / 500000000000)) := by
  have h := reflection_log_8878_neg
  have he : Real.log (657629822397 / 500000000000) = -Real.log (500000000000 / 657629822397) := by
    rw [show ((657629822397 / 500000000000) : ℝ) = ((500000000000 / 657629822397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8879_neg : (549415621 / 1000000000) ≤ -Real.log (500000000000 / 866120218579) ∧
    -Real.log (500000000000 / 866120218579) ≤ (274707811 / 500000000) := by
  have h := checkLog_sound (w := (366120218579 / 1366120218579)) (n := 12)
    (lo := (549415621 / 1000000000)) (hi := (274707811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((866120218579 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(866120218579 / 500000000000) = 1/(500000000000 / 866120218579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8879 : Bounds (549415621 / 1000000000) (274707811 / 500000000) (Real.log (866120218579 / 500000000000)) := by
  have h := reflection_log_8879_neg
  have he : Real.log (866120218579 / 500000000000) = -Real.log (500000000000 / 866120218579) := by
    rw [show ((866120218579 / 500000000000) : ℝ) = ((500000000000 / 866120218579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8880_neg : (275246579 / 500000000) ≤ -Real.log (500000000000 / 867053998633) ∧
    -Real.log (500000000000 / 867053998633) ≤ (550493159 / 1000000000) := by
  have h := checkLog_sound (w := (367053998633 / 1367053998633)) (n := 12)
    (lo := (275246579 / 500000000)) (hi := (550493159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((867053998633 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(867053998633 / 500000000000) = 1/(500000000000 / 867053998633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8880 : Bounds (275246579 / 500000000) (550493159 / 1000000000) (Real.log (867053998633 / 500000000000)) := by
  have h := reflection_log_8880_neg
  have he : Real.log (867053998633 / 500000000000) = -Real.log (500000000000 / 867053998633) := by
    rw [show ((867053998633 / 500000000000) : ℝ) = ((500000000000 / 867053998633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8881_neg : (59557297 / 250000000) ≤ -Real.log (1000 / 1269) ∧
    -Real.log (1000 / 1269) ≤ (238229189 / 1000000000) := by
  have h := checkLog_sound (w := (269 / 2269)) (n := 12)
    (lo := (59557297 / 250000000)) (hi := (238229189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1269 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1269 / 1000) = 1/(1000 / 1269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8881 : Bounds (59557297 / 250000000) (238229189 / 1000000000) (Real.log (1269 / 1000)) := by
  have h := reflection_log_8881_neg
  have he : Real.log (1269 / 1000) = -Real.log (1000 / 1269) := by
    rw [show ((1269 / 1000) : ℝ) = ((1000 / 1269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8882_neg : (313341819 / 1000000000) ≤ -Real.log (731 / 1000) ∧
    -Real.log (731 / 1000) ≤ (15667091 / 50000000) := by
  have h := checkLog_sound (w := (269 / 1731)) (n := 12)
    (lo := (313341819 / 1000000000)) (hi := (15667091 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 731) = 1/(731 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8882 : Bounds (-15667091 / 50000000) (-313341819 / 1000000000) (Real.log (731 / 1000)) := by
  have h := reflection_log_8882_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8883_neg : (268963 / 1000000000) ≤ -Real.log (1000000 / 1000269) ∧
    -Real.log (1000000 / 1000269) ≤ (67241 / 250000000) := by
  have h := checkLog_sound (w := (269 / 2000269)) (n := 12)
    (lo := (268963 / 1000000000)) (hi := (67241 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000269 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000269 / 1000000) = 1/(1000000 / 1000269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8883 : Bounds (268963 / 1000000000) (67241 / 250000000) (Real.log (1000269 / 1000000)) := by
  have h := reflection_log_8883_neg
  have he : Real.log (1000269 / 1000000) = -Real.log (1000000 / 1000269) := by
    rw [show ((1000269 / 1000000) : ℝ) = ((1000000 / 1000269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8884_neg : (67259 / 250000000) ≤ -Real.log (999731 / 1000000) ∧
    -Real.log (999731 / 1000000) ≤ (269037 / 1000000000) := by
  have h := checkLog_sound (w := (269 / 1999731)) (n := 12)
    (lo := (67259 / 250000000)) (hi := (269037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999731) = 1/(999731 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8884 : Bounds (-269037 / 1000000000) (-67259 / 250000000) (Real.log (999731 / 1000000)) := by
  have h := reflection_log_8884_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8885_neg : (15928161 / 125000000) ≤ -Real.log (10000 / 11359) ∧
    -Real.log (10000 / 11359) ≤ (127425289 / 1000000000) := by
  have h := checkLog_sound (w := (1359 / 21359)) (n := 12)
    (lo := (15928161 / 125000000)) (hi := (127425289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11359 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11359 / 10000) = 1/(10000 / 11359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8885 : Bounds (15928161 / 125000000) (127425289 / 1000000000) (Real.log (11359 / 10000)) := by
  have h := reflection_log_8885_neg
  have he : Real.log (11359 / 10000) = -Real.log (10000 / 11359) := by
    rw [show ((11359 / 10000) : ℝ) = ((10000 / 11359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8886_neg : (18258347 / 125000000) ≤ -Real.log (8641 / 10000) ∧
    -Real.log (8641 / 10000) ≤ (146066777 / 1000000000) := by
  have h := checkLog_sound (w := (1359 / 18641)) (n := 12)
    (lo := (18258347 / 125000000)) (hi := (146066777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8641) = 1/(8641 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8886 : Bounds (-146066777 / 1000000000) (-18258347 / 125000000) (Real.log (8641 / 10000)) := by
  have h := reflection_log_8886_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8887_neg : (127889129 / 1000000000) ≤ -Real.log (1000000 / 1136427) ∧
    -Real.log (1000000 / 1136427) ≤ (12788913 / 100000000) := by
  have h := checkLog_sound (w := (136427 / 2136427)) (n := 12)
    (lo := (127889129 / 1000000000)) (hi := (12788913 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1136427 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1136427 / 1000000) = 1/(1000000 / 1136427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8887 : Bounds (127889129 / 1000000000) (12788913 / 100000000) (Real.log (1136427 / 1000000)) := by
  have h := reflection_log_8887_neg
  have he : Real.log (1136427 / 1000000) = -Real.log (1000000 / 1136427) := by
    rw [show ((1136427 / 1000000) : ℝ) = ((1000000 / 1136427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8888_neg : (29335369 / 200000000) ≤ -Real.log (863573 / 1000000) ∧
    -Real.log (863573 / 1000000) ≤ (73338423 / 500000000) := by
  have h := checkLog_sound (w := (136427 / 1863573)) (n := 12)
    (lo := (29335369 / 200000000)) (hi := (73338423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 863573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 863573) = 1/(863573 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8888 : Bounds (-73338423 / 500000000) (-29335369 / 200000000) (Real.log (863573 / 1000000)) := by
  have h := reflection_log_8888_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8889_neg : (3757543 / 200000000) ≤ -Real.log (981387673671 / 1000000000000) ∧
    -Real.log (981387673671 / 1000000000000) ≤ (4696929 / 250000000) := by
  have h := checkLog_sound (w := (18612326329 / 1981387673671)) (n := 12)
    (lo := (3757543 / 200000000)) (hi := (4696929 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981387673671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981387673671) = 1/(981387673671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8889 : Bounds (-4696929 / 250000000) (-3757543 / 200000000) (Real.log (981387673671 / 1000000000000)) := by
  have h := reflection_log_8889_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8890_neg : (18641487 / 1000000000) ≤ -Real.log (98153119 / 100000000) ∧
    -Real.log (98153119 / 100000000) ≤ (1165093 / 62500000) := by
  have h := checkLog_sound (w := (1846881 / 198153119)) (n := 12)
    (lo := (18641487 / 1000000000)) (hi := (1165093 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000000 / 98153119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000000 / 98153119) = 1/(98153119 / 100000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8890 : Bounds (-1165093 / 62500000) (-18641487 / 1000000000) (Real.log (98153119 / 100000000)) := by
  have h := reflection_log_8890_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8891_neg : (8546627 / 31250000) ≤ -Real.log (500000000000 / 657273463719) ∧
    -Real.log (500000000000 / 657273463719) ≤ (54698413 / 200000000) := by
  have h := checkLog_sound (w := (157273463719 / 1157273463719)) (n := 12)
    (lo := (8546627 / 31250000)) (hi := (54698413 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657273463719 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657273463719 / 500000000000) = 1/(500000000000 / 657273463719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8891 : Bounds (8546627 / 31250000) (54698413 / 200000000) (Real.log (657273463719 / 500000000000)) := by
  have h := reflection_log_8891_neg
  have he : Real.log (657273463719 / 500000000000) = -Real.log (500000000000 / 657273463719) := by
    rw [show ((657273463719 / 500000000000) : ℝ) = ((500000000000 / 657273463719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8892_neg : (10982639 / 40000000) ≤ -Real.log (100000000000 / 131595939197) ∧
    -Real.log (100000000000 / 131595939197) ≤ (34320747 / 125000000) := by
  have h := checkLog_sound (w := (31595939197 / 231595939197)) (n := 12)
    (lo := (10982639 / 40000000)) (hi := (34320747 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131595939197 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(131595939197 / 100000000000) = 1/(100000000000 / 131595939197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8892 : Bounds (10982639 / 40000000) (34320747 / 125000000) (Real.log (131595939197 / 100000000000)) := by
  have h := reflection_log_8892_neg
  have he : Real.log (131595939197 / 100000000000) = -Real.log (100000000000 / 131595939197) := by
    rw [show ((131595939197 / 100000000000) : ℝ) = ((100000000000 / 131595939197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8893_neg : (275246579 / 500000000) ≤ -Real.log (62500000000 / 108381749829) ∧
    -Real.log (62500000000 / 108381749829) ≤ (550493159 / 1000000000) := by
  have h := checkLog_sound (w := (45881749829 / 170881749829)) (n := 12)
    (lo := (275246579 / 500000000)) (hi := (550493159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108381749829 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108381749829 / 62500000000) = 1/(62500000000 / 108381749829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8893 : Bounds (275246579 / 500000000) (550493159 / 1000000000) (Real.log (108381749829 / 62500000000)) := by
  have h := reflection_log_8893_neg
  have he : Real.log (108381749829 / 62500000000) = -Real.log (62500000000 / 108381749829) := by
    rw [show ((108381749829 / 62500000000) : ℝ) = ((62500000000 / 108381749829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8894_neg : (551571007 / 1000000000) ≤ -Real.log (62500000000 / 108498632011) ∧
    -Real.log (62500000000 / 108498632011) ≤ (8618297 / 15625000) := by
  have h := checkLog_sound (w := (45998632011 / 170998632011)) (n := 12)
    (lo := (551571007 / 1000000000)) (hi := (8618297 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108498632011 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108498632011 / 62500000000) = 1/(62500000000 / 108498632011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8894 : Bounds (551571007 / 1000000000) (8618297 / 15625000) (Real.log (108498632011 / 62500000000)) := by
  have h := reflection_log_8894_neg
  have he : Real.log (108498632011 / 62500000000) = -Real.log (62500000000 / 108498632011) := by
    rw [show ((108498632011 / 62500000000) : ℝ) = ((62500000000 / 108498632011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8895_neg : (119311561 / 500000000) ≤ -Real.log (2000 / 2539) ∧
    -Real.log (2000 / 2539) ≤ (238623123 / 1000000000) := by
  have h := checkLog_sound (w := (539 / 4539)) (n := 12)
    (lo := (119311561 / 500000000)) (hi := (238623123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2539 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2539 / 2000) = 1/(2000 / 2539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8895 : Bounds (119311561 / 500000000) (238623123 / 1000000000) (Real.log (2539 / 2000)) := by
  have h := reflection_log_8895_neg
  have he : Real.log (2539 / 2000) = -Real.log (2000 / 2539) := by
    rw [show ((2539 / 2000) : ℝ) = ((2000 / 2539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0139 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8896_neg : (314026047 / 1000000000) ≤ -Real.log (1461 / 2000) ∧
    -Real.log (1461 / 2000) ≤ (4906657 / 15625000) := by
  have h := checkLog_sound (w := (539 / 3461)) (n := 12)
    (lo := (314026047 / 1000000000)) (hi := (4906657 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1461) = 1/(1461 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8896 : Bounds (-4906657 / 15625000) (-314026047 / 1000000000) (Real.log (1461 / 2000)) := by
  have h := reflection_log_8896_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8897_neg : (269463 / 1000000000) ≤ -Real.log (2000000 / 2000539) ∧
    -Real.log (2000000 / 2000539) ≤ (33683 / 125000000) := by
  have h := checkLog_sound (w := (539 / 4000539)) (n := 12)
    (lo := (269463 / 1000000000)) (hi := (33683 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000539 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000539 / 2000000) = 1/(2000000 / 2000539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8897 : Bounds (269463 / 1000000000) (33683 / 125000000) (Real.log (2000539 / 2000000)) := by
  have h := reflection_log_8897_neg
  have he : Real.log (2000539 / 2000000) = -Real.log (2000000 / 2000539) := by
    rw [show ((2000539 / 2000000) : ℝ) = ((2000000 / 2000539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8898_neg : (8423 / 31250000) ≤ -Real.log (1999461 / 2000000) ∧
    -Real.log (1999461 / 2000000) ≤ (269537 / 1000000000) := by
  have h := checkLog_sound (w := (539 / 3999461)) (n := 12)
    (lo := (8423 / 31250000)) (hi := (269537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999461) = 1/(1999461 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8898 : Bounds (-269537 / 1000000000) (-8423 / 31250000) (Real.log (1999461 / 2000000)) := by
  have h := reflection_log_8898_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8899_neg : (25530831 / 200000000) ≤ -Real.log (6250 / 7101) ∧
    -Real.log (6250 / 7101) ≤ (31913539 / 250000000) := by
  have h := checkLog_sound (w := (851 / 13351)) (n := 12)
    (lo := (25530831 / 200000000)) (hi := (31913539 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7101 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7101 / 6250) = 1/(6250 / 7101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8899 : Bounds (25530831 / 200000000) (31913539 / 250000000) (Real.log (7101 / 6250)) := by
  have h := reflection_log_8899_neg
  have he : Real.log (7101 / 6250) = -Real.log (6250 / 7101) := by
    rw [show ((7101 / 6250) : ℝ) = ((6250 / 7101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8900_neg : (4573991 / 31250000) ≤ -Real.log (5399 / 6250) ∧
    -Real.log (5399 / 6250) ≤ (146367713 / 1000000000) := by
  have h := checkLog_sound (w := (851 / 11649)) (n := 12)
    (lo := (4573991 / 31250000)) (hi := (146367713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 5399) = 1/(5399 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8900 : Bounds (-146367713 / 1000000000) (-4573991 / 31250000) (Real.log (5399 / 6250)) := by
  have h := reflection_log_8900_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8901_neg : (128117891 / 1000000000) ≤ -Real.log (1000000 / 1136687) ∧
    -Real.log (1000000 / 1136687) ≤ (32029473 / 250000000) := by
  have h := checkLog_sound (w := (136687 / 2136687)) (n := 12)
    (lo := (128117891 / 1000000000)) (hi := (32029473 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1136687 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1136687 / 1000000) = 1/(1000000 / 1136687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8901 : Bounds (128117891 / 1000000000) (32029473 / 250000000) (Real.log (1136687 / 1000000)) := by
  have h := reflection_log_8901_neg
  have he : Real.log (1136687 / 1000000) = -Real.log (1000000 / 1136687) := by
    rw [show ((1136687 / 1000000) : ℝ) = ((1000000 / 1136687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8902_neg : (29395593 / 200000000) ≤ -Real.log (863313 / 1000000) ∧
    -Real.log (863313 / 1000000) ≤ (73488983 / 500000000) := by
  have h := checkLog_sound (w := (136687 / 1863313)) (n := 12)
    (lo := (29395593 / 200000000)) (hi := (73488983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 863313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 863313) = 1/(863313 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8902 : Bounds (-73488983 / 500000000) (-29395593 / 200000000) (Real.log (863313 / 1000000)) := by
  have h := reflection_log_8902_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8903_neg : (9430037 / 500000000) ≤ -Real.log (981316664031 / 1000000000000) ∧
    -Real.log (981316664031 / 1000000000000) ≤ (754403 / 40000000) := by
  have h := checkLog_sound (w := (18683335969 / 1981316664031)) (n := 12)
    (lo := (9430037 / 500000000)) (hi := (754403 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981316664031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981316664031) = 1/(981316664031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8903 : Bounds (-754403 / 40000000) (-9430037 / 500000000) (Real.log (981316664031 / 1000000000000)) := by
  have h := reflection_log_8903_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8904_neg : (18713557 / 1000000000) ≤ -Real.log (38338299 / 39062500) ∧
    -Real.log (38338299 / 39062500) ≤ (9356779 / 500000000) := by
  have h := checkLog_sound (w := (724201 / 77400799)) (n := 12)
    (lo := (18713557 / 1000000000)) (hi := (9356779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39062500 / 38338299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39062500 / 38338299) = 1/(38338299 / 39062500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8904 : Bounds (-9356779 / 500000000) (-18713557 / 1000000000) (Real.log (38338299 / 39062500)) := by
  have h := reflection_log_8904_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8905_neg : (274021867 / 1000000000) ≤ -Real.log (500000000000 / 657621781811) ∧
    -Real.log (500000000000 / 657621781811) ≤ (68505467 / 250000000) := by
  have h := checkLog_sound (w := (157621781811 / 1157621781811)) (n := 12)
    (lo := (274021867 / 1000000000)) (hi := (68505467 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657621781811 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657621781811 / 500000000000) = 1/(500000000000 / 657621781811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8905 : Bounds (274021867 / 1000000000) (68505467 / 250000000) (Real.log (657621781811 / 500000000000)) := by
  have h := reflection_log_8905_neg
  have he : Real.log (657621781811 / 500000000000) = -Real.log (500000000000 / 657621781811) := by
    rw [show ((657621781811 / 500000000000) : ℝ) = ((500000000000 / 657621781811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8906_neg : (17193491 / 62500000) ≤ -Real.log (125000000000 / 164582109849) ∧
    -Real.log (125000000000 / 164582109849) ≤ (275095857 / 1000000000) := by
  have h := checkLog_sound (w := (39582109849 / 289582109849)) (n := 12)
    (lo := (17193491 / 62500000)) (hi := (275095857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164582109849 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164582109849 / 125000000000) = 1/(125000000000 / 164582109849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8906 : Bounds (17193491 / 62500000) (275095857 / 1000000000) (Real.log (164582109849 / 125000000000)) := by
  have h := reflection_log_8906_neg
  have he : Real.log (164582109849 / 125000000000) = -Real.log (125000000000 / 164582109849) := by
    rw [show ((164582109849 / 125000000000) : ℝ) = ((125000000000 / 164582109849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8907_neg : (551571007 / 1000000000) ≤ -Real.log (500000000000 / 867989056087) ∧
    -Real.log (500000000000 / 867989056087) ≤ (8618297 / 15625000) := by
  have h := checkLog_sound (w := (367989056087 / 1367989056087)) (n := 12)
    (lo := (551571007 / 1000000000)) (hi := (8618297 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((867989056087 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(867989056087 / 500000000000) = 1/(500000000000 / 867989056087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8907 : Bounds (551571007 / 1000000000) (8618297 / 15625000) (Real.log (867989056087 / 500000000000)) := by
  have h := reflection_log_8907_neg
  have he : Real.log (867989056087 / 500000000000) = -Real.log (500000000000 / 867989056087) := by
    rw [show ((867989056087 / 500000000000) : ℝ) = ((500000000000 / 867989056087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8908_neg : (552649169 / 1000000000) ≤ -Real.log (500000000000 / 868925393567) ∧
    -Real.log (500000000000 / 868925393567) ≤ (55264917 / 100000000) := by
  have h := checkLog_sound (w := (368925393567 / 1368925393567)) (n := 12)
    (lo := (552649169 / 1000000000)) (hi := (55264917 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((868925393567 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(868925393567 / 500000000000) = 1/(500000000000 / 868925393567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8908 : Bounds (552649169 / 1000000000) (55264917 / 100000000) (Real.log (868925393567 / 500000000000)) := by
  have h := reflection_log_8908_neg
  have he : Real.log (868925393567 / 500000000000) = -Real.log (500000000000 / 868925393567) := by
    rw [show ((868925393567 / 500000000000) : ℝ) = ((500000000000 / 868925393567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8909_neg : (2390169 / 10000000) ≤ -Real.log (100 / 127) ∧
    -Real.log (100 / 127) ≤ (239016901 / 1000000000) := by
  have h := checkLog_sound (w := (27 / 227)) (n := 12)
    (lo := (2390169 / 10000000)) (hi := (239016901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(127 / 100) = 1/(100 / 127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8909 : Bounds (2390169 / 10000000) (239016901 / 1000000000) (Real.log (127 / 100)) := by
  have h := reflection_log_8909_neg
  have he : Real.log (127 / 100) = -Real.log (100 / 127) := by
    rw [show ((127 / 100) : ℝ) = ((100 / 127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8910_neg : (39338843 / 125000000) ≤ -Real.log (73 / 100) ∧
    -Real.log (73 / 100) ≤ (62942149 / 200000000) := by
  have h := checkLog_sound (w := (27 / 173)) (n := 12)
    (lo := (39338843 / 125000000)) (hi := (62942149 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 73) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 73) = 1/(73 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8910 : Bounds (-62942149 / 200000000) (-39338843 / 125000000) (Real.log (73 / 100)) := by
  have h := reflection_log_8910_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8911_neg : (269963 / 1000000000) ≤ -Real.log (100000 / 100027) ∧
    -Real.log (100000 / 100027) ≤ (67491 / 250000000) := by
  have h := checkLog_sound (w := (27 / 200027)) (n := 12)
    (lo := (269963 / 1000000000)) (hi := (67491 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100027 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100027 / 100000) = 1/(100000 / 100027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8911 : Bounds (269963 / 1000000000) (67491 / 250000000) (Real.log (100027 / 100000)) := by
  have h := reflection_log_8911_neg
  have he : Real.log (100027 / 100000) = -Real.log (100000 / 100027) := by
    rw [show ((100027 / 100000) : ℝ) = ((100000 / 100027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8912_neg : (67509 / 250000000) ≤ -Real.log (99973 / 100000) ∧
    -Real.log (99973 / 100000) ≤ (270037 / 1000000000) := by
  have h := checkLog_sound (w := (27 / 199973)) (n := 12)
    (lo := (67509 / 250000000)) (hi := (270037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99973) = 1/(99973 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8912 : Bounds (-270037 / 1000000000) (-67509 / 250000000) (Real.log (99973 / 100000)) := by
  have h := reflection_log_8912_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8913_neg : (12788297 / 100000000) ≤ -Real.log (50000 / 56821) ∧
    -Real.log (50000 / 56821) ≤ (127882971 / 1000000000) := by
  have h := checkLog_sound (w := (6821 / 106821)) (n := 12)
    (lo := (12788297 / 100000000)) (hi := (127882971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56821 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56821 / 50000) = 1/(50000 / 56821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8913 : Bounds (12788297 / 100000000) (127882971 / 1000000000) (Real.log (56821 / 50000)) := by
  have h := reflection_log_8913_neg
  have he : Real.log (56821 / 50000) = -Real.log (50000 / 56821) := by
    rw [show ((56821 / 50000) : ℝ) = ((50000 / 56821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8914_neg : (146668739 / 1000000000) ≤ -Real.log (43179 / 50000) ∧
    -Real.log (43179 / 50000) ≤ (7333437 / 50000000) := by
  have h := checkLog_sound (w := (6821 / 93179)) (n := 12)
    (lo := (146668739 / 1000000000)) (hi := (7333437 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 43179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 43179) = 1/(43179 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8914 : Bounds (-7333437 / 50000000) (-146668739 / 1000000000) (Real.log (43179 / 50000)) := by
  have h := reflection_log_8914_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8915_neg : (128346599 / 1000000000) ≤ -Real.log (1000000 / 1136947) ∧
    -Real.log (1000000 / 1136947) ≤ (641733 / 5000000) := by
  have h := checkLog_sound (w := (136947 / 2136947)) (n := 12)
    (lo := (128346599 / 1000000000)) (hi := (641733 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1136947 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1136947 / 1000000) = 1/(1000000 / 1136947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8915 : Bounds (128346599 / 1000000000) (641733 / 5000000) (Real.log (1136947 / 1000000)) := by
  have h := reflection_log_8915_neg
  have he : Real.log (1136947 / 1000000) = -Real.log (1000000 / 1136947) := by
    rw [show ((1136947 / 1000000) : ℝ) = ((1000000 / 1136947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8916_neg : (18409897 / 125000000) ≤ -Real.log (863053 / 1000000) ∧
    -Real.log (863053 / 1000000) ≤ (147279177 / 1000000000) := by
  have h := checkLog_sound (w := (136947 / 1863053)) (n := 12)
    (lo := (18409897 / 125000000)) (hi := (147279177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 863053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 863053) = 1/(863053 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8916 : Bounds (-147279177 / 1000000000) (-18409897 / 125000000) (Real.log (863053 / 1000000)) := by
  have h := reflection_log_8916_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8917_neg : (591643 / 31250000) ≤ -Real.log (981245519191 / 1000000000000) ∧
    -Real.log (981245519191 / 1000000000000) ≤ (18932577 / 1000000000) := by
  have h := checkLog_sound (w := (18754480809 / 1981245519191)) (n := 12)
    (lo := (591643 / 31250000)) (hi := (18932577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981245519191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981245519191) = 1/(981245519191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8917 : Bounds (-18932577 / 1000000000) (-591643 / 31250000) (Real.log (981245519191 / 1000000000000)) := by
  have h := reflection_log_8917_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8918_neg : (18785769 / 1000000000) ≤ -Real.log (2453473959 / 2500000000) ∧
    -Real.log (2453473959 / 2500000000) ≤ (1878577 / 100000000) := by
  have h := checkLog_sound (w := (46526041 / 4953473959)) (n := 12)
    (lo := (18785769 / 1000000000)) (hi := (1878577 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2453473959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2453473959) = 1/(2453473959 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8918 : Bounds (-1878577 / 100000000) (-18785769 / 1000000000) (Real.log (2453473959 / 2500000000)) := by
  have h := reflection_log_8918_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8919_neg : (274551709 / 1000000000) ≤ -Real.log (500000000000 / 657970309641) ∧
    -Real.log (500000000000 / 657970309641) ≤ (27455171 / 100000000) := by
  have h := checkLog_sound (w := (157970309641 / 1157970309641)) (n := 12)
    (lo := (274551709 / 1000000000)) (hi := (27455171 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657970309641 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657970309641 / 500000000000) = 1/(500000000000 / 657970309641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8919 : Bounds (274551709 / 1000000000) (27455171 / 100000000) (Real.log (657970309641 / 500000000000)) := by
  have h := reflection_log_8919_neg
  have he : Real.log (657970309641 / 500000000000) = -Real.log (500000000000 / 657970309641) := by
    rw [show ((657970309641 / 500000000000) : ℝ) = ((500000000000 / 657970309641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8920_neg : (11025031 / 40000000) ≤ -Real.log (50000000000 / 65867739293) ∧
    -Real.log (50000000000 / 65867739293) ≤ (17226611 / 62500000) := by
  have h := checkLog_sound (w := (15867739293 / 115867739293)) (n := 12)
    (lo := (11025031 / 40000000)) (hi := (17226611 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65867739293 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(65867739293 / 50000000000) = 1/(50000000000 / 65867739293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8920 : Bounds (11025031 / 40000000) (17226611 / 62500000) (Real.log (65867739293 / 50000000000)) := by
  have h := reflection_log_8920_neg
  have he : Real.log (65867739293 / 50000000000) = -Real.log (50000000000 / 65867739293) := by
    rw [show ((65867739293 / 50000000000) : ℝ) = ((50000000000 / 65867739293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8921_neg : (552649169 / 1000000000) ≤ -Real.log (250000000000 / 434462696783) ∧
    -Real.log (250000000000 / 434462696783) ≤ (55264917 / 100000000) := by
  have h := checkLog_sound (w := (184462696783 / 684462696783)) (n := 12)
    (lo := (552649169 / 1000000000)) (hi := (55264917 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((434462696783 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(434462696783 / 250000000000) = 1/(250000000000 / 434462696783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8921 : Bounds (552649169 / 1000000000) (55264917 / 100000000) (Real.log (434462696783 / 250000000000)) := by
  have h := reflection_log_8921_neg
  have he : Real.log (434462696783 / 250000000000) = -Real.log (250000000000 / 434462696783) := by
    rw [show ((434462696783 / 250000000000) : ℝ) = ((250000000000 / 434462696783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8922_neg : (110745529 / 200000000) ≤ -Real.log (500000000000 / 869863013699) ∧
    -Real.log (500000000000 / 869863013699) ≤ (276863823 / 500000000) := by
  have h := checkLog_sound (w := (369863013699 / 1369863013699)) (n := 12)
    (lo := (110745529 / 200000000)) (hi := (276863823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((869863013699 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(869863013699 / 500000000000) = 1/(500000000000 / 869863013699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8922 : Bounds (110745529 / 200000000) (276863823 / 500000000) (Real.log (869863013699 / 500000000000)) := by
  have h := reflection_log_8922_neg
  have he : Real.log (869863013699 / 500000000000) = -Real.log (500000000000 / 869863013699) := by
    rw [show ((869863013699 / 500000000000) : ℝ) = ((500000000000 / 869863013699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8923_neg : (239410523 / 1000000000) ≤ -Real.log (2000 / 2541) ∧
    -Real.log (2000 / 2541) ≤ (59852631 / 250000000) := by
  have h := checkLog_sound (w := (541 / 4541)) (n := 12)
    (lo := (239410523 / 1000000000)) (hi := (59852631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2541 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2541 / 2000) = 1/(2000 / 2541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8923 : Bounds (239410523 / 1000000000) (59852631 / 250000000) (Real.log (2541 / 2000)) := by
  have h := reflection_log_8923_neg
  have he : Real.log (2541 / 2000) = -Real.log (2000 / 2541) := by
    rw [show ((2541 / 2000) : ℝ) = ((2000 / 2541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8924_neg : (315395911 / 1000000000) ≤ -Real.log (1459 / 2000) ∧
    -Real.log (1459 / 2000) ≤ (39424489 / 125000000) := by
  have h := checkLog_sound (w := (541 / 3459)) (n := 12)
    (lo := (315395911 / 1000000000)) (hi := (39424489 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1459) = 1/(1459 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8924 : Bounds (-39424489 / 125000000) (-315395911 / 1000000000) (Real.log (1459 / 2000)) := by
  have h := reflection_log_8924_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8925_neg : (270463 / 1000000000) ≤ -Real.log (2000000 / 2000541) ∧
    -Real.log (2000000 / 2000541) ≤ (2113 / 7812500) := by
  have h := checkLog_sound (w := (541 / 4000541)) (n := 12)
    (lo := (270463 / 1000000000)) (hi := (2113 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000541 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000541 / 2000000) = 1/(2000000 / 2000541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8925 : Bounds (270463 / 1000000000) (2113 / 7812500) (Real.log (2000541 / 2000000)) := by
  have h := reflection_log_8925_neg
  have he : Real.log (2000541 / 2000000) = -Real.log (2000000 / 2000541) := by
    rw [show ((2000541 / 2000000) : ℝ) = ((2000000 / 2000541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8926_neg : (33817 / 125000000) ≤ -Real.log (1999459 / 2000000) ∧
    -Real.log (1999459 / 2000000) ≤ (270537 / 1000000000) := by
  have h := checkLog_sound (w := (541 / 3999459)) (n := 12)
    (lo := (33817 / 125000000)) (hi := (270537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999459) = 1/(1999459 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8926 : Bounds (-270537 / 1000000000) (-33817 / 125000000) (Real.log (1999459 / 2000000)) := by
  have h := reflection_log_8926_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8927_neg : (32027933 / 250000000) ≤ -Real.log (25000 / 28417) ∧
    -Real.log (25000 / 28417) ≤ (128111733 / 1000000000) := by
  have h := checkLog_sound (w := (3417 / 53417)) (n := 12)
    (lo := (32027933 / 250000000)) (hi := (128111733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28417 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28417 / 25000) = 1/(25000 / 28417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8927 : Bounds (32027933 / 250000000) (128111733 / 1000000000) (Real.log (28417 / 25000)) := by
  have h := reflection_log_8927_neg
  have he : Real.log (28417 / 25000) = -Real.log (25000 / 28417) := by
    rw [show ((28417 / 25000) : ℝ) = ((25000 / 28417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8928_neg : (146969857 / 1000000000) ≤ -Real.log (21583 / 25000) ∧
    -Real.log (21583 / 25000) ≤ (73484929 / 500000000) := by
  have h := checkLog_sound (w := (3417 / 46583)) (n := 12)
    (lo := (146969857 / 1000000000)) (hi := (73484929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 21583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 21583) = 1/(21583 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8928 : Bounds (-73484929 / 500000000) (-146969857 / 1000000000) (Real.log (21583 / 25000)) := by
  have h := reflection_log_8928_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8929_neg : (25715227 / 200000000) ≤ -Real.log (125000 / 142151) ∧
    -Real.log (125000 / 142151) ≤ (16072017 / 125000000) := by
  have h := checkLog_sound (w := (17151 / 267151)) (n := 12)
    (lo := (25715227 / 200000000)) (hi := (16072017 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142151 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142151 / 125000) = 1/(125000 / 142151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8929 : Bounds (25715227 / 200000000) (16072017 / 125000000) (Real.log (142151 / 125000)) := by
  have h := reflection_log_8929_neg
  have he : Real.log (142151 / 125000) = -Real.log (125000 / 142151) := by
    rw [show ((142151 / 125000) : ℝ) = ((125000 / 142151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8930_neg : (36895409 / 250000000) ≤ -Real.log (107849 / 125000) ∧
    -Real.log (107849 / 125000) ≤ (147581637 / 1000000000) := by
  have h := checkLog_sound (w := (17151 / 232849)) (n := 12)
    (lo := (36895409 / 250000000)) (hi := (147581637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 107849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 107849) = 1/(107849 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8930 : Bounds (-147581637 / 1000000000) (-36895409 / 250000000) (Real.log (107849 / 125000)) := by
  have h := reflection_log_8930_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8931_neg : (19005501 / 1000000000) ≤ -Real.log (15330843199 / 15625000000) ∧
    -Real.log (15330843199 / 15625000000) ≤ (9502751 / 500000000) := by
  have h := checkLog_sound (w := (294156801 / 30955843199)) (n := 12)
    (lo := (19005501 / 1000000000)) (hi := (9502751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15330843199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15330843199) = 1/(15330843199 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8931 : Bounds (-9502751 / 500000000) (-19005501 / 1000000000) (Real.log (15330843199 / 15625000000)) := by
  have h := reflection_log_8931_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8932_neg : (4714531 / 250000000) ≤ -Real.log (613324111 / 625000000) ∧
    -Real.log (613324111 / 625000000) ≤ (30173 / 1600000) := by
  have h := checkLog_sound (w := (11675889 / 1238324111)) (n := 12)
    (lo := (4714531 / 250000000)) (hi := (30173 / 1600000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 613324111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 613324111) = 1/(613324111 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8932 : Bounds (-30173 / 1600000) (-4714531 / 250000000) (Real.log (613324111 / 625000000)) := by
  have h := reflection_log_8932_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8933_neg : (275081589 / 1000000000) ≤ -Real.log (250000000000 / 329159523699) ∧
    -Real.log (250000000000 / 329159523699) ≤ (27508159 / 100000000) := by
  have h := checkLog_sound (w := (79159523699 / 579159523699)) (n := 12)
    (lo := (275081589 / 1000000000)) (hi := (27508159 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329159523699 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329159523699 / 250000000000) = 1/(250000000000 / 329159523699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8933 : Bounds (275081589 / 1000000000) (27508159 / 100000000) (Real.log (329159523699 / 250000000000)) := by
  have h := reflection_log_8933_neg
  have he : Real.log (329159523699 / 250000000000) = -Real.log (250000000000 / 329159523699) := by
    rw [show ((329159523699 / 250000000000) : ℝ) = ((250000000000 / 329159523699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8934_neg : (69039443 / 250000000) ≤ -Real.log (12500000000 / 16475697503) ∧
    -Real.log (12500000000 / 16475697503) ≤ (276157773 / 1000000000) := by
  have h := checkLog_sound (w := (3975697503 / 28975697503)) (n := 12)
    (lo := (69039443 / 250000000)) (hi := (276157773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16475697503 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16475697503 / 12500000000) = 1/(12500000000 / 16475697503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8934 : Bounds (69039443 / 250000000) (276157773 / 1000000000) (Real.log (16475697503 / 12500000000)) := by
  have h := reflection_log_8934_neg
  have he : Real.log (16475697503 / 12500000000) = -Real.log (12500000000 / 16475697503) := by
    rw [show ((16475697503 / 12500000000) : ℝ) = ((12500000000 / 16475697503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8935_neg : (110745529 / 200000000) ≤ -Real.log (250000000000 / 434931506849) ∧
    -Real.log (250000000000 / 434931506849) ≤ (276863823 / 500000000) := by
  have h := checkLog_sound (w := (184931506849 / 684931506849)) (n := 12)
    (lo := (110745529 / 200000000)) (hi := (276863823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((434931506849 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(434931506849 / 250000000000) = 1/(250000000000 / 434931506849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8935 : Bounds (110745529 / 200000000) (276863823 / 500000000) (Real.log (434931506849 / 250000000000)) := by
  have h := reflection_log_8935_neg
  have he : Real.log (434931506849 / 250000000000) = -Real.log (250000000000 / 434931506849) := by
    rw [show ((434931506849 / 250000000000) : ℝ) = ((250000000000 / 434931506849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8936_neg : (277403217 / 500000000) ≤ -Real.log (500000000000 / 870801919123) ∧
    -Real.log (500000000000 / 870801919123) ≤ (110961287 / 200000000) := by
  have h := checkLog_sound (w := (370801919123 / 1370801919123)) (n := 12)
    (lo := (277403217 / 500000000)) (hi := (110961287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((870801919123 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(870801919123 / 500000000000) = 1/(500000000000 / 870801919123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8936 : Bounds (277403217 / 500000000) (110961287 / 200000000) (Real.log (870801919123 / 500000000000)) := by
  have h := reflection_log_8936_neg
  have he : Real.log (870801919123 / 500000000000) = -Real.log (500000000000 / 870801919123) := by
    rw [show ((870801919123 / 500000000000) : ℝ) = ((500000000000 / 870801919123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8937_neg : (29975499 / 125000000) ≤ -Real.log (1000 / 1271) ∧
    -Real.log (1000 / 1271) ≤ (239803993 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 2271)) (n := 12)
    (lo := (29975499 / 125000000)) (hi := (239803993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1271 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1271 / 1000) = 1/(1000 / 1271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8937 : Bounds (29975499 / 125000000) (239803993 / 1000000000) (Real.log (1271 / 1000)) := by
  have h := reflection_log_8937_neg
  have he : Real.log (1271 / 1000) = -Real.log (1000 / 1271) := by
    rw [show ((1271 / 1000) : ℝ) = ((1000 / 1271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8938_neg : (158040773 / 500000000) ≤ -Real.log (729 / 1000) ∧
    -Real.log (729 / 1000) ≤ (316081547 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 1729)) (n := 12)
    (lo := (158040773 / 500000000)) (hi := (316081547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 729) = 1/(729 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8938 : Bounds (-316081547 / 1000000000) (-158040773 / 500000000) (Real.log (729 / 1000)) := by
  have h := reflection_log_8938_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8939_neg : (270963 / 1000000000) ≤ -Real.log (1000000 / 1000271) ∧
    -Real.log (1000000 / 1000271) ≤ (67741 / 250000000) := by
  have h := checkLog_sound (w := (271 / 2000271)) (n := 12)
    (lo := (270963 / 1000000000)) (hi := (67741 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000271 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000271 / 1000000) = 1/(1000000 / 1000271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8939 : Bounds (270963 / 1000000000) (67741 / 250000000) (Real.log (1000271 / 1000000)) := by
  have h := reflection_log_8939_neg
  have he : Real.log (1000271 / 1000000) = -Real.log (1000000 / 1000271) := by
    rw [show ((1000271 / 1000000) : ℝ) = ((1000000 / 1000271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8940_neg : (67759 / 250000000) ≤ -Real.log (999729 / 1000000) ∧
    -Real.log (999729 / 1000000) ≤ (271037 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 1999729)) (n := 12)
    (lo := (67759 / 250000000)) (hi := (271037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999729) = 1/(999729 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8940 : Bounds (-271037 / 1000000000) (-67759 / 250000000) (Real.log (999729 / 1000000)) := by
  have h := reflection_log_8940_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8941_neg : (64170221 / 500000000) ≤ -Real.log (50000 / 56847) ∧
    -Real.log (50000 / 56847) ≤ (128340443 / 1000000000) := by
  have h := checkLog_sound (w := (6847 / 106847)) (n := 12)
    (lo := (64170221 / 500000000)) (hi := (128340443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56847 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56847 / 50000) = 1/(50000 / 56847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8941 : Bounds (64170221 / 500000000) (128340443 / 1000000000) (Real.log (56847 / 50000)) := by
  have h := reflection_log_8941_neg
  have he : Real.log (56847 / 50000) = -Real.log (50000 / 56847) := by
    rw [show ((56847 / 50000) : ℝ) = ((50000 / 56847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8942_neg : (29454213 / 200000000) ≤ -Real.log (43153 / 50000) ∧
    -Real.log (43153 / 50000) ≤ (73635533 / 500000000) := by
  have h := checkLog_sound (w := (6847 / 93153)) (n := 12)
    (lo := (29454213 / 200000000)) (hi := (73635533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 43153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 43153) = 1/(43153 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8942 : Bounds (-73635533 / 500000000) (-29454213 / 200000000) (Real.log (43153 / 50000)) := by
  have h := reflection_log_8942_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8943_neg : (128804739 / 1000000000) ≤ -Real.log (250000 / 284367) ∧
    -Real.log (250000 / 284367) ≤ (6440237 / 50000000) := by
  have h := checkLog_sound (w := (34367 / 534367)) (n := 12)
    (lo := (128804739 / 1000000000)) (hi := (6440237 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((284367 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(284367 / 250000) = 1/(250000 / 284367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8943 : Bounds (128804739 / 1000000000) (6440237 / 50000000) (Real.log (284367 / 250000)) := by
  have h := reflection_log_8943_neg
  have he : Real.log (284367 / 250000) = -Real.log (250000 / 284367) := by
    rw [show ((284367 / 250000) : ℝ) = ((250000 / 284367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8944_neg : (147883029 / 1000000000) ≤ -Real.log (215633 / 250000) ∧
    -Real.log (215633 / 250000) ≤ (14788303 / 100000000) := by
  have h := checkLog_sound (w := (34367 / 465633)) (n := 12)
    (lo := (147883029 / 1000000000)) (hi := (14788303 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 215633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 215633) = 1/(215633 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8944 : Bounds (-14788303 / 100000000) (-147883029 / 1000000000) (Real.log (215633 / 250000)) := by
  have h := reflection_log_8944_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8945_neg : (19078289 / 1000000000) ≤ -Real.log (61318909311 / 62500000000) ∧
    -Real.log (61318909311 / 62500000000) ≤ (1907829 / 100000000) := by
  have h := checkLog_sound (w := (1181090689 / 123818909311)) (n := 12)
    (lo := (19078289 / 1000000000)) (hi := (1907829 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61318909311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61318909311) = 1/(61318909311 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8945 : Bounds (-1907829 / 100000000) (-19078289 / 1000000000) (Real.log (61318909311 / 62500000000)) := by
  have h := reflection_log_8945_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8946_neg : (9465311 / 500000000) ≤ -Real.log (2453118591 / 2500000000) ∧
    -Real.log (2453118591 / 2500000000) ≤ (18930623 / 1000000000) := by
  have h := checkLog_sound (w := (46881409 / 4953118591)) (n := 12)
    (lo := (9465311 / 500000000)) (hi := (18930623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2453118591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2453118591) = 1/(2453118591 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8946 : Bounds (-18930623 / 1000000000) (-9465311 / 500000000) (Real.log (2453118591 / 2500000000)) := by
  have h := reflection_log_8946_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8947_neg : (68902877 / 250000000) ≤ -Real.log (62500000000 / 82333499409) ∧
    -Real.log (62500000000 / 82333499409) ≤ (275611509 / 1000000000) := by
  have h := checkLog_sound (w := (19833499409 / 144833499409)) (n := 12)
    (lo := (68902877 / 250000000)) (hi := (275611509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82333499409 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82333499409 / 62500000000) = 1/(62500000000 / 82333499409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8947 : Bounds (68902877 / 250000000) (275611509 / 1000000000) (Real.log (82333499409 / 62500000000)) := by
  have h := reflection_log_8947_neg
  have he : Real.log (82333499409 / 62500000000) = -Real.log (62500000000 / 82333499409) := by
    rw [show ((82333499409 / 62500000000) : ℝ) = ((62500000000 / 82333499409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8948_neg : (34585971 / 125000000) ≤ -Real.log (250000000000 / 329688637639) ∧
    -Real.log (250000000000 / 329688637639) ≤ (276687769 / 1000000000) := by
  have h := checkLog_sound (w := (79688637639 / 579688637639)) (n := 12)
    (lo := (34585971 / 125000000)) (hi := (276687769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329688637639 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329688637639 / 250000000000) = 1/(250000000000 / 329688637639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8948 : Bounds (34585971 / 125000000) (276687769 / 1000000000) (Real.log (329688637639 / 250000000000)) := by
  have h := reflection_log_8948_neg
  have he : Real.log (329688637639 / 250000000000) = -Real.log (250000000000 / 329688637639) := by
    rw [show ((329688637639 / 250000000000) : ℝ) = ((250000000000 / 329688637639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8949_neg : (277403217 / 500000000) ≤ -Real.log (250000000000 / 435400959561) ∧
    -Real.log (250000000000 / 435400959561) ≤ (110961287 / 200000000) := by
  have h := checkLog_sound (w := (185400959561 / 685400959561)) (n := 12)
    (lo := (277403217 / 500000000)) (hi := (110961287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((435400959561 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(435400959561 / 250000000000) = 1/(250000000000 / 435400959561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8949 : Bounds (277403217 / 500000000) (110961287 / 200000000) (Real.log (435400959561 / 250000000000)) := by
  have h := reflection_log_8949_neg
  have he : Real.log (435400959561 / 250000000000) = -Real.log (250000000000 / 435400959561) := by
    rw [show ((435400959561 / 250000000000) : ℝ) = ((250000000000 / 435400959561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8950_neg : (555885539 / 1000000000) ≤ -Real.log (500000000000 / 871742112483) ∧
    -Real.log (500000000000 / 871742112483) ≤ (27794277 / 50000000) := by
  have h := checkLog_sound (w := (371742112483 / 1371742112483)) (n := 12)
    (lo := (555885539 / 1000000000)) (hi := (27794277 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((871742112483 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(871742112483 / 500000000000) = 1/(500000000000 / 871742112483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8950 : Bounds (555885539 / 1000000000) (27794277 / 50000000) (Real.log (871742112483 / 500000000000)) := by
  have h := reflection_log_8950_neg
  have he : Real.log (871742112483 / 500000000000) = -Real.log (500000000000 / 871742112483) := by
    rw [show ((871742112483 / 500000000000) : ℝ) = ((500000000000 / 871742112483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8951_neg : (48039461 / 200000000) ≤ -Real.log (2000 / 2543) ∧
    -Real.log (2000 / 2543) ≤ (120098653 / 500000000) := by
  have h := checkLog_sound (w := (543 / 4543)) (n := 12)
    (lo := (48039461 / 200000000)) (hi := (120098653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2543 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2543 / 2000) = 1/(2000 / 2543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8951 : Bounds (48039461 / 200000000) (120098653 / 500000000) (Real.log (2543 / 2000)) := by
  have h := reflection_log_8951_neg
  have he : Real.log (2543 / 2000) = -Real.log (2000 / 2543) := by
    rw [show ((2543 / 2000) : ℝ) = ((2000 / 2543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8952_neg : (316767653 / 1000000000) ≤ -Real.log (1457 / 2000) ∧
    -Real.log (1457 / 2000) ≤ (158383827 / 500000000) := by
  have h := checkLog_sound (w := (543 / 3457)) (n := 12)
    (lo := (316767653 / 1000000000)) (hi := (158383827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1457) = 1/(1457 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8952 : Bounds (-158383827 / 500000000) (-316767653 / 1000000000) (Real.log (1457 / 2000)) := by
  have h := reflection_log_8952_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8953_neg : (271463 / 1000000000) ≤ -Real.log (2000000 / 2000543) ∧
    -Real.log (2000000 / 2000543) ≤ (33933 / 125000000) := by
  have h := checkLog_sound (w := (543 / 4000543)) (n := 12)
    (lo := (271463 / 1000000000)) (hi := (33933 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000543 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000543 / 2000000) = 1/(2000000 / 2000543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8953 : Bounds (271463 / 1000000000) (33933 / 125000000) (Real.log (2000543 / 2000000)) := by
  have h := reflection_log_8953_neg
  have he : Real.log (2000543 / 2000000) = -Real.log (2000000 / 2000543) := by
    rw [show ((2000543 / 2000000) : ℝ) = ((2000000 / 2000543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8954_neg : (16971 / 62500000) ≤ -Real.log (1999457 / 2000000) ∧
    -Real.log (1999457 / 2000000) ≤ (271537 / 1000000000) := by
  have h := checkLog_sound (w := (543 / 3999457)) (n := 12)
    (lo := (16971 / 62500000)) (hi := (271537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999457) = 1/(1999457 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8954 : Bounds (-271537 / 1000000000) (-16971 / 62500000) (Real.log (1999457 / 2000000)) := by
  have h := reflection_log_8954_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8955_neg : (1285691 / 10000000) ≤ -Real.log (2500 / 2843) ∧
    -Real.log (2500 / 2843) ≤ (128569101 / 1000000000) := by
  have h := checkLog_sound (w := (343 / 5343)) (n := 12)
    (lo := (1285691 / 10000000)) (hi := (128569101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2843 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2843 / 2500) = 1/(2500 / 2843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8955 : Bounds (1285691 / 10000000) (128569101 / 1000000000) (Real.log (2843 / 2500)) := by
  have h := reflection_log_8955_neg
  have he : Real.log (2843 / 2500) = -Real.log (2500 / 2843) := by
    rw [show ((2843 / 2500) : ℝ) = ((2500 / 2843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8956_neg : (36893091 / 250000000) ≤ -Real.log (2157 / 2500) ∧
    -Real.log (2157 / 2500) ≤ (29514473 / 200000000) := by
  have h := checkLog_sound (w := (343 / 4657)) (n := 12)
    (lo := (36893091 / 250000000)) (hi := (29514473 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2157) = 1/(2157 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8956 : Bounds (-29514473 / 200000000) (-36893091 / 250000000) (Real.log (2157 / 2500)) := by
  have h := reflection_log_8956_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8957_neg : (12903417 / 100000000) ≤ -Real.log (1000000 / 1137729) ∧
    -Real.log (1000000 / 1137729) ≤ (129034171 / 1000000000) := by
  have h := checkLog_sound (w := (137729 / 2137729)) (n := 12)
    (lo := (12903417 / 100000000)) (hi := (129034171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1137729 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1137729 / 1000000) = 1/(1000000 / 1137729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8957 : Bounds (12903417 / 100000000) (129034171 / 1000000000) (Real.log (1137729 / 1000000)) := by
  have h := reflection_log_8957_neg
  have he : Real.log (1137729 / 1000000) = -Real.log (1000000 / 1137729) := by
    rw [show ((1137729 / 1000000) : ℝ) = ((1000000 / 1137729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8958_neg : (18523209 / 125000000) ≤ -Real.log (862271 / 1000000) ∧
    -Real.log (862271 / 1000000) ≤ (148185673 / 1000000000) := by
  have h := checkLog_sound (w := (137729 / 1862271)) (n := 12)
    (lo := (18523209 / 125000000)) (hi := (148185673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 862271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 862271) = 1/(862271 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8958 : Bounds (-148185673 / 1000000000) (-18523209 / 125000000) (Real.log (862271 / 1000000)) := by
  have h := reflection_log_8958_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8959_neg : (9575751 / 500000000) ≤ -Real.log (981030722559 / 1000000000000) ∧
    -Real.log (981030722559 / 1000000000000) ≤ (19151503 / 1000000000) := by
  have h := checkLog_sound (w := (18969277441 / 1981030722559)) (n := 12)
    (lo := (9575751 / 500000000)) (hi := (19151503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981030722559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981030722559) = 1/(981030722559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8959 : Bounds (-19151503 / 1000000000) (-9575751 / 500000000) (Real.log (981030722559 / 1000000000000)) := by
  have h := reflection_log_8959_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0140 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8960_neg : (19003263 / 1000000000) ≤ -Real.log (6132351 / 6250000) ∧
    -Real.log (6132351 / 6250000) ≤ (148463 / 7812500) := by
  have h := checkLog_sound (w := (117649 / 12382351)) (n := 12)
    (lo := (19003263 / 1000000000)) (hi := (148463 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250000 / 6132351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250000 / 6132351) = 1/(6132351 / 6250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8960 : Bounds (-148463 / 7812500) (-19003263 / 1000000000) (Real.log (6132351 / 6250000)) := by
  have h := reflection_log_8960_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8961_neg : (55228293 / 200000000) ≤ -Real.log (500000000000 / 659017153453) ∧
    -Real.log (500000000000 / 659017153453) ≤ (138070733 / 500000000) := by
  have h := checkLog_sound (w := (159017153453 / 1159017153453)) (n := 12)
    (lo := (55228293 / 200000000)) (hi := (138070733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((659017153453 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(659017153453 / 500000000000) = 1/(500000000000 / 659017153453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8961 : Bounds (55228293 / 200000000) (138070733 / 500000000) (Real.log (659017153453 / 500000000000)) := by
  have h := reflection_log_8961_neg
  have he : Real.log (659017153453 / 500000000000) = -Real.log (500000000000 / 659017153453) := by
    rw [show ((659017153453 / 500000000000) : ℝ) = ((500000000000 / 659017153453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8962_neg : (138609921 / 500000000) ≤ -Real.log (250000000000 / 329864103049) ∧
    -Real.log (250000000000 / 329864103049) ≤ (277219843 / 1000000000) := by
  have h := checkLog_sound (w := (79864103049 / 579864103049)) (n := 12)
    (lo := (138609921 / 500000000)) (hi := (277219843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329864103049 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329864103049 / 250000000000) = 1/(250000000000 / 329864103049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8962 : Bounds (138609921 / 500000000) (277219843 / 1000000000) (Real.log (329864103049 / 250000000000)) := by
  have h := reflection_log_8962_neg
  have he : Real.log (329864103049 / 250000000000) = -Real.log (250000000000 / 329864103049) := by
    rw [show ((329864103049 / 250000000000) : ℝ) = ((250000000000 / 329864103049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8963_neg : (555885539 / 1000000000) ≤ -Real.log (250000000000 / 435871056241) ∧
    -Real.log (250000000000 / 435871056241) ≤ (27794277 / 50000000) := by
  have h := checkLog_sound (w := (185871056241 / 685871056241)) (n := 12)
    (lo := (555885539 / 1000000000)) (hi := (27794277 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((435871056241 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(435871056241 / 250000000000) = 1/(250000000000 / 435871056241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8963 : Bounds (555885539 / 1000000000) (27794277 / 50000000) (Real.log (435871056241 / 250000000000)) := by
  have h := reflection_log_8963_neg
  have he : Real.log (435871056241 / 250000000000) = -Real.log (250000000000 / 435871056241) := by
    rw [show ((435871056241 / 250000000000) : ℝ) = ((250000000000 / 435871056241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8964_neg : (556964959 / 1000000000) ≤ -Real.log (31250000000 / 54542724777) ∧
    -Real.log (31250000000 / 54542724777) ≤ (3481031 / 6250000) := by
  have h := checkLog_sound (w := (23292724777 / 85792724777)) (n := 12)
    (lo := (556964959 / 1000000000)) (hi := (3481031 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54542724777 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54542724777 / 31250000000) = 1/(31250000000 / 54542724777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8964 : Bounds (556964959 / 1000000000) (3481031 / 6250000) (Real.log (54542724777 / 31250000000)) := by
  have h := reflection_log_8964_neg
  have he : Real.log (54542724777 / 31250000000) = -Real.log (31250000000 / 54542724777) := by
    rw [show ((54542724777 / 31250000000) : ℝ) = ((31250000000 / 54542724777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8965_neg : (1879613 / 7812500) ≤ -Real.log (125 / 159) ∧
    -Real.log (125 / 159) ≤ (48118093 / 200000000) := by
  have h := checkLog_sound (w := (17 / 142)) (n := 12)
    (lo := (1879613 / 7812500)) (hi := (48118093 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159 / 125) = 1/(125 / 159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8965 : Bounds (1879613 / 7812500) (48118093 / 200000000) (Real.log (159 / 125)) := by
  have h := reflection_log_8965_neg
  have he : Real.log (159 / 125) = -Real.log (125 / 159) := by
    rw [show ((159 / 125) : ℝ) = ((125 / 159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8966_neg : (31745423 / 100000000) ≤ -Real.log (91 / 125) ∧
    -Real.log (91 / 125) ≤ (317454231 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 108)) (n := 12)
    (lo := (31745423 / 100000000)) (hi := (317454231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 91) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 91) = 1/(91 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8966 : Bounds (-317454231 / 1000000000) (-31745423 / 100000000) (Real.log (91 / 125)) := by
  have h := reflection_log_8966_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8967_neg : (271963 / 1000000000) ≤ -Real.log (62500 / 62517) ∧
    -Real.log (62500 / 62517) ≤ (67991 / 250000000) := by
  have h := checkLog_sound (w := (17 / 125017)) (n := 12)
    (lo := (271963 / 1000000000)) (hi := (67991 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62517 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62517 / 62500) = 1/(62500 / 62517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8967 : Bounds (271963 / 1000000000) (67991 / 250000000) (Real.log (62517 / 62500)) := by
  have h := reflection_log_8967_neg
  have he : Real.log (62517 / 62500) = -Real.log (62500 / 62517) := by
    rw [show ((62517 / 62500) : ℝ) = ((62500 / 62517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8968_neg : (68009 / 250000000) ≤ -Real.log (62483 / 62500) ∧
    -Real.log (62483 / 62500) ≤ (272037 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 124983)) (n := 12)
    (lo := (68009 / 250000000)) (hi := (272037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62483) = 1/(62483 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8968 : Bounds (-272037 / 1000000000) (-68009 / 250000000) (Real.log (62483 / 62500)) := by
  have h := reflection_log_8968_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8969_neg : (64398853 / 500000000) ≤ -Real.log (50000 / 56873) ∧
    -Real.log (50000 / 56873) ≤ (128797707 / 1000000000) := by
  have h := checkLog_sound (w := (6873 / 106873)) (n := 12)
    (lo := (64398853 / 500000000)) (hi := (128797707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56873 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56873 / 50000) = 1/(50000 / 56873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8969 : Bounds (64398853 / 500000000) (128797707 / 1000000000) (Real.log (56873 / 50000)) := by
  have h := reflection_log_8969_neg
  have he : Real.log (56873 / 50000) = -Real.log (50000 / 56873) := by
    rw [show ((56873 / 50000) : ℝ) = ((50000 / 56873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8970_neg : (73936877 / 500000000) ≤ -Real.log (43127 / 50000) ∧
    -Real.log (43127 / 50000) ≤ (29574751 / 200000000) := by
  have h := checkLog_sound (w := (6873 / 93127)) (n := 12)
    (lo := (73936877 / 500000000)) (hi := (29574751 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 43127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 43127) = 1/(43127 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8970 : Bounds (-29574751 / 200000000) (-73936877 / 500000000) (Real.log (43127 / 50000)) := by
  have h := reflection_log_8970_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8971_neg : (32315887 / 250000000) ≤ -Real.log (100000 / 113799) ∧
    -Real.log (100000 / 113799) ≤ (129263549 / 1000000000) := by
  have h := checkLog_sound (w := (13799 / 213799)) (n := 12)
    (lo := (32315887 / 250000000)) (hi := (129263549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113799 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(113799 / 100000) = 1/(100000 / 113799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8971 : Bounds (32315887 / 250000000) (129263549 / 1000000000) (Real.log (113799 / 100000)) := by
  have h := reflection_log_8971_neg
  have he : Real.log (113799 / 100000) = -Real.log (100000 / 113799) := by
    rw [show ((113799 / 100000) : ℝ) = ((100000 / 113799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8972_neg : (148488407 / 1000000000) ≤ -Real.log (86201 / 100000) ∧
    -Real.log (86201 / 100000) ≤ (18561051 / 125000000) := by
  have h := checkLog_sound (w := (13799 / 186201)) (n := 12)
    (lo := (148488407 / 1000000000)) (hi := (18561051 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 86201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 86201) = 1/(86201 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8972 : Bounds (-18561051 / 125000000) (-148488407 / 1000000000) (Real.log (86201 / 100000)) := by
  have h := reflection_log_8972_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8973_neg : (19224859 / 1000000000) ≤ -Real.log (9809587599 / 10000000000) ∧
    -Real.log (9809587599 / 10000000000) ≤ (961243 / 50000000) := by
  have h := checkLog_sound (w := (190412401 / 19809587599)) (n := 12)
    (lo := (19224859 / 1000000000)) (hi := (961243 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9809587599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9809587599) = 1/(9809587599 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8973 : Bounds (-961243 / 50000000) (-19224859 / 1000000000) (Real.log (9809587599 / 10000000000)) := by
  have h := reflection_log_8973_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8974_neg : (19076047 / 1000000000) ≤ -Real.log (2452761871 / 2500000000) ∧
    -Real.log (2452761871 / 2500000000) ≤ (1192253 / 62500000) := by
  have h := checkLog_sound (w := (47238129 / 4952761871)) (n := 12)
    (lo := (19076047 / 1000000000)) (hi := (1192253 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2452761871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2452761871) = 1/(2452761871 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8974 : Bounds (-1192253 / 62500000) (-19076047 / 1000000000) (Real.log (2452761871 / 2500000000)) := by
  have h := reflection_log_8974_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8975_neg : (13833573 / 50000000) ≤ -Real.log (125000000000 / 164841630533) ∧
    -Real.log (125000000000 / 164841630533) ≤ (276671461 / 1000000000) := by
  have h := checkLog_sound (w := (39841630533 / 289841630533)) (n := 12)
    (lo := (13833573 / 50000000)) (hi := (276671461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164841630533 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164841630533 / 125000000000) = 1/(125000000000 / 164841630533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8975 : Bounds (13833573 / 50000000) (276671461 / 1000000000) (Real.log (164841630533 / 125000000000)) := by
  have h := reflection_log_8975_neg
  have he : Real.log (164841630533 / 125000000000) = -Real.log (125000000000 / 164841630533) := by
    rw [show ((164841630533 / 125000000000) : ℝ) = ((125000000000 / 164841630533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8976_neg : (55550391 / 200000000) ≤ -Real.log (125000000000 / 165019837357) ∧
    -Real.log (125000000000 / 165019837357) ≤ (69437989 / 250000000) := by
  have h := checkLog_sound (w := (40019837357 / 290019837357)) (n := 12)
    (lo := (55550391 / 200000000)) (hi := (69437989 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165019837357 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165019837357 / 125000000000) = 1/(125000000000 / 165019837357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8976 : Bounds (55550391 / 200000000) (69437989 / 250000000) (Real.log (165019837357 / 125000000000)) := by
  have h := reflection_log_8976_neg
  have he : Real.log (165019837357 / 125000000000) = -Real.log (125000000000 / 165019837357) := by
    rw [show ((165019837357 / 125000000000) : ℝ) = ((125000000000 / 165019837357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8977_neg : (556964959 / 1000000000) ≤ -Real.log (500000000000 / 872683596431) ∧
    -Real.log (500000000000 / 872683596431) ≤ (3481031 / 6250000) := by
  have h := checkLog_sound (w := (372683596431 / 1372683596431)) (n := 12)
    (lo := (556964959 / 1000000000)) (hi := (3481031 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((872683596431 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(872683596431 / 500000000000) = 1/(500000000000 / 872683596431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8977 : Bounds (556964959 / 1000000000) (3481031 / 6250000) (Real.log (872683596431 / 500000000000)) := by
  have h := reflection_log_8977_neg
  have he : Real.log (872683596431 / 500000000000) = -Real.log (500000000000 / 872683596431) := by
    rw [show ((872683596431 / 500000000000) : ℝ) = ((500000000000 / 872683596431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8978_neg : (111608939 / 200000000) ≤ -Real.log (500000000000 / 873626373627) ∧
    -Real.log (500000000000 / 873626373627) ≤ (69755587 / 125000000) := by
  have h := checkLog_sound (w := (373626373627 / 1373626373627)) (n := 12)
    (lo := (111608939 / 200000000)) (hi := (69755587 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((873626373627 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(873626373627 / 500000000000) = 1/(500000000000 / 873626373627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8978 : Bounds (111608939 / 200000000) (69755587 / 125000000) (Real.log (873626373627 / 500000000000)) := by
  have h := reflection_log_8978_neg
  have he : Real.log (873626373627 / 500000000000) = -Real.log (500000000000 / 873626373627) := by
    rw [show ((873626373627 / 500000000000) : ℝ) = ((500000000000 / 873626373627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8979_neg : (240983469 / 1000000000) ≤ -Real.log (400 / 509) ∧
    -Real.log (400 / 509) ≤ (24098347 / 100000000) := by
  have h := checkLog_sound (w := (109 / 909)) (n := 12)
    (lo := (240983469 / 1000000000)) (hi := (24098347 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((509 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(509 / 400) = 1/(400 / 509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8979 : Bounds (240983469 / 1000000000) (24098347 / 100000000) (Real.log (509 / 400)) := by
  have h := reflection_log_8979_neg
  have he : Real.log (509 / 400) = -Real.log (400 / 509) := by
    rw [show ((509 / 400) : ℝ) = ((400 / 509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8980_neg : (318141279 / 1000000000) ≤ -Real.log (291 / 400) ∧
    -Real.log (291 / 400) ≤ (1988383 / 6250000) := by
  have h := checkLog_sound (w := (109 / 691)) (n := 12)
    (lo := (318141279 / 1000000000)) (hi := (1988383 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 291) = 1/(291 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8980 : Bounds (-1988383 / 6250000) (-318141279 / 1000000000) (Real.log (291 / 400)) := by
  have h := reflection_log_8980_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8981_neg : (136231 / 500000000) ≤ -Real.log (400000 / 400109) ∧
    -Real.log (400000 / 400109) ≤ (272463 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 800109)) (n := 12)
    (lo := (136231 / 500000000)) (hi := (272463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400109 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400109 / 400000) = 1/(400000 / 400109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8981 : Bounds (136231 / 500000000) (272463 / 1000000000) (Real.log (400109 / 400000)) := by
  have h := reflection_log_8981_neg
  have he : Real.log (400109 / 400000) = -Real.log (400000 / 400109) := by
    rw [show ((400109 / 400000) : ℝ) = ((400000 / 400109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8982_neg : (272537 / 1000000000) ≤ -Real.log (399891 / 400000) ∧
    -Real.log (399891 / 400000) ≤ (136269 / 500000000) := by
  have h := checkLog_sound (w := (109 / 799891)) (n := 12)
    (lo := (272537 / 1000000000)) (hi := (136269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399891) = 1/(399891 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8982 : Bounds (-136269 / 500000000) (-272537 / 1000000000) (Real.log (399891 / 400000)) := by
  have h := reflection_log_8982_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8983_neg : (129026259 / 1000000000) ≤ -Real.log (25000 / 28443) ∧
    -Real.log (25000 / 28443) ≤ (6451313 / 50000000) := by
  have h := checkLog_sound (w := (3443 / 53443)) (n := 12)
    (lo := (129026259 / 1000000000)) (hi := (6451313 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28443 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28443 / 25000) = 1/(25000 / 28443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8983 : Bounds (129026259 / 1000000000) (6451313 / 50000000) (Real.log (28443 / 25000)) := by
  have h := reflection_log_8983_neg
  have he : Real.log (28443 / 25000) = -Real.log (25000 / 28443) := by
    rw [show ((28443 / 25000) : ℝ) = ((25000 / 28443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8984_neg : (29635047 / 200000000) ≤ -Real.log (21557 / 25000) ∧
    -Real.log (21557 / 25000) ≤ (37043809 / 250000000) := by
  have h := checkLog_sound (w := (3443 / 46557)) (n := 12)
    (lo := (29635047 / 200000000)) (hi := (37043809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 21557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 21557) = 1/(21557 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8984 : Bounds (-37043809 / 250000000) (-29635047 / 200000000) (Real.log (21557 / 25000)) := by
  have h := reflection_log_8984_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8985_neg : (25898399 / 200000000) ≤ -Real.log (4000 / 4553) ∧
    -Real.log (4000 / 4553) ≤ (32372999 / 250000000) := by
  have h := checkLog_sound (w := (553 / 8553)) (n := 12)
    (lo := (25898399 / 200000000)) (hi := (32372999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4553 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4553 / 4000) = 1/(4000 / 4553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8985 : Bounds (25898399 / 200000000) (32372999 / 250000000) (Real.log (4553 / 4000)) := by
  have h := reflection_log_8985_neg
  have he : Real.log (4553 / 4000) = -Real.log (4000 / 4553) := by
    rw [show ((4553 / 4000) : ℝ) = ((4000 / 4553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8986_neg : (148790073 / 1000000000) ≤ -Real.log (3447 / 4000) ∧
    -Real.log (3447 / 4000) ≤ (74395037 / 500000000) := by
  have h := checkLog_sound (w := (553 / 7447)) (n := 12)
    (lo := (148790073 / 1000000000)) (hi := (74395037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 3447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000 / 3447) = 1/(3447 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8986 : Bounds (-74395037 / 500000000) (-148790073 / 1000000000) (Real.log (3447 / 4000)) := by
  have h := reflection_log_8986_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8987_neg : (9649039 / 500000000) ≤ -Real.log (15694191 / 16000000) ∧
    -Real.log (15694191 / 16000000) ≤ (19298079 / 1000000000) := by
  have h := checkLog_sound (w := (305809 / 31694191)) (n := 12)
    (lo := (9649039 / 500000000)) (hi := (19298079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16000000 / 15694191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16000000 / 15694191) = 1/(15694191 / 16000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8987 : Bounds (-19298079 / 1000000000) (-9649039 / 500000000) (Real.log (15694191 / 16000000)) := by
  have h := reflection_log_8987_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8988_neg : (765959 / 40000000) ≤ -Real.log (613145751 / 625000000) ∧
    -Real.log (613145751 / 625000000) ≤ (1196811 / 62500000) := by
  have h := checkLog_sound (w := (11854249 / 1238145751)) (n := 12)
    (lo := (765959 / 40000000)) (hi := (1196811 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 613145751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 613145751) = 1/(613145751 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8988 : Bounds (-1196811 / 62500000) (-765959 / 40000000) (Real.log (613145751 / 625000000)) := by
  have h := reflection_log_8988_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8989_neg : (138600747 / 500000000) ≤ -Real.log (250000000000 / 329858050749) ∧
    -Real.log (250000000000 / 329858050749) ≤ (55440299 / 200000000) := by
  have h := checkLog_sound (w := (79858050749 / 579858050749)) (n := 12)
    (lo := (138600747 / 500000000)) (hi := (55440299 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329858050749 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329858050749 / 250000000000) = 1/(250000000000 / 329858050749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8989 : Bounds (138600747 / 500000000) (55440299 / 200000000) (Real.log (329858050749 / 250000000000)) := by
  have h := reflection_log_8989_neg
  have he : Real.log (329858050749 / 250000000000) = -Real.log (250000000000 / 329858050749) := by
    rw [show ((329858050749 / 250000000000) : ℝ) = ((250000000000 / 329858050749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8990_neg : (69570517 / 250000000) ≤ -Real.log (500000000000 / 660429358863) ∧
    -Real.log (500000000000 / 660429358863) ≤ (278282069 / 1000000000) := by
  have h := checkLog_sound (w := (160429358863 / 1160429358863)) (n := 12)
    (lo := (69570517 / 250000000)) (hi := (278282069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((660429358863 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(660429358863 / 500000000000) = 1/(500000000000 / 660429358863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8990 : Bounds (69570517 / 250000000) (278282069 / 1000000000) (Real.log (660429358863 / 500000000000)) := by
  have h := reflection_log_8990_neg
  have he : Real.log (660429358863 / 500000000000) = -Real.log (500000000000 / 660429358863) := by
    rw [show ((660429358863 / 500000000000) : ℝ) = ((500000000000 / 660429358863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8991_neg : (111608939 / 200000000) ≤ -Real.log (250000000000 / 436813186813) ∧
    -Real.log (250000000000 / 436813186813) ≤ (69755587 / 125000000) := by
  have h := checkLog_sound (w := (186813186813 / 686813186813)) (n := 12)
    (lo := (111608939 / 200000000)) (hi := (69755587 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((436813186813 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(436813186813 / 250000000000) = 1/(250000000000 / 436813186813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8991 : Bounds (111608939 / 200000000) (69755587 / 125000000) (Real.log (436813186813 / 250000000000)) := by
  have h := reflection_log_8991_neg
  have he : Real.log (436813186813 / 250000000000) = -Real.log (250000000000 / 436813186813) := by
    rw [show ((436813186813 / 250000000000) : ℝ) = ((250000000000 / 436813186813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8992_neg : (559124749 / 1000000000) ≤ -Real.log (31250000000 / 54660652921) ∧
    -Real.log (31250000000 / 54660652921) ≤ (2236499 / 4000000) := by
  have h := checkLog_sound (w := (23410652921 / 85910652921)) (n := 12)
    (lo := (559124749 / 1000000000)) (hi := (2236499 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54660652921 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54660652921 / 31250000000) = 1/(31250000000 / 54660652921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8992 : Bounds (559124749 / 1000000000) (2236499 / 4000000) (Real.log (54660652921 / 31250000000)) := by
  have h := reflection_log_8992_neg
  have he : Real.log (54660652921 / 31250000000) = -Real.log (31250000000 / 54660652921) := by
    rw [show ((54660652921 / 31250000000) : ℝ) = ((31250000000 / 54660652921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8993_neg : (241376319 / 1000000000) ≤ -Real.log (1000 / 1273) ∧
    -Real.log (1000 / 1273) ≤ (754301 / 3125000) := by
  have h := checkLog_sound (w := (273 / 2273)) (n := 12)
    (lo := (241376319 / 1000000000)) (hi := (754301 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1273 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1273 / 1000) = 1/(1000 / 1273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8993 : Bounds (241376319 / 1000000000) (754301 / 3125000) (Real.log (1273 / 1000)) := by
  have h := reflection_log_8993_neg
  have he : Real.log (1273 / 1000) = -Real.log (1000 / 1273) := by
    rw [show ((1273 / 1000) : ℝ) = ((1000 / 1273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8994_neg : (318828801 / 1000000000) ≤ -Real.log (727 / 1000) ∧
    -Real.log (727 / 1000) ≤ (159414401 / 500000000) := by
  have h := checkLog_sound (w := (273 / 1727)) (n := 12)
    (lo := (318828801 / 1000000000)) (hi := (159414401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 727) = 1/(727 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8994 : Bounds (-159414401 / 500000000) (-318828801 / 1000000000) (Real.log (727 / 1000)) := by
  have h := reflection_log_8994_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8995_neg : (136481 / 500000000) ≤ -Real.log (1000000 / 1000273) ∧
    -Real.log (1000000 / 1000273) ≤ (272963 / 1000000000) := by
  have h := checkLog_sound (w := (273 / 2000273)) (n := 12)
    (lo := (136481 / 500000000)) (hi := (272963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000273 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000273 / 1000000) = 1/(1000000 / 1000273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8995 : Bounds (136481 / 500000000) (272963 / 1000000000) (Real.log (1000273 / 1000000)) := by
  have h := reflection_log_8995_neg
  have he : Real.log (1000273 / 1000000) = -Real.log (1000000 / 1000273) := by
    rw [show ((1000273 / 1000000) : ℝ) = ((1000000 / 1000273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8996_neg : (273037 / 1000000000) ≤ -Real.log (999727 / 1000000) ∧
    -Real.log (999727 / 1000000) ≤ (136519 / 500000000) := by
  have h := checkLog_sound (w := (273 / 1999727)) (n := 12)
    (lo := (273037 / 1000000000)) (hi := (136519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999727) = 1/(999727 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8996 : Bounds (-136519 / 500000000) (-273037 / 1000000000) (Real.log (999727 / 1000000)) := by
  have h := reflection_log_8996_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8997_neg : (129255639 / 1000000000) ≤ -Real.log (1000000 / 1137981) ∧
    -Real.log (1000000 / 1137981) ≤ (3231391 / 25000000) := by
  have h := checkLog_sound (w := (137981 / 2137981)) (n := 12)
    (lo := (129255639 / 1000000000)) (hi := (3231391 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1137981 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1137981 / 1000000) = 1/(1000000 / 1137981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8997 : Bounds (129255639 / 1000000000) (3231391 / 25000000) (Real.log (1137981 / 1000000)) := by
  have h := reflection_log_8997_neg
  have he : Real.log (1137981 / 1000000) = -Real.log (1000000 / 1137981) := by
    rw [show ((1137981 / 1000000) : ℝ) = ((1000000 / 1137981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8998_neg : (74238983 / 500000000) ≤ -Real.log (862019 / 1000000) ∧
    -Real.log (862019 / 1000000) ≤ (148477967 / 1000000000) := by
  have h := checkLog_sound (w := (137981 / 1862019)) (n := 12)
    (lo := (74238983 / 500000000)) (hi := (148477967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 862019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 862019) = 1/(862019 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8998 : Bounds (-148477967 / 1000000000) (-74238983 / 500000000) (Real.log (862019 / 1000000)) := by
  have h := reflection_log_8998_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8999_neg : (32430317 / 250000000) ≤ -Real.log (1000000 / 1138511) ∧
    -Real.log (1000000 / 1138511) ≤ (129721269 / 1000000000) := by
  have h := checkLog_sound (w := (138511 / 2138511)) (n := 12)
    (lo := (32430317 / 250000000)) (hi := (129721269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1138511 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1138511 / 1000000) = 1/(1000000 / 1138511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8999 : Bounds (32430317 / 250000000) (129721269 / 1000000000) (Real.log (1138511 / 1000000)) := by
  have h := reflection_log_8999_neg
  have he : Real.log (1138511 / 1000000) = -Real.log (1000000 / 1138511) := by
    rw [show ((1138511 / 1000000) : ℝ) = ((1000000 / 1138511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9000_neg : (149092991 / 1000000000) ≤ -Real.log (861489 / 1000000) ∧
    -Real.log (861489 / 1000000) ≤ (1164789 / 7812500) := by
  have h := checkLog_sound (w := (138511 / 1861489)) (n := 12)
    (lo := (149092991 / 1000000000)) (hi := (1164789 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 861489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 861489) = 1/(861489 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9000 : Bounds (-1164789 / 7812500) (-149092991 / 1000000000) (Real.log (861489 / 1000000)) := by
  have h := reflection_log_9000_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9001_neg : (19371723 / 1000000000) ≤ -Real.log (980814702879 / 1000000000000) ∧
    -Real.log (980814702879 / 1000000000000) ≤ (4842931 / 250000000) := by
  have h := checkLog_sound (w := (19185297121 / 1980814702879)) (n := 12)
    (lo := (19371723 / 1000000000)) (hi := (4842931 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980814702879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980814702879) = 1/(980814702879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9001 : Bounds (-4842931 / 250000000) (-19371723 / 1000000000) (Real.log (980814702879 / 1000000000000)) := by
  have h := reflection_log_9001_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9002_neg : (19222327 / 1000000000) ≤ -Real.log (980961243639 / 1000000000000) ∧
    -Real.log (980961243639 / 1000000000000) ≤ (2402791 / 125000000) := by
  have h := checkLog_sound (w := (19038756361 / 1980961243639)) (n := 12)
    (lo := (19222327 / 1000000000)) (hi := (2402791 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980961243639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980961243639) = 1/(980961243639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9002 : Bounds (-2402791 / 125000000) (-19222327 / 1000000000) (Real.log (980961243639 / 1000000000000)) := by
  have h := reflection_log_9002_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9003_neg : (138866803 / 500000000) ≤ -Real.log (500000000000 / 660067237497) ∧
    -Real.log (500000000000 / 660067237497) ≤ (277733607 / 1000000000) := by
  have h := checkLog_sound (w := (160067237497 / 1160067237497)) (n := 12)
    (lo := (138866803 / 500000000)) (hi := (277733607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((660067237497 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(660067237497 / 500000000000) = 1/(500000000000 / 660067237497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9003 : Bounds (138866803 / 500000000) (277733607 / 1000000000) (Real.log (660067237497 / 500000000000)) := by
  have h := reflection_log_9003_neg
  have he : Real.log (660067237497 / 500000000000) = -Real.log (500000000000 / 660067237497) := by
    rw [show ((660067237497 / 500000000000) : ℝ) = ((500000000000 / 660067237497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9004_neg : (278814259 / 1000000000) ≤ -Real.log (500000000000 / 660780926977) ∧
    -Real.log (500000000000 / 660780926977) ≤ (13940713 / 50000000) := by
  have h := checkLog_sound (w := (160780926977 / 1160780926977)) (n := 12)
    (lo := (278814259 / 1000000000)) (hi := (13940713 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((660780926977 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(660780926977 / 500000000000) = 1/(500000000000 / 660780926977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9004 : Bounds (278814259 / 1000000000) (13940713 / 50000000) (Real.log (660780926977 / 500000000000)) := by
  have h := reflection_log_9004_neg
  have he : Real.log (660780926977 / 500000000000) = -Real.log (500000000000 / 660780926977) := by
    rw [show ((660780926977 / 500000000000) : ℝ) = ((500000000000 / 660780926977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9005_neg : (559124749 / 1000000000) ≤ -Real.log (100000000000 / 174914089347) ∧
    -Real.log (100000000000 / 174914089347) ≤ (2236499 / 4000000) := by
  have h := checkLog_sound (w := (74914089347 / 274914089347)) (n := 12)
    (lo := (559124749 / 1000000000)) (hi := (2236499 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174914089347 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(174914089347 / 100000000000) = 1/(100000000000 / 174914089347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9005 : Bounds (559124749 / 1000000000) (2236499 / 4000000) (Real.log (174914089347 / 100000000000)) := by
  have h := reflection_log_9005_neg
  have he : Real.log (174914089347 / 100000000000) = -Real.log (100000000000 / 174914089347) := by
    rw [show ((174914089347 / 100000000000) : ℝ) = ((100000000000 / 174914089347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9006_neg : (560205121 / 1000000000) ≤ -Real.log (7812500000 / 13679934663) ∧
    -Real.log (7812500000 / 13679934663) ≤ (280102561 / 500000000) := by
  have h := checkLog_sound (w := (5867434663 / 21492434663)) (n := 12)
    (lo := (560205121 / 1000000000)) (hi := (280102561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13679934663 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13679934663 / 7812500000) = 1/(7812500000 / 13679934663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9006 : Bounds (560205121 / 1000000000) (280102561 / 500000000) (Real.log (13679934663 / 7812500000)) := by
  have h := reflection_log_9006_neg
  have he : Real.log (13679934663 / 7812500000) = -Real.log (7812500000 / 13679934663) := by
    rw [show ((13679934663 / 7812500000) : ℝ) = ((7812500000 / 13679934663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9007_neg : (48353803 / 200000000) ≤ -Real.log (2000 / 2547) ∧
    -Real.log (2000 / 2547) ≤ (30221127 / 125000000) := by
  have h := checkLog_sound (w := (547 / 4547)) (n := 12)
    (lo := (48353803 / 200000000)) (hi := (30221127 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2547 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2547 / 2000) = 1/(2000 / 2547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9007 : Bounds (48353803 / 200000000) (30221127 / 125000000) (Real.log (2547 / 2000)) := by
  have h := reflection_log_9007_neg
  have he : Real.log (2547 / 2000) = -Real.log (2000 / 2547) := by
    rw [show ((2547 / 2000) : ℝ) = ((2000 / 2547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9008_neg : (63903359 / 200000000) ≤ -Real.log (1453 / 2000) ∧
    -Real.log (1453 / 2000) ≤ (79879199 / 250000000) := by
  have h := checkLog_sound (w := (547 / 3453)) (n := 12)
    (lo := (63903359 / 200000000)) (hi := (79879199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1453) = 1/(1453 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9008 : Bounds (-79879199 / 250000000) (-63903359 / 200000000) (Real.log (1453 / 2000)) := by
  have h := reflection_log_9008_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9009_neg : (136731 / 500000000) ≤ -Real.log (2000000 / 2000547) ∧
    -Real.log (2000000 / 2000547) ≤ (273463 / 1000000000) := by
  have h := checkLog_sound (w := (547 / 4000547)) (n := 12)
    (lo := (136731 / 500000000)) (hi := (273463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000547 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000547 / 2000000) = 1/(2000000 / 2000547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9009 : Bounds (136731 / 500000000) (273463 / 1000000000) (Real.log (2000547 / 2000000)) := by
  have h := reflection_log_9009_neg
  have he : Real.log (2000547 / 2000000) = -Real.log (2000000 / 2000547) := by
    rw [show ((2000547 / 2000000) : ℝ) = ((2000000 / 2000547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9010_neg : (273537 / 1000000000) ≤ -Real.log (1999453 / 2000000) ∧
    -Real.log (1999453 / 2000000) ≤ (136769 / 500000000) := by
  have h := checkLog_sound (w := (547 / 3999453)) (n := 12)
    (lo := (273537 / 1000000000)) (hi := (136769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999453) = 1/(1999453 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9010 : Bounds (-136769 / 500000000) (-273537 / 1000000000) (Real.log (1999453 / 2000000)) := by
  have h := reflection_log_9010_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9011_neg : (16185511 / 125000000) ≤ -Real.log (1000000 / 1138241) ∧
    -Real.log (1000000 / 1138241) ≤ (129484089 / 1000000000) := by
  have h := checkLog_sound (w := (138241 / 2138241)) (n := 12)
    (lo := (16185511 / 125000000)) (hi := (129484089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1138241 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1138241 / 1000000) = 1/(1000000 / 1138241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9011 : Bounds (16185511 / 125000000) (129484089 / 1000000000) (Real.log (1138241 / 1000000)) := by
  have h := reflection_log_9011_neg
  have he : Real.log (1138241 / 1000000) = -Real.log (1000000 / 1138241) := by
    rw [show ((1138241 / 1000000) : ℝ) = ((1000000 / 1138241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9012_neg : (148779629 / 1000000000) ≤ -Real.log (861759 / 1000000) ∧
    -Real.log (861759 / 1000000) ≤ (14877963 / 100000000) := by
  have h := checkLog_sound (w := (138241 / 1861759)) (n := 12)
    (lo := (148779629 / 1000000000)) (hi := (14877963 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 861759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 861759) = 1/(861759 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9012 : Bounds (-14877963 / 100000000) (-148779629 / 1000000000) (Real.log (861759 / 1000000)) := by
  have h := reflection_log_9012_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9013_neg : (16243811 / 125000000) ≤ -Real.log (250000 / 284693) ∧
    -Real.log (250000 / 284693) ≤ (129950489 / 1000000000) := by
  have h := checkLog_sound (w := (34693 / 534693)) (n := 12)
    (lo := (16243811 / 125000000)) (hi := (129950489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((284693 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(284693 / 250000) = 1/(250000 / 284693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9013 : Bounds (16243811 / 125000000) (129950489 / 1000000000) (Real.log (284693 / 250000)) := by
  have h := reflection_log_9013_neg
  have he : Real.log (284693 / 250000) = -Real.log (250000 / 284693) := by
    rw [show ((284693 / 250000) : ℝ) = ((250000 / 284693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9014_neg : (149396001 / 1000000000) ≤ -Real.log (215307 / 250000) ∧
    -Real.log (215307 / 250000) ≤ (74698001 / 500000000) := by
  have h := checkLog_sound (w := (34693 / 465307)) (n := 12)
    (lo := (149396001 / 1000000000)) (hi := (74698001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 215307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 215307) = 1/(215307 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9014 : Bounds (-74698001 / 500000000) (-149396001 / 1000000000) (Real.log (215307 / 250000)) := by
  have h := reflection_log_9014_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9015_neg : (2430689 / 125000000) ≤ -Real.log (61296395751 / 62500000000) ∧
    -Real.log (61296395751 / 62500000000) ≤ (19445513 / 1000000000) := by
  have h := checkLog_sound (w := (1203604249 / 123796395751)) (n := 12)
    (lo := (2430689 / 125000000)) (hi := (19445513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61296395751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61296395751) = 1/(61296395751 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9015 : Bounds (-19445513 / 1000000000) (-2430689 / 125000000) (Real.log (61296395751 / 62500000000)) := by
  have h := reflection_log_9015_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9016_neg : (19295541 / 1000000000) ≤ -Real.log (980889425919 / 1000000000000) ∧
    -Real.log (980889425919 / 1000000000000) ≤ (9647771 / 500000000) := by
  have h := checkLog_sound (w := (19110574081 / 1980889425919)) (n := 12)
    (lo := (19295541 / 1000000000)) (hi := (9647771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980889425919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980889425919) = 1/(980889425919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9016 : Bounds (-9647771 / 500000000) (-19295541 / 1000000000) (Real.log (980889425919 / 1000000000000)) := by
  have h := reflection_log_9016_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9017_neg : (139131859 / 500000000) ≤ -Real.log (250000000000 / 330208619811) ∧
    -Real.log (250000000000 / 330208619811) ≤ (278263719 / 1000000000) := by
  have h := checkLog_sound (w := (80208619811 / 580208619811)) (n := 12)
    (lo := (139131859 / 500000000)) (hi := (278263719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330208619811 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(330208619811 / 250000000000) = 1/(250000000000 / 330208619811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9017 : Bounds (139131859 / 500000000) (278263719 / 1000000000) (Real.log (330208619811 / 250000000000)) := by
  have h := reflection_log_9017_neg
  have he : Real.log (330208619811 / 250000000000) = -Real.log (250000000000 / 330208619811) := by
    rw [show ((330208619811 / 250000000000) : ℝ) = ((250000000000 / 330208619811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9018_neg : (27934649 / 100000000) ≤ -Real.log (25000000000 / 33056635409) ∧
    -Real.log (25000000000 / 33056635409) ≤ (279346491 / 1000000000) := by
  have h := checkLog_sound (w := (8056635409 / 58056635409)) (n := 12)
    (lo := (27934649 / 100000000)) (hi := (279346491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33056635409 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33056635409 / 25000000000) = 1/(25000000000 / 33056635409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9018 : Bounds (27934649 / 100000000) (279346491 / 1000000000) (Real.log (33056635409 / 25000000000)) := by
  have h := reflection_log_9018_neg
  have he : Real.log (33056635409 / 25000000000) = -Real.log (25000000000 / 33056635409) := by
    rw [show ((33056635409 / 25000000000) : ℝ) = ((25000000000 / 33056635409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9019_neg : (560205121 / 1000000000) ≤ -Real.log (500000000000 / 875515818431) ∧
    -Real.log (500000000000 / 875515818431) ≤ (280102561 / 500000000) := by
  have h := checkLog_sound (w := (375515818431 / 1375515818431)) (n := 12)
    (lo := (560205121 / 1000000000)) (hi := (280102561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((875515818431 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(875515818431 / 500000000000) = 1/(500000000000 / 875515818431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9019 : Bounds (560205121 / 1000000000) (280102561 / 500000000) (Real.log (875515818431 / 500000000000)) := by
  have h := reflection_log_9019_neg
  have he : Real.log (875515818431 / 500000000000) = -Real.log (500000000000 / 875515818431) := by
    rw [show ((875515818431 / 500000000000) : ℝ) = ((500000000000 / 875515818431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9020_neg : (561285811 / 1000000000) ≤ -Real.log (250000000000 / 438231245699) ∧
    -Real.log (250000000000 / 438231245699) ≤ (140321453 / 250000000) := by
  have h := checkLog_sound (w := (188231245699 / 688231245699)) (n := 12)
    (lo := (561285811 / 1000000000)) (hi := (140321453 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((438231245699 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(438231245699 / 250000000000) = 1/(250000000000 / 438231245699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9020 : Bounds (561285811 / 1000000000) (140321453 / 250000000) (Real.log (438231245699 / 250000000000)) := by
  have h := reflection_log_9020_neg
  have he : Real.log (438231245699 / 250000000000) = -Real.log (250000000000 / 438231245699) := by
    rw [show ((438231245699 / 250000000000) : ℝ) = ((250000000000 / 438231245699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9021_neg : (242161557 / 1000000000) ≤ -Real.log (500 / 637) ∧
    -Real.log (500 / 637) ≤ (121080779 / 500000000) := by
  have h := checkLog_sound (w := (137 / 1137)) (n := 12)
    (lo := (242161557 / 1000000000)) (hi := (121080779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((637 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(637 / 500) = 1/(500 / 637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9021 : Bounds (242161557 / 1000000000) (121080779 / 500000000) (Real.log (637 / 500)) := by
  have h := reflection_log_9021_neg
  have he : Real.log (637 / 500) = -Real.log (500 / 637) := by
    rw [show ((637 / 500) : ℝ) = ((500 / 637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9022_neg : (20012829 / 62500000) ≤ -Real.log (363 / 500) ∧
    -Real.log (363 / 500) ≤ (64041053 / 200000000) := by
  have h := checkLog_sound (w := (137 / 863)) (n := 12)
    (lo := (20012829 / 62500000)) (hi := (64041053 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 363) = 1/(363 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9022 : Bounds (-64041053 / 200000000) (-20012829 / 62500000) (Real.log (363 / 500)) := by
  have h := reflection_log_9022_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9023_neg : (136981 / 500000000) ≤ -Real.log (500000 / 500137) ∧
    -Real.log (500000 / 500137) ≤ (273963 / 1000000000) := by
  have h := checkLog_sound (w := (137 / 1000137)) (n := 12)
    (lo := (136981 / 500000000)) (hi := (273963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500137 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500137 / 500000) = 1/(500000 / 500137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9023 : Bounds (136981 / 500000000) (273963 / 1000000000) (Real.log (500137 / 500000)) := by
  have h := reflection_log_9023_neg
  have he : Real.log (500137 / 500000) = -Real.log (500000 / 500137) := by
    rw [show ((500137 / 500000) : ℝ) = ((500000 / 500137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


