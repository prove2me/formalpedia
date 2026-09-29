-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0232__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0232__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T21:53:47.897558+00:00
-- url     : https://prove2.me/theorems/b7102e59-b826-4fdd-be42-5ecb8ab37a17
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0232 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0233, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0232 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0233, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0234)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0232 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0233, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0234)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0232 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0233, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0234) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0232 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0233, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0234).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0232 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14848_neg : (7356497 / 7812500) ≤ -Real.log (389991 / 1000000) ∧
    -Real.log (389991 / 1000000) ≤ (470815809 / 500000000) := by
  have h := checkLog_sound (w := (110009 / 889991)) (n := 12)
    (lo := (62121109 / 250000000)) (hi := (248484437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 389991) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 389991) = 1/(389991 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14848 : Bounds (-470815809 / 500000000) (-7356497 / 7812500) (Real.log (389991 / 1000000)) := by
  have h := reflection_log_14848_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14849_neg : (58173981 / 125000000) ≤ -Real.log (627889019919 / 1000000000000) ∧
    -Real.log (627889019919 / 1000000000000) ≤ (465391849 / 1000000000) := by
  have h := checkLog_sound (w := (372110980081 / 1627889019919)) (n := 12)
    (lo := (58173981 / 125000000)) (hi := (465391849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 627889019919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 627889019919) = 1/(627889019919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14849 : Bounds (-465391849 / 1000000000) (-58173981 / 125000000) (Real.log (627889019919 / 1000000000000)) := by
  have h := reflection_log_14849_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14850_neg : (92372241 / 200000000) ≤ -Real.log (157527447351 / 250000000000) ∧
    -Real.log (157527447351 / 250000000000) ≤ (230930603 / 500000000) := by
  have h := checkLog_sound (w := (92472552649 / 407527447351)) (n := 12)
    (lo := (92372241 / 200000000)) (hi := (230930603 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 157527447351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 157527447351) = 1/(157527447351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14850 : Bounds (-230930603 / 500000000) (-92372241 / 200000000) (Real.log (157527447351 / 250000000000)) := by
  have h := reflection_log_14850_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14851_neg : (353018719 / 250000000) ≤ -Real.log (250000000000 / 1026115707963) ∧
    -Real.log (250000000000 / 1026115707963) ≤ (1412074879 / 1000000000) := by
  have h := checkLog_sound (w := (26115707963 / 2026115707963)) (n := 12)
    (lo := (6445129 / 250000000)) (hi := (25780517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1026115707963 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1026115707963 / 1000000000000) = 1/(250000000000 / 1026115707963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14851 : Bounds (353018719 / 250000000) (1412074879 / 1000000000) (Real.log (1026115707963 / 250000000000)) := by
  have h := reflection_log_14851_neg
  have he : Real.log (1026115707963 / 250000000000) = -Real.log (250000000000 / 1026115707963) := by
    rw [show ((1026115707963 / 250000000000) : ℝ) = ((250000000000 / 1026115707963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14852_neg : (177233923 / 125000000) ≤ -Real.log (250000000000 / 1032080868533) ∧
    -Real.log (250000000000 / 1032080868533) ≤ (1417871387 / 1000000000) := by
  have h := checkLog_sound (w := (32080868533 / 2032080868533)) (n := 12)
    (lo := (493391 / 15625000)) (hi := (1263081 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1032080868533 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1032080868533 / 1000000000000) = 1/(250000000000 / 1032080868533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14852 : Bounds (177233923 / 125000000) (1417871387 / 1000000000) (Real.log (1032080868533 / 250000000000)) := by
  have h := reflection_log_14852_neg
  have he : Real.log (1032080868533 / 250000000000) = -Real.log (250000000000 / 1032080868533) := by
    rw [show ((1032080868533 / 250000000000) : ℝ) = ((250000000000 / 1032080868533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14853_neg : (3999219547 / 1000000000) ≤ -Real.log (500000000000 / 27277777777777) ∧
    -Real.log (500000000000 / 27277777777777) ≤ (3999219553 / 1000000000) := by
  have h := checkLog_sound (w := (11277777777777 / 43277777777777)) (n := 12)
    (lo := (533483647 / 1000000000)) (hi := (4167841 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27277777777777 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(27277777777777 / 16000000000000) = 1/(500000000000 / 27277777777777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14853 : Bounds (3999219547 / 1000000000) (3999219553 / 1000000000) (Real.log (27277777777777 / 500000000000)) := by
  have h := reflection_log_14853_neg
  have he : Real.log (27277777777777 / 500000000000) = -Real.log (500000000000 / 27277777777777) := by
    rw [show ((27277777777777 / 500000000000) : ℝ) = ((500000000000 / 27277777777777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14854_neg : (201394973 / 50000000) ≤ -Real.log (500000000000 / 28071428571429) ∧
    -Real.log (500000000000 / 28071428571429) ≤ (2013949733 / 500000000) := by
  have h := checkLog_sound (w := (12071428571429 / 44071428571429)) (n := 12)
    (lo := (14054089 / 25000000)) (hi := (562163561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28071428571429 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(28071428571429 / 16000000000000) = 1/(500000000000 / 28071428571429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14854 : Bounds (201394973 / 50000000) (2013949733 / 500000000) (Real.log (28071428571429 / 500000000000)) := by
  have h := reflection_log_14854_neg
  have he : Real.log (28071428571429 / 500000000000) = -Real.log (500000000000 / 28071428571429) := by
    rw [show ((28071428571429 / 500000000000) : ℝ) = ((500000000000 / 28071428571429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14855_neg : (676001021 / 1000000000) ≤ -Real.log (500 / 983) ∧
    -Real.log (500 / 983) ≤ (338000511 / 500000000) := by
  have h := checkLog_sound (w := (483 / 1483)) (n := 12)
    (lo := (676001021 / 1000000000)) (hi := (338000511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983 / 500) = 1/(500 / 983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14855 : Bounds (676001021 / 1000000000) (338000511 / 500000000) (Real.log (983 / 500)) := by
  have h := reflection_log_14855_neg
  have he : Real.log (983 / 500) = -Real.log (500 / 983) := by
    rw [show ((983 / 500) : ℝ) = ((500 / 983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14856_neg : (52834293 / 15625000) ≤ -Real.log (17 / 500) ∧
    -Real.log (17 / 500) ≤ (3381394757 / 1000000000) := by
  have h := checkLog_sound (w := (57 / 193)) (n := 12)
    (lo := (38050377 / 62500000)) (hi := (608806033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 68) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 68) = 1/(17 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14856 : Bounds (-3381394757 / 1000000000) (-52834293 / 15625000) (Real.log (17 / 500)) := by
  have h := reflection_log_14856_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14857_neg : (965533 / 1000000000) ≤ -Real.log (500000 / 500483) ∧
    -Real.log (500000 / 500483) ≤ (482767 / 500000000) := by
  have h := checkLog_sound (w := (483 / 1000483)) (n := 12)
    (lo := (965533 / 1000000000)) (hi := (482767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500483 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500483 / 500000) = 1/(500000 / 500483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14857 : Bounds (965533 / 1000000000) (482767 / 500000000) (Real.log (500483 / 500000)) := by
  have h := reflection_log_14857_neg
  have he : Real.log (500483 / 500000) = -Real.log (500000 / 500483) := by
    rw [show ((500483 / 500000) : ℝ) = ((500000 / 500483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14858_neg : (483233 / 500000000) ≤ -Real.log (499517 / 500000) ∧
    -Real.log (499517 / 500000) ≤ (966467 / 1000000000) := by
  have h := checkLog_sound (w := (483 / 999517)) (n := 12)
    (lo := (483233 / 500000000)) (hi := (966467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499517) = 1/(499517 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14858 : Bounds (-966467 / 1000000000) (-483233 / 500000000) (Real.log (499517 / 500000)) := by
  have h := reflection_log_14858_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14859_neg : (475835341 / 1000000000) ≤ -Real.log (500000 / 804679) ∧
    -Real.log (500000 / 804679) ≤ (237917671 / 500000000) := by
  have h := checkLog_sound (w := (304679 / 1304679)) (n := 12)
    (lo := (475835341 / 1000000000)) (hi := (237917671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((804679 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(804679 / 500000) = 1/(500000 / 804679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14859 : Bounds (475835341 / 1000000000) (237917671 / 500000000) (Real.log (804679 / 500000)) := by
  have h := reflection_log_14859_neg
  have he : Real.log (804679 / 500000) = -Real.log (500000 / 804679) := by
    rw [show ((804679 / 500000) : ℝ) = ((500000 / 804679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14860_neg : (469981869 / 500000000) ≤ -Real.log (195321 / 500000) ∧
    -Real.log (195321 / 500000) ≤ (46998187 / 50000000) := by
  have h := checkLog_sound (w := (54679 / 445321)) (n := 12)
    (lo := (123408279 / 500000000)) (hi := (246816559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 195321) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 195321) = 1/(195321 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14860 : Bounds (-46998187 / 50000000) (-469981869 / 500000000) (Real.log (195321 / 500000)) := by
  have h := reflection_log_14860_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14861_neg : (95394359 / 200000000) ≤ -Real.log (250000 / 402797) ∧
    -Real.log (250000 / 402797) ≤ (119242949 / 250000000) := by
  have h := checkLog_sound (w := (152797 / 652797)) (n := 12)
    (lo := (95394359 / 200000000)) (hi := (119242949 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((402797 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(402797 / 250000) = 1/(250000 / 402797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14861 : Bounds (95394359 / 200000000) (119242949 / 250000000) (Real.log (402797 / 250000)) := by
  have h := reflection_log_14861_neg
  have he : Real.log (402797 / 250000) = -Real.log (250000 / 402797) := by
    rw [show ((402797 / 250000) : ℝ) = ((250000 / 402797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14862_neg : (472329671 / 500000000) ≤ -Real.log (97203 / 250000) ∧
    -Real.log (97203 / 250000) ≤ (59041209 / 62500000) := by
  have h := checkLog_sound (w := (27797 / 222203)) (n := 12)
    (lo := (125756081 / 500000000)) (hi := (251512163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 97203) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 97203) = 1/(97203 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14862 : Bounds (-59041209 / 62500000) (-472329671 / 500000000) (Real.log (97203 / 250000)) := by
  have h := reflection_log_14862_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14863_neg : (467687547 / 1000000000) ≤ -Real.log (39153076791 / 62500000000) ∧
    -Real.log (39153076791 / 62500000000) ≤ (116921887 / 250000000) := by
  have h := checkLog_sound (w := (23346923209 / 101653076791)) (n := 12)
    (lo := (467687547 / 1000000000)) (hi := (116921887 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 39153076791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 39153076791) = 1/(39153076791 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14863 : Bounds (-116921887 / 250000000) (-467687547 / 1000000000) (Real.log (39153076791 / 62500000000)) := by
  have h := reflection_log_14863_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14864_neg : (464128397 / 1000000000) ≤ -Real.log (157170706959 / 250000000000) ∧
    -Real.log (157170706959 / 250000000000) ≤ (232064199 / 500000000) := by
  have h := checkLog_sound (w := (92829293041 / 407170706959)) (n := 12)
    (lo := (464128397 / 1000000000)) (hi := (232064199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 157170706959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 157170706959) = 1/(157170706959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14864 : Bounds (-232064199 / 500000000) (-464128397 / 1000000000) (Real.log (157170706959 / 250000000000)) := by
  have h := reflection_log_14864_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14865_neg : (35394977 / 25000000) ≤ -Real.log (31250000000 / 128743037103) ∧
    -Real.log (31250000000 / 128743037103) ≤ (1415799083 / 1000000000) := by
  have h := checkLog_sound (w := (3743037103 / 253743037103)) (n := 12)
    (lo := (368809 / 12500000)) (hi := (29504721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128743037103 / 125000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(128743037103 / 125000000000) = 1/(31250000000 / 128743037103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14865 : Bounds (35394977 / 25000000) (1415799083 / 1000000000) (Real.log (128743037103 / 31250000000)) := by
  have h := reflection_log_14865_neg
  have he : Real.log (128743037103 / 31250000000) = -Real.log (31250000000 / 128743037103) := by
    rw [show ((128743037103 / 31250000000) : ℝ) = ((31250000000 / 128743037103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14866_neg : (44425973 / 31250000) ≤ -Real.log (125000000000 / 517984270033) ∧
    -Real.log (125000000000 / 517984270033) ≤ (1421631139 / 1000000000) := by
  have h := checkLog_sound (w := (17984270033 / 1017984270033)) (n := 12)
    (lo := (4417097 / 125000000)) (hi := (35336777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((517984270033 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(517984270033 / 500000000000) = 1/(125000000000 / 517984270033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14866 : Bounds (44425973 / 31250000) (1421631139 / 1000000000) (Real.log (517984270033 / 125000000000)) := by
  have h := reflection_log_14866_neg
  have he : Real.log (517984270033 / 125000000000) = -Real.log (125000000000 / 517984270033) := by
    rw [show ((517984270033 / 125000000000) : ℝ) = ((125000000000 / 517984270033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14867_neg : (201394973 / 50000000) ≤ -Real.log (125000000000 / 7017857142857) ∧
    -Real.log (125000000000 / 7017857142857) ≤ (2013949733 / 500000000) := by
  have h := checkLog_sound (w := (3017857142857 / 11017857142857)) (n := 12)
    (lo := (14054089 / 25000000)) (hi := (562163561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7017857142857 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(7017857142857 / 4000000000000) = 1/(125000000000 / 7017857142857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14867 : Bounds (201394973 / 50000000) (2013949733 / 500000000) (Real.log (7017857142857 / 125000000000)) := by
  have h := reflection_log_14867_neg
  have he : Real.log (7017857142857 / 125000000000) = -Real.log (125000000000 / 7017857142857) := by
    rw [show ((7017857142857 / 125000000000) : ℝ) = ((125000000000 / 7017857142857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14868_neg : (4057395773 / 1000000000) ≤ -Real.log (500000000000 / 28911764705883) ∧
    -Real.log (500000000000 / 28911764705883) ≤ (4057395779 / 1000000000) := by
  have h := checkLog_sound (w := (12911764705883 / 44911764705883)) (n := 12)
    (lo := (591659873 / 1000000000)) (hi := (295829937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28911764705883 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(28911764705883 / 16000000000000) = 1/(500000000000 / 28911764705883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14868 : Bounds (4057395773 / 1000000000) (4057395779 / 1000000000) (Real.log (28911764705883 / 500000000000)) := by
  have h := reflection_log_14868_neg
  have he : Real.log (28911764705883 / 500000000000) = -Real.log (500000000000 / 28911764705883) := by
    rw [show ((28911764705883 / 500000000000) : ℝ) = ((500000000000 / 28911764705883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14869_neg : (676509539 / 1000000000) ≤ -Real.log (1000 / 1967) ∧
    -Real.log (1000 / 1967) ≤ (33825477 / 50000000) := by
  have h := checkLog_sound (w := (967 / 2967)) (n := 12)
    (lo := (676509539 / 1000000000)) (hi := (33825477 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1967 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1967 / 1000) = 1/(1000 / 1967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14869 : Bounds (676509539 / 1000000000) (33825477 / 50000000) (Real.log (1967 / 1000)) := by
  have h := reflection_log_14869_neg
  have he : Real.log (1967 / 1000) = -Real.log (1000 / 1967) := by
    rw [show ((1967 / 1000) : ℝ) = ((1000 / 1967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14870_neg : (682249543 / 200000000) ≤ -Real.log (33 / 1000) ∧
    -Real.log (33 / 1000) ≤ (85281193 / 25000000) := by
  have h := checkLog_sound (w := (59 / 191)) (n := 12)
    (lo := (127731799 / 200000000)) (hi := (159664749 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 66) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 66) = 1/(33 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14870 : Bounds (-85281193 / 25000000) (-682249543 / 200000000) (Real.log (33 / 1000)) := by
  have h := reflection_log_14870_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14871_neg : (241633 / 250000000) ≤ -Real.log (1000000 / 1000967) ∧
    -Real.log (1000000 / 1000967) ≤ (966533 / 1000000000) := by
  have h := checkLog_sound (w := (967 / 2000967)) (n := 12)
    (lo := (241633 / 250000000)) (hi := (966533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000967 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000967 / 1000000) = 1/(1000000 / 1000967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14871 : Bounds (241633 / 250000000) (966533 / 1000000000) (Real.log (1000967 / 1000000)) := by
  have h := reflection_log_14871_neg
  have he : Real.log (1000967 / 1000000) = -Real.log (1000000 / 1000967) := by
    rw [show ((1000967 / 1000000) : ℝ) = ((1000000 / 1000967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14872_neg : (967467 / 1000000000) ≤ -Real.log (999033 / 1000000) ∧
    -Real.log (999033 / 1000000) ≤ (241867 / 250000000) := by
  have h := checkLog_sound (w := (967 / 1999033)) (n := 12)
    (lo := (967467 / 1000000000)) (hi := (241867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999033) = 1/(999033 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14872 : Bounds (-241867 / 250000000) (-967467 / 1000000000) (Real.log (999033 / 1000000)) := by
  have h := reflection_log_14872_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14873_neg : (476567663 / 1000000000) ≤ -Real.log (1000000 / 1610537) ∧
    -Real.log (1000000 / 1610537) ≤ (29785479 / 62500000) := by
  have h := checkLog_sound (w := (610537 / 2610537)) (n := 12)
    (lo := (476567663 / 1000000000)) (hi := (29785479 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1610537 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1610537 / 1000000) = 1/(1000000 / 1610537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14873 : Bounds (476567663 / 1000000000) (29785479 / 62500000) (Real.log (1610537 / 1000000)) := by
  have h := reflection_log_14873_neg
  have he : Real.log (1610537 / 1000000) = -Real.log (1000000 / 1610537) := by
    rw [show ((1610537 / 1000000) : ℝ) = ((1000000 / 1610537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14874_neg : (942986411 / 1000000000) ≤ -Real.log (389463 / 1000000) ∧
    -Real.log (389463 / 1000000) ≤ (942986413 / 1000000000) := by
  have h := checkLog_sound (w := (110537 / 889463)) (n := 12)
    (lo := (249839231 / 1000000000)) (hi := (1951869 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 389463) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 389463) = 1/(389463 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14874 : Bounds (-942986413 / 1000000000) (-942986411 / 1000000000) (Real.log (389463 / 1000000)) := by
  have h := reflection_log_14874_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14875_neg : (238853503 / 500000000) ≤ -Real.log (1000000 / 1612373) ∧
    -Real.log (1000000 / 1612373) ≤ (477707007 / 1000000000) := by
  have h := checkLog_sound (w := (612373 / 2612373)) (n := 12)
    (lo := (238853503 / 500000000)) (hi := (477707007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1612373 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1612373 / 1000000) = 1/(1000000 / 1612373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14875 : Bounds (238853503 / 500000000) (477707007 / 1000000000) (Real.log (1612373 / 1000000)) := by
  have h := reflection_log_14875_neg
  have he : Real.log (1612373 / 1000000) = -Real.log (1000000 / 1612373) := by
    rw [show ((1612373 / 1000000) : ℝ) = ((1000000 / 1612373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14876_neg : (947711741 / 1000000000) ≤ -Real.log (387627 / 1000000) ∧
    -Real.log (387627 / 1000000) ≤ (947711743 / 1000000000) := by
  have h := checkLog_sound (w := (112373 / 887627)) (n := 12)
    (lo := (254564561 / 1000000000)) (hi := (127282281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 387627) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 387627) = 1/(387627 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14876 : Bounds (-947711743 / 1000000000) (-947711741 / 1000000000) (Real.log (387627 / 1000000)) := by
  have h := reflection_log_14876_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14877_neg : (94000947 / 200000000) ≤ -Real.log (624999308871 / 1000000000000) ∧
    -Real.log (624999308871 / 1000000000000) ≤ (917978 / 1953125) := by
  have h := checkLog_sound (w := (375000691129 / 1624999308871)) (n := 12)
    (lo := (94000947 / 200000000)) (hi := (917978 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 624999308871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 624999308871) = 1/(624999308871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14877 : Bounds (-917978 / 1953125) (-94000947 / 200000000) (Real.log (624999308871 / 1000000000000)) := by
  have h := reflection_log_14877_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14878_neg : (116604687 / 250000000) ≤ -Real.log (627244571631 / 1000000000000) ∧
    -Real.log (627244571631 / 1000000000000) ≤ (466418749 / 1000000000) := by
  have h := checkLog_sound (w := (372755428369 / 1627244571631)) (n := 12)
    (lo := (116604687 / 250000000)) (hi := (466418749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 627244571631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 627244571631) = 1/(627244571631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14878 : Bounds (-466418749 / 1000000000) (-116604687 / 250000000) (Real.log (627244571631 / 1000000000000)) := by
  have h := reflection_log_14878_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14879_neg : (709777037 / 500000000) ≤ -Real.log (500000000000 / 2067638004123) ∧
    -Real.log (500000000000 / 2067638004123) ≤ (1419554077 / 1000000000) := by
  have h := checkLog_sound (w := (67638004123 / 4067638004123)) (n := 12)
    (lo := (16629857 / 500000000)) (hi := (6651943 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2067638004123 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2067638004123 / 2000000000000) = 1/(500000000000 / 2067638004123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14879 : Bounds (709777037 / 500000000) (1419554077 / 1000000000) (Real.log (2067638004123 / 500000000000)) := by
  have h := reflection_log_14879_neg
  have he : Real.log (2067638004123 / 500000000000) = -Real.log (500000000000 / 2067638004123) := by
    rw [show ((2067638004123 / 500000000000) : ℝ) = ((500000000000 / 2067638004123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14880_neg : (1425418747 / 1000000000) ≤ -Real.log (500000000000 / 2079799652759) ∧
    -Real.log (500000000000 / 2079799652759) ≤ (228067 / 160000) := by
  have h := checkLog_sound (w := (79799652759 / 4079799652759)) (n := 12)
    (lo := (39124387 / 1000000000)) (hi := (9781097 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2079799652759 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2079799652759 / 2000000000000) = 1/(500000000000 / 2079799652759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14880 : Bounds (1425418747 / 1000000000) (228067 / 160000) (Real.log (2079799652759 / 500000000000)) := by
  have h := reflection_log_14880_neg
  have he : Real.log (2079799652759 / 500000000000) = -Real.log (500000000000 / 2079799652759) := by
    rw [show ((2079799652759 / 500000000000) : ℝ) = ((500000000000 / 2079799652759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14881_neg : (4057395773 / 1000000000) ≤ -Real.log (250000000000 / 14455882352941) ∧
    -Real.log (250000000000 / 14455882352941) ≤ (4057395779 / 1000000000) := by
  have h := checkLog_sound (w := (6455882352941 / 22455882352941)) (n := 12)
    (lo := (591659873 / 1000000000)) (hi := (295829937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14455882352941 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(14455882352941 / 8000000000000) = 1/(250000000000 / 14455882352941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14881 : Bounds (4057395773 / 1000000000) (4057395779 / 1000000000) (Real.log (14455882352941 / 250000000000)) := by
  have h := reflection_log_14881_neg
  have he : Real.log (14455882352941 / 250000000000) = -Real.log (250000000000 / 14455882352941) := by
    rw [show ((14455882352941 / 250000000000) : ℝ) = ((250000000000 / 14455882352941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14882_neg : (2043878627 / 500000000) ≤ -Real.log (500000000000 / 29803030303031) ∧
    -Real.log (500000000000 / 29803030303031) ≤ (204387863 / 50000000) := by
  have h := checkLog_sound (w := (13803030303031 / 45803030303031)) (n := 12)
    (lo := (311010677 / 500000000)) (hi := (124404271 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29803030303031 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(29803030303031 / 16000000000000) = 1/(500000000000 / 29803030303031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14882 : Bounds (2043878627 / 500000000) (204387863 / 50000000) (Real.log (29803030303031 / 500000000000)) := by
  have h := reflection_log_14882_neg
  have he : Real.log (29803030303031 / 500000000000) = -Real.log (500000000000 / 29803030303031) := by
    rw [show ((29803030303031 / 500000000000) : ℝ) = ((500000000000 / 29803030303031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14883_neg : (338508899 / 500000000) ≤ -Real.log (125 / 246) ∧
    -Real.log (125 / 246) ≤ (677017799 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 371)) (n := 12)
    (lo := (338508899 / 500000000)) (hi := (677017799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246 / 125) = 1/(125 / 246) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14883 : Bounds (338508899 / 500000000) (677017799 / 1000000000) (Real.log (246 / 125)) := by
  have h := reflection_log_14883_neg
  have he : Real.log (246 / 125) = -Real.log (125 / 246) := by
    rw [show ((246 / 125) : ℝ) = ((125 / 246) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14884_neg : (3442019373 / 1000000000) ≤ -Real.log (4 / 125) ∧
    -Real.log (4 / 125) ≤ (1721009689 / 500000000) := by
  have h := checkLog_sound (w := (61 / 189)) (n := 12)
    (lo := (669430653 / 1000000000)) (hi := (334715327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 64) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 64) = 1/(4 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14884 : Bounds (-1721009689 / 500000000) (-3442019373 / 1000000000) (Real.log (4 / 125)) := by
  have h := reflection_log_14884_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14885_neg : (967531 / 1000000000) ≤ -Real.log (125000 / 125121) ∧
    -Real.log (125000 / 125121) ≤ (241883 / 250000000) := by
  have h := checkLog_sound (w := (121 / 250121)) (n := 12)
    (lo := (967531 / 1000000000)) (hi := (241883 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125121 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125121 / 125000) = 1/(125000 / 125121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14885 : Bounds (967531 / 1000000000) (241883 / 250000000) (Real.log (125121 / 125000)) := by
  have h := reflection_log_14885_neg
  have he : Real.log (125121 / 125000) = -Real.log (125000 / 125121) := by
    rw [show ((125121 / 125000) : ℝ) = ((125000 / 125121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14886_neg : (242117 / 250000000) ≤ -Real.log (124879 / 125000) ∧
    -Real.log (124879 / 125000) ≤ (968469 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 249879)) (n := 12)
    (lo := (242117 / 250000000)) (hi := (968469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124879) = 1/(124879 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14886 : Bounds (-968469 / 1000000000) (-242117 / 250000000) (Real.log (124879 / 125000)) := by
  have h := reflection_log_14886_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14887_neg : (119325793 / 250000000) ≤ -Real.log (500000 / 805861) ∧
    -Real.log (500000 / 805861) ≤ (477303173 / 1000000000) := by
  have h := checkLog_sound (w := (305861 / 1305861)) (n := 12)
    (lo := (119325793 / 250000000)) (hi := (477303173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((805861 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(805861 / 500000) = 1/(500000 / 805861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14887 : Bounds (119325793 / 250000000) (477303173 / 1000000000) (Real.log (805861 / 500000)) := by
  have h := reflection_log_14887_neg
  have he : Real.log (805861 / 500000) = -Real.log (500000 / 805861) := by
    rw [show ((805861 / 500000) : ℝ) = ((500000 / 805861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14888_neg : (9460337 / 10000000) ≤ -Real.log (194139 / 500000) ∧
    -Real.log (194139 / 500000) ≤ (473016851 / 500000000) := by
  have h := checkLog_sound (w := (55861 / 444139)) (n := 12)
    (lo := (6322163 / 25000000)) (hi := (252886521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 194139) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 194139) = 1/(194139 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14888 : Bounds (-473016851 / 500000000) (-9460337 / 10000000) (Real.log (194139 / 500000)) := by
  have h := reflection_log_14888_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14889_neg : (7475719 / 15625000) ≤ -Real.log (200000 / 322713) ∧
    -Real.log (200000 / 322713) ≤ (478446017 / 1000000000) := by
  have h := checkLog_sound (w := (122713 / 522713)) (n := 12)
    (lo := (7475719 / 15625000)) (hi := (478446017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((322713 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(322713 / 200000) = 1/(200000 / 322713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14889 : Bounds (7475719 / 15625000) (478446017 / 1000000000) (Real.log (322713 / 200000)) := by
  have h := reflection_log_14889_neg
  have he : Real.log (322713 / 200000) = -Real.log (200000 / 322713) := by
    rw [show ((322713 / 200000) : ℝ) = ((200000 / 322713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14890_neg : (2376979 / 2500000) ≤ -Real.log (77287 / 200000) ∧
    -Real.log (77287 / 200000) ≤ (475395801 / 500000000) := by
  have h := checkLog_sound (w := (22713 / 177287)) (n := 12)
    (lo := (12882221 / 50000000)) (hi := (257644421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 77287) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 77287) = 1/(77287 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14890 : Bounds (-475395801 / 500000000) (-2376979 / 2500000) (Real.log (77287 / 200000)) := by
  have h := reflection_log_14890_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14891_neg : (29521599 / 62500000) ≤ -Real.log (24941519631 / 40000000000) ∧
    -Real.log (24941519631 / 40000000000) ≤ (94469117 / 200000000) := by
  have h := checkLog_sound (w := (15058480369 / 64941519631)) (n := 12)
    (lo := (29521599 / 62500000)) (hi := (94469117 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 24941519631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 24941519631) = 1/(24941519631 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14891 : Bounds (-94469117 / 200000000) (-29521599 / 62500000) (Real.log (24941519631 / 40000000000)) := by
  have h := reflection_log_14891_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14892_neg : (14647829 / 31250000) ≤ -Real.log (156449048679 / 250000000000) ∧
    -Real.log (156449048679 / 250000000000) ≤ (468730529 / 1000000000) := by
  have h := checkLog_sound (w := (93550951321 / 406449048679)) (n := 12)
    (lo := (14647829 / 31250000)) (hi := (468730529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 156449048679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 156449048679) = 1/(156449048679 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14892 : Bounds (-468730529 / 1000000000) (-14647829 / 31250000) (Real.log (156449048679 / 250000000000)) := by
  have h := reflection_log_14892_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14893_neg : (177917109 / 125000000) ≤ -Real.log (500000000000 / 2075474273587) ∧
    -Real.log (500000000000 / 2075474273587) ≤ (2277339 / 1600000) := by
  have h := checkLog_sound (w := (75474273587 / 4075474273587)) (n := 12)
    (lo := (2315157 / 62500000)) (hi := (37042513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2075474273587 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2075474273587 / 2000000000000) = 1/(500000000000 / 2075474273587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14893 : Bounds (177917109 / 125000000) (2277339 / 1600000) (Real.log (2075474273587 / 500000000000)) := by
  have h := reflection_log_14893_neg
  have he : Real.log (2075474273587 / 500000000000) = -Real.log (500000000000 / 2075474273587) := by
    rw [show ((2075474273587 / 500000000000) : ℝ) = ((500000000000 / 2075474273587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14894_neg : (89327351 / 62500000) ≤ -Real.log (500000000000 / 2087757320119) ∧
    -Real.log (500000000000 / 2087757320119) ≤ (1429237619 / 1000000000) := by
  have h := checkLog_sound (w := (87757320119 / 4087757320119)) (n := 12)
    (lo := (5367907 / 125000000)) (hi := (42943257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2087757320119 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2087757320119 / 2000000000000) = 1/(500000000000 / 2087757320119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14894 : Bounds (89327351 / 62500000) (1429237619 / 1000000000) (Real.log (2087757320119 / 500000000000)) := by
  have h := reflection_log_14894_neg
  have he : Real.log (2087757320119 / 500000000000) = -Real.log (500000000000 / 2087757320119) := by
    rw [show ((2087757320119 / 500000000000) : ℝ) = ((500000000000 / 2087757320119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14895_neg : (2043878627 / 500000000) ≤ -Real.log (50000000000 / 2980303030303) ∧
    -Real.log (50000000000 / 2980303030303) ≤ (204387863 / 50000000) := by
  have h := checkLog_sound (w := (1380303030303 / 4580303030303)) (n := 12)
    (lo := (311010677 / 500000000)) (hi := (124404271 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2980303030303 / 1600000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2980303030303 / 1600000000000) = 1/(50000000000 / 2980303030303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14895 : Bounds (2043878627 / 500000000) (204387863 / 50000000) (Real.log (2980303030303 / 50000000000)) := by
  have h := reflection_log_14895_neg
  have he : Real.log (2980303030303 / 50000000000) = -Real.log (50000000000 / 2980303030303) := by
    rw [show ((2980303030303 / 50000000000) : ℝ) = ((50000000000 / 2980303030303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14896_neg : (1029759293 / 250000000) ≤ -Real.log (2 / 123) ∧
    -Real.log (2 / 123) ≤ (2059518589 / 500000000) := by
  have h := checkLog_sound (w := (59 / 187)) (n := 12)
    (lo := (81662659 / 125000000)) (hi := (653301273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123 / 64) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(123 / 64) = 1/(2 / 123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14896 : Bounds (1029759293 / 250000000) (2059518589 / 500000000) (Real.log (123 / 2)) := by
  have h := reflection_log_14896_neg
  have he : Real.log (123 / 2) = -Real.log (2 / 123) := by
    rw [show ((123 / 2) : ℝ) = ((2 / 123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14897_neg : (677525799 / 1000000000) ≤ -Real.log (1000 / 1969) ∧
    -Real.log (1000 / 1969) ≤ (3387629 / 5000000) := by
  have h := checkLog_sound (w := (969 / 2969)) (n := 12)
    (lo := (677525799 / 1000000000)) (hi := (3387629 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1969 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1969 / 1000) = 1/(1000 / 1969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14897 : Bounds (677525799 / 1000000000) (3387629 / 5000000) (Real.log (1969 / 1000)) := by
  have h := reflection_log_14897_neg
  have he : Real.log (1969 / 1000) = -Real.log (1000 / 1969) := by
    rw [show ((1969 / 1000) : ℝ) = ((1000 / 1969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14898_neg : (3473768071 / 1000000000) ≤ -Real.log (31 / 1000) ∧
    -Real.log (31 / 1000) ≤ (3473768077 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 249)) (n := 12)
    (lo := (8032171 / 1000000000)) (hi := (2008043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 124) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 124) = 1/(31 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14898 : Bounds (-3473768077 / 1000000000) (-3473768071 / 1000000000) (Real.log (31 / 1000)) := by
  have h := reflection_log_14898_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14899_neg : (96853 / 100000000) ≤ -Real.log (1000000 / 1000969) ∧
    -Real.log (1000000 / 1000969) ≤ (968531 / 1000000000) := by
  have h := checkLog_sound (w := (969 / 2000969)) (n := 12)
    (lo := (96853 / 100000000)) (hi := (968531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000969 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000969 / 1000000) = 1/(1000000 / 1000969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14899 : Bounds (96853 / 100000000) (968531 / 1000000000) (Real.log (1000969 / 1000000)) := by
  have h := reflection_log_14899_neg
  have he : Real.log (1000969 / 1000000) = -Real.log (1000000 / 1000969) := by
    rw [show ((1000969 / 1000000) : ℝ) = ((1000000 / 1000969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14900_neg : (969469 / 1000000000) ≤ -Real.log (999031 / 1000000) ∧
    -Real.log (999031 / 1000000) ≤ (96947 / 100000000) := by
  have h := checkLog_sound (w := (969 / 1999031)) (n := 12)
    (lo := (969469 / 1000000000)) (hi := (96947 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999031) = 1/(999031 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14900 : Bounds (-96947 / 100000000) (-969469 / 1000000000) (Real.log (999031 / 1000000)) := by
  have h := reflection_log_14900_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14901_neg : (4780431 / 10000000) ≤ -Real.log (200000 / 322583) ∧
    -Real.log (200000 / 322583) ≤ (478043101 / 1000000000) := by
  have h := checkLog_sound (w := (122583 / 522583)) (n := 12)
    (lo := (4780431 / 10000000)) (hi := (478043101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((322583 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(322583 / 200000) = 1/(200000 / 322583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14901 : Bounds (4780431 / 10000000) (478043101 / 1000000000) (Real.log (322583 / 200000)) := by
  have h := reflection_log_14901_neg
  have he : Real.log (322583 / 200000) = -Real.log (200000 / 322583) := by
    rw [show ((322583 / 200000) : ℝ) = ((200000 / 322583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14902_neg : (949110971 / 1000000000) ≤ -Real.log (77417 / 200000) ∧
    -Real.log (77417 / 200000) ≤ (949110973 / 1000000000) := by
  have h := checkLog_sound (w := (22583 / 177417)) (n := 12)
    (lo := (255963791 / 1000000000)) (hi := (15997737 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 77417) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 77417) = 1/(77417 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14902 : Bounds (-949110973 / 1000000000) (-949110971 / 1000000000) (Real.log (77417 / 200000)) := by
  have h := reflection_log_14902_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14903_neg : (95837763 / 200000000) ≤ -Real.log (250000 / 403691) ∧
    -Real.log (250000 / 403691) ≤ (29949301 / 62500000) := by
  have h := checkLog_sound (w := (153691 / 653691)) (n := 12)
    (lo := (95837763 / 200000000)) (hi := (29949301 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((403691 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(403691 / 250000) = 1/(250000 / 403691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14903 : Bounds (95837763 / 200000000) (29949301 / 62500000) (Real.log (403691 / 250000)) := by
  have h := reflection_log_14903_neg
  have he : Real.log (403691 / 250000) = -Real.log (250000 / 403691) := by
    rw [show ((403691 / 250000) : ℝ) = ((250000 / 403691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14904_neg : (119237393 / 125000000) ≤ -Real.log (96309 / 250000) ∧
    -Real.log (96309 / 250000) ≤ (476949573 / 500000000) := by
  have h := checkLog_sound (w := (28691 / 221309)) (n := 12)
    (lo := (65187991 / 250000000)) (hi := (52150393 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 96309) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 96309) = 1/(96309 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14904 : Bounds (-476949573 / 500000000) (-119237393 / 125000000) (Real.log (96309 / 250000)) := by
  have h := reflection_log_14904_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14905_neg : (474710329 / 1000000000) ≤ -Real.log (38879076519 / 62500000000) ∧
    -Real.log (38879076519 / 62500000000) ≤ (47471033 / 100000000) := by
  have h := checkLog_sound (w := (23620923481 / 101379076519)) (n := 12)
    (lo := (474710329 / 1000000000)) (hi := (47471033 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 38879076519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 38879076519) = 1/(38879076519 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14905 : Bounds (-47471033 / 100000000) (-474710329 / 1000000000) (Real.log (38879076519 / 62500000000)) := by
  have h := reflection_log_14905_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14906_neg : (47106787 / 100000000) ≤ -Real.log (24973408111 / 40000000000) ∧
    -Real.log (24973408111 / 40000000000) ≤ (471067871 / 1000000000) := by
  have h := checkLog_sound (w := (15026591889 / 64973408111)) (n := 12)
    (lo := (47106787 / 100000000)) (hi := (471067871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 24973408111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 24973408111) = 1/(24973408111 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14906 : Bounds (-471067871 / 1000000000) (-47106787 / 100000000) (Real.log (24973408111 / 40000000000)) := by
  have h := reflection_log_14906_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14907_neg : (1427154071 / 1000000000) ≤ -Real.log (31250000000 / 130213244507) ∧
    -Real.log (31250000000 / 130213244507) ≤ (713577037 / 500000000) := by
  have h := checkLog_sound (w := (5213244507 / 255213244507)) (n := 12)
    (lo := (40859711 / 1000000000)) (hi := (638433 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((130213244507 / 125000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(130213244507 / 125000000000) = 1/(31250000000 / 130213244507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14907 : Bounds (1427154071 / 1000000000) (713577037 / 500000000) (Real.log (130213244507 / 31250000000)) := by
  have h := reflection_log_14907_neg
  have he : Real.log (130213244507 / 31250000000) = -Real.log (31250000000 / 130213244507) := by
    rw [show ((130213244507 / 31250000000) : ℝ) = ((31250000000 / 130213244507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14908_neg : (35827199 / 25000000) ≤ -Real.log (62500000000 / 261976424841) ∧
    -Real.log (62500000000 / 261976424841) ≤ (1433087963 / 1000000000) := by
  have h := checkLog_sound (w := (11976424841 / 511976424841)) (n := 12)
    (lo := (14623 / 312500)) (hi := (46793601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((261976424841 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(261976424841 / 250000000000) = 1/(62500000000 / 261976424841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14908 : Bounds (35827199 / 25000000) (1433087963 / 1000000000) (Real.log (261976424841 / 62500000000)) := by
  have h := reflection_log_14908_neg
  have he : Real.log (261976424841 / 62500000000) = -Real.log (62500000000 / 261976424841) := by
    rw [show ((261976424841 / 62500000000) : ℝ) = ((62500000000 / 261976424841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14909_neg : (4151293871 / 1000000000) ≤ -Real.log (50000000000 / 3175806451613) ∧
    -Real.log (50000000000 / 3175806451613) ≤ (4151293877 / 1000000000) := by
  have h := checkLog_sound (w := (1575806451613 / 4775806451613)) (n := 12)
    (lo := (685557971 / 1000000000)) (hi := (171389493 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3175806451613 / 1600000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3175806451613 / 1600000000000) = 1/(50000000000 / 3175806451613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14909 : Bounds (4151293871 / 1000000000) (4151293877 / 1000000000) (Real.log (3175806451613 / 50000000000)) := by
  have h := reflection_log_14909_neg
  have he : Real.log (3175806451613 / 50000000000) = -Real.log (50000000000 / 3175806451613) := by
    rw [show ((3175806451613 / 50000000000) : ℝ) = ((50000000000 / 3175806451613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14910_neg : (339016771 / 500000000) ≤ -Real.log (100 / 197) ∧
    -Real.log (100 / 197) ≤ (678033543 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 297)) (n := 12)
    (lo := (339016771 / 500000000)) (hi := (678033543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197 / 100) = 1/(100 / 197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14910 : Bounds (339016771 / 500000000) (678033543 / 1000000000) (Real.log (197 / 100)) := by
  have h := reflection_log_14910_neg
  have he : Real.log (197 / 100) = -Real.log (100 / 197) := by
    rw [show ((197 / 100) : ℝ) = ((100 / 197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14911_neg : (1753278947 / 500000000) ≤ -Real.log (3 / 100) ∧
    -Real.log (3 / 100) ≤ (35065579 / 10000000) := by
  have h := checkLog_sound (w := (1 / 49)) (n := 12)
    (lo := (20410997 / 500000000)) (hi := (8164399 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 24) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(25 / 24) = 1/(3 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14911 : Bounds (-35065579 / 10000000) (-1753278947 / 500000000) (Real.log (3 / 100)) := by
  have h := reflection_log_14911_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0233 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14912_neg : (969529 / 1000000000) ≤ -Real.log (100000 / 100097) ∧
    -Real.log (100000 / 100097) ≤ (96953 / 100000000) := by
  have h := checkLog_sound (w := (97 / 200097)) (n := 12)
    (lo := (969529 / 1000000000)) (hi := (96953 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100097 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100097 / 100000) = 1/(100000 / 100097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14912 : Bounds (969529 / 1000000000) (96953 / 100000000) (Real.log (100097 / 100000)) := by
  have h := reflection_log_14912_neg
  have he : Real.log (100097 / 100000) = -Real.log (100000 / 100097) := by
    rw [show ((100097 / 100000) : ℝ) = ((100000 / 100097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14913_neg : (97047 / 100000000) ≤ -Real.log (99903 / 100000) ∧
    -Real.log (99903 / 100000) ≤ (970471 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 199903)) (n := 12)
    (lo := (97047 / 100000000)) (hi := (970471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99903) = 1/(99903 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14913 : Bounds (-970471 / 1000000000) (-97047 / 100000000) (Real.log (99903 / 100000)) := by
  have h := reflection_log_14913_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14914_neg : (239393409 / 500000000) ≤ -Real.log (200000 / 322823) ∧
    -Real.log (200000 / 322823) ≤ (478786819 / 1000000000) := by
  have h := checkLog_sound (w := (122823 / 522823)) (n := 12)
    (lo := (239393409 / 500000000)) (hi := (478786819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((322823 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(322823 / 200000) = 1/(200000 / 322823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14914 : Bounds (239393409 / 500000000) (478786819 / 1000000000) (Real.log (322823 / 200000)) := by
  have h := reflection_log_14914_neg
  have he : Real.log (322823 / 200000) = -Real.log (200000 / 322823) := by
    rw [show ((322823 / 200000) : ℝ) = ((200000 / 322823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14915_neg : (23805397 / 25000000) ≤ -Real.log (77177 / 200000) ∧
    -Real.log (77177 / 200000) ≤ (476107941 / 500000000) := by
  have h := checkLog_sound (w := (22823 / 177177)) (n := 12)
    (lo := (2590687 / 10000000)) (hi := (259068701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 77177) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 77177) = 1/(77177 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14915 : Bounds (-476107941 / 500000000) (-23805397 / 25000000) (Real.log (77177 / 200000)) := by
  have h := reflection_log_14915_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14916_neg : (239968007 / 500000000) ≤ -Real.log (1000000 / 1615971) ∧
    -Real.log (1000000 / 1615971) ≤ (95987203 / 200000000) := by
  have h := checkLog_sound (w := (615971 / 2615971)) (n := 12)
    (lo := (239968007 / 500000000)) (hi := (95987203 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1615971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1615971 / 1000000) = 1/(1000000 / 1615971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14916 : Bounds (239968007 / 500000000) (95987203 / 200000000) (Real.log (1615971 / 1000000)) := by
  have h := reflection_log_14916_neg
  have he : Real.log (1615971 / 1000000) = -Real.log (1000000 / 1615971) := by
    rw [show ((1615971 / 1000000) : ℝ) = ((1000000 / 1615971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14917_neg : (957037207 / 1000000000) ≤ -Real.log (384029 / 1000000) ∧
    -Real.log (384029 / 1000000) ≤ (957037209 / 1000000000) := by
  have h := checkLog_sound (w := (115971 / 884029)) (n := 12)
    (lo := (263890027 / 1000000000)) (hi := (65972507 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 384029) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 384029) = 1/(384029 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14917 : Bounds (-957037209 / 1000000000) (-957037207 / 1000000000) (Real.log (384029 / 1000000)) := by
  have h := reflection_log_14917_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14918_neg : (238550597 / 500000000) ≤ -Real.log (620579727159 / 1000000000000) ∧
    -Real.log (620579727159 / 1000000000000) ≤ (95420239 / 200000000) := by
  have h := checkLog_sound (w := (379420272841 / 1620579727159)) (n := 12)
    (lo := (238550597 / 500000000)) (hi := (95420239 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 620579727159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 620579727159) = 1/(620579727159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14918 : Bounds (-95420239 / 200000000) (-238550597 / 500000000) (Real.log (620579727159 / 1000000000000)) := by
  have h := reflection_log_14918_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14919_neg : (236714531 / 500000000) ≤ -Real.log (24914510671 / 40000000000) ∧
    -Real.log (24914510671 / 40000000000) ≤ (473429063 / 1000000000) := by
  have h := checkLog_sound (w := (15085489329 / 64914510671)) (n := 12)
    (lo := (236714531 / 500000000)) (hi := (473429063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 24914510671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 24914510671) = 1/(24914510671 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14919 : Bounds (-473429063 / 1000000000) (-236714531 / 500000000) (Real.log (24914510671 / 40000000000)) := by
  have h := reflection_log_14919_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14920_neg : (1431002699 / 1000000000) ≤ -Real.log (500000000000 / 2091445637949) ∧
    -Real.log (500000000000 / 2091445637949) ≤ (715501351 / 500000000) := by
  have h := checkLog_sound (w := (91445637949 / 4091445637949)) (n := 12)
    (lo := (44708339 / 1000000000)) (hi := (2235417 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2091445637949 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2091445637949 / 2000000000000) = 1/(500000000000 / 2091445637949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14920 : Bounds (1431002699 / 1000000000) (715501351 / 500000000) (Real.log (2091445637949 / 500000000000)) := by
  have h := reflection_log_14920_neg
  have he : Real.log (2091445637949 / 500000000000) = -Real.log (500000000000 / 2091445637949) := by
    rw [show ((2091445637949 / 500000000000) : ℝ) = ((500000000000 / 2091445637949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14921_neg : (1436973221 / 1000000000) ≤ -Real.log (250000000000 / 1051985006341) ∧
    -Real.log (250000000000 / 1051985006341) ≤ (179621653 / 125000000) := by
  have h := checkLog_sound (w := (51985006341 / 2051985006341)) (n := 12)
    (lo := (50678861 / 1000000000)) (hi := (25339431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1051985006341 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1051985006341 / 1000000000000) = 1/(250000000000 / 1051985006341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14921 : Bounds (1436973221 / 1000000000) (179621653 / 125000000) (Real.log (1051985006341 / 250000000000)) := by
  have h := reflection_log_14921_neg
  have he : Real.log (1051985006341 / 250000000000) = -Real.log (250000000000 / 1051985006341) := by
    rw [show ((1051985006341 / 250000000000) : ℝ) = ((250000000000 / 1051985006341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14922_neg : (4151293871 / 1000000000) ≤ -Real.log (500000000000 / 31758064516129) ∧
    -Real.log (500000000000 / 31758064516129) ≤ (4151293877 / 1000000000) := by
  have h := checkLog_sound (w := (15758064516129 / 47758064516129)) (n := 12)
    (lo := (685557971 / 1000000000)) (hi := (171389493 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31758064516129 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31758064516129 / 16000000000000) = 1/(500000000000 / 31758064516129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14922 : Bounds (4151293871 / 1000000000) (4151293877 / 1000000000) (Real.log (31758064516129 / 500000000000)) := by
  have h := reflection_log_14922_neg
  have he : Real.log (31758064516129 / 500000000000) = -Real.log (500000000000 / 31758064516129) := by
    rw [show ((31758064516129 / 500000000000) : ℝ) = ((500000000000 / 31758064516129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14923_neg : (1046147859 / 250000000) ≤ -Real.log (250000000000 / 16416666666667) ∧
    -Real.log (250000000000 / 16416666666667) ≤ (4184591443 / 1000000000) := by
  have h := checkLog_sound (w := (416666666667 / 32416666666667)) (n := 12)
    (lo := (6427089 / 250000000)) (hi := (25708357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16416666666667 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(16416666666667 / 16000000000000) = 1/(250000000000 / 16416666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14923 : Bounds (1046147859 / 250000000) (4184591443 / 1000000000) (Real.log (16416666666667 / 250000000000)) := by
  have h := reflection_log_14923_neg
  have he : Real.log (16416666666667 / 250000000000) = -Real.log (250000000000 / 16416666666667) := by
    rw [show ((16416666666667 / 250000000000) : ℝ) = ((250000000000 / 16416666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14924_neg : (169635257 / 250000000) ≤ -Real.log (1000 / 1971) ∧
    -Real.log (1000 / 1971) ≤ (678541029 / 1000000000) := by
  have h := checkLog_sound (w := (971 / 2971)) (n := 12)
    (lo := (169635257 / 250000000)) (hi := (678541029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1971 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1971 / 1000) = 1/(1000 / 1971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14924 : Bounds (169635257 / 250000000) (678541029 / 1000000000) (Real.log (1971 / 1000)) := by
  have h := reflection_log_14924_neg
  have he : Real.log (1971 / 1000) = -Real.log (1000 / 1971) := by
    rw [show ((1971 / 1000) : ℝ) = ((1000 / 1971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14925_neg : (1770229723 / 500000000) ≤ -Real.log (29 / 1000) ∧
    -Real.log (29 / 1000) ≤ (885114863 / 250000000) := by
  have h := checkLog_sound (w := (9 / 241)) (n := 12)
    (lo := (37361773 / 500000000)) (hi := (74723547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 116) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 116) = 1/(29 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14925 : Bounds (-885114863 / 250000000) (-1770229723 / 500000000) (Real.log (29 / 1000)) := by
  have h := reflection_log_14925_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14926_neg : (30329 / 31250000) ≤ -Real.log (1000000 / 1000971) ∧
    -Real.log (1000000 / 1000971) ≤ (970529 / 1000000000) := by
  have h := checkLog_sound (w := (971 / 2000971)) (n := 12)
    (lo := (30329 / 31250000)) (hi := (970529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000971 / 1000000) = 1/(1000000 / 1000971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14926 : Bounds (30329 / 31250000) (970529 / 1000000000) (Real.log (1000971 / 1000000)) := by
  have h := reflection_log_14926_neg
  have he : Real.log (1000971 / 1000000) = -Real.log (1000000 / 1000971) := by
    rw [show ((1000971 / 1000000) : ℝ) = ((1000000 / 1000971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14927_neg : (971471 / 1000000000) ≤ -Real.log (999029 / 1000000) ∧
    -Real.log (999029 / 1000000) ≤ (60717 / 62500000) := by
  have h := checkLog_sound (w := (971 / 1999029)) (n := 12)
    (lo := (971471 / 1000000000)) (hi := (60717 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999029) = 1/(999029 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14927 : Bounds (-60717 / 62500000) (-971471 / 1000000000) (Real.log (999029 / 1000000)) := by
  have h := reflection_log_14927_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14928_neg : (59941867 / 125000000) ≤ -Real.log (1000000 / 1615323) ∧
    -Real.log (1000000 / 1615323) ≤ (479534937 / 1000000000) := by
  have h := checkLog_sound (w := (615323 / 2615323)) (n := 12)
    (lo := (59941867 / 125000000)) (hi := (479534937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1615323 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1615323 / 1000000) = 1/(1000000 / 1615323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14928 : Bounds (59941867 / 125000000) (479534937 / 1000000000) (Real.log (1615323 / 1000000)) := by
  have h := reflection_log_14928_neg
  have he : Real.log (1615323 / 1000000) = -Real.log (1000000 / 1615323) := by
    rw [show ((1615323 / 1000000) : ℝ) = ((1000000 / 1615323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14929_neg : (955351257 / 1000000000) ≤ -Real.log (384677 / 1000000) ∧
    -Real.log (384677 / 1000000) ≤ (955351259 / 1000000000) := by
  have h := checkLog_sound (w := (115323 / 884677)) (n := 12)
    (lo := (262204077 / 1000000000)) (hi := (131102039 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 384677) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 384677) = 1/(384677 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14929 : Bounds (-955351259 / 1000000000) (-955351257 / 1000000000) (Real.log (384677 / 1000000)) := by
  have h := reflection_log_14929_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14930_neg : (480687601 / 1000000000) ≤ -Real.log (500000 / 808593) ∧
    -Real.log (500000 / 808593) ≤ (240343801 / 500000000) := by
  have h := checkLog_sound (w := (308593 / 1308593)) (n := 12)
    (lo := (480687601 / 1000000000)) (hi := (240343801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((808593 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(808593 / 500000) = 1/(500000 / 808593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14930 : Bounds (480687601 / 1000000000) (240343801 / 500000000) (Real.log (808593 / 500000)) := by
  have h := reflection_log_14930_neg
  have he : Real.log (808593 / 500000) = -Real.log (500000 / 808593) := by
    rw [show ((808593 / 500000) : ℝ) = ((500000 / 808593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14931_neg : (480103023 / 500000000) ≤ -Real.log (191407 / 500000) ∧
    -Real.log (191407 / 500000) ≤ (30006439 / 31250000) := by
  have h := checkLog_sound (w := (58593 / 441407)) (n := 12)
    (lo := (133529433 / 500000000)) (hi := (267058867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 191407) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 191407) = 1/(191407 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14931 : Bounds (-30006439 / 31250000) (-480103023 / 500000000) (Real.log (191407 / 500000)) := by
  have h := reflection_log_14931_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14932_neg : (95903689 / 200000000) ≤ -Real.log (154770360351 / 250000000000) ∧
    -Real.log (154770360351 / 250000000000) ≤ (239759223 / 500000000) := by
  have h := checkLog_sound (w := (95229639649 / 404770360351)) (n := 12)
    (lo := (95903689 / 200000000)) (hi := (239759223 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 154770360351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 154770360351) = 1/(154770360351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14932 : Bounds (-239759223 / 500000000) (-95903689 / 200000000) (Real.log (154770360351 / 250000000000)) := by
  have h := reflection_log_14932_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14933_neg : (475816321 / 1000000000) ≤ -Real.log (621377605671 / 1000000000000) ∧
    -Real.log (621377605671 / 1000000000000) ≤ (237908161 / 500000000) := by
  have h := checkLog_sound (w := (378622394329 / 1621377605671)) (n := 12)
    (lo := (475816321 / 1000000000)) (hi := (237908161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 621377605671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 621377605671) = 1/(621377605671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14933 : Bounds (-237908161 / 500000000) (-475816321 / 1000000000) (Real.log (621377605671 / 1000000000000)) := by
  have h := reflection_log_14933_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14934_neg : (1434886193 / 1000000000) ≤ -Real.log (100000000000 / 419916709343) ∧
    -Real.log (100000000000 / 419916709343) ≤ (358721549 / 250000000) := by
  have h := checkLog_sound (w := (19916709343 / 819916709343)) (n := 12)
    (lo := (48591833 / 1000000000)) (hi := (24295917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((419916709343 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(419916709343 / 400000000000) = 1/(100000000000 / 419916709343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14934 : Bounds (1434886193 / 1000000000) (358721549 / 250000000) (Real.log (419916709343 / 100000000000)) := by
  have h := reflection_log_14934_neg
  have he : Real.log (419916709343 / 100000000000) = -Real.log (100000000000 / 419916709343) := by
    rw [show ((419916709343 / 100000000000) : ℝ) = ((100000000000 / 419916709343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14935_neg : (90055853 / 62500000) ≤ -Real.log (100000000000 / 422446932453) ∧
    -Real.log (100000000000 / 422446932453) ≤ (1440893651 / 1000000000) := by
  have h := checkLog_sound (w := (22446932453 / 822446932453)) (n := 12)
    (lo := (6824911 / 125000000)) (hi := (54599289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((422446932453 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(422446932453 / 400000000000) = 1/(100000000000 / 422446932453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14935 : Bounds (90055853 / 62500000) (1440893651 / 1000000000) (Real.log (422446932453 / 100000000000)) := by
  have h := reflection_log_14935_neg
  have he : Real.log (422446932453 / 100000000000) = -Real.log (100000000000 / 422446932453) := by
    rw [show ((422446932453 / 100000000000) : ℝ) = ((100000000000 / 422446932453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14936_neg : (1046147859 / 250000000) ≤ -Real.log (500000000000 / 32833333333333) ∧
    -Real.log (500000000000 / 32833333333333) ≤ (4184591443 / 1000000000) := by
  have h := checkLog_sound (w := (833333333333 / 64833333333333)) (n := 12)
    (lo := (6427089 / 250000000)) (hi := (25708357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32833333333333 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(32833333333333 / 32000000000000) = 1/(500000000000 / 32833333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14936 : Bounds (1046147859 / 250000000) (4184591443 / 1000000000) (Real.log (32833333333333 / 500000000000)) := by
  have h := reflection_log_14936_neg
  have he : Real.log (32833333333333 / 500000000000) = -Real.log (500000000000 / 32833333333333) := by
    rw [show ((32833333333333 / 500000000000) : ℝ) = ((500000000000 / 32833333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14937_neg : (4219000473 / 1000000000) ≤ -Real.log (50000000000 / 3398275862069) ∧
    -Real.log (50000000000 / 3398275862069) ≤ (26368753 / 6250000) := by
  have h := checkLog_sound (w := (198275862069 / 6598275862069)) (n := 12)
    (lo := (60117393 / 1000000000)) (hi := (30058697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3398275862069 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(3398275862069 / 3200000000000) = 1/(50000000000 / 3398275862069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14937 : Bounds (4219000473 / 1000000000) (26368753 / 6250000) (Real.log (3398275862069 / 50000000000)) := by
  have h := reflection_log_14937_neg
  have he : Real.log (3398275862069 / 50000000000) = -Real.log (50000000000 / 3398275862069) := by
    rw [show ((3398275862069 / 50000000000) : ℝ) = ((50000000000 / 3398275862069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14938_neg : (10610129 / 15625000) ≤ -Real.log (250 / 493) ∧
    -Real.log (250 / 493) ≤ (679048257 / 1000000000) := by
  have h := checkLog_sound (w := (243 / 743)) (n := 12)
    (lo := (10610129 / 15625000)) (hi := (679048257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493 / 250) = 1/(250 / 493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14938 : Bounds (10610129 / 15625000) (679048257 / 1000000000) (Real.log (493 / 250)) := by
  have h := reflection_log_14938_neg
  have he : Real.log (493 / 250) = -Real.log (250 / 493) := by
    rw [show ((493 / 250) : ℝ) = ((250 / 493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14939_neg : (1787775383 / 500000000) ≤ -Real.log (7 / 250) ∧
    -Real.log (7 / 250) ≤ (893887693 / 250000000) := by
  have h := checkLog_sound (w := (13 / 237)) (n := 12)
    (lo := (54907433 / 500000000)) (hi := (109814867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 112) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 112) = 1/(7 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14939 : Bounds (-893887693 / 250000000) (-1787775383 / 500000000) (Real.log (7 / 250)) := by
  have h := reflection_log_14939_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14940_neg : (971527 / 1000000000) ≤ -Real.log (250000 / 250243) ∧
    -Real.log (250000 / 250243) ≤ (121441 / 125000000) := by
  have h := checkLog_sound (w := (243 / 500243)) (n := 12)
    (lo := (971527 / 1000000000)) (hi := (121441 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250243 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250243 / 250000) = 1/(250000 / 250243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14940 : Bounds (971527 / 1000000000) (121441 / 125000000) (Real.log (250243 / 250000)) := by
  have h := reflection_log_14940_neg
  have he : Real.log (250243 / 250000) = -Real.log (250000 / 250243) := by
    rw [show ((250243 / 250000) : ℝ) = ((250000 / 250243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14941_neg : (121559 / 125000000) ≤ -Real.log (249757 / 250000) ∧
    -Real.log (249757 / 250000) ≤ (972473 / 1000000000) := by
  have h := checkLog_sound (w := (243 / 499757)) (n := 12)
    (lo := (121559 / 125000000)) (hi := (972473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249757) = 1/(249757 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14941 : Bounds (-972473 / 1000000000) (-121559 / 125000000) (Real.log (249757 / 250000)) := by
  have h := reflection_log_14941_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14942_neg : (120071861 / 250000000) ≤ -Real.log (1000000 / 1616539) ∧
    -Real.log (1000000 / 1616539) ≤ (96057489 / 200000000) := by
  have h := checkLog_sound (w := (616539 / 2616539)) (n := 12)
    (lo := (120071861 / 250000000)) (hi := (96057489 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1616539 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1616539 / 1000000) = 1/(1000000 / 1616539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14942 : Bounds (120071861 / 250000000) (96057489 / 200000000) (Real.log (1616539 / 1000000)) := by
  have h := reflection_log_14942_neg
  have he : Real.log (1616539 / 1000000) = -Real.log (1000000 / 1616539) := by
    rw [show ((1616539 / 1000000) : ℝ) = ((1000000 / 1616539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14943_neg : (958517357 / 1000000000) ≤ -Real.log (383461 / 1000000) ∧
    -Real.log (383461 / 1000000) ≤ (958517359 / 1000000000) := by
  have h := checkLog_sound (w := (116539 / 883461)) (n := 12)
    (lo := (265370177 / 1000000000)) (hi := (132685089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 383461) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 383461) = 1/(383461 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14943 : Bounds (-958517359 / 1000000000) (-958517357 / 1000000000) (Real.log (383461 / 1000000)) := by
  have h := reflection_log_14943_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14944_neg : (481443567 / 1000000000) ≤ -Real.log (1000000 / 1618409) ∧
    -Real.log (1000000 / 1618409) ≤ (30090223 / 62500000) := by
  have h := checkLog_sound (w := (618409 / 2618409)) (n := 12)
    (lo := (481443567 / 1000000000)) (hi := (30090223 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1618409 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1618409 / 1000000) = 1/(1000000 / 1618409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14944 : Bounds (481443567 / 1000000000) (30090223 / 62500000) (Real.log (1618409 / 1000000)) := by
  have h := reflection_log_14944_neg
  have he : Real.log (1618409 / 1000000) = -Real.log (1000000 / 1618409) := by
    rw [show ((1618409 / 1000000) : ℝ) = ((1000000 / 1618409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14945_neg : (240851481 / 250000000) ≤ -Real.log (381591 / 1000000) ∧
    -Real.log (381591 / 1000000) ≤ (481702963 / 500000000) := by
  have h := checkLog_sound (w := (118409 / 881591)) (n := 12)
    (lo := (33782343 / 125000000)) (hi := (54051749 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 381591) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 381591) = 1/(381591 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14945 : Bounds (-481702963 / 500000000) (-240851481 / 250000000) (Real.log (381591 / 1000000)) := by
  have h := reflection_log_14945_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14946_neg : (120490589 / 250000000) ≤ -Real.log (617570308719 / 1000000000000) ∧
    -Real.log (617570308719 / 1000000000000) ≤ (481962357 / 1000000000) := by
  have h := checkLog_sound (w := (382429691281 / 1617570308719)) (n := 12)
    (lo := (120490589 / 250000000)) (hi := (481962357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 617570308719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 617570308719) = 1/(617570308719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14946 : Bounds (-481962357 / 1000000000) (-120490589 / 250000000) (Real.log (617570308719 / 1000000000000)) := by
  have h := reflection_log_14946_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14947_neg : (239114957 / 500000000) ≤ -Real.log (619879661479 / 1000000000000) ∧
    -Real.log (619879661479 / 1000000000000) ≤ (95645983 / 200000000) := by
  have h := checkLog_sound (w := (380120338521 / 1619879661479)) (n := 12)
    (lo := (239114957 / 500000000)) (hi := (95645983 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 619879661479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 619879661479) = 1/(619879661479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14947 : Bounds (-95645983 / 200000000) (-239114957 / 500000000) (Real.log (619879661479 / 1000000000000)) := by
  have h := reflection_log_14947_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14948_neg : (1438804801 / 1000000000) ≤ -Real.log (100000000000 / 421565426471) ∧
    -Real.log (100000000000 / 421565426471) ≤ (359701201 / 250000000) := by
  have h := checkLog_sound (w := (21565426471 / 821565426471)) (n := 12)
    (lo := (52510441 / 1000000000)) (hi := (26255221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((421565426471 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(421565426471 / 400000000000) = 1/(100000000000 / 421565426471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14948 : Bounds (1438804801 / 1000000000) (359701201 / 250000000) (Real.log (421565426471 / 100000000000)) := by
  have h := reflection_log_14948_neg
  have he : Real.log (421565426471 / 100000000000) = -Real.log (100000000000 / 421565426471) := by
    rw [show ((421565426471 / 100000000000) : ℝ) = ((100000000000 / 421565426471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14949_neg : (1444849491 / 1000000000) ≤ -Real.log (250000000000 / 1060303440071) ∧
    -Real.log (250000000000 / 1060303440071) ≤ (722424747 / 500000000) := by
  have h := checkLog_sound (w := (60303440071 / 2060303440071)) (n := 12)
    (lo := (58555131 / 1000000000)) (hi := (14638783 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1060303440071 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1060303440071 / 1000000000000) = 1/(250000000000 / 1060303440071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14949 : Bounds (1444849491 / 1000000000) (722424747 / 500000000) (Real.log (1060303440071 / 250000000000)) := by
  have h := reflection_log_14949_neg
  have he : Real.log (1060303440071 / 250000000000) = -Real.log (250000000000 / 1060303440071) := by
    rw [show ((1060303440071 / 250000000000) : ℝ) = ((250000000000 / 1060303440071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14950_neg : (4219000473 / 1000000000) ≤ -Real.log (500000000000 / 33982758620689) ∧
    -Real.log (500000000000 / 33982758620689) ≤ (26368753 / 6250000) := by
  have h := checkLog_sound (w := (1982758620689 / 65982758620689)) (n := 12)
    (lo := (60117393 / 1000000000)) (hi := (30058697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33982758620689 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(33982758620689 / 32000000000000) = 1/(500000000000 / 33982758620689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14950 : Bounds (4219000473 / 1000000000) (26368753 / 6250000) (Real.log (33982758620689 / 500000000000)) := by
  have h := reflection_log_14950_neg
  have he : Real.log (33982758620689 / 500000000000) = -Real.log (500000000000 / 33982758620689) := by
    rw [show ((33982758620689 / 500000000000) : ℝ) = ((500000000000 / 33982758620689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14951_neg : (4254599021 / 1000000000) ≤ -Real.log (250000000000 / 17607142857143) ∧
    -Real.log (250000000000 / 17607142857143) ≤ (1063649757 / 250000000) := by
  have h := checkLog_sound (w := (1607142857143 / 33607142857143)) (n := 12)
    (lo := (95715941 / 1000000000)) (hi := (47857971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17607142857143 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(17607142857143 / 16000000000000) = 1/(250000000000 / 17607142857143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14951 : Bounds (4254599021 / 1000000000) (1063649757 / 250000000) (Real.log (17607142857143 / 250000000000)) := by
  have h := reflection_log_14951_neg
  have he : Real.log (17607142857143 / 250000000000) = -Real.log (250000000000 / 17607142857143) := by
    rw [show ((17607142857143 / 250000000000) : ℝ) = ((250000000000 / 17607142857143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14952_neg : (679555227 / 1000000000) ≤ -Real.log (1000 / 1973) ∧
    -Real.log (1000 / 1973) ≤ (169888807 / 250000000) := by
  have h := checkLog_sound (w := (973 / 2973)) (n := 12)
    (lo := (679555227 / 1000000000)) (hi := (169888807 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1973 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1973 / 1000) = 1/(1000 / 1973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14952 : Bounds (679555227 / 1000000000) (169888807 / 250000000) (Real.log (1973 / 1000)) := by
  have h := reflection_log_14952_neg
  have he : Real.log (1973 / 1000) = -Real.log (1000 / 1973) := by
    rw [show ((1973 / 1000) : ℝ) = ((1000 / 1973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14953_neg : (361191841 / 100000000) ≤ -Real.log (27 / 1000) ∧
    -Real.log (27 / 1000) ≤ (225744901 / 62500000) := by
  have h := checkLog_sound (w := (17 / 233)) (n := 12)
    (lo := (14618251 / 100000000)) (hi := (146182511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 108) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 108) = 1/(27 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14953 : Bounds (-225744901 / 62500000) (-361191841 / 100000000) (Real.log (27 / 1000)) := by
  have h := reflection_log_14953_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14954_neg : (486263 / 500000000) ≤ -Real.log (1000000 / 1000973) ∧
    -Real.log (1000000 / 1000973) ≤ (972527 / 1000000000) := by
  have h := checkLog_sound (w := (973 / 2000973)) (n := 12)
    (lo := (486263 / 500000000)) (hi := (972527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000973 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000973 / 1000000) = 1/(1000000 / 1000973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14954 : Bounds (486263 / 500000000) (972527 / 1000000000) (Real.log (1000973 / 1000000)) := by
  have h := reflection_log_14954_neg
  have he : Real.log (1000973 / 1000000) = -Real.log (1000000 / 1000973) := by
    rw [show ((1000973 / 1000000) : ℝ) = ((1000000 / 1000973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14955_neg : (973473 / 1000000000) ≤ -Real.log (999027 / 1000000) ∧
    -Real.log (999027 / 1000000) ≤ (486737 / 500000000) := by
  have h := checkLog_sound (w := (973 / 1999027)) (n := 12)
    (lo := (973473 / 1000000000)) (hi := (486737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999027) = 1/(999027 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14955 : Bounds (-486737 / 500000000) (-973473 / 1000000000) (Real.log (999027 / 1000000)) := by
  have h := reflection_log_14955_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14956_neg : (1879077 / 3906250) ≤ -Real.log (500000 / 808881) ∧
    -Real.log (500000 / 808881) ≤ (481043713 / 1000000000) := by
  have h := checkLog_sound (w := (308881 / 1308881)) (n := 12)
    (lo := (1879077 / 3906250)) (hi := (481043713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((808881 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(808881 / 500000) = 1/(500000 / 808881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14956 : Bounds (1879077 / 3906250) (481043713 / 1000000000) (Real.log (808881 / 500000)) := by
  have h := reflection_log_14956_neg
  have he : Real.log (808881 / 500000) = -Real.log (500000 / 808881) := by
    rw [show ((808881 / 500000) : ℝ) = ((500000 / 808881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14957_neg : (961711827 / 1000000000) ≤ -Real.log (191119 / 500000) ∧
    -Real.log (191119 / 500000) ≤ (961711829 / 1000000000) := by
  have h := checkLog_sound (w := (58881 / 441119)) (n := 12)
    (lo := (268564647 / 1000000000)) (hi := (33570581 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 191119) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 191119) = 1/(191119 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14957 : Bounds (-961711829 / 1000000000) (-961711827 / 1000000000) (Real.log (191119 / 500000)) := by
  have h := reflection_log_14957_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14958_neg : (241101951 / 500000000) ≤ -Real.log (25000 / 40491) ∧
    -Real.log (25000 / 40491) ≤ (482203903 / 1000000000) := by
  have h := checkLog_sound (w := (15491 / 65491)) (n := 12)
    (lo := (241101951 / 500000000)) (hi := (482203903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40491 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40491 / 25000) = 1/(25000 / 40491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14958 : Bounds (241101951 / 500000000) (482203903 / 1000000000) (Real.log (40491 / 25000)) := by
  have h := reflection_log_14958_neg
  have he : Real.log (40491 / 25000) = -Real.log (25000 / 40491) := by
    rw [show ((40491 / 25000) : ℝ) = ((25000 / 40491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14959_neg : (193327421 / 200000000) ≤ -Real.log (9509 / 25000) ∧
    -Real.log (9509 / 25000) ≤ (966637107 / 1000000000) := by
  have h := checkLog_sound (w := (2991 / 22009)) (n := 12)
    (lo := (10939597 / 40000000)) (hi := (136744963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9509) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(12500 / 9509) = 1/(9509 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14959 : Bounds (-966637107 / 1000000000) (-193327421 / 200000000) (Real.log (9509 / 25000)) := by
  have h := reflection_log_14959_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14960_neg : (484433203 / 1000000000) ≤ -Real.log (385028919 / 625000000) ∧
    -Real.log (385028919 / 625000000) ≤ (121108301 / 250000000) := by
  have h := checkLog_sound (w := (239971081 / 1010028919)) (n := 12)
    (lo := (484433203 / 1000000000)) (hi := (121108301 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 385028919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 385028919) = 1/(385028919 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14960 : Bounds (-121108301 / 250000000) (-484433203 / 1000000000) (Real.log (385028919 / 625000000)) := by
  have h := reflection_log_14960_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14961_neg : (96133623 / 200000000) ≤ -Real.log (154592527839 / 250000000000) ∧
    -Real.log (154592527839 / 250000000000) ≤ (120167029 / 250000000) := by
  have h := checkLog_sound (w := (95407472161 / 404592527839)) (n := 12)
    (lo := (96133623 / 200000000)) (hi := (120167029 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 154592527839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 154592527839) = 1/(154592527839 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14961 : Bounds (-120167029 / 250000000) (-96133623 / 200000000) (Real.log (154592527839 / 250000000000)) := by
  have h := reflection_log_14961_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14962_neg : (1442755539 / 1000000000) ≤ -Real.log (500000000000 / 2116171076659) ∧
    -Real.log (500000000000 / 2116171076659) ≤ (721377771 / 500000000) := by
  have h := checkLog_sound (w := (116171076659 / 4116171076659)) (n := 12)
    (lo := (56461179 / 1000000000)) (hi := (2823059 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2116171076659 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2116171076659 / 2000000000000) = 1/(500000000000 / 2116171076659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14962 : Bounds (1442755539 / 1000000000) (721377771 / 500000000) (Real.log (2116171076659 / 500000000000)) := by
  have h := reflection_log_14962_neg
  have he : Real.log (2116171076659 / 500000000000) = -Real.log (500000000000 / 2116171076659) := by
    rw [show ((2116171076659 / 500000000000) : ℝ) = ((500000000000 / 2116171076659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14963_neg : (1448841007 / 1000000000) ≤ -Real.log (250000000000 / 1064544116101) ∧
    -Real.log (250000000000 / 1064544116101) ≤ (144884101 / 100000000) := by
  have h := checkLog_sound (w := (64544116101 / 2064544116101)) (n := 12)
    (lo := (62546647 / 1000000000)) (hi := (7818331 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1064544116101 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1064544116101 / 1000000000000) = 1/(250000000000 / 1064544116101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14963 : Bounds (1448841007 / 1000000000) (144884101 / 100000000) (Real.log (1064544116101 / 250000000000)) := by
  have h := reflection_log_14963_neg
  have he : Real.log (1064544116101 / 250000000000) = -Real.log (250000000000 / 1064544116101) := by
    rw [show ((1064544116101 / 250000000000) : ℝ) = ((250000000000 / 1064544116101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14964_neg : (4254599021 / 1000000000) ≤ -Real.log (100000000000 / 7042857142857) ∧
    -Real.log (100000000000 / 7042857142857) ≤ (1063649757 / 250000000) := by
  have h := checkLog_sound (w := (642857142857 / 13442857142857)) (n := 12)
    (lo := (95715941 / 1000000000)) (hi := (47857971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7042857142857 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7042857142857 / 6400000000000) = 1/(100000000000 / 7042857142857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14964 : Bounds (4254599021 / 1000000000) (1063649757 / 250000000) (Real.log (7042857142857 / 100000000000)) := by
  have h := reflection_log_14964_neg
  have he : Real.log (7042857142857 / 100000000000) = -Real.log (100000000000 / 7042857142857) := by
    rw [show ((7042857142857 / 100000000000) : ℝ) = ((100000000000 / 7042857142857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14965_neg : (1072868409 / 250000000) ≤ -Real.log (250000000000 / 18268518518519) ∧
    -Real.log (250000000000 / 18268518518519) ≤ (4291473643 / 1000000000) := by
  have h := checkLog_sound (w := (2268518518519 / 34268518518519)) (n := 12)
    (lo := (33147639 / 250000000)) (hi := (132590557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18268518518519 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(18268518518519 / 16000000000000) = 1/(250000000000 / 18268518518519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14965 : Bounds (1072868409 / 250000000) (4291473643 / 1000000000) (Real.log (18268518518519 / 250000000000)) := by
  have h := reflection_log_14965_neg
  have he : Real.log (18268518518519 / 250000000000) = -Real.log (250000000000 / 18268518518519) := by
    rw [show ((18268518518519 / 250000000000) : ℝ) = ((250000000000 / 18268518518519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14966_neg : (680061941 / 1000000000) ≤ -Real.log (500 / 987) ∧
    -Real.log (500 / 987) ≤ (340030971 / 500000000) := by
  have h := checkLog_sound (w := (487 / 1487)) (n := 12)
    (lo := (680061941 / 1000000000)) (hi := (340030971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987 / 500) = 1/(500 / 987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14966 : Bounds (680061941 / 1000000000) (340030971 / 500000000) (Real.log (987 / 500)) := by
  have h := reflection_log_14966_neg
  have he : Real.log (987 / 500) = -Real.log (500 / 987) := by
    rw [show ((987 / 500) : ℝ) = ((500 / 987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14967_neg : (1824829369 / 500000000) ≤ -Real.log (13 / 500) ∧
    -Real.log (13 / 500) ≤ (456207343 / 125000000) := by
  have h := checkLog_sound (w := (21 / 229)) (n := 12)
    (lo := (91961419 / 500000000)) (hi := (183922839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 104) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 104) = 1/(13 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14967 : Bounds (-456207343 / 125000000) (-1824829369 / 500000000) (Real.log (13 / 500)) := by
  have h := reflection_log_14967_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14968_neg : (38941 / 40000000) ≤ -Real.log (500000 / 500487) ∧
    -Real.log (500000 / 500487) ≤ (486763 / 500000000) := by
  have h := checkLog_sound (w := (487 / 1000487)) (n := 12)
    (lo := (38941 / 40000000)) (hi := (486763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500487 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500487 / 500000) = 1/(500000 / 500487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14968 : Bounds (38941 / 40000000) (486763 / 500000000) (Real.log (500487 / 500000)) := by
  have h := reflection_log_14968_neg
  have he : Real.log (500487 / 500000) = -Real.log (500000 / 500487) := by
    rw [show ((500487 / 500000) : ℝ) = ((500000 / 500487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14969_neg : (487237 / 500000000) ≤ -Real.log (499513 / 500000) ∧
    -Real.log (499513 / 500000) ≤ (38979 / 40000000) := by
  have h := checkLog_sound (w := (487 / 999513)) (n := 12)
    (lo := (487237 / 500000000)) (hi := (38979 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499513) = 1/(499513 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14969 : Bounds (-38979 / 40000000) (-487237 / 500000000) (Real.log (499513 / 500000)) := by
  have h := reflection_log_14969_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14970_neg : (60225621 / 125000000) ≤ -Real.log (500000 / 809497) ∧
    -Real.log (500000 / 809497) ≤ (481804969 / 1000000000) := by
  have h := checkLog_sound (w := (309497 / 1309497)) (n := 12)
    (lo := (60225621 / 125000000)) (hi := (481804969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((809497 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(809497 / 500000) = 1/(500000 / 809497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14970 : Bounds (60225621 / 125000000) (481804969 / 1000000000) (Real.log (809497 / 500000)) := by
  have h := reflection_log_14970_neg
  have he : Real.log (809497 / 500000) = -Real.log (500000 / 809497) := by
    rw [show ((809497 / 500000) : ℝ) = ((500000 / 809497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14971_neg : (192988031 / 200000000) ≤ -Real.log (190503 / 500000) ∧
    -Real.log (190503 / 500000) ≤ (964940157 / 1000000000) := by
  have h := checkLog_sound (w := (59497 / 440503)) (n := 12)
    (lo := (10871719 / 40000000)) (hi := (16987061 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 190503) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 190503) = 1/(190503 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14971 : Bounds (-964940157 / 1000000000) (-192988031 / 200000000) (Real.log (190503 / 500000)) := by
  have h := reflection_log_14971_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14972_neg : (482969211 / 1000000000) ≤ -Real.log (12500 / 20261) ∧
    -Real.log (12500 / 20261) ≤ (120742303 / 250000000) := by
  have h := checkLog_sound (w := (7761 / 32761)) (n := 12)
    (lo := (482969211 / 1000000000)) (hi := (120742303 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20261 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20261 / 12500) = 1/(12500 / 20261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14972 : Bounds (482969211 / 1000000000) (120742303 / 250000000) (Real.log (20261 / 12500)) := by
  have h := reflection_log_14972_neg
  have he : Real.log (20261 / 12500) = -Real.log (12500 / 20261) := by
    rw [show ((20261 / 12500) : ℝ) = ((12500 / 20261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14973_neg : (387961 / 400000) ≤ -Real.log (4739 / 12500) ∧
    -Real.log (4739 / 12500) ≤ (484951251 / 500000000) := by
  have h := checkLog_sound (w := (1511 / 10989)) (n := 12)
    (lo := (6918883 / 25000000)) (hi := (276755321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4739) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(6250 / 4739) = 1/(4739 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14973 : Bounds (-484951251 / 500000000) (-387961 / 400000) (Real.log (4739 / 12500)) := by
  have h := reflection_log_14973_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14974_neg : (486933289 / 1000000000) ≤ -Real.log (96016879 / 156250000) ∧
    -Real.log (96016879 / 156250000) ≤ (48693329 / 100000000) := by
  have h := checkLog_sound (w := (60233121 / 252266879)) (n := 12)
    (lo := (486933289 / 1000000000)) (hi := (48693329 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 96016879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 96016879) = 1/(96016879 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14974 : Bounds (-48693329 / 100000000) (-486933289 / 1000000000) (Real.log (96016879 / 156250000)) := by
  have h := reflection_log_14974_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14975_neg : (483135187 / 1000000000) ≤ -Real.log (154211606991 / 250000000000) ∧
    -Real.log (154211606991 / 250000000000) ≤ (120783797 / 250000000) := by
  have h := checkLog_sound (w := (95788393009 / 404211606991)) (n := 12)
    (lo := (483135187 / 1000000000)) (hi := (120783797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 154211606991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 154211606991) = 1/(154211606991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14975 : Bounds (-120783797 / 250000000) (-483135187 / 1000000000) (Real.log (154211606991 / 250000000000)) := by
  have h := reflection_log_14975_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0234 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14976_neg : (1446745123 / 1000000000) ≤ -Real.log (100000000000 / 424926116649) ∧
    -Real.log (100000000000 / 424926116649) ≤ (723372563 / 500000000) := by
  have h := checkLog_sound (w := (24926116649 / 824926116649)) (n := 12)
    (lo := (60450763 / 1000000000)) (hi := (15112691 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((424926116649 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(424926116649 / 400000000000) = 1/(100000000000 / 424926116649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14976 : Bounds (1446745123 / 1000000000) (723372563 / 500000000) (Real.log (424926116649 / 100000000000)) := by
  have h := reflection_log_14976_neg
  have he : Real.log (424926116649 / 100000000000) = -Real.log (100000000000 / 424926116649) := by
    rw [show ((424926116649 / 100000000000) : ℝ) = ((100000000000 / 424926116649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14977_neg : (1452871711 / 1000000000) ≤ -Real.log (500000000000 / 2137687275797) ∧
    -Real.log (500000000000 / 2137687275797) ≤ (726435857 / 500000000) := by
  have h := checkLog_sound (w := (137687275797 / 4137687275797)) (n := 12)
    (lo := (66577351 / 1000000000)) (hi := (8322169 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2137687275797 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2137687275797 / 2000000000000) = 1/(500000000000 / 2137687275797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14977 : Bounds (1452871711 / 1000000000) (726435857 / 500000000) (Real.log (2137687275797 / 500000000000)) := by
  have h := reflection_log_14977_neg
  have he : Real.log (2137687275797 / 500000000000) = -Real.log (500000000000 / 2137687275797) := by
    rw [show ((2137687275797 / 500000000000) : ℝ) = ((500000000000 / 2137687275797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14978_neg : (1072868409 / 250000000) ≤ -Real.log (500000000000 / 36537037037037) ∧
    -Real.log (500000000000 / 36537037037037) ≤ (4291473643 / 1000000000) := by
  have h := checkLog_sound (w := (4537037037037 / 68537037037037)) (n := 12)
    (lo := (33147639 / 250000000)) (hi := (132590557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36537037037037 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(36537037037037 / 32000000000000) = 1/(500000000000 / 36537037037037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14978 : Bounds (1072868409 / 250000000) (4291473643 / 1000000000) (Real.log (36537037037037 / 500000000000)) := by
  have h := reflection_log_14978_neg
  have he : Real.log (36537037037037 / 500000000000) = -Real.log (500000000000 / 36537037037037) := by
    rw [show ((36537037037037 / 500000000000) : ℝ) = ((500000000000 / 36537037037037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14979_neg : (2164860339 / 500000000) ≤ -Real.log (500000000000 / 37961538461539) ∧
    -Real.log (500000000000 / 37961538461539) ≤ (865944137 / 200000000) := by
  have h := checkLog_sound (w := (5961538461539 / 69961538461539)) (n := 12)
    (lo := (85418799 / 500000000)) (hi := (170837599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37961538461539 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(37961538461539 / 32000000000000) = 1/(500000000000 / 37961538461539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14979 : Bounds (2164860339 / 500000000) (865944137 / 200000000) (Real.log (37961538461539 / 500000000000)) := by
  have h := reflection_log_14979_neg
  have he : Real.log (37961538461539 / 500000000000) = -Real.log (500000000000 / 37961538461539) := by
    rw [show ((37961538461539 / 500000000000) : ℝ) = ((500000000000 / 37961538461539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14980_neg : (340284199 / 500000000) ≤ -Real.log (40 / 79) ∧
    -Real.log (40 / 79) ≤ (680568399 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 119)) (n := 12)
    (lo := (340284199 / 500000000)) (hi := (680568399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79 / 40) = 1/(40 / 79) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14980 : Bounds (340284199 / 500000000) (680568399 / 1000000000) (Real.log (79 / 40)) := by
  have h := reflection_log_14980_neg
  have he : Real.log (79 / 40) = -Real.log (40 / 79) := by
    rw [show ((79 / 40) : ℝ) = ((40 / 79) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14981_neg : (3688879451 / 1000000000) ≤ -Real.log (1 / 40) ∧
    -Real.log (1 / 40) ≤ (3688879457 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 9)) (n := 12)
    (lo := (223143551 / 1000000000)) (hi := (1743309 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 4) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5 / 4) = 1/(1 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14981 : Bounds (-3688879457 / 1000000000) (-3688879451 / 1000000000) (Real.log (1 / 40)) := by
  have h := reflection_log_14981_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14982_neg : (243631 / 250000000) ≤ -Real.log (40000 / 40039) ∧
    -Real.log (40000 / 40039) ≤ (38981 / 40000000) := by
  have h := checkLog_sound (w := (39 / 80039)) (n := 12)
    (lo := (243631 / 250000000)) (hi := (38981 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40039 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40039 / 40000) = 1/(40000 / 40039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14982 : Bounds (243631 / 250000000) (38981 / 40000000) (Real.log (40039 / 40000)) := by
  have h := reflection_log_14982_neg
  have he : Real.log (40039 / 40000) = -Real.log (40000 / 40039) := by
    rw [show ((40039 / 40000) : ℝ) = ((40000 / 40039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14983_neg : (39019 / 40000000) ≤ -Real.log (39961 / 40000) ∧
    -Real.log (39961 / 40000) ≤ (243869 / 250000000) := by
  have h := checkLog_sound (w := (39 / 79961)) (n := 12)
    (lo := (39019 / 40000000)) (hi := (243869 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 39961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 39961) = 1/(39961 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14983 : Bounds (-243869 / 250000000) (-39019 / 40000000) (Real.log (39961 / 40000)) := by
  have h := reflection_log_14983_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14984_neg : (301607 / 625000) ≤ -Real.log (200000 / 324047) ∧
    -Real.log (200000 / 324047) ≤ (482571201 / 1000000000) := by
  have h := checkLog_sound (w := (124047 / 524047)) (n := 12)
    (lo := (301607 / 625000)) (hi := (482571201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((324047 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(324047 / 200000) = 1/(200000 / 324047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14984 : Bounds (301607 / 625000) (482571201 / 1000000000) (Real.log (324047 / 200000)) := by
  have h := reflection_log_14984_neg
  have he : Real.log (324047 / 200000) = -Real.log (200000 / 324047) := by
    rw [show ((324047 / 200000) : ℝ) = ((200000 / 324047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14985_neg : (484101319 / 500000000) ≤ -Real.log (75953 / 200000) ∧
    -Real.log (75953 / 200000) ≤ (12102533 / 12500000) := by
  have h := checkLog_sound (w := (24047 / 175953)) (n := 12)
    (lo := (137527729 / 500000000)) (hi := (275055459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 75953) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 75953) = 1/(75953 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14985 : Bounds (-12102533 / 12500000) (-484101319 / 500000000) (Real.log (75953 / 200000)) := by
  have h := reflection_log_14985_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14986_neg : (483739483 / 1000000000) ≤ -Real.log (1000000 / 1622129) ∧
    -Real.log (1000000 / 1622129) ≤ (120934871 / 250000000) := by
  have h := checkLog_sound (w := (622129 / 2622129)) (n := 12)
    (lo := (483739483 / 1000000000)) (hi := (120934871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1622129 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1622129 / 1000000) = 1/(1000000 / 1622129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14986 : Bounds (483739483 / 1000000000) (120934871 / 250000000) (Real.log (1622129 / 1000000)) := by
  have h := reflection_log_14986_neg
  have he : Real.log (1622129 / 1000000) = -Real.log (1000000 / 1622129) := by
    rw [show ((1622129 / 1000000) : ℝ) = ((1000000 / 1622129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14987_neg : (97320241 / 100000000) ≤ -Real.log (377871 / 1000000) ∧
    -Real.log (377871 / 1000000) ≤ (243300603 / 250000000) := by
  have h := checkLog_sound (w := (122129 / 877871)) (n := 12)
    (lo := (28005523 / 100000000)) (hi := (280055231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 377871) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 377871) = 1/(377871 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14987 : Bounds (-243300603 / 250000000) (-97320241 / 100000000) (Real.log (377871 / 1000000)) := by
  have h := reflection_log_14987_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14988_neg : (489462927 / 1000000000) ≤ -Real.log (612955507359 / 1000000000000) ∧
    -Real.log (612955507359 / 1000000000000) ≤ (30591433 / 62500000) := by
  have h := checkLog_sound (w := (387044492641 / 1612955507359)) (n := 12)
    (lo := (489462927 / 1000000000)) (hi := (30591433 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 612955507359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 612955507359) = 1/(612955507359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14988 : Bounds (-30591433 / 62500000) (-489462927 / 1000000000) (Real.log (612955507359 / 1000000000000)) := by
  have h := reflection_log_14988_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14989_neg : (242815719 / 500000000) ≤ -Real.log (24612341791 / 40000000000) ∧
    -Real.log (24612341791 / 40000000000) ≤ (485631439 / 1000000000) := by
  have h := checkLog_sound (w := (15387658209 / 64612341791)) (n := 12)
    (lo := (242815719 / 500000000)) (hi := (485631439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 24612341791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 24612341791) = 1/(24612341791 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14989 : Bounds (-485631439 / 1000000000) (-242815719 / 500000000) (Real.log (24612341791 / 40000000000)) := by
  have h := reflection_log_14989_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14990_neg : (1450773837 / 1000000000) ≤ -Real.log (500000000000 / 2133207378247) ∧
    -Real.log (500000000000 / 2133207378247) ≤ (18134673 / 12500000) := by
  have h := checkLog_sound (w := (133207378247 / 4133207378247)) (n := 12)
    (lo := (64479477 / 1000000000)) (hi := (32239739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2133207378247 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2133207378247 / 2000000000000) = 1/(500000000000 / 2133207378247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14990 : Bounds (1450773837 / 1000000000) (18134673 / 12500000) (Real.log (2133207378247 / 500000000000)) := by
  have h := reflection_log_14990_neg
  have he : Real.log (2133207378247 / 500000000000) = -Real.log (500000000000 / 2133207378247) := by
    rw [show ((2133207378247 / 500000000000) : ℝ) = ((500000000000 / 2133207378247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14991_neg : (728470947 / 500000000) ≤ -Real.log (100000000000 / 429281156797) ∧
    -Real.log (100000000000 / 429281156797) ≤ (1456941897 / 1000000000) := by
  have h := checkLog_sound (w := (29281156797 / 829281156797)) (n := 12)
    (lo := (35323767 / 500000000)) (hi := (14129507 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((429281156797 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(429281156797 / 400000000000) = 1/(100000000000 / 429281156797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14991 : Bounds (728470947 / 500000000) (1456941897 / 1000000000) (Real.log (429281156797 / 100000000000)) := by
  have h := reflection_log_14991_neg
  have he : Real.log (429281156797 / 100000000000) = -Real.log (100000000000 / 429281156797) := by
    rw [show ((429281156797 / 100000000000) : ℝ) = ((100000000000 / 429281156797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14992_neg : (2164860339 / 500000000) ≤ -Real.log (250000000000 / 18980769230769) ∧
    -Real.log (250000000000 / 18980769230769) ≤ (865944137 / 200000000) := by
  have h := checkLog_sound (w := (2980769230769 / 34980769230769)) (n := 12)
    (lo := (85418799 / 500000000)) (hi := (170837599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18980769230769 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(18980769230769 / 16000000000000) = 1/(250000000000 / 18980769230769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14992 : Bounds (2164860339 / 500000000) (865944137 / 200000000) (Real.log (18980769230769 / 250000000000)) := by
  have h := reflection_log_14992_neg
  have he : Real.log (18980769230769 / 250000000000) = -Real.log (250000000000 / 18980769230769) := by
    rw [show ((18980769230769 / 250000000000) : ℝ) = ((250000000000 / 18980769230769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14993_neg : (4369447849 / 1000000000) ≤ -Real.log (1 / 79) ∧
    -Real.log (1 / 79) ≤ (273090491 / 62500000) := by
  have h := checkLog_sound (w := (15 / 143)) (n := 12)
    (lo := (210564769 / 1000000000)) (hi := (21056477 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79 / 64) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(79 / 64) = 1/(1 / 79) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14993 : Bounds (4369447849 / 1000000000) (273090491 / 62500000) (Real.log (79 / 1)) := by
  have h := reflection_log_14993_neg
  have he : Real.log (79 / 1) = -Real.log (1 / 79) := by
    rw [show ((79 / 1) : ℝ) = ((1 / 79) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14994_neg : (681074599 / 1000000000) ≤ -Real.log (125 / 247) ∧
    -Real.log (125 / 247) ≤ (3405373 / 5000000) := by
  have h := checkLog_sound (w := (61 / 186)) (n := 12)
    (lo := (681074599 / 1000000000)) (hi := (3405373 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247 / 125) = 1/(125 / 247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14994 : Bounds (681074599 / 1000000000) (3405373 / 5000000) (Real.log (247 / 125)) := by
  have h := reflection_log_14994_neg
  have he : Real.log (247 / 125) = -Real.log (125 / 247) := by
    rw [show ((247 / 125) : ℝ) = ((125 / 247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14995_neg : (745940289 / 200000000) ≤ -Real.log (3 / 125) ∧
    -Real.log (3 / 125) ≤ (3729701451 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 221)) (n := 12)
    (lo := (52793109 / 200000000)) (hi := (131982773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 96) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 96) = 1/(3 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14995 : Bounds (-3729701451 / 1000000000) (-745940289 / 200000000) (Real.log (3 / 125)) := by
  have h := reflection_log_14995_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14996_neg : (243881 / 250000000) ≤ -Real.log (62500 / 62561) ∧
    -Real.log (62500 / 62561) ≤ (39021 / 40000000) := by
  have h := checkLog_sound (w := (61 / 125061)) (n := 12)
    (lo := (243881 / 250000000)) (hi := (39021 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62561 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62561 / 62500) = 1/(62500 / 62561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14996 : Bounds (243881 / 250000000) (39021 / 40000000) (Real.log (62561 / 62500)) := by
  have h := reflection_log_14996_neg
  have he : Real.log (62561 / 62500) = -Real.log (62500 / 62561) := by
    rw [show ((62561 / 62500) : ℝ) = ((62500 / 62561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14997_neg : (244119 / 250000000) ≤ -Real.log (62439 / 62500) ∧
    -Real.log (62439 / 62500) ≤ (976477 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 124939)) (n := 12)
    (lo := (244119 / 250000000)) (hi := (976477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62439) = 1/(62439 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14997 : Bounds (-976477 / 1000000000) (-244119 / 250000000) (Real.log (62439 / 62500)) := by
  have h := reflection_log_14997_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14998_neg : (120835599 / 250000000) ≤ -Real.log (200000 / 324297) ∧
    -Real.log (200000 / 324297) ≤ (483342397 / 1000000000) := by
  have h := checkLog_sound (w := (124297 / 524297)) (n := 12)
    (lo := (120835599 / 250000000)) (hi := (483342397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((324297 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(324297 / 200000) = 1/(200000 / 324297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14998 : Bounds (120835599 / 250000000) (483342397 / 1000000000) (Real.log (324297 / 200000)) := by
  have h := reflection_log_14998_neg
  have he : Real.log (324297 / 200000) = -Real.log (200000 / 324297) := by
    rw [show ((324297 / 200000) : ℝ) = ((200000 / 324297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14999_neg : (121437447 / 125000000) ≤ -Real.log (75703 / 200000) ∧
    -Real.log (75703 / 200000) ≤ (485749789 / 500000000) := by
  have h := checkLog_sound (w := (24297 / 175703)) (n := 12)
    (lo := (69588099 / 250000000)) (hi := (278352397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 75703) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 75703) = 1/(75703 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14999 : Bounds (-485749789 / 500000000) (-121437447 / 125000000) (Real.log (75703 / 200000)) := by
  have h := reflection_log_14999_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15000_neg : (484515323 / 1000000000) ≤ -Real.log (250000 / 405847) ∧
    -Real.log (250000 / 405847) ≤ (121128831 / 250000000) := by
  have h := checkLog_sound (w := (155847 / 655847)) (n := 12)
    (lo := (484515323 / 1000000000)) (hi := (121128831 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((405847 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(405847 / 250000) = 1/(250000 / 405847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15000 : Bounds (484515323 / 1000000000) (121128831 / 250000000) (Real.log (405847 / 250000)) := by
  have h := reflection_log_15000_neg
  have he : Real.log (405847 / 250000) = -Real.log (250000 / 405847) := by
    rw [show ((405847 / 250000) : ℝ) = ((250000 / 405847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15001_neg : (488269899 / 500000000) ≤ -Real.log (94153 / 250000) ∧
    -Real.log (94153 / 250000) ≤ (4882699 / 5000000) := by
  have h := checkLog_sound (w := (30847 / 219153)) (n := 12)
    (lo := (141696309 / 500000000)) (hi := (283392619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94153) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 94153) = 1/(94153 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15001 : Bounds (-4882699 / 5000000) (-488269899 / 500000000) (Real.log (94153 / 250000)) := by
  have h := reflection_log_15001_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15002_neg : (19680979 / 40000000) ≤ -Real.log (38211712591 / 62500000000) ∧
    -Real.log (38211712591 / 62500000000) ≤ (123006119 / 250000000) := by
  have h := checkLog_sound (w := (24288287409 / 100711712591)) (n := 12)
    (lo := (19680979 / 40000000)) (hi := (123006119 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 38211712591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 38211712591) = 1/(38211712591 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15002 : Bounds (-123006119 / 250000000) (-19680979 / 40000000) (Real.log (38211712591 / 62500000000)) := by
  have h := reflection_log_15002_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15003_neg : (24407859 / 50000000) ≤ -Real.log (24550255791 / 40000000000) ∧
    -Real.log (24550255791 / 40000000000) ≤ (488157181 / 1000000000) := by
  have h := checkLog_sound (w := (15449744209 / 64550255791)) (n := 12)
    (lo := (24407859 / 50000000)) (hi := (488157181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 24550255791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 24550255791) = 1/(24550255791 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15003 : Bounds (-488157181 / 1000000000) (-24407859 / 50000000) (Real.log (24550255791 / 40000000000)) := by
  have h := reflection_log_15003_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15004_neg : (1454841971 / 1000000000) ≤ -Real.log (125000000000 / 535475806771) ∧
    -Real.log (125000000000 / 535475806771) ≤ (727420987 / 500000000) := by
  have h := checkLog_sound (w := (35475806771 / 1035475806771)) (n := 12)
    (lo := (68547611 / 1000000000)) (hi := (17136903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((535475806771 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(535475806771 / 500000000000) = 1/(125000000000 / 535475806771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15004 : Bounds (1454841971 / 1000000000) (727420987 / 500000000) (Real.log (535475806771 / 125000000000)) := by
  have h := reflection_log_15004_neg
  have he : Real.log (535475806771 / 125000000000) = -Real.log (125000000000 / 535475806771) := by
    rw [show ((535475806771 / 125000000000) : ℝ) = ((125000000000 / 535475806771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15005_neg : (1461055121 / 1000000000) ≤ -Real.log (100000000000 / 431050524147) ∧
    -Real.log (100000000000 / 431050524147) ≤ (365263781 / 250000000) := by
  have h := checkLog_sound (w := (31050524147 / 831050524147)) (n := 12)
    (lo := (74760761 / 1000000000)) (hi := (37380381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((431050524147 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(431050524147 / 400000000000) = 1/(100000000000 / 431050524147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15005 : Bounds (1461055121 / 1000000000) (365263781 / 250000000) (Real.log (431050524147 / 100000000000)) := by
  have h := reflection_log_15005_neg
  have he : Real.log (431050524147 / 100000000000) = -Real.log (100000000000 / 431050524147) := by
    rw [show ((431050524147 / 100000000000) : ℝ) = ((100000000000 / 431050524147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15006_neg : (1102694011 / 250000000) ≤ -Real.log (500000000000 / 41166666666667) ∧
    -Real.log (500000000000 / 41166666666667) ≤ (4410776051 / 1000000000) := by
  have h := checkLog_sound (w := (9166666666667 / 73166666666667)) (n := 12)
    (lo := (62973241 / 250000000)) (hi := (50378593 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41166666666667 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(41166666666667 / 32000000000000) = 1/(500000000000 / 41166666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15006 : Bounds (1102694011 / 250000000) (4410776051 / 1000000000) (Real.log (41166666666667 / 500000000000)) := by
  have h := reflection_log_15006_neg
  have he : Real.log (41166666666667 / 500000000000) = -Real.log (500000000000 / 41166666666667) := by
    rw [show ((41166666666667 / 500000000000) : ℝ) = ((500000000000 / 41166666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15007_neg : (1331212 / 1953125) ≤ -Real.log (1000 / 1977) ∧
    -Real.log (1000 / 1977) ≤ (136316109 / 200000000) := by
  have h := checkLog_sound (w := (977 / 2977)) (n := 12)
    (lo := (1331212 / 1953125)) (hi := (136316109 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1977 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1977 / 1000) = 1/(1000 / 1977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15007 : Bounds (1331212 / 1953125) (136316109 / 200000000) (Real.log (1977 / 1000)) := by
  have h := reflection_log_15007_neg
  have he : Real.log (1977 / 1000) = -Real.log (1000 / 1977) := by
    rw [show ((1977 / 1000) : ℝ) = ((1000 / 1977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15008_neg : (188613053 / 50000000) ≤ -Real.log (23 / 1000) ∧
    -Real.log (23 / 1000) ≤ (1886130533 / 500000000) := by
  have h := checkLog_sound (w := (33 / 217)) (n := 12)
    (lo := (7663129 / 25000000)) (hi := (306525161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 92) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 92) = 1/(23 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15008 : Bounds (-1886130533 / 500000000) (-188613053 / 50000000) (Real.log (23 / 1000)) := by
  have h := reflection_log_15008_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15009_neg : (976523 / 1000000000) ≤ -Real.log (1000000 / 1000977) ∧
    -Real.log (1000000 / 1000977) ≤ (244131 / 250000000) := by
  have h := checkLog_sound (w := (977 / 2000977)) (n := 12)
    (lo := (976523 / 1000000000)) (hi := (244131 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000977 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000977 / 1000000) = 1/(1000000 / 1000977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15009 : Bounds (976523 / 1000000000) (244131 / 250000000) (Real.log (1000977 / 1000000)) := by
  have h := reflection_log_15009_neg
  have he : Real.log (1000977 / 1000000) = -Real.log (1000000 / 1000977) := by
    rw [show ((1000977 / 1000000) : ℝ) = ((1000000 / 1000977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15010_neg : (977477 / 1000000000) ≤ -Real.log (999023 / 1000000) ∧
    -Real.log (999023 / 1000000) ≤ (488739 / 500000000) := by
  have h := checkLog_sound (w := (977 / 1999023)) (n := 12)
    (lo := (977477 / 1000000000)) (hi := (488739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999023) = 1/(999023 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15010 : Bounds (-488739 / 500000000) (-977477 / 1000000000) (Real.log (999023 / 1000000)) := by
  have h := reflection_log_15010_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15011_neg : (484118543 / 1000000000) ≤ -Real.log (125000 / 202843) ∧
    -Real.log (125000 / 202843) ≤ (30257409 / 62500000) := by
  have h := checkLog_sound (w := (77843 / 327843)) (n := 12)
    (lo := (484118543 / 1000000000)) (hi := (30257409 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202843 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202843 / 125000) = 1/(125000 / 202843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15011 : Bounds (484118543 / 1000000000) (30257409 / 62500000) (Real.log (202843 / 125000)) := by
  have h := reflection_log_15011_neg
  have he : Real.log (202843 / 125000) = -Real.log (125000 / 202843) := by
    rw [show ((202843 / 125000) : ℝ) = ((125000 / 202843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15012_neg : (243707819 / 250000000) ≤ -Real.log (47157 / 125000) ∧
    -Real.log (47157 / 125000) ≤ (487415639 / 500000000) := by
  have h := checkLog_sound (w := (15343 / 109657)) (n := 12)
    (lo := (2200657 / 7812500)) (hi := (281684097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 47157) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 47157) = 1/(47157 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15012 : Bounds (-487415639 / 500000000) (-243707819 / 250000000) (Real.log (47157 / 125000)) := by
  have h := reflection_log_15012_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15013_neg : (485296101 / 1000000000) ≤ -Real.log (62500 / 101541) ∧
    -Real.log (62500 / 101541) ≤ (242648051 / 500000000) := by
  have h := checkLog_sound (w := (39041 / 164041)) (n := 12)
    (lo := (485296101 / 1000000000)) (hi := (242648051 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101541 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101541 / 62500) = 1/(62500 / 101541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15013 : Bounds (485296101 / 1000000000) (242648051 / 500000000) (Real.log (101541 / 62500)) := by
  have h := reflection_log_15013_neg
  have he : Real.log (101541 / 62500) = -Real.log (62500 / 101541) := by
    rw [show ((101541 / 62500) : ℝ) = ((62500 / 101541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15014_neg : (979912339 / 1000000000) ≤ -Real.log (23459 / 62500) ∧
    -Real.log (23459 / 62500) ≤ (979912341 / 1000000000) := by
  have h := checkLog_sound (w := (7791 / 54709)) (n := 12)
    (lo := (286765159 / 1000000000)) (hi := (7169129 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23459) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 23459) = 1/(23459 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15014 : Bounds (-979912341 / 1000000000) (-979912339 / 1000000000) (Real.log (23459 / 62500)) := by
  have h := reflection_log_15014_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15015_neg : (494616239 / 1000000000) ≤ -Real.log (2382050319 / 3906250000) ∧
    -Real.log (2382050319 / 3906250000) ≤ (6182703 / 12500000) := by
  have h := checkLog_sound (w := (1524199681 / 6288300319)) (n := 12)
    (lo := (494616239 / 1000000000)) (hi := (6182703 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 2382050319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 2382050319) = 1/(2382050319 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15015 : Bounds (-6182703 / 12500000) (-494616239 / 1000000000) (Real.log (2382050319 / 3906250000)) := by
  have h := reflection_log_15015_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15016_neg : (490712733 / 1000000000) ≤ -Real.log (9565467351 / 15625000000) ∧
    -Real.log (9565467351 / 15625000000) ≤ (245356367 / 500000000) := by
  have h := checkLog_sound (w := (6059532649 / 25190467351)) (n := 12)
    (lo := (490712733 / 1000000000)) (hi := (245356367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 9565467351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 9565467351) = 1/(9565467351 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15016 : Bounds (-245356367 / 500000000) (-490712733 / 1000000000) (Real.log (9565467351 / 15625000000)) := by
  have h := reflection_log_15016_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15017_neg : (1458949819 / 1000000000) ≤ -Real.log (250000000000 / 1075359967767) ∧
    -Real.log (250000000000 / 1075359967767) ≤ (729474911 / 500000000) := by
  have h := checkLog_sound (w := (75359967767 / 2075359967767)) (n := 12)
    (lo := (72655459 / 1000000000)) (hi := (3632773 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1075359967767 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1075359967767 / 1000000000000) = 1/(250000000000 / 1075359967767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15017 : Bounds (1458949819 / 1000000000) (729474911 / 500000000) (Real.log (1075359967767 / 250000000000)) := by
  have h := reflection_log_15017_neg
  have he : Real.log (1075359967767 / 250000000000) = -Real.log (250000000000 / 1075359967767) := by
    rw [show ((1075359967767 / 250000000000) : ℝ) = ((250000000000 / 1075359967767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15018_neg : (36630211 / 25000000) ≤ -Real.log (50000000000 / 216422268639) ∧
    -Real.log (50000000000 / 216422268639) ≤ (1465208443 / 1000000000) := by
  have h := checkLog_sound (w := (16422268639 / 416422268639)) (n := 12)
    (lo := (493213 / 6250000)) (hi := (78914081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216422268639 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(216422268639 / 200000000000) = 1/(50000000000 / 216422268639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15018 : Bounds (36630211 / 25000000) (1465208443 / 1000000000) (Real.log (216422268639 / 50000000000)) := by
  have h := reflection_log_15018_neg
  have he : Real.log (216422268639 / 50000000000) = -Real.log (50000000000 / 216422268639) := by
    rw [show ((216422268639 / 50000000000) : ℝ) = ((50000000000 / 216422268639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15019_neg : (1102694011 / 250000000) ≤ -Real.log (250000000000 / 20583333333333) ∧
    -Real.log (250000000000 / 20583333333333) ≤ (4410776051 / 1000000000) := by
  have h := checkLog_sound (w := (4583333333333 / 36583333333333)) (n := 12)
    (lo := (62973241 / 250000000)) (hi := (50378593 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20583333333333 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(20583333333333 / 16000000000000) = 1/(250000000000 / 20583333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15019 : Bounds (1102694011 / 250000000) (4410776051 / 1000000000) (Real.log (20583333333333 / 250000000000)) := by
  have h := reflection_log_15019_neg
  have he : Real.log (20583333333333 / 250000000000) = -Real.log (250000000000 / 20583333333333) := by
    rw [show ((20583333333333 / 250000000000) : ℝ) = ((250000000000 / 20583333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15020_neg : (4453841603 / 1000000000) ≤ -Real.log (250000000000 / 21489130434783) ∧
    -Real.log (250000000000 / 21489130434783) ≤ (445384161 / 100000000) := by
  have h := checkLog_sound (w := (5489130434783 / 37489130434783)) (n := 12)
    (lo := (294958523 / 1000000000)) (hi := (73739631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21489130434783 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(21489130434783 / 16000000000000) = 1/(250000000000 / 21489130434783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15020 : Bounds (4453841603 / 1000000000) (445384161 / 100000000) (Real.log (21489130434783 / 250000000000)) := by
  have h := reflection_log_15020_neg
  have he : Real.log (21489130434783 / 250000000000) = -Real.log (250000000000 / 21489130434783) := by
    rw [show ((21489130434783 / 250000000000) : ℝ) = ((250000000000 / 21489130434783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15021_neg : (682086233 / 1000000000) ≤ -Real.log (500 / 989) ∧
    -Real.log (500 / 989) ≤ (341043117 / 500000000) := by
  have h := checkLog_sound (w := (489 / 1489)) (n := 12)
    (lo := (682086233 / 1000000000)) (hi := (341043117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989 / 500) = 1/(500 / 989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15021 : Bounds (682086233 / 1000000000) (341043117 / 500000000) (Real.log (989 / 500)) := by
  have h := reflection_log_15021_neg
  have he : Real.log (989 / 500) = -Real.log (500 / 989) := by
    rw [show ((989 / 500) : ℝ) = ((500 / 989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15022_neg : (1908356411 / 500000000) ≤ -Real.log (11 / 500) ∧
    -Real.log (11 / 500) ≤ (954178207 / 250000000) := by
  have h := checkLog_sound (w := (37 / 213)) (n := 12)
    (lo := (175488461 / 500000000)) (hi := (350976923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 88) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 88) = 1/(11 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15022 : Bounds (-954178207 / 250000000) (-1908356411 / 500000000) (Real.log (11 / 500)) := by
  have h := reflection_log_15022_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15023_neg : (488761 / 500000000) ≤ -Real.log (500000 / 500489) ∧
    -Real.log (500000 / 500489) ≤ (977523 / 1000000000) := by
  have h := checkLog_sound (w := (489 / 1000489)) (n := 12)
    (lo := (488761 / 500000000)) (hi := (977523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500489 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500489 / 500000) = 1/(500000 / 500489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15023 : Bounds (488761 / 500000000) (977523 / 1000000000) (Real.log (500489 / 500000)) := by
  have h := reflection_log_15023_neg
  have he : Real.log (500489 / 500000) = -Real.log (500000 / 500489) := by
    rw [show ((500489 / 500000) : ℝ) = ((500000 / 500489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15024_neg : (489239 / 500000000) ≤ -Real.log (499511 / 500000) ∧
    -Real.log (499511 / 500000) ≤ (978479 / 1000000000) := by
  have h := checkLog_sound (w := (489 / 999511)) (n := 12)
    (lo := (489239 / 500000000)) (hi := (978479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499511) = 1/(499511 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15024 : Bounds (-978479 / 1000000000) (-489239 / 500000000) (Real.log (499511 / 500000)) := by
  have h := reflection_log_15024_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15025_neg : (242450123 / 500000000) ≤ -Real.log (1000000 / 1624013) ∧
    -Real.log (1000000 / 1624013) ≤ (484900247 / 1000000000) := by
  have h := checkLog_sound (w := (624013 / 2624013)) (n := 12)
    (lo := (242450123 / 500000000)) (hi := (484900247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1624013 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1624013 / 1000000) = 1/(1000000 / 1624013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15025 : Bounds (242450123 / 500000000) (484900247 / 1000000000) (Real.log (1624013 / 1000000)) := by
  have h := reflection_log_15025_neg
  have he : Real.log (1624013 / 1000000) = -Real.log (1000000 / 1624013) := by
    rw [show ((1624013 / 1000000) : ℝ) = ((1000000 / 1624013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15026_neg : (97820071 / 100000000) ≤ -Real.log (375987 / 1000000) ∧
    -Real.log (375987 / 1000000) ≤ (122275089 / 125000000) := by
  have h := checkLog_sound (w := (124013 / 875987)) (n := 12)
    (lo := (28505353 / 100000000)) (hi := (285053531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 375987) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 375987) = 1/(375987 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15026 : Bounds (-122275089 / 125000000) (-97820071 / 100000000) (Real.log (375987 / 1000000)) := by
  have h := reflection_log_15026_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15027_neg : (486082419 / 1000000000) ≤ -Real.log (500000 / 812967) ∧
    -Real.log (500000 / 812967) ≤ (24304121 / 50000000) := by
  have h := checkLog_sound (w := (312967 / 1312967)) (n := 12)
    (lo := (486082419 / 1000000000)) (hi := (24304121 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((812967 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(812967 / 500000) = 1/(500000 / 812967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15027 : Bounds (486082419 / 1000000000) (24304121 / 50000000) (Real.log (812967 / 500000)) := by
  have h := reflection_log_15027_neg
  have he : Real.log (812967 / 500000) = -Real.log (500000 / 812967) := by
    rw [show ((812967 / 500000) : ℝ) = ((500000 / 812967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15028_neg : (39332921 / 40000000) ≤ -Real.log (187033 / 500000) ∧
    -Real.log (187033 / 500000) ≤ (983323027 / 1000000000) := by
  have h := checkLog_sound (w := (62967 / 437033)) (n := 12)
    (lo := (58035169 / 200000000)) (hi := (145087923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 187033) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 187033) = 1/(187033 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15028 : Bounds (-983323027 / 1000000000) (-39332921 / 40000000) (Real.log (187033 / 500000)) := by
  have h := reflection_log_15028_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15029_neg : (248620303 / 500000000) ≤ -Real.log (152051656911 / 250000000000) ∧
    -Real.log (152051656911 / 250000000000) ≤ (497240607 / 1000000000) := by
  have h := checkLog_sound (w := (97948343089 / 402051656911)) (n := 12)
    (lo := (248620303 / 500000000)) (hi := (497240607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 152051656911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 152051656911) = 1/(152051656911 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15029 : Bounds (-497240607 / 1000000000) (-248620303 / 500000000) (Real.log (152051656911 / 250000000000)) := by
  have h := reflection_log_15029_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15030_neg : (30831279 / 62500000) ≤ -Real.log (610607775831 / 1000000000000) ∧
    -Real.log (610607775831 / 1000000000000) ≤ (98660093 / 200000000) := by
  have h := checkLog_sound (w := (389392224169 / 1610607775831)) (n := 12)
    (lo := (30831279 / 62500000)) (hi := (98660093 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 610607775831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 610607775831) = 1/(610607775831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15030 : Bounds (-98660093 / 200000000) (-30831279 / 62500000) (Real.log (610607775831 / 1000000000000)) := by
  have h := reflection_log_15030_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15031_neg : (365775239 / 250000000) ≤ -Real.log (500000000000 / 2159666424637) ∧
    -Real.log (500000000000 / 2159666424637) ≤ (1463100959 / 1000000000) := by
  have h := checkLog_sound (w := (159666424637 / 4159666424637)) (n := 12)
    (lo := (19201649 / 250000000)) (hi := (76806597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2159666424637 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2159666424637 / 2000000000000) = 1/(500000000000 / 2159666424637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15031 : Bounds (365775239 / 250000000) (1463100959 / 1000000000) (Real.log (2159666424637 / 500000000000)) := by
  have h := reflection_log_15031_neg
  have he : Real.log (2159666424637 / 500000000000) = -Real.log (500000000000 / 2159666424637) := by
    rw [show ((2159666424637 / 500000000000) : ℝ) = ((500000000000 / 2159666424637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15032_neg : (293881089 / 200000000) ≤ -Real.log (125000000000 / 543331257051) ∧
    -Real.log (125000000000 / 543331257051) ≤ (183675681 / 125000000) := by
  have h := checkLog_sound (w := (43331257051 / 1043331257051)) (n := 12)
    (lo := (16622217 / 200000000)) (hi := (41555543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543331257051 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(543331257051 / 500000000000) = 1/(125000000000 / 543331257051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15032 : Bounds (293881089 / 200000000) (183675681 / 125000000) (Real.log (543331257051 / 125000000000)) := by
  have h := reflection_log_15032_neg
  have he : Real.log (543331257051 / 125000000000) = -Real.log (125000000000 / 543331257051) := by
    rw [show ((543331257051 / 125000000000) : ℝ) = ((125000000000 / 543331257051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15033_neg : (4453841603 / 1000000000) ≤ -Real.log (100000000000 / 8595652173913) ∧
    -Real.log (100000000000 / 8595652173913) ≤ (445384161 / 100000000) := by
  have h := checkLog_sound (w := (2195652173913 / 14995652173913)) (n := 12)
    (lo := (294958523 / 1000000000)) (hi := (73739631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8595652173913 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(8595652173913 / 6400000000000) = 1/(100000000000 / 8595652173913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15033 : Bounds (4453841603 / 1000000000) (445384161 / 100000000) (Real.log (8595652173913 / 100000000000)) := by
  have h := reflection_log_15033_neg
  have he : Real.log (8595652173913 / 100000000000) = -Real.log (100000000000 / 8595652173913) := by
    rw [show ((8595652173913 / 100000000000) : ℝ) = ((100000000000 / 8595652173913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15034_neg : (899759811 / 200000000) ≤ -Real.log (250000000000 / 22477272727273) ∧
    -Real.log (250000000000 / 22477272727273) ≤ (2249399531 / 500000000) := by
  have h := checkLog_sound (w := (6477272727273 / 38477272727273)) (n := 12)
    (lo := (13596639 / 40000000)) (hi := (42489497 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22477272727273 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(22477272727273 / 16000000000000) = 1/(250000000000 / 22477272727273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15034 : Bounds (899759811 / 200000000) (2249399531 / 500000000) (Real.log (22477272727273 / 250000000000)) := by
  have h := reflection_log_15034_neg
  have he : Real.log (22477272727273 / 250000000000) = -Real.log (250000000000 / 22477272727273) := by
    rw [show ((22477272727273 / 250000000000) : ℝ) = ((250000000000 / 22477272727273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15035_neg : (341295833 / 500000000) ≤ -Real.log (1000 / 1979) ∧
    -Real.log (1000 / 1979) ≤ (682591667 / 1000000000) := by
  have h := checkLog_sound (w := (979 / 2979)) (n := 12)
    (lo := (341295833 / 500000000)) (hi := (682591667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979 / 1000) = 1/(1000 / 1979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15035 : Bounds (341295833 / 500000000) (682591667 / 1000000000) (Real.log (1979 / 1000)) := by
  have h := reflection_log_15035_neg
  have he : Real.log (1979 / 1000) = -Real.log (1000 / 1979) := by
    rw [show ((1979 / 1000) : ℝ) = ((1000 / 1979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15036_neg : (1931616419 / 500000000) ≤ -Real.log (21 / 1000) ∧
    -Real.log (21 / 1000) ≤ (965808211 / 250000000) := by
  have h := checkLog_sound (w := (41 / 209)) (n := 12)
    (lo := (198748469 / 500000000)) (hi := (397496939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 84) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 84) = 1/(21 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15036 : Bounds (-965808211 / 250000000) (-1931616419 / 500000000) (Real.log (21 / 1000)) := by
  have h := reflection_log_15036_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15037_neg : (978521 / 1000000000) ≤ -Real.log (1000000 / 1000979) ∧
    -Real.log (1000000 / 1000979) ≤ (489261 / 500000000) := by
  have h := checkLog_sound (w := (979 / 2000979)) (n := 12)
    (lo := (978521 / 1000000000)) (hi := (489261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000979 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000979 / 1000000) = 1/(1000000 / 1000979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15037 : Bounds (978521 / 1000000000) (489261 / 500000000) (Real.log (1000979 / 1000000)) := by
  have h := reflection_log_15037_neg
  have he : Real.log (1000979 / 1000000) = -Real.log (1000000 / 1000979) := by
    rw [show ((1000979 / 1000000) : ℝ) = ((1000000 / 1000979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15038_neg : (979479 / 1000000000) ≤ -Real.log (999021 / 1000000) ∧
    -Real.log (999021 / 1000000) ≤ (24487 / 25000000) := by
  have h := checkLog_sound (w := (979 / 1999021)) (n := 12)
    (lo := (979479 / 1000000000)) (hi := (24487 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999021) = 1/(999021 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15038 : Bounds (-24487 / 25000000) (-979479 / 1000000000) (Real.log (999021 / 1000000)) := by
  have h := reflection_log_15038_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15039_neg : (485687491 / 1000000000) ≤ -Real.log (250000 / 406323) ∧
    -Real.log (250000 / 406323) ≤ (121421873 / 250000000) := by
  have h := checkLog_sound (w := (156323 / 656323)) (n := 12)
    (lo := (485687491 / 1000000000)) (hi := (121421873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((406323 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(406323 / 250000) = 1/(250000 / 406323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15039 : Bounds (485687491 / 1000000000) (121421873 / 250000000) (Real.log (406323 / 250000)) := by
  have h := reflection_log_15039_neg
  have he : Real.log (406323 / 250000) = -Real.log (250000 / 406323) := by
    rw [show ((406323 / 250000) : ℝ) = ((250000 / 406323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


