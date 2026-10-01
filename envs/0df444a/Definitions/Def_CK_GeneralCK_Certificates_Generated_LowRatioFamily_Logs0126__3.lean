-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0126__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0126__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:16:35.014782+00:00
-- url     : https://prove2.me/theorems/63945fc6-b6d8-47cb-9f30-5a3175d861cb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0126 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0127, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0126 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0127, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0128)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0126 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0127, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0128)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0126 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0127, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0128) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0126 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0127, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0128).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0126 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8064_neg : (29941 / 125000000) ≤ -Real.log (1999521 / 2000000) ∧
    -Real.log (1999521 / 2000000) ≤ (239529 / 1000000000) := by
  have h := checkLog_sound (w := (479 / 3999521)) (n := 12)
    (lo := (29941 / 125000000)) (hi := (239529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999521) = 1/(1999521 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8064 : Bounds (-239529 / 1000000000) (-29941 / 125000000) (Real.log (1999521 / 2000000)) := by
  have h := reflection_log_8064_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8065_neg : (14236713 / 125000000) ≤ -Real.log (1000000 / 1120633) ∧
    -Real.log (1000000 / 1120633) ≤ (22778741 / 200000000) := by
  have h := checkLog_sound (w := (120633 / 2120633)) (n := 12)
    (lo := (14236713 / 125000000)) (hi := (22778741 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1120633 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1120633 / 1000000) = 1/(1000000 / 1120633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8065 : Bounds (14236713 / 125000000) (22778741 / 200000000) (Real.log (1120633 / 1000000)) := by
  have h := reflection_log_8065_neg
  have he : Real.log (1120633 / 1000000) = -Real.log (1000000 / 1120633) := by
    rw [show ((1120633 / 1000000) : ℝ) = ((1000000 / 1120633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8066_neg : (32138237 / 250000000) ≤ -Real.log (879367 / 1000000) ∧
    -Real.log (879367 / 1000000) ≤ (128552949 / 1000000000) := by
  have h := checkLog_sound (w := (120633 / 1879367)) (n := 12)
    (lo := (32138237 / 250000000)) (hi := (128552949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 879367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 879367) = 1/(879367 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8066 : Bounds (-128552949 / 1000000000) (-32138237 / 250000000) (Real.log (879367 / 1000000)) := by
  have h := reflection_log_8066_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8067_neg : (114336213 / 1000000000) ≤ -Real.log (1000000 / 1121129) ∧
    -Real.log (1000000 / 1121129) ≤ (57168107 / 500000000) := by
  have h := checkLog_sound (w := (121129 / 2121129)) (n := 12)
    (lo := (114336213 / 1000000000)) (hi := (57168107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1121129 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1121129 / 1000000) = 1/(1000000 / 1121129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8067 : Bounds (114336213 / 1000000000) (57168107 / 500000000) (Real.log (1121129 / 1000000)) := by
  have h := reflection_log_8067_neg
  have he : Real.log (1121129 / 1000000) = -Real.log (1000000 / 1121129) := by
    rw [show ((1121129 / 1000000) : ℝ) = ((1000000 / 1121129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8068_neg : (129117149 / 1000000000) ≤ -Real.log (878871 / 1000000) ∧
    -Real.log (878871 / 1000000) ≤ (2582343 / 20000000) := by
  have h := checkLog_sound (w := (121129 / 1878871)) (n := 12)
    (lo := (129117149 / 1000000000)) (hi := (2582343 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 878871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 878871) = 1/(878871 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8068 : Bounds (-2582343 / 20000000) (-129117149 / 1000000000) (Real.log (878871 / 1000000)) := by
  have h := reflection_log_8068_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8069_neg : (1847617 / 125000000) ≤ -Real.log (985327765359 / 1000000000000) ∧
    -Real.log (985327765359 / 1000000000000) ≤ (14780937 / 1000000000) := by
  have h := checkLog_sound (w := (14672234641 / 1985327765359)) (n := 12)
    (lo := (1847617 / 125000000)) (hi := (14780937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 985327765359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 985327765359) = 1/(985327765359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8069 : Bounds (-14780937 / 1000000000) (-1847617 / 125000000) (Real.log (985327765359 / 1000000000000)) := by
  have h := reflection_log_8069_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8070_neg : (3664811 / 250000000) ≤ -Real.log (985447679311 / 1000000000000) ∧
    -Real.log (985447679311 / 1000000000000) ≤ (2931849 / 200000000) := by
  have h := checkLog_sound (w := (14552320689 / 1985447679311)) (n := 12)
    (lo := (3664811 / 250000000)) (hi := (2931849 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 985447679311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 985447679311) = 1/(985447679311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8070 : Bounds (-2931849 / 200000000) (-3664811 / 250000000) (Real.log (985447679311 / 1000000000000)) := by
  have h := reflection_log_8070_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8071_neg : (60611663 / 250000000) ≤ -Real.log (500000000000 / 637181631787) ∧
    -Real.log (500000000000 / 637181631787) ≤ (242446653 / 1000000000) := by
  have h := checkLog_sound (w := (137181631787 / 1137181631787)) (n := 12)
    (lo := (60611663 / 250000000)) (hi := (242446653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((637181631787 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(637181631787 / 500000000000) = 1/(500000000000 / 637181631787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8071 : Bounds (60611663 / 250000000) (242446653 / 1000000000) (Real.log (637181631787 / 500000000000)) := by
  have h := reflection_log_8071_neg
  have he : Real.log (637181631787 / 500000000000) = -Real.log (500000000000 / 637181631787) := by
    rw [show ((637181631787 / 500000000000) : ℝ) = ((500000000000 / 637181631787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8072_neg : (243453363 / 1000000000) ≤ -Real.log (500000000000 / 637823412083) ∧
    -Real.log (500000000000 / 637823412083) ≤ (60863341 / 250000000) := by
  have h := checkLog_sound (w := (137823412083 / 1137823412083)) (n := 12)
    (lo := (243453363 / 1000000000)) (hi := (60863341 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((637823412083 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(637823412083 / 500000000000) = 1/(500000000000 / 637823412083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8072 : Bounds (243453363 / 1000000000) (60863341 / 250000000) (Real.log (637823412083 / 500000000000)) := by
  have h := reflection_log_8072_neg
  have he : Real.log (637823412083 / 500000000000) = -Real.log (500000000000 / 637823412083) := by
    rw [show ((637823412083 / 500000000000) : ℝ) = ((500000000000 / 637823412083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8073_neg : (487426523 / 1000000000) ≤ -Real.log (25000000000 / 40703022339) ∧
    -Real.log (25000000000 / 40703022339) ≤ (121856631 / 250000000) := by
  have h := checkLog_sound (w := (15703022339 / 65703022339)) (n := 12)
    (lo := (487426523 / 1000000000)) (hi := (121856631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40703022339 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40703022339 / 25000000000) = 1/(25000000000 / 40703022339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8073 : Bounds (487426523 / 1000000000) (121856631 / 250000000) (Real.log (40703022339 / 25000000000)) := by
  have h := reflection_log_8073_neg
  have he : Real.log (40703022339 / 25000000000) = -Real.log (25000000000 / 40703022339) := by
    rw [show ((40703022339 / 25000000000) : ℝ) = ((25000000000 / 40703022339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8074_neg : (488487239 / 1000000000) ≤ -Real.log (62500000000 / 101865548981) ∧
    -Real.log (62500000000 / 101865548981) ≤ (12212181 / 25000000) := by
  have h := checkLog_sound (w := (39365548981 / 164365548981)) (n := 12)
    (lo := (488487239 / 1000000000)) (hi := (12212181 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101865548981 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101865548981 / 62500000000) = 1/(62500000000 / 101865548981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8074 : Bounds (488487239 / 1000000000) (12212181 / 25000000) (Real.log (101865548981 / 62500000000)) := by
  have h := reflection_log_8074_neg
  have he : Real.log (101865548981 / 62500000000) = -Real.log (62500000000 / 101865548981) := by
    rw [show ((101865548981 / 62500000000) : ℝ) = ((62500000000 / 101865548981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8075_neg : (215111379 / 1000000000) ≤ -Real.log (25 / 31) ∧
    -Real.log (25 / 31) ≤ (10755569 / 50000000) := by
  have h := checkLog_sound (w := (3 / 28)) (n := 12)
    (lo := (215111379 / 1000000000)) (hi := (10755569 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31 / 25) = 1/(25 / 31) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8075 : Bounds (215111379 / 1000000000) (10755569 / 50000000) (Real.log (31 / 25)) := by
  have h := reflection_log_8075_neg
  have he : Real.log (31 / 25) = -Real.log (25 / 31) := by
    rw [show ((31 / 25) : ℝ) = ((25 / 31) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8076_neg : (54887369 / 200000000) ≤ -Real.log (19 / 25) ∧
    -Real.log (19 / 25) ≤ (137218423 / 500000000) := by
  have h := checkLog_sound (w := (3 / 22)) (n := 12)
    (lo := (54887369 / 200000000)) (hi := (137218423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 19) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25 / 19) = 1/(19 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8076 : Bounds (-137218423 / 500000000) (-54887369 / 200000000) (Real.log (19 / 25)) := by
  have h := reflection_log_8076_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8077_neg : (239971 / 1000000000) ≤ -Real.log (12500 / 12503) ∧
    -Real.log (12500 / 12503) ≤ (59993 / 250000000) := by
  have h := checkLog_sound (w := (3 / 25003)) (n := 12)
    (lo := (239971 / 1000000000)) (hi := (59993 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12503 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12503 / 12500) = 1/(12500 / 12503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8077 : Bounds (239971 / 1000000000) (59993 / 250000000) (Real.log (12503 / 12500)) := by
  have h := reflection_log_8077_neg
  have he : Real.log (12503 / 12500) = -Real.log (12500 / 12503) := by
    rw [show ((12503 / 12500) : ℝ) = ((12500 / 12503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8078_neg : (60007 / 250000000) ≤ -Real.log (12497 / 12500) ∧
    -Real.log (12497 / 12500) ≤ (240029 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 24997)) (n := 12)
    (lo := (60007 / 250000000)) (hi := (240029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 12497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 12497) = 1/(12497 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8078 : Bounds (-240029 / 1000000000) (-60007 / 250000000) (Real.log (12497 / 12500)) := by
  have h := reflection_log_8078_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8079_neg : (891593 / 7812500) ≤ -Real.log (1000000 / 1120891) ∧
    -Real.log (1000000 / 1120891) ≤ (22824781 / 200000000) := by
  have h := checkLog_sound (w := (120891 / 2120891)) (n := 12)
    (lo := (891593 / 7812500)) (hi := (22824781 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1120891 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1120891 / 1000000) = 1/(1000000 / 1120891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8079 : Bounds (891593 / 7812500) (22824781 / 200000000) (Real.log (1120891 / 1000000)) := by
  have h := reflection_log_8079_neg
  have he : Real.log (1120891 / 1000000) = -Real.log (1000000 / 1120891) := by
    rw [show ((1120891 / 1000000) : ℝ) = ((1000000 / 1120891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8080_neg : (8052899 / 62500000) ≤ -Real.log (879109 / 1000000) ∧
    -Real.log (879109 / 1000000) ≤ (25769277 / 200000000) := by
  have h := checkLog_sound (w := (120891 / 1879109)) (n := 12)
    (lo := (8052899 / 62500000)) (hi := (25769277 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 879109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 879109) = 1/(879109 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8080 : Bounds (-25769277 / 200000000) (-8052899 / 62500000) (Real.log (879109 / 1000000)) := by
  have h := reflection_log_8080_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8081_neg : (114566311 / 1000000000) ≤ -Real.log (1000000 / 1121387) ∧
    -Real.log (1000000 / 1121387) ≤ (14320789 / 125000000) := by
  have h := checkLog_sound (w := (121387 / 2121387)) (n := 12)
    (lo := (114566311 / 1000000000)) (hi := (14320789 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1121387 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1121387 / 1000000) = 1/(1000000 / 1121387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8081 : Bounds (114566311 / 1000000000) (14320789 / 125000000) (Real.log (1121387 / 1000000)) := by
  have h := reflection_log_8081_neg
  have he : Real.log (1121387 / 1000000) = -Real.log (1000000 / 1121387) := by
    rw [show ((1121387 / 1000000) : ℝ) = ((1000000 / 1121387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8082_neg : (129410751 / 1000000000) ≤ -Real.log (878613 / 1000000) ∧
    -Real.log (878613 / 1000000) ≤ (2022043 / 15625000) := by
  have h := checkLog_sound (w := (121387 / 1878613)) (n := 12)
    (lo := (129410751 / 1000000000)) (hi := (2022043 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 878613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 878613) = 1/(878613 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8082 : Bounds (-2022043 / 15625000) (-129410751 / 1000000000) (Real.log (878613 / 1000000)) := by
  have h := reflection_log_8082_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8083_neg : (14844439 / 1000000000) ≤ -Real.log (985265196231 / 1000000000000) ∧
    -Real.log (985265196231 / 1000000000000) ≤ (371111 / 25000000) := by
  have h := checkLog_sound (w := (14734803769 / 1985265196231)) (n := 12)
    (lo := (14844439 / 1000000000)) (hi := (371111 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 985265196231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 985265196231) = 1/(985265196231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8083 : Bounds (-371111 / 25000000) (-14844439 / 1000000000) (Real.log (985265196231 / 1000000000000)) := by
  have h := reflection_log_8083_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8084_neg : (14722479 / 1000000000) ≤ -Real.log (985385366119 / 1000000000000) ∧
    -Real.log (985385366119 / 1000000000000) ≤ (184031 / 12500000) := by
  have h := checkLog_sound (w := (14614633881 / 1985385366119)) (n := 12)
    (lo := (14722479 / 1000000000)) (hi := (184031 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 985385366119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 985385366119) = 1/(985385366119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8084 : Bounds (-184031 / 12500000) (-14722479 / 1000000000) (Real.log (985385366119 / 1000000000000)) := by
  have h := reflection_log_8084_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8085_neg : (242970289 / 1000000000) ≤ -Real.log (125000000000 / 159378842669) ∧
    -Real.log (125000000000 / 159378842669) ≤ (24297029 / 100000000) := by
  have h := checkLog_sound (w := (34378842669 / 284378842669)) (n := 12)
    (lo := (242970289 / 1000000000)) (hi := (24297029 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159378842669 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159378842669 / 125000000000) = 1/(125000000000 / 159378842669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8085 : Bounds (242970289 / 1000000000) (24297029 / 100000000) (Real.log (159378842669 / 125000000000)) := by
  have h := reflection_log_8085_neg
  have he : Real.log (159378842669 / 125000000000) = -Real.log (125000000000 / 159378842669) := by
    rw [show ((159378842669 / 125000000000) : ℝ) = ((125000000000 / 159378842669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8086_neg : (243977063 / 1000000000) ≤ -Real.log (500000000000 / 638157527831) ∧
    -Real.log (500000000000 / 638157527831) ≤ (30497133 / 125000000) := by
  have h := checkLog_sound (w := (138157527831 / 1138157527831)) (n := 12)
    (lo := (243977063 / 1000000000)) (hi := (30497133 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((638157527831 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(638157527831 / 500000000000) = 1/(500000000000 / 638157527831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8086 : Bounds (243977063 / 1000000000) (30497133 / 125000000) (Real.log (638157527831 / 500000000000)) := by
  have h := reflection_log_8086_neg
  have he : Real.log (638157527831 / 500000000000) = -Real.log (500000000000 / 638157527831) := by
    rw [show ((638157527831 / 500000000000) : ℝ) = ((500000000000 / 638157527831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8087_neg : (488487239 / 1000000000) ≤ -Real.log (500000000000 / 814924391847) ∧
    -Real.log (500000000000 / 814924391847) ≤ (12212181 / 25000000) := by
  have h := checkLog_sound (w := (314924391847 / 1314924391847)) (n := 12)
    (lo := (488487239 / 1000000000)) (hi := (12212181 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((814924391847 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(814924391847 / 500000000000) = 1/(500000000000 / 814924391847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8087 : Bounds (488487239 / 1000000000) (12212181 / 25000000) (Real.log (814924391847 / 500000000000)) := by
  have h := reflection_log_8087_neg
  have he : Real.log (814924391847 / 500000000000) = -Real.log (500000000000 / 814924391847) := by
    rw [show ((814924391847 / 500000000000) : ℝ) = ((500000000000 / 814924391847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8088_neg : (19581929 / 40000000) ≤ -Real.log (100000000000 / 163157894737) ∧
    -Real.log (100000000000 / 163157894737) ≤ (244774113 / 500000000) := by
  have h := checkLog_sound (w := (63157894737 / 263157894737)) (n := 12)
    (lo := (19581929 / 40000000)) (hi := (244774113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163157894737 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163157894737 / 100000000000) = 1/(100000000000 / 163157894737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8088 : Bounds (19581929 / 40000000) (244774113 / 500000000) (Real.log (163157894737 / 100000000000)) := by
  have h := reflection_log_8088_neg
  have he : Real.log (163157894737 / 100000000000) = -Real.log (100000000000 / 163157894737) := by
    rw [show ((163157894737 / 100000000000) : ℝ) = ((100000000000 / 163157894737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8089_neg : (53878631 / 250000000) ≤ -Real.log (2000 / 2481) ∧
    -Real.log (2000 / 2481) ≤ (8620581 / 40000000) := by
  have h := checkLog_sound (w := (481 / 4481)) (n := 12)
    (lo := (53878631 / 250000000)) (hi := (8620581 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2481 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2481 / 2000) = 1/(2000 / 2481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8089 : Bounds (53878631 / 250000000) (8620581 / 40000000) (Real.log (2481 / 2000)) := by
  have h := reflection_log_8089_neg
  have he : Real.log (2481 / 2000) = -Real.log (2000 / 2481) := by
    rw [show ((2481 / 2000) : ℝ) = ((2000 / 2481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8090_neg : (68773739 / 250000000) ≤ -Real.log (1519 / 2000) ∧
    -Real.log (1519 / 2000) ≤ (275094957 / 1000000000) := by
  have h := checkLog_sound (w := (481 / 3519)) (n := 12)
    (lo := (68773739 / 250000000)) (hi := (275094957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1519) = 1/(1519 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8090 : Bounds (-275094957 / 1000000000) (-68773739 / 250000000) (Real.log (1519 / 2000)) := by
  have h := reflection_log_8090_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8091_neg : (240471 / 1000000000) ≤ -Real.log (2000000 / 2000481) ∧
    -Real.log (2000000 / 2000481) ≤ (30059 / 125000000) := by
  have h := checkLog_sound (w := (481 / 4000481)) (n := 12)
    (lo := (240471 / 1000000000)) (hi := (30059 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000481 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000481 / 2000000) = 1/(2000000 / 2000481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8091 : Bounds (240471 / 1000000000) (30059 / 125000000) (Real.log (2000481 / 2000000)) := by
  have h := reflection_log_8091_neg
  have he : Real.log (2000481 / 2000000) = -Real.log (2000000 / 2000481) := by
    rw [show ((2000481 / 2000000) : ℝ) = ((2000000 / 2000481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8092_neg : (15033 / 62500000) ≤ -Real.log (1999519 / 2000000) ∧
    -Real.log (1999519 / 2000000) ≤ (240529 / 1000000000) := by
  have h := checkLog_sound (w := (481 / 3999519)) (n := 12)
    (lo := (15033 / 62500000)) (hi := (240529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999519) = 1/(1999519 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8092 : Bounds (-240529 / 1000000000) (-15033 / 62500000) (Real.log (1999519 / 2000000)) := by
  have h := reflection_log_8092_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8093_neg : (28588513 / 250000000) ≤ -Real.log (1000000 / 1121149) ∧
    -Real.log (1000000 / 1121149) ≤ (114354053 / 1000000000) := by
  have h := checkLog_sound (w := (121149 / 2121149)) (n := 12)
    (lo := (28588513 / 250000000)) (hi := (114354053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1121149 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1121149 / 1000000) = 1/(1000000 / 1121149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8093 : Bounds (28588513 / 250000000) (114354053 / 1000000000) (Real.log (1121149 / 1000000)) := by
  have h := reflection_log_8093_neg
  have he : Real.log (1121149 / 1000000) = -Real.log (1000000 / 1121149) := by
    rw [show ((1121149 / 1000000) : ℝ) = ((1000000 / 1121149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8094_neg : (64569953 / 500000000) ≤ -Real.log (878851 / 1000000) ∧
    -Real.log (878851 / 1000000) ≤ (129139907 / 1000000000) := by
  have h := checkLog_sound (w := (121149 / 1878851)) (n := 12)
    (lo := (64569953 / 500000000)) (hi := (129139907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 878851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 878851) = 1/(878851 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8094 : Bounds (-129139907 / 1000000000) (-64569953 / 500000000) (Real.log (878851 / 1000000)) := by
  have h := reflection_log_8094_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8095_neg : (114796357 / 1000000000) ≤ -Real.log (200000 / 224329) ∧
    -Real.log (200000 / 224329) ≤ (57398179 / 500000000) := by
  have h := checkLog_sound (w := (24329 / 424329)) (n := 12)
    (lo := (114796357 / 1000000000)) (hi := (57398179 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((224329 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(224329 / 200000) = 1/(200000 / 224329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8095 : Bounds (114796357 / 1000000000) (57398179 / 500000000) (Real.log (224329 / 200000)) := by
  have h := reflection_log_8095_neg
  have he : Real.log (224329 / 200000) = -Real.log (200000 / 224329) := by
    rw [show ((224329 / 200000) : ℝ) = ((200000 / 224329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8096_neg : (129704439 / 1000000000) ≤ -Real.log (175671 / 200000) ∧
    -Real.log (175671 / 200000) ≤ (3242611 / 25000000) := by
  have h := checkLog_sound (w := (24329 / 375671)) (n := 12)
    (lo := (129704439 / 1000000000)) (hi := (3242611 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 175671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 175671) = 1/(175671 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8096 : Bounds (-3242611 / 25000000) (-129704439 / 1000000000) (Real.log (175671 / 200000)) := by
  have h := reflection_log_8096_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8097_neg : (14908081 / 1000000000) ≤ -Real.log (39408099759 / 40000000000) ∧
    -Real.log (39408099759 / 40000000000) ≤ (7454041 / 500000000) := by
  have h := checkLog_sound (w := (591900241 / 79408099759)) (n := 12)
    (lo := (14908081 / 1000000000)) (hi := (7454041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39408099759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39408099759) = 1/(39408099759 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8097 : Bounds (-7454041 / 500000000) (-14908081 / 1000000000) (Real.log (39408099759 / 40000000000)) := by
  have h := reflection_log_8097_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8098_neg : (7392927 / 500000000) ≤ -Real.log (985322919799 / 1000000000000) ∧
    -Real.log (985322919799 / 1000000000000) ≤ (2957171 / 200000000) := by
  have h := checkLog_sound (w := (14677080201 / 1985322919799)) (n := 12)
    (lo := (7392927 / 500000000)) (hi := (2957171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 985322919799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 985322919799) = 1/(985322919799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8098 : Bounds (-2957171 / 200000000) (-7392927 / 500000000) (Real.log (985322919799 / 1000000000000)) := by
  have h := reflection_log_8098_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8099_neg : (121746979 / 500000000) ≤ -Real.log (500000000000 / 637849305513) ∧
    -Real.log (500000000000 / 637849305513) ≤ (243493959 / 1000000000) := by
  have h := checkLog_sound (w := (137849305513 / 1137849305513)) (n := 12)
    (lo := (121746979 / 500000000)) (hi := (243493959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((637849305513 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(637849305513 / 500000000000) = 1/(500000000000 / 637849305513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8099 : Bounds (121746979 / 500000000) (243493959 / 1000000000) (Real.log (637849305513 / 500000000000)) := by
  have h := reflection_log_8099_neg
  have he : Real.log (637849305513 / 500000000000) = -Real.log (500000000000 / 637849305513) := by
    rw [show ((637849305513 / 500000000000) : ℝ) = ((500000000000 / 637849305513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8100_neg : (61125199 / 250000000) ≤ -Real.log (25000000000 / 31924591993) ∧
    -Real.log (25000000000 / 31924591993) ≤ (244500797 / 1000000000) := by
  have h := checkLog_sound (w := (6924591993 / 56924591993)) (n := 12)
    (lo := (61125199 / 250000000)) (hi := (244500797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31924591993 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31924591993 / 25000000000) = 1/(25000000000 / 31924591993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8100 : Bounds (61125199 / 250000000) (244500797 / 1000000000) (Real.log (31924591993 / 25000000000)) := by
  have h := reflection_log_8100_neg
  have he : Real.log (31924591993 / 25000000000) = -Real.log (25000000000 / 31924591993) := by
    rw [show ((31924591993 / 25000000000) : ℝ) = ((25000000000 / 31924591993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8101_neg : (19581929 / 40000000) ≤ -Real.log (125000000000 / 203947368421) ∧
    -Real.log (125000000000 / 203947368421) ≤ (244774113 / 500000000) := by
  have h := checkLog_sound (w := (78947368421 / 328947368421)) (n := 12)
    (lo := (19581929 / 40000000)) (hi := (244774113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((203947368421 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(203947368421 / 125000000000) = 1/(125000000000 / 203947368421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8101 : Bounds (19581929 / 40000000) (244774113 / 500000000) (Real.log (203947368421 / 125000000000)) := by
  have h := reflection_log_8101_neg
  have he : Real.log (203947368421 / 125000000000) = -Real.log (125000000000 / 203947368421) := by
    rw [show ((203947368421 / 125000000000) : ℝ) = ((125000000000 / 203947368421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8102_neg : (490609481 / 1000000000) ≤ -Real.log (62500000000 / 102081961817) ∧
    -Real.log (62500000000 / 102081961817) ≤ (245304741 / 500000000) := by
  have h := checkLog_sound (w := (39581961817 / 164581961817)) (n := 12)
    (lo := (490609481 / 1000000000)) (hi := (245304741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102081961817 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102081961817 / 62500000000) = 1/(62500000000 / 102081961817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8102 : Bounds (490609481 / 1000000000) (245304741 / 500000000) (Real.log (102081961817 / 62500000000)) := by
  have h := reflection_log_8102_neg
  have he : Real.log (102081961817 / 62500000000) = -Real.log (62500000000 / 102081961817) := by
    rw [show ((102081961817 / 62500000000) : ℝ) = ((62500000000 / 102081961817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8103_neg : (107958753 / 500000000) ≤ -Real.log (1000 / 1241) ∧
    -Real.log (1000 / 1241) ≤ (215917507 / 1000000000) := by
  have h := checkLog_sound (w := (241 / 2241)) (n := 12)
    (lo := (107958753 / 500000000)) (hi := (215917507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1241 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1241 / 1000) = 1/(1000 / 1241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8103 : Bounds (107958753 / 500000000) (215917507 / 1000000000) (Real.log (1241 / 1000)) := by
  have h := reflection_log_8103_neg
  have he : Real.log (1241 / 1000) = -Real.log (1000 / 1241) := by
    rw [show ((1241 / 1000) : ℝ) = ((1000 / 1241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8104_neg : (275753501 / 1000000000) ≤ -Real.log (759 / 1000) ∧
    -Real.log (759 / 1000) ≤ (137876751 / 500000000) := by
  have h := checkLog_sound (w := (241 / 1759)) (n := 12)
    (lo := (275753501 / 1000000000)) (hi := (137876751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 759) = 1/(759 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8104 : Bounds (-137876751 / 500000000) (-275753501 / 1000000000) (Real.log (759 / 1000)) := by
  have h := reflection_log_8104_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8105_neg : (24097 / 100000000) ≤ -Real.log (1000000 / 1000241) ∧
    -Real.log (1000000 / 1000241) ≤ (240971 / 1000000000) := by
  have h := checkLog_sound (w := (241 / 2000241)) (n := 12)
    (lo := (24097 / 100000000)) (hi := (240971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000241 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000241 / 1000000) = 1/(1000000 / 1000241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8105 : Bounds (24097 / 100000000) (240971 / 1000000000) (Real.log (1000241 / 1000000)) := by
  have h := reflection_log_8105_neg
  have he : Real.log (1000241 / 1000000) = -Real.log (1000000 / 1000241) := by
    rw [show ((1000241 / 1000000) : ℝ) = ((1000000 / 1000241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8106_neg : (241029 / 1000000000) ≤ -Real.log (999759 / 1000000) ∧
    -Real.log (999759 / 1000000) ≤ (24103 / 100000000) := by
  have h := checkLog_sound (w := (241 / 1999759)) (n := 12)
    (lo := (241029 / 1000000000)) (hi := (24103 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999759) = 1/(999759 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8106 : Bounds (-24103 / 100000000) (-241029 / 1000000000) (Real.log (999759 / 1000000)) := by
  have h := reflection_log_8106_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8107_neg : (57292073 / 500000000) ≤ -Real.log (1000000 / 1121407) ∧
    -Real.log (1000000 / 1121407) ≤ (114584147 / 1000000000) := by
  have h := checkLog_sound (w := (121407 / 2121407)) (n := 12)
    (lo := (57292073 / 500000000)) (hi := (114584147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1121407 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1121407 / 1000000) = 1/(1000000 / 1121407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8107 : Bounds (57292073 / 500000000) (114584147 / 1000000000) (Real.log (1121407 / 1000000)) := by
  have h := reflection_log_8107_neg
  have he : Real.log (1121407 / 1000000) = -Real.log (1000000 / 1121407) := by
    rw [show ((1121407 / 1000000) : ℝ) = ((1000000 / 1121407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8108_neg : (64716757 / 500000000) ≤ -Real.log (878593 / 1000000) ∧
    -Real.log (878593 / 1000000) ≤ (25886703 / 200000000) := by
  have h := checkLog_sound (w := (121407 / 1878593)) (n := 12)
    (lo := (64716757 / 500000000)) (hi := (25886703 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 878593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 878593) = 1/(878593 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8108 : Bounds (-25886703 / 200000000) (-64716757 / 500000000) (Real.log (878593 / 1000000)) := by
  have h := reflection_log_8108_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8109_neg : (115027241 / 1000000000) ≤ -Real.log (62500 / 70119) ∧
    -Real.log (62500 / 70119) ≤ (57513621 / 500000000) := by
  have h := checkLog_sound (w := (7619 / 132619)) (n := 12)
    (lo := (115027241 / 1000000000)) (hi := (57513621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70119 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(70119 / 62500) = 1/(62500 / 70119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8109 : Bounds (115027241 / 1000000000) (57513621 / 500000000) (Real.log (70119 / 62500)) := by
  have h := reflection_log_8109_neg
  have he : Real.log (70119 / 62500) = -Real.log (62500 / 70119) := by
    rw [show ((70119 / 62500) : ℝ) = ((62500 / 70119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8110_neg : (129999351 / 1000000000) ≤ -Real.log (54881 / 62500) ∧
    -Real.log (54881 / 62500) ≤ (16249919 / 125000000) := by
  have h := checkLog_sound (w := (7619 / 117381)) (n := 12)
    (lo := (129999351 / 1000000000)) (hi := (16249919 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 54881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 54881) = 1/(54881 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8110 : Bounds (-16249919 / 125000000) (-129999351 / 1000000000) (Real.log (54881 / 62500)) := by
  have h := reflection_log_8110_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8111_neg : (14972109 / 1000000000) ≤ -Real.log (3848200839 / 3906250000) ∧
    -Real.log (3848200839 / 3906250000) ≤ (1497211 / 100000000) := by
  have h := checkLog_sound (w := (58049161 / 7754450839)) (n := 12)
    (lo := (14972109 / 1000000000)) (hi := (1497211 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3848200839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3848200839) = 1/(3848200839 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8111 : Bounds (-1497211 / 100000000) (-14972109 / 1000000000) (Real.log (3848200839 / 3906250000)) := by
  have h := reflection_log_8111_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8112_neg : (14849367 / 1000000000) ≤ -Real.log (985260340351 / 1000000000000) ∧
    -Real.log (985260340351 / 1000000000000) ≤ (1856171 / 125000000) := by
  have h := checkLog_sound (w := (14739659649 / 1985260340351)) (n := 12)
    (lo := (14849367 / 1000000000)) (hi := (1856171 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 985260340351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 985260340351) = 1/(985260340351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8112 : Bounds (-1856171 / 125000000) (-14849367 / 1000000000) (Real.log (985260340351 / 1000000000000)) := by
  have h := reflection_log_8112_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8113_neg : (244017661 / 1000000000) ≤ -Real.log (500000000000 / 638183436471) ∧
    -Real.log (500000000000 / 638183436471) ≤ (122008831 / 500000000) := by
  have h := checkLog_sound (w := (138183436471 / 1138183436471)) (n := 12)
    (lo := (244017661 / 1000000000)) (hi := (122008831 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((638183436471 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(638183436471 / 500000000000) = 1/(500000000000 / 638183436471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8113 : Bounds (244017661 / 1000000000) (122008831 / 500000000) (Real.log (638183436471 / 500000000000)) := by
  have h := reflection_log_8113_neg
  have he : Real.log (638183436471 / 500000000000) = -Real.log (500000000000 / 638183436471) := by
    rw [show ((638183436471 / 500000000000) : ℝ) = ((500000000000 / 638183436471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8114_neg : (245026593 / 1000000000) ≤ -Real.log (500000000000 / 638827645269) ∧
    -Real.log (500000000000 / 638827645269) ≤ (122513297 / 500000000) := by
  have h := checkLog_sound (w := (138827645269 / 1138827645269)) (n := 12)
    (lo := (245026593 / 1000000000)) (hi := (122513297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((638827645269 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(638827645269 / 500000000000) = 1/(500000000000 / 638827645269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8114 : Bounds (245026593 / 1000000000) (122513297 / 500000000) (Real.log (638827645269 / 500000000000)) := by
  have h := reflection_log_8114_neg
  have he : Real.log (638827645269 / 500000000000) = -Real.log (500000000000 / 638827645269) := by
    rw [show ((638827645269 / 500000000000) : ℝ) = ((500000000000 / 638827645269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8115_neg : (490609481 / 1000000000) ≤ -Real.log (100000000000 / 163331138907) ∧
    -Real.log (100000000000 / 163331138907) ≤ (245304741 / 500000000) := by
  have h := checkLog_sound (w := (63331138907 / 263331138907)) (n := 12)
    (lo := (490609481 / 1000000000)) (hi := (245304741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163331138907 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163331138907 / 100000000000) = 1/(100000000000 / 163331138907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8115 : Bounds (490609481 / 1000000000) (245304741 / 500000000) (Real.log (163331138907 / 100000000000)) := by
  have h := reflection_log_8115_neg
  have he : Real.log (163331138907 / 100000000000) = -Real.log (100000000000 / 163331138907) := by
    rw [show ((163331138907 / 100000000000) : ℝ) = ((100000000000 / 163331138907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8116_neg : (491671007 / 1000000000) ≤ -Real.log (250000000000 / 408761528327) ∧
    -Real.log (250000000000 / 408761528327) ≤ (15364719 / 31250000) := by
  have h := checkLog_sound (w := (158761528327 / 658761528327)) (n := 12)
    (lo := (491671007 / 1000000000)) (hi := (15364719 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((408761528327 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(408761528327 / 250000000000) = 1/(250000000000 / 408761528327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8116 : Bounds (491671007 / 1000000000) (15364719 / 31250000) (Real.log (408761528327 / 250000000000)) := by
  have h := reflection_log_8116_neg
  have he : Real.log (408761528327 / 250000000000) = -Real.log (250000000000 / 408761528327) := by
    rw [show ((408761528327 / 250000000000) : ℝ) = ((250000000000 / 408761528327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8117_neg : (8652813 / 40000000) ≤ -Real.log (2000 / 2483) ∧
    -Real.log (2000 / 2483) ≤ (108160163 / 500000000) := by
  have h := checkLog_sound (w := (483 / 4483)) (n := 12)
    (lo := (8652813 / 40000000)) (hi := (108160163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2483 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2483 / 2000) = 1/(2000 / 2483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8117 : Bounds (8652813 / 40000000) (108160163 / 500000000) (Real.log (2483 / 2000)) := by
  have h := reflection_log_8117_neg
  have he : Real.log (2483 / 2000) = -Real.log (2000 / 2483) := by
    rw [show ((2483 / 2000) : ℝ) = ((2000 / 2483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8118_neg : (863789 / 3125000) ≤ -Real.log (1517 / 2000) ∧
    -Real.log (1517 / 2000) ≤ (276412481 / 1000000000) := by
  have h := checkLog_sound (w := (483 / 3517)) (n := 12)
    (lo := (863789 / 3125000)) (hi := (276412481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1517) = 1/(1517 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8118 : Bounds (-276412481 / 1000000000) (-863789 / 3125000) (Real.log (1517 / 2000)) := by
  have h := reflection_log_8118_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8119_neg : (24147 / 100000000) ≤ -Real.log (2000000 / 2000483) ∧
    -Real.log (2000000 / 2000483) ≤ (241471 / 1000000000) := by
  have h := checkLog_sound (w := (483 / 4000483)) (n := 12)
    (lo := (24147 / 100000000)) (hi := (241471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000483 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000483 / 2000000) = 1/(2000000 / 2000483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8119 : Bounds (24147 / 100000000) (241471 / 1000000000) (Real.log (2000483 / 2000000)) := by
  have h := reflection_log_8119_neg
  have he : Real.log (2000483 / 2000000) = -Real.log (2000000 / 2000483) := by
    rw [show ((2000483 / 2000000) : ℝ) = ((2000000 / 2000483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8120_neg : (241529 / 1000000000) ≤ -Real.log (1999517 / 2000000) ∧
    -Real.log (1999517 / 2000000) ≤ (24153 / 100000000) := by
  have h := checkLog_sound (w := (483 / 3999517)) (n := 12)
    (lo := (241529 / 1000000000)) (hi := (24153 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999517) = 1/(1999517 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8120 : Bounds (-24153 / 100000000) (-241529 / 1000000000) (Real.log (1999517 / 2000000)) := by
  have h := reflection_log_8120_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8121_neg : (114813297 / 1000000000) ≤ -Real.log (15625 / 17526) ∧
    -Real.log (15625 / 17526) ≤ (57406649 / 500000000) := by
  have h := checkLog_sound (w := (1901 / 33151)) (n := 12)
    (lo := (114813297 / 1000000000)) (hi := (57406649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17526 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17526 / 15625) = 1/(15625 / 17526) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8121 : Bounds (114813297 / 1000000000) (57406649 / 500000000) (Real.log (17526 / 15625)) := by
  have h := reflection_log_8121_neg
  have he : Real.log (17526 / 15625) = -Real.log (15625 / 17526) := by
    rw [show ((17526 / 15625) : ℝ) = ((15625 / 17526) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8122_neg : (12972607 / 100000000) ≤ -Real.log (13724 / 15625) ∧
    -Real.log (13724 / 15625) ≤ (129726071 / 1000000000) := by
  have h := checkLog_sound (w := (1901 / 29349)) (n := 12)
    (lo := (12972607 / 100000000)) (hi := (129726071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13724) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 13724) = 1/(13724 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8122 : Bounds (-129726071 / 1000000000) (-12972607 / 100000000) (Real.log (13724 / 15625)) := by
  have h := reflection_log_8122_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8123_neg : (115257181 / 1000000000) ≤ -Real.log (500000 / 561081) ∧
    -Real.log (500000 / 561081) ≤ (57628591 / 500000000) := by
  have h := checkLog_sound (w := (61081 / 1061081)) (n := 12)
    (lo := (115257181 / 1000000000)) (hi := (57628591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((561081 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(561081 / 500000) = 1/(500000 / 561081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8123 : Bounds (115257181 / 1000000000) (57628591 / 500000000) (Real.log (561081 / 500000)) := by
  have h := reflection_log_8123_neg
  have he : Real.log (561081 / 500000) = -Real.log (500000 / 561081) := by
    rw [show ((561081 / 500000) : ℝ) = ((500000 / 561081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8124_neg : (32573303 / 250000000) ≤ -Real.log (438919 / 500000) ∧
    -Real.log (438919 / 500000) ≤ (130293213 / 1000000000) := by
  have h := checkLog_sound (w := (61081 / 938919)) (n := 12)
    (lo := (32573303 / 250000000)) (hi := (130293213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 438919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 438919) = 1/(438919 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8124 : Bounds (-130293213 / 1000000000) (-32573303 / 250000000) (Real.log (438919 / 500000)) := by
  have h := reflection_log_8124_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8125_neg : (1503603 / 100000000) ≤ -Real.log (246269111439 / 250000000000) ∧
    -Real.log (246269111439 / 250000000000) ≤ (15036031 / 1000000000) := by
  have h := checkLog_sound (w := (3730888561 / 496269111439)) (n := 12)
    (lo := (1503603 / 100000000)) (hi := (15036031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246269111439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246269111439) = 1/(246269111439 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8125 : Bounds (-15036031 / 1000000000) (-1503603 / 100000000) (Real.log (246269111439 / 250000000000)) := by
  have h := reflection_log_8125_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8126_neg : (14912773 / 1000000000) ≤ -Real.log (240526824 / 244140625) ∧
    -Real.log (240526824 / 244140625) ≤ (7456387 / 500000000) := by
  have h := checkLog_sound (w := (3613801 / 484667449)) (n := 12)
    (lo := (14912773 / 1000000000)) (hi := (7456387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 240526824) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 240526824) = 1/(240526824 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8126 : Bounds (-7456387 / 500000000) (-14912773 / 1000000000) (Real.log (240526824 / 244140625)) := by
  have h := reflection_log_8126_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8127_neg : (244539367 / 1000000000) ≤ -Real.log (250000000000 / 319258233751) ∧
    -Real.log (250000000000 / 319258233751) ≤ (30567421 / 125000000) := by
  have h := checkLog_sound (w := (69258233751 / 569258233751)) (n := 12)
    (lo := (244539367 / 1000000000)) (hi := (30567421 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((319258233751 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(319258233751 / 250000000000) = 1/(250000000000 / 319258233751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8127 : Bounds (244539367 / 1000000000) (30567421 / 125000000) (Real.log (319258233751 / 250000000000)) := by
  have h := reflection_log_8127_neg
  have he : Real.log (319258233751 / 250000000000) = -Real.log (250000000000 / 319258233751) := by
    rw [show ((319258233751 / 250000000000) : ℝ) = ((250000000000 / 319258233751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0127 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8128_neg : (122775197 / 500000000) ≤ -Real.log (25000000000 / 31958117557) ∧
    -Real.log (25000000000 / 31958117557) ≤ (49110079 / 200000000) := by
  have h := checkLog_sound (w := (6958117557 / 56958117557)) (n := 12)
    (lo := (122775197 / 500000000)) (hi := (49110079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31958117557 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31958117557 / 25000000000) = 1/(25000000000 / 31958117557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8128 : Bounds (122775197 / 500000000) (49110079 / 200000000) (Real.log (31958117557 / 25000000000)) := by
  have h := reflection_log_8128_neg
  have he : Real.log (31958117557 / 25000000000) = -Real.log (25000000000 / 31958117557) := by
    rw [show ((31958117557 / 25000000000) : ℝ) = ((25000000000 / 31958117557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8129_neg : (491671007 / 1000000000) ≤ -Real.log (500000000000 / 817523056653) ∧
    -Real.log (500000000000 / 817523056653) ≤ (15364719 / 31250000) := by
  have h := checkLog_sound (w := (317523056653 / 1317523056653)) (n := 12)
    (lo := (491671007 / 1000000000)) (hi := (15364719 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((817523056653 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(817523056653 / 500000000000) = 1/(500000000000 / 817523056653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8129 : Bounds (491671007 / 1000000000) (15364719 / 31250000) (Real.log (817523056653 / 500000000000)) := by
  have h := reflection_log_8129_neg
  have he : Real.log (817523056653 / 500000000000) = -Real.log (500000000000 / 817523056653) := by
    rw [show ((817523056653 / 500000000000) : ℝ) = ((500000000000 / 817523056653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8130_neg : (246366403 / 500000000) ≤ -Real.log (100000000000 / 163678312459) ∧
    -Real.log (100000000000 / 163678312459) ≤ (492732807 / 1000000000) := by
  have h := checkLog_sound (w := (63678312459 / 263678312459)) (n := 12)
    (lo := (246366403 / 500000000)) (hi := (492732807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163678312459 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163678312459 / 100000000000) = 1/(100000000000 / 163678312459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8130 : Bounds (246366403 / 500000000) (492732807 / 1000000000) (Real.log (163678312459 / 100000000000)) := by
  have h := reflection_log_8130_neg
  have he : Real.log (163678312459 / 100000000000) = -Real.log (100000000000 / 163678312459) := by
    rw [show ((163678312459 / 100000000000) : ℝ) = ((100000000000 / 163678312459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8131_neg : (216722983 / 1000000000) ≤ -Real.log (500 / 621) ∧
    -Real.log (500 / 621) ≤ (27090373 / 125000000) := by
  have h := checkLog_sound (w := (121 / 1121)) (n := 12)
    (lo := (216722983 / 1000000000)) (hi := (27090373 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(621 / 500) = 1/(500 / 621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8131 : Bounds (216722983 / 1000000000) (27090373 / 125000000) (Real.log (621 / 500)) := by
  have h := reflection_log_8131_neg
  have he : Real.log (621 / 500) = -Real.log (500 / 621) := by
    rw [show ((621 / 500) : ℝ) = ((500 / 621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8132_neg : (277071893 / 1000000000) ≤ -Real.log (379 / 500) ∧
    -Real.log (379 / 500) ≤ (138535947 / 500000000) := by
  have h := checkLog_sound (w := (121 / 879)) (n := 12)
    (lo := (277071893 / 1000000000)) (hi := (138535947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 379) = 1/(379 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8132 : Bounds (-138535947 / 500000000) (-277071893 / 1000000000) (Real.log (379 / 500)) := by
  have h := reflection_log_8132_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8133_neg : (24197 / 100000000) ≤ -Real.log (500000 / 500121) ∧
    -Real.log (500000 / 500121) ≤ (241971 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 1000121)) (n := 12)
    (lo := (24197 / 100000000)) (hi := (241971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500121 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500121 / 500000) = 1/(500000 / 500121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8133 : Bounds (24197 / 100000000) (241971 / 1000000000) (Real.log (500121 / 500000)) := by
  have h := reflection_log_8133_neg
  have he : Real.log (500121 / 500000) = -Real.log (500000 / 500121) := by
    rw [show ((500121 / 500000) : ℝ) = ((500000 / 500121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8134_neg : (242029 / 1000000000) ≤ -Real.log (499879 / 500000) ∧
    -Real.log (499879 / 500000) ≤ (24203 / 100000000) := by
  have h := checkLog_sound (w := (121 / 999879)) (n := 12)
    (lo := (242029 / 1000000000)) (hi := (24203 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499879) = 1/(499879 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8134 : Bounds (-24203 / 100000000) (-242029 / 1000000000) (Real.log (499879 / 500000)) := by
  have h := reflection_log_8134_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8135_neg : (23008657 / 200000000) ≤ -Real.log (500000 / 560961) ∧
    -Real.log (500000 / 560961) ≤ (57521643 / 500000000) := by
  have h := checkLog_sound (w := (60961 / 1060961)) (n := 12)
    (lo := (23008657 / 200000000)) (hi := (57521643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((560961 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(560961 / 500000) = 1/(500000 / 560961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8135 : Bounds (23008657 / 200000000) (57521643 / 500000000) (Real.log (560961 / 500000)) := by
  have h := reflection_log_8135_neg
  have he : Real.log (560961 / 500000) = -Real.log (500000 / 560961) := by
    rw [show ((560961 / 500000) : ℝ) = ((500000 / 560961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8136_neg : (130019851 / 1000000000) ≤ -Real.log (439039 / 500000) ∧
    -Real.log (439039 / 500000) ≤ (32504963 / 250000000) := by
  have h := checkLog_sound (w := (60961 / 939039)) (n := 12)
    (lo := (130019851 / 1000000000)) (hi := (32504963 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 439039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 439039) = 1/(439039 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8136 : Bounds (-32504963 / 250000000) (-130019851 / 1000000000) (Real.log (439039 / 500000)) := by
  have h := reflection_log_8136_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8137_neg : (28871767 / 250000000) ≤ -Real.log (50000 / 56121) ∧
    -Real.log (50000 / 56121) ≤ (115487069 / 1000000000) := by
  have h := checkLog_sound (w := (6121 / 106121)) (n := 12)
    (lo := (28871767 / 250000000)) (hi := (115487069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56121 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56121 / 50000) = 1/(50000 / 56121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8137 : Bounds (28871767 / 250000000) (115487069 / 1000000000) (Real.log (56121 / 50000)) := by
  have h := reflection_log_8137_neg
  have he : Real.log (56121 / 50000) = -Real.log (50000 / 56121) := by
    rw [show ((56121 / 50000) : ℝ) = ((50000 / 56121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8138_neg : (130587159 / 1000000000) ≤ -Real.log (43879 / 50000) ∧
    -Real.log (43879 / 50000) ≤ (3264679 / 25000000) := by
  have h := checkLog_sound (w := (6121 / 93879)) (n := 12)
    (lo := (130587159 / 1000000000)) (hi := (3264679 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 43879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 43879) = 1/(43879 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8138 : Bounds (-3264679 / 25000000) (-130587159 / 1000000000) (Real.log (43879 / 50000)) := by
  have h := reflection_log_8138_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8139_neg : (15100091 / 1000000000) ≤ -Real.log (2462533359 / 2500000000) ∧
    -Real.log (2462533359 / 2500000000) ≤ (3775023 / 250000000) := by
  have h := checkLog_sound (w := (37466641 / 4962533359)) (n := 12)
    (lo := (15100091 / 1000000000)) (hi := (3775023 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2462533359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2462533359) = 1/(2462533359 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8139 : Bounds (-3775023 / 250000000) (-15100091 / 1000000000) (Real.log (2462533359 / 2500000000)) := by
  have h := reflection_log_8139_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8140_neg : (2995313 / 200000000) ≤ -Real.log (246283756479 / 250000000000) ∧
    -Real.log (246283756479 / 250000000000) ≤ (7488283 / 500000000) := by
  have h := checkLog_sound (w := (3716243521 / 496283756479)) (n := 12)
    (lo := (2995313 / 200000000)) (hi := (7488283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246283756479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246283756479) = 1/(246283756479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8140 : Bounds (-7488283 / 500000000) (-2995313 / 200000000) (Real.log (246283756479 / 250000000000)) := by
  have h := reflection_log_8140_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8141_neg : (7658223 / 31250000) ≤ -Real.log (250000000000 / 319425495229) ∧
    -Real.log (250000000000 / 319425495229) ≤ (245063137 / 1000000000) := by
  have h := checkLog_sound (w := (69425495229 / 569425495229)) (n := 12)
    (lo := (7658223 / 31250000)) (hi := (245063137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((319425495229 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(319425495229 / 250000000000) = 1/(250000000000 / 319425495229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8141 : Bounds (7658223 / 31250000) (245063137 / 1000000000) (Real.log (319425495229 / 250000000000)) := by
  have h := reflection_log_8141_neg
  have he : Real.log (319425495229 / 250000000000) = -Real.log (250000000000 / 319425495229) := by
    rw [show ((319425495229 / 250000000000) : ℝ) = ((250000000000 / 319425495229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8142_neg : (61518557 / 250000000) ≤ -Real.log (125000000000 / 159874313453) ∧
    -Real.log (125000000000 / 159874313453) ≤ (246074229 / 1000000000) := by
  have h := checkLog_sound (w := (34874313453 / 284874313453)) (n := 12)
    (lo := (61518557 / 250000000)) (hi := (246074229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159874313453 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159874313453 / 125000000000) = 1/(125000000000 / 159874313453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8142 : Bounds (61518557 / 250000000) (246074229 / 1000000000) (Real.log (159874313453 / 125000000000)) := by
  have h := reflection_log_8142_neg
  have he : Real.log (159874313453 / 125000000000) = -Real.log (125000000000 / 159874313453) := by
    rw [show ((159874313453 / 125000000000) : ℝ) = ((125000000000 / 159874313453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8143_neg : (246366403 / 500000000) ≤ -Real.log (250000000000 / 409195781147) ∧
    -Real.log (250000000000 / 409195781147) ≤ (492732807 / 1000000000) := by
  have h := checkLog_sound (w := (159195781147 / 659195781147)) (n := 12)
    (lo := (246366403 / 500000000)) (hi := (492732807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((409195781147 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(409195781147 / 250000000000) = 1/(250000000000 / 409195781147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8143 : Bounds (246366403 / 500000000) (492732807 / 1000000000) (Real.log (409195781147 / 250000000000)) := by
  have h := reflection_log_8143_neg
  have he : Real.log (409195781147 / 250000000000) = -Real.log (250000000000 / 409195781147) := by
    rw [show ((409195781147 / 250000000000) : ℝ) = ((250000000000 / 409195781147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8144_neg : (123448719 / 250000000) ≤ -Real.log (500000000000 / 819261213721) ∧
    -Real.log (500000000000 / 819261213721) ≤ (493794877 / 1000000000) := by
  have h := checkLog_sound (w := (319261213721 / 1319261213721)) (n := 12)
    (lo := (123448719 / 250000000)) (hi := (493794877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819261213721 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819261213721 / 500000000000) = 1/(500000000000 / 819261213721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8144 : Bounds (123448719 / 250000000) (493794877 / 1000000000) (Real.log (819261213721 / 500000000000)) := by
  have h := reflection_log_8144_neg
  have he : Real.log (819261213721 / 500000000000) = -Real.log (500000000000 / 819261213721) := by
    rw [show ((819261213721 / 500000000000) : ℝ) = ((500000000000 / 819261213721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8145_neg : (108562739 / 500000000) ≤ -Real.log (400 / 497) ∧
    -Real.log (400 / 497) ≤ (217125479 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 897)) (n := 12)
    (lo := (108562739 / 500000000)) (hi := (217125479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((497 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(497 / 400) = 1/(400 / 497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8145 : Bounds (108562739 / 500000000) (217125479 / 1000000000) (Real.log (497 / 400)) := by
  have h := reflection_log_8145_neg
  have he : Real.log (497 / 400) = -Real.log (400 / 497) := by
    rw [show ((497 / 400) : ℝ) = ((400 / 497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8146_neg : (277731741 / 1000000000) ≤ -Real.log (303 / 400) ∧
    -Real.log (303 / 400) ≤ (138865871 / 500000000) := by
  have h := checkLog_sound (w := (97 / 703)) (n := 12)
    (lo := (277731741 / 1000000000)) (hi := (138865871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 303) = 1/(303 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8146 : Bounds (-138865871 / 500000000) (-277731741 / 1000000000) (Real.log (303 / 400)) := by
  have h := reflection_log_8146_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8147_neg : (24247 / 100000000) ≤ -Real.log (400000 / 400097) ∧
    -Real.log (400000 / 400097) ≤ (242471 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 800097)) (n := 12)
    (lo := (24247 / 100000000)) (hi := (242471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400097 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400097 / 400000) = 1/(400000 / 400097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8147 : Bounds (24247 / 100000000) (242471 / 1000000000) (Real.log (400097 / 400000)) := by
  have h := reflection_log_8147_neg
  have he : Real.log (400097 / 400000) = -Real.log (400000 / 400097) := by
    rw [show ((400097 / 400000) : ℝ) = ((400000 / 400097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8148_neg : (242529 / 1000000000) ≤ -Real.log (399903 / 400000) ∧
    -Real.log (399903 / 400000) ≤ (24253 / 100000000) := by
  have h := checkLog_sound (w := (97 / 799903)) (n := 12)
    (lo := (242529 / 1000000000)) (hi := (24253 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399903) = 1/(399903 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8148 : Bounds (-24253 / 100000000) (-242529 / 1000000000) (Real.log (399903 / 400000)) := by
  have h := reflection_log_8148_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8149_neg : (57636611 / 500000000) ≤ -Real.log (50000 / 56109) ∧
    -Real.log (50000 / 56109) ≤ (115273223 / 1000000000) := by
  have h := checkLog_sound (w := (6109 / 106109)) (n := 12)
    (lo := (57636611 / 500000000)) (hi := (115273223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56109 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56109 / 50000) = 1/(50000 / 56109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8149 : Bounds (57636611 / 500000000) (115273223 / 1000000000) (Real.log (56109 / 50000)) := by
  have h := reflection_log_8149_neg
  have he : Real.log (56109 / 50000) = -Real.log (50000 / 56109) := by
    rw [show ((56109 / 50000) : ℝ) = ((50000 / 56109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8150_neg : (130313717 / 1000000000) ≤ -Real.log (43891 / 50000) ∧
    -Real.log (43891 / 50000) ≤ (65156859 / 500000000) := by
  have h := checkLog_sound (w := (6109 / 93891)) (n := 12)
    (lo := (130313717 / 1000000000)) (hi := (65156859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 43891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 43891) = 1/(43891 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8150 : Bounds (-65156859 / 500000000) (-130313717 / 1000000000) (Real.log (43891 / 50000)) := by
  have h := reflection_log_8150_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8151_neg : (115717793 / 1000000000) ≤ -Real.log (1000000 / 1122679) ∧
    -Real.log (1000000 / 1122679) ≤ (57858897 / 500000000) := by
  have h := checkLog_sound (w := (122679 / 2122679)) (n := 12)
    (lo := (115717793 / 1000000000)) (hi := (57858897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1122679 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1122679 / 1000000) = 1/(1000000 / 1122679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8151 : Bounds (115717793 / 1000000000) (57858897 / 500000000) (Real.log (1122679 / 1000000)) := by
  have h := reflection_log_8151_neg
  have he : Real.log (1122679 / 1000000) = -Real.log (1000000 / 1122679) := by
    rw [show ((1122679 / 1000000) : ℝ) = ((1000000 / 1122679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8152_neg : (130882333 / 1000000000) ≤ -Real.log (877321 / 1000000) ∧
    -Real.log (877321 / 1000000) ≤ (65441167 / 500000000) := by
  have h := checkLog_sound (w := (122679 / 1877321)) (n := 12)
    (lo := (130882333 / 1000000000)) (hi := (65441167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 877321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 877321) = 1/(877321 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8152 : Bounds (-65441167 / 500000000) (-130882333 / 1000000000) (Real.log (877321 / 1000000)) := by
  have h := reflection_log_8152_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8153_neg : (15164539 / 1000000000) ≤ -Real.log (984949862959 / 1000000000000) ∧
    -Real.log (984949862959 / 1000000000000) ≤ (758227 / 50000000) := by
  have h := checkLog_sound (w := (15050137041 / 1984949862959)) (n := 12)
    (lo := (15164539 / 1000000000)) (hi := (758227 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984949862959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984949862959) = 1/(984949862959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8153 : Bounds (-758227 / 50000000) (-15164539 / 1000000000) (Real.log (984949862959 / 1000000000000)) := by
  have h := reflection_log_8153_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8154_neg : (3008099 / 200000000) ≤ -Real.log (2462680119 / 2500000000) ∧
    -Real.log (2462680119 / 2500000000) ≤ (940031 / 62500000) := by
  have h := checkLog_sound (w := (37319881 / 4962680119)) (n := 12)
    (lo := (3008099 / 200000000)) (hi := (940031 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2462680119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2462680119) = 1/(2462680119 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8154 : Bounds (-940031 / 62500000) (-3008099 / 200000000) (Real.log (2462680119 / 2500000000)) := by
  have h := reflection_log_8154_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8155_neg : (245586939 / 1000000000) ≤ -Real.log (250000000000 / 319592855027) ∧
    -Real.log (250000000000 / 319592855027) ≤ (12279347 / 50000000) := by
  have h := checkLog_sound (w := (69592855027 / 569592855027)) (n := 12)
    (lo := (245586939 / 1000000000)) (hi := (12279347 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((319592855027 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(319592855027 / 250000000000) = 1/(250000000000 / 319592855027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8155 : Bounds (245586939 / 1000000000) (12279347 / 50000000) (Real.log (319592855027 / 250000000000)) := by
  have h := reflection_log_8155_neg
  have he : Real.log (319592855027 / 250000000000) = -Real.log (250000000000 / 319592855027) := by
    rw [show ((319592855027 / 250000000000) : ℝ) = ((250000000000 / 319592855027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8156_neg : (123300063 / 500000000) ≤ -Real.log (500000000000 / 639833652677) ∧
    -Real.log (500000000000 / 639833652677) ≤ (246600127 / 1000000000) := by
  have h := checkLog_sound (w := (139833652677 / 1139833652677)) (n := 12)
    (lo := (123300063 / 500000000)) (hi := (246600127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((639833652677 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(639833652677 / 500000000000) = 1/(500000000000 / 639833652677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8156 : Bounds (123300063 / 500000000) (246600127 / 1000000000) (Real.log (639833652677 / 500000000000)) := by
  have h := reflection_log_8156_neg
  have he : Real.log (639833652677 / 500000000000) = -Real.log (500000000000 / 639833652677) := by
    rw [show ((639833652677 / 500000000000) : ℝ) = ((500000000000 / 639833652677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8157_neg : (123448719 / 250000000) ≤ -Real.log (12500000000 / 20481530343) ∧
    -Real.log (12500000000 / 20481530343) ≤ (493794877 / 1000000000) := by
  have h := checkLog_sound (w := (7981530343 / 32981530343)) (n := 12)
    (lo := (123448719 / 250000000)) (hi := (493794877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20481530343 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20481530343 / 12500000000) = 1/(12500000000 / 20481530343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8157 : Bounds (123448719 / 250000000) (493794877 / 1000000000) (Real.log (20481530343 / 12500000000)) := by
  have h := reflection_log_8157_neg
  have he : Real.log (20481530343 / 12500000000) = -Real.log (12500000000 / 20481530343) := by
    rw [show ((20481530343 / 12500000000) : ℝ) = ((12500000000 / 20481530343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8158_neg : (24742861 / 50000000) ≤ -Real.log (250000000000 / 410066006601) ∧
    -Real.log (250000000000 / 410066006601) ≤ (494857221 / 1000000000) := by
  have h := checkLog_sound (w := (160066006601 / 660066006601)) (n := 12)
    (lo := (24742861 / 50000000)) (hi := (494857221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((410066006601 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(410066006601 / 250000000000) = 1/(250000000000 / 410066006601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8158 : Bounds (24742861 / 50000000) (494857221 / 1000000000) (Real.log (410066006601 / 250000000000)) := by
  have h := reflection_log_8158_neg
  have he : Real.log (410066006601 / 250000000000) = -Real.log (250000000000 / 410066006601) := by
    rw [show ((410066006601 / 250000000000) : ℝ) = ((250000000000 / 410066006601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8159_neg : (54381953 / 250000000) ≤ -Real.log (1000 / 1243) ∧
    -Real.log (1000 / 1243) ≤ (217527813 / 1000000000) := by
  have h := checkLog_sound (w := (243 / 2243)) (n := 12)
    (lo := (54381953 / 250000000)) (hi := (217527813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1243 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1243 / 1000) = 1/(1000 / 1243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8159 : Bounds (54381953 / 250000000) (217527813 / 1000000000) (Real.log (1243 / 1000)) := by
  have h := reflection_log_8159_neg
  have he : Real.log (1243 / 1000) = -Real.log (1000 / 1243) := by
    rw [show ((1243 / 1000) : ℝ) = ((1000 / 1243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8160_neg : (11135681 / 40000000) ≤ -Real.log (757 / 1000) ∧
    -Real.log (757 / 1000) ≤ (139196013 / 500000000) := by
  have h := checkLog_sound (w := (243 / 1757)) (n := 12)
    (lo := (11135681 / 40000000)) (hi := (139196013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 757) = 1/(757 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8160 : Bounds (-139196013 / 500000000) (-11135681 / 40000000) (Real.log (757 / 1000)) := by
  have h := reflection_log_8160_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8161_neg : (24297 / 100000000) ≤ -Real.log (1000000 / 1000243) ∧
    -Real.log (1000000 / 1000243) ≤ (242971 / 1000000000) := by
  have h := checkLog_sound (w := (243 / 2000243)) (n := 12)
    (lo := (24297 / 100000000)) (hi := (242971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000243 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000243 / 1000000) = 1/(1000000 / 1000243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8161 : Bounds (24297 / 100000000) (242971 / 1000000000) (Real.log (1000243 / 1000000)) := by
  have h := reflection_log_8161_neg
  have he : Real.log (1000243 / 1000000) = -Real.log (1000000 / 1000243) := by
    rw [show ((1000243 / 1000000) : ℝ) = ((1000000 / 1000243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8162_neg : (243029 / 1000000000) ≤ -Real.log (999757 / 1000000) ∧
    -Real.log (999757 / 1000000) ≤ (24303 / 100000000) := by
  have h := checkLog_sound (w := (243 / 1999757)) (n := 12)
    (lo := (243029 / 1000000000)) (hi := (24303 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999757) = 1/(999757 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8162 : Bounds (-24303 / 100000000) (-243029 / 1000000000) (Real.log (999757 / 1000000)) := by
  have h := reflection_log_8162_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8163_neg : (23100621 / 200000000) ≤ -Real.log (500000 / 561219) ∧
    -Real.log (500000 / 561219) ≤ (57751553 / 500000000) := by
  have h := checkLog_sound (w := (61219 / 1061219)) (n := 12)
    (lo := (23100621 / 200000000)) (hi := (57751553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((561219 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(561219 / 500000) = 1/(500000 / 561219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8163 : Bounds (23100621 / 200000000) (57751553 / 500000000) (Real.log (561219 / 500000)) := by
  have h := reflection_log_8163_neg
  have he : Real.log (561219 / 500000) = -Real.log (500000 / 561219) := by
    rw [show ((561219 / 500000) : ℝ) = ((500000 / 561219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8164_neg : (13060767 / 100000000) ≤ -Real.log (438781 / 500000) ∧
    -Real.log (438781 / 500000) ≤ (130607671 / 1000000000) := by
  have h := checkLog_sound (w := (61219 / 938781)) (n := 12)
    (lo := (13060767 / 100000000)) (hi := (130607671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 438781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 438781) = 1/(438781 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8164 : Bounds (-130607671 / 1000000000) (-13060767 / 100000000) (Real.log (438781 / 500000)) := by
  have h := reflection_log_8164_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8165_neg : (57973787 / 500000000) ≤ -Real.log (1000000 / 1122937) ∧
    -Real.log (1000000 / 1122937) ≤ (4637903 / 40000000) := by
  have h := checkLog_sound (w := (122937 / 2122937)) (n := 12)
    (lo := (57973787 / 500000000)) (hi := (4637903 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1122937 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1122937 / 1000000) = 1/(1000000 / 1122937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8165 : Bounds (57973787 / 500000000) (4637903 / 40000000) (Real.log (1122937 / 1000000)) := by
  have h := reflection_log_8165_neg
  have he : Real.log (1122937 / 1000000) = -Real.log (1000000 / 1122937) := by
    rw [show ((1122937 / 1000000) : ℝ) = ((1000000 / 1122937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8166_neg : (131176453 / 1000000000) ≤ -Real.log (877063 / 1000000) ∧
    -Real.log (877063 / 1000000) ≤ (65588227 / 500000000) := by
  have h := checkLog_sound (w := (122937 / 1877063)) (n := 12)
    (lo := (131176453 / 1000000000)) (hi := (65588227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 877063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 877063) = 1/(877063 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8166 : Bounds (-65588227 / 500000000) (-131176453 / 1000000000) (Real.log (877063 / 1000000)) := by
  have h := reflection_log_8166_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8167_neg : (7614439 / 500000000) ≤ -Real.log (984886494031 / 1000000000000) ∧
    -Real.log (984886494031 / 1000000000000) ≤ (15228879 / 1000000000) := by
  have h := checkLog_sound (w := (15113505969 / 1984886494031)) (n := 12)
    (lo := (7614439 / 500000000)) (hi := (15228879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984886494031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984886494031) = 1/(984886494031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8167 : Bounds (-15228879 / 1000000000) (-7614439 / 500000000) (Real.log (984886494031 / 1000000000000)) := by
  have h := reflection_log_8167_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8168_neg : (3020913 / 200000000) ≤ -Real.log (246252234039 / 250000000000) ∧
    -Real.log (246252234039 / 250000000000) ≤ (7552283 / 500000000) := by
  have h := checkLog_sound (w := (3747765961 / 496252234039)) (n := 12)
    (lo := (3020913 / 200000000)) (hi := (7552283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246252234039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246252234039) = 1/(246252234039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8168 : Bounds (-7552283 / 500000000) (-3020913 / 200000000) (Real.log (246252234039 / 250000000000)) := by
  have h := reflection_log_8168_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8169_neg : (30763847 / 125000000) ≤ -Real.log (250000000000 / 319760313231) ∧
    -Real.log (250000000000 / 319760313231) ≤ (246110777 / 1000000000) := by
  have h := checkLog_sound (w := (69760313231 / 569760313231)) (n := 12)
    (lo := (30763847 / 125000000)) (hi := (246110777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((319760313231 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(319760313231 / 250000000000) = 1/(250000000000 / 319760313231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8169 : Bounds (30763847 / 125000000) (246110777 / 1000000000) (Real.log (319760313231 / 250000000000)) := by
  have h := reflection_log_8169_neg
  have he : Real.log (319760313231 / 250000000000) = -Real.log (250000000000 / 319760313231) := by
    rw [show ((319760313231 / 250000000000) : ℝ) = ((250000000000 / 319760313231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8170_neg : (247124027 / 1000000000) ≤ -Real.log (125000000000 / 160042237559) ∧
    -Real.log (125000000000 / 160042237559) ≤ (61781007 / 250000000) := by
  have h := checkLog_sound (w := (35042237559 / 285042237559)) (n := 12)
    (lo := (247124027 / 1000000000)) (hi := (61781007 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160042237559 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160042237559 / 125000000000) = 1/(125000000000 / 160042237559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8170 : Bounds (247124027 / 1000000000) (61781007 / 250000000) (Real.log (160042237559 / 125000000000)) := by
  have h := reflection_log_8170_neg
  have he : Real.log (160042237559 / 125000000000) = -Real.log (125000000000 / 160042237559) := by
    rw [show ((160042237559 / 125000000000) : ℝ) = ((125000000000 / 160042237559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8171_neg : (24742861 / 50000000) ≤ -Real.log (500000000000 / 820132013201) ∧
    -Real.log (500000000000 / 820132013201) ≤ (494857221 / 1000000000) := by
  have h := checkLog_sound (w := (320132013201 / 1320132013201)) (n := 12)
    (lo := (24742861 / 50000000)) (hi := (494857221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((820132013201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(820132013201 / 500000000000) = 1/(500000000000 / 820132013201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8171 : Bounds (24742861 / 50000000) (494857221 / 1000000000) (Real.log (820132013201 / 500000000000)) := by
  have h := reflection_log_8171_neg
  have he : Real.log (820132013201 / 500000000000) = -Real.log (500000000000 / 820132013201) := by
    rw [show ((820132013201 / 500000000000) : ℝ) = ((500000000000 / 820132013201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8172_neg : (247959919 / 500000000) ≤ -Real.log (125000000000 / 205250990753) ∧
    -Real.log (125000000000 / 205250990753) ≤ (495919839 / 1000000000) := by
  have h := checkLog_sound (w := (80250990753 / 330250990753)) (n := 12)
    (lo := (247959919 / 500000000)) (hi := (495919839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((205250990753 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(205250990753 / 125000000000) = 1/(125000000000 / 205250990753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8172 : Bounds (247959919 / 500000000) (495919839 / 1000000000) (Real.log (205250990753 / 125000000000)) := by
  have h := reflection_log_8172_neg
  have he : Real.log (205250990753 / 125000000000) = -Real.log (125000000000 / 205250990753) := by
    rw [show ((205250990753 / 125000000000) : ℝ) = ((125000000000 / 205250990753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8173_neg : (851289 / 3906250) ≤ -Real.log (2000 / 2487) ∧
    -Real.log (2000 / 2487) ≤ (43585997 / 200000000) := by
  have h := checkLog_sound (w := (487 / 4487)) (n := 12)
    (lo := (851289 / 3906250)) (hi := (43585997 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2487 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2487 / 2000) = 1/(2000 / 2487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8173 : Bounds (851289 / 3906250) (43585997 / 200000000) (Real.log (2487 / 2000)) := by
  have h := reflection_log_8173_neg
  have he : Real.log (2487 / 2000) = -Real.log (2000 / 2487) := by
    rw [show ((2487 / 2000) : ℝ) = ((2000 / 2487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8174_neg : (55810549 / 200000000) ≤ -Real.log (1513 / 2000) ∧
    -Real.log (1513 / 2000) ≤ (139526373 / 500000000) := by
  have h := checkLog_sound (w := (487 / 3513)) (n := 12)
    (lo := (55810549 / 200000000)) (hi := (139526373 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1513) = 1/(1513 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8174 : Bounds (-139526373 / 500000000) (-55810549 / 200000000) (Real.log (1513 / 2000)) := by
  have h := reflection_log_8174_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8175_neg : (24347 / 100000000) ≤ -Real.log (2000000 / 2000487) ∧
    -Real.log (2000000 / 2000487) ≤ (243471 / 1000000000) := by
  have h := checkLog_sound (w := (487 / 4000487)) (n := 12)
    (lo := (24347 / 100000000)) (hi := (243471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000487 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000487 / 2000000) = 1/(2000000 / 2000487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8175 : Bounds (24347 / 100000000) (243471 / 1000000000) (Real.log (2000487 / 2000000)) := by
  have h := reflection_log_8175_neg
  have he : Real.log (2000487 / 2000000) = -Real.log (2000000 / 2000487) := by
    rw [show ((2000487 / 2000000) : ℝ) = ((2000000 / 2000487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8176_neg : (243529 / 1000000000) ≤ -Real.log (1999513 / 2000000) ∧
    -Real.log (1999513 / 2000000) ≤ (24353 / 100000000) := by
  have h := checkLog_sound (w := (487 / 3999513)) (n := 12)
    (lo := (243529 / 1000000000)) (hi := (24353 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999513) = 1/(1999513 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8176 : Bounds (-24353 / 100000000) (-243529 / 1000000000) (Real.log (1999513 / 2000000)) := by
  have h := reflection_log_8176_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8177_neg : (23146587 / 200000000) ≤ -Real.log (125000 / 140337) ∧
    -Real.log (125000 / 140337) ≤ (14466617 / 125000000) := by
  have h := checkLog_sound (w := (15337 / 265337)) (n := 12)
    (lo := (23146587 / 200000000)) (hi := (14466617 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140337 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140337 / 125000) = 1/(125000 / 140337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8177 : Bounds (23146587 / 200000000) (14466617 / 125000000) (Real.log (140337 / 125000)) := by
  have h := reflection_log_8177_neg
  have he : Real.log (140337 / 125000) = -Real.log (125000 / 140337) := by
    rw [show ((140337 / 125000) : ℝ) = ((125000 / 140337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8178_neg : (13090171 / 100000000) ≤ -Real.log (109663 / 125000) ∧
    -Real.log (109663 / 125000) ≤ (130901711 / 1000000000) := by
  have h := checkLog_sound (w := (15337 / 234663)) (n := 12)
    (lo := (13090171 / 100000000)) (hi := (130901711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 109663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 109663) = 1/(109663 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8178 : Bounds (-130901711 / 1000000000) (-13090171 / 100000000) (Real.log (109663 / 125000)) := by
  have h := reflection_log_8178_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8179_neg : (116178193 / 1000000000) ≤ -Real.log (250000 / 280799) ∧
    -Real.log (250000 / 280799) ≤ (58089097 / 500000000) := by
  have h := checkLog_sound (w := (30799 / 530799)) (n := 12)
    (lo := (116178193 / 1000000000)) (hi := (58089097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((280799 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(280799 / 250000) = 1/(250000 / 280799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8179 : Bounds (116178193 / 1000000000) (58089097 / 500000000) (Real.log (280799 / 250000)) := by
  have h := reflection_log_8179_neg
  have he : Real.log (280799 / 250000) = -Real.log (250000 / 280799) := by
    rw [show ((280799 / 250000) : ℝ) = ((250000 / 280799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8180_neg : (657359 / 5000000) ≤ -Real.log (219201 / 250000) ∧
    -Real.log (219201 / 250000) ≤ (131471801 / 1000000000) := by
  have h := checkLog_sound (w := (30799 / 469201)) (n := 12)
    (lo := (657359 / 5000000)) (hi := (131471801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 219201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 219201) = 1/(219201 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8180 : Bounds (-131471801 / 1000000000) (-657359 / 5000000) (Real.log (219201 / 250000)) := by
  have h := reflection_log_8180_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8181_neg : (15293607 / 1000000000) ≤ -Real.log (61551421599 / 62500000000) ∧
    -Real.log (61551421599 / 62500000000) ≤ (1911701 / 125000000) := by
  have h := checkLog_sound (w := (948578401 / 124051421599)) (n := 12)
    (lo := (15293607 / 1000000000)) (hi := (1911701 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61551421599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61551421599) = 1/(61551421599 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8181 : Bounds (-1911701 / 125000000) (-15293607 / 1000000000) (Real.log (61551421599 / 62500000000)) := by
  have h := reflection_log_8181_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8182_neg : (7584387 / 500000000) ≤ -Real.log (15389776431 / 15625000000) ∧
    -Real.log (15389776431 / 15625000000) ≤ (606751 / 40000000) := by
  have h := checkLog_sound (w := (235223569 / 31014776431)) (n := 12)
    (lo := (7584387 / 500000000)) (hi := (606751 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15389776431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15389776431) = 1/(15389776431 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8182 : Bounds (-606751 / 40000000) (-7584387 / 500000000) (Real.log (15389776431 / 15625000000)) := by
  have h := reflection_log_8182_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8183_neg : (123317323 / 500000000) ≤ -Real.log (500000000000 / 639855739857) ∧
    -Real.log (500000000000 / 639855739857) ≤ (246634647 / 1000000000) := by
  have h := checkLog_sound (w := (139855739857 / 1139855739857)) (n := 12)
    (lo := (123317323 / 500000000)) (hi := (246634647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((639855739857 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(639855739857 / 500000000000) = 1/(500000000000 / 639855739857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8183 : Bounds (123317323 / 500000000) (246634647 / 1000000000) (Real.log (639855739857 / 500000000000)) := by
  have h := reflection_log_8183_neg
  have he : Real.log (639855739857 / 500000000000) = -Real.log (500000000000 / 639855739857) := by
    rw [show ((639855739857 / 500000000000) : ℝ) = ((500000000000 / 639855739857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8184_neg : (247649993 / 1000000000) ≤ -Real.log (125000000000 / 160126436467) ∧
    -Real.log (125000000000 / 160126436467) ≤ (123824997 / 500000000) := by
  have h := checkLog_sound (w := (35126436467 / 285126436467)) (n := 12)
    (lo := (247649993 / 1000000000)) (hi := (123824997 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160126436467 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160126436467 / 125000000000) = 1/(125000000000 / 160126436467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8184 : Bounds (247649993 / 1000000000) (123824997 / 500000000) (Real.log (160126436467 / 125000000000)) := by
  have h := reflection_log_8184_neg
  have he : Real.log (160126436467 / 125000000000) = -Real.log (125000000000 / 160126436467) := by
    rw [show ((160126436467 / 125000000000) : ℝ) = ((125000000000 / 160126436467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8185_neg : (247959919 / 500000000) ≤ -Real.log (500000000000 / 821003963011) ∧
    -Real.log (500000000000 / 821003963011) ≤ (495919839 / 1000000000) := by
  have h := checkLog_sound (w := (321003963011 / 1321003963011)) (n := 12)
    (lo := (247959919 / 500000000)) (hi := (495919839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821003963011 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(821003963011 / 500000000000) = 1/(500000000000 / 821003963011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8185 : Bounds (247959919 / 500000000) (495919839 / 1000000000) (Real.log (821003963011 / 500000000000)) := by
  have h := reflection_log_8185_neg
  have he : Real.log (821003963011 / 500000000000) = -Real.log (500000000000 / 821003963011) := by
    rw [show ((821003963011 / 500000000000) : ℝ) = ((500000000000 / 821003963011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8186_neg : (49698273 / 100000000) ≤ -Real.log (500000000000 / 821877065433) ∧
    -Real.log (500000000000 / 821877065433) ≤ (496982731 / 1000000000) := by
  have h := checkLog_sound (w := (321877065433 / 1321877065433)) (n := 12)
    (lo := (49698273 / 100000000)) (hi := (496982731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821877065433 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(821877065433 / 500000000000) = 1/(500000000000 / 821877065433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8186 : Bounds (49698273 / 100000000) (496982731 / 1000000000) (Real.log (821877065433 / 500000000000)) := by
  have h := reflection_log_8186_neg
  have he : Real.log (821877065433 / 500000000000) = -Real.log (500000000000 / 821877065433) := by
    rw [show ((821877065433 / 500000000000) : ℝ) = ((500000000000 / 821877065433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8187_neg : (109165997 / 500000000) ≤ -Real.log (250 / 311) ∧
    -Real.log (250 / 311) ≤ (43666399 / 200000000) := by
  have h := checkLog_sound (w := (61 / 561)) (n := 12)
    (lo := (109165997 / 500000000)) (hi := (43666399 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311 / 250) = 1/(250 / 311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8187 : Bounds (109165997 / 500000000) (43666399 / 200000000) (Real.log (311 / 250)) := by
  have h := reflection_log_8187_neg
  have he : Real.log (311 / 250) = -Real.log (250 / 311) := by
    rw [show ((311 / 250) : ℝ) = ((250 / 311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8188_neg : (139856951 / 500000000) ≤ -Real.log (189 / 250) ∧
    -Real.log (189 / 250) ≤ (279713903 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 439)) (n := 12)
    (lo := (139856951 / 500000000)) (hi := (279713903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 189) = 1/(189 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8188 : Bounds (-279713903 / 1000000000) (-139856951 / 500000000) (Real.log (189 / 250)) := by
  have h := reflection_log_8188_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8189_neg : (24397 / 100000000) ≤ -Real.log (250000 / 250061) ∧
    -Real.log (250000 / 250061) ≤ (243971 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 500061)) (n := 12)
    (lo := (24397 / 100000000)) (hi := (243971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250061 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250061 / 250000) = 1/(250000 / 250061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8189 : Bounds (24397 / 100000000) (243971 / 1000000000) (Real.log (250061 / 250000)) := by
  have h := reflection_log_8189_neg
  have he : Real.log (250061 / 250000) = -Real.log (250000 / 250061) := by
    rw [show ((250061 / 250000) : ℝ) = ((250000 / 250061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8190_neg : (244029 / 1000000000) ≤ -Real.log (249939 / 250000) ∧
    -Real.log (249939 / 250000) ≤ (24403 / 100000000) := by
  have h := checkLog_sound (w := (61 / 499939)) (n := 12)
    (lo := (244029 / 1000000000)) (hi := (24403 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249939) = 1/(249939 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8190 : Bounds (-24403 / 100000000) (-244029 / 1000000000) (Real.log (249939 / 250000)) := by
  have h := reflection_log_8190_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8191_neg : (115962713 / 1000000000) ≤ -Real.log (500000 / 561477) ∧
    -Real.log (500000 / 561477) ≤ (57981357 / 500000000) := by
  have h := checkLog_sound (w := (61477 / 1061477)) (n := 12)
    (lo := (115962713 / 1000000000)) (hi := (57981357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((561477 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(561477 / 500000) = 1/(500000 / 561477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8191 : Bounds (115962713 / 1000000000) (57981357 / 500000000) (Real.log (561477 / 500000)) := by
  have h := reflection_log_8191_neg
  have he : Real.log (561477 / 500000) = -Real.log (500000 / 561477) := by
    rw [show ((561477 / 500000) : ℝ) = ((500000 / 561477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0128 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8192_neg : (32798959 / 250000000) ≤ -Real.log (438523 / 500000) ∧
    -Real.log (438523 / 500000) ≤ (131195837 / 1000000000) := by
  have h := checkLog_sound (w := (61477 / 938523)) (n := 12)
    (lo := (32798959 / 250000000)) (hi := (131195837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 438523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 438523) = 1/(438523 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8192 : Bounds (-131195837 / 1000000000) (-32798959 / 250000000) (Real.log (438523 / 500000)) := by
  have h := reflection_log_8192_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8193_neg : (29101967 / 250000000) ≤ -Real.log (500000 / 561727) ∧
    -Real.log (500000 / 561727) ≤ (116407869 / 1000000000) := by
  have h := checkLog_sound (w := (61727 / 1061727)) (n := 12)
    (lo := (29101967 / 250000000)) (hi := (116407869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((561727 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(561727 / 500000) = 1/(500000 / 561727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8193 : Bounds (29101967 / 250000000) (116407869 / 1000000000) (Real.log (561727 / 500000)) := by
  have h := reflection_log_8193_neg
  have he : Real.log (561727 / 500000) = -Real.log (500000 / 561727) := by
    rw [show ((561727 / 500000) : ℝ) = ((500000 / 561727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8194_neg : (65883047 / 500000000) ≤ -Real.log (438273 / 500000) ∧
    -Real.log (438273 / 500000) ≤ (26353219 / 200000000) := by
  have h := checkLog_sound (w := (61727 / 938273)) (n := 12)
    (lo := (65883047 / 500000000)) (hi := (26353219 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 438273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 438273) = 1/(438273 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8194 : Bounds (-26353219 / 200000000) (-65883047 / 500000000) (Real.log (438273 / 500000)) := by
  have h := reflection_log_8194_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8195_neg : (7679113 / 500000000) ≤ -Real.log (246189777471 / 250000000000) ∧
    -Real.log (246189777471 / 250000000000) ≤ (15358227 / 1000000000) := by
  have h := checkLog_sound (w := (3810222529 / 496189777471)) (n := 12)
    (lo := (7679113 / 500000000)) (hi := (15358227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246189777471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246189777471) = 1/(246189777471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8195 : Bounds (-15358227 / 1000000000) (-7679113 / 500000000) (Real.log (246189777471 / 250000000000)) := by
  have h := reflection_log_8195_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8196_neg : (15233123 / 1000000000) ≤ -Real.log (246220578471 / 250000000000) ∧
    -Real.log (246220578471 / 250000000000) ≤ (3808281 / 250000000) := by
  have h := checkLog_sound (w := (3779421529 / 496220578471)) (n := 12)
    (lo := (15233123 / 1000000000)) (hi := (3808281 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246220578471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246220578471) = 1/(246220578471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8196 : Bounds (-3808281 / 250000000) (-15233123 / 1000000000) (Real.log (246220578471 / 250000000000)) := by
  have h := reflection_log_8196_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8197_neg : (247158549 / 1000000000) ≤ -Real.log (125000000000 / 160047762603) ∧
    -Real.log (125000000000 / 160047762603) ≤ (4943171 / 20000000) := by
  have h := checkLog_sound (w := (35047762603 / 285047762603)) (n := 12)
    (lo := (247158549 / 1000000000)) (hi := (4943171 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160047762603 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160047762603 / 125000000000) = 1/(125000000000 / 160047762603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8197 : Bounds (247158549 / 1000000000) (4943171 / 20000000) (Real.log (160047762603 / 125000000000)) := by
  have h := reflection_log_8197_neg
  have he : Real.log (160047762603 / 125000000000) = -Real.log (125000000000 / 160047762603) := by
    rw [show ((160047762603 / 125000000000) : ℝ) = ((125000000000 / 160047762603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8198_neg : (124086981 / 500000000) ≤ -Real.log (125000000000 / 160210359753) ∧
    -Real.log (125000000000 / 160210359753) ≤ (248173963 / 1000000000) := by
  have h := checkLog_sound (w := (35210359753 / 285210359753)) (n := 12)
    (lo := (124086981 / 500000000)) (hi := (248173963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160210359753 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160210359753 / 125000000000) = 1/(125000000000 / 160210359753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8198 : Bounds (124086981 / 500000000) (248173963 / 1000000000) (Real.log (160210359753 / 125000000000)) := by
  have h := reflection_log_8198_neg
  have he : Real.log (160210359753 / 125000000000) = -Real.log (125000000000 / 160210359753) := by
    rw [show ((160210359753 / 125000000000) : ℝ) = ((125000000000 / 160210359753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8199_neg : (49698273 / 100000000) ≤ -Real.log (62500000000 / 102734633179) ∧
    -Real.log (62500000000 / 102734633179) ≤ (496982731 / 1000000000) := by
  have h := checkLog_sound (w := (40234633179 / 165234633179)) (n := 12)
    (lo := (49698273 / 100000000)) (hi := (496982731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102734633179 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102734633179 / 62500000000) = 1/(62500000000 / 102734633179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8199 : Bounds (49698273 / 100000000) (496982731 / 1000000000) (Real.log (102734633179 / 62500000000)) := by
  have h := reflection_log_8199_neg
  have he : Real.log (102734633179 / 62500000000) = -Real.log (62500000000 / 102734633179) := by
    rw [show ((102734633179 / 62500000000) : ℝ) = ((62500000000 / 102734633179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8200_neg : (498045897 / 1000000000) ≤ -Real.log (3906250000 / 6427744709) ∧
    -Real.log (3906250000 / 6427744709) ≤ (249022949 / 500000000) := by
  have h := checkLog_sound (w := (2521494709 / 10333994709)) (n := 12)
    (lo := (498045897 / 1000000000)) (hi := (249022949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6427744709 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6427744709 / 3906250000) = 1/(3906250000 / 6427744709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8200 : Bounds (498045897 / 1000000000) (249022949 / 500000000) (Real.log (6427744709 / 3906250000)) := by
  have h := reflection_log_8200_neg
  have he : Real.log (6427744709 / 3906250000) = -Real.log (3906250000 / 6427744709) := by
    rw [show ((6427744709 / 3906250000) : ℝ) = ((3906250000 / 6427744709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8201_neg : (109366921 / 500000000) ≤ -Real.log (2000 / 2489) ∧
    -Real.log (2000 / 2489) ≤ (218733843 / 1000000000) := by
  have h := checkLog_sound (w := (489 / 4489)) (n := 12)
    (lo := (109366921 / 500000000)) (hi := (218733843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2489 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2489 / 2000) = 1/(2000 / 2489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8201 : Bounds (109366921 / 500000000) (218733843 / 1000000000) (Real.log (2489 / 2000)) := by
  have h := reflection_log_8201_neg
  have he : Real.log (2489 / 2000) = -Real.log (2000 / 2489) := by
    rw [show ((2489 / 2000) : ℝ) = ((2000 / 2489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8202_neg : (280375497 / 1000000000) ≤ -Real.log (1511 / 2000) ∧
    -Real.log (1511 / 2000) ≤ (140187749 / 500000000) := by
  have h := checkLog_sound (w := (489 / 3511)) (n := 12)
    (lo := (280375497 / 1000000000)) (hi := (140187749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1511) = 1/(1511 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8202 : Bounds (-140187749 / 500000000) (-280375497 / 1000000000) (Real.log (1511 / 2000)) := by
  have h := reflection_log_8202_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8203_neg : (24447 / 100000000) ≤ -Real.log (2000000 / 2000489) ∧
    -Real.log (2000000 / 2000489) ≤ (244471 / 1000000000) := by
  have h := checkLog_sound (w := (489 / 4000489)) (n := 12)
    (lo := (24447 / 100000000)) (hi := (244471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000489 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000489 / 2000000) = 1/(2000000 / 2000489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8203 : Bounds (24447 / 100000000) (244471 / 1000000000) (Real.log (2000489 / 2000000)) := by
  have h := reflection_log_8203_neg
  have he : Real.log (2000489 / 2000000) = -Real.log (2000000 / 2000489) := by
    rw [show ((2000489 / 2000000) : ℝ) = ((2000000 / 2000489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8204_neg : (244529 / 1000000000) ≤ -Real.log (1999511 / 2000000) ∧
    -Real.log (1999511 / 2000000) ≤ (24453 / 100000000) := by
  have h := checkLog_sound (w := (489 / 3999511)) (n := 12)
    (lo := (244529 / 1000000000)) (hi := (24453 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999511) = 1/(1999511 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8204 : Bounds (-24453 / 100000000) (-244529 / 1000000000) (Real.log (1999511 / 2000000)) := by
  have h := reflection_log_8204_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8205_neg : (116192437 / 1000000000) ≤ -Real.log (250000 / 280803) ∧
    -Real.log (250000 / 280803) ≤ (58096219 / 500000000) := by
  have h := checkLog_sound (w := (30803 / 530803)) (n := 12)
    (lo := (116192437 / 1000000000)) (hi := (58096219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((280803 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(280803 / 250000) = 1/(250000 / 280803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8205 : Bounds (116192437 / 1000000000) (58096219 / 500000000) (Real.log (280803 / 250000)) := by
  have h := reflection_log_8205_neg
  have he : Real.log (280803 / 250000) = -Real.log (250000 / 280803) := by
    rw [show ((280803 / 250000) : ℝ) = ((250000 / 280803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8206_neg : (131490049 / 1000000000) ≤ -Real.log (219197 / 250000) ∧
    -Real.log (219197 / 250000) ≤ (2629801 / 20000000) := by
  have h := checkLog_sound (w := (30803 / 469197)) (n := 12)
    (lo := (131490049 / 1000000000)) (hi := (2629801 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 219197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 219197) = 1/(219197 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8206 : Bounds (-2629801 / 20000000) (-131490049 / 1000000000) (Real.log (219197 / 250000)) := by
  have h := reflection_log_8206_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8207_neg : (5831919 / 50000000) ≤ -Real.log (1000000 / 1123713) ∧
    -Real.log (1000000 / 1123713) ≤ (116638381 / 1000000000) := by
  have h := checkLog_sound (w := (123713 / 2123713)) (n := 12)
    (lo := (5831919 / 50000000)) (hi := (116638381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1123713 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1123713 / 1000000) = 1/(1000000 / 1123713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8207 : Bounds (5831919 / 50000000) (116638381 / 1000000000) (Real.log (1123713 / 1000000)) := by
  have h := reflection_log_8207_neg
  have he : Real.log (1123713 / 1000000) = -Real.log (1000000 / 1123713) := by
    rw [show ((1123713 / 1000000) : ℝ) = ((1000000 / 1123713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8208_neg : (8253851 / 62500000) ≤ -Real.log (876287 / 1000000) ∧
    -Real.log (876287 / 1000000) ≤ (132061617 / 1000000000) := by
  have h := checkLog_sound (w := (123713 / 1876287)) (n := 12)
    (lo := (8253851 / 62500000)) (hi := (132061617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 876287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 876287) = 1/(876287 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8208 : Bounds (-132061617 / 1000000000) (-8253851 / 62500000) (Real.log (876287 / 1000000)) := by
  have h := reflection_log_8208_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8209_neg : (3084647 / 200000000) ≤ -Real.log (984695093631 / 1000000000000) ∧
    -Real.log (984695093631 / 1000000000000) ≤ (3855809 / 250000000) := by
  have h := checkLog_sound (w := (15304906369 / 1984695093631)) (n := 12)
    (lo := (3084647 / 200000000)) (hi := (3855809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984695093631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984695093631) = 1/(984695093631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8209 : Bounds (-3855809 / 250000000) (-3084647 / 200000000) (Real.log (984695093631 / 1000000000000)) := by
  have h := reflection_log_8209_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8210_neg : (15297611 / 1000000000) ≤ -Real.log (61551175191 / 62500000000) ∧
    -Real.log (61551175191 / 62500000000) ≤ (3824403 / 250000000) := by
  have h := checkLog_sound (w := (948824809 / 124051175191)) (n := 12)
    (lo := (15297611 / 1000000000)) (hi := (3824403 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61551175191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61551175191) = 1/(61551175191 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8210 : Bounds (-3824403 / 250000000) (-15297611 / 1000000000) (Real.log (61551175191 / 62500000000)) := by
  have h := reflection_log_8210_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8211_neg : (247682487 / 1000000000) ≤ -Real.log (500000000000 / 640526558301) ∧
    -Real.log (500000000000 / 640526558301) ≤ (30960311 / 125000000) := by
  have h := checkLog_sound (w := (140526558301 / 1140526558301)) (n := 12)
    (lo := (247682487 / 1000000000)) (hi := (30960311 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640526558301 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640526558301 / 500000000000) = 1/(500000000000 / 640526558301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8211 : Bounds (247682487 / 1000000000) (30960311 / 125000000) (Real.log (640526558301 / 500000000000)) := by
  have h := reflection_log_8211_neg
  have he : Real.log (640526558301 / 500000000000) = -Real.log (500000000000 / 640526558301) := by
    rw [show ((640526558301 / 500000000000) : ℝ) = ((500000000000 / 640526558301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8212_neg : (62174999 / 250000000) ≤ -Real.log (100000000000 / 128235726423) ∧
    -Real.log (100000000000 / 128235726423) ≤ (248699997 / 1000000000) := by
  have h := checkLog_sound (w := (28235726423 / 228235726423)) (n := 12)
    (lo := (62174999 / 250000000)) (hi := (248699997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128235726423 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128235726423 / 100000000000) = 1/(100000000000 / 128235726423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8212 : Bounds (62174999 / 250000000) (248699997 / 1000000000) (Real.log (128235726423 / 100000000000)) := by
  have h := reflection_log_8212_neg
  have he : Real.log (128235726423 / 100000000000) = -Real.log (100000000000 / 128235726423) := by
    rw [show ((128235726423 / 100000000000) : ℝ) = ((100000000000 / 128235726423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8213_neg : (498045897 / 1000000000) ≤ -Real.log (500000000000 / 822751322751) ∧
    -Real.log (500000000000 / 822751322751) ≤ (249022949 / 500000000) := by
  have h := checkLog_sound (w := (322751322751 / 1322751322751)) (n := 12)
    (lo := (498045897 / 1000000000)) (hi := (249022949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((822751322751 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(822751322751 / 500000000000) = 1/(500000000000 / 822751322751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8213 : Bounds (498045897 / 1000000000) (249022949 / 500000000) (Real.log (822751322751 / 500000000000)) := by
  have h := reflection_log_8213_neg
  have he : Real.log (822751322751 / 500000000000) = -Real.log (500000000000 / 822751322751) := by
    rw [show ((822751322751 / 500000000000) : ℝ) = ((500000000000 / 822751322751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8214_neg : (24955467 / 50000000) ≤ -Real.log (500000000000 / 823626737261) ∧
    -Real.log (500000000000 / 823626737261) ≤ (499109341 / 1000000000) := by
  have h := checkLog_sound (w := (323626737261 / 1323626737261)) (n := 12)
    (lo := (24955467 / 50000000)) (hi := (499109341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((823626737261 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(823626737261 / 500000000000) = 1/(500000000000 / 823626737261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8214 : Bounds (24955467 / 50000000) (499109341 / 1000000000) (Real.log (823626737261 / 500000000000)) := by
  have h := reflection_log_8214_neg
  have he : Real.log (823626737261 / 500000000000) = -Real.log (500000000000 / 823626737261) := by
    rw [show ((823626737261 / 500000000000) : ℝ) = ((500000000000 / 823626737261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8215_neg : (219135529 / 1000000000) ≤ -Real.log (200 / 249) ∧
    -Real.log (200 / 249) ≤ (21913553 / 100000000) := by
  have h := checkLog_sound (w := (49 / 449)) (n := 12)
    (lo := (219135529 / 1000000000)) (hi := (21913553 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(249 / 200) = 1/(200 / 249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8215 : Bounds (219135529 / 1000000000) (21913553 / 100000000) (Real.log (249 / 200)) := by
  have h := reflection_log_8215_neg
  have he : Real.log (249 / 200) = -Real.log (200 / 249) := by
    rw [show ((249 / 200) : ℝ) = ((200 / 249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8216_neg : (281037529 / 1000000000) ≤ -Real.log (151 / 200) ∧
    -Real.log (151 / 200) ≤ (28103753 / 100000000) := by
  have h := checkLog_sound (w := (49 / 351)) (n := 12)
    (lo := (281037529 / 1000000000)) (hi := (28103753 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 151) = 1/(151 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8216 : Bounds (-28103753 / 100000000) (-281037529 / 1000000000) (Real.log (151 / 200)) := by
  have h := reflection_log_8216_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8217_neg : (244969 / 1000000000) ≤ -Real.log (200000 / 200049) ∧
    -Real.log (200000 / 200049) ≤ (24497 / 100000000) := by
  have h := checkLog_sound (w := (49 / 400049)) (n := 12)
    (lo := (244969 / 1000000000)) (hi := (24497 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200049 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200049 / 200000) = 1/(200000 / 200049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8217 : Bounds (244969 / 1000000000) (24497 / 100000000) (Real.log (200049 / 200000)) := by
  have h := reflection_log_8217_neg
  have he : Real.log (200049 / 200000) = -Real.log (200000 / 200049) := by
    rw [show ((200049 / 200000) : ℝ) = ((200000 / 200049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8218_neg : (24503 / 100000000) ≤ -Real.log (199951 / 200000) ∧
    -Real.log (199951 / 200000) ≤ (245031 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 399951)) (n := 12)
    (lo := (24503 / 100000000)) (hi := (245031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199951) = 1/(199951 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8218 : Bounds (-245031 / 1000000000) (-24503 / 100000000) (Real.log (199951 / 200000)) := by
  have h := reflection_log_8218_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8219_neg : (11642211 / 100000000) ≤ -Real.log (100000 / 112347) ∧
    -Real.log (100000 / 112347) ≤ (116422111 / 1000000000) := by
  have h := checkLog_sound (w := (12347 / 212347)) (n := 12)
    (lo := (11642211 / 100000000)) (hi := (116422111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((112347 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(112347 / 100000) = 1/(100000 / 112347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8219 : Bounds (11642211 / 100000000) (116422111 / 1000000000) (Real.log (112347 / 100000)) := by
  have h := reflection_log_8219_neg
  have he : Real.log (112347 / 100000) = -Real.log (100000 / 112347) := by
    rw [show ((112347 / 100000) : ℝ) = ((100000 / 112347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8220_neg : (32946087 / 250000000) ≤ -Real.log (87653 / 100000) ∧
    -Real.log (87653 / 100000) ≤ (131784349 / 1000000000) := by
  have h := checkLog_sound (w := (12347 / 187653)) (n := 12)
    (lo := (32946087 / 250000000)) (hi := (131784349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 87653) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 87653) = 1/(87653 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8220 : Bounds (-131784349 / 1000000000) (-32946087 / 250000000) (Real.log (87653 / 100000)) := by
  have h := reflection_log_8220_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8221_neg : (2337359 / 20000000) ≤ -Real.log (1000000 / 1123971) ∧
    -Real.log (1000000 / 1123971) ≤ (116867951 / 1000000000) := by
  have h := checkLog_sound (w := (123971 / 2123971)) (n := 12)
    (lo := (2337359 / 20000000)) (hi := (116867951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1123971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1123971 / 1000000) = 1/(1000000 / 1123971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8221 : Bounds (2337359 / 20000000) (116867951 / 1000000000) (Real.log (1123971 / 1000000)) := by
  have h := reflection_log_8221_neg
  have he : Real.log (1123971 / 1000000) = -Real.log (1000000 / 1123971) := by
    rw [show ((1123971 / 1000000) : ℝ) = ((1000000 / 1123971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8222_neg : (132356083 / 1000000000) ≤ -Real.log (876029 / 1000000) ∧
    -Real.log (876029 / 1000000) ≤ (33089021 / 250000000) := by
  have h := checkLog_sound (w := (123971 / 1876029)) (n := 12)
    (lo := (132356083 / 1000000000)) (hi := (33089021 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 876029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 876029) = 1/(876029 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8222 : Bounds (-33089021 / 250000000) (-132356083 / 1000000000) (Real.log (876029 / 1000000)) := by
  have h := reflection_log_8222_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8223_neg : (15488133 / 1000000000) ≤ -Real.log (984631191159 / 1000000000000) ∧
    -Real.log (984631191159 / 1000000000000) ≤ (7744067 / 500000000) := by
  have h := checkLog_sound (w := (15368808841 / 1984631191159)) (n := 12)
    (lo := (15488133 / 1000000000)) (hi := (7744067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984631191159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984631191159) = 1/(984631191159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8223 : Bounds (-7744067 / 500000000) (-15488133 / 1000000000) (Real.log (984631191159 / 1000000000000)) := by
  have h := reflection_log_8223_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8224_neg : (7681119 / 500000000) ≤ -Real.log (9847551591 / 10000000000) ∧
    -Real.log (9847551591 / 10000000000) ≤ (15362239 / 1000000000) := by
  have h := checkLog_sound (w := (152448409 / 19847551591)) (n := 12)
    (lo := (7681119 / 500000000)) (hi := (15362239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9847551591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9847551591) = 1/(9847551591 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8224 : Bounds (-15362239 / 1000000000) (-7681119 / 500000000) (Real.log (9847551591 / 10000000000)) := by
  have h := reflection_log_8224_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8225_neg : (124103229 / 500000000) ≤ -Real.log (250000000000 / 320431131849) ∧
    -Real.log (250000000000 / 320431131849) ≤ (248206459 / 1000000000) := by
  have h := checkLog_sound (w := (70431131849 / 570431131849)) (n := 12)
    (lo := (124103229 / 500000000)) (hi := (248206459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320431131849 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320431131849 / 250000000000) = 1/(250000000000 / 320431131849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8225 : Bounds (124103229 / 500000000) (248206459 / 1000000000) (Real.log (320431131849 / 250000000000)) := by
  have h := reflection_log_8225_neg
  have he : Real.log (320431131849 / 250000000000) = -Real.log (250000000000 / 320431131849) := by
    rw [show ((320431131849 / 250000000000) : ℝ) = ((250000000000 / 320431131849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8226_neg : (249224033 / 1000000000) ≤ -Real.log (100000000000 / 128302944309) ∧
    -Real.log (100000000000 / 128302944309) ≤ (124612017 / 500000000) := by
  have h := checkLog_sound (w := (28302944309 / 228302944309)) (n := 12)
    (lo := (249224033 / 1000000000)) (hi := (124612017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128302944309 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128302944309 / 100000000000) = 1/(100000000000 / 128302944309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8226 : Bounds (249224033 / 1000000000) (124612017 / 500000000) (Real.log (128302944309 / 100000000000)) := by
  have h := reflection_log_8226_neg
  have he : Real.log (128302944309 / 100000000000) = -Real.log (100000000000 / 128302944309) := by
    rw [show ((128302944309 / 100000000000) : ℝ) = ((100000000000 / 128302944309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8227_neg : (24955467 / 50000000) ≤ -Real.log (25000000000 / 41181336863) ∧
    -Real.log (25000000000 / 41181336863) ≤ (499109341 / 1000000000) := by
  have h := checkLog_sound (w := (16181336863 / 66181336863)) (n := 12)
    (lo := (24955467 / 50000000)) (hi := (499109341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41181336863 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41181336863 / 25000000000) = 1/(25000000000 / 41181336863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8227 : Bounds (24955467 / 50000000) (499109341 / 1000000000) (Real.log (41181336863 / 25000000000)) := by
  have h := reflection_log_8227_neg
  have he : Real.log (41181336863 / 25000000000) = -Real.log (25000000000 / 41181336863) := by
    rw [show ((41181336863 / 25000000000) : ℝ) = ((25000000000 / 41181336863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8228_neg : (500173059 / 1000000000) ≤ -Real.log (500000000000 / 824503311259) ∧
    -Real.log (500000000000 / 824503311259) ≤ (25008653 / 50000000) := by
  have h := checkLog_sound (w := (324503311259 / 1324503311259)) (n := 12)
    (lo := (500173059 / 1000000000)) (hi := (25008653 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((824503311259 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(824503311259 / 500000000000) = 1/(500000000000 / 824503311259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8228 : Bounds (500173059 / 1000000000) (25008653 / 50000000) (Real.log (824503311259 / 500000000000)) := by
  have h := reflection_log_8228_neg
  have he : Real.log (824503311259 / 500000000000) = -Real.log (500000000000 / 824503311259) := by
    rw [show ((824503311259 / 500000000000) : ℝ) = ((500000000000 / 824503311259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8229_neg : (43907411 / 200000000) ≤ -Real.log (2000 / 2491) ∧
    -Real.log (2000 / 2491) ≤ (6860533 / 31250000) := by
  have h := checkLog_sound (w := (491 / 4491)) (n := 12)
    (lo := (43907411 / 200000000)) (hi := (6860533 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2491 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2491 / 2000) = 1/(2000 / 2491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8229 : Bounds (43907411 / 200000000) (6860533 / 31250000) (Real.log (2491 / 2000)) := by
  have h := reflection_log_8229_neg
  have he : Real.log (2491 / 2000) = -Real.log (2000 / 2491) := by
    rw [show ((2491 / 2000) : ℝ) = ((2000 / 2491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8230_neg : (2817 / 10000) ≤ -Real.log (1509 / 2000) ∧
    -Real.log (1509 / 2000) ≤ (281700001 / 1000000000) := by
  have h := checkLog_sound (w := (491 / 3509)) (n := 12)
    (lo := (2817 / 10000)) (hi := (281700001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1509) = 1/(1509 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8230 : Bounds (-281700001 / 1000000000) (-2817 / 10000) (Real.log (1509 / 2000)) := by
  have h := reflection_log_8230_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8231_neg : (245469 / 1000000000) ≤ -Real.log (2000000 / 2000491) ∧
    -Real.log (2000000 / 2000491) ≤ (24547 / 100000000) := by
  have h := checkLog_sound (w := (491 / 4000491)) (n := 12)
    (lo := (245469 / 1000000000)) (hi := (24547 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000491 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000491 / 2000000) = 1/(2000000 / 2000491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8231 : Bounds (245469 / 1000000000) (24547 / 100000000) (Real.log (2000491 / 2000000)) := by
  have h := reflection_log_8231_neg
  have he : Real.log (2000491 / 2000000) = -Real.log (2000000 / 2000491) := by
    rw [show ((2000491 / 2000000) : ℝ) = ((2000000 / 2000491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8232_neg : (24553 / 100000000) ≤ -Real.log (1999509 / 2000000) ∧
    -Real.log (1999509 / 2000000) ≤ (245531 / 1000000000) := by
  have h := checkLog_sound (w := (491 / 3999509)) (n := 12)
    (lo := (24553 / 100000000)) (hi := (245531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999509) = 1/(1999509 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8232 : Bounds (-245531 / 1000000000) (-24553 / 100000000) (Real.log (1999509 / 2000000)) := by
  have h := reflection_log_8232_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8233_neg : (116651729 / 1000000000) ≤ -Real.log (62500 / 70233) ∧
    -Real.log (62500 / 70233) ≤ (11665173 / 100000000) := by
  have h := checkLog_sound (w := (7733 / 132733)) (n := 12)
    (lo := (116651729 / 1000000000)) (hi := (11665173 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70233 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(70233 / 62500) = 1/(62500 / 70233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8233 : Bounds (116651729 / 1000000000) (11665173 / 100000000) (Real.log (70233 / 62500)) := by
  have h := reflection_log_8233_neg
  have he : Real.log (70233 / 62500) = -Real.log (62500 / 70233) := by
    rw [show ((70233 / 62500) : ℝ) = ((62500 / 70233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8234_neg : (132078733 / 1000000000) ≤ -Real.log (54767 / 62500) ∧
    -Real.log (54767 / 62500) ≤ (66039367 / 500000000) := by
  have h := checkLog_sound (w := (7733 / 117267)) (n := 12)
    (lo := (132078733 / 1000000000)) (hi := (66039367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 54767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 54767) = 1/(54767 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8234 : Bounds (-66039367 / 500000000) (-132078733 / 1000000000) (Real.log (54767 / 62500)) := by
  have h := reflection_log_8234_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8235_neg : (29274589 / 250000000) ≤ -Real.log (100000 / 112423) ∧
    -Real.log (100000 / 112423) ≤ (117098357 / 1000000000) := by
  have h := checkLog_sound (w := (12423 / 212423)) (n := 12)
    (lo := (29274589 / 250000000)) (hi := (117098357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((112423 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(112423 / 100000) = 1/(100000 / 112423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8235 : Bounds (29274589 / 250000000) (117098357 / 1000000000) (Real.log (112423 / 100000)) := by
  have h := reflection_log_8235_neg
  have he : Real.log (112423 / 100000) = -Real.log (100000 / 112423) := by
    rw [show ((112423 / 100000) : ℝ) = ((100000 / 112423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8236_neg : (132651779 / 1000000000) ≤ -Real.log (87577 / 100000) ∧
    -Real.log (87577 / 100000) ≤ (6632589 / 50000000) := by
  have h := checkLog_sound (w := (12423 / 187577)) (n := 12)
    (lo := (132651779 / 1000000000)) (hi := (6632589 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 87577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 87577) = 1/(87577 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8236 : Bounds (-6632589 / 50000000) (-132651779 / 1000000000) (Real.log (87577 / 100000)) := by
  have h := reflection_log_8236_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8237_neg : (7776711 / 500000000) ≤ -Real.log (9845669071 / 10000000000) ∧
    -Real.log (9845669071 / 10000000000) ≤ (15553423 / 1000000000) := by
  have h := checkLog_sound (w := (154330929 / 19845669071)) (n := 12)
    (lo := (7776711 / 500000000)) (hi := (15553423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9845669071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9845669071) = 1/(9845669071 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8237 : Bounds (-15553423 / 1000000000) (-7776711 / 500000000) (Real.log (9845669071 / 10000000000)) := by
  have h := reflection_log_8237_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8238_neg : (3856751 / 250000000) ≤ -Real.log (3846450711 / 3906250000) ∧
    -Real.log (3846450711 / 3906250000) ≤ (3085401 / 200000000) := by
  have h := checkLog_sound (w := (59799289 / 7752700711)) (n := 12)
    (lo := (3856751 / 250000000)) (hi := (3085401 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3846450711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3846450711) = 1/(3846450711 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8238 : Bounds (-3085401 / 200000000) (-3856751 / 250000000) (Real.log (3846450711 / 3906250000)) := by
  have h := reflection_log_8238_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8239_neg : (248730463 / 1000000000) ≤ -Real.log (500000000000 / 641198166779) ∧
    -Real.log (500000000000 / 641198166779) ≤ (7772827 / 31250000) := by
  have h := checkLog_sound (w := (141198166779 / 1141198166779)) (n := 12)
    (lo := (248730463 / 1000000000)) (hi := (7772827 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((641198166779 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(641198166779 / 500000000000) = 1/(500000000000 / 641198166779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8239 : Bounds (248730463 / 1000000000) (7772827 / 31250000) (Real.log (641198166779 / 500000000000)) := by
  have h := reflection_log_8239_neg
  have he : Real.log (641198166779 / 500000000000) = -Real.log (500000000000 / 641198166779) := by
    rw [show ((641198166779 / 500000000000) : ℝ) = ((500000000000 / 641198166779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8240_neg : (31218767 / 125000000) ≤ -Real.log (250000000000 / 320926156411) ∧
    -Real.log (250000000000 / 320926156411) ≤ (249750137 / 1000000000) := by
  have h := checkLog_sound (w := (70926156411 / 570926156411)) (n := 12)
    (lo := (31218767 / 125000000)) (hi := (249750137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320926156411 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320926156411 / 250000000000) = 1/(250000000000 / 320926156411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8240 : Bounds (31218767 / 125000000) (249750137 / 1000000000) (Real.log (320926156411 / 250000000000)) := by
  have h := reflection_log_8240_neg
  have he : Real.log (320926156411 / 250000000000) = -Real.log (250000000000 / 320926156411) := by
    rw [show ((320926156411 / 250000000000) : ℝ) = ((250000000000 / 320926156411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8241_neg : (500173059 / 1000000000) ≤ -Real.log (250000000000 / 412251655629) ∧
    -Real.log (250000000000 / 412251655629) ≤ (25008653 / 50000000) := by
  have h := checkLog_sound (w := (162251655629 / 662251655629)) (n := 12)
    (lo := (500173059 / 1000000000)) (hi := (25008653 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((412251655629 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(412251655629 / 250000000000) = 1/(250000000000 / 412251655629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8241 : Bounds (500173059 / 1000000000) (25008653 / 50000000) (Real.log (412251655629 / 250000000000)) := by
  have h := reflection_log_8241_neg
  have he : Real.log (412251655629 / 250000000000) = -Real.log (250000000000 / 412251655629) := by
    rw [show ((412251655629 / 250000000000) : ℝ) = ((250000000000 / 412251655629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8242_neg : (7831829 / 15625000) ≤ -Real.log (125000000000 / 206345261763) ∧
    -Real.log (125000000000 / 206345261763) ≤ (501237057 / 1000000000) := by
  have h := checkLog_sound (w := (81345261763 / 331345261763)) (n := 12)
    (lo := (7831829 / 15625000)) (hi := (501237057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((206345261763 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(206345261763 / 125000000000) = 1/(125000000000 / 206345261763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8242 : Bounds (7831829 / 15625000) (501237057 / 1000000000) (Real.log (206345261763 / 125000000000)) := by
  have h := reflection_log_8242_neg
  have he : Real.log (206345261763 / 125000000000) = -Real.log (125000000000 / 206345261763) := by
    rw [show ((206345261763 / 125000000000) : ℝ) = ((125000000000 / 206345261763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8243_neg : (10996921 / 50000000) ≤ -Real.log (500 / 623) ∧
    -Real.log (500 / 623) ≤ (219938421 / 1000000000) := by
  have h := checkLog_sound (w := (123 / 1123)) (n := 12)
    (lo := (10996921 / 50000000)) (hi := (219938421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((623 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(623 / 500) = 1/(500 / 623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8243 : Bounds (10996921 / 50000000) (219938421 / 1000000000) (Real.log (623 / 500)) := by
  have h := reflection_log_8243_neg
  have he : Real.log (623 / 500) = -Real.log (500 / 623) := by
    rw [show ((623 / 500) : ℝ) = ((500 / 623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8244_neg : (28236291 / 100000000) ≤ -Real.log (377 / 500) ∧
    -Real.log (377 / 500) ≤ (282362911 / 1000000000) := by
  have h := checkLog_sound (w := (123 / 877)) (n := 12)
    (lo := (28236291 / 100000000)) (hi := (282362911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 377) = 1/(377 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8244 : Bounds (-282362911 / 1000000000) (-28236291 / 100000000) (Real.log (377 / 500)) := by
  have h := reflection_log_8244_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8245_neg : (245969 / 1000000000) ≤ -Real.log (500000 / 500123) ∧
    -Real.log (500000 / 500123) ≤ (24597 / 100000000) := by
  have h := checkLog_sound (w := (123 / 1000123)) (n := 12)
    (lo := (245969 / 1000000000)) (hi := (24597 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500123 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500123 / 500000) = 1/(500000 / 500123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8245 : Bounds (245969 / 1000000000) (24597 / 100000000) (Real.log (500123 / 500000)) := by
  have h := reflection_log_8245_neg
  have he : Real.log (500123 / 500000) = -Real.log (500000 / 500123) := by
    rw [show ((500123 / 500000) : ℝ) = ((500000 / 500123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8246_neg : (24603 / 100000000) ≤ -Real.log (499877 / 500000) ∧
    -Real.log (499877 / 500000) ≤ (246031 / 1000000000) := by
  have h := checkLog_sound (w := (123 / 999877)) (n := 12)
    (lo := (24603 / 100000000)) (hi := (246031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499877) = 1/(499877 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8246 : Bounds (-246031 / 1000000000) (-24603 / 100000000) (Real.log (499877 / 500000)) := by
  have h := reflection_log_8246_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8247_neg : (23376259 / 200000000) ≤ -Real.log (500000 / 561993) ∧
    -Real.log (500000 / 561993) ≤ (7305081 / 62500000) := by
  have h := checkLog_sound (w := (61993 / 1061993)) (n := 12)
    (lo := (23376259 / 200000000)) (hi := (7305081 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((561993 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(561993 / 500000) = 1/(500000 / 561993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8247 : Bounds (23376259 / 200000000) (7305081 / 62500000) (Real.log (561993 / 500000)) := by
  have h := reflection_log_8247_neg
  have he : Real.log (561993 / 500000) = -Real.log (500000 / 561993) := by
    rw [show ((561993 / 500000) : ℝ) = ((500000 / 561993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8248_neg : (66186603 / 500000000) ≤ -Real.log (438007 / 500000) ∧
    -Real.log (438007 / 500000) ≤ (132373207 / 1000000000) := by
  have h := checkLog_sound (w := (61993 / 938007)) (n := 12)
    (lo := (66186603 / 500000000)) (hi := (132373207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 438007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 438007) = 1/(438007 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8248 : Bounds (-132373207 / 1000000000) (-66186603 / 500000000) (Real.log (438007 / 500000)) := by
  have h := reflection_log_8248_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8249_neg : (11732871 / 100000000) ≤ -Real.log (1000000 / 1124489) ∧
    -Real.log (1000000 / 1124489) ≤ (117328711 / 1000000000) := by
  have h := checkLog_sound (w := (124489 / 2124489)) (n := 12)
    (lo := (11732871 / 100000000)) (hi := (117328711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1124489 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1124489 / 1000000) = 1/(1000000 / 1124489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8249 : Bounds (11732871 / 100000000) (117328711 / 1000000000) (Real.log (1124489 / 1000000)) := by
  have h := reflection_log_8249_neg
  have he : Real.log (1124489 / 1000000) = -Real.log (1000000 / 1124489) := by
    rw [show ((1124489 / 1000000) : ℝ) = ((1000000 / 1124489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8250_neg : (132947563 / 1000000000) ≤ -Real.log (875511 / 1000000) ∧
    -Real.log (875511 / 1000000) ≤ (33236891 / 250000000) := by
  have h := checkLog_sound (w := (124489 / 1875511)) (n := 12)
    (lo := (132947563 / 1000000000)) (hi := (33236891 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 875511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 875511) = 1/(875511 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8250 : Bounds (-33236891 / 250000000) (-132947563 / 1000000000) (Real.log (875511 / 1000000)) := by
  have h := reflection_log_8250_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8251_neg : (3904713 / 250000000) ≤ -Real.log (984502488879 / 1000000000000) ∧
    -Real.log (984502488879 / 1000000000000) ≤ (15618853 / 1000000000) := by
  have h := checkLog_sound (w := (15497511121 / 1984502488879)) (n := 12)
    (lo := (3904713 / 250000000)) (hi := (15618853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984502488879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984502488879) = 1/(984502488879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8251 : Bounds (-15618853 / 1000000000) (-3904713 / 250000000) (Real.log (984502488879 / 1000000000000)) := by
  have h := reflection_log_8251_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8252_neg : (1549191 / 100000000) ≤ -Real.log (246156867951 / 250000000000) ∧
    -Real.log (246156867951 / 250000000000) ≤ (15491911 / 1000000000) := by
  have h := checkLog_sound (w := (3843132049 / 496156867951)) (n := 12)
    (lo := (1549191 / 100000000)) (hi := (15491911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246156867951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246156867951) = 1/(246156867951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8252 : Bounds (-15491911 / 1000000000) (-1549191 / 100000000) (Real.log (246156867951 / 250000000000)) := by
  have h := reflection_log_8252_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8253_neg : (124627251 / 500000000) ≤ -Real.log (500000000000 / 641534267717) ∧
    -Real.log (500000000000 / 641534267717) ≤ (249254503 / 1000000000) := by
  have h := checkLog_sound (w := (141534267717 / 1141534267717)) (n := 12)
    (lo := (124627251 / 500000000)) (hi := (249254503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((641534267717 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(641534267717 / 500000000000) = 1/(500000000000 / 641534267717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8253 : Bounds (124627251 / 500000000) (249254503 / 1000000000) (Real.log (641534267717 / 500000000000)) := by
  have h := reflection_log_8253_neg
  have he : Real.log (641534267717 / 500000000000) = -Real.log (500000000000 / 641534267717) := by
    rw [show ((641534267717 / 500000000000) : ℝ) = ((500000000000 / 641534267717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8254_neg : (250276273 / 1000000000) ≤ -Real.log (500000000000 / 642190103837) ∧
    -Real.log (500000000000 / 642190103837) ≤ (125138137 / 500000000) := by
  have h := checkLog_sound (w := (142190103837 / 1142190103837)) (n := 12)
    (lo := (250276273 / 1000000000)) (hi := (125138137 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((642190103837 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(642190103837 / 500000000000) = 1/(500000000000 / 642190103837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8254 : Bounds (250276273 / 1000000000) (125138137 / 500000000) (Real.log (642190103837 / 500000000000)) := by
  have h := reflection_log_8254_neg
  have he : Real.log (642190103837 / 500000000000) = -Real.log (500000000000 / 642190103837) := by
    rw [show ((642190103837 / 500000000000) : ℝ) = ((500000000000 / 642190103837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8255_neg : (7831829 / 15625000) ≤ -Real.log (500000000000 / 825381047051) ∧
    -Real.log (500000000000 / 825381047051) ≤ (501237057 / 1000000000) := by
  have h := checkLog_sound (w := (325381047051 / 1325381047051)) (n := 12)
    (lo := (7831829 / 15625000)) (hi := (501237057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((825381047051 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(825381047051 / 500000000000) = 1/(500000000000 / 825381047051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8255 : Bounds (7831829 / 15625000) (501237057 / 1000000000) (Real.log (825381047051 / 500000000000)) := by
  have h := reflection_log_8255_neg
  have he : Real.log (825381047051 / 500000000000) = -Real.log (500000000000 / 825381047051) := by
    rw [show ((825381047051 / 500000000000) : ℝ) = ((500000000000 / 825381047051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


