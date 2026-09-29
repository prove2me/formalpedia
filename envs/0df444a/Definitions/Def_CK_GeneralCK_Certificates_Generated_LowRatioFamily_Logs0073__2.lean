-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0073__2
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0073__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T07:50:56.08355+00:00
-- url     : https://prove2.me/theorems/17cb580c-bb9e-4036-a1d3-1504bdf4a67e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0073 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0074)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0073 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0074)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0073 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0074)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0073 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0074) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0073 (+1 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0074).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0073 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4672_neg : (92801129 / 250000000) ≤ -Real.log (125000000000 / 181184935701) ∧
    -Real.log (125000000000 / 181184935701) ≤ (371204517 / 1000000000) := by
  have h := checkLog_sound (w := (56184935701 / 306184935701)) (n := 12)
    (lo := (92801129 / 250000000)) (hi := (371204517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181184935701 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181184935701 / 125000000000) = 1/(125000000000 / 181184935701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4672 : Bounds (92801129 / 250000000) (371204517 / 1000000000) (Real.log (181184935701 / 125000000000)) := by
  have h := reflection_log_4672_neg
  have he : Real.log (181184935701 / 125000000000) = -Real.log (125000000000 / 181184935701) := by
    rw [show ((181184935701 / 125000000000) : ℝ) = ((125000000000 / 181184935701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4673_neg : (371411489 / 1000000000) ≤ -Real.log (250000000000 / 362444879961) ∧
    -Real.log (250000000000 / 362444879961) ≤ (37141149 / 100000000) := by
  have h := checkLog_sound (w := (112444879961 / 612444879961)) (n := 12)
    (lo := (371411489 / 1000000000)) (hi := (37141149 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((362444879961 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(362444879961 / 250000000000) = 1/(250000000000 / 362444879961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4673 : Bounds (371411489 / 1000000000) (37141149 / 100000000) (Real.log (362444879961 / 250000000000)) := by
  have h := reflection_log_4673_neg
  have he : Real.log (362444879961 / 250000000000) = -Real.log (250000000000 / 362444879961) := by
    rw [show ((362444879961 / 250000000000) : ℝ) = ((250000000000 / 362444879961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4674_neg : (1349161 / 8000000) ≤ -Real.log (10000 / 11837) ∧
    -Real.log (10000 / 11837) ≤ (84322563 / 500000000) := by
  have h := checkLog_sound (w := (1837 / 21837)) (n := 12)
    (lo := (1349161 / 8000000)) (hi := (84322563 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11837 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11837 / 10000) = 1/(10000 / 11837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4674 : Bounds (1349161 / 8000000) (84322563 / 500000000) (Real.log (11837 / 10000)) := by
  have h := reflection_log_4674_neg
  have he : Real.log (11837 / 10000) = -Real.log (10000 / 11837) := by
    rw [show ((11837 / 10000) : ℝ) = ((10000 / 11837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4675_neg : (6342917 / 31250000) ≤ -Real.log (8163 / 10000) ∧
    -Real.log (8163 / 10000) ≤ (40594669 / 200000000) := by
  have h := checkLog_sound (w := (1837 / 18163)) (n := 12)
    (lo := (6342917 / 31250000)) (hi := (40594669 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8163) = 1/(8163 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4675 : Bounds (-40594669 / 200000000) (-6342917 / 31250000) (Real.log (8163 / 10000)) := by
  have h := reflection_log_4675_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4676_neg : (183683 / 1000000000) ≤ -Real.log (10000000 / 10001837) ∧
    -Real.log (10000000 / 10001837) ≤ (45921 / 250000000) := by
  have h := checkLog_sound (w := (1837 / 20001837)) (n := 12)
    (lo := (183683 / 1000000000)) (hi := (45921 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001837 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001837 / 10000000) = 1/(10000000 / 10001837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4676 : Bounds (183683 / 1000000000) (45921 / 250000000) (Real.log (10001837 / 10000000)) := by
  have h := reflection_log_4676_neg
  have he : Real.log (10001837 / 10000000) = -Real.log (10000000 / 10001837) := by
    rw [show ((10001837 / 10000000) : ℝ) = ((10000000 / 10001837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4677_neg : (45929 / 250000000) ≤ -Real.log (9998163 / 10000000) ∧
    -Real.log (9998163 / 10000000) ≤ (183717 / 1000000000) := by
  have h := checkLog_sound (w := (1837 / 19998163)) (n := 12)
    (lo := (45929 / 250000000)) (hi := (183717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998163) = 1/(9998163 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4677 : Bounds (-183717 / 1000000000) (-45929 / 250000000) (Real.log (9998163 / 10000000)) := by
  have h := reflection_log_4677_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4678_neg : (8825993 / 100000000) ≤ -Real.log (62500 / 68267) ∧
    -Real.log (62500 / 68267) ≤ (88259931 / 1000000000) := by
  have h := checkLog_sound (w := (5767 / 130767)) (n := 12)
    (lo := (8825993 / 100000000)) (hi := (88259931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68267 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68267 / 62500) = 1/(62500 / 68267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4678 : Bounds (8825993 / 100000000) (88259931 / 1000000000) (Real.log (68267 / 62500)) := by
  have h := reflection_log_4678_neg
  have he : Real.log (68267 / 62500) = -Real.log (62500 / 68267) := by
    rw [show ((68267 / 62500) : ℝ) = ((62500 / 68267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4679_neg : (12101313 / 125000000) ≤ -Real.log (56733 / 62500) ∧
    -Real.log (56733 / 62500) ≤ (19362101 / 200000000) := by
  have h := checkLog_sound (w := (5767 / 119233)) (n := 12)
    (lo := (12101313 / 125000000)) (hi := (19362101 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56733) = 1/(56733 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4679 : Bounds (-19362101 / 200000000) (-12101313 / 125000000) (Real.log (56733 / 62500)) := by
  have h := reflection_log_4679_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4680_neg : (88474139 / 1000000000) ≤ -Real.log (500000 / 546253) ∧
    -Real.log (500000 / 546253) ≤ (4423707 / 50000000) := by
  have h := checkLog_sound (w := (46253 / 1046253)) (n := 12)
    (lo := (88474139 / 1000000000)) (hi := (4423707 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546253 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546253 / 500000) = 1/(500000 / 546253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4680 : Bounds (88474139 / 1000000000) (4423707 / 50000000) (Real.log (546253 / 500000)) := by
  have h := reflection_log_4680_neg
  have he : Real.log (546253 / 500000) = -Real.log (500000 / 546253) := by
    rw [show ((546253 / 500000) : ℝ) = ((500000 / 546253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4681_neg : (24267081 / 250000000) ≤ -Real.log (453747 / 500000) ∧
    -Real.log (453747 / 500000) ≤ (3882733 / 40000000) := by
  have h := checkLog_sound (w := (46253 / 953747)) (n := 12)
    (lo := (24267081 / 250000000)) (hi := (3882733 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453747) = 1/(453747 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4681 : Bounds (-3882733 / 40000000) (-24267081 / 250000000) (Real.log (453747 / 500000)) := by
  have h := reflection_log_4681_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4682_neg : (1074273 / 125000000) ≤ -Real.log (247860659991 / 250000000000) ∧
    -Real.log (247860659991 / 250000000000) ≤ (1718837 / 200000000) := by
  have h := checkLog_sound (w := (2139340009 / 497860659991)) (n := 12)
    (lo := (1074273 / 125000000)) (hi := (1718837 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247860659991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247860659991) = 1/(247860659991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4682 : Bounds (-1718837 / 200000000) (-1074273 / 125000000) (Real.log (247860659991 / 250000000000)) := by
  have h := reflection_log_4682_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4683_neg : (4275287 / 500000000) ≤ -Real.log (3872991711 / 3906250000) ∧
    -Real.log (3872991711 / 3906250000) ≤ (342023 / 40000000) := by
  have h := checkLog_sound (w := (33258289 / 7779241711)) (n := 12)
    (lo := (4275287 / 500000000)) (hi := (342023 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3872991711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3872991711) = 1/(3872991711 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4683 : Bounds (-342023 / 40000000) (-4275287 / 500000000) (Real.log (3872991711 / 3906250000)) := by
  have h := reflection_log_4683_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4684_neg : (37014087 / 200000000) ≤ -Real.log (62500000000 / 75206449509) ∧
    -Real.log (62500000000 / 75206449509) ≤ (46267609 / 250000000) := by
  have h := checkLog_sound (w := (12706449509 / 137706449509)) (n := 12)
    (lo := (37014087 / 200000000)) (hi := (46267609 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75206449509 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75206449509 / 62500000000) = 1/(62500000000 / 75206449509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4684 : Bounds (37014087 / 200000000) (46267609 / 250000000) (Real.log (75206449509 / 62500000000)) := by
  have h := reflection_log_4684_neg
  have he : Real.log (75206449509 / 62500000000) = -Real.log (62500000000 / 75206449509) := by
    rw [show ((75206449509 / 62500000000) : ℝ) = ((62500000000 / 75206449509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4685_neg : (2899101 / 15625000) ≤ -Real.log (500000000000 / 601935660181) ∧
    -Real.log (500000000000 / 601935660181) ≤ (37108493 / 200000000) := by
  have h := checkLog_sound (w := (101935660181 / 1101935660181)) (n := 12)
    (lo := (2899101 / 15625000)) (hi := (37108493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601935660181 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(601935660181 / 500000000000) = 1/(500000000000 / 601935660181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4685 : Bounds (2899101 / 15625000) (37108493 / 200000000) (Real.log (601935660181 / 500000000000)) := by
  have h := reflection_log_4685_neg
  have he : Real.log (601935660181 / 500000000000) = -Real.log (500000000000 / 601935660181) := by
    rw [show ((601935660181 / 500000000000) : ℝ) = ((500000000000 / 601935660181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4686_neg : (371411489 / 1000000000) ≤ -Real.log (500000000000 / 724889759921) ∧
    -Real.log (500000000000 / 724889759921) ≤ (37141149 / 100000000) := by
  have h := checkLog_sound (w := (224889759921 / 1224889759921)) (n := 12)
    (lo := (371411489 / 1000000000)) (hi := (37141149 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((724889759921 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(724889759921 / 500000000000) = 1/(500000000000 / 724889759921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4686 : Bounds (371411489 / 1000000000) (37141149 / 100000000) (Real.log (724889759921 / 500000000000)) := by
  have h := reflection_log_4686_neg
  have he : Real.log (724889759921 / 500000000000) = -Real.log (500000000000 / 724889759921) := by
    rw [show ((724889759921 / 500000000000) : ℝ) = ((500000000000 / 724889759921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4687_neg : (37161847 / 100000000) ≤ -Real.log (250000000000 / 362519906897) ∧
    -Real.log (250000000000 / 362519906897) ≤ (371618471 / 1000000000) := by
  have h := checkLog_sound (w := (112519906897 / 612519906897)) (n := 12)
    (lo := (37161847 / 100000000)) (hi := (371618471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((362519906897 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(362519906897 / 250000000000) = 1/(250000000000 / 362519906897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4687 : Bounds (37161847 / 100000000) (371618471 / 1000000000) (Real.log (362519906897 / 250000000000)) := by
  have h := reflection_log_4687_neg
  have he : Real.log (362519906897 / 250000000000) = -Real.log (250000000000 / 362519906897) := by
    rw [show ((362519906897 / 250000000000) : ℝ) = ((250000000000 / 362519906897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4688_neg : (168729603 / 1000000000) ≤ -Real.log (5000 / 5919) ∧
    -Real.log (5000 / 5919) ≤ (42182401 / 250000000) := by
  have h := checkLog_sound (w := (919 / 10919)) (n := 12)
    (lo := (168729603 / 1000000000)) (hi := (42182401 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5919 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5919 / 5000) = 1/(5000 / 5919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4688 : Bounds (168729603 / 1000000000) (42182401 / 250000000) (Real.log (5919 / 5000)) := by
  have h := reflection_log_4688_neg
  have he : Real.log (5919 / 5000) = -Real.log (5000 / 5919) := by
    rw [show ((5919 / 5000) : ℝ) = ((5000 / 5919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4689_neg : (12693491 / 62500000) ≤ -Real.log (4081 / 5000) ∧
    -Real.log (4081 / 5000) ≤ (203095857 / 1000000000) := by
  have h := checkLog_sound (w := (919 / 9081)) (n := 12)
    (lo := (12693491 / 62500000)) (hi := (203095857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4081) = 1/(4081 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4689 : Bounds (-203095857 / 1000000000) (-12693491 / 62500000) (Real.log (4081 / 5000)) := by
  have h := reflection_log_4689_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4690_neg : (183783 / 1000000000) ≤ -Real.log (5000000 / 5000919) ∧
    -Real.log (5000000 / 5000919) ≤ (22973 / 125000000) := by
  have h := checkLog_sound (w := (919 / 10000919)) (n := 12)
    (lo := (183783 / 1000000000)) (hi := (22973 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000919 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000919 / 5000000) = 1/(5000000 / 5000919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4690 : Bounds (183783 / 1000000000) (22973 / 125000000) (Real.log (5000919 / 5000000)) := by
  have h := reflection_log_4690_neg
  have he : Real.log (5000919 / 5000000) = -Real.log (5000000 / 5000919) := by
    rw [show ((5000919 / 5000000) : ℝ) = ((5000000 / 5000919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4691_neg : (22977 / 125000000) ≤ -Real.log (4999081 / 5000000) ∧
    -Real.log (4999081 / 5000000) ≤ (183817 / 1000000000) := by
  have h := checkLog_sound (w := (919 / 9999081)) (n := 12)
    (lo := (22977 / 125000000)) (hi := (183817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999081) = 1/(4999081 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4691 : Bounds (-183817 / 1000000000) (-22977 / 125000000) (Real.log (4999081 / 5000000)) := by
  have h := reflection_log_4691_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4692_neg : (88306621 / 1000000000) ≤ -Real.log (1000000 / 1092323) ∧
    -Real.log (1000000 / 1092323) ≤ (44153311 / 500000000) := by
  have h := checkLog_sound (w := (92323 / 2092323)) (n := 12)
    (lo := (88306621 / 1000000000)) (hi := (44153311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092323 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1092323 / 1000000) = 1/(1000000 / 1092323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4692 : Bounds (88306621 / 1000000000) (44153311 / 500000000) (Real.log (1092323 / 1000000)) := by
  have h := reflection_log_4692_neg
  have he : Real.log (1092323 / 1000000) = -Real.log (1000000 / 1092323) := by
    rw [show ((1092323 / 1000000) : ℝ) = ((1000000 / 1092323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4693_neg : (9686669 / 100000000) ≤ -Real.log (907677 / 1000000) ∧
    -Real.log (907677 / 1000000) ≤ (96866691 / 1000000000) := by
  have h := checkLog_sound (w := (92323 / 1907677)) (n := 12)
    (lo := (9686669 / 100000000)) (hi := (96866691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 907677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 907677) = 1/(907677 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4693 : Bounds (-96866691 / 1000000000) (-9686669 / 100000000) (Real.log (907677 / 1000000)) := by
  have h := reflection_log_4693_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4694_neg : (4426041 / 50000000) ≤ -Real.log (1000000 / 1092557) ∧
    -Real.log (1000000 / 1092557) ≤ (88520821 / 1000000000) := by
  have h := checkLog_sound (w := (92557 / 2092557)) (n := 12)
    (lo := (4426041 / 50000000)) (hi := (88520821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092557 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1092557 / 1000000) = 1/(1000000 / 1092557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4694 : Bounds (4426041 / 50000000) (88520821 / 1000000000) (Real.log (1092557 / 1000000)) := by
  have h := reflection_log_4694_neg
  have he : Real.log (1092557 / 1000000) = -Real.log (1000000 / 1092557) := by
    rw [show ((1092557 / 1000000) : ℝ) = ((1000000 / 1092557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4695_neg : (24281131 / 250000000) ≤ -Real.log (907443 / 1000000) ∧
    -Real.log (907443 / 1000000) ≤ (3884981 / 40000000) := by
  have h := checkLog_sound (w := (92557 / 1907443)) (n := 12)
    (lo := (24281131 / 250000000)) (hi := (3884981 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 907443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 907443) = 1/(907443 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4695 : Bounds (-3884981 / 40000000) (-24281131 / 250000000) (Real.log (907443 / 1000000)) := by
  have h := reflection_log_4695_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4696_neg : (1075463 / 125000000) ≤ -Real.log (991433201751 / 1000000000000) ∧
    -Real.log (991433201751 / 1000000000000) ≤ (1720741 / 200000000) := by
  have h := checkLog_sound (w := (8566798249 / 1991433201751)) (n := 12)
    (lo := (1075463 / 125000000)) (hi := (1720741 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991433201751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991433201751) = 1/(991433201751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4696 : Bounds (-1720741 / 200000000) (-1075463 / 125000000) (Real.log (991433201751 / 1000000000000)) := by
  have h := reflection_log_4696_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4697_neg : (8560069 / 1000000000) ≤ -Real.log (991476463671 / 1000000000000) ∧
    -Real.log (991476463671 / 1000000000000) ≤ (856007 / 100000000) := by
  have h := checkLog_sound (w := (8523536329 / 1991476463671)) (n := 12)
    (lo := (8560069 / 1000000000)) (hi := (856007 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991476463671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991476463671) = 1/(991476463671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4697 : Bounds (-856007 / 100000000) (-8560069 / 1000000000) (Real.log (991476463671 / 1000000000000)) := by
  have h := reflection_log_4697_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4698_neg : (185173311 / 1000000000) ≤ -Real.log (250000000000 / 300856747499) ∧
    -Real.log (250000000000 / 300856747499) ≤ (2893333 / 15625000) := by
  have h := checkLog_sound (w := (50856747499 / 550856747499)) (n := 12)
    (lo := (185173311 / 1000000000)) (hi := (2893333 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300856747499 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300856747499 / 250000000000) = 1/(250000000000 / 300856747499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4698 : Bounds (185173311 / 1000000000) (2893333 / 15625000) (Real.log (300856747499 / 250000000000)) := by
  have h := reflection_log_4698_neg
  have he : Real.log (300856747499 / 250000000000) = -Real.log (250000000000 / 300856747499) := by
    rw [show ((300856747499 / 250000000000) : ℝ) = ((250000000000 / 300856747499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4699_neg : (37129069 / 200000000) ≤ -Real.log (250000000000 / 300998795517) ∧
    -Real.log (250000000000 / 300998795517) ≤ (92822673 / 500000000) := by
  have h := checkLog_sound (w := (50998795517 / 550998795517)) (n := 12)
    (lo := (37129069 / 200000000)) (hi := (92822673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300998795517 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300998795517 / 250000000000) = 1/(250000000000 / 300998795517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4699 : Bounds (37129069 / 200000000) (92822673 / 500000000) (Real.log (300998795517 / 250000000000)) := by
  have h := reflection_log_4699_neg
  have he : Real.log (300998795517 / 250000000000) = -Real.log (250000000000 / 300998795517) := by
    rw [show ((300998795517 / 250000000000) : ℝ) = ((250000000000 / 300998795517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4700_neg : (37161847 / 100000000) ≤ -Real.log (500000000000 / 725039813793) ∧
    -Real.log (500000000000 / 725039813793) ≤ (371618471 / 1000000000) := by
  have h := checkLog_sound (w := (225039813793 / 1225039813793)) (n := 12)
    (lo := (37161847 / 100000000)) (hi := (371618471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((725039813793 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(725039813793 / 500000000000) = 1/(500000000000 / 725039813793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4700 : Bounds (37161847 / 100000000) (371618471 / 1000000000) (Real.log (725039813793 / 500000000000)) := by
  have h := reflection_log_4700_neg
  have he : Real.log (725039813793 / 500000000000) = -Real.log (500000000000 / 725039813793) := by
    rw [show ((725039813793 / 500000000000) : ℝ) = ((500000000000 / 725039813793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4701_neg : (371825459 / 1000000000) ≤ -Real.log (125000000000 / 181297476109) ∧
    -Real.log (125000000000 / 181297476109) ≤ (18591273 / 50000000) := by
  have h := checkLog_sound (w := (56297476109 / 306297476109)) (n := 12)
    (lo := (371825459 / 1000000000)) (hi := (18591273 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181297476109 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181297476109 / 125000000000) = 1/(125000000000 / 181297476109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4701 : Bounds (371825459 / 1000000000) (18591273 / 50000000) (Real.log (181297476109 / 125000000000)) := by
  have h := reflection_log_4701_neg
  have he : Real.log (181297476109 / 125000000000) = -Real.log (125000000000 / 181297476109) := by
    rw [show ((181297476109 / 125000000000) : ℝ) = ((125000000000 / 181297476109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4702_neg : (168814073 / 1000000000) ≤ -Real.log (10000 / 11839) ∧
    -Real.log (10000 / 11839) ≤ (84407037 / 500000000) := by
  have h := checkLog_sound (w := (1839 / 21839)) (n := 12)
    (lo := (168814073 / 1000000000)) (hi := (84407037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11839 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11839 / 10000) = 1/(10000 / 11839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4702 : Bounds (168814073 / 1000000000) (84407037 / 500000000) (Real.log (11839 / 10000)) := by
  have h := reflection_log_4702_neg
  have he : Real.log (11839 / 10000) = -Real.log (10000 / 11839) := by
    rw [show ((11839 / 10000) : ℝ) = ((10000 / 11839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4703_neg : (101609191 / 500000000) ≤ -Real.log (8161 / 10000) ∧
    -Real.log (8161 / 10000) ≤ (203218383 / 1000000000) := by
  have h := checkLog_sound (w := (1839 / 18161)) (n := 12)
    (lo := (101609191 / 500000000)) (hi := (203218383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8161) = 1/(8161 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4703 : Bounds (-203218383 / 1000000000) (-101609191 / 500000000) (Real.log (8161 / 10000)) := by
  have h := reflection_log_4703_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4704_neg : (183883 / 1000000000) ≤ -Real.log (10000000 / 10001839) ∧
    -Real.log (10000000 / 10001839) ≤ (45971 / 250000000) := by
  have h := checkLog_sound (w := (1839 / 20001839)) (n := 12)
    (lo := (183883 / 1000000000)) (hi := (45971 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001839 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001839 / 10000000) = 1/(10000000 / 10001839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4704 : Bounds (183883 / 1000000000) (45971 / 250000000) (Real.log (10001839 / 10000000)) := by
  have h := reflection_log_4704_neg
  have he : Real.log (10001839 / 10000000) = -Real.log (10000000 / 10001839) := by
    rw [show ((10001839 / 10000000) : ℝ) = ((10000000 / 10001839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4705_neg : (45979 / 250000000) ≤ -Real.log (9998161 / 10000000) ∧
    -Real.log (9998161 / 10000000) ≤ (183917 / 1000000000) := by
  have h := checkLog_sound (w := (1839 / 19998161)) (n := 12)
    (lo := (45979 / 250000000)) (hi := (183917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998161) = 1/(9998161 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4705 : Bounds (-183917 / 1000000000) (-45979 / 250000000) (Real.log (9998161 / 10000000)) := by
  have h := reflection_log_4705_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4706_neg : (88353309 / 1000000000) ≤ -Real.log (500000 / 546187) ∧
    -Real.log (500000 / 546187) ≤ (8835331 / 100000000) := by
  have h := checkLog_sound (w := (46187 / 1046187)) (n := 12)
    (lo := (88353309 / 1000000000)) (hi := (8835331 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546187 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546187 / 500000) = 1/(500000 / 546187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4706 : Bounds (88353309 / 1000000000) (8835331 / 100000000) (Real.log (546187 / 500000)) := by
  have h := reflection_log_4706_neg
  have he : Real.log (546187 / 500000) = -Real.log (500000 / 546187) := by
    rw [show ((546187 / 500000) : ℝ) = ((500000 / 546187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4707_neg : (96922879 / 1000000000) ≤ -Real.log (453813 / 500000) ∧
    -Real.log (453813 / 500000) ≤ (75721 / 781250) := by
  have h := checkLog_sound (w := (46187 / 953813)) (n := 12)
    (lo := (96922879 / 1000000000)) (hi := (75721 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453813) = 1/(453813 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4707 : Bounds (-75721 / 781250) (-96922879 / 1000000000) (Real.log (453813 / 500000)) := by
  have h := reflection_log_4707_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4708_neg : (44283749 / 500000000) ≤ -Real.log (15625 / 17072) ∧
    -Real.log (15625 / 17072) ≤ (88567499 / 1000000000) := by
  have h := checkLog_sound (w := (1447 / 32697)) (n := 12)
    (lo := (44283749 / 500000000)) (hi := (88567499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17072 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17072 / 15625) = 1/(15625 / 17072) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4708 : Bounds (44283749 / 500000000) (88567499 / 1000000000) (Real.log (17072 / 15625)) := by
  have h := reflection_log_4708_neg
  have he : Real.log (17072 / 15625) = -Real.log (15625 / 17072) := by
    rw [show ((17072 / 15625) : ℝ) = ((15625 / 17072) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4709_neg : (12147591 / 125000000) ≤ -Real.log (14178 / 15625) ∧
    -Real.log (14178 / 15625) ≤ (97180729 / 1000000000) := by
  have h := checkLog_sound (w := (1447 / 29803)) (n := 12)
    (lo := (12147591 / 125000000)) (hi := (97180729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14178) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 14178) = 1/(14178 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4709 : Bounds (-97180729 / 1000000000) (-12147591 / 125000000) (Real.log (14178 / 15625)) := by
  have h := reflection_log_4709_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4710_neg : (8613229 / 1000000000) ≤ -Real.log (242046816 / 244140625) ∧
    -Real.log (242046816 / 244140625) ≤ (861323 / 100000000) := by
  have h := checkLog_sound (w := (2093809 / 486187441)) (n := 12)
    (lo := (8613229 / 1000000000)) (hi := (861323 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 242046816) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 242046816) = 1/(242046816 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4710 : Bounds (-861323 / 100000000) (-8613229 / 1000000000) (Real.log (242046816 / 244140625)) := by
  have h := reflection_log_4710_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4711_neg : (8569569 / 1000000000) ≤ -Real.log (247866761031 / 250000000000) ∧
    -Real.log (247866761031 / 250000000000) ≤ (856957 / 100000000) := by
  have h := checkLog_sound (w := (2133238969 / 497866761031)) (n := 12)
    (lo := (8569569 / 1000000000)) (hi := (856957 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247866761031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247866761031) = 1/(247866761031 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4711 : Bounds (-856957 / 100000000) (-8569569 / 1000000000) (Real.log (247866761031 / 250000000000)) := by
  have h := reflection_log_4711_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4712_neg : (185276189 / 1000000000) ≤ -Real.log (6250000000 / 7522192511) ∧
    -Real.log (6250000000 / 7522192511) ≤ (18527619 / 100000000) := by
  have h := checkLog_sound (w := (1272192511 / 13772192511)) (n := 12)
    (lo := (185276189 / 1000000000)) (hi := (18527619 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7522192511 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7522192511 / 6250000000) = 1/(6250000000 / 7522192511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4712 : Bounds (185276189 / 1000000000) (18527619 / 100000000) (Real.log (7522192511 / 6250000000)) := by
  have h := reflection_log_4712_neg
  have he : Real.log (7522192511 / 6250000000) = -Real.log (6250000000 / 7522192511) := by
    rw [show ((7522192511 / 6250000000) : ℝ) = ((6250000000 / 7522192511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4713_neg : (185748227 / 1000000000) ≤ -Real.log (31250000000 / 37628720553) ∧
    -Real.log (31250000000 / 37628720553) ≤ (46437057 / 250000000) := by
  have h := checkLog_sound (w := (6378720553 / 68878720553)) (n := 12)
    (lo := (185748227 / 1000000000)) (hi := (46437057 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37628720553 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37628720553 / 31250000000) = 1/(31250000000 / 37628720553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4713 : Bounds (185748227 / 1000000000) (46437057 / 250000000) (Real.log (37628720553 / 31250000000)) := by
  have h := reflection_log_4713_neg
  have he : Real.log (37628720553 / 31250000000) = -Real.log (31250000000 / 37628720553) := by
    rw [show ((37628720553 / 31250000000) : ℝ) = ((31250000000 / 37628720553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4714_neg : (371825459 / 1000000000) ≤ -Real.log (100000000000 / 145037980887) ∧
    -Real.log (100000000000 / 145037980887) ≤ (18591273 / 50000000) := by
  have h := checkLog_sound (w := (45037980887 / 245037980887)) (n := 12)
    (lo := (371825459 / 1000000000)) (hi := (18591273 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145037980887 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145037980887 / 100000000000) = 1/(100000000000 / 145037980887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4714 : Bounds (371825459 / 1000000000) (18591273 / 50000000) (Real.log (145037980887 / 100000000000)) := by
  have h := reflection_log_4714_neg
  have he : Real.log (145037980887 / 100000000000) = -Real.log (100000000000 / 145037980887) := by
    rw [show ((145037980887 / 100000000000) : ℝ) = ((100000000000 / 145037980887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4715_neg : (74406491 / 200000000) ≤ -Real.log (500000000000 / 725340031859) ∧
    -Real.log (500000000000 / 725340031859) ≤ (46504057 / 125000000) := by
  have h := checkLog_sound (w := (225340031859 / 1225340031859)) (n := 12)
    (lo := (74406491 / 200000000)) (hi := (46504057 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((725340031859 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(725340031859 / 500000000000) = 1/(500000000000 / 725340031859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4715 : Bounds (74406491 / 200000000) (46504057 / 125000000) (Real.log (725340031859 / 500000000000)) := by
  have h := reflection_log_4715_neg
  have he : Real.log (725340031859 / 500000000000) = -Real.log (500000000000 / 725340031859) := by
    rw [show ((725340031859 / 500000000000) : ℝ) = ((500000000000 / 725340031859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4716_neg : (21112317 / 125000000) ≤ -Real.log (125 / 148) ∧
    -Real.log (125 / 148) ≤ (168898537 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 273)) (n := 12)
    (lo := (21112317 / 125000000)) (hi := (168898537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148 / 125) = 1/(125 / 148) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4716 : Bounds (21112317 / 125000000) (168898537 / 1000000000) (Real.log (148 / 125)) := by
  have h := reflection_log_4716_neg
  have he : Real.log (148 / 125) = -Real.log (125 / 148) := by
    rw [show ((148 / 125) : ℝ) = ((125 / 148) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4717_neg : (50835231 / 250000000) ≤ -Real.log (102 / 125) ∧
    -Real.log (102 / 125) ≤ (8133637 / 40000000) := by
  have h := checkLog_sound (w := (23 / 227)) (n := 12)
    (lo := (50835231 / 250000000)) (hi := (8133637 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 102) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 102) = 1/(102 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4717 : Bounds (-8133637 / 40000000) (-50835231 / 250000000) (Real.log (102 / 125)) := by
  have h := reflection_log_4717_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4718_neg : (183983 / 1000000000) ≤ -Real.log (125000 / 125023) ∧
    -Real.log (125000 / 125023) ≤ (11499 / 62500000) := by
  have h := checkLog_sound (w := (23 / 250023)) (n := 12)
    (lo := (183983 / 1000000000)) (hi := (11499 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125023 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125023 / 125000) = 1/(125000 / 125023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4718 : Bounds (183983 / 1000000000) (11499 / 62500000) (Real.log (125023 / 125000)) := by
  have h := reflection_log_4718_neg
  have he : Real.log (125023 / 125000) = -Real.log (125000 / 125023) := by
    rw [show ((125023 / 125000) : ℝ) = ((125000 / 125023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4719_neg : (11501 / 62500000) ≤ -Real.log (124977 / 125000) ∧
    -Real.log (124977 / 125000) ≤ (184017 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 249977)) (n := 12)
    (lo := (11501 / 62500000)) (hi := (184017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124977) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124977) = 1/(124977 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4719 : Bounds (-184017 / 1000000000) (-11501 / 62500000) (Real.log (124977 / 125000)) := by
  have h := reflection_log_4719_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4720_neg : (17679999 / 200000000) ≤ -Real.log (40000 / 43697) ∧
    -Real.log (40000 / 43697) ≤ (22099999 / 250000000) := by
  have h := checkLog_sound (w := (3697 / 83697)) (n := 12)
    (lo := (17679999 / 200000000)) (hi := (22099999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43697 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43697 / 40000) = 1/(40000 / 43697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4720 : Bounds (17679999 / 200000000) (22099999 / 250000000) (Real.log (43697 / 40000)) := by
  have h := reflection_log_4720_neg
  have he : Real.log (43697 / 40000) = -Real.log (40000 / 43697) := by
    rw [show ((43697 / 40000) : ℝ) = ((40000 / 43697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4721_neg : (96979071 / 1000000000) ≤ -Real.log (36303 / 40000) ∧
    -Real.log (36303 / 40000) ≤ (757649 / 7812500) := by
  have h := checkLog_sound (w := (3697 / 76303)) (n := 12)
    (lo := (96979071 / 1000000000)) (hi := (757649 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36303) = 1/(36303 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4721 : Bounds (-757649 / 7812500) (-96979071 / 1000000000) (Real.log (36303 / 40000)) := by
  have h := reflection_log_4721_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4722_neg : (3544567 / 40000000) ≤ -Real.log (1000000 / 1092659) ∧
    -Real.log (1000000 / 1092659) ≤ (2769193 / 31250000) := by
  have h := checkLog_sound (w := (92659 / 2092659)) (n := 12)
    (lo := (3544567 / 40000000)) (hi := (2769193 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092659 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1092659 / 1000000) = 1/(1000000 / 1092659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4722 : Bounds (3544567 / 40000000) (2769193 / 31250000) (Real.log (1092659 / 1000000)) := by
  have h := reflection_log_4722_neg
  have he : Real.log (1092659 / 1000000) = -Real.log (1000000 / 1092659) := by
    rw [show ((1092659 / 1000000) : ℝ) = ((1000000 / 1092659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4723_neg : (48618467 / 500000000) ≤ -Real.log (907341 / 1000000) ∧
    -Real.log (907341 / 1000000) ≤ (19447387 / 200000000) := by
  have h := checkLog_sound (w := (92659 / 1907341)) (n := 12)
    (lo := (48618467 / 500000000)) (hi := (19447387 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 907341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 907341) = 1/(907341 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4723 : Bounds (-19447387 / 200000000) (-48618467 / 500000000) (Real.log (907341 / 1000000)) := by
  have h := reflection_log_4723_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4724_neg : (8622759 / 1000000000) ≤ -Real.log (991414309719 / 1000000000000) ∧
    -Real.log (991414309719 / 1000000000000) ≤ (215569 / 25000000) := by
  have h := checkLog_sound (w := (8585690281 / 1991414309719)) (n := 12)
    (lo := (8622759 / 1000000000)) (hi := (215569 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991414309719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991414309719) = 1/(991414309719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4724 : Bounds (-215569 / 25000000) (-8622759 / 1000000000) (Real.log (991414309719 / 1000000000000)) := by
  have h := reflection_log_4724_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4725_neg : (343163 / 40000000) ≤ -Real.log (1586332191 / 1600000000) ∧
    -Real.log (1586332191 / 1600000000) ≤ (2144769 / 250000000) := by
  have h := checkLog_sound (w := (13667809 / 3186332191)) (n := 12)
    (lo := (343163 / 40000000)) (hi := (2144769 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1586332191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1586332191) = 1/(1586332191 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4725 : Bounds (-2144769 / 250000000) (-343163 / 40000000) (Real.log (1586332191 / 1600000000)) := by
  have h := reflection_log_4725_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4726_neg : (185379067 / 1000000000) ≤ -Real.log (12500000000 / 15045932843) ∧
    -Real.log (12500000000 / 15045932843) ≤ (46344767 / 250000000) := by
  have h := checkLog_sound (w := (2545932843 / 27545932843)) (n := 12)
    (lo := (185379067 / 1000000000)) (hi := (46344767 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15045932843 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15045932843 / 12500000000) = 1/(12500000000 / 15045932843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4726 : Bounds (185379067 / 1000000000) (46344767 / 250000000) (Real.log (15045932843 / 12500000000)) := by
  have h := reflection_log_4726_neg
  have he : Real.log (15045932843 / 12500000000) = -Real.log (12500000000 / 15045932843) := by
    rw [show ((15045932843 / 12500000000) : ℝ) = ((12500000000 / 15045932843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4727_neg : (185851109 / 1000000000) ≤ -Real.log (4000000000 / 4816971789) ∧
    -Real.log (4000000000 / 4816971789) ≤ (18585111 / 100000000) := by
  have h := checkLog_sound (w := (816971789 / 8816971789)) (n := 12)
    (lo := (185851109 / 1000000000)) (hi := (18585111 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4816971789 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4816971789 / 4000000000) = 1/(4000000000 / 4816971789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4727 : Bounds (185851109 / 1000000000) (18585111 / 100000000) (Real.log (4816971789 / 4000000000)) := by
  have h := reflection_log_4727_neg
  have he : Real.log (4816971789 / 4000000000) = -Real.log (4000000000 / 4816971789) := by
    rw [show ((4816971789 / 4000000000) : ℝ) = ((4000000000 / 4816971789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4728_neg : (74406491 / 200000000) ≤ -Real.log (250000000000 / 362670015929) ∧
    -Real.log (250000000000 / 362670015929) ≤ (46504057 / 125000000) := by
  have h := checkLog_sound (w := (112670015929 / 612670015929)) (n := 12)
    (lo := (74406491 / 200000000)) (hi := (46504057 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((362670015929 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(362670015929 / 250000000000) = 1/(250000000000 / 362670015929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4728 : Bounds (74406491 / 200000000) (46504057 / 125000000) (Real.log (362670015929 / 250000000000)) := by
  have h := reflection_log_4728_neg
  have he : Real.log (362670015929 / 250000000000) = -Real.log (250000000000 / 362670015929) := by
    rw [show ((362670015929 / 250000000000) : ℝ) = ((250000000000 / 362670015929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4729_neg : (18611973 / 50000000) ≤ -Real.log (500000000000 / 725490196079) ∧
    -Real.log (500000000000 / 725490196079) ≤ (372239461 / 1000000000) := by
  have h := checkLog_sound (w := (225490196079 / 1225490196079)) (n := 12)
    (lo := (18611973 / 50000000)) (hi := (372239461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((725490196079 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(725490196079 / 500000000000) = 1/(500000000000 / 725490196079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4729 : Bounds (18611973 / 50000000) (372239461 / 1000000000) (Real.log (725490196079 / 500000000000)) := by
  have h := reflection_log_4729_neg
  have he : Real.log (725490196079 / 500000000000) = -Real.log (500000000000 / 725490196079) := by
    rw [show ((725490196079 / 500000000000) : ℝ) = ((500000000000 / 725490196079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4730_neg : (10561437 / 62500000) ≤ -Real.log (10000 / 11841) ∧
    -Real.log (10000 / 11841) ≤ (168982993 / 1000000000) := by
  have h := checkLog_sound (w := (1841 / 21841)) (n := 12)
    (lo := (10561437 / 62500000)) (hi := (168982993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11841 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11841 / 10000) = 1/(10000 / 11841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4730 : Bounds (10561437 / 62500000) (168982993 / 1000000000) (Real.log (11841 / 10000)) := by
  have h := reflection_log_4730_neg
  have he : Real.log (11841 / 10000) = -Real.log (10000 / 11841) := by
    rw [show ((11841 / 10000) : ℝ) = ((10000 / 11841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4731_neg : (5086587 / 25000000) ≤ -Real.log (8159 / 10000) ∧
    -Real.log (8159 / 10000) ≤ (203463481 / 1000000000) := by
  have h := checkLog_sound (w := (1841 / 18159)) (n := 12)
    (lo := (5086587 / 25000000)) (hi := (203463481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8159) = 1/(8159 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4731 : Bounds (-203463481 / 1000000000) (-5086587 / 25000000) (Real.log (8159 / 10000)) := by
  have h := reflection_log_4731_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4732_neg : (184083 / 1000000000) ≤ -Real.log (10000000 / 10001841) ∧
    -Real.log (10000000 / 10001841) ≤ (46021 / 250000000) := by
  have h := checkLog_sound (w := (1841 / 20001841)) (n := 12)
    (lo := (184083 / 1000000000)) (hi := (46021 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001841 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001841 / 10000000) = 1/(10000000 / 10001841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4732 : Bounds (184083 / 1000000000) (46021 / 250000000) (Real.log (10001841 / 10000000)) := by
  have h := reflection_log_4732_neg
  have he : Real.log (10001841 / 10000000) = -Real.log (10000000 / 10001841) := by
    rw [show ((10001841 / 10000000) : ℝ) = ((10000000 / 10001841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4733_neg : (46029 / 250000000) ≤ -Real.log (9998159 / 10000000) ∧
    -Real.log (9998159 / 10000000) ≤ (184117 / 1000000000) := by
  have h := checkLog_sound (w := (1841 / 19998159)) (n := 12)
    (lo := (46029 / 250000000)) (hi := (184117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998159) = 1/(9998159 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4733 : Bounds (-184117 / 1000000000) (-46029 / 250000000) (Real.log (9998159 / 10000000)) := by
  have h := reflection_log_4733_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4734_neg : (22111441 / 250000000) ≤ -Real.log (40000 / 43699) ∧
    -Real.log (40000 / 43699) ≤ (17689153 / 200000000) := by
  have h := checkLog_sound (w := (3699 / 83699)) (n := 12)
    (lo := (22111441 / 250000000)) (hi := (17689153 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43699 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43699 / 40000) = 1/(40000 / 43699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4734 : Bounds (22111441 / 250000000) (17689153 / 200000000) (Real.log (43699 / 40000)) := by
  have h := reflection_log_4734_neg
  have he : Real.log (43699 / 40000) = -Real.log (40000 / 43699) := by
    rw [show ((43699 / 40000) : ℝ) = ((40000 / 43699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4735_neg : (19406833 / 200000000) ≤ -Real.log (36301 / 40000) ∧
    -Real.log (36301 / 40000) ≤ (48517083 / 500000000) := by
  have h := checkLog_sound (w := (3699 / 76301)) (n := 12)
    (lo := (19406833 / 200000000)) (hi := (48517083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36301) = 1/(36301 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4735 : Bounds (-48517083 / 500000000) (-19406833 / 200000000) (Real.log (36301 / 40000)) := by
  have h := reflection_log_4735_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0074 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4736_neg : (88660849 / 1000000000) ≤ -Real.log (100000 / 109271) ∧
    -Real.log (100000 / 109271) ≤ (1773217 / 20000000) := by
  have h := checkLog_sound (w := (9271 / 209271)) (n := 12)
    (lo := (88660849 / 1000000000)) (hi := (1773217 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109271 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109271 / 100000) = 1/(100000 / 109271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4736 : Bounds (88660849 / 1000000000) (1773217 / 20000000) (Real.log (109271 / 100000)) := by
  have h := reflection_log_4736_neg
  have he : Real.log (109271 / 100000) = -Real.log (100000 / 109271) := by
    rw [show ((109271 / 100000) : ℝ) = ((100000 / 109271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4737_neg : (12161643 / 125000000) ≤ -Real.log (90729 / 100000) ∧
    -Real.log (90729 / 100000) ≤ (19458629 / 200000000) := by
  have h := checkLog_sound (w := (9271 / 190729)) (n := 12)
    (lo := (12161643 / 125000000)) (hi := (19458629 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90729) = 1/(90729 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4737 : Bounds (-19458629 / 200000000) (-12161643 / 125000000) (Real.log (90729 / 100000)) := by
  have h := reflection_log_4737_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4738_neg : (1726459 / 200000000) ≤ -Real.log (9914048559 / 10000000000) ∧
    -Real.log (9914048559 / 10000000000) ≤ (1079037 / 125000000) := by
  have h := checkLog_sound (w := (85951441 / 19914048559)) (n := 12)
    (lo := (1726459 / 200000000)) (hi := (1079037 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9914048559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9914048559) = 1/(9914048559 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4738 : Bounds (-1079037 / 125000000) (-1726459 / 200000000) (Real.log (9914048559 / 10000000000)) := by
  have h := reflection_log_4738_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4739_neg : (21471 / 2500000) ≤ -Real.log (1586317399 / 1600000000) ∧
    -Real.log (1586317399 / 1600000000) ≤ (8588401 / 1000000000) := by
  have h := checkLog_sound (w := (13682601 / 3186317399)) (n := 12)
    (lo := (21471 / 2500000)) (hi := (8588401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1586317399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1586317399) = 1/(1586317399 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4739 : Bounds (-8588401 / 1000000000) (-21471 / 2500000) (Real.log (1586317399 / 1600000000)) := by
  have h := reflection_log_4739_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4740_neg : (185479929 / 1000000000) ≤ -Real.log (250000000000 / 300949009669) ∧
    -Real.log (250000000000 / 300949009669) ≤ (18547993 / 100000000) := by
  have h := checkLog_sound (w := (50949009669 / 550949009669)) (n := 12)
    (lo := (185479929 / 1000000000)) (hi := (18547993 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300949009669 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300949009669 / 250000000000) = 1/(250000000000 / 300949009669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4740 : Bounds (185479929 / 1000000000) (18547993 / 100000000) (Real.log (300949009669 / 250000000000)) := by
  have h := reflection_log_4740_neg
  have he : Real.log (300949009669 / 250000000000) = -Real.log (250000000000 / 300949009669) := by
    rw [show ((300949009669 / 250000000000) : ℝ) = ((250000000000 / 300949009669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4741_neg : (185953993 / 1000000000) ≤ -Real.log (250000000000 / 301091712683) ∧
    -Real.log (250000000000 / 301091712683) ≤ (92976997 / 500000000) := by
  have h := checkLog_sound (w := (51091712683 / 551091712683)) (n := 12)
    (lo := (185953993 / 1000000000)) (hi := (92976997 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301091712683 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301091712683 / 250000000000) = 1/(250000000000 / 301091712683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4741 : Bounds (185953993 / 1000000000) (92976997 / 500000000) (Real.log (301091712683 / 250000000000)) := by
  have h := reflection_log_4741_neg
  have he : Real.log (301091712683 / 250000000000) = -Real.log (250000000000 / 301091712683) := by
    rw [show ((301091712683 / 250000000000) : ℝ) = ((250000000000 / 301091712683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4742_neg : (18611973 / 50000000) ≤ -Real.log (250000000000 / 362745098039) ∧
    -Real.log (250000000000 / 362745098039) ≤ (372239461 / 1000000000) := by
  have h := checkLog_sound (w := (112745098039 / 612745098039)) (n := 12)
    (lo := (18611973 / 50000000)) (hi := (372239461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((362745098039 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(362745098039 / 250000000000) = 1/(250000000000 / 362745098039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4742 : Bounds (18611973 / 50000000) (372239461 / 1000000000) (Real.log (362745098039 / 250000000000)) := by
  have h := reflection_log_4742_neg
  have he : Real.log (362745098039 / 250000000000) = -Real.log (250000000000 / 362745098039) := by
    rw [show ((362745098039 / 250000000000) : ℝ) = ((250000000000 / 362745098039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4743_neg : (46555809 / 125000000) ≤ -Real.log (125000000000 / 181410099277) ∧
    -Real.log (125000000000 / 181410099277) ≤ (372446473 / 1000000000) := by
  have h := checkLog_sound (w := (56410099277 / 306410099277)) (n := 12)
    (lo := (46555809 / 125000000)) (hi := (372446473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181410099277 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181410099277 / 125000000000) = 1/(125000000000 / 181410099277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4743 : Bounds (46555809 / 125000000) (372446473 / 1000000000) (Real.log (181410099277 / 125000000000)) := by
  have h := reflection_log_4743_neg
  have he : Real.log (181410099277 / 125000000000) = -Real.log (125000000000 / 181410099277) := by
    rw [show ((181410099277 / 125000000000) : ℝ) = ((125000000000 / 181410099277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4744_neg : (169067441 / 1000000000) ≤ -Real.log (5000 / 5921) ∧
    -Real.log (5000 / 5921) ≤ (84533721 / 500000000) := by
  have h := checkLog_sound (w := (921 / 10921)) (n := 12)
    (lo := (169067441 / 1000000000)) (hi := (84533721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5921 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5921 / 5000) = 1/(5000 / 5921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4744 : Bounds (169067441 / 1000000000) (84533721 / 500000000) (Real.log (5921 / 5000)) := by
  have h := reflection_log_4744_neg
  have he : Real.log (5921 / 5000) = -Real.log (5000 / 5921) := by
    rw [show ((5921 / 5000) : ℝ) = ((5000 / 5921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4745_neg : (50896513 / 250000000) ≤ -Real.log (4079 / 5000) ∧
    -Real.log (4079 / 5000) ≤ (203586053 / 1000000000) := by
  have h := checkLog_sound (w := (921 / 9079)) (n := 12)
    (lo := (50896513 / 250000000)) (hi := (203586053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4079) = 1/(4079 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4745 : Bounds (-203586053 / 1000000000) (-50896513 / 250000000) (Real.log (4079 / 5000)) := by
  have h := reflection_log_4745_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4746_neg : (184183 / 1000000000) ≤ -Real.log (5000000 / 5000921) ∧
    -Real.log (5000000 / 5000921) ≤ (23023 / 125000000) := by
  have h := checkLog_sound (w := (921 / 10000921)) (n := 12)
    (lo := (184183 / 1000000000)) (hi := (23023 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000921 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000921 / 5000000) = 1/(5000000 / 5000921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4746 : Bounds (184183 / 1000000000) (23023 / 125000000) (Real.log (5000921 / 5000000)) := by
  have h := reflection_log_4746_neg
  have he : Real.log (5000921 / 5000000) = -Real.log (5000000 / 5000921) := by
    rw [show ((5000921 / 5000000) : ℝ) = ((5000000 / 5000921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4747_neg : (23027 / 125000000) ≤ -Real.log (4999079 / 5000000) ∧
    -Real.log (4999079 / 5000000) ≤ (184217 / 1000000000) := by
  have h := checkLog_sound (w := (921 / 9999079)) (n := 12)
    (lo := (23027 / 125000000)) (hi := (184217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999079) = 1/(4999079 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4747 : Bounds (-184217 / 1000000000) (-23027 / 125000000) (Real.log (4999079 / 5000000)) := by
  have h := reflection_log_4747_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4748_neg : (44246223 / 500000000) ≤ -Real.log (500000 / 546263) ∧
    -Real.log (500000 / 546263) ≤ (88492447 / 1000000000) := by
  have h := checkLog_sound (w := (46263 / 1046263)) (n := 12)
    (lo := (44246223 / 500000000)) (hi := (88492447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546263 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546263 / 500000) = 1/(500000 / 546263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4748 : Bounds (44246223 / 500000000) (88492447 / 1000000000) (Real.log (546263 / 500000)) := by
  have h := reflection_log_4748_neg
  have he : Real.log (546263 / 500000) = -Real.log (500000 / 546263) := by
    rw [show ((546263 / 500000) : ℝ) = ((500000 / 546263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4749_neg : (97090363 / 1000000000) ≤ -Real.log (453737 / 500000) ∧
    -Real.log (453737 / 500000) ≤ (24272591 / 250000000) := by
  have h := checkLog_sound (w := (46263 / 953737)) (n := 12)
    (lo := (97090363 / 1000000000)) (hi := (24272591 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453737) = 1/(453737 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4749 : Bounds (-24272591 / 250000000) (-97090363 / 1000000000) (Real.log (453737 / 500000)) := by
  have h := reflection_log_4749_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4750_neg : (88707521 / 1000000000) ≤ -Real.log (1000000 / 1092761) ∧
    -Real.log (1000000 / 1092761) ≤ (44353761 / 500000000) := by
  have h := checkLog_sound (w := (92761 / 2092761)) (n := 12)
    (lo := (88707521 / 1000000000)) (hi := (44353761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092761 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1092761 / 1000000) = 1/(1000000 / 1092761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4750 : Bounds (88707521 / 1000000000) (44353761 / 500000000) (Real.log (1092761 / 1000000)) := by
  have h := reflection_log_4750_neg
  have he : Real.log (1092761 / 1000000) = -Real.log (1000000 / 1092761) := by
    rw [show ((1092761 / 1000000) : ℝ) = ((1000000 / 1092761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4751_neg : (97349357 / 1000000000) ≤ -Real.log (907239 / 1000000) ∧
    -Real.log (907239 / 1000000) ≤ (48674679 / 500000000) := by
  have h := checkLog_sound (w := (92761 / 1907239)) (n := 12)
    (lo := (97349357 / 1000000000)) (hi := (48674679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 907239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 907239) = 1/(907239 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4751 : Bounds (-48674679 / 500000000) (-97349357 / 1000000000) (Real.log (907239 / 1000000)) := by
  have h := reflection_log_4751_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4752_neg : (2160459 / 250000000) ≤ -Real.log (991395396879 / 1000000000000) ∧
    -Real.log (991395396879 / 1000000000000) ≤ (8641837 / 1000000000) := by
  have h := checkLog_sound (w := (8604603121 / 1991395396879)) (n := 12)
    (lo := (2160459 / 250000000)) (hi := (8641837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991395396879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991395396879) = 1/(991395396879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4752 : Bounds (-8641837 / 1000000000) (-2160459 / 250000000) (Real.log (991395396879 / 1000000000000)) := by
  have h := reflection_log_4752_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4753_neg : (8597917 / 1000000000) ≤ -Real.log (247859734831 / 250000000000) ∧
    -Real.log (247859734831 / 250000000000) ≤ (4298959 / 500000000) := by
  have h := checkLog_sound (w := (2140265169 / 497859734831)) (n := 12)
    (lo := (8597917 / 1000000000)) (hi := (4298959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247859734831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247859734831) = 1/(247859734831 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4753 : Bounds (-4298959 / 500000000) (-8597917 / 1000000000) (Real.log (247859734831 / 250000000000)) := by
  have h := reflection_log_4753_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4754_neg : (185582809 / 1000000000) ≤ -Real.log (500000000000 / 601959945959) ∧
    -Real.log (500000000000 / 601959945959) ≤ (18558281 / 100000000) := by
  have h := checkLog_sound (w := (101959945959 / 1101959945959)) (n := 12)
    (lo := (185582809 / 1000000000)) (hi := (18558281 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601959945959 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(601959945959 / 500000000000) = 1/(500000000000 / 601959945959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4754 : Bounds (185582809 / 1000000000) (18558281 / 100000000) (Real.log (601959945959 / 500000000000)) := by
  have h := reflection_log_4754_neg
  have he : Real.log (601959945959 / 500000000000) = -Real.log (500000000000 / 601959945959) := by
    rw [show ((601959945959 / 500000000000) : ℝ) = ((500000000000 / 601959945959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4755_neg : (93028439 / 500000000) ≤ -Real.log (62500000000 / 75280673009) ∧
    -Real.log (62500000000 / 75280673009) ≤ (186056879 / 1000000000) := by
  have h := checkLog_sound (w := (12780673009 / 137780673009)) (n := 12)
    (lo := (93028439 / 500000000)) (hi := (186056879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75280673009 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75280673009 / 62500000000) = 1/(62500000000 / 75280673009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4755 : Bounds (93028439 / 500000000) (186056879 / 1000000000) (Real.log (75280673009 / 62500000000)) := by
  have h := reflection_log_4755_neg
  have he : Real.log (75280673009 / 62500000000) = -Real.log (62500000000 / 75280673009) := by
    rw [show ((75280673009 / 62500000000) : ℝ) = ((62500000000 / 75280673009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4756_neg : (46555809 / 125000000) ≤ -Real.log (500000000000 / 725640397107) ∧
    -Real.log (500000000000 / 725640397107) ≤ (372446473 / 1000000000) := by
  have h := checkLog_sound (w := (225640397107 / 1225640397107)) (n := 12)
    (lo := (46555809 / 125000000)) (hi := (372446473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((725640397107 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(725640397107 / 500000000000) = 1/(500000000000 / 725640397107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4756 : Bounds (46555809 / 125000000) (372446473 / 1000000000) (Real.log (725640397107 / 500000000000)) := by
  have h := reflection_log_4756_neg
  have he : Real.log (725640397107 / 500000000000) = -Real.log (500000000000 / 725640397107) := by
    rw [show ((725640397107 / 500000000000) : ℝ) = ((500000000000 / 725640397107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4757_neg : (372653493 / 1000000000) ≤ -Real.log (6250000000 / 9072382937) ∧
    -Real.log (6250000000 / 9072382937) ≤ (186326747 / 500000000) := by
  have h := checkLog_sound (w := (2822382937 / 15322382937)) (n := 12)
    (lo := (372653493 / 1000000000)) (hi := (186326747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9072382937 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9072382937 / 6250000000) = 1/(6250000000 / 9072382937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4757 : Bounds (372653493 / 1000000000) (186326747 / 500000000) (Real.log (9072382937 / 6250000000)) := by
  have h := reflection_log_4757_neg
  have he : Real.log (9072382937 / 6250000000) = -Real.log (6250000000 / 9072382937) := by
    rw [show ((9072382937 / 6250000000) : ℝ) = ((6250000000 / 9072382937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4758_neg : (84575941 / 500000000) ≤ -Real.log (10000 / 11843) ∧
    -Real.log (10000 / 11843) ≤ (169151883 / 1000000000) := by
  have h := checkLog_sound (w := (1843 / 21843)) (n := 12)
    (lo := (84575941 / 500000000)) (hi := (169151883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11843 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11843 / 10000) = 1/(10000 / 11843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4758 : Bounds (84575941 / 500000000) (169151883 / 1000000000) (Real.log (11843 / 10000)) := by
  have h := reflection_log_4758_neg
  have he : Real.log (11843 / 10000) = -Real.log (10000 / 11843) := by
    rw [show ((11843 / 10000) : ℝ) = ((10000 / 11843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4759_neg : (101854319 / 500000000) ≤ -Real.log (8157 / 10000) ∧
    -Real.log (8157 / 10000) ≤ (203708639 / 1000000000) := by
  have h := checkLog_sound (w := (1843 / 18157)) (n := 12)
    (lo := (101854319 / 500000000)) (hi := (203708639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8157) = 1/(8157 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4759 : Bounds (-203708639 / 1000000000) (-101854319 / 500000000) (Real.log (8157 / 10000)) := by
  have h := reflection_log_4759_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4760_neg : (184283 / 1000000000) ≤ -Real.log (10000000 / 10001843) ∧
    -Real.log (10000000 / 10001843) ≤ (46071 / 250000000) := by
  have h := checkLog_sound (w := (1843 / 20001843)) (n := 12)
    (lo := (184283 / 1000000000)) (hi := (46071 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001843 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001843 / 10000000) = 1/(10000000 / 10001843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4760 : Bounds (184283 / 1000000000) (46071 / 250000000) (Real.log (10001843 / 10000000)) := by
  have h := reflection_log_4760_neg
  have he : Real.log (10001843 / 10000000) = -Real.log (10000000 / 10001843) := by
    rw [show ((10001843 / 10000000) : ℝ) = ((10000000 / 10001843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4761_neg : (46079 / 250000000) ≤ -Real.log (9998157 / 10000000) ∧
    -Real.log (9998157 / 10000000) ≤ (184317 / 1000000000) := by
  have h := checkLog_sound (w := (1843 / 19998157)) (n := 12)
    (lo := (46079 / 250000000)) (hi := (184317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998157) = 1/(9998157 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4761 : Bounds (-184317 / 1000000000) (-46079 / 250000000) (Real.log (9998157 / 10000000)) := by
  have h := reflection_log_4761_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4762_neg : (44269563 / 500000000) ≤ -Real.log (1000000 / 1092577) ∧
    -Real.log (1000000 / 1092577) ≤ (88539127 / 1000000000) := by
  have h := checkLog_sound (w := (92577 / 2092577)) (n := 12)
    (lo := (44269563 / 500000000)) (hi := (88539127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092577 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1092577 / 1000000) = 1/(1000000 / 1092577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4762 : Bounds (44269563 / 500000000) (88539127 / 1000000000) (Real.log (1092577 / 1000000)) := by
  have h := reflection_log_4762_neg
  have he : Real.log (1092577 / 1000000) = -Real.log (1000000 / 1092577) := by
    rw [show ((1092577 / 1000000) : ℝ) = ((1000000 / 1092577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4763_neg : (24286641 / 250000000) ≤ -Real.log (907423 / 1000000) ∧
    -Real.log (907423 / 1000000) ≤ (19429313 / 200000000) := by
  have h := checkLog_sound (w := (92577 / 1907423)) (n := 12)
    (lo := (24286641 / 250000000)) (hi := (19429313 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 907423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 907423) = 1/(907423 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4763 : Bounds (-19429313 / 200000000) (-24286641 / 250000000) (Real.log (907423 / 1000000)) := by
  have h := reflection_log_4763_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4764_neg : (8875419 / 100000000) ≤ -Real.log (250000 / 273203) ∧
    -Real.log (250000 / 273203) ≤ (88754191 / 1000000000) := by
  have h := checkLog_sound (w := (23203 / 523203)) (n := 12)
    (lo := (8875419 / 100000000)) (hi := (88754191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273203 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273203 / 250000) = 1/(250000 / 273203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4764 : Bounds (8875419 / 100000000) (88754191 / 1000000000) (Real.log (273203 / 250000)) := by
  have h := reflection_log_4764_neg
  have he : Real.log (273203 / 250000) = -Real.log (250000 / 273203) := by
    rw [show ((273203 / 250000) : ℝ) = ((250000 / 273203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4765_neg : (97405573 / 1000000000) ≤ -Real.log (226797 / 250000) ∧
    -Real.log (226797 / 250000) ≤ (48702787 / 500000000) := by
  have h := checkLog_sound (w := (23203 / 476797)) (n := 12)
    (lo := (97405573 / 1000000000)) (hi := (48702787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226797) = 1/(226797 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4765 : Bounds (-48702787 / 500000000) (-97405573 / 1000000000) (Real.log (226797 / 250000)) := by
  have h := reflection_log_4765_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4766_neg : (4325691 / 500000000) ≤ -Real.log (61961620791 / 62500000000) ∧
    -Real.log (61961620791 / 62500000000) ≤ (8651383 / 1000000000) := by
  have h := checkLog_sound (w := (538379209 / 124461620791)) (n := 12)
    (lo := (4325691 / 500000000)) (hi := (8651383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61961620791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61961620791) = 1/(61961620791 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4766 : Bounds (-8651383 / 1000000000) (-4325691 / 500000000) (Real.log (61961620791 / 62500000000)) := by
  have h := reflection_log_4766_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4767_neg : (4303719 / 500000000) ≤ -Real.log (991429499071 / 1000000000000) ∧
    -Real.log (991429499071 / 1000000000000) ≤ (8607439 / 1000000000) := by
  have h := checkLog_sound (w := (8570500929 / 1991429499071)) (n := 12)
    (lo := (4303719 / 500000000)) (hi := (8607439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991429499071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991429499071) = 1/(991429499071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4767 : Bounds (-8607439 / 1000000000) (-4303719 / 500000000) (Real.log (991429499071 / 1000000000000)) := by
  have h := reflection_log_4767_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4768_neg : (18568569 / 100000000) ≤ -Real.log (250000000000 / 301010939771) ∧
    -Real.log (250000000000 / 301010939771) ≤ (185685691 / 1000000000) := by
  have h := checkLog_sound (w := (51010939771 / 551010939771)) (n := 12)
    (lo := (18568569 / 100000000)) (hi := (185685691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301010939771 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301010939771 / 250000000000) = 1/(250000000000 / 301010939771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4768 : Bounds (18568569 / 100000000) (185685691 / 1000000000) (Real.log (301010939771 / 250000000000)) := by
  have h := reflection_log_4768_neg
  have he : Real.log (301010939771 / 250000000000) = -Real.log (250000000000 / 301010939771) := by
    rw [show ((301010939771 / 250000000000) : ℝ) = ((250000000000 / 301010939771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4769_neg : (46539941 / 250000000) ≤ -Real.log (100000000000 / 120461469949) ∧
    -Real.log (100000000000 / 120461469949) ≤ (37231953 / 200000000) := by
  have h := checkLog_sound (w := (20461469949 / 220461469949)) (n := 12)
    (lo := (46539941 / 250000000)) (hi := (37231953 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120461469949 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120461469949 / 100000000000) = 1/(100000000000 / 120461469949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4769 : Bounds (46539941 / 250000000) (37231953 / 200000000) (Real.log (120461469949 / 100000000000)) := by
  have h := reflection_log_4769_neg
  have he : Real.log (120461469949 / 100000000000) = -Real.log (100000000000 / 120461469949) := by
    rw [show ((120461469949 / 100000000000) : ℝ) = ((100000000000 / 120461469949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4770_neg : (372653493 / 1000000000) ≤ -Real.log (500000000000 / 725790634959) ∧
    -Real.log (500000000000 / 725790634959) ≤ (186326747 / 500000000) := by
  have h := checkLog_sound (w := (225790634959 / 1225790634959)) (n := 12)
    (lo := (372653493 / 1000000000)) (hi := (186326747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((725790634959 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(725790634959 / 500000000000) = 1/(500000000000 / 725790634959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4770 : Bounds (372653493 / 1000000000) (186326747 / 500000000) (Real.log (725790634959 / 500000000000)) := by
  have h := reflection_log_4770_neg
  have he : Real.log (725790634959 / 500000000000) = -Real.log (500000000000 / 725790634959) := by
    rw [show ((725790634959 / 500000000000) : ℝ) = ((500000000000 / 725790634959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4771_neg : (372860521 / 1000000000) ≤ -Real.log (500000000000 / 725940909649) ∧
    -Real.log (500000000000 / 725940909649) ≤ (186430261 / 500000000) := by
  have h := checkLog_sound (w := (225940909649 / 1225940909649)) (n := 12)
    (lo := (372860521 / 1000000000)) (hi := (186430261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((725940909649 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(725940909649 / 500000000000) = 1/(500000000000 / 725940909649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4771 : Bounds (372860521 / 1000000000) (186430261 / 500000000) (Real.log (725940909649 / 500000000000)) := by
  have h := reflection_log_4771_neg
  have he : Real.log (725940909649 / 500000000000) = -Real.log (500000000000 / 725940909649) := by
    rw [show ((725940909649 / 500000000000) : ℝ) = ((500000000000 / 725940909649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4772_neg : (169236317 / 1000000000) ≤ -Real.log (2500 / 2961) ∧
    -Real.log (2500 / 2961) ≤ (84618159 / 500000000) := by
  have h := checkLog_sound (w := (461 / 5461)) (n := 12)
    (lo := (169236317 / 1000000000)) (hi := (84618159 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2961 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2961 / 2500) = 1/(2500 / 2961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4772 : Bounds (169236317 / 1000000000) (84618159 / 500000000) (Real.log (2961 / 2500)) := by
  have h := reflection_log_4772_neg
  have he : Real.log (2961 / 2500) = -Real.log (2500 / 2961) := by
    rw [show ((2961 / 2500) : ℝ) = ((2500 / 2961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4773_neg : (5095781 / 25000000) ≤ -Real.log (2039 / 2500) ∧
    -Real.log (2039 / 2500) ≤ (203831241 / 1000000000) := by
  have h := checkLog_sound (w := (461 / 4539)) (n := 12)
    (lo := (5095781 / 25000000)) (hi := (203831241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2039) = 1/(2039 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4773 : Bounds (-203831241 / 1000000000) (-5095781 / 25000000) (Real.log (2039 / 2500)) := by
  have h := reflection_log_4773_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4774_neg : (184383 / 1000000000) ≤ -Real.log (2500000 / 2500461) ∧
    -Real.log (2500000 / 2500461) ≤ (2881 / 15625000) := by
  have h := checkLog_sound (w := (461 / 5000461)) (n := 12)
    (lo := (184383 / 1000000000)) (hi := (2881 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500461 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500461 / 2500000) = 1/(2500000 / 2500461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4774 : Bounds (184383 / 1000000000) (2881 / 15625000) (Real.log (2500461 / 2500000)) := by
  have h := reflection_log_4774_neg
  have he : Real.log (2500461 / 2500000) = -Real.log (2500000 / 2500461) := by
    rw [show ((2500461 / 2500000) : ℝ) = ((2500000 / 2500461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4775_neg : (184417 / 1000000000) ≤ -Real.log (2499539 / 2500000) ∧
    -Real.log (2499539 / 2500000) ≤ (92209 / 500000000) := by
  have h := checkLog_sound (w := (461 / 4999539)) (n := 12)
    (lo := (184417 / 1000000000)) (hi := (92209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499539) = 1/(2499539 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4775 : Bounds (-92209 / 500000000) (-184417 / 1000000000) (Real.log (2499539 / 2500000)) := by
  have h := reflection_log_4775_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4776_neg : (88585803 / 1000000000) ≤ -Real.log (250000 / 273157) ∧
    -Real.log (250000 / 273157) ≤ (22146451 / 250000000) := by
  have h := checkLog_sound (w := (23157 / 523157)) (n := 12)
    (lo := (88585803 / 1000000000)) (hi := (22146451 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273157 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273157 / 250000) = 1/(250000 / 273157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4776 : Bounds (88585803 / 1000000000) (22146451 / 250000000) (Real.log (273157 / 250000)) := by
  have h := reflection_log_4776_neg
  have he : Real.log (273157 / 250000) = -Real.log (250000 / 273157) := by
    rw [show ((273157 / 250000) : ℝ) = ((250000 / 273157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4777_neg : (97202769 / 1000000000) ≤ -Real.log (226843 / 250000) ∧
    -Real.log (226843 / 250000) ≤ (9720277 / 100000000) := by
  have h := checkLog_sound (w := (23157 / 476843)) (n := 12)
    (lo := (97202769 / 1000000000)) (hi := (9720277 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226843) = 1/(226843 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4777 : Bounds (-9720277 / 100000000) (-97202769 / 1000000000) (Real.log (226843 / 250000)) := by
  have h := reflection_log_4777_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4778_neg : (44400429 / 500000000) ≤ -Real.log (1000000 / 1092863) ∧
    -Real.log (1000000 / 1092863) ≤ (88800859 / 1000000000) := by
  have h := checkLog_sound (w := (92863 / 2092863)) (n := 12)
    (lo := (44400429 / 500000000)) (hi := (88800859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1092863 / 1000000) = 1/(1000000 / 1092863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4778 : Bounds (44400429 / 500000000) (88800859 / 1000000000) (Real.log (1092863 / 1000000)) := by
  have h := reflection_log_4778_neg
  have he : Real.log (1092863 / 1000000) = -Real.log (1000000 / 1092863) := by
    rw [show ((1092863 / 1000000) : ℝ) = ((1000000 / 1092863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4779_neg : (3045681 / 31250000) ≤ -Real.log (907137 / 1000000) ∧
    -Real.log (907137 / 1000000) ≤ (97461793 / 1000000000) := by
  have h := checkLog_sound (w := (92863 / 1907137)) (n := 12)
    (lo := (3045681 / 31250000)) (hi := (97461793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 907137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 907137) = 1/(907137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4779 : Bounds (-97461793 / 1000000000) (-3045681 / 31250000) (Real.log (907137 / 1000000)) := by
  have h := reflection_log_4779_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4780_neg : (4330467 / 500000000) ≤ -Real.log (991376463231 / 1000000000000) ∧
    -Real.log (991376463231 / 1000000000000) ≤ (1732187 / 200000000) := by
  have h := checkLog_sound (w := (8623536769 / 1991376463231)) (n := 12)
    (lo := (4330467 / 500000000)) (hi := (1732187 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991376463231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991376463231) = 1/(991376463231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4780 : Bounds (-1732187 / 200000000) (-4330467 / 500000000) (Real.log (991376463231 / 1000000000000)) := by
  have h := reflection_log_4780_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4781_neg : (4308483 / 500000000) ≤ -Real.log (61963753351 / 62500000000) ∧
    -Real.log (61963753351 / 62500000000) ≤ (8616967 / 1000000000) := by
  have h := checkLog_sound (w := (536246649 / 124463753351)) (n := 12)
    (lo := (4308483 / 500000000)) (hi := (8616967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61963753351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61963753351) = 1/(61963753351 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4781 : Bounds (-8616967 / 1000000000) (-4308483 / 500000000) (Real.log (61963753351 / 62500000000)) := by
  have h := reflection_log_4781_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4782_neg : (185788573 / 1000000000) ≤ -Real.log (500000000000 / 602083820087) ∧
    -Real.log (500000000000 / 602083820087) ≤ (92894287 / 500000000) := by
  have h := checkLog_sound (w := (102083820087 / 1102083820087)) (n := 12)
    (lo := (185788573 / 1000000000)) (hi := (92894287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602083820087 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602083820087 / 500000000000) = 1/(500000000000 / 602083820087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4782 : Bounds (185788573 / 1000000000) (92894287 / 500000000) (Real.log (602083820087 / 500000000000)) := by
  have h := reflection_log_4782_neg
  have he : Real.log (602083820087 / 500000000000) = -Real.log (500000000000 / 602083820087) := by
    rw [show ((602083820087 / 500000000000) : ℝ) = ((500000000000 / 602083820087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4783_neg : (186262651 / 1000000000) ≤ -Real.log (100000000000 / 120473864477) ∧
    -Real.log (100000000000 / 120473864477) ≤ (46565663 / 250000000) := by
  have h := checkLog_sound (w := (20473864477 / 220473864477)) (n := 12)
    (lo := (186262651 / 1000000000)) (hi := (46565663 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120473864477 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120473864477 / 100000000000) = 1/(100000000000 / 120473864477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4783 : Bounds (186262651 / 1000000000) (46565663 / 250000000) (Real.log (120473864477 / 100000000000)) := by
  have h := reflection_log_4783_neg
  have he : Real.log (120473864477 / 100000000000) = -Real.log (100000000000 / 120473864477) := by
    rw [show ((120473864477 / 100000000000) : ℝ) = ((100000000000 / 120473864477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4784_neg : (372860521 / 1000000000) ≤ -Real.log (31250000000 / 45371306853) ∧
    -Real.log (31250000000 / 45371306853) ≤ (186430261 / 500000000) := by
  have h := checkLog_sound (w := (14121306853 / 76621306853)) (n := 12)
    (lo := (372860521 / 1000000000)) (hi := (186430261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45371306853 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45371306853 / 31250000000) = 1/(31250000000 / 45371306853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4784 : Bounds (372860521 / 1000000000) (186430261 / 500000000) (Real.log (45371306853 / 31250000000)) := by
  have h := reflection_log_4784_neg
  have he : Real.log (45371306853 / 31250000000) = -Real.log (31250000000 / 45371306853) := by
    rw [show ((45371306853 / 31250000000) : ℝ) = ((31250000000 / 45371306853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4785_neg : (373067557 / 1000000000) ≤ -Real.log (500000000000 / 726091221187) ∧
    -Real.log (500000000000 / 726091221187) ≤ (186533779 / 500000000) := by
  have h := checkLog_sound (w := (226091221187 / 1226091221187)) (n := 12)
    (lo := (373067557 / 1000000000)) (hi := (186533779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((726091221187 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(726091221187 / 500000000000) = 1/(500000000000 / 726091221187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4785 : Bounds (373067557 / 1000000000) (186533779 / 500000000) (Real.log (726091221187 / 500000000000)) := by
  have h := reflection_log_4785_neg
  have he : Real.log (726091221187 / 500000000000) = -Real.log (500000000000 / 726091221187) := by
    rw [show ((726091221187 / 500000000000) : ℝ) = ((500000000000 / 726091221187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4786_neg : (21165093 / 125000000) ≤ -Real.log (2000 / 2369) ∧
    -Real.log (2000 / 2369) ≤ (33864149 / 200000000) := by
  have h := checkLog_sound (w := (369 / 4369)) (n := 12)
    (lo := (21165093 / 125000000)) (hi := (33864149 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2369 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2369 / 2000) = 1/(2000 / 2369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4786 : Bounds (21165093 / 125000000) (33864149 / 200000000) (Real.log (2369 / 2000)) := by
  have h := reflection_log_4786_neg
  have he : Real.log (2369 / 2000) = -Real.log (2000 / 2369) := by
    rw [show ((2369 / 2000) : ℝ) = ((2000 / 2369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4787_neg : (3186779 / 15625000) ≤ -Real.log (1631 / 2000) ∧
    -Real.log (1631 / 2000) ≤ (203953857 / 1000000000) := by
  have h := checkLog_sound (w := (369 / 3631)) (n := 12)
    (lo := (3186779 / 15625000)) (hi := (203953857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1631) = 1/(1631 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4787 : Bounds (-203953857 / 1000000000) (-3186779 / 15625000) (Real.log (1631 / 2000)) := by
  have h := reflection_log_4787_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4788_neg : (92241 / 500000000) ≤ -Real.log (2000000 / 2000369) ∧
    -Real.log (2000000 / 2000369) ≤ (184483 / 1000000000) := by
  have h := checkLog_sound (w := (369 / 4000369)) (n := 12)
    (lo := (92241 / 500000000)) (hi := (184483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000369 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000369 / 2000000) = 1/(2000000 / 2000369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4788 : Bounds (92241 / 500000000) (184483 / 1000000000) (Real.log (2000369 / 2000000)) := by
  have h := reflection_log_4788_neg
  have he : Real.log (2000369 / 2000000) = -Real.log (2000000 / 2000369) := by
    rw [show ((2000369 / 2000000) : ℝ) = ((2000000 / 2000369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4789_neg : (184517 / 1000000000) ≤ -Real.log (1999631 / 2000000) ∧
    -Real.log (1999631 / 2000000) ≤ (92259 / 500000000) := by
  have h := checkLog_sound (w := (369 / 3999631)) (n := 12)
    (lo := (184517 / 1000000000)) (hi := (92259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999631) = 1/(1999631 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4789 : Bounds (-92259 / 500000000) (-184517 / 1000000000) (Real.log (1999631 / 2000000)) := by
  have h := reflection_log_4789_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4790_neg : (44316239 / 500000000) ≤ -Real.log (1000000 / 1092679) ∧
    -Real.log (1000000 / 1092679) ≤ (88632479 / 1000000000) := by
  have h := checkLog_sound (w := (92679 / 2092679)) (n := 12)
    (lo := (44316239 / 500000000)) (hi := (88632479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092679 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1092679 / 1000000) = 1/(1000000 / 1092679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4790 : Bounds (44316239 / 500000000) (88632479 / 1000000000) (Real.log (1092679 / 1000000)) := by
  have h := reflection_log_4790_neg
  have he : Real.log (1092679 / 1000000) = -Real.log (1000000 / 1092679) := by
    rw [show ((1092679 / 1000000) : ℝ) = ((1000000 / 1092679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4791_neg : (97258977 / 1000000000) ≤ -Real.log (907321 / 1000000) ∧
    -Real.log (907321 / 1000000) ≤ (48629489 / 500000000) := by
  have h := checkLog_sound (w := (92679 / 1907321)) (n := 12)
    (lo := (97258977 / 1000000000)) (hi := (48629489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 907321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 907321) = 1/(907321 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4791 : Bounds (-48629489 / 500000000) (-97258977 / 1000000000) (Real.log (907321 / 1000000)) := by
  have h := reflection_log_4791_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4792_neg : (88847523 / 1000000000) ≤ -Real.log (500000 / 546457) ∧
    -Real.log (500000 / 546457) ≤ (22211881 / 250000000) := by
  have h := checkLog_sound (w := (46457 / 1046457)) (n := 12)
    (lo := (88847523 / 1000000000)) (hi := (22211881 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546457 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546457 / 500000) = 1/(500000 / 546457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4792 : Bounds (88847523 / 1000000000) (22211881 / 250000000) (Real.log (546457 / 500000)) := by
  have h := reflection_log_4792_neg
  have he : Real.log (546457 / 500000) = -Real.log (500000 / 546457) := by
    rw [show ((546457 / 500000) : ℝ) = ((500000 / 546457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4793_neg : (19503603 / 200000000) ≤ -Real.log (453543 / 500000) ∧
    -Real.log (453543 / 500000) ≤ (1523719 / 15625000) := by
  have h := checkLog_sound (w := (46457 / 953543)) (n := 12)
    (lo := (19503603 / 200000000)) (hi := (1523719 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453543) = 1/(453543 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4793 : Bounds (-1523719 / 15625000) (-19503603 / 200000000) (Real.log (453543 / 500000)) := by
  have h := reflection_log_4793_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4794_neg : (8670491 / 1000000000) ≤ -Real.log (247841747151 / 250000000000) ∧
    -Real.log (247841747151 / 250000000000) ≤ (2167623 / 250000000) := by
  have h := checkLog_sound (w := (2158252849 / 497841747151)) (n := 12)
    (lo := (8670491 / 1000000000)) (hi := (2167623 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247841747151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247841747151) = 1/(247841747151 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4794 : Bounds (-2167623 / 250000000) (-8670491 / 1000000000) (Real.log (247841747151 / 250000000000)) := by
  have h := reflection_log_4794_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4795_neg : (4313249 / 500000000) ≤ -Real.log (991410602959 / 1000000000000) ∧
    -Real.log (991410602959 / 1000000000000) ≤ (8626499 / 1000000000) := by
  have h := checkLog_sound (w := (8589397041 / 1991410602959)) (n := 12)
    (lo := (4313249 / 500000000)) (hi := (8626499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991410602959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991410602959) = 1/(991410602959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4795 : Bounds (-8626499 / 1000000000) (-4313249 / 500000000) (Real.log (991410602959 / 1000000000000)) := by
  have h := reflection_log_4795_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4796_neg : (1452277 / 7812500) ≤ -Real.log (250000000000 / 301072883797) ∧
    -Real.log (250000000000 / 301072883797) ≤ (185891457 / 1000000000) := by
  have h := checkLog_sound (w := (51072883797 / 551072883797)) (n := 12)
    (lo := (1452277 / 7812500)) (hi := (185891457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301072883797 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301072883797 / 250000000000) = 1/(250000000000 / 301072883797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4796 : Bounds (1452277 / 7812500) (185891457 / 1000000000) (Real.log (301072883797 / 250000000000)) := by
  have h := reflection_log_4796_neg
  have he : Real.log (301072883797 / 250000000000) = -Real.log (250000000000 / 301072883797) := by
    rw [show ((301072883797 / 250000000000) : ℝ) = ((250000000000 / 301072883797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4797_neg : (93182769 / 500000000) ≤ -Real.log (250000000000 / 301215650997) ∧
    -Real.log (250000000000 / 301215650997) ≤ (186365539 / 1000000000) := by
  have h := checkLog_sound (w := (51215650997 / 551215650997)) (n := 12)
    (lo := (93182769 / 500000000)) (hi := (186365539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301215650997 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301215650997 / 250000000000) = 1/(250000000000 / 301215650997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4797 : Bounds (93182769 / 500000000) (186365539 / 1000000000) (Real.log (301215650997 / 250000000000)) := by
  have h := reflection_log_4797_neg
  have he : Real.log (301215650997 / 250000000000) = -Real.log (250000000000 / 301215650997) := by
    rw [show ((301215650997 / 250000000000) : ℝ) = ((250000000000 / 301215650997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4798_neg : (373067557 / 1000000000) ≤ -Real.log (250000000000 / 363045610593) ∧
    -Real.log (250000000000 / 363045610593) ≤ (186533779 / 500000000) := by
  have h := checkLog_sound (w := (113045610593 / 613045610593)) (n := 12)
    (lo := (373067557 / 1000000000)) (hi := (186533779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363045610593 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363045610593 / 250000000000) = 1/(250000000000 / 363045610593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4798 : Bounds (373067557 / 1000000000) (186533779 / 500000000) (Real.log (363045610593 / 250000000000)) := by
  have h := reflection_log_4798_neg
  have he : Real.log (363045610593 / 250000000000) = -Real.log (250000000000 / 363045610593) := by
    rw [show ((363045610593 / 250000000000) : ℝ) = ((250000000000 / 363045610593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4799_neg : (373274601 / 1000000000) ≤ -Real.log (50000000000 / 72624156959) ∧
    -Real.log (50000000000 / 72624156959) ≤ (186637301 / 500000000) := by
  have h := checkLog_sound (w := (22624156959 / 122624156959)) (n := 12)
    (lo := (373274601 / 1000000000)) (hi := (186637301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72624156959 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72624156959 / 50000000000) = 1/(50000000000 / 72624156959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4799 : Bounds (373274601 / 1000000000) (186637301 / 500000000) (Real.log (72624156959 / 50000000000)) := by
  have h := reflection_log_4799_neg
  have he : Real.log (72624156959 / 50000000000) = -Real.log (50000000000 / 72624156959) := by
    rw [show ((72624156959 / 50000000000) : ℝ) = ((50000000000 / 72624156959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


