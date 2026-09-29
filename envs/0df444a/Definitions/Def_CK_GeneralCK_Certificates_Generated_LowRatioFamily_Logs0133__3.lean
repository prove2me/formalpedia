-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0133__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0133__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T21:29:47.889876+00:00
-- url     : https://prove2.me/theorems/e9a61779-fc47-4ae4-9f34-5aee79ade67a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0133 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0134, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0133 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0134, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0135)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0133 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0134, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0135)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0133 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0134, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0135) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0133 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0134, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0135).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0133 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8512_neg : (63883 / 250000000) ≤ -Real.log (1999489 / 2000000) ∧
    -Real.log (1999489 / 2000000) ≤ (255533 / 1000000000) := by
  have h := checkLog_sound (w := (511 / 3999489)) (n := 12)
    (lo := (63883 / 250000000)) (hi := (255533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999489) = 1/(1999489 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8512 : Bounds (-255533 / 1000000000) (-63883 / 250000000) (Real.log (1999489 / 2000000)) := by
  have h := reflection_log_8512_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8513_neg : (24248387 / 200000000) ≤ -Real.log (500000 / 564449) ∧
    -Real.log (500000 / 564449) ≤ (7577621 / 62500000) := by
  have h := checkLog_sound (w := (64449 / 1064449)) (n := 12)
    (lo := (24248387 / 200000000)) (hi := (7577621 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((564449 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(564449 / 500000) = 1/(500000 / 564449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8513 : Bounds (24248387 / 200000000) (7577621 / 62500000) (Real.log (564449 / 500000)) := by
  have h := reflection_log_8513_neg
  have he : Real.log (564449 / 500000) = -Real.log (500000 / 564449) := by
    rw [show ((564449 / 500000) : ℝ) = ((500000 / 564449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8514_neg : (68998101 / 500000000) ≤ -Real.log (435551 / 500000) ∧
    -Real.log (435551 / 500000) ≤ (137996203 / 1000000000) := by
  have h := checkLog_sound (w := (64449 / 935551)) (n := 12)
    (lo := (68998101 / 500000000)) (hi := (137996203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 435551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 435551) = 1/(435551 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8514 : Bounds (-137996203 / 1000000000) (-68998101 / 500000000) (Real.log (435551 / 500000)) := by
  have h := reflection_log_8514_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8515_neg : (30423843 / 250000000) ≤ -Real.log (100000 / 112941) ∧
    -Real.log (100000 / 112941) ≤ (121695373 / 1000000000) := by
  have h := checkLog_sound (w := (12941 / 212941)) (n := 12)
    (lo := (30423843 / 250000000)) (hi := (121695373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((112941 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(112941 / 100000) = 1/(100000 / 112941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8515 : Bounds (30423843 / 250000000) (121695373 / 1000000000) (Real.log (112941 / 100000)) := by
  have h := reflection_log_8515_neg
  have he : Real.log (112941 / 100000) = -Real.log (100000 / 112941) := by
    rw [show ((112941 / 100000) : ℝ) = ((100000 / 112941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8516_neg : (17323017 / 125000000) ≤ -Real.log (87059 / 100000) ∧
    -Real.log (87059 / 100000) ≤ (138584137 / 1000000000) := by
  have h := checkLog_sound (w := (12941 / 187059)) (n := 12)
    (lo := (17323017 / 125000000)) (hi := (138584137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 87059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 87059) = 1/(87059 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8516 : Bounds (-138584137 / 1000000000) (-17323017 / 125000000) (Real.log (87059 / 100000)) := by
  have h := reflection_log_8516_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8517_neg : (16888763 / 1000000000) ≤ -Real.log (9832530519 / 10000000000) ∧
    -Real.log (9832530519 / 10000000000) ≤ (4222191 / 250000000) := by
  have h := checkLog_sound (w := (167469481 / 19832530519)) (n := 12)
    (lo := (16888763 / 1000000000)) (hi := (4222191 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9832530519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9832530519) = 1/(9832530519 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8517 : Bounds (-4222191 / 250000000) (-16888763 / 1000000000) (Real.log (9832530519 / 10000000000)) := by
  have h := reflection_log_8517_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8518_neg : (8377133 / 500000000) ≤ -Real.log (245846326399 / 250000000000) ∧
    -Real.log (245846326399 / 250000000000) ≤ (16754267 / 1000000000) := by
  have h := checkLog_sound (w := (4153673601 / 495846326399)) (n := 12)
    (lo := (8377133 / 500000000)) (hi := (16754267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245846326399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245846326399) = 1/(245846326399 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8518 : Bounds (-16754267 / 1000000000) (-8377133 / 500000000) (Real.log (245846326399 / 250000000000)) := by
  have h := reflection_log_8518_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8519_neg : (259238137 / 1000000000) ≤ -Real.log (100000000000 / 129594238103) ∧
    -Real.log (100000000000 / 129594238103) ≤ (129619069 / 500000000) := by
  have h := checkLog_sound (w := (29594238103 / 229594238103)) (n := 12)
    (lo := (259238137 / 1000000000)) (hi := (129619069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((129594238103 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(129594238103 / 100000000000) = 1/(100000000000 / 129594238103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8519 : Bounds (259238137 / 1000000000) (129619069 / 500000000) (Real.log (129594238103 / 100000000000)) := by
  have h := reflection_log_8519_neg
  have he : Real.log (129594238103 / 100000000000) = -Real.log (100000000000 / 129594238103) := by
    rw [show ((129594238103 / 100000000000) : ℝ) = ((100000000000 / 129594238103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8520_neg : (65069877 / 250000000) ≤ -Real.log (62500000000 / 81080790039) ∧
    -Real.log (62500000000 / 81080790039) ≤ (260279509 / 1000000000) := by
  have h := checkLog_sound (w := (18580790039 / 143580790039)) (n := 12)
    (lo := (65069877 / 250000000)) (hi := (260279509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81080790039 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81080790039 / 62500000000) = 1/(62500000000 / 81080790039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8520 : Bounds (65069877 / 250000000) (260279509 / 1000000000) (Real.log (81080790039 / 62500000000)) := by
  have h := reflection_log_8520_neg
  have he : Real.log (81080790039 / 62500000000) = -Real.log (62500000000 / 81080790039) := by
    rw [show ((81080790039 / 62500000000) : ℝ) = ((62500000000 / 81080790039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8521_neg : (521506633 / 1000000000) ≤ -Real.log (250000000000 / 421140939597) ∧
    -Real.log (250000000000 / 421140939597) ≤ (260753317 / 500000000) := by
  have h := checkLog_sound (w := (171140939597 / 671140939597)) (n := 12)
    (lo := (521506633 / 1000000000)) (hi := (260753317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((421140939597 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(421140939597 / 250000000000) = 1/(250000000000 / 421140939597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8521 : Bounds (521506633 / 1000000000) (260753317 / 500000000) (Real.log (421140939597 / 250000000000)) := by
  have h := reflection_log_8521_neg
  have he : Real.log (421140939597 / 250000000000) = -Real.log (250000000000 / 421140939597) := by
    rw [show ((421140939597 / 250000000000) : ℝ) = ((250000000000 / 421140939597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8522_neg : (261288163 / 500000000) ≤ -Real.log (500000000000 / 843183344527) ∧
    -Real.log (500000000000 / 843183344527) ≤ (522576327 / 1000000000) := by
  have h := checkLog_sound (w := (343183344527 / 1343183344527)) (n := 12)
    (lo := (261288163 / 500000000)) (hi := (522576327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((843183344527 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(843183344527 / 500000000000) = 1/(500000000000 / 843183344527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8522 : Bounds (261288163 / 500000000) (522576327 / 1000000000) (Real.log (843183344527 / 500000000000)) := by
  have h := reflection_log_8522_neg
  have he : Real.log (843183344527 / 500000000000) = -Real.log (500000000000 / 843183344527) := by
    rw [show ((843183344527 / 500000000000) : ℝ) = ((500000000000 / 843183344527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8523_neg : (56983017 / 250000000) ≤ -Real.log (125 / 157) ∧
    -Real.log (125 / 157) ≤ (227932069 / 1000000000) := by
  have h := checkLog_sound (w := (16 / 141)) (n := 12)
    (lo := (56983017 / 250000000)) (hi := (227932069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157 / 125) = 1/(125 / 157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8523 : Bounds (56983017 / 250000000) (227932069 / 1000000000) (Real.log (157 / 125)) := by
  have h := reflection_log_8523_neg
  have he : Real.log (157 / 125) = -Real.log (125 / 157) := by
    rw [show ((157 / 125) : ℝ) = ((125 / 157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8524_neg : (73928561 / 250000000) ≤ -Real.log (93 / 125) ∧
    -Real.log (93 / 125) ≤ (59142849 / 200000000) := by
  have h := checkLog_sound (w := (16 / 109)) (n := 12)
    (lo := (73928561 / 250000000)) (hi := (59142849 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 93) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 93) = 1/(93 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8524 : Bounds (-59142849 / 200000000) (-73928561 / 250000000) (Real.log (93 / 125)) := by
  have h := reflection_log_8524_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8525_neg : (255967 / 1000000000) ≤ -Real.log (15625 / 15629) ∧
    -Real.log (15625 / 15629) ≤ (7999 / 31250000) := by
  have h := checkLog_sound (w := (2 / 15627)) (n := 12)
    (lo := (255967 / 1000000000)) (hi := (7999 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15629 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15629 / 15625) = 1/(15625 / 15629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8525 : Bounds (255967 / 1000000000) (7999 / 31250000) (Real.log (15629 / 15625)) := by
  have h := reflection_log_8525_neg
  have he : Real.log (15629 / 15625) = -Real.log (15625 / 15629) := by
    rw [show ((15629 / 15625) : ℝ) = ((15625 / 15629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8526_neg : (8001 / 31250000) ≤ -Real.log (15621 / 15625) ∧
    -Real.log (15621 / 15625) ≤ (256033 / 1000000000) := by
  have h := checkLog_sound (w := (2 / 15623)) (n := 12)
    (lo := (8001 / 31250000)) (hi := (256033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 15621) = 1/(15621 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8526 : Bounds (-256033 / 1000000000) (-8001 / 31250000) (Real.log (15621 / 15625)) := by
  have h := reflection_log_8526_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8527_neg : (15183917 / 125000000) ≤ -Real.log (1000000 / 1129157) ∧
    -Real.log (1000000 / 1129157) ≤ (121471337 / 1000000000) := by
  have h := checkLog_sound (w := (129157 / 2129157)) (n := 12)
    (lo := (15183917 / 125000000)) (hi := (121471337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1129157 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1129157 / 1000000) = 1/(1000000 / 1129157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8527 : Bounds (15183917 / 125000000) (121471337 / 1000000000) (Real.log (1129157 / 1000000)) := by
  have h := reflection_log_8527_neg
  have he : Real.log (1129157 / 1000000) = -Real.log (1000000 / 1129157) := by
    rw [show ((1129157 / 1000000) : ℝ) = ((1000000 / 1129157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8528_neg : (13829357 / 100000000) ≤ -Real.log (870843 / 1000000) ∧
    -Real.log (870843 / 1000000) ≤ (138293571 / 1000000000) := by
  have h := checkLog_sound (w := (129157 / 1870843)) (n := 12)
    (lo := (13829357 / 100000000)) (hi := (138293571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 870843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 870843) = 1/(870843 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8528 : Bounds (-138293571 / 1000000000) (-13829357 / 100000000) (Real.log (870843 / 1000000)) := by
  have h := reflection_log_8528_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8529_neg : (121924669 / 1000000000) ≤ -Real.log (1000000 / 1129669) ∧
    -Real.log (1000000 / 1129669) ≤ (12192467 / 100000000) := by
  have h := checkLog_sound (w := (129669 / 2129669)) (n := 12)
    (lo := (121924669 / 1000000000)) (hi := (12192467 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1129669 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1129669 / 1000000) = 1/(1000000 / 1129669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8529 : Bounds (121924669 / 1000000000) (12192467 / 100000000) (Real.log (1129669 / 1000000)) := by
  have h := reflection_log_8529_neg
  have he : Real.log (1129669 / 1000000) = -Real.log (1000000 / 1129669) := by
    rw [show ((1129669 / 1000000) : ℝ) = ((1000000 / 1129669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8530_neg : (138881679 / 1000000000) ≤ -Real.log (870331 / 1000000) ∧
    -Real.log (870331 / 1000000) ≤ (1736021 / 12500000) := by
  have h := checkLog_sound (w := (129669 / 1870331)) (n := 12)
    (lo := (138881679 / 1000000000)) (hi := (1736021 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 870331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 870331) = 1/(870331 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8530 : Bounds (-1736021 / 12500000) (-138881679 / 1000000000) (Real.log (870331 / 1000000)) := by
  have h := reflection_log_8530_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8531_neg : (1695701 / 100000000) ≤ -Real.log (983185950439 / 1000000000000) ∧
    -Real.log (983185950439 / 1000000000000) ≤ (16957011 / 1000000000) := by
  have h := checkLog_sound (w := (16814049561 / 1983185950439)) (n := 12)
    (lo := (1695701 / 100000000)) (hi := (16957011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983185950439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983185950439) = 1/(983185950439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8531 : Bounds (-16957011 / 1000000000) (-1695701 / 100000000) (Real.log (983185950439 / 1000000000000)) := by
  have h := reflection_log_8531_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8532_neg : (8411117 / 500000000) ≤ -Real.log (983318469351 / 1000000000000) ∧
    -Real.log (983318469351 / 1000000000000) ≤ (3364447 / 200000000) := by
  have h := checkLog_sound (w := (16681530649 / 1983318469351)) (n := 12)
    (lo := (8411117 / 500000000)) (hi := (3364447 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983318469351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983318469351) = 1/(983318469351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8532 : Bounds (-3364447 / 200000000) (-8411117 / 500000000) (Real.log (983318469351 / 1000000000000)) := by
  have h := reflection_log_8532_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8533_neg : (259764907 / 1000000000) ≤ -Real.log (7812500000 / 10129884563) ∧
    -Real.log (7812500000 / 10129884563) ≤ (64941227 / 250000000) := by
  have h := checkLog_sound (w := (2317384563 / 17942384563)) (n := 12)
    (lo := (259764907 / 1000000000)) (hi := (64941227 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10129884563 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10129884563 / 7812500000) = 1/(7812500000 / 10129884563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8533 : Bounds (259764907 / 1000000000) (64941227 / 250000000) (Real.log (10129884563 / 7812500000)) := by
  have h := reflection_log_8533_neg
  have he : Real.log (10129884563 / 7812500000) = -Real.log (7812500000 / 10129884563) := by
    rw [show ((10129884563 / 7812500000) : ℝ) = ((7812500000 / 10129884563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8534_neg : (260806349 / 1000000000) ≤ -Real.log (62500000000 / 81123517949) ∧
    -Real.log (62500000000 / 81123517949) ≤ (5216127 / 20000000) := by
  have h := checkLog_sound (w := (18623517949 / 143623517949)) (n := 12)
    (lo := (260806349 / 1000000000)) (hi := (5216127 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81123517949 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81123517949 / 62500000000) = 1/(62500000000 / 81123517949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8534 : Bounds (260806349 / 1000000000) (5216127 / 20000000) (Real.log (81123517949 / 62500000000)) := by
  have h := reflection_log_8534_neg
  have he : Real.log (81123517949 / 62500000000) = -Real.log (62500000000 / 81123517949) := by
    rw [show ((81123517949 / 62500000000) : ℝ) = ((62500000000 / 81123517949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8535_neg : (261288163 / 500000000) ≤ -Real.log (250000000000 / 421591672263) ∧
    -Real.log (250000000000 / 421591672263) ≤ (522576327 / 1000000000) := by
  have h := checkLog_sound (w := (171591672263 / 671591672263)) (n := 12)
    (lo := (261288163 / 500000000)) (hi := (522576327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((421591672263 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(421591672263 / 250000000000) = 1/(250000000000 / 421591672263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8535 : Bounds (261288163 / 500000000) (522576327 / 1000000000) (Real.log (421591672263 / 250000000000)) := by
  have h := reflection_log_8535_neg
  have he : Real.log (421591672263 / 250000000000) = -Real.log (250000000000 / 421591672263) := by
    rw [show ((421591672263 / 250000000000) : ℝ) = ((250000000000 / 421591672263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8536_neg : (65455789 / 125000000) ≤ -Real.log (250000000000 / 422043010753) ∧
    -Real.log (250000000000 / 422043010753) ≤ (523646313 / 1000000000) := by
  have h := checkLog_sound (w := (172043010753 / 672043010753)) (n := 12)
    (lo := (65455789 / 125000000)) (hi := (523646313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((422043010753 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(422043010753 / 250000000000) = 1/(250000000000 / 422043010753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8536 : Bounds (65455789 / 125000000) (523646313 / 1000000000) (Real.log (422043010753 / 250000000000)) := by
  have h := reflection_log_8536_neg
  have he : Real.log (422043010753 / 250000000000) = -Real.log (250000000000 / 422043010753) := by
    rw [show ((422043010753 / 250000000000) : ℝ) = ((250000000000 / 422043010753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8537_neg : (114165039 / 500000000) ≤ -Real.log (2000 / 2513) ∧
    -Real.log (2000 / 2513) ≤ (228330079 / 1000000000) := by
  have h := checkLog_sound (w := (513 / 4513)) (n := 12)
    (lo := (114165039 / 500000000)) (hi := (228330079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2513 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2513 / 2000) = 1/(2000 / 2513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8537 : Bounds (114165039 / 500000000) (228330079 / 1000000000) (Real.log (2513 / 2000)) := by
  have h := reflection_log_8537_neg
  have he : Real.log (2513 / 2000) = -Real.log (2000 / 2513) := by
    rw [show ((2513 / 2000) : ℝ) = ((2000 / 2513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8538_neg : (296386513 / 1000000000) ≤ -Real.log (1487 / 2000) ∧
    -Real.log (1487 / 2000) ≤ (148193257 / 500000000) := by
  have h := checkLog_sound (w := (513 / 3487)) (n := 12)
    (lo := (296386513 / 1000000000)) (hi := (148193257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1487) = 1/(1487 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8538 : Bounds (-148193257 / 500000000) (-296386513 / 1000000000) (Real.log (1487 / 2000)) := by
  have h := reflection_log_8538_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8539_neg : (256467 / 1000000000) ≤ -Real.log (2000000 / 2000513) ∧
    -Real.log (2000000 / 2000513) ≤ (64117 / 250000000) := by
  have h := checkLog_sound (w := (513 / 4000513)) (n := 12)
    (lo := (256467 / 1000000000)) (hi := (64117 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000513 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000513 / 2000000) = 1/(2000000 / 2000513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8539 : Bounds (256467 / 1000000000) (64117 / 250000000) (Real.log (2000513 / 2000000)) := by
  have h := reflection_log_8539_neg
  have he : Real.log (2000513 / 2000000) = -Real.log (2000000 / 2000513) := by
    rw [show ((2000513 / 2000000) : ℝ) = ((2000000 / 2000513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8540_neg : (64133 / 250000000) ≤ -Real.log (1999487 / 2000000) ∧
    -Real.log (1999487 / 2000000) ≤ (256533 / 1000000000) := by
  have h := checkLog_sound (w := (513 / 3999487)) (n := 12)
    (lo := (64133 / 250000000)) (hi := (256533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999487) = 1/(1999487 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8540 : Bounds (-256533 / 1000000000) (-64133 / 250000000) (Real.log (1999487 / 2000000)) := by
  have h := reflection_log_8540_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8541_neg : (30425171 / 250000000) ≤ -Real.log (125000 / 141177) ∧
    -Real.log (125000 / 141177) ≤ (24340137 / 200000000) := by
  have h := checkLog_sound (w := (16177 / 266177)) (n := 12)
    (lo := (30425171 / 250000000)) (hi := (24340137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141177 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(141177 / 125000) = 1/(125000 / 141177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8541 : Bounds (30425171 / 250000000) (24340137 / 200000000) (Real.log (141177 / 125000)) := by
  have h := reflection_log_8541_neg
  have he : Real.log (141177 / 125000) = -Real.log (125000 / 141177) := by
    rw [show ((141177 / 125000) : ℝ) = ((125000 / 141177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8542_neg : (34647757 / 250000000) ≤ -Real.log (108823 / 125000) ∧
    -Real.log (108823 / 125000) ≤ (138591029 / 1000000000) := by
  have h := checkLog_sound (w := (16177 / 233823)) (n := 12)
    (lo := (34647757 / 250000000)) (hi := (138591029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 108823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 108823) = 1/(108823 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8542 : Bounds (-138591029 / 1000000000) (-34647757 / 250000000) (Real.log (108823 / 125000)) := by
  have h := reflection_log_8542_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8543_neg : (61077399 / 500000000) ≤ -Real.log (1000000 / 1129929) ∧
    -Real.log (1000000 / 1129929) ≤ (122154799 / 1000000000) := by
  have h := checkLog_sound (w := (129929 / 2129929)) (n := 12)
    (lo := (61077399 / 500000000)) (hi := (122154799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1129929 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1129929 / 1000000) = 1/(1000000 / 1129929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8543 : Bounds (61077399 / 500000000) (122154799 / 1000000000) (Real.log (1129929 / 1000000)) := by
  have h := reflection_log_8543_neg
  have he : Real.log (1129929 / 1000000) = -Real.log (1000000 / 1129929) := by
    rw [show ((1129929 / 1000000) : ℝ) = ((1000000 / 1129929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8544_neg : (139180461 / 1000000000) ≤ -Real.log (870071 / 1000000) ∧
    -Real.log (870071 / 1000000) ≤ (69590231 / 500000000) := by
  have h := checkLog_sound (w := (129929 / 1870071)) (n := 12)
    (lo := (139180461 / 1000000000)) (hi := (69590231 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 870071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 870071) = 1/(870071 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8544 : Bounds (-69590231 / 500000000) (-139180461 / 1000000000) (Real.log (870071 / 1000000)) := by
  have h := reflection_log_8544_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8545_neg : (8512831 / 500000000) ≤ -Real.log (983118454959 / 1000000000000) ∧
    -Real.log (983118454959 / 1000000000000) ≤ (17025663 / 1000000000) := by
  have h := checkLog_sound (w := (16881545041 / 1983118454959)) (n := 12)
    (lo := (8512831 / 500000000)) (hi := (17025663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983118454959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983118454959) = 1/(983118454959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8545 : Bounds (-17025663 / 1000000000) (-8512831 / 500000000) (Real.log (983118454959 / 1000000000000)) := by
  have h := reflection_log_8545_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8546_neg : (16890343 / 1000000000) ≤ -Real.log (15363304671 / 15625000000) ∧
    -Real.log (15363304671 / 15625000000) ≤ (2111293 / 125000000) := by
  have h := checkLog_sound (w := (261695329 / 30988304671)) (n := 12)
    (lo := (16890343 / 1000000000)) (hi := (2111293 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15363304671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15363304671) = 1/(15363304671 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8546 : Bounds (-2111293 / 125000000) (-16890343 / 1000000000) (Real.log (15363304671 / 15625000000)) := by
  have h := reflection_log_8546_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8547_neg : (260291713 / 1000000000) ≤ -Real.log (62500000000 / 81081779587) ∧
    -Real.log (62500000000 / 81081779587) ≤ (130145857 / 500000000) := by
  have h := checkLog_sound (w := (18581779587 / 143581779587)) (n := 12)
    (lo := (260291713 / 1000000000)) (hi := (130145857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81081779587 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81081779587 / 62500000000) = 1/(62500000000 / 81081779587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8547 : Bounds (260291713 / 1000000000) (130145857 / 500000000) (Real.log (81081779587 / 62500000000)) := by
  have h := reflection_log_8547_neg
  have he : Real.log (81081779587 / 62500000000) = -Real.log (62500000000 / 81081779587) := by
    rw [show ((81081779587 / 62500000000) : ℝ) = ((62500000000 / 81081779587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8548_neg : (13066763 / 50000000) ≤ -Real.log (500000000000 / 649331491339) ∧
    -Real.log (500000000000 / 649331491339) ≤ (261335261 / 1000000000) := by
  have h := checkLog_sound (w := (149331491339 / 1149331491339)) (n := 12)
    (lo := (13066763 / 50000000)) (hi := (261335261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((649331491339 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(649331491339 / 500000000000) = 1/(500000000000 / 649331491339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8548 : Bounds (13066763 / 50000000) (261335261 / 1000000000) (Real.log (649331491339 / 500000000000)) := by
  have h := reflection_log_8548_neg
  have he : Real.log (649331491339 / 500000000000) = -Real.log (500000000000 / 649331491339) := by
    rw [show ((649331491339 / 500000000000) : ℝ) = ((500000000000 / 649331491339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8549_neg : (65455789 / 125000000) ≤ -Real.log (100000000000 / 168817204301) ∧
    -Real.log (100000000000 / 168817204301) ≤ (523646313 / 1000000000) := by
  have h := checkLog_sound (w := (68817204301 / 268817204301)) (n := 12)
    (lo := (65455789 / 125000000)) (hi := (523646313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168817204301 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168817204301 / 100000000000) = 1/(100000000000 / 168817204301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8549 : Bounds (65455789 / 125000000) (523646313 / 1000000000) (Real.log (168817204301 / 100000000000)) := by
  have h := reflection_log_8549_neg
  have he : Real.log (168817204301 / 100000000000) = -Real.log (100000000000 / 168817204301) := by
    rw [show ((168817204301 / 100000000000) : ℝ) = ((100000000000 / 168817204301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8550_neg : (524716591 / 1000000000) ≤ -Real.log (976562500 / 1650370923) ∧
    -Real.log (976562500 / 1650370923) ≤ (32794787 / 62500000) := by
  have h := checkLog_sound (w := (673808423 / 2626933423)) (n := 12)
    (lo := (524716591 / 1000000000)) (hi := (32794787 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1650370923 / 976562500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1650370923 / 976562500) = 1/(976562500 / 1650370923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8550 : Bounds (524716591 / 1000000000) (32794787 / 62500000) (Real.log (1650370923 / 976562500)) := by
  have h := reflection_log_8550_neg
  have he : Real.log (1650370923 / 976562500) = -Real.log (976562500 / 1650370923) := by
    rw [show ((1650370923 / 976562500) : ℝ) = ((976562500 / 1650370923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8551_neg : (228727929 / 1000000000) ≤ -Real.log (1000 / 1257) ∧
    -Real.log (1000 / 1257) ≤ (22872793 / 100000000) := by
  have h := checkLog_sound (w := (257 / 2257)) (n := 12)
    (lo := (228727929 / 1000000000)) (hi := (22872793 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1257 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1257 / 1000) = 1/(1000 / 1257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8551 : Bounds (228727929 / 1000000000) (22872793 / 100000000) (Real.log (1257 / 1000)) := by
  have h := reflection_log_8551_neg
  have he : Real.log (1257 / 1000) = -Real.log (1000 / 1257) := by
    rw [show ((1257 / 1000) : ℝ) = ((1000 / 1257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8552_neg : (148529617 / 500000000) ≤ -Real.log (743 / 1000) ∧
    -Real.log (743 / 1000) ≤ (59411847 / 200000000) := by
  have h := checkLog_sound (w := (257 / 1743)) (n := 12)
    (lo := (148529617 / 500000000)) (hi := (59411847 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 743) = 1/(743 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8552 : Bounds (-59411847 / 200000000) (-148529617 / 500000000) (Real.log (743 / 1000)) := by
  have h := reflection_log_8552_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8553_neg : (128483 / 500000000) ≤ -Real.log (1000000 / 1000257) ∧
    -Real.log (1000000 / 1000257) ≤ (256967 / 1000000000) := by
  have h := checkLog_sound (w := (257 / 2000257)) (n := 12)
    (lo := (128483 / 500000000)) (hi := (256967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000257 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000257 / 1000000) = 1/(1000000 / 1000257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8553 : Bounds (128483 / 500000000) (256967 / 1000000000) (Real.log (1000257 / 1000000)) := by
  have h := reflection_log_8553_neg
  have he : Real.log (1000257 / 1000000) = -Real.log (1000000 / 1000257) := by
    rw [show ((1000257 / 1000000) : ℝ) = ((1000000 / 1000257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8554_neg : (257033 / 1000000000) ≤ -Real.log (999743 / 1000000) ∧
    -Real.log (999743 / 1000000) ≤ (128517 / 500000000) := by
  have h := checkLog_sound (w := (257 / 1999743)) (n := 12)
    (lo := (257033 / 1000000000)) (hi := (128517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999743) = 1/(999743 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8554 : Bounds (-128517 / 500000000) (-257033 / 1000000000) (Real.log (999743 / 1000000)) := by
  have h := reflection_log_8554_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8555_neg : (6096499 / 50000000) ≤ -Real.log (40000 / 45187) ∧
    -Real.log (40000 / 45187) ≤ (121929981 / 1000000000) := by
  have h := checkLog_sound (w := (5187 / 85187)) (n := 12)
    (lo := (6096499 / 50000000)) (hi := (121929981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45187 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45187 / 40000) = 1/(40000 / 45187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8555 : Bounds (6096499 / 50000000) (121929981 / 1000000000) (Real.log (45187 / 40000)) := by
  have h := reflection_log_8555_neg
  have he : Real.log (45187 / 40000) = -Real.log (40000 / 45187) := by
    rw [show ((45187 / 40000) : ℝ) = ((40000 / 45187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8556_neg : (138888573 / 1000000000) ≤ -Real.log (34813 / 40000) ∧
    -Real.log (34813 / 40000) ≤ (69444287 / 500000000) := by
  have h := checkLog_sound (w := (5187 / 74813)) (n := 12)
    (lo := (138888573 / 1000000000)) (hi := (69444287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 34813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 34813) = 1/(34813 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8556 : Bounds (-69444287 / 500000000) (-138888573 / 1000000000) (Real.log (34813 / 40000)) := by
  have h := reflection_log_8556_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8557_neg : (12238399 / 100000000) ≤ -Real.log (250000 / 282547) ∧
    -Real.log (250000 / 282547) ≤ (122383991 / 1000000000) := by
  have h := checkLog_sound (w := (32547 / 532547)) (n := 12)
    (lo := (12238399 / 100000000)) (hi := (122383991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((282547 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(282547 / 250000) = 1/(250000 / 282547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8557 : Bounds (12238399 / 100000000) (122383991 / 1000000000) (Real.log (282547 / 250000)) := by
  have h := reflection_log_8557_neg
  have he : Real.log (282547 / 250000) = -Real.log (250000 / 282547) := by
    rw [show ((282547 / 250000) : ℝ) = ((250000 / 282547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8558_neg : (69739091 / 500000000) ≤ -Real.log (217453 / 250000) ∧
    -Real.log (217453 / 250000) ≤ (139478183 / 1000000000) := by
  have h := checkLog_sound (w := (32547 / 467453)) (n := 12)
    (lo := (69739091 / 500000000)) (hi := (139478183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 217453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 217453) = 1/(217453 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8558 : Bounds (-139478183 / 1000000000) (-69739091 / 500000000) (Real.log (217453 / 250000)) := by
  have h := reflection_log_8558_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8559_neg : (1068387 / 62500000) ≤ -Real.log (61440692791 / 62500000000) ∧
    -Real.log (61440692791 / 62500000000) ≤ (17094193 / 1000000000) := by
  have h := checkLog_sound (w := (1059307209 / 123940692791)) (n := 12)
    (lo := (1068387 / 62500000)) (hi := (17094193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61440692791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61440692791) = 1/(61440692791 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8559 : Bounds (-17094193 / 1000000000) (-1068387 / 62500000) (Real.log (61440692791 / 62500000000)) := by
  have h := reflection_log_8559_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8560_neg : (16958593 / 1000000000) ≤ -Real.log (1573095031 / 1600000000) ∧
    -Real.log (1573095031 / 1600000000) ≤ (8479297 / 500000000) := by
  have h := checkLog_sound (w := (26904969 / 3173095031)) (n := 12)
    (lo := (16958593 / 1000000000)) (hi := (8479297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1573095031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1573095031) = 1/(1573095031 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8560 : Bounds (-8479297 / 500000000) (-16958593 / 1000000000) (Real.log (1573095031 / 1600000000)) := by
  have h := reflection_log_8560_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8561_neg : (130409277 / 500000000) ≤ -Real.log (31250000000 / 40562254043) ∧
    -Real.log (31250000000 / 40562254043) ≤ (52163711 / 200000000) := by
  have h := checkLog_sound (w := (9312254043 / 71812254043)) (n := 12)
    (lo := (130409277 / 500000000)) (hi := (52163711 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40562254043 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40562254043 / 31250000000) = 1/(31250000000 / 40562254043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8561 : Bounds (130409277 / 500000000) (52163711 / 200000000) (Real.log (40562254043 / 31250000000)) := by
  have h := reflection_log_8561_neg
  have he : Real.log (40562254043 / 31250000000) = -Real.log (31250000000 / 40562254043) := by
    rw [show ((40562254043 / 31250000000) : ℝ) = ((31250000000 / 40562254043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8562_neg : (261862173 / 1000000000) ≤ -Real.log (250000000000 / 324836861299) ∧
    -Real.log (250000000000 / 324836861299) ≤ (130931087 / 500000000) := by
  have h := checkLog_sound (w := (74836861299 / 574836861299)) (n := 12)
    (lo := (261862173 / 1000000000)) (hi := (130931087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((324836861299 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(324836861299 / 250000000000) = 1/(250000000000 / 324836861299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8562 : Bounds (261862173 / 1000000000) (130931087 / 500000000) (Real.log (324836861299 / 250000000000)) := by
  have h := reflection_log_8562_neg
  have he : Real.log (324836861299 / 250000000000) = -Real.log (250000000000 / 324836861299) := by
    rw [show ((324836861299 / 250000000000) : ℝ) = ((250000000000 / 324836861299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8563_neg : (524716591 / 1000000000) ≤ -Real.log (20000000000 / 33799596503) ∧
    -Real.log (20000000000 / 33799596503) ≤ (32794787 / 62500000) := by
  have h := checkLog_sound (w := (13799596503 / 53799596503)) (n := 12)
    (lo := (524716591 / 1000000000)) (hi := (32794787 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33799596503 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33799596503 / 20000000000) = 1/(20000000000 / 33799596503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8563 : Bounds (524716591 / 1000000000) (32794787 / 62500000) (Real.log (33799596503 / 20000000000)) := by
  have h := reflection_log_8563_neg
  have he : Real.log (33799596503 / 20000000000) = -Real.log (20000000000 / 33799596503) := by
    rw [show ((33799596503 / 20000000000) : ℝ) = ((20000000000 / 33799596503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8564_neg : (525787163 / 1000000000) ≤ -Real.log (500000000000 / 845895020189) ∧
    -Real.log (500000000000 / 845895020189) ≤ (131446791 / 250000000) := by
  have h := checkLog_sound (w := (345895020189 / 1345895020189)) (n := 12)
    (lo := (525787163 / 1000000000)) (hi := (131446791 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((845895020189 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(845895020189 / 500000000000) = 1/(500000000000 / 845895020189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8564 : Bounds (525787163 / 1000000000) (131446791 / 250000000) (Real.log (845895020189 / 500000000000)) := by
  have h := reflection_log_8564_neg
  have he : Real.log (845895020189 / 500000000000) = -Real.log (500000000000 / 845895020189) := by
    rw [show ((845895020189 / 500000000000) : ℝ) = ((500000000000 / 845895020189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8565_neg : (114562811 / 500000000) ≤ -Real.log (400 / 503) ∧
    -Real.log (400 / 503) ≤ (229125623 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 903)) (n := 12)
    (lo := (114562811 / 500000000)) (hi := (229125623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((503 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(503 / 400) = 1/(400 / 503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8565 : Bounds (114562811 / 500000000) (229125623 / 1000000000) (Real.log (503 / 400)) := by
  have h := reflection_log_8565_neg
  have he : Real.log (503 / 400) = -Real.log (400 / 503) := by
    rw [show ((503 / 400) : ℝ) = ((400 / 503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8566_neg : (37216551 / 125000000) ≤ -Real.log (297 / 400) ∧
    -Real.log (297 / 400) ≤ (297732409 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 697)) (n := 12)
    (lo := (37216551 / 125000000)) (hi := (297732409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 297) = 1/(297 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8566 : Bounds (-297732409 / 1000000000) (-37216551 / 125000000) (Real.log (297 / 400)) := by
  have h := reflection_log_8566_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8567_neg : (128733 / 500000000) ≤ -Real.log (400000 / 400103) ∧
    -Real.log (400000 / 400103) ≤ (257467 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 800103)) (n := 12)
    (lo := (128733 / 500000000)) (hi := (257467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400103 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400103 / 400000) = 1/(400000 / 400103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8567 : Bounds (128733 / 500000000) (257467 / 1000000000) (Real.log (400103 / 400000)) := by
  have h := reflection_log_8567_neg
  have he : Real.log (400103 / 400000) = -Real.log (400000 / 400103) := by
    rw [show ((400103 / 400000) : ℝ) = ((400000 / 400103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8568_neg : (257533 / 1000000000) ≤ -Real.log (399897 / 400000) ∧
    -Real.log (399897 / 400000) ≤ (128767 / 500000000) := by
  have h := checkLog_sound (w := (103 / 799897)) (n := 12)
    (lo := (257533 / 1000000000)) (hi := (128767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399897) = 1/(399897 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8568 : Bounds (-128767 / 500000000) (-257533 / 1000000000) (Real.log (399897 / 400000)) := by
  have h := reflection_log_8568_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8569_neg : (122159223 / 1000000000) ≤ -Real.log (500000 / 564967) ∧
    -Real.log (500000 / 564967) ≤ (15269903 / 125000000) := by
  have h := checkLog_sound (w := (64967 / 1064967)) (n := 12)
    (lo := (122159223 / 1000000000)) (hi := (15269903 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((564967 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(564967 / 500000) = 1/(500000 / 564967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8569 : Bounds (122159223 / 1000000000) (15269903 / 125000000) (Real.log (564967 / 500000)) := by
  have h := reflection_log_8569_neg
  have he : Real.log (564967 / 500000) = -Real.log (500000 / 564967) := by
    rw [show ((564967 / 500000) : ℝ) = ((500000 / 564967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8570_neg : (4349569 / 31250000) ≤ -Real.log (435033 / 500000) ∧
    -Real.log (435033 / 500000) ≤ (139186209 / 1000000000) := by
  have h := checkLog_sound (w := (64967 / 935033)) (n := 12)
    (lo := (4349569 / 31250000)) (hi := (139186209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 435033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 435033) = 1/(435033 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8570 : Bounds (-139186209 / 1000000000) (-4349569 / 31250000) (Real.log (435033 / 500000)) := by
  have h := reflection_log_8570_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8571_neg : (61307007 / 500000000) ≤ -Real.log (62500 / 70653) ∧
    -Real.log (62500 / 70653) ≤ (24522803 / 200000000) := by
  have h := checkLog_sound (w := (8153 / 133153)) (n := 12)
    (lo := (61307007 / 500000000)) (hi := (24522803 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70653 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(70653 / 62500) = 1/(62500 / 70653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8571 : Bounds (61307007 / 500000000) (24522803 / 200000000) (Real.log (70653 / 62500)) := by
  have h := reflection_log_8571_neg
  have he : Real.log (70653 / 62500) = -Real.log (62500 / 70653) := by
    rw [show ((70653 / 62500) : ℝ) = ((62500 / 70653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8572_neg : (69888571 / 500000000) ≤ -Real.log (54347 / 62500) ∧
    -Real.log (54347 / 62500) ≤ (139777143 / 1000000000) := by
  have h := checkLog_sound (w := (8153 / 116847)) (n := 12)
    (lo := (69888571 / 500000000)) (hi := (139777143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 54347) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 54347) = 1/(54347 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8572 : Bounds (-139777143 / 1000000000) (-69888571 / 500000000) (Real.log (54347 / 62500)) := by
  have h := reflection_log_8572_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8573_neg : (2145391 / 125000000) ≤ -Real.log (3839778591 / 3906250000) ∧
    -Real.log (3839778591 / 3906250000) ≤ (17163129 / 1000000000) := by
  have h := checkLog_sound (w := (66471409 / 7746028591)) (n := 12)
    (lo := (2145391 / 125000000)) (hi := (17163129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3839778591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3839778591) = 1/(3839778591 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8573 : Bounds (-17163129 / 1000000000) (-2145391 / 125000000) (Real.log (3839778591 / 3906250000)) := by
  have h := reflection_log_8573_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8574_neg : (2128373 / 125000000) ≤ -Real.log (245779288911 / 250000000000) ∧
    -Real.log (245779288911 / 250000000000) ≤ (3405397 / 200000000) := by
  have h := checkLog_sound (w := (4220711089 / 495779288911)) (n := 12)
    (lo := (2128373 / 125000000)) (hi := (3405397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245779288911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245779288911) = 1/(245779288911 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8574 : Bounds (-3405397 / 200000000) (-2128373 / 125000000) (Real.log (245779288911 / 250000000000)) := by
  have h := reflection_log_8574_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8575_neg : (32668179 / 125000000) ≤ -Real.log (50000000000 / 64933809619) ∧
    -Real.log (50000000000 / 64933809619) ≤ (261345433 / 1000000000) := by
  have h := checkLog_sound (w := (14933809619 / 114933809619)) (n := 12)
    (lo := (32668179 / 125000000)) (hi := (261345433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64933809619 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64933809619 / 50000000000) = 1/(50000000000 / 64933809619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8575 : Bounds (32668179 / 125000000) (261345433 / 1000000000) (Real.log (64933809619 / 50000000000)) := by
  have h := reflection_log_8575_neg
  have he : Real.log (64933809619 / 50000000000) = -Real.log (50000000000 / 64933809619) := by
    rw [show ((64933809619 / 50000000000) : ℝ) = ((50000000000 / 64933809619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0134 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8576_neg : (65597789 / 250000000) ≤ -Real.log (250000000000 / 325008740133) ∧
    -Real.log (250000000000 / 325008740133) ≤ (262391157 / 1000000000) := by
  have h := checkLog_sound (w := (75008740133 / 575008740133)) (n := 12)
    (lo := (65597789 / 250000000)) (hi := (262391157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((325008740133 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(325008740133 / 250000000000) = 1/(250000000000 / 325008740133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8576 : Bounds (65597789 / 250000000) (262391157 / 1000000000) (Real.log (325008740133 / 250000000000)) := by
  have h := reflection_log_8576_neg
  have he : Real.log (325008740133 / 250000000000) = -Real.log (250000000000 / 325008740133) := by
    rw [show ((325008740133 / 250000000000) : ℝ) = ((250000000000 / 325008740133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8577_neg : (525787163 / 1000000000) ≤ -Real.log (125000000000 / 211473755047) ∧
    -Real.log (125000000000 / 211473755047) ≤ (131446791 / 250000000) := by
  have h := checkLog_sound (w := (86473755047 / 336473755047)) (n := 12)
    (lo := (525787163 / 1000000000)) (hi := (131446791 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211473755047 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(211473755047 / 125000000000) = 1/(125000000000 / 211473755047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8577 : Bounds (525787163 / 1000000000) (131446791 / 250000000) (Real.log (211473755047 / 125000000000)) := by
  have h := reflection_log_8577_neg
  have he : Real.log (211473755047 / 125000000000) = -Real.log (125000000000 / 211473755047) := by
    rw [show ((211473755047 / 125000000000) : ℝ) = ((125000000000 / 211473755047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8578_neg : (526858031 / 1000000000) ≤ -Real.log (250000000000 / 423400673401) ∧
    -Real.log (250000000000 / 423400673401) ≤ (32928627 / 62500000) := by
  have h := checkLog_sound (w := (173400673401 / 673400673401)) (n := 12)
    (lo := (526858031 / 1000000000)) (hi := (32928627 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((423400673401 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(423400673401 / 250000000000) = 1/(250000000000 / 423400673401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8578 : Bounds (526858031 / 1000000000) (32928627 / 62500000) (Real.log (423400673401 / 250000000000)) := by
  have h := reflection_log_8578_neg
  have he : Real.log (423400673401 / 250000000000) = -Real.log (250000000000 / 423400673401) := by
    rw [show ((423400673401 / 250000000000) : ℝ) = ((250000000000 / 423400673401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8579_neg : (114761579 / 500000000) ≤ -Real.log (500 / 629) ∧
    -Real.log (500 / 629) ≤ (229523159 / 1000000000) := by
  have h := checkLog_sound (w := (129 / 1129)) (n := 12)
    (lo := (114761579 / 500000000)) (hi := (229523159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((629 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(629 / 500) = 1/(500 / 629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8579 : Bounds (114761579 / 500000000) (229523159 / 1000000000) (Real.log (629 / 500)) := by
  have h := reflection_log_8579_neg
  have he : Real.log (629 / 500) = -Real.log (500 / 629) := by
    rw [show ((629 / 500) : ℝ) = ((500 / 629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8580_neg : (59681207 / 200000000) ≤ -Real.log (371 / 500) ∧
    -Real.log (371 / 500) ≤ (74601509 / 250000000) := by
  have h := checkLog_sound (w := (129 / 871)) (n := 12)
    (lo := (59681207 / 200000000)) (hi := (74601509 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 371) = 1/(371 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8580 : Bounds (-74601509 / 250000000) (-59681207 / 200000000) (Real.log (371 / 500)) := by
  have h := reflection_log_8580_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8581_neg : (128983 / 500000000) ≤ -Real.log (500000 / 500129) ∧
    -Real.log (500000 / 500129) ≤ (257967 / 1000000000) := by
  have h := checkLog_sound (w := (129 / 1000129)) (n := 12)
    (lo := (128983 / 500000000)) (hi := (257967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500129 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500129 / 500000) = 1/(500000 / 500129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8581 : Bounds (128983 / 500000000) (257967 / 1000000000) (Real.log (500129 / 500000)) := by
  have h := reflection_log_8581_neg
  have he : Real.log (500129 / 500000) = -Real.log (500000 / 500129) := by
    rw [show ((500129 / 500000) : ℝ) = ((500000 / 500129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8582_neg : (258033 / 1000000000) ≤ -Real.log (499871 / 500000) ∧
    -Real.log (499871 / 500000) ≤ (129017 / 500000000) := by
  have h := checkLog_sound (w := (129 / 999871)) (n := 12)
    (lo := (258033 / 1000000000)) (hi := (129017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499871) = 1/(499871 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8582 : Bounds (-129017 / 500000000) (-258033 / 1000000000) (Real.log (499871 / 500000)) := by
  have h := reflection_log_8582_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8583_neg : (61194207 / 500000000) ≤ -Real.log (1000000 / 1130193) ∧
    -Real.log (1000000 / 1130193) ≤ (24477683 / 200000000) := by
  have h := checkLog_sound (w := (130193 / 2130193)) (n := 12)
    (lo := (61194207 / 500000000)) (hi := (24477683 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1130193 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1130193 / 1000000) = 1/(1000000 / 1130193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8583 : Bounds (61194207 / 500000000) (24477683 / 200000000) (Real.log (1130193 / 1000000)) := by
  have h := reflection_log_8583_neg
  have he : Real.log (1130193 / 1000000) = -Real.log (1000000 / 1130193) := by
    rw [show ((1130193 / 1000000) : ℝ) = ((1000000 / 1130193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8584_neg : (139483931 / 1000000000) ≤ -Real.log (869807 / 1000000) ∧
    -Real.log (869807 / 1000000) ≤ (34870983 / 250000000) := by
  have h := checkLog_sound (w := (130193 / 1869807)) (n := 12)
    (lo := (139483931 / 1000000000)) (hi := (34870983 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 869807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 869807) = 1/(869807 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8584 : Bounds (-34870983 / 250000000) (-139483931 / 1000000000) (Real.log (869807 / 1000000)) := by
  have h := reflection_log_8584_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8585_neg : (1228431 / 10000000) ≤ -Real.log (1000000 / 1130707) ∧
    -Real.log (1000000 / 1130707) ≤ (122843101 / 1000000000) := by
  have h := checkLog_sound (w := (130707 / 2130707)) (n := 12)
    (lo := (1228431 / 10000000)) (hi := (122843101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1130707 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1130707 / 1000000) = 1/(1000000 / 1130707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8585 : Bounds (1228431 / 10000000) (122843101 / 1000000000) (Real.log (1130707 / 1000000)) := by
  have h := reflection_log_8585_neg
  have he : Real.log (1130707 / 1000000) = -Real.log (1000000 / 1130707) := by
    rw [show ((1130707 / 1000000) : ℝ) = ((1000000 / 1130707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8586_neg : (140075041 / 1000000000) ≤ -Real.log (869293 / 1000000) ∧
    -Real.log (869293 / 1000000) ≤ (70037521 / 500000000) := by
  have h := checkLog_sound (w := (130707 / 1869293)) (n := 12)
    (lo := (140075041 / 1000000000)) (hi := (70037521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 869293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 869293) = 1/(869293 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8586 : Bounds (-70037521 / 500000000) (-140075041 / 1000000000) (Real.log (869293 / 1000000)) := by
  have h := reflection_log_8586_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8587_neg : (861597 / 50000000) ≤ -Real.log (982915680151 / 1000000000000) ∧
    -Real.log (982915680151 / 1000000000000) ≤ (17231941 / 1000000000) := by
  have h := checkLog_sound (w := (17084319849 / 1982915680151)) (n := 12)
    (lo := (861597 / 50000000)) (hi := (17231941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982915680151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982915680151) = 1/(982915680151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8587 : Bounds (-17231941 / 1000000000) (-861597 / 50000000) (Real.log (982915680151 / 1000000000000)) := by
  have h := reflection_log_8587_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8588_neg : (4273879 / 250000000) ≤ -Real.log (983049782751 / 1000000000000) ∧
    -Real.log (983049782751 / 1000000000000) ≤ (17095517 / 1000000000) := by
  have h := checkLog_sound (w := (16950217249 / 1983049782751)) (n := 12)
    (lo := (4273879 / 250000000)) (hi := (17095517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983049782751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983049782751) = 1/(983049782751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8588 : Bounds (-17095517 / 1000000000) (-4273879 / 250000000) (Real.log (983049782751 / 1000000000000)) := by
  have h := reflection_log_8588_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8589_neg : (52374469 / 200000000) ≤ -Real.log (500000000000 / 649680331383) ∧
    -Real.log (500000000000 / 649680331383) ≤ (130936173 / 500000000) := by
  have h := checkLog_sound (w := (149680331383 / 1149680331383)) (n := 12)
    (lo := (52374469 / 200000000)) (hi := (130936173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((649680331383 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(649680331383 / 500000000000) = 1/(500000000000 / 649680331383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8589 : Bounds (52374469 / 200000000) (130936173 / 500000000) (Real.log (649680331383 / 500000000000)) := by
  have h := reflection_log_8589_neg
  have he : Real.log (649680331383 / 500000000000) = -Real.log (500000000000 / 649680331383) := by
    rw [show ((649680331383 / 500000000000) : ℝ) = ((500000000000 / 649680331383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8590_neg : (131459071 / 500000000) ≤ -Real.log (125000000000 / 162590030059) ∧
    -Real.log (125000000000 / 162590030059) ≤ (262918143 / 1000000000) := by
  have h := checkLog_sound (w := (37590030059 / 287590030059)) (n := 12)
    (lo := (131459071 / 500000000)) (hi := (262918143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162590030059 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162590030059 / 125000000000) = 1/(125000000000 / 162590030059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8590 : Bounds (131459071 / 500000000) (262918143 / 1000000000) (Real.log (162590030059 / 125000000000)) := by
  have h := reflection_log_8590_neg
  have he : Real.log (162590030059 / 125000000000) = -Real.log (125000000000 / 162590030059) := by
    rw [show ((162590030059 / 125000000000) : ℝ) = ((125000000000 / 162590030059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8591_neg : (526858031 / 1000000000) ≤ -Real.log (500000000000 / 846801346801) ∧
    -Real.log (500000000000 / 846801346801) ≤ (32928627 / 62500000) := by
  have h := checkLog_sound (w := (346801346801 / 1346801346801)) (n := 12)
    (lo := (526858031 / 1000000000)) (hi := (32928627 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((846801346801 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(846801346801 / 500000000000) = 1/(500000000000 / 846801346801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8591 : Bounds (526858031 / 1000000000) (32928627 / 62500000) (Real.log (846801346801 / 500000000000)) := by
  have h := reflection_log_8591_neg
  have he : Real.log (846801346801 / 500000000000) = -Real.log (500000000000 / 846801346801) := by
    rw [show ((846801346801 / 500000000000) : ℝ) = ((500000000000 / 846801346801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8592_neg : (263964597 / 500000000) ≤ -Real.log (500000000000 / 847708894879) ∧
    -Real.log (500000000000 / 847708894879) ≤ (105585839 / 200000000) := by
  have h := checkLog_sound (w := (347708894879 / 1347708894879)) (n := 12)
    (lo := (263964597 / 500000000)) (hi := (105585839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((847708894879 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(847708894879 / 500000000000) = 1/(500000000000 / 847708894879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8592 : Bounds (263964597 / 500000000) (105585839 / 200000000) (Real.log (847708894879 / 500000000000)) := by
  have h := reflection_log_8592_neg
  have he : Real.log (847708894879 / 500000000000) = -Real.log (500000000000 / 847708894879) := by
    rw [show ((847708894879 / 500000000000) : ℝ) = ((500000000000 / 847708894879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8593_neg : (45984107 / 200000000) ≤ -Real.log (2000 / 2517) ∧
    -Real.log (2000 / 2517) ≤ (28740067 / 125000000) := by
  have h := checkLog_sound (w := (517 / 4517)) (n := 12)
    (lo := (45984107 / 200000000)) (hi := (28740067 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2517 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2517 / 2000) = 1/(2000 / 2517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8593 : Bounds (45984107 / 200000000) (28740067 / 125000000) (Real.log (2517 / 2000)) := by
  have h := reflection_log_8593_neg
  have he : Real.log (2517 / 2000) = -Real.log (2000 / 2517) := by
    rw [show ((2517 / 2000) : ℝ) = ((2000 / 2517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8594_neg : (299080117 / 1000000000) ≤ -Real.log (1483 / 2000) ∧
    -Real.log (1483 / 2000) ≤ (149540059 / 500000000) := by
  have h := checkLog_sound (w := (517 / 3483)) (n := 12)
    (lo := (299080117 / 1000000000)) (hi := (149540059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1483) = 1/(1483 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8594 : Bounds (-149540059 / 500000000) (-299080117 / 1000000000) (Real.log (1483 / 2000)) := by
  have h := reflection_log_8594_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8595_neg : (129233 / 500000000) ≤ -Real.log (2000000 / 2000517) ∧
    -Real.log (2000000 / 2000517) ≤ (258467 / 1000000000) := by
  have h := checkLog_sound (w := (517 / 4000517)) (n := 12)
    (lo := (129233 / 500000000)) (hi := (258467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000517 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000517 / 2000000) = 1/(2000000 / 2000517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8595 : Bounds (129233 / 500000000) (258467 / 1000000000) (Real.log (2000517 / 2000000)) := by
  have h := reflection_log_8595_neg
  have he : Real.log (2000517 / 2000000) = -Real.log (2000000 / 2000517) := by
    rw [show ((2000517 / 2000000) : ℝ) = ((2000000 / 2000517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8596_neg : (258533 / 1000000000) ≤ -Real.log (1999483 / 2000000) ∧
    -Real.log (1999483 / 2000000) ≤ (129267 / 500000000) := by
  have h := checkLog_sound (w := (517 / 3999483)) (n := 12)
    (lo := (258533 / 1000000000)) (hi := (129267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999483) = 1/(1999483 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8596 : Bounds (-129267 / 500000000) (-258533 / 1000000000) (Real.log (1999483 / 2000000)) := by
  have h := reflection_log_8596_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8597_neg : (7663597 / 62500000) ≤ -Real.log (250000 / 282613) ∧
    -Real.log (250000 / 282613) ≤ (122617553 / 1000000000) := by
  have h := checkLog_sound (w := (32613 / 532613)) (n := 12)
    (lo := (7663597 / 62500000)) (hi := (122617553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((282613 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(282613 / 250000) = 1/(250000 / 282613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8597 : Bounds (7663597 / 62500000) (122617553 / 1000000000) (Real.log (282613 / 250000)) := by
  have h := reflection_log_8597_neg
  have he : Real.log (282613 / 250000) = -Real.log (250000 / 282613) := by
    rw [show ((282613 / 250000) : ℝ) = ((250000 / 282613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8598_neg : (69890871 / 500000000) ≤ -Real.log (217387 / 250000) ∧
    -Real.log (217387 / 250000) ≤ (139781743 / 1000000000) := by
  have h := checkLog_sound (w := (32613 / 467387)) (n := 12)
    (lo := (69890871 / 500000000)) (hi := (139781743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 217387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 217387) = 1/(217387 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8598 : Bounds (-139781743 / 1000000000) (-69890871 / 500000000) (Real.log (217387 / 250000)) := by
  have h := reflection_log_8598_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8599_neg : (61536509 / 500000000) ≤ -Real.log (1000000 / 1130967) ∧
    -Real.log (1000000 / 1130967) ≤ (123073019 / 1000000000) := by
  have h := checkLog_sound (w := (130967 / 2130967)) (n := 12)
    (lo := (61536509 / 500000000)) (hi := (123073019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1130967 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1130967 / 1000000) = 1/(1000000 / 1130967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8599 : Bounds (61536509 / 500000000) (123073019 / 1000000000) (Real.log (1130967 / 1000000)) := by
  have h := reflection_log_8599_neg
  have he : Real.log (1130967 / 1000000) = -Real.log (1000000 / 1130967) := by
    rw [show ((1130967 / 1000000) : ℝ) = ((1000000 / 1130967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8600_neg : (140374179 / 1000000000) ≤ -Real.log (869033 / 1000000) ∧
    -Real.log (869033 / 1000000) ≤ (7018709 / 50000000) := by
  have h := checkLog_sound (w := (130967 / 1869033)) (n := 12)
    (lo := (140374179 / 1000000000)) (hi := (7018709 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 869033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 869033) = 1/(869033 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8600 : Bounds (-7018709 / 50000000) (-140374179 / 1000000000) (Real.log (869033 / 1000000)) := by
  have h := reflection_log_8600_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8601_neg : (432529 / 25000000) ≤ -Real.log (982847644911 / 1000000000000) ∧
    -Real.log (982847644911 / 1000000000000) ≤ (17301161 / 1000000000) := by
  have h := checkLog_sound (w := (17152355089 / 1982847644911)) (n := 12)
    (lo := (432529 / 25000000)) (hi := (17301161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982847644911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982847644911) = 1/(982847644911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8601 : Bounds (-17301161 / 1000000000) (-432529 / 25000000) (Real.log (982847644911 / 1000000000000)) := by
  have h := reflection_log_8601_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8602_neg : (17164189 / 1000000000) ≤ -Real.log (61436392231 / 62500000000) ∧
    -Real.log (61436392231 / 62500000000) ≤ (1716419 / 100000000) := by
  have h := checkLog_sound (w := (1063607769 / 123936392231)) (n := 12)
    (lo := (17164189 / 1000000000)) (hi := (1716419 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61436392231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61436392231) = 1/(61436392231 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8602 : Bounds (-1716419 / 100000000) (-17164189 / 1000000000) (Real.log (61436392231 / 62500000000)) := by
  have h := reflection_log_8602_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8603_neg : (52479859 / 200000000) ≤ -Real.log (10000000000 / 13000455409) ∧
    -Real.log (10000000000 / 13000455409) ≤ (4099989 / 15625000) := by
  have h := checkLog_sound (w := (3000455409 / 23000455409)) (n := 12)
    (lo := (52479859 / 200000000)) (hi := (4099989 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13000455409 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13000455409 / 10000000000) = 1/(10000000000 / 13000455409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8603 : Bounds (52479859 / 200000000) (4099989 / 15625000) (Real.log (13000455409 / 10000000000)) := by
  have h := reflection_log_8603_neg
  have he : Real.log (13000455409 / 10000000000) = -Real.log (10000000000 / 13000455409) := by
    rw [show ((13000455409 / 10000000000) : ℝ) = ((10000000000 / 13000455409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8604_neg : (131723599 / 500000000) ≤ -Real.log (6250000000 / 8133803607) ∧
    -Real.log (6250000000 / 8133803607) ≤ (263447199 / 1000000000) := by
  have h := checkLog_sound (w := (1883803607 / 14383803607)) (n := 12)
    (lo := (131723599 / 500000000)) (hi := (263447199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8133803607 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8133803607 / 6250000000) = 1/(6250000000 / 8133803607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8604 : Bounds (131723599 / 500000000) (263447199 / 1000000000) (Real.log (8133803607 / 6250000000)) := by
  have h := reflection_log_8604_neg
  have he : Real.log (8133803607 / 6250000000) = -Real.log (6250000000 / 8133803607) := by
    rw [show ((8133803607 / 6250000000) : ℝ) = ((6250000000 / 8133803607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8605_neg : (263964597 / 500000000) ≤ -Real.log (250000000000 / 423854447439) ∧
    -Real.log (250000000000 / 423854447439) ≤ (105585839 / 200000000) := by
  have h := checkLog_sound (w := (173854447439 / 673854447439)) (n := 12)
    (lo := (263964597 / 500000000)) (hi := (105585839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((423854447439 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(423854447439 / 250000000000) = 1/(250000000000 / 423854447439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8605 : Bounds (263964597 / 500000000) (105585839 / 200000000) (Real.log (423854447439 / 250000000000)) := by
  have h := reflection_log_8605_neg
  have he : Real.log (423854447439 / 250000000000) = -Real.log (250000000000 / 423854447439) := by
    rw [show ((423854447439 / 250000000000) : ℝ) = ((250000000000 / 423854447439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8606_neg : (132250163 / 250000000) ≤ -Real.log (125000000000 / 212154416723) ∧
    -Real.log (125000000000 / 212154416723) ≤ (529000653 / 1000000000) := by
  have h := checkLog_sound (w := (87154416723 / 337154416723)) (n := 12)
    (lo := (132250163 / 250000000)) (hi := (529000653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((212154416723 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(212154416723 / 125000000000) = 1/(125000000000 / 212154416723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8606 : Bounds (132250163 / 250000000) (529000653 / 1000000000) (Real.log (212154416723 / 125000000000)) := by
  have h := reflection_log_8606_neg
  have he : Real.log (212154416723 / 125000000000) = -Real.log (125000000000 / 212154416723) := by
    rw [show ((212154416723 / 125000000000) : ℝ) = ((125000000000 / 212154416723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8607_neg : (46063551 / 200000000) ≤ -Real.log (1000 / 1259) ∧
    -Real.log (1000 / 1259) ≤ (57579439 / 250000000) := by
  have h := checkLog_sound (w := (259 / 2259)) (n := 12)
    (lo := (46063551 / 200000000)) (hi := (57579439 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1259 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1259 / 1000) = 1/(1000 / 1259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8607 : Bounds (46063551 / 200000000) (57579439 / 250000000) (Real.log (1259 / 1000)) := by
  have h := reflection_log_8607_neg
  have he : Real.log (1259 / 1000) = -Real.log (1000 / 1259) := by
    rw [show ((1259 / 1000) : ℝ) = ((1000 / 1259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8608_neg : (299754653 / 1000000000) ≤ -Real.log (741 / 1000) ∧
    -Real.log (741 / 1000) ≤ (149877327 / 500000000) := by
  have h := checkLog_sound (w := (259 / 1741)) (n := 12)
    (lo := (299754653 / 1000000000)) (hi := (149877327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 741) = 1/(741 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8608 : Bounds (-149877327 / 500000000) (-299754653 / 1000000000) (Real.log (741 / 1000)) := by
  have h := reflection_log_8608_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8609_neg : (129483 / 500000000) ≤ -Real.log (1000000 / 1000259) ∧
    -Real.log (1000000 / 1000259) ≤ (258967 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 2000259)) (n := 12)
    (lo := (129483 / 500000000)) (hi := (258967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000259 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000259 / 1000000) = 1/(1000000 / 1000259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8609 : Bounds (129483 / 500000000) (258967 / 1000000000) (Real.log (1000259 / 1000000)) := by
  have h := reflection_log_8609_neg
  have he : Real.log (1000259 / 1000000) = -Real.log (1000000 / 1000259) := by
    rw [show ((1000259 / 1000000) : ℝ) = ((1000000 / 1000259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8610_neg : (259033 / 1000000000) ≤ -Real.log (999741 / 1000000) ∧
    -Real.log (999741 / 1000000) ≤ (129517 / 500000000) := by
  have h := checkLog_sound (w := (259 / 1999741)) (n := 12)
    (lo := (259033 / 1000000000)) (hi := (129517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999741) = 1/(999741 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8610 : Bounds (-129517 / 500000000) (-259033 / 1000000000) (Real.log (999741 / 1000000)) := by
  have h := reflection_log_8610_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8611_neg : (61423319 / 500000000) ≤ -Real.log (1000000 / 1130711) ∧
    -Real.log (1000000 / 1130711) ≤ (122846639 / 1000000000) := by
  have h := checkLog_sound (w := (130711 / 2130711)) (n := 12)
    (lo := (61423319 / 500000000)) (hi := (122846639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1130711 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1130711 / 1000000) = 1/(1000000 / 1130711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8611 : Bounds (61423319 / 500000000) (122846639 / 1000000000) (Real.log (1130711 / 1000000)) := by
  have h := reflection_log_8611_neg
  have he : Real.log (1130711 / 1000000) = -Real.log (1000000 / 1130711) := by
    rw [show ((1130711 / 1000000) : ℝ) = ((1000000 / 1130711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8612_neg : (70039821 / 500000000) ≤ -Real.log (869289 / 1000000) ∧
    -Real.log (869289 / 1000000) ≤ (140079643 / 1000000000) := by
  have h := checkLog_sound (w := (130711 / 1869289)) (n := 12)
    (lo := (70039821 / 500000000)) (hi := (140079643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 869289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 869289) = 1/(869289 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8612 : Bounds (-140079643 / 1000000000) (-70039821 / 500000000) (Real.log (869289 / 1000000)) := by
  have h := reflection_log_8612_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8613_neg : (30825721 / 250000000) ≤ -Real.log (1000000 / 1131227) ∧
    -Real.log (1000000 / 1131227) ≤ (24660577 / 200000000) := by
  have h := checkLog_sound (w := (131227 / 2131227)) (n := 12)
    (lo := (30825721 / 250000000)) (hi := (24660577 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1131227 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1131227 / 1000000) = 1/(1000000 / 1131227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8613 : Bounds (30825721 / 250000000) (24660577 / 200000000) (Real.log (1131227 / 1000000)) := by
  have h := reflection_log_8613_neg
  have he : Real.log (1131227 / 1000000) = -Real.log (1000000 / 1131227) := by
    rw [show ((1131227 / 1000000) : ℝ) = ((1000000 / 1131227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8614_neg : (140673407 / 1000000000) ≤ -Real.log (868773 / 1000000) ∧
    -Real.log (868773 / 1000000) ≤ (1099011 / 7812500) := by
  have h := checkLog_sound (w := (131227 / 1868773)) (n := 12)
    (lo := (140673407 / 1000000000)) (hi := (1099011 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 868773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 868773) = 1/(868773 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8614 : Bounds (-1099011 / 7812500) (-140673407 / 1000000000) (Real.log (868773 / 1000000)) := by
  have h := reflection_log_8614_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8615_neg : (17370523 / 1000000000) ≤ -Real.log (982779474471 / 1000000000000) ∧
    -Real.log (982779474471 / 1000000000000) ≤ (4342631 / 250000000) := by
  have h := checkLog_sound (w := (17220525529 / 1982779474471)) (n := 12)
    (lo := (17370523 / 1000000000)) (hi := (4342631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982779474471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982779474471) = 1/(982779474471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8615 : Bounds (-4342631 / 250000000) (-17370523 / 1000000000) (Real.log (982779474471 / 1000000000000)) := by
  have h := reflection_log_8615_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8616_neg : (4308251 / 250000000) ≤ -Real.log (982914634479 / 1000000000000) ∧
    -Real.log (982914634479 / 1000000000000) ≤ (3446601 / 200000000) := by
  have h := checkLog_sound (w := (17085365521 / 1982914634479)) (n := 12)
    (lo := (4308251 / 250000000)) (hi := (3446601 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982914634479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982914634479) = 1/(982914634479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8616 : Bounds (-3446601 / 200000000) (-4308251 / 250000000) (Real.log (982914634479 / 1000000000000)) := by
  have h := reflection_log_8616_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8617_neg : (262926281 / 1000000000) ≤ -Real.log (500000000000 / 650365413573) ∧
    -Real.log (500000000000 / 650365413573) ≤ (131463141 / 500000000) := by
  have h := checkLog_sound (w := (150365413573 / 1150365413573)) (n := 12)
    (lo := (262926281 / 1000000000)) (hi := (131463141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((650365413573 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(650365413573 / 500000000000) = 1/(500000000000 / 650365413573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8617 : Bounds (262926281 / 1000000000) (131463141 / 500000000) (Real.log (650365413573 / 500000000000)) := by
  have h := reflection_log_8617_neg
  have he : Real.log (650365413573 / 500000000000) = -Real.log (500000000000 / 650365413573) := by
    rw [show ((650365413573 / 500000000000) : ℝ) = ((500000000000 / 650365413573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8618_neg : (263976291 / 1000000000) ≤ -Real.log (100000000000 / 130209732577) ∧
    -Real.log (100000000000 / 130209732577) ≤ (65994073 / 250000000) := by
  have h := checkLog_sound (w := (30209732577 / 230209732577)) (n := 12)
    (lo := (263976291 / 1000000000)) (hi := (65994073 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((130209732577 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(130209732577 / 100000000000) = 1/(100000000000 / 130209732577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8618 : Bounds (263976291 / 1000000000) (65994073 / 250000000) (Real.log (130209732577 / 100000000000)) := by
  have h := reflection_log_8618_neg
  have he : Real.log (130209732577 / 100000000000) = -Real.log (100000000000 / 130209732577) := by
    rw [show ((130209732577 / 100000000000) : ℝ) = ((100000000000 / 130209732577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8619_neg : (132250163 / 250000000) ≤ -Real.log (500000000000 / 848617666891) ∧
    -Real.log (500000000000 / 848617666891) ≤ (529000653 / 1000000000) := by
  have h := checkLog_sound (w := (348617666891 / 1348617666891)) (n := 12)
    (lo := (132250163 / 250000000)) (hi := (529000653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((848617666891 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(848617666891 / 500000000000) = 1/(500000000000 / 848617666891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8619 : Bounds (132250163 / 250000000) (529000653 / 1000000000) (Real.log (848617666891 / 500000000000)) := by
  have h := reflection_log_8619_neg
  have he : Real.log (848617666891 / 500000000000) = -Real.log (500000000000 / 848617666891) := by
    rw [show ((848617666891 / 500000000000) : ℝ) = ((500000000000 / 848617666891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8620_neg : (66259051 / 125000000) ≤ -Real.log (250000000000 / 424763832659) ∧
    -Real.log (250000000000 / 424763832659) ≤ (530072409 / 1000000000) := by
  have h := checkLog_sound (w := (174763832659 / 674763832659)) (n := 12)
    (lo := (66259051 / 125000000)) (hi := (530072409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((424763832659 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(424763832659 / 250000000000) = 1/(250000000000 / 424763832659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8620 : Bounds (66259051 / 125000000) (530072409 / 1000000000) (Real.log (424763832659 / 250000000000)) := by
  have h := reflection_log_8620_neg
  have he : Real.log (424763832659 / 250000000000) = -Real.log (250000000000 / 424763832659) := by
    rw [show ((424763832659 / 250000000000) : ℝ) = ((250000000000 / 424763832659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8621_neg : (3604919 / 15625000) ≤ -Real.log (2000 / 2519) ∧
    -Real.log (2000 / 2519) ≤ (230714817 / 1000000000) := by
  have h := checkLog_sound (w := (519 / 4519)) (n := 12)
    (lo := (3604919 / 15625000)) (hi := (230714817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2519 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2519 / 2000) = 1/(2000 / 2519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8621 : Bounds (3604919 / 15625000) (230714817 / 1000000000) (Real.log (2519 / 2000)) := by
  have h := reflection_log_8621_neg
  have he : Real.log (2519 / 2000) = -Real.log (2000 / 2519) := by
    rw [show ((2519 / 2000) : ℝ) = ((2000 / 2519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8622_neg : (60085929 / 200000000) ≤ -Real.log (1481 / 2000) ∧
    -Real.log (1481 / 2000) ≤ (150214823 / 500000000) := by
  have h := checkLog_sound (w := (519 / 3481)) (n := 12)
    (lo := (60085929 / 200000000)) (hi := (150214823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1481) = 1/(1481 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8622 : Bounds (-150214823 / 500000000) (-60085929 / 200000000) (Real.log (1481 / 2000)) := by
  have h := reflection_log_8622_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8623_neg : (129733 / 500000000) ≤ -Real.log (2000000 / 2000519) ∧
    -Real.log (2000000 / 2000519) ≤ (259467 / 1000000000) := by
  have h := checkLog_sound (w := (519 / 4000519)) (n := 12)
    (lo := (129733 / 500000000)) (hi := (259467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000519 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000519 / 2000000) = 1/(2000000 / 2000519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8623 : Bounds (129733 / 500000000) (259467 / 1000000000) (Real.log (2000519 / 2000000)) := by
  have h := reflection_log_8623_neg
  have he : Real.log (2000519 / 2000000) = -Real.log (2000000 / 2000519) := by
    rw [show ((2000519 / 2000000) : ℝ) = ((2000000 / 2000519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8624_neg : (259533 / 1000000000) ≤ -Real.log (1999481 / 2000000) ∧
    -Real.log (1999481 / 2000000) ≤ (129767 / 500000000) := by
  have h := checkLog_sound (w := (519 / 3999481)) (n := 12)
    (lo := (259533 / 1000000000)) (hi := (129767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999481) = 1/(1999481 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8624 : Bounds (-129767 / 500000000) (-259533 / 1000000000) (Real.log (1999481 / 2000000)) := by
  have h := reflection_log_8624_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8625_neg : (123075671 / 1000000000) ≤ -Real.log (100000 / 113097) ∧
    -Real.log (100000 / 113097) ≤ (15384459 / 125000000) := by
  have h := checkLog_sound (w := (13097 / 213097)) (n := 12)
    (lo := (123075671 / 1000000000)) (hi := (15384459 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113097 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(113097 / 100000) = 1/(100000 / 113097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8625 : Bounds (123075671 / 1000000000) (15384459 / 125000000) (Real.log (113097 / 100000)) := by
  have h := reflection_log_8625_neg
  have he : Real.log (113097 / 100000) = -Real.log (100000 / 113097) := by
    rw [show ((113097 / 100000) : ℝ) = ((100000 / 113097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8626_neg : (140377631 / 1000000000) ≤ -Real.log (86903 / 100000) ∧
    -Real.log (86903 / 100000) ≤ (4386801 / 31250000) := by
  have h := checkLog_sound (w := (13097 / 186903)) (n := 12)
    (lo := (140377631 / 1000000000)) (hi := (4386801 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 86903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 86903) = 1/(86903 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8626 : Bounds (-4386801 / 31250000) (-140377631 / 1000000000) (Real.log (86903 / 100000)) := by
  have h := reflection_log_8626_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8627_neg : (123531813 / 1000000000) ≤ -Real.log (500000 / 565743) ∧
    -Real.log (500000 / 565743) ≤ (61765907 / 500000000) := by
  have h := checkLog_sound (w := (65743 / 1065743)) (n := 12)
    (lo := (123531813 / 1000000000)) (hi := (61765907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((565743 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(565743 / 500000) = 1/(500000 / 565743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8627 : Bounds (123531813 / 1000000000) (61765907 / 500000000) (Real.log (565743 / 500000)) := by
  have h := reflection_log_8627_neg
  have he : Real.log (565743 / 500000) = -Real.log (500000 / 565743) := by
    rw [show ((565743 / 500000) : ℝ) = ((500000 / 565743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8628_neg : (140971573 / 1000000000) ≤ -Real.log (434257 / 500000) ∧
    -Real.log (434257 / 500000) ≤ (70485787 / 500000000) := by
  have h := checkLog_sound (w := (65743 / 934257)) (n := 12)
    (lo := (140971573 / 1000000000)) (hi := (70485787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 434257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 434257) = 1/(434257 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8628 : Bounds (-70485787 / 500000000) (-140971573 / 1000000000) (Real.log (434257 / 500000)) := by
  have h := reflection_log_8628_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8629_neg : (217997 / 12500000) ≤ -Real.log (245677857951 / 250000000000) ∧
    -Real.log (245677857951 / 250000000000) ≤ (17439761 / 1000000000) := by
  have h := checkLog_sound (w := (4322142049 / 495677857951)) (n := 12)
    (lo := (217997 / 12500000)) (hi := (17439761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245677857951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245677857951) = 1/(245677857951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8629 : Bounds (-17439761 / 1000000000) (-217997 / 12500000) (Real.log (245677857951 / 250000000000)) := by
  have h := reflection_log_8629_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8630_neg : (432549 / 25000000) ≤ -Real.log (9828468591 / 10000000000) ∧
    -Real.log (9828468591 / 10000000000) ≤ (17301961 / 1000000000) := by
  have h := checkLog_sound (w := (171531409 / 19828468591)) (n := 12)
    (lo := (432549 / 25000000)) (hi := (17301961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9828468591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9828468591) = 1/(9828468591 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8630 : Bounds (-17301961 / 1000000000) (-432549 / 25000000) (Real.log (9828468591 / 10000000000)) := by
  have h := reflection_log_8630_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8631_neg : (263453303 / 1000000000) ≤ -Real.log (250000000000 / 325354130467) ∧
    -Real.log (250000000000 / 325354130467) ≤ (32931663 / 125000000) := by
  have h := checkLog_sound (w := (75354130467 / 575354130467)) (n := 12)
    (lo := (263453303 / 1000000000)) (hi := (32931663 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((325354130467 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(325354130467 / 250000000000) = 1/(250000000000 / 325354130467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8631 : Bounds (263453303 / 1000000000) (32931663 / 125000000) (Real.log (325354130467 / 250000000000)) := by
  have h := reflection_log_8631_neg
  have he : Real.log (325354130467 / 250000000000) = -Real.log (250000000000 / 325354130467) := by
    rw [show ((325354130467 / 250000000000) : ℝ) = ((250000000000 / 325354130467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8632_neg : (132251693 / 500000000) ≤ -Real.log (50000000000 / 65139191769) ∧
    -Real.log (50000000000 / 65139191769) ≤ (264503387 / 1000000000) := by
  have h := checkLog_sound (w := (15139191769 / 115139191769)) (n := 12)
    (lo := (132251693 / 500000000)) (hi := (264503387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65139191769 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(65139191769 / 50000000000) = 1/(50000000000 / 65139191769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8632 : Bounds (132251693 / 500000000) (264503387 / 1000000000) (Real.log (65139191769 / 50000000000)) := by
  have h := reflection_log_8632_neg
  have he : Real.log (65139191769 / 50000000000) = -Real.log (50000000000 / 65139191769) := by
    rw [show ((65139191769 / 50000000000) : ℝ) = ((50000000000 / 65139191769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8633_neg : (66259051 / 125000000) ≤ -Real.log (500000000000 / 849527665317) ∧
    -Real.log (500000000000 / 849527665317) ≤ (530072409 / 1000000000) := by
  have h := checkLog_sound (w := (349527665317 / 1349527665317)) (n := 12)
    (lo := (66259051 / 125000000)) (hi := (530072409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((849527665317 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(849527665317 / 500000000000) = 1/(500000000000 / 849527665317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8633 : Bounds (66259051 / 125000000) (530072409 / 1000000000) (Real.log (849527665317 / 500000000000)) := by
  have h := reflection_log_8633_neg
  have he : Real.log (849527665317 / 500000000000) = -Real.log (500000000000 / 849527665317) := by
    rw [show ((849527665317 / 500000000000) : ℝ) = ((500000000000 / 849527665317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8634_neg : (265572231 / 500000000) ≤ -Real.log (500000000000 / 850438892641) ∧
    -Real.log (500000000000 / 850438892641) ≤ (531144463 / 1000000000) := by
  have h := checkLog_sound (w := (350438892641 / 1350438892641)) (n := 12)
    (lo := (265572231 / 500000000)) (hi := (531144463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((850438892641 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(850438892641 / 500000000000) = 1/(500000000000 / 850438892641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8634 : Bounds (265572231 / 500000000) (531144463 / 1000000000) (Real.log (850438892641 / 500000000000)) := by
  have h := reflection_log_8634_neg
  have he : Real.log (850438892641 / 500000000000) = -Real.log (500000000000 / 850438892641) := by
    rw [show ((850438892641 / 500000000000) : ℝ) = ((500000000000 / 850438892641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8635_neg : (5777793 / 25000000) ≤ -Real.log (50 / 63) ∧
    -Real.log (50 / 63) ≤ (231111721 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 113)) (n := 12)
    (lo := (5777793 / 25000000)) (hi := (231111721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63 / 50) = 1/(50 / 63) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8635 : Bounds (5777793 / 25000000) (231111721 / 1000000000) (Real.log (63 / 50)) := by
  have h := reflection_log_8635_neg
  have he : Real.log (63 / 50) = -Real.log (50 / 63) := by
    rw [show ((63 / 50) : ℝ) = ((50 / 63) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8636_neg : (75276273 / 250000000) ≤ -Real.log (37 / 50) ∧
    -Real.log (37 / 50) ≤ (301105093 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 87)) (n := 12)
    (lo := (75276273 / 250000000)) (hi := (301105093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 37) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50 / 37) = 1/(37 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8636 : Bounds (-301105093 / 1000000000) (-75276273 / 250000000) (Real.log (37 / 50)) := by
  have h := reflection_log_8636_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8637_neg : (129983 / 500000000) ≤ -Real.log (50000 / 50013) ∧
    -Real.log (50000 / 50013) ≤ (259967 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 100013)) (n := 12)
    (lo := (129983 / 500000000)) (hi := (259967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50013 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50013 / 50000) = 1/(50000 / 50013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8637 : Bounds (129983 / 500000000) (259967 / 1000000000) (Real.log (50013 / 50000)) := by
  have h := reflection_log_8637_neg
  have he : Real.log (50013 / 50000) = -Real.log (50000 / 50013) := by
    rw [show ((50013 / 50000) : ℝ) = ((50000 / 50013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8638_neg : (260033 / 1000000000) ≤ -Real.log (49987 / 50000) ∧
    -Real.log (49987 / 50000) ≤ (130017 / 500000000) := by
  have h := checkLog_sound (w := (13 / 99987)) (n := 12)
    (lo := (260033 / 1000000000)) (hi := (130017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 49987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 49987) = 1/(49987 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8638 : Bounds (-130017 / 500000000) (-260033 / 1000000000) (Real.log (49987 / 50000)) := by
  have h := reflection_log_8638_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8639_neg : (30826163 / 250000000) ≤ -Real.log (1000000 / 1131229) ∧
    -Real.log (1000000 / 1131229) ≤ (123304653 / 1000000000) := by
  have h := checkLog_sound (w := (131229 / 2131229)) (n := 12)
    (lo := (30826163 / 250000000)) (hi := (123304653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1131229 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1131229 / 1000000) = 1/(1000000 / 1131229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8639 : Bounds (30826163 / 250000000) (123304653 / 1000000000) (Real.log (1131229 / 1000000)) := by
  have h := reflection_log_8639_neg
  have he : Real.log (1131229 / 1000000) = -Real.log (1000000 / 1131229) := by
    rw [show ((1131229 / 1000000) : ℝ) = ((1000000 / 1131229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0135 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8640_neg : (140675709 / 1000000000) ≤ -Real.log (868771 / 1000000) ∧
    -Real.log (868771 / 1000000) ≤ (14067571 / 100000000) := by
  have h := checkLog_sound (w := (131229 / 1868771)) (n := 12)
    (lo := (140675709 / 1000000000)) (hi := (14067571 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 868771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 868771) = 1/(868771 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8640 : Bounds (-14067571 / 100000000) (-140675709 / 1000000000) (Real.log (868771 / 1000000)) := by
  have h := reflection_log_8640_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8641_neg : (30940393 / 250000000) ≤ -Real.log (500000 / 565873) ∧
    -Real.log (500000 / 565873) ≤ (123761573 / 1000000000) := by
  have h := checkLog_sound (w := (65873 / 1065873)) (n := 12)
    (lo := (30940393 / 250000000)) (hi := (123761573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((565873 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(565873 / 500000) = 1/(500000 / 565873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8641 : Bounds (30940393 / 250000000) (123761573 / 1000000000) (Real.log (565873 / 500000)) := by
  have h := reflection_log_8641_neg
  have he : Real.log (565873 / 500000) = -Real.log (500000 / 565873) := by
    rw [show ((565873 / 500000) : ℝ) = ((500000 / 565873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8642_neg : (7063549 / 50000000) ≤ -Real.log (434127 / 500000) ∧
    -Real.log (434127 / 500000) ≤ (141270981 / 1000000000) := by
  have h := checkLog_sound (w := (65873 / 934127)) (n := 12)
    (lo := (7063549 / 50000000)) (hi := (141270981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 434127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 434127) = 1/(434127 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8642 : Bounds (-141270981 / 1000000000) (-7063549 / 50000000) (Real.log (434127 / 500000)) := by
  have h := reflection_log_8642_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8643_neg : (17509407 / 1000000000) ≤ -Real.log (245660747871 / 250000000000) ∧
    -Real.log (245660747871 / 250000000000) ≤ (547169 / 31250000) := by
  have h := checkLog_sound (w := (4339252129 / 495660747871)) (n := 12)
    (lo := (17509407 / 1000000000)) (hi := (547169 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245660747871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245660747871) = 1/(245660747871 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8643 : Bounds (-547169 / 31250000) (-17509407 / 1000000000) (Real.log (245660747871 / 250000000000)) := by
  have h := reflection_log_8643_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8644_neg : (17371057 / 1000000000) ≤ -Real.log (982778949559 / 1000000000000) ∧
    -Real.log (982778949559 / 1000000000000) ≤ (8685529 / 500000000) := by
  have h := checkLog_sound (w := (17221050441 / 1982778949559)) (n := 12)
    (lo := (17371057 / 1000000000)) (hi := (8685529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982778949559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982778949559) = 1/(982778949559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8644 : Bounds (-8685529 / 500000000) (-17371057 / 1000000000) (Real.log (982778949559 / 1000000000000)) := by
  have h := reflection_log_8644_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8645_neg : (131990181 / 500000000) ≤ -Real.log (125000000000 / 162762828179) ∧
    -Real.log (125000000000 / 162762828179) ≤ (263980363 / 1000000000) := by
  have h := checkLog_sound (w := (37762828179 / 287762828179)) (n := 12)
    (lo := (131990181 / 500000000)) (hi := (263980363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162762828179 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162762828179 / 125000000000) = 1/(125000000000 / 162762828179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8645 : Bounds (131990181 / 500000000) (263980363 / 1000000000) (Real.log (162762828179 / 125000000000)) := by
  have h := reflection_log_8645_neg
  have he : Real.log (162762828179 / 125000000000) = -Real.log (125000000000 / 162762828179) := by
    rw [show ((162762828179 / 125000000000) : ℝ) = ((125000000000 / 162762828179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8646_neg : (265032553 / 1000000000) ≤ -Real.log (15625000000 / 20366771993) ∧
    -Real.log (15625000000 / 20366771993) ≤ (132516277 / 500000000) := by
  have h := checkLog_sound (w := (4741771993 / 35991771993)) (n := 12)
    (lo := (265032553 / 1000000000)) (hi := (132516277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20366771993 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20366771993 / 15625000000) = 1/(15625000000 / 20366771993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8646 : Bounds (265032553 / 1000000000) (132516277 / 500000000) (Real.log (20366771993 / 15625000000)) := by
  have h := reflection_log_8646_neg
  have he : Real.log (20366771993 / 15625000000) = -Real.log (15625000000 / 20366771993) := by
    rw [show ((20366771993 / 15625000000) : ℝ) = ((15625000000 / 20366771993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8647_neg : (265572231 / 500000000) ≤ -Real.log (3125000000 / 5315243079) ∧
    -Real.log (3125000000 / 5315243079) ≤ (531144463 / 1000000000) := by
  have h := checkLog_sound (w := (2190243079 / 8440243079)) (n := 12)
    (lo := (265572231 / 500000000)) (hi := (531144463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5315243079 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5315243079 / 3125000000) = 1/(3125000000 / 5315243079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8647 : Bounds (265572231 / 500000000) (531144463 / 1000000000) (Real.log (5315243079 / 3125000000)) := by
  have h := reflection_log_8647_neg
  have he : Real.log (5315243079 / 3125000000) = -Real.log (3125000000 / 5315243079) := by
    rw [show ((5315243079 / 3125000000) : ℝ) = ((3125000000 / 5315243079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8648_neg : (532216813 / 1000000000) ≤ -Real.log (62500000000 / 106418918919) ∧
    -Real.log (62500000000 / 106418918919) ≤ (266108407 / 500000000) := by
  have h := checkLog_sound (w := (43918918919 / 168918918919)) (n := 12)
    (lo := (532216813 / 1000000000)) (hi := (266108407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((106418918919 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(106418918919 / 62500000000) = 1/(62500000000 / 106418918919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8648 : Bounds (532216813 / 1000000000) (266108407 / 500000000) (Real.log (106418918919 / 62500000000)) := by
  have h := reflection_log_8648_neg
  have he : Real.log (106418918919 / 62500000000) = -Real.log (62500000000 / 106418918919) := by
    rw [show ((106418918919 / 62500000000) : ℝ) = ((62500000000 / 106418918919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8649_neg : (231508467 / 1000000000) ≤ -Real.log (2000 / 2521) ∧
    -Real.log (2000 / 2521) ≤ (57877117 / 250000000) := by
  have h := checkLog_sound (w := (521 / 4521)) (n := 12)
    (lo := (231508467 / 1000000000)) (hi := (57877117 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2521 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2521 / 2000) = 1/(2000 / 2521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8649 : Bounds (231508467 / 1000000000) (57877117 / 250000000) (Real.log (2521 / 2000)) := by
  have h := reflection_log_8649_neg
  have he : Real.log (2521 / 2000) = -Real.log (2000 / 2521) := by
    rw [show ((2521 / 2000) : ℝ) = ((2000 / 2521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8650_neg : (75445249 / 250000000) ≤ -Real.log (1479 / 2000) ∧
    -Real.log (1479 / 2000) ≤ (301780997 / 1000000000) := by
  have h := checkLog_sound (w := (521 / 3479)) (n := 12)
    (lo := (75445249 / 250000000)) (hi := (301780997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1479) = 1/(1479 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8650 : Bounds (-301780997 / 1000000000) (-75445249 / 250000000) (Real.log (1479 / 2000)) := by
  have h := reflection_log_8650_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8651_neg : (130233 / 500000000) ≤ -Real.log (2000000 / 2000521) ∧
    -Real.log (2000000 / 2000521) ≤ (260467 / 1000000000) := by
  have h := checkLog_sound (w := (521 / 4000521)) (n := 12)
    (lo := (130233 / 500000000)) (hi := (260467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000521 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000521 / 2000000) = 1/(2000000 / 2000521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8651 : Bounds (130233 / 500000000) (260467 / 1000000000) (Real.log (2000521 / 2000000)) := by
  have h := reflection_log_8651_neg
  have he : Real.log (2000521 / 2000000) = -Real.log (2000000 / 2000521) := by
    rw [show ((2000521 / 2000000) : ℝ) = ((2000000 / 2000521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8652_neg : (260533 / 1000000000) ≤ -Real.log (1999479 / 2000000) ∧
    -Real.log (1999479 / 2000000) ≤ (130267 / 500000000) := by
  have h := checkLog_sound (w := (521 / 3999479)) (n := 12)
    (lo := (260533 / 1000000000)) (hi := (130267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999479) = 1/(1999479 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8652 : Bounds (-130267 / 500000000) (-260533 / 1000000000) (Real.log (1999479 / 2000000)) := by
  have h := reflection_log_8652_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8653_neg : (6176679 / 50000000) ≤ -Real.log (31250 / 35359) ∧
    -Real.log (31250 / 35359) ≤ (123533581 / 1000000000) := by
  have h := checkLog_sound (w := (4109 / 66609)) (n := 12)
    (lo := (6176679 / 50000000)) (hi := (123533581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35359 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35359 / 31250) = 1/(31250 / 35359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8653 : Bounds (6176679 / 50000000) (123533581 / 1000000000) (Real.log (35359 / 31250)) := by
  have h := reflection_log_8653_neg
  have he : Real.log (35359 / 31250) = -Real.log (31250 / 35359) := by
    rw [show ((35359 / 31250) : ℝ) = ((31250 / 35359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8654_neg : (35243469 / 250000000) ≤ -Real.log (27141 / 31250) ∧
    -Real.log (27141 / 31250) ≤ (140973877 / 1000000000) := by
  have h := checkLog_sound (w := (4109 / 58391)) (n := 12)
    (lo := (35243469 / 250000000)) (hi := (140973877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 27141) = 1/(27141 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8654 : Bounds (-140973877 / 1000000000) (-35243469 / 250000000) (Real.log (27141 / 31250)) := by
  have h := reflection_log_8654_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8655_neg : (1549891 / 12500000) ≤ -Real.log (500000 / 566003) ∧
    -Real.log (500000 / 566003) ≤ (123991281 / 1000000000) := by
  have h := checkLog_sound (w := (66003 / 1066003)) (n := 12)
    (lo := (1549891 / 12500000)) (hi := (123991281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((566003 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(566003 / 500000) = 1/(500000 / 566003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8655 : Bounds (1549891 / 12500000) (123991281 / 1000000000) (Real.log (566003 / 500000)) := by
  have h := reflection_log_8655_neg
  have he : Real.log (566003 / 500000) = -Real.log (500000 / 566003) := by
    rw [show ((566003 / 500000) : ℝ) = ((500000 / 566003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8656_neg : (35392619 / 250000000) ≤ -Real.log (433997 / 500000) ∧
    -Real.log (433997 / 500000) ≤ (141570477 / 1000000000) := by
  have h := checkLog_sound (w := (66003 / 933997)) (n := 12)
    (lo := (35392619 / 250000000)) (hi := (141570477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 433997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 433997) = 1/(433997 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8656 : Bounds (-141570477 / 1000000000) (-35392619 / 250000000) (Real.log (433997 / 500000)) := by
  have h := reflection_log_8656_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8657_neg : (4394799 / 250000000) ≤ -Real.log (245643603991 / 250000000000) ∧
    -Real.log (245643603991 / 250000000000) ≤ (17579197 / 1000000000) := by
  have h := checkLog_sound (w := (4356396009 / 495643603991)) (n := 12)
    (lo := (4394799 / 250000000)) (hi := (17579197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245643603991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245643603991) = 1/(245643603991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8657 : Bounds (-17579197 / 1000000000) (-4394799 / 250000000) (Real.log (245643603991 / 250000000000)) := by
  have h := reflection_log_8657_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8658_neg : (3488059 / 200000000) ≤ -Real.log (959678619 / 976562500) ∧
    -Real.log (959678619 / 976562500) ≤ (2180037 / 125000000) := by
  have h := checkLog_sound (w := (16883881 / 1936241119)) (n := 12)
    (lo := (3488059 / 200000000)) (hi := (2180037 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 959678619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 959678619) = 1/(959678619 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8658 : Bounds (-2180037 / 125000000) (-3488059 / 200000000) (Real.log (959678619 / 976562500)) := by
  have h := reflection_log_8658_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8659_neg : (264507457 / 1000000000) ≤ -Real.log (250000000000 / 325697284551) ∧
    -Real.log (250000000000 / 325697284551) ≤ (132253729 / 500000000) := by
  have h := checkLog_sound (w := (75697284551 / 575697284551)) (n := 12)
    (lo := (264507457 / 1000000000)) (hi := (132253729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((325697284551 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(325697284551 / 250000000000) = 1/(250000000000 / 325697284551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8659 : Bounds (264507457 / 1000000000) (132253729 / 500000000) (Real.log (325697284551 / 250000000000)) := by
  have h := reflection_log_8659_neg
  have he : Real.log (325697284551 / 250000000000) = -Real.log (250000000000 / 325697284551) := by
    rw [show ((325697284551 / 250000000000) : ℝ) = ((250000000000 / 325697284551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8660_neg : (66390439 / 250000000) ≤ -Real.log (250000000000 / 326040848209) ∧
    -Real.log (250000000000 / 326040848209) ≤ (265561757 / 1000000000) := by
  have h := checkLog_sound (w := (76040848209 / 576040848209)) (n := 12)
    (lo := (66390439 / 250000000)) (hi := (265561757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326040848209 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326040848209 / 250000000000) = 1/(250000000000 / 326040848209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8660 : Bounds (66390439 / 250000000) (265561757 / 1000000000) (Real.log (326040848209 / 250000000000)) := by
  have h := reflection_log_8660_neg
  have he : Real.log (326040848209 / 250000000000) = -Real.log (250000000000 / 326040848209) := by
    rw [show ((326040848209 / 250000000000) : ℝ) = ((250000000000 / 326040848209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8661_neg : (532216813 / 1000000000) ≤ -Real.log (500000000000 / 851351351351) ∧
    -Real.log (500000000000 / 851351351351) ≤ (266108407 / 500000000) := by
  have h := checkLog_sound (w := (351351351351 / 1351351351351)) (n := 12)
    (lo := (532216813 / 1000000000)) (hi := (266108407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851351351351 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851351351351 / 500000000000) = 1/(500000000000 / 851351351351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8661 : Bounds (532216813 / 1000000000) (266108407 / 500000000) (Real.log (851351351351 / 500000000000)) := by
  have h := reflection_log_8661_neg
  have he : Real.log (851351351351 / 500000000000) = -Real.log (500000000000 / 851351351351) := by
    rw [show ((851351351351 / 500000000000) : ℝ) = ((500000000000 / 851351351351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8662_neg : (66661183 / 125000000) ≤ -Real.log (500000000000 / 852265043949) ∧
    -Real.log (500000000000 / 852265043949) ≤ (106657893 / 200000000) := by
  have h := checkLog_sound (w := (352265043949 / 1352265043949)) (n := 12)
    (lo := (66661183 / 125000000)) (hi := (106657893 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((852265043949 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(852265043949 / 500000000000) = 1/(500000000000 / 852265043949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8662 : Bounds (66661183 / 125000000) (106657893 / 200000000) (Real.log (852265043949 / 500000000000)) := by
  have h := reflection_log_8662_neg
  have he : Real.log (852265043949 / 500000000000) = -Real.log (500000000000 / 852265043949) := by
    rw [show ((852265043949 / 500000000000) : ℝ) = ((500000000000 / 852265043949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8663_neg : (7247033 / 31250000) ≤ -Real.log (1000 / 1261) ∧
    -Real.log (1000 / 1261) ≤ (231905057 / 1000000000) := by
  have h := checkLog_sound (w := (261 / 2261)) (n := 12)
    (lo := (7247033 / 31250000)) (hi := (231905057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1261 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1261 / 1000) = 1/(1000 / 1261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8663 : Bounds (7247033 / 31250000) (231905057 / 1000000000) (Real.log (1261 / 1000)) := by
  have h := reflection_log_8663_neg
  have he : Real.log (1261 / 1000) = -Real.log (1000 / 1261) := by
    rw [show ((1261 / 1000) : ℝ) = ((1000 / 1261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8664_neg : (151228679 / 500000000) ≤ -Real.log (739 / 1000) ∧
    -Real.log (739 / 1000) ≤ (302457359 / 1000000000) := by
  have h := checkLog_sound (w := (261 / 1739)) (n := 12)
    (lo := (151228679 / 500000000)) (hi := (302457359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 739) = 1/(739 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8664 : Bounds (-302457359 / 1000000000) (-151228679 / 500000000) (Real.log (739 / 1000)) := by
  have h := reflection_log_8664_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8665_neg : (52193 / 200000000) ≤ -Real.log (1000000 / 1000261) ∧
    -Real.log (1000000 / 1000261) ≤ (130483 / 500000000) := by
  have h := checkLog_sound (w := (261 / 2000261)) (n := 12)
    (lo := (52193 / 200000000)) (hi := (130483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000261 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000261 / 1000000) = 1/(1000000 / 1000261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8665 : Bounds (52193 / 200000000) (130483 / 500000000) (Real.log (1000261 / 1000000)) := by
  have h := reflection_log_8665_neg
  have he : Real.log (1000261 / 1000000) = -Real.log (1000000 / 1000261) := by
    rw [show ((1000261 / 1000000) : ℝ) = ((1000000 / 1000261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8666_neg : (130517 / 500000000) ≤ -Real.log (999739 / 1000000) ∧
    -Real.log (999739 / 1000000) ≤ (52207 / 200000000) := by
  have h := checkLog_sound (w := (261 / 1999739)) (n := 12)
    (lo := (130517 / 500000000)) (hi := (52207 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999739) = 1/(999739 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8666 : Bounds (-52207 / 200000000) (-130517 / 500000000) (Real.log (999739 / 1000000)) := by
  have h := reflection_log_8666_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8667_neg : (15470307 / 125000000) ≤ -Real.log (1000000 / 1131747) ∧
    -Real.log (1000000 / 1131747) ≤ (123762457 / 1000000000) := by
  have h := checkLog_sound (w := (131747 / 2131747)) (n := 12)
    (lo := (15470307 / 125000000)) (hi := (123762457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1131747 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1131747 / 1000000) = 1/(1000000 / 1131747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8667 : Bounds (15470307 / 125000000) (123762457 / 1000000000) (Real.log (1131747 / 1000000)) := by
  have h := reflection_log_8667_neg
  have he : Real.log (1131747 / 1000000) = -Real.log (1000000 / 1131747) := by
    rw [show ((1131747 / 1000000) : ℝ) = ((1000000 / 1131747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8668_neg : (35318033 / 250000000) ≤ -Real.log (868253 / 1000000) ∧
    -Real.log (868253 / 1000000) ≤ (141272133 / 1000000000) := by
  have h := checkLog_sound (w := (131747 / 1868253)) (n := 12)
    (lo := (35318033 / 250000000)) (hi := (141272133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 868253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 868253) = 1/(868253 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8668 : Bounds (-141272133 / 1000000000) (-35318033 / 250000000) (Real.log (868253 / 1000000)) := by
  have h := reflection_log_8668_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8669_neg : (124220051 / 1000000000) ≤ -Real.log (200000 / 226453) ∧
    -Real.log (200000 / 226453) ≤ (31055013 / 250000000) := by
  have h := checkLog_sound (w := (26453 / 426453)) (n := 12)
    (lo := (124220051 / 1000000000)) (hi := (31055013 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226453 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226453 / 200000) = 1/(200000 / 226453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8669 : Bounds (124220051 / 1000000000) (31055013 / 250000000) (Real.log (226453 / 200000)) := by
  have h := reflection_log_8669_neg
  have he : Real.log (226453 / 200000) = -Real.log (200000 / 226453) := by
    rw [show ((226453 / 200000) : ℝ) = ((200000 / 226453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8670_neg : (14186891 / 100000000) ≤ -Real.log (173547 / 200000) ∧
    -Real.log (173547 / 200000) ≤ (141868911 / 1000000000) := by
  have h := checkLog_sound (w := (26453 / 373547)) (n := 12)
    (lo := (14186891 / 100000000)) (hi := (141868911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 173547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 173547) = 1/(173547 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8670 : Bounds (-141868911 / 1000000000) (-14186891 / 100000000) (Real.log (173547 / 200000)) := by
  have h := reflection_log_8670_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8671_neg : (17648859 / 1000000000) ≤ -Real.log (39300238791 / 40000000000) ∧
    -Real.log (39300238791 / 40000000000) ≤ (882443 / 50000000) := by
  have h := checkLog_sound (w := (699761209 / 79300238791)) (n := 12)
    (lo := (17648859 / 1000000000)) (hi := (882443 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39300238791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39300238791) = 1/(39300238791 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8671 : Bounds (-882443 / 50000000) (-17648859 / 1000000000) (Real.log (39300238791 / 40000000000)) := by
  have h := reflection_log_8671_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8672_neg : (700387 / 40000000) ≤ -Real.log (982642727991 / 1000000000000) ∧
    -Real.log (982642727991 / 1000000000000) ≤ (4377419 / 250000000) := by
  have h := checkLog_sound (w := (17357272009 / 1982642727991)) (n := 12)
    (lo := (700387 / 40000000)) (hi := (4377419 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982642727991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982642727991) = 1/(982642727991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8672 : Bounds (-4377419 / 250000000) (-700387 / 40000000) (Real.log (982642727991 / 1000000000000)) := by
  have h := reflection_log_8672_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8673_neg : (66258647 / 250000000) ≤ -Real.log (250000000000 / 325869015137) ∧
    -Real.log (250000000000 / 325869015137) ≤ (265034589 / 1000000000) := by
  have h := checkLog_sound (w := (75869015137 / 575869015137)) (n := 12)
    (lo := (66258647 / 250000000)) (hi := (265034589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((325869015137 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(325869015137 / 250000000000) = 1/(250000000000 / 325869015137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8673 : Bounds (66258647 / 250000000) (265034589 / 1000000000) (Real.log (325869015137 / 250000000000)) := by
  have h := reflection_log_8673_neg
  have he : Real.log (325869015137 / 250000000000) = -Real.log (250000000000 / 325869015137) := by
    rw [show ((325869015137 / 250000000000) : ℝ) = ((250000000000 / 325869015137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8674_neg : (266088961 / 1000000000) ≤ -Real.log (250000000000 / 326212783857) ∧
    -Real.log (250000000000 / 326212783857) ≤ (133044481 / 500000000) := by
  have h := checkLog_sound (w := (76212783857 / 576212783857)) (n := 12)
    (lo := (266088961 / 1000000000)) (hi := (133044481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326212783857 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326212783857 / 250000000000) = 1/(250000000000 / 326212783857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8674 : Bounds (266088961 / 1000000000) (133044481 / 500000000) (Real.log (326212783857 / 250000000000)) := by
  have h := reflection_log_8674_neg
  have he : Real.log (326212783857 / 250000000000) = -Real.log (250000000000 / 326212783857) := by
    rw [show ((326212783857 / 250000000000) : ℝ) = ((250000000000 / 326212783857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8675_neg : (66661183 / 125000000) ≤ -Real.log (125000000000 / 213066260987) ∧
    -Real.log (125000000000 / 213066260987) ≤ (106657893 / 200000000) := by
  have h := checkLog_sound (w := (88066260987 / 338066260987)) (n := 12)
    (lo := (66661183 / 125000000)) (hi := (106657893 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((213066260987 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(213066260987 / 125000000000) = 1/(125000000000 / 213066260987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8675 : Bounds (66661183 / 125000000) (106657893 / 200000000) (Real.log (213066260987 / 125000000000)) := by
  have h := reflection_log_8675_neg
  have he : Real.log (213066260987 / 125000000000) = -Real.log (125000000000 / 213066260987) := by
    rw [show ((213066260987 / 125000000000) : ℝ) = ((125000000000 / 213066260987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8676_neg : (106872483 / 200000000) ≤ -Real.log (500000000000 / 853179972937) ∧
    -Real.log (500000000000 / 853179972937) ≤ (33397651 / 62500000) := by
  have h := checkLog_sound (w := (353179972937 / 1353179972937)) (n := 12)
    (lo := (106872483 / 200000000)) (hi := (33397651 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((853179972937 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(853179972937 / 500000000000) = 1/(500000000000 / 853179972937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8676 : Bounds (106872483 / 200000000) (33397651 / 62500000) (Real.log (853179972937 / 500000000000)) := by
  have h := reflection_log_8676_neg
  have he : Real.log (853179972937 / 500000000000) = -Real.log (500000000000 / 853179972937) := by
    rw [show ((853179972937 / 500000000000) : ℝ) = ((500000000000 / 853179972937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8677_neg : (232301489 / 1000000000) ≤ -Real.log (2000 / 2523) ∧
    -Real.log (2000 / 2523) ≤ (23230149 / 100000000) := by
  have h := checkLog_sound (w := (523 / 4523)) (n := 12)
    (lo := (232301489 / 1000000000)) (hi := (23230149 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2523 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2523 / 2000) = 1/(2000 / 2523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8677 : Bounds (232301489 / 1000000000) (23230149 / 100000000) (Real.log (2523 / 2000)) := by
  have h := reflection_log_8677_neg
  have he : Real.log (2523 / 2000) = -Real.log (2000 / 2523) := by
    rw [show ((2523 / 2000) : ℝ) = ((2000 / 2523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8678_neg : (303134177 / 1000000000) ≤ -Real.log (1477 / 2000) ∧
    -Real.log (1477 / 2000) ≤ (151567089 / 500000000) := by
  have h := checkLog_sound (w := (523 / 3477)) (n := 12)
    (lo := (303134177 / 1000000000)) (hi := (151567089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1477) = 1/(1477 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8678 : Bounds (-151567089 / 500000000) (-303134177 / 1000000000) (Real.log (1477 / 2000)) := by
  have h := reflection_log_8678_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8679_neg : (52293 / 200000000) ≤ -Real.log (2000000 / 2000523) ∧
    -Real.log (2000000 / 2000523) ≤ (130733 / 500000000) := by
  have h := checkLog_sound (w := (523 / 4000523)) (n := 12)
    (lo := (52293 / 200000000)) (hi := (130733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000523 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000523 / 2000000) = 1/(2000000 / 2000523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8679 : Bounds (52293 / 200000000) (130733 / 500000000) (Real.log (2000523 / 2000000)) := by
  have h := reflection_log_8679_neg
  have he : Real.log (2000523 / 2000000) = -Real.log (2000000 / 2000523) := by
    rw [show ((2000523 / 2000000) : ℝ) = ((2000000 / 2000523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8680_neg : (130767 / 500000000) ≤ -Real.log (1999477 / 2000000) ∧
    -Real.log (1999477 / 2000000) ≤ (52307 / 200000000) := by
  have h := checkLog_sound (w := (523 / 3999477)) (n := 12)
    (lo := (130767 / 500000000)) (hi := (52307 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999477) = 1/(1999477 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8680 : Bounds (-52307 / 200000000) (-130767 / 500000000) (Real.log (1999477 / 2000000)) := by
  have h := reflection_log_8680_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8681_neg : (123992163 / 1000000000) ≤ -Real.log (1000000 / 1132007) ∧
    -Real.log (1000000 / 1132007) ≤ (30998041 / 250000000) := by
  have h := checkLog_sound (w := (132007 / 2132007)) (n := 12)
    (lo := (123992163 / 1000000000)) (hi := (30998041 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1132007 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1132007 / 1000000) = 1/(1000000 / 1132007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8681 : Bounds (123992163 / 1000000000) (30998041 / 250000000) (Real.log (1132007 / 1000000)) := by
  have h := reflection_log_8681_neg
  have he : Real.log (1132007 / 1000000) = -Real.log (1000000 / 1132007) := by
    rw [show ((1132007 / 1000000) : ℝ) = ((1000000 / 1132007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8682_neg : (35392907 / 250000000) ≤ -Real.log (867993 / 1000000) ∧
    -Real.log (867993 / 1000000) ≤ (141571629 / 1000000000) := by
  have h := checkLog_sound (w := (132007 / 1867993)) (n := 12)
    (lo := (35392907 / 250000000)) (hi := (141571629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 867993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 867993) = 1/(867993 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8682 : Bounds (-141571629 / 1000000000) (-35392907 / 250000000) (Real.log (867993 / 1000000)) := by
  have h := reflection_log_8682_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8683_neg : (124449653 / 1000000000) ≤ -Real.log (40000 / 45301) ∧
    -Real.log (40000 / 45301) ≤ (62224827 / 500000000) := by
  have h := checkLog_sound (w := (5301 / 85301)) (n := 12)
    (lo := (124449653 / 1000000000)) (hi := (62224827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45301 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45301 / 40000) = 1/(40000 / 45301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8683 : Bounds (124449653 / 1000000000) (62224827 / 500000000) (Real.log (45301 / 40000)) := by
  have h := reflection_log_8683_neg
  have he : Real.log (45301 / 40000) = -Real.log (40000 / 45301) := by
    rw [show ((45301 / 40000) : ℝ) = ((40000 / 45301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8684_neg : (71084293 / 500000000) ≤ -Real.log (34699 / 40000) ∧
    -Real.log (34699 / 40000) ≤ (142168587 / 1000000000) := by
  have h := checkLog_sound (w := (5301 / 74699)) (n := 12)
    (lo := (71084293 / 500000000)) (hi := (142168587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 34699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 34699) = 1/(34699 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8684 : Bounds (-142168587 / 1000000000) (-71084293 / 500000000) (Real.log (34699 / 40000)) := by
  have h := reflection_log_8684_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8685_neg : (4429733 / 250000000) ≤ -Real.log (1571899399 / 1600000000) ∧
    -Real.log (1571899399 / 1600000000) ≤ (17718933 / 1000000000) := by
  have h := checkLog_sound (w := (28100601 / 3171899399)) (n := 12)
    (lo := (4429733 / 250000000)) (hi := (17718933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1571899399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1571899399) = 1/(1571899399 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8685 : Bounds (-17718933 / 1000000000) (-4429733 / 250000000) (Real.log (1571899399 / 1600000000)) := by
  have h := reflection_log_8685_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8686_neg : (3515893 / 200000000) ≤ -Real.log (982574151951 / 1000000000000) ∧
    -Real.log (982574151951 / 1000000000000) ≤ (8789733 / 500000000) := by
  have h := checkLog_sound (w := (17425848049 / 1982574151951)) (n := 12)
    (lo := (3515893 / 200000000)) (hi := (8789733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982574151951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982574151951) = 1/(982574151951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8686 : Bounds (-8789733 / 500000000) (-3515893 / 200000000) (Real.log (982574151951 / 1000000000000)) := by
  have h := reflection_log_8686_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8687_neg : (16597737 / 62500000) ≤ -Real.log (500000000000 / 652083023711) ∧
    -Real.log (500000000000 / 652083023711) ≤ (265563793 / 1000000000) := by
  have h := checkLog_sound (w := (152083023711 / 1152083023711)) (n := 12)
    (lo := (16597737 / 62500000)) (hi := (265563793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((652083023711 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(652083023711 / 500000000000) = 1/(500000000000 / 652083023711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8687 : Bounds (16597737 / 62500000) (265563793 / 1000000000) (Real.log (652083023711 / 500000000000)) := by
  have h := reflection_log_8687_neg
  have he : Real.log (652083023711 / 500000000000) = -Real.log (500000000000 / 652083023711) := by
    rw [show ((652083023711 / 500000000000) : ℝ) = ((500000000000 / 652083023711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8688_neg : (266618239 / 1000000000) ≤ -Real.log (500000000000 / 652770973227) ∧
    -Real.log (500000000000 / 652770973227) ≤ (416591 / 1562500) := by
  have h := checkLog_sound (w := (152770973227 / 1152770973227)) (n := 12)
    (lo := (266618239 / 1000000000)) (hi := (416591 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((652770973227 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(652770973227 / 500000000000) = 1/(500000000000 / 652770973227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8688 : Bounds (266618239 / 1000000000) (416591 / 1562500) (Real.log (652770973227 / 500000000000)) := by
  have h := reflection_log_8688_neg
  have he : Real.log (652770973227 / 500000000000) = -Real.log (500000000000 / 652770973227) := by
    rw [show ((652770973227 / 500000000000) : ℝ) = ((500000000000 / 652770973227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8689_neg : (106872483 / 200000000) ≤ -Real.log (62500000000 / 106647496617) ∧
    -Real.log (62500000000 / 106647496617) ≤ (33397651 / 62500000) := by
  have h := checkLog_sound (w := (44147496617 / 169147496617)) (n := 12)
    (lo := (106872483 / 200000000)) (hi := (33397651 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((106647496617 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(106647496617 / 62500000000) = 1/(62500000000 / 106647496617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8689 : Bounds (106872483 / 200000000) (33397651 / 62500000) (Real.log (106647496617 / 62500000000)) := by
  have h := reflection_log_8689_neg
  have he : Real.log (106647496617 / 62500000000) = -Real.log (62500000000 / 106647496617) := by
    rw [show ((106647496617 / 62500000000) : ℝ) = ((62500000000 / 106647496617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8690_neg : (267717833 / 500000000) ≤ -Real.log (250000000000 / 427048070413) ∧
    -Real.log (250000000000 / 427048070413) ≤ (535435667 / 1000000000) := by
  have h := checkLog_sound (w := (177048070413 / 677048070413)) (n := 12)
    (lo := (267717833 / 500000000)) (hi := (535435667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((427048070413 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(427048070413 / 250000000000) = 1/(250000000000 / 427048070413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8690 : Bounds (267717833 / 500000000) (535435667 / 1000000000) (Real.log (427048070413 / 250000000000)) := by
  have h := reflection_log_8690_neg
  have he : Real.log (427048070413 / 250000000000) = -Real.log (250000000000 / 427048070413) := by
    rw [show ((427048070413 / 250000000000) : ℝ) = ((250000000000 / 427048070413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8691_neg : (58174441 / 250000000) ≤ -Real.log (500 / 631) ∧
    -Real.log (500 / 631) ≤ (46539553 / 200000000) := by
  have h := checkLog_sound (w := (131 / 1131)) (n := 12)
    (lo := (58174441 / 250000000)) (hi := (46539553 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((631 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(631 / 500) = 1/(500 / 631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8691 : Bounds (58174441 / 250000000) (46539553 / 200000000) (Real.log (631 / 500)) := by
  have h := reflection_log_8691_neg
  have he : Real.log (631 / 500) = -Real.log (500 / 631) := by
    rw [show ((631 / 500) : ℝ) = ((500 / 631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8692_neg : (151905727 / 500000000) ≤ -Real.log (369 / 500) ∧
    -Real.log (369 / 500) ≤ (60762291 / 200000000) := by
  have h := checkLog_sound (w := (131 / 869)) (n := 12)
    (lo := (151905727 / 500000000)) (hi := (60762291 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 369) = 1/(369 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8692 : Bounds (-60762291 / 200000000) (-151905727 / 500000000) (Real.log (369 / 500)) := by
  have h := reflection_log_8692_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8693_neg : (52393 / 200000000) ≤ -Real.log (500000 / 500131) ∧
    -Real.log (500000 / 500131) ≤ (130983 / 500000000) := by
  have h := checkLog_sound (w := (131 / 1000131)) (n := 12)
    (lo := (52393 / 200000000)) (hi := (130983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500131 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500131 / 500000) = 1/(500000 / 500131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8693 : Bounds (52393 / 200000000) (130983 / 500000000) (Real.log (500131 / 500000)) := by
  have h := reflection_log_8693_neg
  have he : Real.log (500131 / 500000) = -Real.log (500000 / 500131) := by
    rw [show ((500131 / 500000) : ℝ) = ((500000 / 500131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8694_neg : (131017 / 500000000) ≤ -Real.log (499869 / 500000) ∧
    -Real.log (499869 / 500000) ≤ (52407 / 200000000) := by
  have h := checkLog_sound (w := (131 / 999869)) (n := 12)
    (lo := (131017 / 500000000)) (hi := (52407 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499869) = 1/(499869 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8694 : Bounds (-52407 / 200000000) (-131017 / 500000000) (Real.log (499869 / 500000)) := by
  have h := reflection_log_8694_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8695_neg : (62110467 / 500000000) ≤ -Real.log (500000 / 566133) ∧
    -Real.log (500000 / 566133) ≤ (24844187 / 200000000) := by
  have h := checkLog_sound (w := (66133 / 1066133)) (n := 12)
    (lo := (62110467 / 500000000)) (hi := (24844187 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((566133 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(566133 / 500000) = 1/(500000 / 566133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8695 : Bounds (62110467 / 500000000) (24844187 / 200000000) (Real.log (566133 / 500000)) := by
  have h := reflection_log_8695_neg
  have he : Real.log (566133 / 500000) = -Real.log (500000 / 566133) := by
    rw [show ((566133 / 500000) : ℝ) = ((500000 / 566133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8696_neg : (70935031 / 500000000) ≤ -Real.log (433867 / 500000) ∧
    -Real.log (433867 / 500000) ≤ (141870063 / 1000000000) := by
  have h := checkLog_sound (w := (66133 / 933867)) (n := 12)
    (lo := (70935031 / 500000000)) (hi := (141870063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 433867) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 433867) = 1/(433867 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8696 : Bounds (-141870063 / 1000000000) (-70935031 / 500000000) (Real.log (433867 / 500000)) := by
  have h := reflection_log_8696_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8697_neg : (62339601 / 500000000) ≤ -Real.log (200000 / 226557) ∧
    -Real.log (200000 / 226557) ≤ (124679203 / 1000000000) := by
  have h := checkLog_sound (w := (26557 / 426557)) (n := 12)
    (lo := (62339601 / 500000000)) (hi := (124679203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226557 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226557 / 200000) = 1/(200000 / 226557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8697 : Bounds (62339601 / 500000000) (124679203 / 1000000000) (Real.log (226557 / 200000)) := by
  have h := reflection_log_8697_neg
  have he : Real.log (226557 / 200000) = -Real.log (200000 / 226557) := by
    rw [show ((226557 / 200000) : ℝ) = ((200000 / 226557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8698_neg : (142468351 / 1000000000) ≤ -Real.log (173443 / 200000) ∧
    -Real.log (173443 / 200000) ≤ (556517 / 3906250) := by
  have h := checkLog_sound (w := (26557 / 373443)) (n := 12)
    (lo := (142468351 / 1000000000)) (hi := (556517 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 173443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 173443) = 1/(173443 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8698 : Bounds (-556517 / 3906250) (-142468351 / 1000000000) (Real.log (173443 / 200000)) := by
  have h := reflection_log_8698_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8699_neg : (17789149 / 1000000000) ≤ -Real.log (39294725751 / 40000000000) ∧
    -Real.log (39294725751 / 40000000000) ≤ (355783 / 20000000) := by
  have h := checkLog_sound (w := (705274249 / 79294725751)) (n := 12)
    (lo := (17789149 / 1000000000)) (hi := (355783 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39294725751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39294725751) = 1/(39294725751 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8699 : Bounds (-355783 / 20000000) (-17789149 / 1000000000) (Real.log (39294725751 / 40000000000)) := by
  have h := reflection_log_8699_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8700_neg : (2206141 / 125000000) ≤ -Real.log (245626426311 / 250000000000) ∧
    -Real.log (245626426311 / 250000000000) ≤ (17649129 / 1000000000) := by
  have h := checkLog_sound (w := (4373573689 / 495626426311)) (n := 12)
    (lo := (2206141 / 125000000)) (hi := (17649129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245626426311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245626426311) = 1/(245626426311 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8700 : Bounds (-17649129 / 1000000000) (-2206141 / 125000000) (Real.log (245626426311 / 250000000000)) := by
  have h := reflection_log_8700_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8701_neg : (266090997 / 1000000000) ≤ -Real.log (500000000000 / 652426895799) ∧
    -Real.log (500000000000 / 652426895799) ≤ (133045499 / 500000000) := by
  have h := checkLog_sound (w := (152426895799 / 1152426895799)) (n := 12)
    (lo := (266090997 / 1000000000)) (hi := (133045499 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((652426895799 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(652426895799 / 500000000000) = 1/(500000000000 / 652426895799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8701 : Bounds (266090997 / 1000000000) (133045499 / 500000000) (Real.log (652426895799 / 500000000000)) := by
  have h := reflection_log_8701_neg
  have he : Real.log (652426895799 / 500000000000) = -Real.log (500000000000 / 652426895799) := by
    rw [show ((652426895799 / 500000000000) : ℝ) = ((500000000000 / 652426895799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8702_neg : (267147553 / 1000000000) ≤ -Real.log (500000000000 / 653116585853) ∧
    -Real.log (500000000000 / 653116585853) ≤ (133573777 / 500000000) := by
  have h := checkLog_sound (w := (153116585853 / 1153116585853)) (n := 12)
    (lo := (267147553 / 1000000000)) (hi := (133573777 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((653116585853 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(653116585853 / 500000000000) = 1/(500000000000 / 653116585853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8702 : Bounds (267147553 / 1000000000) (133573777 / 500000000) (Real.log (653116585853 / 500000000000)) := by
  have h := reflection_log_8702_neg
  have he : Real.log (653116585853 / 500000000000) = -Real.log (500000000000 / 653116585853) := by
    rw [show ((653116585853 / 500000000000) : ℝ) = ((500000000000 / 653116585853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8703_neg : (267717833 / 500000000) ≤ -Real.log (20000000000 / 34163845633) ∧
    -Real.log (20000000000 / 34163845633) ≤ (535435667 / 1000000000) := by
  have h := checkLog_sound (w := (14163845633 / 54163845633)) (n := 12)
    (lo := (267717833 / 500000000)) (hi := (535435667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34163845633 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34163845633 / 20000000000) = 1/(20000000000 / 34163845633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8703 : Bounds (267717833 / 500000000) (535435667 / 1000000000) (Real.log (34163845633 / 20000000000)) := by
  have h := reflection_log_8703_neg
  have he : Real.log (34163845633 / 20000000000) = -Real.log (20000000000 / 34163845633) := by
    rw [show ((34163845633 / 20000000000) : ℝ) = ((20000000000 / 34163845633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


