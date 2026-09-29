-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0102__2
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0102__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T21:04:53.744301+00:00
-- url     : https://prove2.me/theorems/f0b7025f-1efb-49f3-a489-93937ed98028
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0102 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0103)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0102 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0103)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0102 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0103)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0102 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0103) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0102 (+1 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0103).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0102 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6528_neg : (9462267 / 100000000) ≤ -Real.log (250000 / 274811) ∧
    -Real.log (250000 / 274811) ≤ (94622671 / 1000000000) := by
  have h := checkLog_sound (w := (24811 / 524811)) (n := 12)
    (lo := (9462267 / 100000000)) (hi := (94622671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274811 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274811 / 250000) = 1/(250000 / 274811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6528 : Bounds (9462267 / 100000000) (94622671 / 1000000000) (Real.log (274811 / 250000)) := by
  have h := reflection_log_6528_neg
  have he : Real.log (274811 / 250000) = -Real.log (250000 / 274811) := by
    rw [show ((274811 / 250000) : ℝ) = ((250000 / 274811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6529_neg : (26130217 / 250000000) ≤ -Real.log (225189 / 250000) ∧
    -Real.log (225189 / 250000) ≤ (104520869 / 1000000000) := by
  have h := checkLog_sound (w := (24811 / 475189)) (n := 12)
    (lo := (26130217 / 250000000)) (hi := (104520869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225189) = 1/(225189 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6529 : Bounds (-104520869 / 1000000000) (-26130217 / 250000000) (Real.log (225189 / 250000)) := by
  have h := reflection_log_6529_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6530_neg : (9898197 / 1000000000) ≤ -Real.log (61884414279 / 62500000000) ∧
    -Real.log (61884414279 / 62500000000) ≤ (4949099 / 500000000) := by
  have h := checkLog_sound (w := (615585721 / 124384414279)) (n := 12)
    (lo := (9898197 / 1000000000)) (hi := (4949099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61884414279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61884414279) = 1/(61884414279 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6530 : Bounds (-4949099 / 500000000) (-9898197 / 1000000000) (Real.log (61884414279 / 62500000000)) := by
  have h := reflection_log_6530_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6531_neg : (4924373 / 500000000) ≤ -Real.log (990199593991 / 1000000000000) ∧
    -Real.log (990199593991 / 1000000000000) ≤ (9848747 / 1000000000) := by
  have h := checkLog_sound (w := (9800406009 / 1990199593991)) (n := 12)
    (lo := (4924373 / 500000000)) (hi := (9848747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990199593991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990199593991) = 1/(990199593991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6531 : Bounds (-9848747 / 1000000000) (-4924373 / 500000000) (Real.log (990199593991 / 1000000000000)) := by
  have h := reflection_log_6531_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6532_neg : (198644637 / 1000000000) ≤ -Real.log (250000000000 / 304937108977) ∧
    -Real.log (250000000000 / 304937108977) ≤ (99322319 / 500000000) := by
  have h := checkLog_sound (w := (54937108977 / 554937108977)) (n := 12)
    (lo := (198644637 / 1000000000)) (hi := (99322319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304937108977 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304937108977 / 250000000000) = 1/(250000000000 / 304937108977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6532 : Bounds (198644637 / 1000000000) (99322319 / 500000000) (Real.log (304937108977 / 250000000000)) := by
  have h := reflection_log_6532_neg
  have he : Real.log (304937108977 / 250000000000) = -Real.log (250000000000 / 304937108977) := by
    rw [show ((304937108977 / 250000000000) : ℝ) = ((250000000000 / 304937108977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6533_neg : (199143539 / 1000000000) ≤ -Real.log (3125000000 / 3813616007) ∧
    -Real.log (3125000000 / 3813616007) ≤ (9957177 / 50000000) := by
  have h := checkLog_sound (w := (688616007 / 6938616007)) (n := 12)
    (lo := (199143539 / 1000000000)) (hi := (9957177 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3813616007 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3813616007 / 3125000000) = 1/(3125000000 / 3813616007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6533 : Bounds (199143539 / 1000000000) (9957177 / 50000000) (Real.log (3813616007 / 3125000000)) := by
  have h := reflection_log_6533_neg
  have he : Real.log (3813616007 / 3125000000) = -Real.log (3125000000 / 3813616007) := by
    rw [show ((3813616007 / 3125000000) : ℝ) = ((3125000000 / 3813616007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6534_neg : (199401429 / 500000000) ≤ -Real.log (250000000000 / 372509960159) ∧
    -Real.log (250000000000 / 372509960159) ≤ (398802859 / 1000000000) := by
  have h := checkLog_sound (w := (122509960159 / 622509960159)) (n := 12)
    (lo := (199401429 / 500000000)) (hi := (398802859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372509960159 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372509960159 / 250000000000) = 1/(250000000000 / 372509960159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6534 : Bounds (199401429 / 500000000) (398802859 / 1000000000) (Real.log (372509960159 / 250000000000)) := by
  have h := reflection_log_6534_neg
  have he : Real.log (372509960159 / 250000000000) = -Real.log (250000000000 / 372509960159) := by
    rw [show ((372509960159 / 250000000000) : ℝ) = ((250000000000 / 372509960159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6535_neg : (9975273 / 25000000) ≤ -Real.log (500000000000 / 745174947081) ∧
    -Real.log (500000000000 / 745174947081) ≤ (399010921 / 1000000000) := by
  have h := checkLog_sound (w := (245174947081 / 1245174947081)) (n := 12)
    (lo := (9975273 / 25000000)) (hi := (399010921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((745174947081 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(745174947081 / 500000000000) = 1/(500000000000 / 745174947081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6535 : Bounds (9975273 / 25000000) (399010921 / 1000000000) (Real.log (745174947081 / 500000000000)) := by
  have h := reflection_log_6535_neg
  have he : Real.log (745174947081 / 500000000000) = -Real.log (500000000000 / 745174947081) := by
    rw [show ((745174947081 / 500000000000) : ℝ) = ((500000000000 / 745174947081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6536_neg : (89909213 / 500000000) ≤ -Real.log (1000 / 1197) ∧
    -Real.log (1000 / 1197) ≤ (179818427 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 2197)) (n := 12)
    (lo := (89909213 / 500000000)) (hi := (179818427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1197 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1197 / 1000) = 1/(1000 / 1197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6536 : Bounds (89909213 / 500000000) (179818427 / 1000000000) (Real.log (1197 / 1000)) := by
  have h := reflection_log_6536_neg
  have he : Real.log (1197 / 1000) = -Real.log (1000 / 1197) := by
    rw [show ((1197 / 1000) : ℝ) = ((1000 / 1197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6537_neg : (43880113 / 200000000) ≤ -Real.log (803 / 1000) ∧
    -Real.log (803 / 1000) ≤ (109700283 / 500000000) := by
  have h := checkLog_sound (w := (197 / 1803)) (n := 12)
    (lo := (43880113 / 200000000)) (hi := (109700283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 803) = 1/(803 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6537 : Bounds (-109700283 / 500000000) (-43880113 / 200000000) (Real.log (803 / 1000)) := by
  have h := reflection_log_6537_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6538_neg : (9849 / 50000000) ≤ -Real.log (1000000 / 1000197) ∧
    -Real.log (1000000 / 1000197) ≤ (196981 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 2000197)) (n := 12)
    (lo := (9849 / 50000000)) (hi := (196981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000197 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000197 / 1000000) = 1/(1000000 / 1000197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6538 : Bounds (9849 / 50000000) (196981 / 1000000000) (Real.log (1000197 / 1000000)) := by
  have h := reflection_log_6538_neg
  have he : Real.log (1000197 / 1000000) = -Real.log (1000000 / 1000197) := by
    rw [show ((1000197 / 1000000) : ℝ) = ((1000000 / 1000197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6539_neg : (197019 / 1000000000) ≤ -Real.log (999803 / 1000000) ∧
    -Real.log (999803 / 1000000) ≤ (9851 / 50000000) := by
  have h := checkLog_sound (w := (197 / 1999803)) (n := 12)
    (lo := (197019 / 1000000000)) (hi := (9851 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999803) = 1/(999803 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6539 : Bounds (-9851 / 50000000) (-197019 / 1000000000) (Real.log (999803 / 1000000)) := by
  have h := reflection_log_6539_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6540_neg : (1888887 / 20000000) ≤ -Real.log (125000 / 137381) ∧
    -Real.log (125000 / 137381) ≤ (94444351 / 1000000000) := by
  have h := checkLog_sound (w := (12381 / 262381)) (n := 12)
    (lo := (1888887 / 20000000)) (hi := (94444351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137381 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137381 / 125000) = 1/(125000 / 137381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6540 : Bounds (1888887 / 20000000) (94444351 / 1000000000) (Real.log (137381 / 125000)) := by
  have h := reflection_log_6540_neg
  have he : Real.log (137381 / 125000) = -Real.log (125000 / 137381) := by
    rw [show ((137381 / 125000) : ℝ) = ((125000 / 137381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6541_neg : (1629739 / 15625000) ≤ -Real.log (112619 / 125000) ∧
    -Real.log (112619 / 125000) ≤ (104303297 / 1000000000) := by
  have h := checkLog_sound (w := (12381 / 237619)) (n := 12)
    (lo := (1629739 / 15625000)) (hi := (104303297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 112619) = 1/(112619 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6541 : Bounds (-104303297 / 1000000000) (-1629739 / 15625000) (Real.log (112619 / 125000)) := by
  have h := reflection_log_6541_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6542_neg : (47334987 / 500000000) ≤ -Real.log (31250 / 34353) ∧
    -Real.log (31250 / 34353) ≤ (3786799 / 40000000) := by
  have h := checkLog_sound (w := (3103 / 65603)) (n := 12)
    (lo := (47334987 / 500000000)) (hi := (3786799 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34353 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34353 / 31250) = 1/(31250 / 34353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6542 : Bounds (47334987 / 500000000) (3786799 / 40000000) (Real.log (34353 / 31250)) := by
  have h := reflection_log_6542_neg
  have he : Real.log (34353 / 31250) = -Real.log (31250 / 34353) := by
    rw [show ((34353 / 31250) : ℝ) = ((31250 / 34353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6543_neg : (104578599 / 1000000000) ≤ -Real.log (28147 / 31250) ∧
    -Real.log (28147 / 31250) ≤ (522893 / 5000000) := by
  have h := checkLog_sound (w := (3103 / 59397)) (n := 12)
    (lo := (104578599 / 1000000000)) (hi := (522893 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 28147) = 1/(28147 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6543 : Bounds (-522893 / 5000000) (-104578599 / 1000000000) (Real.log (28147 / 31250)) := by
  have h := reflection_log_6543_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6544_neg : (619289 / 62500000) ≤ -Real.log (966933891 / 976562500) ∧
    -Real.log (966933891 / 976562500) ≤ (79269 / 8000000) := by
  have h := checkLog_sound (w := (9628609 / 1943496391)) (n := 12)
    (lo := (619289 / 62500000)) (hi := (79269 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 966933891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 966933891) = 1/(966933891 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6544 : Bounds (-79269 / 8000000) (-619289 / 62500000) (Real.log (966933891 / 976562500)) := by
  have h := reflection_log_6544_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6545_neg : (4929473 / 500000000) ≤ -Real.log (15471710839 / 15625000000) ∧
    -Real.log (15471710839 / 15625000000) ≤ (9858947 / 1000000000) := by
  have h := checkLog_sound (w := (153289161 / 31096710839)) (n := 12)
    (lo := (4929473 / 500000000)) (hi := (9858947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15471710839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15471710839) = 1/(15471710839 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6545 : Bounds (-9858947 / 1000000000) (-4929473 / 500000000) (Real.log (15471710839 / 15625000000)) := by
  have h := reflection_log_6545_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6546_neg : (198747647 / 1000000000) ≤ -Real.log (50000000000 / 60993704437) ∧
    -Real.log (50000000000 / 60993704437) ≤ (388179 / 1953125) := by
  have h := checkLog_sound (w := (10993704437 / 110993704437)) (n := 12)
    (lo := (198747647 / 1000000000)) (hi := (388179 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60993704437 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60993704437 / 50000000000) = 1/(50000000000 / 60993704437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6546 : Bounds (198747647 / 1000000000) (388179 / 1953125) (Real.log (60993704437 / 50000000000)) := by
  have h := reflection_log_6546_neg
  have he : Real.log (60993704437 / 50000000000) = -Real.log (50000000000 / 60993704437) := by
    rw [show ((60993704437 / 50000000000) : ℝ) = ((50000000000 / 60993704437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6547_neg : (99624287 / 500000000) ≤ -Real.log (100000000000 / 122048530927) ∧
    -Real.log (100000000000 / 122048530927) ≤ (7969943 / 40000000) := by
  have h := checkLog_sound (w := (22048530927 / 222048530927)) (n := 12)
    (lo := (99624287 / 500000000)) (hi := (7969943 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122048530927 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122048530927 / 100000000000) = 1/(100000000000 / 122048530927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6547 : Bounds (99624287 / 500000000) (7969943 / 40000000) (Real.log (122048530927 / 100000000000)) := by
  have h := reflection_log_6547_neg
  have he : Real.log (122048530927 / 100000000000) = -Real.log (100000000000 / 122048530927) := by
    rw [show ((122048530927 / 100000000000) : ℝ) = ((100000000000 / 122048530927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6548_neg : (9975273 / 25000000) ≤ -Real.log (12500000000 / 18629373677) ∧
    -Real.log (12500000000 / 18629373677) ≤ (399010921 / 1000000000) := by
  have h := checkLog_sound (w := (6129373677 / 31129373677)) (n := 12)
    (lo := (9975273 / 25000000)) (hi := (399010921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18629373677 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18629373677 / 12500000000) = 1/(12500000000 / 18629373677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6548 : Bounds (9975273 / 25000000) (399010921 / 1000000000) (Real.log (18629373677 / 12500000000)) := by
  have h := reflection_log_6548_neg
  have he : Real.log (18629373677 / 12500000000) = -Real.log (12500000000 / 18629373677) := by
    rw [show ((18629373677 / 12500000000) : ℝ) = ((12500000000 / 18629373677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6549_neg : (399218991 / 1000000000) ≤ -Real.log (250000000000 / 372665006227) ∧
    -Real.log (250000000000 / 372665006227) ≤ (24951187 / 62500000) := by
  have h := checkLog_sound (w := (122665006227 / 622665006227)) (n := 12)
    (lo := (399218991 / 1000000000)) (hi := (24951187 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372665006227 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372665006227 / 250000000000) = 1/(250000000000 / 372665006227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6549 : Bounds (399218991 / 1000000000) (24951187 / 62500000) (Real.log (372665006227 / 250000000000)) := by
  have h := reflection_log_6549_neg
  have he : Real.log (372665006227 / 250000000000) = -Real.log (250000000000 / 372665006227) := by
    rw [show ((372665006227 / 250000000000) : ℝ) = ((250000000000 / 372665006227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6550_neg : (35980393 / 200000000) ≤ -Real.log (10000 / 11971) ∧
    -Real.log (10000 / 11971) ≤ (89950983 / 500000000) := by
  have h := checkLog_sound (w := (1971 / 21971)) (n := 12)
    (lo := (35980393 / 200000000)) (hi := (89950983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11971 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11971 / 10000) = 1/(10000 / 11971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6550 : Bounds (35980393 / 200000000) (89950983 / 500000000) (Real.log (11971 / 10000)) := by
  have h := reflection_log_6550_neg
  have he : Real.log (11971 / 10000) = -Real.log (10000 / 11971) := by
    rw [show ((11971 / 10000) : ℝ) = ((10000 / 11971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6551_neg : (43905021 / 200000000) ≤ -Real.log (8029 / 10000) ∧
    -Real.log (8029 / 10000) ≤ (109762553 / 500000000) := by
  have h := checkLog_sound (w := (1971 / 18029)) (n := 12)
    (lo := (43905021 / 200000000)) (hi := (109762553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8029) = 1/(8029 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6551 : Bounds (-109762553 / 500000000) (-43905021 / 200000000) (Real.log (8029 / 10000)) := by
  have h := reflection_log_6551_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6552_neg : (4927 / 25000000) ≤ -Real.log (10000000 / 10001971) ∧
    -Real.log (10000000 / 10001971) ≤ (197081 / 1000000000) := by
  have h := checkLog_sound (w := (1971 / 20001971)) (n := 12)
    (lo := (4927 / 25000000)) (hi := (197081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001971 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001971 / 10000000) = 1/(10000000 / 10001971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6552 : Bounds (4927 / 25000000) (197081 / 1000000000) (Real.log (10001971 / 10000000)) := by
  have h := reflection_log_6552_neg
  have he : Real.log (10001971 / 10000000) = -Real.log (10000000 / 10001971) := by
    rw [show ((10001971 / 10000000) : ℝ) = ((10000000 / 10001971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6553_neg : (197119 / 1000000000) ≤ -Real.log (9998029 / 10000000) ∧
    -Real.log (9998029 / 10000000) ≤ (77 / 390625) := by
  have h := checkLog_sound (w := (1971 / 19998029)) (n := 12)
    (lo := (197119 / 1000000000)) (hi := (77 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998029) = 1/(9998029 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6553 : Bounds (-77 / 390625) (-197119 / 1000000000) (Real.log (9998029 / 10000000)) := by
  have h := reflection_log_6553_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6554_neg : (94490753 / 1000000000) ≤ -Real.log (1000000 / 1099099) ∧
    -Real.log (1000000 / 1099099) ≤ (47245377 / 500000000) := by
  have h := checkLog_sound (w := (99099 / 2099099)) (n := 12)
    (lo := (94490753 / 1000000000)) (hi := (47245377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099099 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099099 / 1000000) = 1/(1000000 / 1099099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6554 : Bounds (94490753 / 1000000000) (47245377 / 500000000) (Real.log (1099099 / 1000000)) := by
  have h := reflection_log_6554_neg
  have he : Real.log (1099099 / 1000000) = -Real.log (1000000 / 1099099) := by
    rw [show ((1099099 / 1000000) : ℝ) = ((1000000 / 1099099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6555_neg : (20871981 / 200000000) ≤ -Real.log (900901 / 1000000) ∧
    -Real.log (900901 / 1000000) ≤ (52179953 / 500000000) := by
  have h := checkLog_sound (w := (99099 / 1900901)) (n := 12)
    (lo := (20871981 / 200000000)) (hi := (52179953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900901) = 1/(900901 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6555 : Bounds (-52179953 / 500000000) (-20871981 / 200000000) (Real.log (900901 / 1000000)) := by
  have h := reflection_log_6555_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6556_neg : (94716367 / 1000000000) ≤ -Real.log (1000000 / 1099347) ∧
    -Real.log (1000000 / 1099347) ≤ (5919773 / 62500000) := by
  have h := checkLog_sound (w := (99347 / 2099347)) (n := 12)
    (lo := (94716367 / 1000000000)) (hi := (5919773 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099347 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099347 / 1000000) = 1/(1000000 / 1099347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6556 : Bounds (94716367 / 1000000000) (5919773 / 62500000) (Real.log (1099347 / 1000000)) := by
  have h := reflection_log_6556_neg
  have he : Real.log (1099347 / 1000000) = -Real.log (1000000 / 1099347) := by
    rw [show ((1099347 / 1000000) : ℝ) = ((1000000 / 1099347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6557_neg : (104635223 / 1000000000) ≤ -Real.log (900653 / 1000000) ∧
    -Real.log (900653 / 1000000) ≤ (13079403 / 125000000) := by
  have h := checkLog_sound (w := (99347 / 1900653)) (n := 12)
    (lo := (104635223 / 1000000000)) (hi := (13079403 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900653) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900653) = 1/(900653 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6557 : Bounds (-13079403 / 125000000) (-104635223 / 1000000000) (Real.log (900653 / 1000000)) := by
  have h := reflection_log_6557_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6558_neg : (1239857 / 125000000) ≤ -Real.log (990130173591 / 1000000000000) ∧
    -Real.log (990130173591 / 1000000000000) ≤ (9918857 / 1000000000) := by
  have h := checkLog_sound (w := (9869826409 / 1990130173591)) (n := 12)
    (lo := (1239857 / 125000000)) (hi := (9918857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990130173591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990130173591) = 1/(990130173591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6558 : Bounds (-9918857 / 1000000000) (-1239857 / 125000000) (Real.log (990130173591 / 1000000000000)) := by
  have h := reflection_log_6558_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6559_neg : (308411 / 31250000) ≤ -Real.log (990179388199 / 1000000000000) ∧
    -Real.log (990179388199 / 1000000000000) ≤ (9869153 / 1000000000) := by
  have h := checkLog_sound (w := (9820611801 / 1990179388199)) (n := 12)
    (lo := (308411 / 31250000)) (hi := (9869153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990179388199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990179388199) = 1/(990179388199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6559 : Bounds (-9869153 / 1000000000) (-308411 / 31250000) (Real.log (990179388199 / 1000000000000)) := by
  have h := reflection_log_6559_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6560_neg : (99425329 / 500000000) ≤ -Real.log (5000000000 / 6099998779) ∧
    -Real.log (5000000000 / 6099998779) ≤ (198850659 / 1000000000) := by
  have h := checkLog_sound (w := (1099998779 / 11099998779)) (n := 12)
    (lo := (99425329 / 500000000)) (hi := (198850659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6099998779 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6099998779 / 5000000000) = 1/(5000000000 / 6099998779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6560 : Bounds (99425329 / 500000000) (198850659 / 1000000000) (Real.log (6099998779 / 5000000000)) := by
  have h := reflection_log_6560_neg
  have he : Real.log (6099998779 / 5000000000) = -Real.log (5000000000 / 6099998779) := by
    rw [show ((6099998779 / 5000000000) : ℝ) = ((5000000000 / 6099998779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6561_neg : (19935159 / 100000000) ≤ -Real.log (500000000000 / 610305522771) ∧
    -Real.log (500000000000 / 610305522771) ≤ (199351591 / 1000000000) := by
  have h := checkLog_sound (w := (110305522771 / 1110305522771)) (n := 12)
    (lo := (19935159 / 100000000)) (hi := (199351591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610305522771 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(610305522771 / 500000000000) = 1/(500000000000 / 610305522771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6561 : Bounds (19935159 / 100000000) (199351591 / 1000000000) (Real.log (610305522771 / 500000000000)) := by
  have h := reflection_log_6561_neg
  have he : Real.log (610305522771 / 500000000000) = -Real.log (500000000000 / 610305522771) := by
    rw [show ((610305522771 / 500000000000) : ℝ) = ((500000000000 / 610305522771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6562_neg : (399218991 / 1000000000) ≤ -Real.log (500000000000 / 745330012453) ∧
    -Real.log (500000000000 / 745330012453) ≤ (24951187 / 62500000) := by
  have h := checkLog_sound (w := (245330012453 / 1245330012453)) (n := 12)
    (lo := (399218991 / 1000000000)) (hi := (24951187 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((745330012453 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(745330012453 / 500000000000) = 1/(500000000000 / 745330012453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6562 : Bounds (399218991 / 1000000000) (24951187 / 62500000) (Real.log (745330012453 / 500000000000)) := by
  have h := reflection_log_6562_neg
  have he : Real.log (745330012453 / 500000000000) = -Real.log (500000000000 / 745330012453) := by
    rw [show ((745330012453 / 500000000000) : ℝ) = ((500000000000 / 745330012453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6563_neg : (399427071 / 1000000000) ≤ -Real.log (500000000000 / 745485116453) ∧
    -Real.log (500000000000 / 745485116453) ≤ (780131 / 1953125) := by
  have h := checkLog_sound (w := (245485116453 / 1245485116453)) (n := 12)
    (lo := (399427071 / 1000000000)) (hi := (780131 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((745485116453 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(745485116453 / 500000000000) = 1/(500000000000 / 745485116453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6563 : Bounds (399427071 / 1000000000) (780131 / 1953125) (Real.log (745485116453 / 500000000000)) := by
  have h := reflection_log_6563_neg
  have he : Real.log (745485116453 / 500000000000) = -Real.log (500000000000 / 745485116453) := by
    rw [show ((745485116453 / 500000000000) : ℝ) = ((500000000000 / 745485116453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6564_neg : (22498187 / 125000000) ≤ -Real.log (2500 / 2993) ∧
    -Real.log (2500 / 2993) ≤ (179985497 / 1000000000) := by
  have h := checkLog_sound (w := (493 / 5493)) (n := 12)
    (lo := (22498187 / 125000000)) (hi := (179985497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2993 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2993 / 2500) = 1/(2500 / 2993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6564 : Bounds (22498187 / 125000000) (179985497 / 1000000000) (Real.log (2993 / 2500)) := by
  have h := reflection_log_6564_neg
  have he : Real.log (2993 / 2500) = -Real.log (2500 / 2993) := by
    rw [show ((2993 / 2500) : ℝ) = ((2500 / 2993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6565_neg : (109824831 / 500000000) ≤ -Real.log (2007 / 2500) ∧
    -Real.log (2007 / 2500) ≤ (219649663 / 1000000000) := by
  have h := checkLog_sound (w := (493 / 4507)) (n := 12)
    (lo := (109824831 / 500000000)) (hi := (219649663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2007) = 1/(2007 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6565 : Bounds (-219649663 / 1000000000) (-109824831 / 500000000) (Real.log (2007 / 2500)) := by
  have h := reflection_log_6565_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6566_neg : (9859 / 50000000) ≤ -Real.log (2500000 / 2500493) ∧
    -Real.log (2500000 / 2500493) ≤ (197181 / 1000000000) := by
  have h := checkLog_sound (w := (493 / 5000493)) (n := 12)
    (lo := (9859 / 50000000)) (hi := (197181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500493 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500493 / 2500000) = 1/(2500000 / 2500493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6566 : Bounds (9859 / 50000000) (197181 / 1000000000) (Real.log (2500493 / 2500000)) := by
  have h := reflection_log_6566_neg
  have he : Real.log (2500493 / 2500000) = -Real.log (2500000 / 2500493) := by
    rw [show ((2500493 / 2500000) : ℝ) = ((2500000 / 2500493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6567_neg : (197219 / 1000000000) ≤ -Real.log (2499507 / 2500000) ∧
    -Real.log (2499507 / 2500000) ≤ (9861 / 50000000) := by
  have h := checkLog_sound (w := (493 / 4999507)) (n := 12)
    (lo := (197219 / 1000000000)) (hi := (9861 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499507) = 1/(2499507 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6567 : Bounds (-9861 / 50000000) (-197219 / 1000000000) (Real.log (2499507 / 2500000)) := by
  have h := reflection_log_6567_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6568_neg : (94537153 / 1000000000) ≤ -Real.log (20000 / 21983) ∧
    -Real.log (20000 / 21983) ≤ (47268577 / 500000000) := by
  have h := checkLog_sound (w := (1983 / 41983)) (n := 12)
    (lo := (94537153 / 1000000000)) (hi := (47268577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21983 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21983 / 20000) = 1/(20000 / 21983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6568 : Bounds (94537153 / 1000000000) (47268577 / 500000000) (Real.log (21983 / 20000)) := by
  have h := reflection_log_6568_neg
  have he : Real.log (21983 / 20000) = -Real.log (20000 / 21983) := by
    rw [show ((21983 / 20000) : ℝ) = ((20000 / 21983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6569_neg : (26104129 / 250000000) ≤ -Real.log (18017 / 20000) ∧
    -Real.log (18017 / 20000) ≤ (104416517 / 1000000000) := by
  have h := checkLog_sound (w := (1983 / 38017)) (n := 12)
    (lo := (26104129 / 250000000)) (hi := (104416517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 18017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 18017) = 1/(18017 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6569 : Bounds (-104416517 / 1000000000) (-26104129 / 250000000) (Real.log (18017 / 20000)) := by
  have h := reflection_log_6569_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6570_neg : (94762757 / 1000000000) ≤ -Real.log (500000 / 549699) ∧
    -Real.log (500000 / 549699) ≤ (47381379 / 500000000) := by
  have h := checkLog_sound (w := (49699 / 1049699)) (n := 12)
    (lo := (94762757 / 1000000000)) (hi := (47381379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549699 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549699 / 500000) = 1/(500000 / 549699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6570 : Bounds (94762757 / 1000000000) (47381379 / 500000000) (Real.log (549699 / 500000)) := by
  have h := reflection_log_6570_neg
  have he : Real.log (549699 / 500000) = -Real.log (500000 / 549699) := by
    rw [show ((549699 / 500000) : ℝ) = ((500000 / 549699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6571_neg : (2093837 / 20000000) ≤ -Real.log (450301 / 500000) ∧
    -Real.log (450301 / 500000) ≤ (104691851 / 1000000000) := by
  have h := checkLog_sound (w := (49699 / 950301)) (n := 12)
    (lo := (2093837 / 20000000)) (hi := (104691851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450301) = 1/(450301 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6571 : Bounds (-104691851 / 1000000000) (-2093837 / 20000000) (Real.log (450301 / 500000)) := by
  have h := reflection_log_6571_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6572_neg : (9929093 / 1000000000) ≤ -Real.log (247530009399 / 250000000000) ∧
    -Real.log (247530009399 / 250000000000) ≤ (4964547 / 500000000) := by
  have h := checkLog_sound (w := (2469990601 / 497530009399)) (n := 12)
    (lo := (9929093 / 1000000000)) (hi := (4964547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247530009399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247530009399) = 1/(247530009399 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6572 : Bounds (-4964547 / 500000000) (-9929093 / 1000000000) (Real.log (247530009399 / 250000000000)) := by
  have h := reflection_log_6572_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6573_neg : (9879363 / 1000000000) ≤ -Real.log (396067711 / 400000000) ∧
    -Real.log (396067711 / 400000000) ≤ (2469841 / 250000000) := by
  have h := checkLog_sound (w := (3932289 / 796067711)) (n := 12)
    (lo := (9879363 / 1000000000)) (hi := (2469841 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 396067711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 396067711) = 1/(396067711 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6573 : Bounds (-2469841 / 250000000) (-9879363 / 1000000000) (Real.log (396067711 / 400000000)) := by
  have h := reflection_log_6573_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6574_neg : (19895367 / 100000000) ≤ -Real.log (500000000000 / 610062718543) ∧
    -Real.log (500000000000 / 610062718543) ≤ (198953671 / 1000000000) := by
  have h := checkLog_sound (w := (110062718543 / 1110062718543)) (n := 12)
    (lo := (19895367 / 100000000)) (hi := (198953671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610062718543 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(610062718543 / 500000000000) = 1/(500000000000 / 610062718543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6574 : Bounds (19895367 / 100000000) (198953671 / 1000000000) (Real.log (610062718543 / 500000000000)) := by
  have h := reflection_log_6574_neg
  have he : Real.log (610062718543 / 500000000000) = -Real.log (500000000000 / 610062718543) := by
    rw [show ((610062718543 / 500000000000) : ℝ) = ((500000000000 / 610062718543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6575_neg : (199454607 / 1000000000) ≤ -Real.log (125000000000 / 152592099507) ∧
    -Real.log (125000000000 / 152592099507) ≤ (12465913 / 62500000) := by
  have h := checkLog_sound (w := (27592099507 / 277592099507)) (n := 12)
    (lo := (199454607 / 1000000000)) (hi := (12465913 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152592099507 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152592099507 / 125000000000) = 1/(125000000000 / 152592099507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6575 : Bounds (199454607 / 1000000000) (12465913 / 62500000) (Real.log (152592099507 / 125000000000)) := by
  have h := reflection_log_6575_neg
  have he : Real.log (152592099507 / 125000000000) = -Real.log (125000000000 / 152592099507) := by
    rw [show ((152592099507 / 125000000000) : ℝ) = ((125000000000 / 152592099507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6576_neg : (399427071 / 1000000000) ≤ -Real.log (125000000000 / 186371279113) ∧
    -Real.log (125000000000 / 186371279113) ≤ (780131 / 1953125) := by
  have h := checkLog_sound (w := (61371279113 / 311371279113)) (n := 12)
    (lo := (399427071 / 1000000000)) (hi := (780131 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186371279113 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186371279113 / 125000000000) = 1/(125000000000 / 186371279113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6576 : Bounds (399427071 / 1000000000) (780131 / 1953125) (Real.log (186371279113 / 125000000000)) := by
  have h := reflection_log_6576_neg
  have he : Real.log (186371279113 / 125000000000) = -Real.log (125000000000 / 186371279113) := by
    rw [show ((186371279113 / 125000000000) : ℝ) = ((125000000000 / 186371279113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6577_neg : (399635159 / 1000000000) ≤ -Real.log (250000000000 / 372820129547) ∧
    -Real.log (250000000000 / 372820129547) ≤ (9990879 / 25000000) := by
  have h := checkLog_sound (w := (122820129547 / 622820129547)) (n := 12)
    (lo := (399635159 / 1000000000)) (hi := (9990879 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372820129547 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372820129547 / 250000000000) = 1/(250000000000 / 372820129547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6577 : Bounds (399635159 / 1000000000) (9990879 / 25000000) (Real.log (372820129547 / 250000000000)) := by
  have h := reflection_log_6577_neg
  have he : Real.log (372820129547 / 250000000000) = -Real.log (250000000000 / 372820129547) := by
    rw [show ((372820129547 / 250000000000) : ℝ) = ((250000000000 / 372820129547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6578_neg : (180069021 / 1000000000) ≤ -Real.log (10000 / 11973) ∧
    -Real.log (10000 / 11973) ≤ (90034511 / 500000000) := by
  have h := checkLog_sound (w := (1973 / 21973)) (n := 12)
    (lo := (180069021 / 1000000000)) (hi := (90034511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11973 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11973 / 10000) = 1/(10000 / 11973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6578 : Bounds (180069021 / 1000000000) (90034511 / 500000000) (Real.log (11973 / 10000)) := by
  have h := reflection_log_6578_neg
  have he : Real.log (11973 / 10000) = -Real.log (10000 / 11973) := by
    rw [show ((11973 / 10000) : ℝ) = ((10000 / 11973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6579_neg : (219774233 / 1000000000) ≤ -Real.log (8027 / 10000) ∧
    -Real.log (8027 / 10000) ≤ (109887117 / 500000000) := by
  have h := checkLog_sound (w := (1973 / 18027)) (n := 12)
    (lo := (219774233 / 1000000000)) (hi := (109887117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8027) = 1/(8027 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6579 : Bounds (-109887117 / 500000000) (-219774233 / 1000000000) (Real.log (8027 / 10000)) := by
  have h := reflection_log_6579_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6580_neg : (1233 / 6250000) ≤ -Real.log (10000000 / 10001973) ∧
    -Real.log (10000000 / 10001973) ≤ (197281 / 1000000000) := by
  have h := checkLog_sound (w := (1973 / 20001973)) (n := 12)
    (lo := (1233 / 6250000)) (hi := (197281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001973 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001973 / 10000000) = 1/(10000000 / 10001973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6580 : Bounds (1233 / 6250000) (197281 / 1000000000) (Real.log (10001973 / 10000000)) := by
  have h := reflection_log_6580_neg
  have he : Real.log (10001973 / 10000000) = -Real.log (10000000 / 10001973) := by
    rw [show ((10001973 / 10000000) : ℝ) = ((10000000 / 10001973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6581_neg : (197319 / 1000000000) ≤ -Real.log (9998027 / 10000000) ∧
    -Real.log (9998027 / 10000000) ≤ (4933 / 25000000) := by
  have h := checkLog_sound (w := (1973 / 19998027)) (n := 12)
    (lo := (197319 / 1000000000)) (hi := (4933 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998027) = 1/(9998027 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6581 : Bounds (-4933 / 25000000) (-197319 / 1000000000) (Real.log (9998027 / 10000000)) := by
  have h := reflection_log_6581_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6582_neg : (369467 / 3906250) ≤ -Real.log (1000000 / 1099201) ∧
    -Real.log (1000000 / 1099201) ≤ (94583553 / 1000000000) := by
  have h := checkLog_sound (w := (99201 / 2099201)) (n := 12)
    (lo := (369467 / 3906250)) (hi := (94583553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099201 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099201 / 1000000) = 1/(1000000 / 1099201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6582 : Bounds (369467 / 3906250) (94583553 / 1000000000) (Real.log (1099201 / 1000000)) := by
  have h := reflection_log_6582_neg
  have he : Real.log (1099201 / 1000000) = -Real.log (1000000 / 1099201) := by
    rw [show ((1099201 / 1000000) : ℝ) = ((1000000 / 1099201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6583_neg : (104473131 / 1000000000) ≤ -Real.log (900799 / 1000000) ∧
    -Real.log (900799 / 1000000) ≤ (26118283 / 250000000) := by
  have h := checkLog_sound (w := (99201 / 1900799)) (n := 12)
    (lo := (104473131 / 1000000000)) (hi := (26118283 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900799) = 1/(900799 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6583 : Bounds (-26118283 / 250000000) (-104473131 / 1000000000) (Real.log (900799 / 1000000)) := by
  have h := reflection_log_6583_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6584_neg : (18961829 / 200000000) ≤ -Real.log (1000000 / 1099449) ∧
    -Real.log (1000000 / 1099449) ≤ (47404573 / 500000000) := by
  have h := checkLog_sound (w := (99449 / 2099449)) (n := 12)
    (lo := (18961829 / 200000000)) (hi := (47404573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099449 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099449 / 1000000) = 1/(1000000 / 1099449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6584 : Bounds (18961829 / 200000000) (47404573 / 500000000) (Real.log (1099449 / 1000000)) := by
  have h := reflection_log_6584_neg
  have he : Real.log (1099449 / 1000000) = -Real.log (1000000 / 1099449) := by
    rw [show ((1099449 / 1000000) : ℝ) = ((1000000 / 1099449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6585_neg : (327339 / 3125000) ≤ -Real.log (900551 / 1000000) ∧
    -Real.log (900551 / 1000000) ≤ (104748481 / 1000000000) := by
  have h := checkLog_sound (w := (99449 / 1900551)) (n := 12)
    (lo := (327339 / 3125000)) (hi := (104748481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900551) = 1/(900551 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6585 : Bounds (-104748481 / 1000000000) (-327339 / 3125000) (Real.log (900551 / 1000000)) := by
  have h := reflection_log_6585_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6586_neg : (1987867 / 200000000) ≤ -Real.log (990109896399 / 1000000000000) ∧
    -Real.log (990109896399 / 1000000000000) ≤ (1242417 / 125000000) := by
  have h := checkLog_sound (w := (9890103601 / 1990109896399)) (n := 12)
    (lo := (1987867 / 200000000)) (hi := (1242417 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990109896399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990109896399) = 1/(990109896399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6586 : Bounds (-1242417 / 125000000) (-1987867 / 200000000) (Real.log (990109896399 / 1000000000000)) := by
  have h := reflection_log_6586_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6587_neg : (9889579 / 1000000000) ≤ -Real.log (990159161599 / 1000000000000) ∧
    -Real.log (990159161599 / 1000000000000) ≤ (494479 / 50000000) := by
  have h := checkLog_sound (w := (9840838401 / 1990159161599)) (n := 12)
    (lo := (9889579 / 1000000000)) (hi := (494479 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990159161599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990159161599) = 1/(990159161599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6587 : Bounds (-494479 / 50000000) (-9889579 / 1000000000) (Real.log (990159161599 / 1000000000000)) := by
  have h := reflection_log_6587_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6588_neg : (199056683 / 1000000000) ≤ -Real.log (250000000000 / 305062783151) ∧
    -Real.log (250000000000 / 305062783151) ≤ (49764171 / 250000000) := by
  have h := checkLog_sound (w := (55062783151 / 555062783151)) (n := 12)
    (lo := (199056683 / 1000000000)) (hi := (49764171 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305062783151 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305062783151 / 250000000000) = 1/(250000000000 / 305062783151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6588 : Bounds (199056683 / 1000000000) (49764171 / 250000000) (Real.log (305062783151 / 250000000000)) := by
  have h := reflection_log_6588_neg
  have he : Real.log (305062783151 / 250000000000) = -Real.log (250000000000 / 305062783151) := by
    rw [show ((305062783151 / 250000000000) : ℝ) = ((250000000000 / 305062783151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6589_neg : (1596461 / 8000000) ≤ -Real.log (100000000000 / 122086256081) ∧
    -Real.log (100000000000 / 122086256081) ≤ (99778813 / 500000000) := by
  have h := checkLog_sound (w := (22086256081 / 222086256081)) (n := 12)
    (lo := (1596461 / 8000000)) (hi := (99778813 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122086256081 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122086256081 / 100000000000) = 1/(100000000000 / 122086256081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6589 : Bounds (1596461 / 8000000) (99778813 / 500000000) (Real.log (122086256081 / 100000000000)) := by
  have h := reflection_log_6589_neg
  have he : Real.log (122086256081 / 100000000000) = -Real.log (100000000000 / 122086256081) := by
    rw [show ((122086256081 / 100000000000) : ℝ) = ((100000000000 / 122086256081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6590_neg : (399635159 / 1000000000) ≤ -Real.log (500000000000 / 745640259093) ∧
    -Real.log (500000000000 / 745640259093) ≤ (9990879 / 25000000) := by
  have h := checkLog_sound (w := (245640259093 / 1245640259093)) (n := 12)
    (lo := (399635159 / 1000000000)) (hi := (9990879 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((745640259093 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(745640259093 / 500000000000) = 1/(500000000000 / 745640259093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6590 : Bounds (399635159 / 1000000000) (9990879 / 25000000) (Real.log (745640259093 / 500000000000)) := by
  have h := reflection_log_6590_neg
  have he : Real.log (745640259093 / 500000000000) = -Real.log (500000000000 / 745640259093) := by
    rw [show ((745640259093 / 500000000000) : ℝ) = ((500000000000 / 745640259093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6591_neg : (79968651 / 200000000) ≤ -Real.log (500000000000 / 745795440389) ∧
    -Real.log (500000000000 / 745795440389) ≤ (49980407 / 125000000) := by
  have h := checkLog_sound (w := (245795440389 / 1245795440389)) (n := 12)
    (lo := (79968651 / 200000000)) (hi := (49980407 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((745795440389 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(745795440389 / 500000000000) = 1/(500000000000 / 745795440389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6591 : Bounds (79968651 / 200000000) (49980407 / 125000000) (Real.log (745795440389 / 500000000000)) := by
  have h := reflection_log_6591_neg
  have he : Real.log (745795440389 / 500000000000) = -Real.log (500000000000 / 745795440389) := by
    rw [show ((745795440389 / 500000000000) : ℝ) = ((500000000000 / 745795440389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0103 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6592_neg : (180152539 / 1000000000) ≤ -Real.log (5000 / 5987) ∧
    -Real.log (5000 / 5987) ≤ (9007627 / 50000000) := by
  have h := checkLog_sound (w := (987 / 10987)) (n := 12)
    (lo := (180152539 / 1000000000)) (hi := (9007627 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5987 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5987 / 5000) = 1/(5000 / 5987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6592 : Bounds (180152539 / 1000000000) (9007627 / 50000000) (Real.log (5987 / 5000)) := by
  have h := reflection_log_6592_neg
  have he : Real.log (5987 / 5000) = -Real.log (5000 / 5987) := by
    rw [show ((5987 / 5000) : ℝ) = ((5000 / 5987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6593_neg : (219898821 / 1000000000) ≤ -Real.log (4013 / 5000) ∧
    -Real.log (4013 / 5000) ≤ (109949411 / 500000000) := by
  have h := checkLog_sound (w := (987 / 9013)) (n := 12)
    (lo := (219898821 / 1000000000)) (hi := (109949411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4013) = 1/(4013 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6593 : Bounds (-109949411 / 500000000) (-219898821 / 1000000000) (Real.log (4013 / 5000)) := by
  have h := reflection_log_6593_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6594_neg : (9869 / 50000000) ≤ -Real.log (5000000 / 5000987) ∧
    -Real.log (5000000 / 5000987) ≤ (197381 / 1000000000) := by
  have h := checkLog_sound (w := (987 / 10000987)) (n := 12)
    (lo := (9869 / 50000000)) (hi := (197381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000987 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000987 / 5000000) = 1/(5000000 / 5000987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6594 : Bounds (9869 / 50000000) (197381 / 1000000000) (Real.log (5000987 / 5000000)) := by
  have h := reflection_log_6594_neg
  have he : Real.log (5000987 / 5000000) = -Real.log (5000000 / 5000987) := by
    rw [show ((5000987 / 5000000) : ℝ) = ((5000000 / 5000987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6595_neg : (197419 / 1000000000) ≤ -Real.log (4999013 / 5000000) ∧
    -Real.log (4999013 / 5000000) ≤ (9871 / 50000000) := by
  have h := checkLog_sound (w := (987 / 9999013)) (n := 12)
    (lo := (197419 / 1000000000)) (hi := (9871 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999013) = 1/(4999013 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6595 : Bounds (-9871 / 50000000) (-197419 / 1000000000) (Real.log (4999013 / 5000000)) := by
  have h := reflection_log_6595_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6596_neg : (23657487 / 250000000) ≤ -Real.log (250000 / 274813) ∧
    -Real.log (250000 / 274813) ≤ (94629949 / 1000000000) := by
  have h := checkLog_sound (w := (24813 / 524813)) (n := 12)
    (lo := (23657487 / 250000000)) (hi := (94629949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274813 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274813 / 250000) = 1/(250000 / 274813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6596 : Bounds (23657487 / 250000000) (94629949 / 1000000000) (Real.log (274813 / 250000)) := by
  have h := reflection_log_6596_neg
  have he : Real.log (274813 / 250000) = -Real.log (250000 / 274813) := by
    rw [show ((274813 / 250000) : ℝ) = ((250000 / 274813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6597_neg : (104529749 / 1000000000) ≤ -Real.log (225187 / 250000) ∧
    -Real.log (225187 / 250000) ≤ (418119 / 4000000) := by
  have h := checkLog_sound (w := (24813 / 475187)) (n := 12)
    (lo := (104529749 / 1000000000)) (hi := (418119 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225187) = 1/(225187 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6597 : Bounds (-418119 / 4000000) (-104529749 / 1000000000) (Real.log (225187 / 250000)) := by
  have h := reflection_log_6597_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6598_neg : (94855531 / 1000000000) ≤ -Real.log (2000 / 2199) ∧
    -Real.log (2000 / 2199) ≤ (23713883 / 250000000) := by
  have h := checkLog_sound (w := (199 / 4199)) (n := 12)
    (lo := (94855531 / 1000000000)) (hi := (23713883 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2199 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2199 / 2000) = 1/(2000 / 2199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6598 : Bounds (94855531 / 1000000000) (23713883 / 250000000) (Real.log (2199 / 2000)) := by
  have h := reflection_log_6598_neg
  have he : Real.log (2199 / 2000) = -Real.log (2000 / 2199) := by
    rw [show ((2199 / 2000) : ℝ) = ((2000 / 2199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6599_neg : (52402557 / 500000000) ≤ -Real.log (1801 / 2000) ∧
    -Real.log (1801 / 2000) ≤ (20961023 / 200000000) := by
  have h := checkLog_sound (w := (199 / 3801)) (n := 12)
    (lo := (52402557 / 500000000)) (hi := (20961023 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1801) = 1/(1801 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6599 : Bounds (-20961023 / 200000000) (-52402557 / 500000000) (Real.log (1801 / 2000)) := by
  have h := reflection_log_6599_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6600_neg : (9949583 / 1000000000) ≤ -Real.log (3960399 / 4000000) ∧
    -Real.log (3960399 / 4000000) ≤ (621849 / 62500000) := by
  have h := checkLog_sound (w := (39601 / 7960399)) (n := 12)
    (lo := (9949583 / 1000000000)) (hi := (621849 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000000 / 3960399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000000 / 3960399) = 1/(3960399 / 4000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6600 : Bounds (-621849 / 62500000) (-9949583 / 1000000000) (Real.log (3960399 / 4000000)) := by
  have h := reflection_log_6600_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6601_neg : (9899801 / 1000000000) ≤ -Real.log (61884315031 / 62500000000) ∧
    -Real.log (61884315031 / 62500000000) ≤ (4949901 / 500000000) := by
  have h := checkLog_sound (w := (615684969 / 124384315031)) (n := 12)
    (lo := (9899801 / 1000000000)) (hi := (4949901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61884315031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61884315031) = 1/(61884315031 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6601 : Bounds (-4949901 / 500000000) (-9899801 / 1000000000) (Real.log (61884315031 / 62500000000)) := by
  have h := reflection_log_6601_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6602_neg : (99579849 / 500000000) ≤ -Real.log (250000000000 / 305094210589) ∧
    -Real.log (250000000000 / 305094210589) ≤ (199159699 / 1000000000) := by
  have h := checkLog_sound (w := (55094210589 / 555094210589)) (n := 12)
    (lo := (99579849 / 500000000)) (hi := (199159699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305094210589 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305094210589 / 250000000000) = 1/(250000000000 / 305094210589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6602 : Bounds (99579849 / 500000000) (199159699 / 1000000000) (Real.log (305094210589 / 250000000000)) := by
  have h := reflection_log_6602_neg
  have he : Real.log (305094210589 / 250000000000) = -Real.log (250000000000 / 305094210589) := by
    rw [show ((305094210589 / 250000000000) : ℝ) = ((250000000000 / 305094210589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6603_neg : (39932129 / 200000000) ≤ -Real.log (250000000000 / 305247084953) ∧
    -Real.log (250000000000 / 305247084953) ≤ (99830323 / 500000000) := by
  have h := checkLog_sound (w := (55247084953 / 555247084953)) (n := 12)
    (lo := (39932129 / 200000000)) (hi := (99830323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305247084953 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305247084953 / 250000000000) = 1/(250000000000 / 305247084953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6603 : Bounds (39932129 / 200000000) (99830323 / 500000000) (Real.log (305247084953 / 250000000000)) := by
  have h := reflection_log_6603_neg
  have he : Real.log (305247084953 / 250000000000) = -Real.log (250000000000 / 305247084953) := by
    rw [show ((305247084953 / 250000000000) : ℝ) = ((250000000000 / 305247084953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6604_neg : (79968651 / 200000000) ≤ -Real.log (125000000000 / 186448860097) ∧
    -Real.log (125000000000 / 186448860097) ≤ (49980407 / 125000000) := by
  have h := checkLog_sound (w := (61448860097 / 311448860097)) (n := 12)
    (lo := (79968651 / 200000000)) (hi := (49980407 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186448860097 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186448860097 / 125000000000) = 1/(125000000000 / 186448860097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6604 : Bounds (79968651 / 200000000) (49980407 / 125000000) (Real.log (186448860097 / 125000000000)) := by
  have h := reflection_log_6604_neg
  have he : Real.log (186448860097 / 125000000000) = -Real.log (125000000000 / 186448860097) := by
    rw [show ((186448860097 / 125000000000) : ℝ) = ((125000000000 / 186448860097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6605_neg : (2500321 / 6250000) ≤ -Real.log (250000000000 / 372975330177) ∧
    -Real.log (250000000000 / 372975330177) ≤ (400051361 / 1000000000) := by
  have h := checkLog_sound (w := (122975330177 / 622975330177)) (n := 12)
    (lo := (2500321 / 6250000)) (hi := (400051361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372975330177 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372975330177 / 250000000000) = 1/(250000000000 / 372975330177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6605 : Bounds (2500321 / 6250000) (400051361 / 1000000000) (Real.log (372975330177 / 250000000000)) := by
  have h := reflection_log_6605_neg
  have he : Real.log (372975330177 / 250000000000) = -Real.log (250000000000 / 372975330177) := by
    rw [show ((372975330177 / 250000000000) : ℝ) = ((250000000000 / 372975330177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6606_neg : (3604721 / 20000000) ≤ -Real.log (400 / 479) ∧
    -Real.log (400 / 479) ≤ (180236051 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 879)) (n := 12)
    (lo := (3604721 / 20000000)) (hi := (180236051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((479 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(479 / 400) = 1/(400 / 479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6606 : Bounds (3604721 / 20000000) (180236051 / 1000000000) (Real.log (479 / 400)) := by
  have h := reflection_log_6606_neg
  have he : Real.log (479 / 400) = -Real.log (400 / 479) := by
    rw [show ((479 / 400) : ℝ) = ((400 / 479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6607_neg : (220023423 / 1000000000) ≤ -Real.log (321 / 400) ∧
    -Real.log (321 / 400) ≤ (1718933 / 7812500) := by
  have h := checkLog_sound (w := (79 / 721)) (n := 12)
    (lo := (220023423 / 1000000000)) (hi := (1718933 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 321) = 1/(321 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6607 : Bounds (-1718933 / 7812500) (-220023423 / 1000000000) (Real.log (321 / 400)) := by
  have h := reflection_log_6607_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6608_neg : (4937 / 25000000) ≤ -Real.log (400000 / 400079) ∧
    -Real.log (400000 / 400079) ≤ (197481 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 800079)) (n := 12)
    (lo := (4937 / 25000000)) (hi := (197481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400079 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400079 / 400000) = 1/(400000 / 400079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6608 : Bounds (4937 / 25000000) (197481 / 1000000000) (Real.log (400079 / 400000)) := by
  have h := reflection_log_6608_neg
  have he : Real.log (400079 / 400000) = -Real.log (400000 / 400079) := by
    rw [show ((400079 / 400000) : ℝ) = ((400000 / 400079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6609_neg : (197519 / 1000000000) ≤ -Real.log (399921 / 400000) ∧
    -Real.log (399921 / 400000) ≤ (2469 / 12500000) := by
  have h := checkLog_sound (w := (79 / 799921)) (n := 12)
    (lo := (197519 / 1000000000)) (hi := (2469 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399921) = 1/(399921 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6609 : Bounds (-2469 / 12500000) (-197519 / 1000000000) (Real.log (399921 / 400000)) := by
  have h := reflection_log_6609_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6610_neg : (47338171 / 500000000) ≤ -Real.log (1000000 / 1099303) ∧
    -Real.log (1000000 / 1099303) ≤ (94676343 / 1000000000) := by
  have h := checkLog_sound (w := (99303 / 2099303)) (n := 12)
    (lo := (47338171 / 500000000)) (hi := (94676343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099303 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099303 / 1000000) = 1/(1000000 / 1099303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6610 : Bounds (47338171 / 500000000) (94676343 / 1000000000) (Real.log (1099303 / 1000000)) := by
  have h := reflection_log_6610_neg
  have he : Real.log (1099303 / 1000000) = -Real.log (1000000 / 1099303) := by
    rw [show ((1099303 / 1000000) : ℝ) = ((1000000 / 1099303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6611_neg : (10458637 / 100000000) ≤ -Real.log (900697 / 1000000) ∧
    -Real.log (900697 / 1000000) ≤ (104586371 / 1000000000) := by
  have h := checkLog_sound (w := (99303 / 1900697)) (n := 12)
    (lo := (10458637 / 100000000)) (hi := (104586371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900697) = 1/(900697 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6611 : Bounds (-104586371 / 1000000000) (-10458637 / 100000000) (Real.log (900697 / 1000000)) := by
  have h := reflection_log_6611_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6612_neg : (47450957 / 500000000) ≤ -Real.log (1000000 / 1099551) ∧
    -Real.log (1000000 / 1099551) ≤ (18980383 / 200000000) := by
  have h := checkLog_sound (w := (99551 / 2099551)) (n := 12)
    (lo := (47450957 / 500000000)) (hi := (18980383 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099551 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099551 / 1000000) = 1/(1000000 / 1099551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6612 : Bounds (47450957 / 500000000) (18980383 / 200000000) (Real.log (1099551 / 1000000)) := by
  have h := reflection_log_6612_neg
  have he : Real.log (1099551 / 1000000) = -Real.log (1000000 / 1099551) := by
    rw [show ((1099551 / 1000000) : ℝ) = ((1000000 / 1099551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6613_neg : (104861751 / 1000000000) ≤ -Real.log (900449 / 1000000) ∧
    -Real.log (900449 / 1000000) ≤ (13107719 / 125000000) := by
  have h := checkLog_sound (w := (99551 / 1900449)) (n := 12)
    (lo := (104861751 / 1000000000)) (hi := (13107719 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900449) = 1/(900449 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6613 : Bounds (-13107719 / 125000000) (-104861751 / 1000000000) (Real.log (900449 / 1000000)) := by
  have h := reflection_log_6613_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6614_neg : (2489959 / 250000000) ≤ -Real.log (990089598399 / 1000000000000) ∧
    -Real.log (990089598399 / 1000000000000) ≤ (9959837 / 1000000000) := by
  have h := checkLog_sound (w := (9910401601 / 1990089598399)) (n := 12)
    (lo := (2489959 / 250000000)) (hi := (9959837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990089598399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990089598399) = 1/(990089598399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6614 : Bounds (-9959837 / 1000000000) (-2489959 / 250000000) (Real.log (990089598399 / 1000000000000)) := by
  have h := reflection_log_6614_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6615_neg : (2477507 / 250000000) ≤ -Real.log (990138914191 / 1000000000000) ∧
    -Real.log (990138914191 / 1000000000000) ≤ (9910029 / 1000000000) := by
  have h := checkLog_sound (w := (9861085809 / 1990138914191)) (n := 12)
    (lo := (2477507 / 250000000)) (hi := (9910029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990138914191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990138914191) = 1/(990138914191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6615 : Bounds (-9910029 / 1000000000) (-2477507 / 250000000) (Real.log (990138914191 / 1000000000000)) := by
  have h := reflection_log_6615_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6616_neg : (199262713 / 1000000000) ≤ -Real.log (125000000000 / 152562820793) ∧
    -Real.log (125000000000 / 152562820793) ≤ (99631357 / 500000000) := by
  have h := checkLog_sound (w := (27562820793 / 277562820793)) (n := 12)
    (lo := (199262713 / 1000000000)) (hi := (99631357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152562820793 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152562820793 / 125000000000) = 1/(125000000000 / 152562820793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6616 : Bounds (199262713 / 1000000000) (99631357 / 500000000) (Real.log (152562820793 / 125000000000)) := by
  have h := reflection_log_6616_neg
  have he : Real.log (152562820793 / 125000000000) = -Real.log (125000000000 / 152562820793) := by
    rw [show ((152562820793 / 125000000000) : ℝ) = ((125000000000 / 152562820793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6617_neg : (39952733 / 200000000) ≤ -Real.log (500000000000 / 610557066531) ∧
    -Real.log (500000000000 / 610557066531) ≤ (99881833 / 500000000) := by
  have h := checkLog_sound (w := (110557066531 / 1110557066531)) (n := 12)
    (lo := (39952733 / 200000000)) (hi := (99881833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610557066531 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(610557066531 / 500000000000) = 1/(500000000000 / 610557066531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6617 : Bounds (39952733 / 200000000) (99881833 / 500000000) (Real.log (610557066531 / 500000000000)) := by
  have h := reflection_log_6617_neg
  have he : Real.log (610557066531 / 500000000000) = -Real.log (500000000000 / 610557066531) := by
    rw [show ((610557066531 / 500000000000) : ℝ) = ((500000000000 / 610557066531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6618_neg : (2500321 / 6250000) ≤ -Real.log (500000000000 / 745950660353) ∧
    -Real.log (500000000000 / 745950660353) ≤ (400051361 / 1000000000) := by
  have h := checkLog_sound (w := (245950660353 / 1245950660353)) (n := 12)
    (lo := (2500321 / 6250000)) (hi := (400051361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((745950660353 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(745950660353 / 500000000000) = 1/(500000000000 / 745950660353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6618 : Bounds (2500321 / 6250000) (400051361 / 1000000000) (Real.log (745950660353 / 500000000000)) := by
  have h := reflection_log_6618_neg
  have he : Real.log (745950660353 / 500000000000) = -Real.log (500000000000 / 745950660353) := by
    rw [show ((745950660353 / 500000000000) : ℝ) = ((500000000000 / 745950660353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6619_neg : (200129737 / 500000000) ≤ -Real.log (125000000000 / 186526479751) ∧
    -Real.log (125000000000 / 186526479751) ≤ (16010379 / 40000000) := by
  have h := checkLog_sound (w := (61526479751 / 311526479751)) (n := 12)
    (lo := (200129737 / 500000000)) (hi := (16010379 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186526479751 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186526479751 / 125000000000) = 1/(125000000000 / 186526479751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6619 : Bounds (200129737 / 500000000) (16010379 / 40000000) (Real.log (186526479751 / 125000000000)) := by
  have h := reflection_log_6619_neg
  have he : Real.log (186526479751 / 125000000000) = -Real.log (125000000000 / 186526479751) := by
    rw [show ((186526479751 / 125000000000) : ℝ) = ((125000000000 / 186526479751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6620_neg : (90159777 / 500000000) ≤ -Real.log (1250 / 1497) ∧
    -Real.log (1250 / 1497) ≤ (36063911 / 200000000) := by
  have h := checkLog_sound (w := (247 / 2747)) (n := 12)
    (lo := (90159777 / 500000000)) (hi := (36063911 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1497 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1497 / 1250) = 1/(1250 / 1497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6620 : Bounds (90159777 / 500000000) (36063911 / 200000000) (Real.log (1497 / 1250)) := by
  have h := reflection_log_6620_neg
  have he : Real.log (1497 / 1250) = -Real.log (1250 / 1497) := by
    rw [show ((1497 / 1250) : ℝ) = ((1250 / 1497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6621_neg : (110074021 / 500000000) ≤ -Real.log (1003 / 1250) ∧
    -Real.log (1003 / 1250) ≤ (220148043 / 1000000000) := by
  have h := checkLog_sound (w := (247 / 2253)) (n := 12)
    (lo := (110074021 / 500000000)) (hi := (220148043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1003) = 1/(1003 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6621 : Bounds (-220148043 / 1000000000) (-110074021 / 500000000) (Real.log (1003 / 1250)) := by
  have h := reflection_log_6621_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6622_neg : (9879 / 50000000) ≤ -Real.log (1250000 / 1250247) ∧
    -Real.log (1250000 / 1250247) ≤ (197581 / 1000000000) := by
  have h := checkLog_sound (w := (247 / 2500247)) (n := 12)
    (lo := (9879 / 50000000)) (hi := (197581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250247 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250247 / 1250000) = 1/(1250000 / 1250247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6622 : Bounds (9879 / 50000000) (197581 / 1000000000) (Real.log (1250247 / 1250000)) := by
  have h := reflection_log_6622_neg
  have he : Real.log (1250247 / 1250000) = -Real.log (1250000 / 1250247) := by
    rw [show ((1250247 / 1250000) : ℝ) = ((1250000 / 1250247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6623_neg : (197619 / 1000000000) ≤ -Real.log (1249753 / 1250000) ∧
    -Real.log (1249753 / 1250000) ≤ (9881 / 50000000) := by
  have h := checkLog_sound (w := (247 / 2499753)) (n := 12)
    (lo := (197619 / 1000000000)) (hi := (9881 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249753) = 1/(1249753 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6623 : Bounds (-9881 / 50000000) (-197619 / 1000000000) (Real.log (1249753 / 1250000)) := by
  have h := reflection_log_6623_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6624_neg : (47361367 / 500000000) ≤ -Real.log (500000 / 549677) ∧
    -Real.log (500000 / 549677) ≤ (18944547 / 200000000) := by
  have h := checkLog_sound (w := (49677 / 1049677)) (n := 12)
    (lo := (47361367 / 500000000)) (hi := (18944547 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549677 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549677 / 500000) = 1/(500000 / 549677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6624 : Bounds (47361367 / 500000000) (18944547 / 200000000) (Real.log (549677 / 500000)) := by
  have h := reflection_log_6624_neg
  have he : Real.log (549677 / 500000) = -Real.log (500000 / 549677) := by
    rw [show ((549677 / 500000) : ℝ) = ((500000 / 549677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6625_neg : (20928599 / 200000000) ≤ -Real.log (450323 / 500000) ∧
    -Real.log (450323 / 500000) ≤ (26160749 / 250000000) := by
  have h := checkLog_sound (w := (49677 / 950323)) (n := 12)
    (lo := (20928599 / 200000000)) (hi := (26160749 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450323) = 1/(450323 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6625 : Bounds (-26160749 / 250000000) (-20928599 / 200000000) (Real.log (450323 / 500000)) := by
  have h := reflection_log_6625_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6626_neg : (11868537 / 125000000) ≤ -Real.log (500000 / 549801) ∧
    -Real.log (500000 / 549801) ≤ (94948297 / 1000000000) := by
  have h := checkLog_sound (w := (49801 / 1049801)) (n := 12)
    (lo := (11868537 / 125000000)) (hi := (94948297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549801 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549801 / 500000) = 1/(500000 / 549801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6626 : Bounds (11868537 / 125000000) (94948297 / 1000000000) (Real.log (549801 / 500000)) := by
  have h := reflection_log_6626_neg
  have he : Real.log (549801 / 500000) = -Real.log (500000 / 549801) := by
    rw [show ((549801 / 500000) : ℝ) = ((500000 / 549801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6627_neg : (104918391 / 1000000000) ≤ -Real.log (450199 / 500000) ∧
    -Real.log (450199 / 500000) ≤ (13114799 / 125000000) := by
  have h := checkLog_sound (w := (49801 / 950199)) (n := 12)
    (lo := (104918391 / 1000000000)) (hi := (13114799 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450199) = 1/(450199 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6627 : Bounds (-13114799 / 125000000) (-104918391 / 1000000000) (Real.log (450199 / 500000)) := by
  have h := reflection_log_6627_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6628_neg : (1994019 / 200000000) ≤ -Real.log (247519860399 / 250000000000) ∧
    -Real.log (247519860399 / 250000000000) ≤ (623131 / 62500000) := by
  have h := checkLog_sound (w := (2480139601 / 497519860399)) (n := 12)
    (lo := (1994019 / 200000000)) (hi := (623131 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247519860399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247519860399) = 1/(247519860399 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6628 : Bounds (-623131 / 62500000) (-1994019 / 200000000) (Real.log (247519860399 / 250000000000)) := by
  have h := reflection_log_6628_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6629_neg : (496013 / 50000000) ≤ -Real.log (247532195671 / 250000000000) ∧
    -Real.log (247532195671 / 250000000000) ≤ (9920261 / 1000000000) := by
  have h := checkLog_sound (w := (2467804329 / 497532195671)) (n := 12)
    (lo := (496013 / 50000000)) (hi := (9920261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247532195671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247532195671) = 1/(247532195671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6629 : Bounds (-9920261 / 1000000000) (-496013 / 50000000) (Real.log (247532195671 / 250000000000)) := by
  have h := reflection_log_6629_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6630_neg : (199365729 / 1000000000) ≤ -Real.log (250000000000 / 305157076143) ∧
    -Real.log (250000000000 / 305157076143) ≤ (19936573 / 100000000) := by
  have h := checkLog_sound (w := (55157076143 / 555157076143)) (n := 12)
    (lo := (199365729 / 1000000000)) (hi := (19936573 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305157076143 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305157076143 / 250000000000) = 1/(250000000000 / 305157076143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6630 : Bounds (199365729 / 1000000000) (19936573 / 100000000) (Real.log (305157076143 / 250000000000)) := by
  have h := reflection_log_6630_neg
  have he : Real.log (305157076143 / 250000000000) = -Real.log (250000000000 / 305157076143) := by
    rw [show ((305157076143 / 250000000000) : ℝ) = ((250000000000 / 305157076143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6631_neg : (199866687 / 1000000000) ≤ -Real.log (12500000000 / 15265499257) ∧
    -Real.log (12500000000 / 15265499257) ≤ (3122917 / 15625000) := by
  have h := checkLog_sound (w := (2765499257 / 27765499257)) (n := 12)
    (lo := (199866687 / 1000000000)) (hi := (3122917 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15265499257 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15265499257 / 12500000000) = 1/(12500000000 / 15265499257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6631 : Bounds (199866687 / 1000000000) (3122917 / 15625000) (Real.log (15265499257 / 12500000000)) := by
  have h := reflection_log_6631_neg
  have he : Real.log (15265499257 / 12500000000) = -Real.log (12500000000 / 15265499257) := by
    rw [show ((15265499257 / 12500000000) : ℝ) = ((12500000000 / 15265499257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6632_neg : (200129737 / 500000000) ≤ -Real.log (500000000000 / 746105919003) ∧
    -Real.log (500000000000 / 746105919003) ≤ (16010379 / 40000000) := by
  have h := checkLog_sound (w := (246105919003 / 1246105919003)) (n := 12)
    (lo := (200129737 / 500000000)) (hi := (16010379 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746105919003 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746105919003 / 500000000000) = 1/(500000000000 / 746105919003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6632 : Bounds (200129737 / 500000000) (16010379 / 40000000) (Real.log (746105919003 / 500000000000)) := by
  have h := reflection_log_6632_neg
  have he : Real.log (746105919003 / 500000000000) = -Real.log (500000000000 / 746105919003) := by
    rw [show ((746105919003 / 500000000000) : ℝ) = ((500000000000 / 746105919003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6633_neg : (100116899 / 250000000) ≤ -Real.log (500000000000 / 746261216351) ∧
    -Real.log (500000000000 / 746261216351) ≤ (400467597 / 1000000000) := by
  have h := checkLog_sound (w := (246261216351 / 1246261216351)) (n := 12)
    (lo := (100116899 / 250000000)) (hi := (400467597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746261216351 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746261216351 / 500000000000) = 1/(500000000000 / 746261216351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6633 : Bounds (100116899 / 250000000) (400467597 / 1000000000) (Real.log (746261216351 / 500000000000)) := by
  have h := reflection_log_6633_neg
  have he : Real.log (746261216351 / 500000000000) = -Real.log (500000000000 / 746261216351) := by
    rw [show ((746261216351 / 500000000000) : ℝ) = ((500000000000 / 746261216351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6634_neg : (3608061 / 20000000) ≤ -Real.log (10000 / 11977) ∧
    -Real.log (10000 / 11977) ≤ (180403051 / 1000000000) := by
  have h := checkLog_sound (w := (1977 / 21977)) (n := 12)
    (lo := (3608061 / 20000000)) (hi := (180403051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11977 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11977 / 10000) = 1/(10000 / 11977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6634 : Bounds (3608061 / 20000000) (180403051 / 1000000000) (Real.log (11977 / 10000)) := by
  have h := reflection_log_6634_neg
  have he : Real.log (11977 / 10000) = -Real.log (10000 / 11977) := by
    rw [show ((11977 / 10000) : ℝ) = ((10000 / 11977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6635_neg : (55068169 / 250000000) ≤ -Real.log (8023 / 10000) ∧
    -Real.log (8023 / 10000) ≤ (220272677 / 1000000000) := by
  have h := checkLog_sound (w := (1977 / 18023)) (n := 12)
    (lo := (55068169 / 250000000)) (hi := (220272677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8023) = 1/(8023 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6635 : Bounds (-220272677 / 1000000000) (-55068169 / 250000000) (Real.log (8023 / 10000)) := by
  have h := reflection_log_6635_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6636_neg : (2471 / 12500000) ≤ -Real.log (10000000 / 10001977) ∧
    -Real.log (10000000 / 10001977) ≤ (197681 / 1000000000) := by
  have h := checkLog_sound (w := (1977 / 20001977)) (n := 12)
    (lo := (2471 / 12500000)) (hi := (197681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001977 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001977 / 10000000) = 1/(10000000 / 10001977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6636 : Bounds (2471 / 12500000) (197681 / 1000000000) (Real.log (10001977 / 10000000)) := by
  have h := reflection_log_6636_neg
  have he : Real.log (10001977 / 10000000) = -Real.log (10000000 / 10001977) := by
    rw [show ((10001977 / 10000000) : ℝ) = ((10000000 / 10001977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6637_neg : (197719 / 1000000000) ≤ -Real.log (9998023 / 10000000) ∧
    -Real.log (9998023 / 10000000) ≤ (4943 / 25000000) := by
  have h := checkLog_sound (w := (1977 / 19998023)) (n := 12)
    (lo := (197719 / 1000000000)) (hi := (4943 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998023) = 1/(9998023 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6637 : Bounds (-4943 / 25000000) (-197719 / 1000000000) (Real.log (9998023 / 10000000)) := by
  have h := reflection_log_6637_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6638_neg : (23692281 / 250000000) ≤ -Real.log (200000 / 219881) ∧
    -Real.log (200000 / 219881) ≤ (758153 / 8000000) := by
  have h := checkLog_sound (w := (19881 / 419881)) (n := 12)
    (lo := (23692281 / 250000000)) (hi := (758153 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219881 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219881 / 200000) = 1/(200000 / 219881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6638 : Bounds (23692281 / 250000000) (758153 / 8000000) (Real.log (219881 / 200000)) := by
  have h := reflection_log_6638_neg
  have he : Real.log (219881 / 200000) = -Real.log (200000 / 219881) := by
    rw [show ((219881 / 200000) : ℝ) = ((200000 / 219881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6639_neg : (52349811 / 500000000) ≤ -Real.log (180119 / 200000) ∧
    -Real.log (180119 / 200000) ≤ (104699623 / 1000000000) := by
  have h := checkLog_sound (w := (19881 / 380119)) (n := 12)
    (lo := (52349811 / 500000000)) (hi := (104699623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180119) = 1/(180119 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6639 : Bounds (-104699623 / 1000000000) (-52349811 / 500000000) (Real.log (180119 / 200000)) := by
  have h := reflection_log_6639_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6640_neg : (3799787 / 40000000) ≤ -Real.log (1000000 / 1099653) ∧
    -Real.log (1000000 / 1099653) ≤ (23748669 / 250000000) := by
  have h := checkLog_sound (w := (99653 / 2099653)) (n := 12)
    (lo := (3799787 / 40000000)) (hi := (23748669 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099653 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099653 / 1000000) = 1/(1000000 / 1099653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6640 : Bounds (3799787 / 40000000) (23748669 / 250000000) (Real.log (1099653 / 1000000)) := by
  have h := reflection_log_6640_neg
  have he : Real.log (1099653 / 1000000) = -Real.log (1000000 / 1099653) := by
    rw [show ((1099653 / 1000000) : ℝ) = ((1000000 / 1099653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6641_neg : (52487517 / 500000000) ≤ -Real.log (900347 / 1000000) ∧
    -Real.log (900347 / 1000000) ≤ (20995007 / 200000000) := by
  have h := checkLog_sound (w := (99653 / 1900347)) (n := 12)
    (lo := (52487517 / 500000000)) (hi := (20995007 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900347) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900347) = 1/(900347 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6641 : Bounds (-20995007 / 200000000) (-52487517 / 500000000) (Real.log (900347 / 1000000)) := by
  have h := reflection_log_6641_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6642_neg : (4990179 / 500000000) ≤ -Real.log (990069279591 / 1000000000000) ∧
    -Real.log (990069279591 / 1000000000000) ≤ (9980359 / 1000000000) := by
  have h := checkLog_sound (w := (9930720409 / 1990069279591)) (n := 12)
    (lo := (4990179 / 500000000)) (hi := (9980359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990069279591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990069279591) = 1/(990069279591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6642 : Bounds (-9980359 / 1000000000) (-4990179 / 500000000) (Real.log (990069279591 / 1000000000000)) := by
  have h := reflection_log_6642_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6643_neg : (4965249 / 500000000) ≤ -Real.log (39604745839 / 40000000000) ∧
    -Real.log (39604745839 / 40000000000) ≤ (9930499 / 1000000000) := by
  have h := checkLog_sound (w := (395254161 / 79604745839)) (n := 12)
    (lo := (4965249 / 500000000)) (hi := (9930499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39604745839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39604745839) = 1/(39604745839 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6643 : Bounds (-9930499 / 1000000000) (-4965249 / 500000000) (Real.log (39604745839 / 40000000000)) := by
  have h := reflection_log_6643_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6644_neg : (199468747 / 1000000000) ≤ -Real.log (12500000000 / 15259425713) ∧
    -Real.log (12500000000 / 15259425713) ≤ (49867187 / 250000000) := by
  have h := checkLog_sound (w := (2759425713 / 27759425713)) (n := 12)
    (lo := (199468747 / 1000000000)) (hi := (49867187 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15259425713 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15259425713 / 12500000000) = 1/(12500000000 / 15259425713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6644 : Bounds (199468747 / 1000000000) (49867187 / 250000000) (Real.log (15259425713 / 12500000000)) := by
  have h := reflection_log_6644_neg
  have he : Real.log (15259425713 / 12500000000) = -Real.log (12500000000 / 15259425713) := by
    rw [show ((15259425713 / 12500000000) : ℝ) = ((12500000000 / 15259425713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6645_neg : (199969709 / 1000000000) ≤ -Real.log (125000000000 / 152670720289) ∧
    -Real.log (125000000000 / 152670720289) ≤ (19996971 / 100000000) := by
  have h := checkLog_sound (w := (27670720289 / 277670720289)) (n := 12)
    (lo := (199969709 / 1000000000)) (hi := (19996971 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152670720289 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152670720289 / 125000000000) = 1/(125000000000 / 152670720289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6645 : Bounds (199969709 / 1000000000) (19996971 / 100000000) (Real.log (152670720289 / 125000000000)) := by
  have h := reflection_log_6645_neg
  have he : Real.log (152670720289 / 125000000000) = -Real.log (125000000000 / 152670720289) := by
    rw [show ((152670720289 / 125000000000) : ℝ) = ((125000000000 / 152670720289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6646_neg : (100116899 / 250000000) ≤ -Real.log (10000000000 / 14925224327) ∧
    -Real.log (10000000000 / 14925224327) ≤ (400467597 / 1000000000) := by
  have h := checkLog_sound (w := (4925224327 / 24925224327)) (n := 12)
    (lo := (100116899 / 250000000)) (hi := (400467597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14925224327 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14925224327 / 10000000000) = 1/(10000000000 / 14925224327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6646 : Bounds (100116899 / 250000000) (400467597 / 1000000000) (Real.log (14925224327 / 10000000000)) := by
  have h := reflection_log_6646_neg
  have he : Real.log (14925224327 / 10000000000) = -Real.log (10000000000 / 14925224327) := by
    rw [show ((14925224327 / 10000000000) : ℝ) = ((10000000000 / 14925224327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6647_neg : (400675727 / 1000000000) ≤ -Real.log (125000000000 / 186604138103) ∧
    -Real.log (125000000000 / 186604138103) ≤ (25042233 / 62500000) := by
  have h := checkLog_sound (w := (61604138103 / 311604138103)) (n := 12)
    (lo := (400675727 / 1000000000)) (hi := (25042233 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186604138103 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186604138103 / 125000000000) = 1/(125000000000 / 186604138103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6647 : Bounds (400675727 / 1000000000) (25042233 / 62500000) (Real.log (186604138103 / 125000000000)) := by
  have h := reflection_log_6647_neg
  have he : Real.log (186604138103 / 125000000000) = -Real.log (125000000000 / 186604138103) := by
    rw [show ((186604138103 / 125000000000) : ℝ) = ((125000000000 / 186604138103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6648_neg : (9024327 / 50000000) ≤ -Real.log (5000 / 5989) ∧
    -Real.log (5000 / 5989) ≤ (180486541 / 1000000000) := by
  have h := checkLog_sound (w := (989 / 10989)) (n := 12)
    (lo := (9024327 / 50000000)) (hi := (180486541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5989 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5989 / 5000) = 1/(5000 / 5989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6648 : Bounds (9024327 / 50000000) (180486541 / 1000000000) (Real.log (5989 / 5000)) := by
  have h := reflection_log_6648_neg
  have he : Real.log (5989 / 5000) = -Real.log (5000 / 5989) := by
    rw [show ((5989 / 5000) : ℝ) = ((5000 / 5989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6649_neg : (8815893 / 40000000) ≤ -Real.log (4011 / 5000) ∧
    -Real.log (4011 / 5000) ≤ (110198663 / 500000000) := by
  have h := checkLog_sound (w := (989 / 9011)) (n := 12)
    (lo := (8815893 / 40000000)) (hi := (110198663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4011) = 1/(4011 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6649 : Bounds (-110198663 / 500000000) (-8815893 / 40000000) (Real.log (4011 / 5000)) := by
  have h := reflection_log_6649_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6650_neg : (9889 / 50000000) ≤ -Real.log (5000000 / 5000989) ∧
    -Real.log (5000000 / 5000989) ≤ (197781 / 1000000000) := by
  have h := checkLog_sound (w := (989 / 10000989)) (n := 12)
    (lo := (9889 / 50000000)) (hi := (197781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000989 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000989 / 5000000) = 1/(5000000 / 5000989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6650 : Bounds (9889 / 50000000) (197781 / 1000000000) (Real.log (5000989 / 5000000)) := by
  have h := reflection_log_6650_neg
  have he : Real.log (5000989 / 5000000) = -Real.log (5000000 / 5000989) := by
    rw [show ((5000989 / 5000000) : ℝ) = ((5000000 / 5000989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6651_neg : (197819 / 1000000000) ≤ -Real.log (4999011 / 5000000) ∧
    -Real.log (4999011 / 5000000) ≤ (9891 / 50000000) := by
  have h := checkLog_sound (w := (989 / 9999011)) (n := 12)
    (lo := (197819 / 1000000000)) (hi := (9891 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999011) = 1/(4999011 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6651 : Bounds (-9891 / 50000000) (-197819 / 1000000000) (Real.log (4999011 / 5000000)) := by
  have h := reflection_log_6651_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6652_neg : (11851939 / 125000000) ≤ -Real.log (15625 / 17179) ∧
    -Real.log (15625 / 17179) ≤ (94815513 / 1000000000) := by
  have h := checkLog_sound (w := (777 / 16402)) (n := 12)
    (lo := (11851939 / 125000000)) (hi := (94815513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17179 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17179 / 15625) = 1/(15625 / 17179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6652 : Bounds (11851939 / 125000000) (94815513 / 1000000000) (Real.log (17179 / 15625)) := by
  have h := reflection_log_6652_neg
  have he : Real.log (17179 / 15625) = -Real.log (15625 / 17179) := by
    rw [show ((17179 / 15625) : ℝ) = ((15625 / 17179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6653_neg : (104756253 / 1000000000) ≤ -Real.log (14071 / 15625) ∧
    -Real.log (14071 / 15625) ≤ (52378127 / 500000000) := by
  have h := checkLog_sound (w := (777 / 14848)) (n := 12)
    (lo := (104756253 / 1000000000)) (hi := (52378127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 14071) = 1/(14071 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6653 : Bounds (-52378127 / 500000000) (-104756253 / 1000000000) (Real.log (14071 / 15625)) := by
  have h := reflection_log_6653_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6654_neg : (47520981 / 500000000) ≤ -Real.log (200000 / 219941) ∧
    -Real.log (200000 / 219941) ≤ (95041963 / 1000000000) := by
  have h := checkLog_sound (w := (19941 / 419941)) (n := 12)
    (lo := (47520981 / 500000000)) (hi := (95041963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219941 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219941 / 200000) = 1/(200000 / 219941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6654 : Bounds (47520981 / 500000000) (95041963 / 1000000000) (Real.log (219941 / 200000)) := by
  have h := reflection_log_6654_neg
  have he : Real.log (219941 / 200000) = -Real.log (200000 / 219941) := by
    rw [show ((219941 / 200000) : ℝ) = ((200000 / 219941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6655_neg : (105032791 / 1000000000) ≤ -Real.log (180059 / 200000) ∧
    -Real.log (180059 / 200000) ≤ (13129099 / 125000000) := by
  have h := checkLog_sound (w := (19941 / 380059)) (n := 12)
    (lo := (105032791 / 1000000000)) (hi := (13129099 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180059) = 1/(180059 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6655 : Bounds (-13129099 / 125000000) (-105032791 / 1000000000) (Real.log (180059 / 200000)) := by
  have h := reflection_log_6655_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


