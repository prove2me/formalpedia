-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0114__3_q01
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0114__3_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T10:26:43.542718+00:00
-- url     : https://prove2.me/theorems/99ab1cb2-52fa-4394-b19a-790afdbbbb63
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0114 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0115, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0114 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0115, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0116) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0114 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0115, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0116) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0114 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0115, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0116) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0114 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0115, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0116) (piece 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0114__3_q00

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0115 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7360_neg : (434719179 / 1000000000) ≤ -Real.log (125000000000 / 193066157761) ∧
    -Real.log (125000000000 / 193066157761) ≤ (21735959 / 50000000) := by
  have h := checkLog_sound (w := (68066157761 / 318066157761)) (n := 12)
    (lo := (434719179 / 1000000000)) (hi := (21735959 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((193066157761 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(193066157761 / 125000000000) = 1/(125000000000 / 193066157761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7360 : Bounds (434719179 / 1000000000) (21735959 / 50000000) (Real.log (193066157761 / 125000000000)) := by
  have h := reflection_log_7360_neg
  have he : Real.log (193066157761 / 125000000000) = -Real.log (125000000000 / 193066157761) := by
    rw [show ((193066157761 / 125000000000) : ℝ) = ((125000000000 / 193066157761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7361_neg : (194332469 / 1000000000) ≤ -Real.log (2000 / 2429) ∧
    -Real.log (2000 / 2429) ≤ (19433247 / 100000000) := by
  have h := checkLog_sound (w := (429 / 4429)) (n := 12)
    (lo := (194332469 / 1000000000)) (hi := (19433247 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2429 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2429 / 2000) = 1/(2000 / 2429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7361 : Bounds (194332469 / 1000000000) (19433247 / 100000000) (Real.log (2429 / 2000)) := by
  have h := reflection_log_7361_neg
  have he : Real.log (2429 / 2000) = -Real.log (2000 / 2429) := by
    rw [show ((2429 / 2000) : ℝ) = ((2000 / 2429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7362_neg : (241434821 / 1000000000) ≤ -Real.log (1571 / 2000) ∧
    -Real.log (1571 / 2000) ≤ (120717411 / 500000000) := by
  have h := checkLog_sound (w := (429 / 3571)) (n := 12)
    (lo := (241434821 / 1000000000)) (hi := (120717411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1571) = 1/(1571 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7362 : Bounds (-120717411 / 500000000) (-241434821 / 1000000000) (Real.log (1571 / 2000)) := by
  have h := reflection_log_7362_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7363_neg : (53619 / 250000000) ≤ -Real.log (2000000 / 2000429) ∧
    -Real.log (2000000 / 2000429) ≤ (214477 / 1000000000) := by
  have h := checkLog_sound (w := (429 / 4000429)) (n := 12)
    (lo := (53619 / 250000000)) (hi := (214477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000429 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000429 / 2000000) = 1/(2000000 / 2000429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7363 : Bounds (53619 / 250000000) (214477 / 1000000000) (Real.log (2000429 / 2000000)) := by
  have h := reflection_log_7363_neg
  have he : Real.log (2000429 / 2000000) = -Real.log (2000000 / 2000429) := by
    rw [show ((2000429 / 2000000) : ℝ) = ((2000000 / 2000429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7364_neg : (214523 / 1000000000) ≤ -Real.log (1999571 / 2000000) ∧
    -Real.log (1999571 / 2000000) ≤ (53631 / 250000000) := by
  have h := checkLog_sound (w := (429 / 3999571)) (n := 12)
    (lo := (214523 / 1000000000)) (hi := (53631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999571) = 1/(1999571 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7364 : Bounds (-53631 / 250000000) (-214523 / 1000000000) (Real.log (1999571 / 2000000)) := by
  have h := reflection_log_7364_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7365_neg : (12795767 / 125000000) ≤ -Real.log (1000000 / 1107789) ∧
    -Real.log (1000000 / 1107789) ≤ (102366137 / 1000000000) := by
  have h := checkLog_sound (w := (107789 / 2107789)) (n := 12)
    (lo := (12795767 / 125000000)) (hi := (102366137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1107789 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1107789 / 1000000) = 1/(1000000 / 1107789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7365 : Bounds (12795767 / 125000000) (102366137 / 1000000000) (Real.log (1107789 / 1000000)) := by
  have h := reflection_log_7365_neg
  have he : Real.log (1107789 / 1000000) = -Real.log (1000000 / 1107789) := by
    rw [show ((1107789 / 1000000) : ℝ) = ((1000000 / 1107789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7366_neg : (114052627 / 1000000000) ≤ -Real.log (892211 / 1000000) ∧
    -Real.log (892211 / 1000000) ≤ (28513157 / 250000000) := by
  have h := checkLog_sound (w := (107789 / 1892211)) (n := 12)
    (lo := (114052627 / 1000000000)) (hi := (28513157 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 892211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 892211) = 1/(892211 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7366 : Bounds (-28513157 / 250000000) (-114052627 / 1000000000) (Real.log (892211 / 1000000)) := by
  have h := reflection_log_7366_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7367_neg : (20558063 / 200000000) ≤ -Real.log (1000000 / 1108259) ∧
    -Real.log (1000000 / 1108259) ≤ (25697579 / 250000000) := by
  have h := checkLog_sound (w := (108259 / 2108259)) (n := 12)
    (lo := (20558063 / 200000000)) (hi := (25697579 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1108259 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1108259 / 1000000) = 1/(1000000 / 1108259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7367 : Bounds (20558063 / 200000000) (25697579 / 250000000) (Real.log (1108259 / 1000000)) := by
  have h := reflection_log_7367_neg
  have he : Real.log (1108259 / 1000000) = -Real.log (1000000 / 1108259) := by
    rw [show ((1108259 / 1000000) : ℝ) = ((1000000 / 1108259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7368_neg : (114579547 / 1000000000) ≤ -Real.log (891741 / 1000000) ∧
    -Real.log (891741 / 1000000) ≤ (28644887 / 250000000) := by
  have h := checkLog_sound (w := (108259 / 1891741)) (n := 12)
    (lo := (114579547 / 1000000000)) (hi := (28644887 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 891741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 891741) = 1/(891741 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7368 : Bounds (-28644887 / 250000000) (-114579547 / 1000000000) (Real.log (891741 / 1000000)) := by
  have h := reflection_log_7368_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7369_neg : (11789231 / 1000000000) ≤ -Real.log (988279988919 / 1000000000000) ∧
    -Real.log (988279988919 / 1000000000000) ≤ (736827 / 62500000) := by
  have h := checkLog_sound (w := (11720011081 / 1988279988919)) (n := 12)
    (lo := (11789231 / 1000000000)) (hi := (736827 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 988279988919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 988279988919) = 1/(988279988919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7369 : Bounds (-736827 / 62500000) (-11789231 / 1000000000) (Real.log (988279988919 / 1000000000000)) := by
  have h := reflection_log_7369_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7370_neg : (1168649 / 100000000) ≤ -Real.log (988381531479 / 1000000000000) ∧
    -Real.log (988381531479 / 1000000000000) ≤ (11686491 / 1000000000) := by
  have h := checkLog_sound (w := (11618468521 / 1988381531479)) (n := 12)
    (lo := (1168649 / 100000000)) (hi := (11686491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 988381531479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 988381531479) = 1/(988381531479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7370 : Bounds (-11686491 / 1000000000) (-1168649 / 100000000) (Real.log (988381531479 / 1000000000000)) := by
  have h := reflection_log_7370_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7371_neg : (54104691 / 250000000) ≤ -Real.log (500000000000 / 620811108583) ∧
    -Real.log (500000000000 / 620811108583) ≤ (43283753 / 200000000) := by
  have h := checkLog_sound (w := (120811108583 / 1120811108583)) (n := 12)
    (lo := (54104691 / 250000000)) (hi := (43283753 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((620811108583 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(620811108583 / 500000000000) = 1/(500000000000 / 620811108583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7371 : Bounds (54104691 / 250000000) (43283753 / 200000000) (Real.log (620811108583 / 500000000000)) := by
  have h := reflection_log_7371_neg
  have he : Real.log (620811108583 / 500000000000) = -Real.log (500000000000 / 620811108583) := by
    rw [show ((620811108583 / 500000000000) : ℝ) = ((500000000000 / 620811108583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7372_neg : (108684931 / 500000000) ≤ -Real.log (100000000000 / 124280368403) ∧
    -Real.log (100000000000 / 124280368403) ≤ (217369863 / 1000000000) := by
  have h := checkLog_sound (w := (24280368403 / 224280368403)) (n := 12)
    (lo := (108684931 / 500000000)) (hi := (217369863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((124280368403 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(124280368403 / 100000000000) = 1/(100000000000 / 124280368403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7372 : Bounds (108684931 / 500000000) (217369863 / 1000000000) (Real.log (124280368403 / 100000000000)) := by
  have h := reflection_log_7372_neg
  have he : Real.log (124280368403 / 100000000000) = -Real.log (100000000000 / 124280368403) := by
    rw [show ((124280368403 / 100000000000) : ℝ) = ((100000000000 / 124280368403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7373_neg : (434719179 / 1000000000) ≤ -Real.log (500000000000 / 772264631043) ∧
    -Real.log (500000000000 / 772264631043) ≤ (21735959 / 50000000) := by
  have h := checkLog_sound (w := (272264631043 / 1272264631043)) (n := 12)
    (lo := (434719179 / 1000000000)) (hi := (21735959 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((772264631043 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(772264631043 / 500000000000) = 1/(500000000000 / 772264631043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7373 : Bounds (434719179 / 1000000000) (21735959 / 50000000) (Real.log (772264631043 / 500000000000)) := by
  have h := reflection_log_7373_neg
  have he : Real.log (772264631043 / 500000000000) = -Real.log (500000000000 / 772264631043) := by
    rw [show ((772264631043 / 500000000000) : ℝ) = ((500000000000 / 772264631043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7374_neg : (43576729 / 100000000) ≤ -Real.log (500000000000 / 773074474857) ∧
    -Real.log (500000000000 / 773074474857) ≤ (435767291 / 1000000000) := by
  have h := checkLog_sound (w := (273074474857 / 1273074474857)) (n := 12)
    (lo := (43576729 / 100000000)) (hi := (435767291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((773074474857 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(773074474857 / 500000000000) = 1/(500000000000 / 773074474857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7374 : Bounds (43576729 / 100000000) (435767291 / 1000000000) (Real.log (773074474857 / 500000000000)) := by
  have h := reflection_log_7374_neg
  have he : Real.log (773074474857 / 500000000000) = -Real.log (500000000000 / 773074474857) := by
    rw [show ((773074474857 / 500000000000) : ℝ) = ((500000000000 / 773074474857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7375_neg : (48686019 / 250000000) ≤ -Real.log (200 / 243) ∧
    -Real.log (200 / 243) ≤ (194744077 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 443)) (n := 12)
    (lo := (48686019 / 250000000)) (hi := (194744077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(243 / 200) = 1/(200 / 243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7375 : Bounds (48686019 / 250000000) (194744077 / 1000000000) (Real.log (243 / 200)) := by
  have h := reflection_log_7375_neg
  have he : Real.log (243 / 200) = -Real.log (200 / 243) := by
    rw [show ((243 / 200) : ℝ) = ((200 / 243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7376_neg : (242071561 / 1000000000) ≤ -Real.log (157 / 200) ∧
    -Real.log (157 / 200) ≤ (121035781 / 500000000) := by
  have h := checkLog_sound (w := (43 / 357)) (n := 12)
    (lo := (242071561 / 1000000000)) (hi := (121035781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 157) = 1/(157 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7376 : Bounds (-121035781 / 500000000) (-242071561 / 1000000000) (Real.log (157 / 200)) := by
  have h := reflection_log_7376_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7377_neg : (3359 / 15625000) ≤ -Real.log (200000 / 200043) ∧
    -Real.log (200000 / 200043) ≤ (214977 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 400043)) (n := 12)
    (lo := (3359 / 15625000)) (hi := (214977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200043 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200043 / 200000) = 1/(200000 / 200043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7377 : Bounds (3359 / 15625000) (214977 / 1000000000) (Real.log (200043 / 200000)) := by
  have h := reflection_log_7377_neg
  have he : Real.log (200043 / 200000) = -Real.log (200000 / 200043) := by
    rw [show ((200043 / 200000) : ℝ) = ((200000 / 200043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7378_neg : (215023 / 1000000000) ≤ -Real.log (199957 / 200000) ∧
    -Real.log (199957 / 200000) ≤ (13439 / 62500000) := by
  have h := checkLog_sound (w := (43 / 399957)) (n := 12)
    (lo := (215023 / 1000000000)) (hi := (13439 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199957) = 1/(199957 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7378 : Bounds (-13439 / 62500000) (-215023 / 1000000000) (Real.log (199957 / 200000)) := by
  have h := reflection_log_7378_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7379_neg : (102597201 / 1000000000) ≤ -Real.log (200000 / 221609) ∧
    -Real.log (200000 / 221609) ≤ (51298601 / 500000000) := by
  have h := checkLog_sound (w := (21609 / 421609)) (n := 12)
    (lo := (102597201 / 1000000000)) (hi := (51298601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((221609 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(221609 / 200000) = 1/(200000 / 221609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7379 : Bounds (102597201 / 1000000000) (51298601 / 500000000) (Real.log (221609 / 200000)) := by
  have h := reflection_log_7379_neg
  have he : Real.log (221609 / 200000) = -Real.log (200000 / 221609) := by
    rw [show ((221609 / 200000) : ℝ) = ((200000 / 221609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7380_neg : (28584899 / 250000000) ≤ -Real.log (178391 / 200000) ∧
    -Real.log (178391 / 200000) ≤ (114339597 / 1000000000) := by
  have h := checkLog_sound (w := (21609 / 378391)) (n := 12)
    (lo := (28584899 / 250000000)) (hi := (114339597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 178391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 178391) = 1/(178391 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7380 : Bounds (-114339597 / 1000000000) (-28584899 / 250000000) (Real.log (178391 / 200000)) := by
  have h := reflection_log_7380_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7381_neg : (103022183 / 1000000000) ≤ -Real.log (250000 / 277129) ∧
    -Real.log (250000 / 277129) ≤ (12877773 / 125000000) := by
  have h := checkLog_sound (w := (27129 / 527129)) (n := 12)
    (lo := (103022183 / 1000000000)) (hi := (12877773 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((277129 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(277129 / 250000) = 1/(250000 / 277129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7381 : Bounds (103022183 / 1000000000) (12877773 / 125000000) (Real.log (277129 / 250000)) := by
  have h := reflection_log_7381_neg
  have he : Real.log (277129 / 250000) = -Real.log (250000 / 277129) := by
    rw [show ((277129 / 250000) : ℝ) = ((250000 / 277129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7382_neg : (114867789 / 1000000000) ≤ -Real.log (222871 / 250000) ∧
    -Real.log (222871 / 250000) ≤ (11486779 / 100000000) := by
  have h := checkLog_sound (w := (27129 / 472871)) (n := 12)
    (lo := (114867789 / 1000000000)) (hi := (11486779 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 222871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 222871) = 1/(222871 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7382 : Bounds (-11486779 / 100000000) (-114867789 / 1000000000) (Real.log (222871 / 250000)) := by
  have h := reflection_log_7382_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7383_neg : (2369121 / 200000000) ≤ -Real.log (61764017359 / 62500000000) ∧
    -Real.log (61764017359 / 62500000000) ≤ (5922803 / 500000000) := by
  have h := checkLog_sound (w := (735982641 / 124264017359)) (n := 12)
    (lo := (2369121 / 200000000)) (hi := (5922803 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61764017359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61764017359) = 1/(61764017359 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7383 : Bounds (-5922803 / 500000000) (-2369121 / 200000000) (Real.log (61764017359 / 62500000000)) := by
  have h := reflection_log_7383_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7384_neg : (5871197 / 500000000) ≤ -Real.log (39533051119 / 40000000000) ∧
    -Real.log (39533051119 / 40000000000) ≤ (2348479 / 200000000) := by
  have h := checkLog_sound (w := (466948881 / 79533051119)) (n := 12)
    (lo := (5871197 / 500000000)) (hi := (2348479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39533051119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39533051119) = 1/(39533051119 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7384 : Bounds (-2348479 / 200000000) (-5871197 / 500000000) (Real.log (39533051119 / 40000000000)) := by
  have h := reflection_log_7384_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7385_neg : (216936797 / 1000000000) ≤ -Real.log (500000000000 / 621132792573) ∧
    -Real.log (500000000000 / 621132792573) ≤ (108468399 / 500000000) := by
  have h := checkLog_sound (w := (121132792573 / 1121132792573)) (n := 12)
    (lo := (216936797 / 1000000000)) (hi := (108468399 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621132792573 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(621132792573 / 500000000000) = 1/(500000000000 / 621132792573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7385 : Bounds (216936797 / 1000000000) (108468399 / 500000000) (Real.log (621132792573 / 500000000000)) := by
  have h := reflection_log_7385_neg
  have he : Real.log (621132792573 / 500000000000) = -Real.log (500000000000 / 621132792573) := by
    rw [show ((621132792573 / 500000000000) : ℝ) = ((500000000000 / 621132792573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7386_neg : (217889973 / 1000000000) ≤ -Real.log (250000000000 / 310862561751) ∧
    -Real.log (250000000000 / 310862561751) ≤ (108944987 / 500000000) := by
  have h := checkLog_sound (w := (60862561751 / 560862561751)) (n := 12)
    (lo := (217889973 / 1000000000)) (hi := (108944987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((310862561751 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(310862561751 / 250000000000) = 1/(250000000000 / 310862561751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7386 : Bounds (217889973 / 1000000000) (108944987 / 500000000) (Real.log (310862561751 / 250000000000)) := by
  have h := reflection_log_7386_neg
  have he : Real.log (310862561751 / 250000000000) = -Real.log (250000000000 / 310862561751) := by
    rw [show ((310862561751 / 250000000000) : ℝ) = ((250000000000 / 310862561751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7387_neg : (43576729 / 100000000) ≤ -Real.log (62500000000 / 96634309357) ∧
    -Real.log (62500000000 / 96634309357) ≤ (435767291 / 1000000000) := by
  have h := checkLog_sound (w := (34134309357 / 159134309357)) (n := 12)
    (lo := (43576729 / 100000000)) (hi := (435767291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96634309357 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96634309357 / 62500000000) = 1/(62500000000 / 96634309357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7387 : Bounds (43576729 / 100000000) (435767291 / 1000000000) (Real.log (96634309357 / 62500000000)) := by
  have h := reflection_log_7387_neg
  have he : Real.log (96634309357 / 62500000000) = -Real.log (62500000000 / 96634309357) := by
    rw [show ((96634309357 / 62500000000) : ℝ) = ((62500000000 / 96634309357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7388_neg : (436815637 / 1000000000) ≤ -Real.log (500000000000 / 773885350319) ∧
    -Real.log (500000000000 / 773885350319) ≤ (218407819 / 500000000) := by
  have h := checkLog_sound (w := (273885350319 / 1273885350319)) (n := 12)
    (lo := (436815637 / 1000000000)) (hi := (218407819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((773885350319 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(773885350319 / 500000000000) = 1/(500000000000 / 773885350319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7388 : Bounds (436815637 / 1000000000) (218407819 / 500000000) (Real.log (773885350319 / 500000000000)) := by
  have h := reflection_log_7388_neg
  have he : Real.log (773885350319 / 500000000000) = -Real.log (500000000000 / 773885350319) := by
    rw [show ((773885350319 / 500000000000) : ℝ) = ((500000000000 / 773885350319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7389_neg : (97577757 / 500000000) ≤ -Real.log (2000 / 2431) ∧
    -Real.log (2000 / 2431) ≤ (39031103 / 200000000) := by
  have h := checkLog_sound (w := (431 / 4431)) (n := 12)
    (lo := (97577757 / 500000000)) (hi := (39031103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2431 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2431 / 2000) = 1/(2000 / 2431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7389 : Bounds (97577757 / 500000000) (39031103 / 200000000) (Real.log (2431 / 2000)) := by
  have h := reflection_log_7389_neg
  have he : Real.log (2431 / 2000) = -Real.log (2000 / 2431) := by
    rw [show ((2431 / 2000) : ℝ) = ((2000 / 2431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7390_neg : (121354353 / 500000000) ≤ -Real.log (1569 / 2000) ∧
    -Real.log (1569 / 2000) ≤ (242708707 / 1000000000) := by
  have h := checkLog_sound (w := (431 / 3569)) (n := 12)
    (lo := (121354353 / 500000000)) (hi := (242708707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1569) = 1/(1569 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7390 : Bounds (-242708707 / 1000000000) (-121354353 / 500000000) (Real.log (1569 / 2000)) := by
  have h := reflection_log_7390_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7391_neg : (53869 / 250000000) ≤ -Real.log (2000000 / 2000431) ∧
    -Real.log (2000000 / 2000431) ≤ (215477 / 1000000000) := by
  have h := checkLog_sound (w := (431 / 4000431)) (n := 12)
    (lo := (53869 / 250000000)) (hi := (215477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000431 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000431 / 2000000) = 1/(2000000 / 2000431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7391 : Bounds (53869 / 250000000) (215477 / 1000000000) (Real.log (2000431 / 2000000)) := by
  have h := reflection_log_7391_neg
  have he : Real.log (2000431 / 2000000) = -Real.log (2000000 / 2000431) := by
    rw [show ((2000431 / 2000000) : ℝ) = ((2000000 / 2000431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7392_neg : (215523 / 1000000000) ≤ -Real.log (1999569 / 2000000) ∧
    -Real.log (1999569 / 2000000) ≤ (53881 / 250000000) := by
  have h := checkLog_sound (w := (431 / 3999569)) (n := 12)
    (lo := (215523 / 1000000000)) (hi := (53881 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999569) = 1/(1999569 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7392 : Bounds (-53881 / 250000000) (-215523 / 1000000000) (Real.log (1999569 / 2000000)) := by
  have h := reflection_log_7392_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7393_neg : (25707053 / 250000000) ≤ -Real.log (1000000 / 1108301) ∧
    -Real.log (1000000 / 1108301) ≤ (102828213 / 1000000000) := by
  have h := checkLog_sound (w := (108301 / 2108301)) (n := 12)
    (lo := (25707053 / 250000000)) (hi := (102828213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1108301 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1108301 / 1000000) = 1/(1000000 / 1108301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7393 : Bounds (25707053 / 250000000) (102828213 / 1000000000) (Real.log (1108301 / 1000000)) := by
  have h := reflection_log_7393_neg
  have he : Real.log (1108301 / 1000000) = -Real.log (1000000 / 1108301) := by
    rw [show ((1108301 / 1000000) : ℝ) = ((1000000 / 1108301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7394_neg : (114626647 / 1000000000) ≤ -Real.log (891699 / 1000000) ∧
    -Real.log (891699 / 1000000) ≤ (14328331 / 125000000) := by
  have h := checkLog_sound (w := (108301 / 1891699)) (n := 12)
    (lo := (114626647 / 1000000000)) (hi := (14328331 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 891699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 891699) = 1/(891699 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7394 : Bounds (-14328331 / 125000000) (-114626647 / 1000000000) (Real.log (891699 / 1000000)) := by
  have h := reflection_log_7394_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7395_neg : (12906637 / 125000000) ≤ -Real.log (250000 / 277193) ∧
    -Real.log (250000 / 277193) ≤ (103253097 / 1000000000) := by
  have h := checkLog_sound (w := (27193 / 527193)) (n := 12)
    (lo := (12906637 / 125000000)) (hi := (103253097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((277193 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(277193 / 250000) = 1/(250000 / 277193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7395 : Bounds (12906637 / 125000000) (103253097 / 1000000000) (Real.log (277193 / 250000)) := by
  have h := reflection_log_7395_neg
  have he : Real.log (277193 / 250000) = -Real.log (250000 / 277193) := by
    rw [show ((277193 / 250000) : ℝ) = ((250000 / 277193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7396_neg : (115154991 / 1000000000) ≤ -Real.log (222807 / 250000) ∧
    -Real.log (222807 / 250000) ≤ (7197187 / 62500000) := by
  have h := checkLog_sound (w := (27193 / 472807)) (n := 12)
    (lo := (115154991 / 1000000000)) (hi := (7197187 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 222807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 222807) = 1/(222807 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7396 : Bounds (-7197187 / 62500000) (-115154991 / 1000000000) (Real.log (222807 / 250000)) := by
  have h := reflection_log_7396_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7397_neg : (2380379 / 200000000) ≤ -Real.log (61760540751 / 62500000000) ∧
    -Real.log (61760540751 / 62500000000) ≤ (1487737 / 125000000) := by
  have h := checkLog_sound (w := (739459249 / 124260540751)) (n := 12)
    (lo := (2380379 / 200000000)) (hi := (1487737 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61760540751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61760540751) = 1/(61760540751 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7397 : Bounds (-1487737 / 125000000) (-2380379 / 200000000) (Real.log (61760540751 / 62500000000)) := by
  have h := reflection_log_7397_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7398_neg : (2359687 / 200000000) ≤ -Real.log (988270893399 / 1000000000000) ∧
    -Real.log (988270893399 / 1000000000000) ≤ (2949609 / 250000000) := by
  have h := checkLog_sound (w := (11729106601 / 1988270893399)) (n := 12)
    (lo := (2359687 / 200000000)) (hi := (2949609 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 988270893399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 988270893399) = 1/(988270893399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7398 : Bounds (-2949609 / 250000000) (-2359687 / 200000000) (Real.log (988270893399 / 1000000000000)) := by
  have h := reflection_log_7398_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7399_neg : (217454859 / 1000000000) ≤ -Real.log (50000000000 / 62145466127) ∧
    -Real.log (50000000000 / 62145466127) ≤ (10872743 / 50000000) := by
  have h := checkLog_sound (w := (12145466127 / 112145466127)) (n := 12)
    (lo := (217454859 / 1000000000)) (hi := (10872743 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62145466127 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62145466127 / 50000000000) = 1/(50000000000 / 62145466127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7399 : Bounds (217454859 / 1000000000) (10872743 / 50000000) (Real.log (62145466127 / 50000000000)) := by
  have h := reflection_log_7399_neg
  have he : Real.log (62145466127 / 50000000000) = -Real.log (50000000000 / 62145466127) := by
    rw [show ((62145466127 / 50000000000) : ℝ) = ((50000000000 / 62145466127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7400_neg : (27301011 / 125000000) ≤ -Real.log (100000000000 / 124409466489) ∧
    -Real.log (100000000000 / 124409466489) ≤ (218408089 / 1000000000) := by
  have h := checkLog_sound (w := (24409466489 / 224409466489)) (n := 12)
    (lo := (27301011 / 125000000)) (hi := (218408089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((124409466489 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(124409466489 / 100000000000) = 1/(100000000000 / 124409466489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7400 : Bounds (27301011 / 125000000) (218408089 / 1000000000) (Real.log (124409466489 / 100000000000)) := by
  have h := reflection_log_7400_neg
  have he : Real.log (124409466489 / 100000000000) = -Real.log (100000000000 / 124409466489) := by
    rw [show ((124409466489 / 100000000000) : ℝ) = ((100000000000 / 124409466489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7401_neg : (436815637 / 1000000000) ≤ -Real.log (250000000000 / 386942675159) ∧
    -Real.log (250000000000 / 386942675159) ≤ (218407819 / 500000000) := by
  have h := checkLog_sound (w := (136942675159 / 636942675159)) (n := 12)
    (lo := (436815637 / 1000000000)) (hi := (218407819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((386942675159 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(386942675159 / 250000000000) = 1/(250000000000 / 386942675159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7401 : Bounds (436815637 / 1000000000) (218407819 / 500000000) (Real.log (386942675159 / 250000000000)) := by
  have h := reflection_log_7401_neg
  have he : Real.log (386942675159 / 250000000000) = -Real.log (250000000000 / 386942675159) := by
    rw [show ((386942675159 / 250000000000) : ℝ) = ((250000000000 / 386942675159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7402_neg : (437864221 / 1000000000) ≤ -Real.log (500000000000 / 774697259401) ∧
    -Real.log (500000000000 / 774697259401) ≤ (218932111 / 500000000) := by
  have h := checkLog_sound (w := (274697259401 / 1274697259401)) (n := 12)
    (lo := (437864221 / 1000000000)) (hi := (218932111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((774697259401 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(774697259401 / 500000000000) = 1/(500000000000 / 774697259401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7402 : Bounds (437864221 / 1000000000) (218932111 / 500000000) (Real.log (774697259401 / 500000000000)) := by
  have h := reflection_log_7402_neg
  have he : Real.log (774697259401 / 500000000000) = -Real.log (500000000000 / 774697259401) := by
    rw [show ((774697259401 / 500000000000) : ℝ) = ((500000000000 / 774697259401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7403_neg : (195566783 / 1000000000) ≤ -Real.log (125 / 152) ∧
    -Real.log (125 / 152) ≤ (3055731 / 15625000) := by
  have h := checkLog_sound (w := (27 / 277)) (n := 12)
    (lo := (195566783 / 1000000000)) (hi := (3055731 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152 / 125) = 1/(125 / 152) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7403 : Bounds (195566783 / 1000000000) (3055731 / 15625000) (Real.log (152 / 125)) := by
  have h := reflection_log_7403_neg
  have he : Real.log (152 / 125) = -Real.log (125 / 152) := by
    rw [show ((152 / 125) : ℝ) = ((125 / 152) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7404_neg : (121673129 / 500000000) ≤ -Real.log (98 / 125) ∧
    -Real.log (98 / 125) ≤ (243346259 / 1000000000) := by
  have h := checkLog_sound (w := (27 / 223)) (n := 12)
    (lo := (121673129 / 500000000)) (hi := (243346259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 98) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 98) = 1/(98 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7404 : Bounds (-243346259 / 1000000000) (-121673129 / 500000000) (Real.log (98 / 125)) := by
  have h := reflection_log_7404_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7405_neg : (26997 / 125000000) ≤ -Real.log (125000 / 125027) ∧
    -Real.log (125000 / 125027) ≤ (215977 / 1000000000) := by
  have h := checkLog_sound (w := (27 / 250027)) (n := 12)
    (lo := (26997 / 125000000)) (hi := (215977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125027 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125027 / 125000) = 1/(125000 / 125027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7405 : Bounds (26997 / 125000000) (215977 / 1000000000) (Real.log (125027 / 125000)) := by
  have h := reflection_log_7405_neg
  have he : Real.log (125027 / 125000) = -Real.log (125000 / 125027) := by
    rw [show ((125027 / 125000) : ℝ) = ((125000 / 125027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7406_neg : (216023 / 1000000000) ≤ -Real.log (124973 / 125000) ∧
    -Real.log (124973 / 125000) ≤ (27003 / 125000000) := by
  have h := checkLog_sound (w := (27 / 249973)) (n := 12)
    (lo := (216023 / 1000000000)) (hi := (27003 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124973) = 1/(124973 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7406 : Bounds (-27003 / 125000000) (-216023 / 1000000000) (Real.log (124973 / 125000)) := by
  have h := reflection_log_7406_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7407_neg : (103060071 / 1000000000) ≤ -Real.log (500000 / 554279) ∧
    -Real.log (500000 / 554279) ≤ (12882509 / 125000000) := by
  have h := checkLog_sound (w := (54279 / 1054279)) (n := 12)
    (lo := (103060071 / 1000000000)) (hi := (12882509 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((554279 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(554279 / 500000) = 1/(500000 / 554279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7407 : Bounds (103060071 / 1000000000) (12882509 / 125000000) (Real.log (554279 / 500000)) := by
  have h := reflection_log_7407_neg
  have he : Real.log (554279 / 500000) = -Real.log (500000 / 554279) := by
    rw [show ((554279 / 500000) : ℝ) = ((500000 / 554279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7408_neg : (57457451 / 500000000) ≤ -Real.log (445721 / 500000) ∧
    -Real.log (445721 / 500000) ≤ (114914903 / 1000000000) := by
  have h := checkLog_sound (w := (54279 / 945721)) (n := 12)
    (lo := (57457451 / 500000000)) (hi := (114914903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 445721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 445721) = 1/(445721 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7408 : Bounds (-114914903 / 1000000000) (-57457451 / 500000000) (Real.log (445721 / 500000)) := by
  have h := reflection_log_7408_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7409_neg : (103484857 / 1000000000) ≤ -Real.log (1000000 / 1109029) ∧
    -Real.log (1000000 / 1109029) ≤ (51742429 / 500000000) := by
  have h := checkLog_sound (w := (109029 / 2109029)) (n := 12)
    (lo := (103484857 / 1000000000)) (hi := (51742429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1109029 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1109029 / 1000000) = 1/(1000000 / 1109029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7409 : Bounds (103484857 / 1000000000) (51742429 / 500000000) (Real.log (1109029 / 1000000)) := by
  have h := reflection_log_7409_neg
  have he : Real.log (1109029 / 1000000) = -Real.log (1000000 / 1109029) := by
    rw [show ((1109029 / 1000000) : ℝ) = ((1000000 / 1109029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7410_neg : (115443399 / 1000000000) ≤ -Real.log (890971 / 1000000) ∧
    -Real.log (890971 / 1000000) ≤ (577217 / 5000000) := by
  have h := checkLog_sound (w := (109029 / 1890971)) (n := 12)
    (lo := (115443399 / 1000000000)) (hi := (577217 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 890971) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 890971) = 1/(890971 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7410 : Bounds (-577217 / 5000000) (-115443399 / 1000000000) (Real.log (890971 / 1000000)) := by
  have h := reflection_log_7410_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7411_neg : (5979271 / 500000000) ≤ -Real.log (988112677159 / 1000000000000) ∧
    -Real.log (988112677159 / 1000000000000) ≤ (11958543 / 1000000000) := by
  have h := checkLog_sound (w := (11887322841 / 1988112677159)) (n := 12)
    (lo := (5979271 / 500000000)) (hi := (11958543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 988112677159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 988112677159) = 1/(988112677159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7411 : Bounds (-11958543 / 1000000000) (-5979271 / 500000000) (Real.log (988112677159 / 1000000000000)) := by
  have h := reflection_log_7411_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7412_neg : (11854831 / 1000000000) ≤ -Real.log (247053790159 / 250000000000) ∧
    -Real.log (247053790159 / 250000000000) ≤ (740927 / 62500000) := by
  have h := checkLog_sound (w := (2946209841 / 497053790159)) (n := 12)
    (lo := (11854831 / 1000000000)) (hi := (740927 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247053790159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247053790159) = 1/(247053790159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7412 : Bounds (-740927 / 62500000) (-11854831 / 1000000000) (Real.log (247053790159 / 250000000000)) := by
  have h := reflection_log_7412_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7413_neg : (108987487 / 500000000) ≤ -Real.log (15625000000 / 19430561663) ∧
    -Real.log (15625000000 / 19430561663) ≤ (8718999 / 40000000) := by
  have h := checkLog_sound (w := (3805561663 / 35055561663)) (n := 12)
    (lo := (108987487 / 500000000)) (hi := (8718999 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19430561663 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19430561663 / 15625000000) = 1/(15625000000 / 19430561663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7413 : Bounds (108987487 / 500000000) (8718999 / 40000000) (Real.log (19430561663 / 15625000000)) := by
  have h := reflection_log_7413_neg
  have he : Real.log (19430561663 / 15625000000) = -Real.log (15625000000 / 19430561663) := by
    rw [show ((19430561663 / 15625000000) : ℝ) = ((15625000000 / 19430561663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7414_neg : (218928257 / 1000000000) ≤ -Real.log (250000000000 / 311185493131) ∧
    -Real.log (250000000000 / 311185493131) ≤ (109464129 / 500000000) := by
  have h := checkLog_sound (w := (61185493131 / 561185493131)) (n := 12)
    (lo := (218928257 / 1000000000)) (hi := (109464129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311185493131 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311185493131 / 250000000000) = 1/(250000000000 / 311185493131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7414 : Bounds (218928257 / 1000000000) (109464129 / 500000000) (Real.log (311185493131 / 250000000000)) := by
  have h := reflection_log_7414_neg
  have he : Real.log (311185493131 / 250000000000) = -Real.log (250000000000 / 311185493131) := by
    rw [show ((311185493131 / 250000000000) : ℝ) = ((250000000000 / 311185493131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7415_neg : (437864221 / 1000000000) ≤ -Real.log (2500000000 / 3873486297) ∧
    -Real.log (2500000000 / 3873486297) ≤ (218932111 / 500000000) := by
  have h := checkLog_sound (w := (1373486297 / 6373486297)) (n := 12)
    (lo := (437864221 / 1000000000)) (hi := (218932111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3873486297 / 2500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3873486297 / 2500000000) = 1/(2500000000 / 3873486297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7415 : Bounds (437864221 / 1000000000) (218932111 / 500000000) (Real.log (3873486297 / 2500000000)) := by
  have h := reflection_log_7415_neg
  have he : Real.log (3873486297 / 2500000000) = -Real.log (2500000000 / 3873486297) := by
    rw [show ((3873486297 / 2500000000) : ℝ) = ((2500000000 / 3873486297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7416_neg : (219456521 / 500000000) ≤ -Real.log (250000000000 / 387755102041) ∧
    -Real.log (250000000000 / 387755102041) ≤ (438913043 / 1000000000) := by
  have h := checkLog_sound (w := (137755102041 / 637755102041)) (n := 12)
    (lo := (219456521 / 500000000)) (hi := (438913043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387755102041 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387755102041 / 250000000000) = 1/(250000000000 / 387755102041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7416 : Bounds (219456521 / 500000000) (438913043 / 1000000000) (Real.log (387755102041 / 250000000000)) := by
  have h := reflection_log_7416_neg
  have he : Real.log (387755102041 / 250000000000) = -Real.log (250000000000 / 387755102041) := by
    rw [show ((387755102041 / 250000000000) : ℝ) = ((250000000000 / 387755102041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7417_neg : (195977883 / 1000000000) ≤ -Real.log (2000 / 2433) ∧
    -Real.log (2000 / 2433) ≤ (48994471 / 250000000) := by
  have h := checkLog_sound (w := (433 / 4433)) (n := 12)
    (lo := (195977883 / 1000000000)) (hi := (48994471 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2433 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2433 / 2000) = 1/(2000 / 2433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7417 : Bounds (195977883 / 1000000000) (48994471 / 250000000) (Real.log (2433 / 2000)) := by
  have h := reflection_log_7417_neg
  have he : Real.log (2433 / 2000) = -Real.log (2000 / 2433) := by
    rw [show ((2433 / 2000) : ℝ) = ((2000 / 2433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7418_neg : (243984217 / 1000000000) ≤ -Real.log (1567 / 2000) ∧
    -Real.log (1567 / 2000) ≤ (121992109 / 500000000) := by
  have h := checkLog_sound (w := (433 / 3567)) (n := 12)
    (lo := (243984217 / 1000000000)) (hi := (121992109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1567) = 1/(1567 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7418 : Bounds (-121992109 / 500000000) (-243984217 / 1000000000) (Real.log (1567 / 2000)) := by
  have h := reflection_log_7418_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7419_neg : (54119 / 250000000) ≤ -Real.log (2000000 / 2000433) ∧
    -Real.log (2000000 / 2000433) ≤ (216477 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 4000433)) (n := 12)
    (lo := (54119 / 250000000)) (hi := (216477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000433 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000433 / 2000000) = 1/(2000000 / 2000433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7419 : Bounds (54119 / 250000000) (216477 / 1000000000) (Real.log (2000433 / 2000000)) := by
  have h := reflection_log_7419_neg
  have he : Real.log (2000433 / 2000000) = -Real.log (2000000 / 2000433) := by
    rw [show ((2000433 / 2000000) : ℝ) = ((2000000 / 2000433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7420_neg : (216523 / 1000000000) ≤ -Real.log (1999567 / 2000000) ∧
    -Real.log (1999567 / 2000000) ≤ (54131 / 250000000) := by
  have h := checkLog_sound (w := (433 / 3999567)) (n := 12)
    (lo := (216523 / 1000000000)) (hi := (54131 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999567) = 1/(1999567 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7420 : Bounds (-54131 / 250000000) (-216523 / 1000000000) (Real.log (1999567 / 2000000)) := by
  have h := reflection_log_7420_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7421_neg : (4131639 / 40000000) ≤ -Real.log (500000 / 554407) ∧
    -Real.log (500000 / 554407) ≤ (3227843 / 31250000) := by
  have h := checkLog_sound (w := (54407 / 1054407)) (n := 12)
    (lo := (4131639 / 40000000)) (hi := (3227843 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((554407 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(554407 / 500000) = 1/(500000 / 554407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7421 : Bounds (4131639 / 40000000) (3227843 / 31250000) (Real.log (554407 / 500000)) := by
  have h := reflection_log_7421_neg
  have he : Real.log (554407 / 500000) = -Real.log (500000 / 554407) := by
    rw [show ((554407 / 500000) : ℝ) = ((500000 / 554407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7422_neg : (115202119 / 1000000000) ≤ -Real.log (445593 / 500000) ∧
    -Real.log (445593 / 500000) ≤ (2880053 / 25000000) := by
  have h := checkLog_sound (w := (54407 / 945593)) (n := 12)
    (lo := (115202119 / 1000000000)) (hi := (2880053 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 445593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 445593) = 1/(445593 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7422 : Bounds (-2880053 / 25000000) (-115202119 / 1000000000) (Real.log (445593 / 500000)) := by
  have h := reflection_log_7422_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7423_neg : (20743313 / 200000000) ≤ -Real.log (500000 / 554643) ∧
    -Real.log (500000 / 554643) ≤ (51858283 / 500000000) := by
  have h := checkLog_sound (w := (54643 / 1054643)) (n := 12)
    (lo := (20743313 / 200000000)) (hi := (51858283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((554643 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(554643 / 500000) = 1/(500000 / 554643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7423 : Bounds (20743313 / 200000000) (51858283 / 500000000) (Real.log (554643 / 500000)) := by
  have h := reflection_log_7423_neg
  have he : Real.log (554643 / 500000) = -Real.log (500000 / 554643) := by
    rw [show ((554643 / 500000) : ℝ) = ((500000 / 554643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


