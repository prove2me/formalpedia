-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0196__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0196__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T21:33:31.621881+00:00
-- url     : https://prove2.me/theorems/e6b53c09-b40e-4aee-8595-db3c0d2c897c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0196 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0197, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0196 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0197, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0198)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0196 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0197, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0198)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0196 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0197, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0198) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0196 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0197, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0198).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0196 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12544_neg : (3787197 / 12500000) ≤ -Real.log (738617 / 1000000) ∧
    -Real.log (738617 / 1000000) ≤ (302975761 / 1000000000) := by
  have h := checkLog_sound (w := (261383 / 1738617)) (n := 12)
    (lo := (3787197 / 12500000)) (hi := (302975761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 738617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 738617) = 1/(738617 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12544 : Bounds (-302975761 / 1000000000) (-3787197 / 12500000) (Real.log (738617 / 1000000)) := by
  have h := reflection_log_12544_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12545_neg : (46608479 / 200000000) ≤ -Real.log (200000 / 252487) ∧
    -Real.log (200000 / 252487) ≤ (58260599 / 250000000) := by
  have h := checkLog_sound (w := (52487 / 452487)) (n := 12)
    (lo := (46608479 / 200000000)) (hi := (58260599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((252487 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(252487 / 200000) = 1/(200000 / 252487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12545 : Bounds (46608479 / 200000000) (58260599 / 250000000) (Real.log (252487 / 200000)) := by
  have h := reflection_log_12545_neg
  have he : Real.log (252487 / 200000) = -Real.log (200000 / 252487) := by
    rw [show ((252487 / 200000) : ℝ) = ((200000 / 252487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12546_neg : (304401059 / 1000000000) ≤ -Real.log (147513 / 200000) ∧
    -Real.log (147513 / 200000) ≤ (15220053 / 50000000) := by
  have h := checkLog_sound (w := (52487 / 347513)) (n := 12)
    (lo := (304401059 / 1000000000)) (hi := (15220053 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 147513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 147513) = 1/(147513 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12546 : Bounds (-15220053 / 50000000) (-304401059 / 1000000000) (Real.log (147513 / 200000)) := by
  have h := reflection_log_12546_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12547_neg : (71358663 / 1000000000) ≤ -Real.log (37245114831 / 40000000000) ∧
    -Real.log (37245114831 / 40000000000) ≤ (8919833 / 125000000) := by
  have h := checkLog_sound (w := (2754885169 / 77245114831)) (n := 12)
    (lo := (71358663 / 1000000000)) (hi := (8919833 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37245114831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37245114831) = 1/(37245114831 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12547 : Bounds (-8919833 / 125000000) (-71358663 / 1000000000) (Real.log (37245114831 / 40000000000)) := by
  have h := reflection_log_12547_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12548_neg : (35383511 / 500000000) ≤ -Real.log (931678927311 / 1000000000000) ∧
    -Real.log (931678927311 / 1000000000000) ≤ (70767023 / 1000000000) := by
  have h := checkLog_sound (w := (68321072689 / 1931678927311)) (n := 12)
    (lo := (35383511 / 500000000)) (hi := (70767023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 931678927311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 931678927311) = 1/(931678927311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12548 : Bounds (-70767023 / 1000000000) (-35383511 / 500000000) (Real.log (931678927311 / 1000000000000)) := by
  have h := reflection_log_12548_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12549_neg : (267592249 / 500000000) ≤ -Real.log (250000000000 / 426940823187) ∧
    -Real.log (250000000000 / 426940823187) ≤ (535184499 / 1000000000) := by
  have h := checkLog_sound (w := (176940823187 / 676940823187)) (n := 12)
    (lo := (267592249 / 500000000)) (hi := (535184499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((426940823187 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(426940823187 / 250000000000) = 1/(250000000000 / 426940823187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12549 : Bounds (267592249 / 500000000) (535184499 / 1000000000) (Real.log (426940823187 / 250000000000)) := by
  have h := reflection_log_12549_neg
  have he : Real.log (426940823187 / 250000000000) = -Real.log (250000000000 / 426940823187) := by
    rw [show ((426940823187 / 250000000000) : ℝ) = ((250000000000 / 426940823187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12550_neg : (268721727 / 500000000) ≤ -Real.log (500000000000 / 855812708033) ∧
    -Real.log (500000000000 / 855812708033) ≤ (107488691 / 200000000) := by
  have h := checkLog_sound (w := (355812708033 / 1355812708033)) (n := 12)
    (lo := (268721727 / 500000000)) (hi := (107488691 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((855812708033 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(855812708033 / 500000000000) = 1/(500000000000 / 855812708033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12550 : Bounds (268721727 / 500000000) (107488691 / 200000000) (Real.log (855812708033 / 500000000000)) := by
  have h := reflection_log_12550_neg
  have he : Real.log (855812708033 / 500000000000) = -Real.log (500000000000 / 855812708033) := by
    rw [show ((855812708033 / 500000000000) : ℝ) = ((500000000000 / 855812708033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12551_neg : (273986849 / 250000000) ≤ -Real.log (500000000000 / 1496007984031) ∧
    -Real.log (500000000000 / 1496007984031) ≤ (547973699 / 500000000) := by
  have h := checkLog_sound (w := (496007984031 / 2496007984031)) (n := 12)
    (lo := (50350027 / 125000000)) (hi := (402800217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1496007984031 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1496007984031 / 1000000000000) = 1/(500000000000 / 1496007984031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12551 : Bounds (273986849 / 250000000) (547973699 / 500000000) (Real.log (1496007984031 / 500000000000)) := by
  have h := reflection_log_12551_neg
  have he : Real.log (1496007984031 / 500000000000) = -Real.log (500000000000 / 1496007984031) := by
    rw [show ((1496007984031 / 500000000000) : ℝ) = ((500000000000 / 1496007984031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12552_neg : (17165817 / 15625000) ≤ -Real.log (1 / 3) ∧
    -Real.log (1 / 3) ≤ (109861229 / 100000000) := by
  have h := checkLog_sound (w := (1 / 5)) (n := 12)
    (lo := (101366277 / 250000000)) (hi := (405465109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3 / 2) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(3 / 2) = 1/(1 / 3) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12552 : Bounds (17165817 / 15625000) (109861229 / 100000000) (Real.log (3 / 1)) := by
  have h := reflection_log_12552_neg
  have he : Real.log (3 / 1) = -Real.log (1 / 3) := by
    rw [show ((3 / 1) : ℝ) = ((1 / 3) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12553_neg : (40746311 / 100000000) ≤ -Real.log (1000 / 1503) ∧
    -Real.log (1000 / 1503) ≤ (407463111 / 1000000000) := by
  have h := checkLog_sound (w := (503 / 2503)) (n := 12)
    (lo := (40746311 / 100000000)) (hi := (407463111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1503 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1503 / 1000) = 1/(1000 / 1503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12553 : Bounds (40746311 / 100000000) (407463111 / 1000000000) (Real.log (1503 / 1000)) := by
  have h := reflection_log_12553_neg
  have he : Real.log (1503 / 1000) = -Real.log (1000 / 1503) := by
    rw [show ((1503 / 1000) : ℝ) = ((1000 / 1503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12554_neg : (174791313 / 250000000) ≤ -Real.log (497 / 1000) ∧
    -Real.log (497 / 1000) ≤ (349582627 / 500000000) := by
  have h := checkLog_sound (w := (3 / 997)) (n := 12)
    (lo := (752259 / 125000000)) (hi := (6018073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 497) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 497) = 1/(497 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12554 : Bounds (-349582627 / 500000000) (-174791313 / 250000000) (Real.log (497 / 1000)) := by
  have h := reflection_log_12554_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12555_neg : (502873 / 1000000000) ≤ -Real.log (1000000 / 1000503) ∧
    -Real.log (1000000 / 1000503) ≤ (251437 / 500000000) := by
  have h := checkLog_sound (w := (503 / 2000503)) (n := 12)
    (lo := (502873 / 1000000000)) (hi := (251437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000503 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000503 / 1000000) = 1/(1000000 / 1000503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12555 : Bounds (502873 / 1000000000) (251437 / 500000000) (Real.log (1000503 / 1000000)) := by
  have h := reflection_log_12555_neg
  have he : Real.log (1000503 / 1000000) = -Real.log (1000000 / 1000503) := by
    rw [show ((1000503 / 1000000) : ℝ) = ((1000000 / 1000503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12556_neg : (251563 / 500000000) ≤ -Real.log (999497 / 1000000) ∧
    -Real.log (999497 / 1000000) ≤ (503127 / 1000000000) := by
  have h := checkLog_sound (w := (503 / 1999497)) (n := 12)
    (lo := (251563 / 500000000)) (hi := (503127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999497) = 1/(999497 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12556 : Bounds (-503127 / 1000000000) (-251563 / 500000000) (Real.log (999497 / 1000000)) := by
  have h := reflection_log_12556_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12557_neg : (232666067 / 1000000000) ≤ -Real.log (25000 / 31549) ∧
    -Real.log (25000 / 31549) ≤ (58166517 / 250000000) := by
  have h := checkLog_sound (w := (6549 / 56549)) (n := 12)
    (lo := (232666067 / 1000000000)) (hi := (58166517 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31549 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31549 / 25000) = 1/(25000 / 31549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12557 : Bounds (232666067 / 1000000000) (58166517 / 250000000) (Real.log (31549 / 25000)) := by
  have h := reflection_log_12557_neg
  have he : Real.log (31549 / 25000) = -Real.log (25000 / 31549) := by
    rw [show ((31549 / 25000) : ℝ) = ((25000 / 31549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12558_neg : (60751451 / 200000000) ≤ -Real.log (18451 / 25000) ∧
    -Real.log (18451 / 25000) ≤ (37969657 / 125000000) := by
  have h := checkLog_sound (w := (6549 / 43451)) (n := 12)
    (lo := (60751451 / 200000000)) (hi := (37969657 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 18451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 18451) = 1/(18451 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12558 : Bounds (-37969657 / 125000000) (-60751451 / 200000000) (Real.log (18451 / 25000)) := by
  have h := reflection_log_12558_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12559_neg : (11720789 / 50000000) ≤ -Real.log (100000 / 126417) ∧
    -Real.log (100000 / 126417) ≤ (234415781 / 1000000000) := by
  have h := checkLog_sound (w := (26417 / 226417)) (n := 12)
    (lo := (11720789 / 50000000)) (hi := (234415781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126417 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(126417 / 100000) = 1/(100000 / 126417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12559 : Bounds (11720789 / 50000000) (234415781 / 1000000000) (Real.log (126417 / 100000)) := by
  have h := reflection_log_12559_neg
  have he : Real.log (126417 / 100000) = -Real.log (100000 / 126417) := by
    rw [show ((126417 / 100000) : ℝ) = ((100000 / 126417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12560_neg : (61351233 / 200000000) ≤ -Real.log (73583 / 100000) ∧
    -Real.log (73583 / 100000) ≤ (153378083 / 500000000) := by
  have h := checkLog_sound (w := (26417 / 173583)) (n := 12)
    (lo := (61351233 / 200000000)) (hi := (153378083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 73583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 73583) = 1/(73583 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12560 : Bounds (-153378083 / 500000000) (-61351233 / 200000000) (Real.log (73583 / 100000)) := by
  have h := reflection_log_12560_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12561_neg : (2260637 / 31250000) ≤ -Real.log (9302142111 / 10000000000) ∧
    -Real.log (9302142111 / 10000000000) ≤ (14468077 / 200000000) := by
  have h := checkLog_sound (w := (697857889 / 19302142111)) (n := 12)
    (lo := (2260637 / 31250000)) (hi := (14468077 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9302142111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9302142111) = 1/(9302142111 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12561 : Bounds (-14468077 / 200000000) (-2260637 / 31250000) (Real.log (9302142111 / 10000000000)) := by
  have h := reflection_log_12561_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12562_neg : (71091187 / 1000000000) ≤ -Real.log (582110599 / 625000000) ∧
    -Real.log (582110599 / 625000000) ≤ (17772797 / 250000000) := by
  have h := checkLog_sound (w := (42889401 / 1207110599)) (n := 12)
    (lo := (71091187 / 1000000000)) (hi := (17772797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 582110599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 582110599) = 1/(582110599 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12562 : Bounds (-17772797 / 250000000) (-71091187 / 1000000000) (Real.log (582110599 / 625000000)) := by
  have h := reflection_log_12562_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12563_neg : (536423323 / 1000000000) ≤ -Real.log (500000000000 / 854940111647) ∧
    -Real.log (500000000000 / 854940111647) ≤ (134105831 / 250000000) := by
  have h := checkLog_sound (w := (354940111647 / 1354940111647)) (n := 12)
    (lo := (536423323 / 1000000000)) (hi := (134105831 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((854940111647 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(854940111647 / 500000000000) = 1/(500000000000 / 854940111647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12563 : Bounds (536423323 / 1000000000) (134105831 / 250000000) (Real.log (854940111647 / 500000000000)) := by
  have h := reflection_log_12563_neg
  have he : Real.log (854940111647 / 500000000000) = -Real.log (500000000000 / 854940111647) := by
    rw [show ((854940111647 / 500000000000) : ℝ) = ((500000000000 / 854940111647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12564_neg : (108234389 / 200000000) ≤ -Real.log (250000000000 / 429504776919) ∧
    -Real.log (250000000000 / 429504776919) ≤ (270585973 / 500000000) := by
  have h := checkLog_sound (w := (179504776919 / 679504776919)) (n := 12)
    (lo := (108234389 / 200000000)) (hi := (270585973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((429504776919 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(429504776919 / 250000000000) = 1/(250000000000 / 429504776919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12564 : Bounds (108234389 / 200000000) (270585973 / 500000000) (Real.log (429504776919 / 250000000000)) := by
  have h := reflection_log_12564_neg
  have he : Real.log (429504776919 / 250000000000) = -Real.log (250000000000 / 429504776919) := by
    rw [show ((429504776919 / 250000000000) : ℝ) = ((250000000000 / 429504776919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12565_neg : (1106628363 / 1000000000) ≤ -Real.log (31250000000 / 94504527163) ∧
    -Real.log (31250000000 / 94504527163) ≤ (221325673 / 200000000) := by
  have h := checkLog_sound (w := (32004527163 / 157004527163)) (n := 12)
    (lo := (413481183 / 1000000000)) (hi := (12921287 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((94504527163 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(94504527163 / 62500000000) = 1/(31250000000 / 94504527163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12565 : Bounds (1106628363 / 1000000000) (221325673 / 200000000) (Real.log (94504527163 / 31250000000)) := by
  have h := reflection_log_12565_neg
  have he : Real.log (94504527163 / 31250000000) = -Real.log (31250000000 / 94504527163) := by
    rw [show ((94504527163 / 31250000000) : ℝ) = ((31250000000 / 94504527163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12566_neg : (409457129 / 1000000000) ≤ -Real.log (500 / 753) ∧
    -Real.log (500 / 753) ≤ (40945713 / 100000000) := by
  have h := checkLog_sound (w := (253 / 1253)) (n := 12)
    (lo := (409457129 / 1000000000)) (hi := (40945713 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((753 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(753 / 500) = 1/(500 / 753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12566 : Bounds (409457129 / 1000000000) (40945713 / 100000000) (Real.log (753 / 500)) := by
  have h := reflection_log_12566_neg
  have he : Real.log (753 / 500) = -Real.log (500 / 753) := by
    rw [show ((753 / 500) : ℝ) = ((500 / 753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12567_neg : (705219761 / 1000000000) ≤ -Real.log (247 / 500) ∧
    -Real.log (247 / 500) ≤ (705219763 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 497)) (n := 12)
    (lo := (12072581 / 1000000000)) (hi := (6036291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 247) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 247) = 1/(247 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12567 : Bounds (-705219763 / 1000000000) (-705219761 / 1000000000) (Real.log (247 / 500)) := by
  have h := reflection_log_12567_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12568_neg : (31617 / 62500000) ≤ -Real.log (500000 / 500253) ∧
    -Real.log (500000 / 500253) ≤ (505873 / 1000000000) := by
  have h := checkLog_sound (w := (253 / 1000253)) (n := 12)
    (lo := (31617 / 62500000)) (hi := (505873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500253 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500253 / 500000) = 1/(500000 / 500253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12568 : Bounds (31617 / 62500000) (505873 / 1000000000) (Real.log (500253 / 500000)) := by
  have h := reflection_log_12568_neg
  have he : Real.log (500253 / 500000) = -Real.log (500000 / 500253) := by
    rw [show ((500253 / 500000) : ℝ) = ((500000 / 500253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12569_neg : (31633 / 62500000) ≤ -Real.log (499747 / 500000) ∧
    -Real.log (499747 / 500000) ≤ (506129 / 1000000000) := by
  have h := checkLog_sound (w := (253 / 999747)) (n := 12)
    (lo := (31633 / 62500000)) (hi := (506129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499747) = 1/(499747 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12569 : Bounds (-506129 / 1000000000) (-31633 / 62500000) (Real.log (499747 / 500000)) := by
  have h := reflection_log_12569_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12570_neg : (46807519 / 200000000) ≤ -Real.log (250000 / 315923) ∧
    -Real.log (250000 / 315923) ≤ (58509399 / 250000000) := by
  have h := checkLog_sound (w := (65923 / 565923)) (n := 12)
    (lo := (46807519 / 200000000)) (hi := (58509399 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((315923 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(315923 / 250000) = 1/(250000 / 315923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12570 : Bounds (46807519 / 200000000) (58509399 / 250000000) (Real.log (315923 / 250000)) := by
  have h := reflection_log_12570_neg
  have he : Real.log (315923 / 250000) = -Real.log (250000 / 315923) := by
    rw [show ((315923 / 250000) : ℝ) = ((250000 / 315923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12571_neg : (306106769 / 1000000000) ≤ -Real.log (184077 / 250000) ∧
    -Real.log (184077 / 250000) ≤ (30610677 / 100000000) := by
  have h := checkLog_sound (w := (65923 / 434077)) (n := 12)
    (lo := (306106769 / 1000000000)) (hi := (30610677 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 184077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 184077) = 1/(184077 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12571 : Bounds (-30610677 / 100000000) (-306106769 / 1000000000) (Real.log (184077 / 250000)) := by
  have h := reflection_log_12571_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12572_neg : (235789651 / 1000000000) ≤ -Real.log (250000 / 316477) ∧
    -Real.log (250000 / 316477) ≤ (58947413 / 250000000) := by
  have h := checkLog_sound (w := (66477 / 566477)) (n := 12)
    (lo := (235789651 / 1000000000)) (hi := (58947413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((316477 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(316477 / 250000) = 1/(250000 / 316477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12572 : Bounds (235789651 / 1000000000) (58947413 / 250000000) (Real.log (316477 / 250000)) := by
  have h := reflection_log_12572_neg
  have he : Real.log (316477 / 250000) = -Real.log (250000 / 316477) := by
    rw [show ((316477 / 250000) : ℝ) = ((250000 / 316477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12573_neg : (309120917 / 1000000000) ≤ -Real.log (183523 / 250000) ∧
    -Real.log (183523 / 250000) ≤ (154560459 / 500000000) := by
  have h := checkLog_sound (w := (66477 / 433523)) (n := 12)
    (lo := (309120917 / 1000000000)) (hi := (154560459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 183523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 183523) = 1/(183523 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12573 : Bounds (-154560459 / 500000000) (-309120917 / 1000000000) (Real.log (183523 / 250000)) := by
  have h := reflection_log_12573_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12574_neg : (36665633 / 500000000) ≤ -Real.log (58080808471 / 62500000000) ∧
    -Real.log (58080808471 / 62500000000) ≤ (73331267 / 1000000000) := by
  have h := checkLog_sound (w := (4419191529 / 120580808471)) (n := 12)
    (lo := (36665633 / 500000000)) (hi := (73331267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 58080808471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 58080808471) = 1/(58080808471 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12574 : Bounds (-73331267 / 1000000000) (-36665633 / 500000000) (Real.log (58080808471 / 62500000000)) := by
  have h := reflection_log_12574_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12575_neg : (36034587 / 500000000) ≤ -Real.log (58154158071 / 62500000000) ∧
    -Real.log (58154158071 / 62500000000) ≤ (2882767 / 40000000) := by
  have h := checkLog_sound (w := (4345841929 / 120654158071)) (n := 12)
    (lo := (36034587 / 500000000)) (hi := (2882767 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 58154158071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 58154158071) = 1/(58154158071 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12575 : Bounds (-2882767 / 40000000) (-36034587 / 500000000) (Real.log (58154158071 / 62500000000)) := by
  have h := reflection_log_12575_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12576_neg : (135036091 / 250000000) ≤ -Real.log (500000000000 / 858127305421) ∧
    -Real.log (500000000000 / 858127305421) ≤ (108028873 / 200000000) := by
  have h := checkLog_sound (w := (358127305421 / 1358127305421)) (n := 12)
    (lo := (135036091 / 250000000)) (hi := (108028873 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((858127305421 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(858127305421 / 500000000000) = 1/(500000000000 / 858127305421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12576 : Bounds (135036091 / 250000000) (108028873 / 200000000) (Real.log (858127305421 / 500000000000)) := by
  have h := reflection_log_12576_neg
  have he : Real.log (858127305421 / 500000000000) = -Real.log (500000000000 / 858127305421) := by
    rw [show ((858127305421 / 500000000000) : ℝ) = ((500000000000 / 858127305421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12577_neg : (68113821 / 125000000) ≤ -Real.log (100000000000 / 172445415561) ∧
    -Real.log (100000000000 / 172445415561) ≤ (544910569 / 1000000000) := by
  have h := checkLog_sound (w := (72445415561 / 272445415561)) (n := 12)
    (lo := (68113821 / 125000000)) (hi := (544910569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172445415561 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172445415561 / 100000000000) = 1/(100000000000 / 172445415561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12577 : Bounds (68113821 / 125000000) (544910569 / 1000000000) (Real.log (172445415561 / 100000000000)) := by
  have h := reflection_log_12577_neg
  have he : Real.log (172445415561 / 100000000000) = -Real.log (100000000000 / 172445415561) := by
    rw [show ((172445415561 / 100000000000) : ℝ) = ((100000000000 / 172445415561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12578_neg : (1106628363 / 1000000000) ≤ -Real.log (500000000000 / 1512072434607) ∧
    -Real.log (500000000000 / 1512072434607) ≤ (221325673 / 200000000) := by
  have h := checkLog_sound (w := (512072434607 / 2512072434607)) (n := 12)
    (lo := (413481183 / 1000000000)) (hi := (12921287 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1512072434607 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1512072434607 / 1000000000000) = 1/(500000000000 / 1512072434607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12578 : Bounds (1106628363 / 1000000000) (221325673 / 200000000) (Real.log (1512072434607 / 500000000000)) := by
  have h := reflection_log_12578_neg
  have he : Real.log (1512072434607 / 500000000000) = -Real.log (500000000000 / 1512072434607) := by
    rw [show ((1512072434607 / 500000000000) : ℝ) = ((500000000000 / 1512072434607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12579_neg : (111467689 / 100000000) ≤ -Real.log (62500000000 / 190536437247) ∧
    -Real.log (62500000000 / 190536437247) ≤ (278669223 / 250000000) := by
  have h := checkLog_sound (w := (65536437247 / 315536437247)) (n := 12)
    (lo := (42152971 / 100000000)) (hi := (421529711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190536437247 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(190536437247 / 125000000000) = 1/(62500000000 / 190536437247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12579 : Bounds (111467689 / 100000000) (278669223 / 250000000) (Real.log (190536437247 / 62500000000)) := by
  have h := reflection_log_12579_neg
  have he : Real.log (190536437247 / 62500000000) = -Real.log (62500000000 / 190536437247) := by
    rw [show ((190536437247 / 62500000000) : ℝ) = ((62500000000 / 190536437247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12580_neg : (411447179 / 1000000000) ≤ -Real.log (1000 / 1509) ∧
    -Real.log (1000 / 1509) ≤ (20572359 / 50000000) := by
  have h := checkLog_sound (w := (509 / 2509)) (n := 12)
    (lo := (411447179 / 1000000000)) (hi := (20572359 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1509 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1509 / 1000) = 1/(1000 / 1509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12580 : Bounds (411447179 / 1000000000) (20572359 / 50000000) (Real.log (1509 / 1000)) := by
  have h := reflection_log_12580_neg
  have he : Real.log (1509 / 1000) = -Real.log (1000 / 1509) := by
    rw [show ((1509 / 1000) : ℝ) = ((1000 / 1509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12581_neg : (14226223 / 20000000) ≤ -Real.log (491 / 1000) ∧
    -Real.log (491 / 1000) ≤ (44456947 / 62500000) := by
  have h := checkLog_sound (w := (9 / 991)) (n := 12)
    (lo := (1816397 / 100000000)) (hi := (18163971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 491) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 491) = 1/(491 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12581 : Bounds (-44456947 / 62500000) (-14226223 / 20000000) (Real.log (491 / 1000)) := by
  have h := reflection_log_12581_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12582_neg : (50887 / 100000000) ≤ -Real.log (1000000 / 1000509) ∧
    -Real.log (1000000 / 1000509) ≤ (508871 / 1000000000) := by
  have h := checkLog_sound (w := (509 / 2000509)) (n := 12)
    (lo := (50887 / 100000000)) (hi := (508871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000509 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000509 / 1000000) = 1/(1000000 / 1000509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12582 : Bounds (50887 / 100000000) (508871 / 1000000000) (Real.log (1000509 / 1000000)) := by
  have h := reflection_log_12582_neg
  have he : Real.log (1000509 / 1000000) = -Real.log (1000000 / 1000509) := by
    rw [show ((1000509 / 1000000) : ℝ) = ((1000000 / 1000509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12583_neg : (509129 / 1000000000) ≤ -Real.log (999491 / 1000000) ∧
    -Real.log (999491 / 1000000) ≤ (50913 / 100000000) := by
  have h := checkLog_sound (w := (509 / 1999491)) (n := 12)
    (lo := (509129 / 1000000000)) (hi := (50913 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999491) = 1/(999491 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12583 : Bounds (-50913 / 100000000) (-509129 / 1000000000) (Real.log (999491 / 1000000)) := by
  have h := reflection_log_12583_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12584_neg : (58852601 / 250000000) ≤ -Real.log (250000 / 316357) ∧
    -Real.log (250000 / 316357) ≤ (47082081 / 200000000) := by
  have h := checkLog_sound (w := (66357 / 566357)) (n := 12)
    (lo := (58852601 / 250000000)) (hi := (47082081 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((316357 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(316357 / 250000) = 1/(250000 / 316357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12584 : Bounds (58852601 / 250000000) (47082081 / 200000000) (Real.log (316357 / 250000)) := by
  have h := reflection_log_12584_neg
  have he : Real.log (316357 / 250000) = -Real.log (250000 / 316357) := by
    rw [show ((316357 / 250000) : ℝ) = ((250000 / 316357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12585_neg : (154233631 / 500000000) ≤ -Real.log (183643 / 250000) ∧
    -Real.log (183643 / 250000) ≤ (308467263 / 1000000000) := by
  have h := checkLog_sound (w := (66357 / 433643)) (n := 12)
    (lo := (154233631 / 500000000)) (hi := (308467263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 183643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 183643) = 1/(183643 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12585 : Bounds (-308467263 / 1000000000) (-154233631 / 500000000) (Real.log (183643 / 250000)) := by
  have h := reflection_log_12585_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12586_neg : (237164003 / 1000000000) ≤ -Real.log (1000000 / 1267649) ∧
    -Real.log (1000000 / 1267649) ≤ (59291001 / 250000000) := by
  have h := checkLog_sound (w := (267649 / 2267649)) (n := 12)
    (lo := (237164003 / 1000000000)) (hi := (59291001 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1267649 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1267649 / 1000000) = 1/(1000000 / 1267649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12586 : Bounds (237164003 / 1000000000) (59291001 / 250000000) (Real.log (1267649 / 1000000)) := by
  have h := reflection_log_12586_neg
  have he : Real.log (1267649 / 1000000) = -Real.log (1000000 / 1267649) := by
    rw [show ((1267649 / 1000000) : ℝ) = ((1000000 / 1267649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12587_neg : (311495371 / 1000000000) ≤ -Real.log (732351 / 1000000) ∧
    -Real.log (732351 / 1000000) ≤ (77873843 / 250000000) := by
  have h := checkLog_sound (w := (267649 / 1732351)) (n := 12)
    (lo := (311495371 / 1000000000)) (hi := (77873843 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 732351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 732351) = 1/(732351 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12587 : Bounds (-77873843 / 250000000) (-311495371 / 1000000000) (Real.log (732351 / 1000000)) := by
  have h := reflection_log_12587_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12588_neg : (74331367 / 1000000000) ≤ -Real.log (928364012799 / 1000000000000) ∧
    -Real.log (928364012799 / 1000000000000) ≤ (9291421 / 125000000) := by
  have h := checkLog_sound (w := (71635987201 / 1928364012799)) (n := 12)
    (lo := (74331367 / 1000000000)) (hi := (9291421 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 928364012799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 928364012799) = 1/(928364012799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12588 : Bounds (-9291421 / 125000000) (-74331367 / 1000000000) (Real.log (928364012799 / 1000000000000)) := by
  have h := reflection_log_12588_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12589_neg : (73056857 / 1000000000) ≤ -Real.log (58096748551 / 62500000000) ∧
    -Real.log (58096748551 / 62500000000) ≤ (36528429 / 500000000) := by
  have h := checkLog_sound (w := (4403251449 / 120596748551)) (n := 12)
    (lo := (73056857 / 1000000000)) (hi := (36528429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 58096748551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 58096748551) = 1/(58096748551 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12589 : Bounds (-36528429 / 500000000) (-73056857 / 1000000000) (Real.log (58096748551 / 62500000000)) := by
  have h := reflection_log_12589_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12590_neg : (543877667 / 1000000000) ≤ -Real.log (500000000000 / 861336941783) ∧
    -Real.log (500000000000 / 861336941783) ≤ (135969417 / 250000000) := by
  have h := checkLog_sound (w := (361336941783 / 1361336941783)) (n := 12)
    (lo := (543877667 / 1000000000)) (hi := (135969417 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((861336941783 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(861336941783 / 500000000000) = 1/(500000000000 / 861336941783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12590 : Bounds (543877667 / 1000000000) (135969417 / 250000000) (Real.log (861336941783 / 500000000000)) := by
  have h := reflection_log_12590_neg
  have he : Real.log (861336941783 / 500000000000) = -Real.log (500000000000 / 861336941783) := by
    rw [show ((861336941783 / 500000000000) : ℝ) = ((500000000000 / 861336941783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12591_neg : (175571 / 320000) ≤ -Real.log (62500000000 / 108183183337) ∧
    -Real.log (62500000000 / 108183183337) ≤ (34291211 / 62500000) := by
  have h := checkLog_sound (w := (45683183337 / 170683183337)) (n := 12)
    (lo := (175571 / 320000)) (hi := (34291211 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108183183337 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108183183337 / 62500000000) = 1/(62500000000 / 108183183337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12591 : Bounds (175571 / 320000) (34291211 / 62500000) (Real.log (108183183337 / 62500000000)) := by
  have h := reflection_log_12591_neg
  have he : Real.log (108183183337 / 62500000000) = -Real.log (62500000000 / 108183183337) := by
    rw [show ((108183183337 / 62500000000) : ℝ) = ((62500000000 / 108183183337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12592_neg : (111467689 / 100000000) ≤ -Real.log (20000000000 / 60971659919) ∧
    -Real.log (20000000000 / 60971659919) ≤ (278669223 / 250000000) := by
  have h := checkLog_sound (w := (20971659919 / 100971659919)) (n := 12)
    (lo := (42152971 / 100000000)) (hi := (421529711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60971659919 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(60971659919 / 40000000000) = 1/(20000000000 / 60971659919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12592 : Bounds (111467689 / 100000000) (278669223 / 250000000) (Real.log (60971659919 / 20000000000)) := by
  have h := reflection_log_12592_neg
  have he : Real.log (60971659919 / 20000000000) = -Real.log (20000000000 / 60971659919) := by
    rw [show ((60971659919 / 20000000000) : ℝ) = ((20000000000 / 60971659919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12593_neg : (112275833 / 100000000) ≤ -Real.log (500000000000 / 1536659877801) ∧
    -Real.log (500000000000 / 1536659877801) ≤ (280689583 / 250000000) := by
  have h := checkLog_sound (w := (536659877801 / 2536659877801)) (n := 12)
    (lo := (8592223 / 20000000)) (hi := (429611151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1536659877801 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1536659877801 / 1000000000000) = 1/(500000000000 / 1536659877801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12593 : Bounds (112275833 / 100000000) (280689583 / 250000000) (Real.log (1536659877801 / 500000000000)) := by
  have h := reflection_log_12593_neg
  have he : Real.log (1536659877801 / 500000000000) = -Real.log (500000000000 / 1536659877801) := by
    rw [show ((1536659877801 / 500000000000) : ℝ) = ((500000000000 / 1536659877801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12594_neg : (413433277 / 1000000000) ≤ -Real.log (125 / 189) ∧
    -Real.log (125 / 189) ≤ (206716639 / 500000000) := by
  have h := checkLog_sound (w := (32 / 157)) (n := 12)
    (lo := (413433277 / 1000000000)) (hi := (206716639 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189 / 125) = 1/(125 / 189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12594 : Bounds (413433277 / 1000000000) (206716639 / 500000000) (Real.log (189 / 125)) := by
  have h := reflection_log_12594_neg
  have he : Real.log (189 / 125) = -Real.log (125 / 189) := by
    rw [show ((189 / 125) : ℝ) = ((125 / 189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12595_neg : (5604999 / 7812500) ≤ -Real.log (61 / 125) ∧
    -Real.log (61 / 125) ≤ (358719937 / 500000000) := by
  have h := checkLog_sound (w := (3 / 247)) (n := 12)
    (lo := (6073173 / 250000000)) (hi := (24292693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 122) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 122) = 1/(61 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12595 : Bounds (-358719937 / 500000000) (-5604999 / 7812500) (Real.log (61 / 125)) := by
  have h := reflection_log_12595_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12596_neg : (127967 / 250000000) ≤ -Real.log (15625 / 15633) ∧
    -Real.log (15625 / 15633) ≤ (511869 / 1000000000) := by
  have h := checkLog_sound (w := (4 / 15629)) (n := 12)
    (lo := (127967 / 250000000)) (hi := (511869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15633 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15633 / 15625) = 1/(15625 / 15633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12596 : Bounds (127967 / 250000000) (511869 / 1000000000) (Real.log (15633 / 15625)) := by
  have h := reflection_log_12596_neg
  have he : Real.log (15633 / 15625) = -Real.log (15625 / 15633) := by
    rw [show ((15633 / 15625) : ℝ) = ((15625 / 15633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12597_neg : (512131 / 1000000000) ≤ -Real.log (15617 / 15625) ∧
    -Real.log (15617 / 15625) ≤ (128033 / 250000000) := by
  have h := checkLog_sound (w := (4 / 15621)) (n := 12)
    (lo := (512131 / 1000000000)) (hi := (128033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 15617) = 1/(15617 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12597 : Bounds (-128033 / 250000000) (-512131 / 1000000000) (Real.log (15617 / 15625)) := by
  have h := reflection_log_12597_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12598_neg : (2367837 / 10000000) ≤ -Real.log (1000000 / 1267167) ∧
    -Real.log (1000000 / 1267167) ≤ (236783701 / 1000000000) := by
  have h := checkLog_sound (w := (267167 / 2267167)) (n := 12)
    (lo := (2367837 / 10000000)) (hi := (236783701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1267167 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1267167 / 1000000) = 1/(1000000 / 1267167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12598 : Bounds (2367837 / 10000000) (236783701 / 1000000000) (Real.log (1267167 / 1000000)) := by
  have h := reflection_log_12598_neg
  have he : Real.log (1267167 / 1000000) = -Real.log (1000000 / 1267167) := by
    rw [show ((1267167 / 1000000) : ℝ) = ((1000000 / 1267167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12599_neg : (310837433 / 1000000000) ≤ -Real.log (732833 / 1000000) ∧
    -Real.log (732833 / 1000000) ≤ (155418717 / 500000000) := by
  have h := checkLog_sound (w := (267167 / 1732833)) (n := 12)
    (lo := (310837433 / 1000000000)) (hi := (155418717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 732833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 732833) = 1/(732833 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12599 : Bounds (-155418717 / 500000000) (-310837433 / 1000000000) (Real.log (732833 / 1000000)) := by
  have h := reflection_log_12599_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12600_neg : (238539621 / 1000000000) ≤ -Real.log (500000 / 634697) ∧
    -Real.log (500000 / 634697) ≤ (119269811 / 500000000) := by
  have h := checkLog_sound (w := (134697 / 1134697)) (n := 12)
    (lo := (238539621 / 1000000000)) (hi := (119269811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((634697 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(634697 / 500000) = 1/(500000 / 634697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12600 : Bounds (238539621 / 1000000000) (119269811 / 500000000) (Real.log (634697 / 500000)) := by
  have h := reflection_log_12600_neg
  have he : Real.log (634697 / 500000) = -Real.log (500000 / 634697) := by
    rw [show ((634697 / 500000) : ℝ) = ((500000 / 634697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12601_neg : (39235119 / 125000000) ≤ -Real.log (365303 / 500000) ∧
    -Real.log (365303 / 500000) ≤ (313880953 / 1000000000) := by
  have h := checkLog_sound (w := (134697 / 865303)) (n := 12)
    (lo := (39235119 / 125000000)) (hi := (313880953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 365303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 365303) = 1/(365303 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12601 : Bounds (-313880953 / 1000000000) (-39235119 / 125000000) (Real.log (365303 / 500000)) := by
  have h := reflection_log_12601_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12602_neg : (7534133 / 100000000) ≤ -Real.log (231856718191 / 250000000000) ∧
    -Real.log (231856718191 / 250000000000) ≤ (75341331 / 1000000000) := by
  have h := checkLog_sound (w := (18143281809 / 481856718191)) (n := 12)
    (lo := (7534133 / 100000000)) (hi := (75341331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 231856718191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 231856718191) = 1/(231856718191 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12602 : Bounds (-75341331 / 1000000000) (-7534133 / 100000000) (Real.log (231856718191 / 250000000000)) := by
  have h := reflection_log_12602_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12603_neg : (74053733 / 1000000000) ≤ -Real.log (928621794111 / 1000000000000) ∧
    -Real.log (928621794111 / 1000000000000) ≤ (37026867 / 500000000) := by
  have h := checkLog_sound (w := (71378205889 / 1928621794111)) (n := 12)
    (lo := (74053733 / 1000000000)) (hi := (37026867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 928621794111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 928621794111) = 1/(928621794111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12603 : Bounds (-37026867 / 500000000) (-74053733 / 1000000000) (Real.log (928621794111 / 1000000000000)) := by
  have h := reflection_log_12603_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12604_neg : (547621133 / 1000000000) ≤ -Real.log (500000000000 / 864567370737) ∧
    -Real.log (500000000000 / 864567370737) ≤ (273810567 / 500000000) := by
  have h := checkLog_sound (w := (364567370737 / 1364567370737)) (n := 12)
    (lo := (547621133 / 1000000000)) (hi := (273810567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((864567370737 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(864567370737 / 500000000000) = 1/(500000000000 / 864567370737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12604 : Bounds (547621133 / 1000000000) (273810567 / 500000000) (Real.log (864567370737 / 500000000000)) := by
  have h := reflection_log_12604_neg
  have he : Real.log (864567370737 / 500000000000) = -Real.log (500000000000 / 864567370737) := by
    rw [show ((864567370737 / 500000000000) : ℝ) = ((500000000000 / 864567370737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12605_neg : (552420573 / 1000000000) ≤ -Real.log (125000000000 / 217181695743) ∧
    -Real.log (125000000000 / 217181695743) ≤ (276210287 / 500000000) := by
  have h := checkLog_sound (w := (92181695743 / 342181695743)) (n := 12)
    (lo := (552420573 / 1000000000)) (hi := (276210287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217181695743 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217181695743 / 125000000000) = 1/(125000000000 / 217181695743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12605 : Bounds (552420573 / 1000000000) (276210287 / 500000000) (Real.log (217181695743 / 125000000000)) := by
  have h := reflection_log_12605_neg
  have he : Real.log (217181695743 / 125000000000) = -Real.log (125000000000 / 217181695743) := by
    rw [show ((217181695743 / 125000000000) : ℝ) = ((125000000000 / 217181695743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12606_neg : (112275833 / 100000000) ≤ -Real.log (2500000000 / 7683299389) ∧
    -Real.log (2500000000 / 7683299389) ≤ (280689583 / 250000000) := by
  have h := checkLog_sound (w := (2683299389 / 12683299389)) (n := 12)
    (lo := (8592223 / 20000000)) (hi := (429611151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7683299389 / 5000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(7683299389 / 5000000000) = 1/(2500000000 / 7683299389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12606 : Bounds (112275833 / 100000000) (280689583 / 250000000) (Real.log (7683299389 / 2500000000)) := by
  have h := reflection_log_12606_neg
  have he : Real.log (7683299389 / 2500000000) = -Real.log (2500000000 / 7683299389) := by
    rw [show ((7683299389 / 2500000000) : ℝ) = ((2500000000 / 7683299389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12607_neg : (22617463 / 20000000) ≤ -Real.log (500000000000 / 1549180327869) ∧
    -Real.log (500000000000 / 1549180327869) ≤ (17669893 / 15625000) := by
  have h := checkLog_sound (w := (549180327869 / 2549180327869)) (n := 12)
    (lo := (43772597 / 100000000)) (hi := (437725971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1549180327869 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1549180327869 / 1000000000000) = 1/(500000000000 / 1549180327869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12607 : Bounds (22617463 / 20000000) (17669893 / 15625000) (Real.log (1549180327869 / 500000000000)) := by
  have h := reflection_log_12607_neg
  have he : Real.log (1549180327869 / 500000000000) = -Real.log (500000000000 / 1549180327869) := by
    rw [show ((1549180327869 / 500000000000) : ℝ) = ((500000000000 / 1549180327869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0197 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12608_neg : (207707719 / 500000000) ≤ -Real.log (200 / 303) ∧
    -Real.log (200 / 303) ≤ (415415439 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 503)) (n := 12)
    (lo := (207707719 / 500000000)) (hi := (415415439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303 / 200) = 1/(200 / 303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12608 : Bounds (207707719 / 500000000) (415415439 / 1000000000) (Real.log (303 / 200)) := by
  have h := reflection_log_12608_neg
  have he : Real.log (303 / 200) = -Real.log (200 / 303) := by
    rw [show ((303 / 200) : ℝ) = ((200 / 303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12609_neg : (723606387 / 1000000000) ≤ -Real.log (97 / 200) ∧
    -Real.log (97 / 200) ≤ (723606389 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 197)) (n := 12)
    (lo := (30459207 / 1000000000)) (hi := (3807401 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 97) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100 / 97) = 1/(97 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12609 : Bounds (-723606389 / 1000000000) (-723606387 / 1000000000) (Real.log (97 / 200)) := by
  have h := reflection_log_12609_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12610_neg : (514867 / 1000000000) ≤ -Real.log (200000 / 200103) ∧
    -Real.log (200000 / 200103) ≤ (128717 / 250000000) := by
  have h := checkLog_sound (w := (103 / 400103)) (n := 12)
    (lo := (514867 / 1000000000)) (hi := (128717 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200103 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200103 / 200000) = 1/(200000 / 200103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12610 : Bounds (514867 / 1000000000) (128717 / 250000000) (Real.log (200103 / 200000)) := by
  have h := reflection_log_12610_neg
  have he : Real.log (200103 / 200000) = -Real.log (200000 / 200103) := by
    rw [show ((200103 / 200000) : ℝ) = ((200000 / 200103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12611_neg : (128783 / 250000000) ≤ -Real.log (199897 / 200000) ∧
    -Real.log (199897 / 200000) ≤ (515133 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 399897)) (n := 12)
    (lo := (128783 / 250000000)) (hi := (515133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199897) = 1/(199897 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12611 : Bounds (-515133 / 1000000000) (-128783 / 250000000) (Real.log (199897 / 200000)) := by
  have h := reflection_log_12611_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12612_neg : (29769783 / 125000000) ≤ -Real.log (100000 / 126891) ∧
    -Real.log (100000 / 126891) ≤ (47631653 / 200000000) := by
  have h := checkLog_sound (w := (26891 / 226891)) (n := 12)
    (lo := (29769783 / 125000000)) (hi := (47631653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126891 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(126891 / 100000) = 1/(100000 / 126891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12612 : Bounds (29769783 / 125000000) (47631653 / 200000000) (Real.log (126891 / 100000)) := by
  have h := reflection_log_12612_neg
  have he : Real.log (126891 / 100000) = -Real.log (100000 / 126891) := by
    rw [show ((126891 / 100000) : ℝ) = ((100000 / 126891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12613_neg : (313218707 / 1000000000) ≤ -Real.log (73109 / 100000) ∧
    -Real.log (73109 / 100000) ≤ (78304677 / 250000000) := by
  have h := checkLog_sound (w := (26891 / 173109)) (n := 12)
    (lo := (313218707 / 1000000000)) (hi := (78304677 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 73109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 73109) = 1/(73109 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12613 : Bounds (-78304677 / 250000000) (-313218707 / 1000000000) (Real.log (73109 / 100000)) := by
  have h := reflection_log_12613_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12614_neg : (239915709 / 1000000000) ≤ -Real.log (500000 / 635571) ∧
    -Real.log (500000 / 635571) ≤ (23991571 / 100000000) := by
  have h := checkLog_sound (w := (135571 / 1135571)) (n := 12)
    (lo := (239915709 / 1000000000)) (hi := (23991571 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((635571 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(635571 / 500000) = 1/(500000 / 635571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12614 : Bounds (239915709 / 1000000000) (23991571 / 100000000) (Real.log (635571 / 500000)) := by
  have h := reflection_log_12614_neg
  have he : Real.log (635571 / 500000) = -Real.log (500000 / 635571) := by
    rw [show ((635571 / 500000) : ℝ) = ((500000 / 635571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12615_neg : (316276353 / 1000000000) ≤ -Real.log (364429 / 500000) ∧
    -Real.log (364429 / 500000) ≤ (158138177 / 500000000) := by
  have h := checkLog_sound (w := (135571 / 864429)) (n := 12)
    (lo := (316276353 / 1000000000)) (hi := (158138177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 364429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 364429) = 1/(364429 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12615 : Bounds (-158138177 / 500000000) (-316276353 / 1000000000) (Real.log (364429 / 500000)) := by
  have h := reflection_log_12615_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12616_neg : (19090161 / 250000000) ≤ -Real.log (231620503959 / 250000000000) ∧
    -Real.log (231620503959 / 250000000000) ≤ (15272129 / 200000000) := by
  have h := checkLog_sound (w := (18379496041 / 481620503959)) (n := 12)
    (lo := (19090161 / 250000000)) (hi := (15272129 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 231620503959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 231620503959) = 1/(231620503959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12616 : Bounds (-15272129 / 200000000) (-19090161 / 250000000) (Real.log (231620503959 / 250000000000)) := by
  have h := reflection_log_12616_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12617_neg : (75060443 / 1000000000) ≤ -Real.log (9276874119 / 10000000000) ∧
    -Real.log (9276874119 / 10000000000) ≤ (18765111 / 250000000) := by
  have h := checkLog_sound (w := (723125881 / 19276874119)) (n := 12)
    (lo := (75060443 / 1000000000)) (hi := (18765111 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9276874119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9276874119) = 1/(9276874119 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12617 : Bounds (-18765111 / 250000000) (-75060443 / 1000000000) (Real.log (9276874119 / 10000000000)) := by
  have h := reflection_log_12617_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12618_neg : (137844243 / 250000000) ≤ -Real.log (125000000000 / 216955162839) ∧
    -Real.log (125000000000 / 216955162839) ≤ (551376973 / 1000000000) := by
  have h := checkLog_sound (w := (91955162839 / 341955162839)) (n := 12)
    (lo := (137844243 / 250000000)) (hi := (551376973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216955162839 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216955162839 / 125000000000) = 1/(125000000000 / 216955162839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12618 : Bounds (137844243 / 250000000) (551376973 / 1000000000) (Real.log (216955162839 / 125000000000)) := by
  have h := reflection_log_12618_neg
  have he : Real.log (216955162839 / 125000000000) = -Real.log (125000000000 / 216955162839) := by
    rw [show ((216955162839 / 125000000000) : ℝ) = ((125000000000 / 216955162839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12619_neg : (278096031 / 500000000) ≤ -Real.log (15625000000 / 27250292581) ∧
    -Real.log (15625000000 / 27250292581) ≤ (556192063 / 1000000000) := by
  have h := checkLog_sound (w := (11625292581 / 42875292581)) (n := 12)
    (lo := (278096031 / 500000000)) (hi := (556192063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27250292581 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27250292581 / 15625000000) = 1/(15625000000 / 27250292581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12619 : Bounds (278096031 / 500000000) (556192063 / 1000000000) (Real.log (27250292581 / 15625000000)) := by
  have h := reflection_log_12619_neg
  have he : Real.log (27250292581 / 15625000000) = -Real.log (15625000000 / 27250292581) := by
    rw [show ((27250292581 / 15625000000) : ℝ) = ((15625000000 / 27250292581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12620_neg : (22617463 / 20000000) ≤ -Real.log (125000000000 / 387295081967) ∧
    -Real.log (125000000000 / 387295081967) ≤ (17669893 / 15625000) := by
  have h := checkLog_sound (w := (137295081967 / 637295081967)) (n := 12)
    (lo := (43772597 / 100000000)) (hi := (437725971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387295081967 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(387295081967 / 250000000000) = 1/(125000000000 / 387295081967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12620 : Bounds (22617463 / 20000000) (17669893 / 15625000) (Real.log (387295081967 / 125000000000)) := by
  have h := reflection_log_12620_neg
  have he : Real.log (387295081967 / 125000000000) = -Real.log (125000000000 / 387295081967) := by
    rw [show ((387295081967 / 125000000000) : ℝ) = ((125000000000 / 387295081967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12621_neg : (569510913 / 500000000) ≤ -Real.log (62500000000 / 195231958763) ∧
    -Real.log (62500000000 / 195231958763) ≤ (284755457 / 250000000) := by
  have h := checkLog_sound (w := (70231958763 / 320231958763)) (n := 12)
    (lo := (222937323 / 500000000)) (hi := (445874647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((195231958763 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(195231958763 / 125000000000) = 1/(62500000000 / 195231958763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12621 : Bounds (569510913 / 500000000) (284755457 / 250000000) (Real.log (195231958763 / 62500000000)) := by
  have h := reflection_log_12621_neg
  have he : Real.log (195231958763 / 62500000000) = -Real.log (62500000000 / 195231958763) := by
    rw [show ((195231958763 / 62500000000) : ℝ) = ((62500000000 / 195231958763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12622_neg : (208696839 / 500000000) ≤ -Real.log (500 / 759) ∧
    -Real.log (500 / 759) ≤ (417393679 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 1259)) (n := 12)
    (lo := (208696839 / 500000000)) (hi := (417393679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((759 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(759 / 500) = 1/(500 / 759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12622 : Bounds (208696839 / 500000000) (417393679 / 1000000000) (Real.log (759 / 500)) := by
  have h := reflection_log_12622_neg
  have he : Real.log (759 / 500) = -Real.log (500 / 759) := by
    rw [show ((759 / 500) : ℝ) = ((500 / 759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12623_neg : (182452791 / 250000000) ≤ -Real.log (241 / 500) ∧
    -Real.log (241 / 500) ≤ (364905583 / 500000000) := by
  have h := checkLog_sound (w := (9 / 491)) (n := 12)
    (lo := (2291499 / 62500000)) (hi := (7332797 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 241) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 241) = 1/(241 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12623 : Bounds (-364905583 / 500000000) (-182452791 / 250000000) (Real.log (241 / 500)) := by
  have h := reflection_log_12623_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12624_neg : (103573 / 200000000) ≤ -Real.log (500000 / 500259) ∧
    -Real.log (500000 / 500259) ≤ (258933 / 500000000) := by
  have h := checkLog_sound (w := (259 / 1000259)) (n := 12)
    (lo := (103573 / 200000000)) (hi := (258933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500259 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500259 / 500000) = 1/(500000 / 500259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12624 : Bounds (103573 / 200000000) (258933 / 500000000) (Real.log (500259 / 500000)) := by
  have h := reflection_log_12624_neg
  have he : Real.log (500259 / 500000) = -Real.log (500000 / 500259) := by
    rw [show ((500259 / 500000) : ℝ) = ((500000 / 500259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12625_neg : (259067 / 500000000) ≤ -Real.log (499741 / 500000) ∧
    -Real.log (499741 / 500000) ≤ (103627 / 200000000) := by
  have h := checkLog_sound (w := (259 / 999741)) (n := 12)
    (lo := (259067 / 500000000)) (hi := (103627 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499741) = 1/(499741 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12625 : Bounds (-103627 / 200000000) (-259067 / 500000000) (Real.log (499741 / 500000)) := by
  have h := reflection_log_12625_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12626_neg : (47906503 / 200000000) ≤ -Real.log (200000 / 254131) ∧
    -Real.log (200000 / 254131) ≤ (59883129 / 250000000) := by
  have h := checkLog_sound (w := (54131 / 454131)) (n := 12)
    (lo := (47906503 / 200000000)) (hi := (59883129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((254131 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(254131 / 200000) = 1/(200000 / 254131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12626 : Bounds (47906503 / 200000000) (59883129 / 250000000) (Real.log (254131 / 200000)) := by
  have h := reflection_log_12626_neg
  have he : Real.log (254131 / 200000) = -Real.log (200000 / 254131) := by
    rw [show ((254131 / 200000) : ℝ) = ((200000 / 254131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12627_neg : (315608407 / 1000000000) ≤ -Real.log (145869 / 200000) ∧
    -Real.log (145869 / 200000) ≤ (39451051 / 125000000) := by
  have h := checkLog_sound (w := (54131 / 345869)) (n := 12)
    (lo := (315608407 / 1000000000)) (hi := (39451051 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 145869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 145869) = 1/(145869 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12627 : Bounds (-39451051 / 125000000) (-315608407 / 1000000000) (Real.log (145869 / 200000)) := by
  have h := reflection_log_12627_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12628_neg : (30161631 / 125000000) ≤ -Real.log (500000 / 636447) ∧
    -Real.log (500000 / 636447) ≤ (241293049 / 1000000000) := by
  have h := checkLog_sound (w := (136447 / 1136447)) (n := 12)
    (lo := (30161631 / 125000000)) (hi := (241293049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((636447 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(636447 / 500000) = 1/(500000 / 636447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12628 : Bounds (30161631 / 125000000) (241293049 / 1000000000) (Real.log (636447 / 500000)) := by
  have h := reflection_log_12628_neg
  have he : Real.log (636447 / 500000) = -Real.log (500000 / 636447) := by
    rw [show ((636447 / 500000) : ℝ) = ((500000 / 636447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12629_neg : (318683007 / 1000000000) ≤ -Real.log (363553 / 500000) ∧
    -Real.log (363553 / 500000) ≤ (2489711 / 7812500) := by
  have h := checkLog_sound (w := (136447 / 863553)) (n := 12)
    (lo := (318683007 / 1000000000)) (hi := (2489711 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 363553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 363553) = 1/(363553 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12629 : Bounds (-2489711 / 7812500) (-318683007 / 1000000000) (Real.log (363553 / 500000)) := by
  have h := reflection_log_12629_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12630_neg : (77389959 / 1000000000) ≤ -Real.log (231382216191 / 250000000000) ∧
    -Real.log (231382216191 / 250000000000) ≤ (1934749 / 25000000) := by
  have h := checkLog_sound (w := (18617783809 / 481382216191)) (n := 12)
    (lo := (77389959 / 1000000000)) (hi := (1934749 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 231382216191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 231382216191) = 1/(231382216191 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12630 : Bounds (-1934749 / 25000000) (-77389959 / 1000000000) (Real.log (231382216191 / 250000000000)) := by
  have h := reflection_log_12630_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12631_neg : (19018973 / 250000000) ≤ -Real.log (37069834839 / 40000000000) ∧
    -Real.log (37069834839 / 40000000000) ≤ (76075893 / 1000000000) := by
  have h := checkLog_sound (w := (2930165161 / 77069834839)) (n := 12)
    (lo := (19018973 / 250000000)) (hi := (76075893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37069834839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37069834839) = 1/(37069834839 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12631 : Bounds (-76075893 / 1000000000) (-19018973 / 250000000) (Real.log (37069834839 / 40000000000)) := by
  have h := reflection_log_12631_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12632_neg : (555140923 / 1000000000) ≤ -Real.log (100000000000 / 174218648239) ∧
    -Real.log (100000000000 / 174218648239) ≤ (138785231 / 250000000) := by
  have h := checkLog_sound (w := (74218648239 / 274218648239)) (n := 12)
    (lo := (555140923 / 1000000000)) (hi := (138785231 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174218648239 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(174218648239 / 100000000000) = 1/(100000000000 / 174218648239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12632 : Bounds (555140923 / 1000000000) (138785231 / 250000000) (Real.log (174218648239 / 100000000000)) := by
  have h := reflection_log_12632_neg
  have he : Real.log (174218648239 / 100000000000) = -Real.log (100000000000 / 174218648239) := by
    rw [show ((174218648239 / 100000000000) : ℝ) = ((100000000000 / 174218648239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12633_neg : (111995211 / 200000000) ≤ -Real.log (500000000000 / 875315291031) ∧
    -Real.log (500000000000 / 875315291031) ≤ (69997007 / 125000000) := by
  have h := checkLog_sound (w := (375315291031 / 1375315291031)) (n := 12)
    (lo := (111995211 / 200000000)) (hi := (69997007 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((875315291031 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(875315291031 / 500000000000) = 1/(500000000000 / 875315291031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12633 : Bounds (111995211 / 200000000) (69997007 / 125000000) (Real.log (875315291031 / 500000000000)) := by
  have h := reflection_log_12633_neg
  have he : Real.log (875315291031 / 500000000000) = -Real.log (500000000000 / 875315291031) := by
    rw [show ((875315291031 / 500000000000) : ℝ) = ((500000000000 / 875315291031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12634_neg : (569510913 / 500000000) ≤ -Real.log (500000000000 / 1561855670103) ∧
    -Real.log (500000000000 / 1561855670103) ≤ (284755457 / 250000000) := by
  have h := checkLog_sound (w := (561855670103 / 2561855670103)) (n := 12)
    (lo := (222937323 / 500000000)) (hi := (445874647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1561855670103 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1561855670103 / 1000000000000) = 1/(500000000000 / 1561855670103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12634 : Bounds (569510913 / 500000000) (284755457 / 250000000) (Real.log (1561855670103 / 500000000000)) := by
  have h := reflection_log_12634_neg
  have he : Real.log (1561855670103 / 500000000000) = -Real.log (500000000000 / 1561855670103) := by
    rw [show ((1561855670103 / 500000000000) : ℝ) = ((500000000000 / 1561855670103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12635_neg : (1147204843 / 1000000000) ≤ -Real.log (500000000000 / 1574688796681) ∧
    -Real.log (500000000000 / 1574688796681) ≤ (229440969 / 200000000) := by
  have h := checkLog_sound (w := (574688796681 / 2574688796681)) (n := 12)
    (lo := (454057663 / 1000000000)) (hi := (7094651 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1574688796681 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1574688796681 / 1000000000000) = 1/(500000000000 / 1574688796681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12635 : Bounds (1147204843 / 1000000000) (229440969 / 200000000) (Real.log (1574688796681 / 500000000000)) := by
  have h := reflection_log_12635_neg
  have he : Real.log (1574688796681 / 500000000000) = -Real.log (500000000000 / 1574688796681) := by
    rw [show ((1574688796681 / 500000000000) : ℝ) = ((500000000000 / 1574688796681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12636_neg : (419368013 / 1000000000) ≤ -Real.log (1000 / 1521) ∧
    -Real.log (1000 / 1521) ≤ (209684007 / 500000000) := by
  have h := checkLog_sound (w := (521 / 2521)) (n := 12)
    (lo := (419368013 / 1000000000)) (hi := (209684007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1521 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1521 / 1000) = 1/(1000 / 1521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12636 : Bounds (419368013 / 1000000000) (209684007 / 500000000) (Real.log (1521 / 1000)) := by
  have h := reflection_log_12636_neg
  have he : Real.log (1521 / 1000) = -Real.log (1000 / 1521) := by
    rw [show ((1521 / 1000) : ℝ) = ((1000 / 1521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12637_neg : (736054681 / 1000000000) ≤ -Real.log (479 / 1000) ∧
    -Real.log (479 / 1000) ≤ (736054683 / 1000000000) := by
  have h := checkLog_sound (w := (21 / 979)) (n := 12)
    (lo := (42907501 / 1000000000)) (hi := (21453751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 479) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 479) = 1/(479 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12637 : Bounds (-736054683 / 1000000000) (-736054681 / 1000000000) (Real.log (479 / 1000)) := by
  have h := reflection_log_12637_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12638_neg : (16277 / 31250000) ≤ -Real.log (1000000 / 1000521) ∧
    -Real.log (1000000 / 1000521) ≤ (104173 / 200000000) := by
  have h := checkLog_sound (w := (521 / 2000521)) (n := 12)
    (lo := (16277 / 31250000)) (hi := (104173 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000521 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000521 / 1000000) = 1/(1000000 / 1000521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12638 : Bounds (16277 / 31250000) (104173 / 200000000) (Real.log (1000521 / 1000000)) := by
  have h := reflection_log_12638_neg
  have he : Real.log (1000521 / 1000000) = -Real.log (1000000 / 1000521) := by
    rw [show ((1000521 / 1000000) : ℝ) = ((1000000 / 1000521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12639_neg : (104227 / 200000000) ≤ -Real.log (999479 / 1000000) ∧
    -Real.log (999479 / 1000000) ≤ (32571 / 62500000) := by
  have h := checkLog_sound (w := (521 / 1999479)) (n := 12)
    (lo := (104227 / 200000000)) (hi := (32571 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999479) = 1/(999479 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12639 : Bounds (-32571 / 62500000) (-104227 / 200000000) (Real.log (999479 / 1000000)) := by
  have h := reflection_log_12639_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12640_neg : (30113503 / 125000000) ≤ -Real.log (250000 / 318101) ∧
    -Real.log (250000 / 318101) ≤ (9636321 / 40000000) := by
  have h := checkLog_sound (w := (68101 / 568101)) (n := 12)
    (lo := (30113503 / 125000000)) (hi := (9636321 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((318101 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(318101 / 250000) = 1/(250000 / 318101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12640 : Bounds (30113503 / 125000000) (9636321 / 40000000) (Real.log (318101 / 250000)) := by
  have h := reflection_log_12640_neg
  have he : Real.log (318101 / 250000) = -Real.log (250000 / 318101) := by
    rw [show ((318101 / 250000) : ℝ) = ((250000 / 318101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12641_neg : (318009329 / 1000000000) ≤ -Real.log (181899 / 250000) ∧
    -Real.log (181899 / 250000) ≤ (31800933 / 100000000) := by
  have h := checkLog_sound (w := (68101 / 431899)) (n := 12)
    (lo := (318009329 / 1000000000)) (hi := (31800933 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 181899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 181899) = 1/(181899 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12641 : Bounds (-31800933 / 100000000) (-318009329 / 1000000000) (Real.log (181899 / 250000)) := by
  have h := reflection_log_12641_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12642_neg : (121335423 / 500000000) ≤ -Real.log (1000000 / 1274649) ∧
    -Real.log (1000000 / 1274649) ≤ (242670847 / 1000000000) := by
  have h := checkLog_sound (w := (274649 / 2274649)) (n := 12)
    (lo := (121335423 / 500000000)) (hi := (242670847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1274649 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1274649 / 1000000) = 1/(1000000 / 1274649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12642 : Bounds (121335423 / 500000000) (242670847 / 1000000000) (Real.log (1274649 / 1000000)) := by
  have h := reflection_log_12642_neg
  have he : Real.log (1274649 / 1000000) = -Real.log (1000000 / 1274649) := by
    rw [show ((1274649 / 1000000) : ℝ) = ((1000000 / 1274649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12643_neg : (321099603 / 1000000000) ≤ -Real.log (725351 / 1000000) ∧
    -Real.log (725351 / 1000000) ≤ (80274901 / 250000000) := by
  have h := checkLog_sound (w := (274649 / 1725351)) (n := 12)
    (lo := (321099603 / 1000000000)) (hi := (80274901 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 725351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 725351) = 1/(725351 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12643 : Bounds (-80274901 / 250000000) (-321099603 / 1000000000) (Real.log (725351 / 1000000)) := by
  have h := reflection_log_12643_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12644_neg : (19607189 / 250000000) ≤ -Real.log (924567926799 / 1000000000000) ∧
    -Real.log (924567926799 / 1000000000000) ≤ (78428757 / 1000000000) := by
  have h := checkLog_sound (w := (75432073201 / 1924567926799)) (n := 12)
    (lo := (19607189 / 250000000)) (hi := (78428757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 924567926799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 924567926799) = 1/(924567926799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12644 : Bounds (-78428757 / 1000000000) (-19607189 / 250000000) (Real.log (924567926799 / 1000000000000)) := by
  have h := reflection_log_12644_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12645_neg : (15420261 / 200000000) ≤ -Real.log (57862253799 / 62500000000) ∧
    -Real.log (57862253799 / 62500000000) ≤ (38550653 / 500000000) := by
  have h := checkLog_sound (w := (4637746201 / 120362253799)) (n := 12)
    (lo := (15420261 / 200000000)) (hi := (38550653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 57862253799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 57862253799) = 1/(57862253799 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12645 : Bounds (-38550653 / 500000000) (-15420261 / 200000000) (Real.log (57862253799 / 62500000000)) := by
  have h := reflection_log_12645_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12646_neg : (279458677 / 500000000) ≤ -Real.log (125000000000 / 218597271013) ∧
    -Real.log (125000000000 / 218597271013) ≤ (111783471 / 200000000) := by
  have h := checkLog_sound (w := (93597271013 / 343597271013)) (n := 12)
    (lo := (279458677 / 500000000)) (hi := (111783471 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218597271013 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218597271013 / 125000000000) = 1/(125000000000 / 218597271013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12646 : Bounds (279458677 / 500000000) (111783471 / 200000000) (Real.log (218597271013 / 125000000000)) := by
  have h := reflection_log_12646_neg
  have he : Real.log (218597271013 / 125000000000) = -Real.log (125000000000 / 218597271013) := by
    rw [show ((218597271013 / 125000000000) : ℝ) = ((125000000000 / 218597271013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12647_neg : (563770449 / 1000000000) ≤ -Real.log (500000000000 / 878642891511) ∧
    -Real.log (500000000000 / 878642891511) ≤ (11275409 / 20000000) := by
  have h := checkLog_sound (w := (378642891511 / 1378642891511)) (n := 12)
    (lo := (563770449 / 1000000000)) (hi := (11275409 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((878642891511 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(878642891511 / 500000000000) = 1/(500000000000 / 878642891511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12647 : Bounds (563770449 / 1000000000) (11275409 / 20000000) (Real.log (878642891511 / 500000000000)) := by
  have h := reflection_log_12647_neg
  have he : Real.log (878642891511 / 500000000000) = -Real.log (500000000000 / 878642891511) := by
    rw [show ((878642891511 / 500000000000) : ℝ) = ((500000000000 / 878642891511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12648_neg : (1147204843 / 1000000000) ≤ -Real.log (12500000000 / 39367219917) ∧
    -Real.log (12500000000 / 39367219917) ≤ (229440969 / 200000000) := by
  have h := checkLog_sound (w := (14367219917 / 64367219917)) (n := 12)
    (lo := (454057663 / 1000000000)) (hi := (7094651 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39367219917 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(39367219917 / 25000000000) = 1/(12500000000 / 39367219917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12648 : Bounds (1147204843 / 1000000000) (229440969 / 200000000) (Real.log (39367219917 / 12500000000)) := by
  have h := reflection_log_12648_neg
  have he : Real.log (39367219917 / 12500000000) = -Real.log (12500000000 / 39367219917) := by
    rw [show ((39367219917 / 12500000000) : ℝ) = ((12500000000 / 39367219917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12649_neg : (577711347 / 500000000) ≤ -Real.log (250000000000 / 793841336117) ∧
    -Real.log (250000000000 / 793841336117) ≤ (144427837 / 125000000) := by
  have h := checkLog_sound (w := (293841336117 / 1293841336117)) (n := 12)
    (lo := (231137757 / 500000000)) (hi := (92455103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((793841336117 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(793841336117 / 500000000000) = 1/(250000000000 / 793841336117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12649 : Bounds (577711347 / 500000000) (144427837 / 125000000) (Real.log (793841336117 / 250000000000)) := by
  have h := reflection_log_12649_neg
  have he : Real.log (793841336117 / 250000000000) = -Real.log (250000000000 / 793841336117) := by
    rw [show ((793841336117 / 250000000000) : ℝ) = ((250000000000 / 793841336117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12650_neg : (421338457 / 1000000000) ≤ -Real.log (250 / 381) ∧
    -Real.log (250 / 381) ≤ (210669229 / 500000000) := by
  have h := checkLog_sound (w := (131 / 631)) (n := 12)
    (lo := (421338457 / 1000000000)) (hi := (210669229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381 / 250) = 1/(250 / 381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12650 : Bounds (421338457 / 1000000000) (210669229 / 500000000) (Real.log (381 / 250)) := by
  have h := reflection_log_12650_neg
  have he : Real.log (381 / 250) = -Real.log (250 / 381) := by
    rw [show ((381 / 250) : ℝ) = ((250 / 381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12651_neg : (46396089 / 62500000) ≤ -Real.log (119 / 250) ∧
    -Real.log (119 / 250) ≤ (371168713 / 500000000) := by
  have h := checkLog_sound (w := (3 / 122)) (n := 12)
    (lo := (12297561 / 250000000)) (hi := (9838049 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 119) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 119) = 1/(119 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12651 : Bounds (-371168713 / 500000000) (-46396089 / 62500000) (Real.log (119 / 250)) := by
  have h := reflection_log_12651_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12652_neg : (261931 / 500000000) ≤ -Real.log (250000 / 250131) ∧
    -Real.log (250000 / 250131) ≤ (523863 / 1000000000) := by
  have h := checkLog_sound (w := (131 / 500131)) (n := 12)
    (lo := (261931 / 500000000)) (hi := (523863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250131 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250131 / 250000) = 1/(250000 / 250131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12652 : Bounds (261931 / 500000000) (523863 / 1000000000) (Real.log (250131 / 250000)) := by
  have h := reflection_log_12652_neg
  have he : Real.log (250131 / 250000) = -Real.log (250000 / 250131) := by
    rw [show ((250131 / 250000) : ℝ) = ((250000 / 250131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12653_neg : (524137 / 1000000000) ≤ -Real.log (249869 / 250000) ∧
    -Real.log (249869 / 250000) ≤ (262069 / 500000000) := by
  have h := checkLog_sound (w := (131 / 499869)) (n := 12)
    (lo := (524137 / 1000000000)) (hi := (262069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249869) = 1/(249869 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12653 : Bounds (-262069 / 500000000) (-524137 / 1000000000) (Real.log (249869 / 250000)) := by
  have h := reflection_log_12653_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12654_neg : (242284783 / 1000000000) ≤ -Real.log (1000000 / 1274157) ∧
    -Real.log (1000000 / 1274157) ≤ (15142799 / 62500000) := by
  have h := checkLog_sound (w := (274157 / 2274157)) (n := 12)
    (lo := (242284783 / 1000000000)) (hi := (15142799 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1274157 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1274157 / 1000000) = 1/(1000000 / 1274157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12654 : Bounds (242284783 / 1000000000) (15142799 / 62500000) (Real.log (1274157 / 1000000)) := by
  have h := reflection_log_12654_neg
  have he : Real.log (1274157 / 1000000) = -Real.log (1000000 / 1274157) := by
    rw [show ((1274157 / 1000000) : ℝ) = ((1000000 / 1274157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12655_neg : (16021077 / 50000000) ≤ -Real.log (725843 / 1000000) ∧
    -Real.log (725843 / 1000000) ≤ (320421541 / 1000000000) := by
  have h := checkLog_sound (w := (274157 / 1725843)) (n := 12)
    (lo := (16021077 / 50000000)) (hi := (320421541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 725843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 725843) = 1/(725843 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12655 : Bounds (-320421541 / 1000000000) (-16021077 / 50000000) (Real.log (725843 / 1000000)) := by
  have h := reflection_log_12655_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12656_neg : (244049099 / 1000000000) ≤ -Real.log (1000000 / 1276407) ∧
    -Real.log (1000000 / 1276407) ≤ (2440491 / 10000000) := by
  have h := checkLog_sound (w := (276407 / 2276407)) (n := 12)
    (lo := (244049099 / 1000000000)) (hi := (2440491 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1276407 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1276407 / 1000000) = 1/(1000000 / 1276407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12656 : Bounds (244049099 / 1000000000) (2440491 / 10000000) (Real.log (1276407 / 1000000)) := by
  have h := reflection_log_12656_neg
  have he : Real.log (1276407 / 1000000) = -Real.log (1000000 / 1276407) := by
    rw [show ((1276407 / 1000000) : ℝ) = ((1000000 / 1276407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12657_neg : (323526199 / 1000000000) ≤ -Real.log (723593 / 1000000) ∧
    -Real.log (723593 / 1000000) ≤ (1617631 / 5000000) := by
  have h := checkLog_sound (w := (276407 / 1723593)) (n := 12)
    (lo := (323526199 / 1000000000)) (hi := (1617631 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 723593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 723593) = 1/(723593 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12657 : Bounds (-1617631 / 5000000) (-323526199 / 1000000000) (Real.log (723593 / 1000000)) := by
  have h := reflection_log_12657_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12658_neg : (79477099 / 1000000000) ≤ -Real.log (923599170351 / 1000000000000) ∧
    -Real.log (923599170351 / 1000000000000) ≤ (794771 / 10000000) := by
  have h := checkLog_sound (w := (76400829649 / 1923599170351)) (n := 12)
    (lo := (79477099 / 1000000000)) (hi := (794771 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 923599170351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 923599170351) = 1/(923599170351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12658 : Bounds (-794771 / 10000000) (-79477099 / 1000000000) (Real.log (923599170351 / 1000000000000)) := by
  have h := reflection_log_12658_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12659_neg : (78136757 / 1000000000) ≤ -Real.log (924837939351 / 1000000000000) ∧
    -Real.log (924837939351 / 1000000000000) ≤ (39068379 / 500000000) := by
  have h := checkLog_sound (w := (75162060649 / 1924837939351)) (n := 12)
    (lo := (78136757 / 1000000000)) (hi := (39068379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 924837939351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 924837939351) = 1/(924837939351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12659 : Bounds (-39068379 / 500000000) (-78136757 / 1000000000) (Real.log (924837939351 / 1000000000000)) := by
  have h := reflection_log_12659_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12660_neg : (140676581 / 250000000) ≤ -Real.log (100000000000 / 175541680501) ∧
    -Real.log (100000000000 / 175541680501) ≤ (22508253 / 40000000) := by
  have h := checkLog_sound (w := (75541680501 / 275541680501)) (n := 12)
    (lo := (140676581 / 250000000)) (hi := (22508253 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175541680501 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175541680501 / 100000000000) = 1/(100000000000 / 175541680501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12660 : Bounds (140676581 / 250000000) (22508253 / 40000000) (Real.log (175541680501 / 100000000000)) := by
  have h := reflection_log_12660_neg
  have he : Real.log (175541680501 / 100000000000) = -Real.log (100000000000 / 175541680501) := by
    rw [show ((175541680501 / 100000000000) : ℝ) = ((100000000000 / 175541680501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12661_neg : (283787649 / 500000000) ≤ -Real.log (500000000000 / 881992363111) ∧
    -Real.log (500000000000 / 881992363111) ≤ (567575299 / 1000000000) := by
  have h := checkLog_sound (w := (381992363111 / 1381992363111)) (n := 12)
    (lo := (283787649 / 500000000)) (hi := (567575299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((881992363111 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(881992363111 / 500000000000) = 1/(500000000000 / 881992363111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12661 : Bounds (283787649 / 500000000) (567575299 / 1000000000) (Real.log (881992363111 / 500000000000)) := by
  have h := reflection_log_12661_neg
  have he : Real.log (881992363111 / 500000000000) = -Real.log (500000000000 / 881992363111) := by
    rw [show ((881992363111 / 500000000000) : ℝ) = ((500000000000 / 881992363111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12662_neg : (577711347 / 500000000) ≤ -Real.log (500000000000 / 1587682672233) ∧
    -Real.log (500000000000 / 1587682672233) ≤ (144427837 / 125000000) := by
  have h := checkLog_sound (w := (587682672233 / 2587682672233)) (n := 12)
    (lo := (231137757 / 500000000)) (hi := (92455103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1587682672233 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1587682672233 / 1000000000000) = 1/(500000000000 / 1587682672233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12662 : Bounds (577711347 / 500000000) (144427837 / 125000000) (Real.log (1587682672233 / 500000000000)) := by
  have h := reflection_log_12662_neg
  have he : Real.log (1587682672233 / 500000000000) = -Real.log (500000000000 / 1587682672233) := by
    rw [show ((1587682672233 / 500000000000) : ℝ) = ((500000000000 / 1587682672233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12663_neg : (1163675881 / 1000000000) ≤ -Real.log (100000000000 / 320168067227) ∧
    -Real.log (100000000000 / 320168067227) ≤ (1163675883 / 1000000000) := by
  have h := checkLog_sound (w := (120168067227 / 520168067227)) (n := 12)
    (lo := (470528701 / 1000000000)) (hi := (235264351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320168067227 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320168067227 / 200000000000) = 1/(100000000000 / 320168067227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12663 : Bounds (1163675881 / 1000000000) (1163675883 / 1000000000) (Real.log (320168067227 / 100000000000)) := by
  have h := reflection_log_12663_neg
  have he : Real.log (320168067227 / 100000000000) = -Real.log (100000000000 / 320168067227) := by
    rw [show ((320168067227 / 100000000000) : ℝ) = ((100000000000 / 320168067227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12664_neg : (211652513 / 500000000) ≤ -Real.log (1000 / 1527) ∧
    -Real.log (1000 / 1527) ≤ (423305027 / 1000000000) := by
  have h := checkLog_sound (w := (527 / 2527)) (n := 12)
    (lo := (211652513 / 500000000)) (hi := (423305027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1527 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1527 / 1000) = 1/(1000 / 1527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12664 : Bounds (211652513 / 500000000) (423305027 / 1000000000) (Real.log (1527 / 1000)) := by
  have h := reflection_log_12664_neg
  have he : Real.log (1527 / 1000) = -Real.log (1000 / 1527) := by
    rw [show ((1527 / 1000) : ℝ) = ((1000 / 1527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12665_neg : (748659889 / 1000000000) ≤ -Real.log (473 / 1000) ∧
    -Real.log (473 / 1000) ≤ (748659891 / 1000000000) := by
  have h := checkLog_sound (w := (27 / 973)) (n := 12)
    (lo := (55512709 / 1000000000)) (hi := (5551271 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 473) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 473) = 1/(473 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12665 : Bounds (-748659891 / 1000000000) (-748659889 / 1000000000) (Real.log (473 / 1000)) := by
  have h := reflection_log_12665_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12666_neg : (526861 / 1000000000) ≤ -Real.log (1000000 / 1000527) ∧
    -Real.log (1000000 / 1000527) ≤ (263431 / 500000000) := by
  have h := checkLog_sound (w := (527 / 2000527)) (n := 12)
    (lo := (526861 / 1000000000)) (hi := (263431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000527 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000527 / 1000000) = 1/(1000000 / 1000527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12666 : Bounds (526861 / 1000000000) (263431 / 500000000) (Real.log (1000527 / 1000000)) := by
  have h := reflection_log_12666_neg
  have he : Real.log (1000527 / 1000000) = -Real.log (1000000 / 1000527) := by
    rw [show ((1000527 / 1000000) : ℝ) = ((1000000 / 1000527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12667_neg : (263569 / 500000000) ≤ -Real.log (999473 / 1000000) ∧
    -Real.log (999473 / 1000000) ≤ (527139 / 1000000000) := by
  have h := checkLog_sound (w := (527 / 1999473)) (n := 12)
    (lo := (263569 / 500000000)) (hi := (527139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999473) = 1/(999473 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12667 : Bounds (-527139 / 1000000000) (-263569 / 500000000) (Real.log (999473 / 1000000)) := by
  have h := reflection_log_12667_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12668_neg : (121831 / 500000) ≤ -Real.log (1000000 / 1275913) ∧
    -Real.log (1000000 / 1275913) ≤ (243662001 / 1000000000) := by
  have h := checkLog_sound (w := (275913 / 2275913)) (n := 12)
    (lo := (121831 / 500000)) (hi := (243662001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1275913 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1275913 / 1000000) = 1/(1000000 / 1275913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12668 : Bounds (121831 / 500000) (243662001 / 1000000000) (Real.log (1275913 / 1000000)) := by
  have h := reflection_log_12668_neg
  have he : Real.log (1275913 / 1000000) = -Real.log (1000000 / 1275913) := by
    rw [show ((1275913 / 1000000) : ℝ) = ((1000000 / 1275913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12669_neg : (20177733 / 62500000) ≤ -Real.log (724087 / 1000000) ∧
    -Real.log (724087 / 1000000) ≤ (322843729 / 1000000000) := by
  have h := checkLog_sound (w := (275913 / 1724087)) (n := 12)
    (lo := (20177733 / 62500000)) (hi := (322843729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 724087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 724087) = 1/(724087 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12669 : Bounds (-322843729 / 1000000000) (-20177733 / 62500000) (Real.log (724087 / 1000000)) := by
  have h := reflection_log_12669_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12670_neg : (49085717 / 200000000) ≤ -Real.log (1000000 / 1278169) ∧
    -Real.log (1000000 / 1278169) ≤ (122714293 / 500000000) := by
  have h := checkLog_sound (w := (278169 / 2278169)) (n := 12)
    (lo := (49085717 / 200000000)) (hi := (122714293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1278169 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1278169 / 1000000) = 1/(1000000 / 1278169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12670 : Bounds (49085717 / 200000000) (122714293 / 500000000) (Real.log (1278169 / 1000000)) := by
  have h := reflection_log_12670_neg
  have he : Real.log (1278169 / 1000000) = -Real.log (1000000 / 1278169) := by
    rw [show ((1278169 / 1000000) : ℝ) = ((1000000 / 1278169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12671_neg : (325964239 / 1000000000) ≤ -Real.log (721831 / 1000000) ∧
    -Real.log (721831 / 1000000) ≤ (4074553 / 12500000) := by
  have h := checkLog_sound (w := (278169 / 1721831)) (n := 12)
    (lo := (325964239 / 1000000000)) (hi := (4074553 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 721831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 721831) = 1/(721831 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12671 : Bounds (-4074553 / 12500000) (-325964239 / 1000000000) (Real.log (721831 / 1000000)) := by
  have h := reflection_log_12671_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0198 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12672_neg : (40267827 / 500000000) ≤ -Real.log (922622007439 / 1000000000000) ∧
    -Real.log (922622007439 / 1000000000000) ≤ (16107131 / 200000000) := by
  have h := checkLog_sound (w := (77377992561 / 1922622007439)) (n := 12)
    (lo := (40267827 / 500000000)) (hi := (16107131 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 922622007439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 922622007439) = 1/(922622007439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12672 : Bounds (-16107131 / 200000000) (-40267827 / 500000000) (Real.log (922622007439 / 1000000000000)) := by
  have h := reflection_log_12672_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12673_neg : (79181727 / 1000000000) ≤ -Real.log (923872016431 / 1000000000000) ∧
    -Real.log (923872016431 / 1000000000000) ≤ (2474429 / 31250000) := by
  have h := checkLog_sound (w := (76127983569 / 1923872016431)) (n := 12)
    (lo := (79181727 / 1000000000)) (hi := (2474429 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 923872016431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 923872016431) = 1/(923872016431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12673 : Bounds (-2474429 / 31250000) (-79181727 / 1000000000) (Real.log (923872016431 / 1000000000000)) := by
  have h := reflection_log_12673_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12674_neg : (2212913 / 3906250) ≤ -Real.log (31250000000 / 55065594673) ∧
    -Real.log (31250000000 / 55065594673) ≤ (566505729 / 1000000000) := by
  have h := checkLog_sound (w := (23815594673 / 86315594673)) (n := 12)
    (lo := (2212913 / 3906250)) (hi := (566505729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55065594673 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55065594673 / 31250000000) = 1/(31250000000 / 55065594673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12674 : Bounds (2212913 / 3906250) (566505729 / 1000000000) (Real.log (55065594673 / 31250000000)) := by
  have h := reflection_log_12674_neg
  have he : Real.log (55065594673 / 31250000000) = -Real.log (31250000000 / 55065594673) := by
    rw [show ((55065594673 / 31250000000) : ℝ) = ((31250000000 / 55065594673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12675_neg : (71424103 / 125000000) ≤ -Real.log (125000000000 / 221341456657) ∧
    -Real.log (125000000000 / 221341456657) ≤ (22855713 / 40000000) := by
  have h := checkLog_sound (w := (96341456657 / 346341456657)) (n := 12)
    (lo := (71424103 / 125000000)) (hi := (22855713 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((221341456657 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(221341456657 / 125000000000) = 1/(125000000000 / 221341456657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12675 : Bounds (71424103 / 125000000) (22855713 / 40000000) (Real.log (221341456657 / 125000000000)) := by
  have h := reflection_log_12675_neg
  have he : Real.log (221341456657 / 125000000000) = -Real.log (125000000000 / 221341456657) := by
    rw [show ((221341456657 / 125000000000) : ℝ) = ((125000000000 / 221341456657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12676_neg : (1163675881 / 1000000000) ≤ -Real.log (250000000000 / 800420168067) ∧
    -Real.log (250000000000 / 800420168067) ≤ (1163675883 / 1000000000) := by
  have h := checkLog_sound (w := (300420168067 / 1300420168067)) (n := 12)
    (lo := (470528701 / 1000000000)) (hi := (235264351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800420168067 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800420168067 / 500000000000) = 1/(250000000000 / 800420168067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12676 : Bounds (1163675881 / 1000000000) (1163675883 / 1000000000) (Real.log (800420168067 / 250000000000)) := by
  have h := reflection_log_12676_neg
  have he : Real.log (800420168067 / 250000000000) = -Real.log (250000000000 / 800420168067) := by
    rw [show ((800420168067 / 250000000000) : ℝ) = ((250000000000 / 800420168067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12677_neg : (292991229 / 250000000) ≤ -Real.log (500000000000 / 1614164904863) ∧
    -Real.log (500000000000 / 1614164904863) ≤ (585982459 / 500000000) := by
  have h := checkLog_sound (w := (614164904863 / 2614164904863)) (n := 12)
    (lo := (59852217 / 125000000)) (hi := (478817737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1614164904863 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1614164904863 / 1000000000000) = 1/(500000000000 / 1614164904863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12677 : Bounds (292991229 / 250000000) (585982459 / 500000000) (Real.log (1614164904863 / 500000000000)) := by
  have h := reflection_log_12677_neg
  have he : Real.log (1614164904863 / 500000000000) = -Real.log (500000000000 / 1614164904863) := by
    rw [show ((1614164904863 / 500000000000) : ℝ) = ((500000000000 / 1614164904863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12678_neg : (85053547 / 200000000) ≤ -Real.log (100 / 153) ∧
    -Real.log (100 / 153) ≤ (53158467 / 125000000) := by
  have h := checkLog_sound (w := (53 / 253)) (n := 12)
    (lo := (85053547 / 200000000)) (hi := (53158467 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153 / 100) = 1/(100 / 153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12678 : Bounds (85053547 / 200000000) (53158467 / 125000000) (Real.log (153 / 100)) := by
  have h := reflection_log_12678_neg
  have he : Real.log (153 / 100) = -Real.log (100 / 153) := by
    rw [show ((153 / 100) : ℝ) = ((100 / 153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12679_neg : (755022583 / 1000000000) ≤ -Real.log (47 / 100) ∧
    -Real.log (47 / 100) ≤ (151004517 / 200000000) := by
  have h := checkLog_sound (w := (3 / 97)) (n := 12)
    (lo := (61875403 / 1000000000)) (hi := (15468851 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 47) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50 / 47) = 1/(47 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12679 : Bounds (-151004517 / 200000000) (-755022583 / 1000000000) (Real.log (47 / 100)) := by
  have h := reflection_log_12679_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12680_neg : (529859 / 1000000000) ≤ -Real.log (100000 / 100053) ∧
    -Real.log (100000 / 100053) ≤ (26493 / 50000000) := by
  have h := checkLog_sound (w := (53 / 200053)) (n := 12)
    (lo := (529859 / 1000000000)) (hi := (26493 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100053 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100053 / 100000) = 1/(100000 / 100053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12680 : Bounds (529859 / 1000000000) (26493 / 50000000) (Real.log (100053 / 100000)) := by
  have h := reflection_log_12680_neg
  have he : Real.log (100053 / 100000) = -Real.log (100000 / 100053) := by
    rw [show ((100053 / 100000) : ℝ) = ((100000 / 100053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12681_neg : (26507 / 50000000) ≤ -Real.log (99947 / 100000) ∧
    -Real.log (99947 / 100000) ≤ (530141 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 199947)) (n := 12)
    (lo := (26507 / 50000000)) (hi := (530141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99947) = 1/(99947 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12681 : Bounds (-530141 / 1000000000) (-26507 / 50000000) (Real.log (99947 / 100000)) := by
  have h := reflection_log_12681_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12682_neg : (245039671 / 1000000000) ≤ -Real.log (125000 / 159709) ∧
    -Real.log (125000 / 159709) ≤ (30629959 / 125000000) := by
  have h := checkLog_sound (w := (34709 / 284709)) (n := 12)
    (lo := (245039671 / 1000000000)) (hi := (30629959 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159709 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159709 / 125000) = 1/(125000 / 159709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12682 : Bounds (245039671 / 1000000000) (30629959 / 125000000) (Real.log (159709 / 125000)) := by
  have h := reflection_log_12682_neg
  have he : Real.log (159709 / 125000) = -Real.log (125000 / 159709) := by
    rw [show ((159709 / 125000) : ℝ) = ((125000 / 159709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12683_neg : (325275949 / 1000000000) ≤ -Real.log (90291 / 125000) ∧
    -Real.log (90291 / 125000) ≤ (6505519 / 20000000) := by
  have h := checkLog_sound (w := (34709 / 215291)) (n := 12)
    (lo := (325275949 / 1000000000)) (hi := (6505519 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 90291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 90291) = 1/(90291 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12683 : Bounds (-6505519 / 20000000) (-325275949 / 1000000000) (Real.log (90291 / 125000)) := by
  have h := reflection_log_12683_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12684_neg : (123404257 / 500000000) ≤ -Real.log (500000 / 639967) ∧
    -Real.log (500000 / 639967) ≤ (49361703 / 200000000) := by
  have h := checkLog_sound (w := (139967 / 1139967)) (n := 12)
    (lo := (123404257 / 500000000)) (hi := (49361703 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((639967 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(639967 / 500000) = 1/(500000 / 639967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12684 : Bounds (123404257 / 500000000) (49361703 / 200000000) (Real.log (639967 / 500000)) := by
  have h := reflection_log_12684_neg
  have he : Real.log (639967 / 500000) = -Real.log (500000 / 639967) := by
    rw [show ((639967 / 500000) : ℝ) = ((500000 / 639967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12685_neg : (82103101 / 250000000) ≤ -Real.log (360033 / 500000) ∧
    -Real.log (360033 / 500000) ≤ (65682481 / 200000000) := by
  have h := checkLog_sound (w := (139967 / 860033)) (n := 12)
    (lo := (82103101 / 250000000)) (hi := (65682481 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 360033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 360033) = 1/(360033 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12685 : Bounds (-65682481 / 200000000) (-82103101 / 250000000) (Real.log (360033 / 500000)) := by
  have h := reflection_log_12685_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12686_neg : (8160389 / 100000000) ≤ -Real.log (230409238911 / 250000000000) ∧
    -Real.log (230409238911 / 250000000000) ≤ (81603891 / 1000000000) := by
  have h := checkLog_sound (w := (19590761089 / 480409238911)) (n := 12)
    (lo := (8160389 / 100000000)) (hi := (81603891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 230409238911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 230409238911) = 1/(230409238911 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12686 : Bounds (-81603891 / 1000000000) (-8160389 / 100000000) (Real.log (230409238911 / 250000000000)) := by
  have h := reflection_log_12686_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12687_neg : (80236277 / 1000000000) ≤ -Real.log (14420285319 / 15625000000) ∧
    -Real.log (14420285319 / 15625000000) ≤ (40118139 / 500000000) := by
  have h := checkLog_sound (w := (1204714681 / 30045285319)) (n := 12)
    (lo := (80236277 / 1000000000)) (hi := (40118139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14420285319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14420285319) = 1/(14420285319 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12687 : Bounds (-40118139 / 500000000) (-80236277 / 1000000000) (Real.log (14420285319 / 15625000000)) := by
  have h := reflection_log_12687_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12688_neg : (570315621 / 1000000000) ≤ -Real.log (125000000000 / 221103155353) ∧
    -Real.log (125000000000 / 221103155353) ≤ (285157811 / 500000000) := by
  have h := checkLog_sound (w := (96103155353 / 346103155353)) (n := 12)
    (lo := (570315621 / 1000000000)) (hi := (285157811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((221103155353 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(221103155353 / 125000000000) = 1/(125000000000 / 221103155353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12688 : Bounds (570315621 / 1000000000) (285157811 / 500000000) (Real.log (221103155353 / 125000000000)) := by
  have h := reflection_log_12688_neg
  have he : Real.log (221103155353 / 125000000000) = -Real.log (125000000000 / 221103155353) := by
    rw [show ((221103155353 / 125000000000) : ℝ) = ((125000000000 / 221103155353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12689_neg : (287610459 / 500000000) ≤ -Real.log (31250000000 / 55547599109) ∧
    -Real.log (31250000000 / 55547599109) ≤ (575220919 / 1000000000) := by
  have h := checkLog_sound (w := (24297599109 / 86797599109)) (n := 12)
    (lo := (287610459 / 500000000)) (hi := (575220919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55547599109 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55547599109 / 31250000000) = 1/(31250000000 / 55547599109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12689 : Bounds (287610459 / 500000000) (575220919 / 1000000000) (Real.log (55547599109 / 31250000000)) := by
  have h := reflection_log_12689_neg
  have he : Real.log (55547599109 / 31250000000) = -Real.log (31250000000 / 55547599109) := by
    rw [show ((55547599109 / 31250000000) : ℝ) = ((31250000000 / 55547599109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12690_neg : (292991229 / 250000000) ≤ -Real.log (250000000000 / 807082452431) ∧
    -Real.log (250000000000 / 807082452431) ≤ (585982459 / 500000000) := by
  have h := checkLog_sound (w := (307082452431 / 1307082452431)) (n := 12)
    (lo := (59852217 / 125000000)) (hi := (478817737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((807082452431 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(807082452431 / 500000000000) = 1/(250000000000 / 807082452431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12690 : Bounds (292991229 / 250000000) (585982459 / 500000000) (Real.log (807082452431 / 250000000000)) := by
  have h := reflection_log_12690_neg
  have he : Real.log (807082452431 / 250000000000) = -Real.log (250000000000 / 807082452431) := by
    rw [show ((807082452431 / 250000000000) : ℝ) = ((250000000000 / 807082452431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12691_neg : (1180290319 / 1000000000) ≤ -Real.log (500000000000 / 1627659574469) ∧
    -Real.log (500000000000 / 1627659574469) ≤ (1180290321 / 1000000000) := by
  have h := checkLog_sound (w := (627659574469 / 2627659574469)) (n := 12)
    (lo := (487143139 / 1000000000)) (hi := (24357157 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1627659574469 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1627659574469 / 1000000000000) = 1/(500000000000 / 1627659574469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12691 : Bounds (1180290319 / 1000000000) (1180290321 / 1000000000) (Real.log (1627659574469 / 500000000000)) := by
  have h := reflection_log_12691_neg
  have he : Real.log (1627659574469 / 500000000000) = -Real.log (500000000000 / 1627659574469) := by
    rw [show ((1627659574469 / 500000000000) : ℝ) = ((500000000000 / 1627659574469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12692_neg : (427226599 / 1000000000) ≤ -Real.log (1000 / 1533) ∧
    -Real.log (1000 / 1533) ≤ (2136133 / 5000000) := by
  have h := checkLog_sound (w := (533 / 2533)) (n := 12)
    (lo := (427226599 / 1000000000)) (hi := (2136133 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1533 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1533 / 1000) = 1/(1000 / 1533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12692 : Bounds (427226599 / 1000000000) (2136133 / 5000000) (Real.log (1533 / 1000)) := by
  have h := reflection_log_12692_neg
  have he : Real.log (1533 / 1000) = -Real.log (1000 / 1533) := by
    rw [show ((1533 / 1000) : ℝ) = ((1000 / 1533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12693_neg : (38071301 / 50000000) ≤ -Real.log (467 / 1000) ∧
    -Real.log (467 / 1000) ≤ (380713011 / 500000000) := by
  have h := checkLog_sound (w := (33 / 967)) (n := 12)
    (lo := (1706971 / 25000000)) (hi := (68278841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 467) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 467) = 1/(467 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12693 : Bounds (-380713011 / 500000000) (-38071301 / 50000000) (Real.log (467 / 1000)) := by
  have h := reflection_log_12693_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12694_neg : (266429 / 500000000) ≤ -Real.log (1000000 / 1000533) ∧
    -Real.log (1000000 / 1000533) ≤ (532859 / 1000000000) := by
  have h := checkLog_sound (w := (533 / 2000533)) (n := 12)
    (lo := (266429 / 500000000)) (hi := (532859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000533 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000533 / 1000000) = 1/(1000000 / 1000533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12694 : Bounds (266429 / 500000000) (532859 / 1000000000) (Real.log (1000533 / 1000000)) := by
  have h := reflection_log_12694_neg
  have he : Real.log (1000533 / 1000000) = -Real.log (1000000 / 1000533) := by
    rw [show ((1000533 / 1000000) : ℝ) = ((1000000 / 1000533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12695_neg : (266571 / 500000000) ≤ -Real.log (999467 / 1000000) ∧
    -Real.log (999467 / 1000000) ≤ (533143 / 1000000000) := by
  have h := checkLog_sound (w := (533 / 1999467)) (n := 12)
    (lo := (266571 / 500000000)) (hi := (533143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999467) = 1/(999467 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12695 : Bounds (-533143 / 1000000000) (-266571 / 500000000) (Real.log (999467 / 1000000)) := by
  have h := reflection_log_12695_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12696_neg : (123209287 / 500000000) ≤ -Real.log (200000 / 255887) ∧
    -Real.log (200000 / 255887) ≤ (9856743 / 40000000) := by
  have h := checkLog_sound (w := (55887 / 455887)) (n := 12)
    (lo := (123209287 / 500000000)) (hi := (9856743 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((255887 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(255887 / 200000) = 1/(200000 / 255887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12696 : Bounds (123209287 / 500000000) (9856743 / 40000000) (Real.log (255887 / 200000)) := by
  have h := reflection_log_12696_neg
  have he : Real.log (255887 / 200000) = -Real.log (200000 / 255887) := by
    rw [show ((255887 / 200000) : ℝ) = ((200000 / 255887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12697_neg : (81929913 / 250000000) ≤ -Real.log (144113 / 200000) ∧
    -Real.log (144113 / 200000) ≤ (327719653 / 1000000000) := by
  have h := checkLog_sound (w := (55887 / 344113)) (n := 12)
    (lo := (81929913 / 250000000)) (hi := (327719653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 144113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 144113) = 1/(144113 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12697 : Bounds (-327719653 / 1000000000) (-81929913 / 250000000) (Real.log (144113 / 200000)) := by
  have h := reflection_log_12697_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12698_neg : (124094831 / 500000000) ≤ -Real.log (1000000 / 1281703) ∧
    -Real.log (1000000 / 1281703) ≤ (248189663 / 1000000000) := by
  have h := checkLog_sound (w := (281703 / 2281703)) (n := 12)
    (lo := (124094831 / 500000000)) (hi := (248189663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1281703 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1281703 / 1000000) = 1/(1000000 / 1281703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12698 : Bounds (124094831 / 500000000) (248189663 / 1000000000) (Real.log (1281703 / 1000000)) := by
  have h := reflection_log_12698_neg
  have he : Real.log (1281703 / 1000000) = -Real.log (1000000 / 1281703) := by
    rw [show ((1281703 / 1000000) : ℝ) = ((1000000 / 1281703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12699_neg : (165436073 / 500000000) ≤ -Real.log (718297 / 1000000) ∧
    -Real.log (718297 / 1000000) ≤ (330872147 / 1000000000) := by
  have h := checkLog_sound (w := (281703 / 1718297)) (n := 12)
    (lo := (165436073 / 500000000)) (hi := (330872147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 718297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 718297) = 1/(718297 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12699 : Bounds (-330872147 / 1000000000) (-165436073 / 500000000) (Real.log (718297 / 1000000)) := by
  have h := reflection_log_12699_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12700_neg : (20670621 / 250000000) ≤ -Real.log (920643419791 / 1000000000000) ∧
    -Real.log (920643419791 / 1000000000000) ≤ (16536497 / 200000000) := by
  have h := checkLog_sound (w := (79356580209 / 1920643419791)) (n := 12)
    (lo := (20670621 / 250000000)) (hi := (16536497 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 920643419791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 920643419791) = 1/(920643419791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12700 : Bounds (-16536497 / 200000000) (-20670621 / 250000000) (Real.log (920643419791 / 1000000000000)) := by
  have h := reflection_log_12700_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12701_neg : (40650539 / 500000000) ≤ -Real.log (36876643231 / 40000000000) ∧
    -Real.log (36876643231 / 40000000000) ≤ (81301079 / 1000000000) := by
  have h := checkLog_sound (w := (3123356769 / 76876643231)) (n := 12)
    (lo := (40650539 / 500000000)) (hi := (81301079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 36876643231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 36876643231) = 1/(36876643231 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12701 : Bounds (-81301079 / 1000000000) (-40650539 / 500000000) (Real.log (36876643231 / 40000000000)) := by
  have h := reflection_log_12701_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12702_neg : (287069113 / 500000000) ≤ -Real.log (100000000000 / 177559970301) ∧
    -Real.log (100000000000 / 177559970301) ≤ (574138227 / 1000000000) := by
  have h := checkLog_sound (w := (77559970301 / 277559970301)) (n := 12)
    (lo := (287069113 / 500000000)) (hi := (574138227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177559970301 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177559970301 / 100000000000) = 1/(100000000000 / 177559970301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12702 : Bounds (287069113 / 500000000) (574138227 / 1000000000) (Real.log (177559970301 / 100000000000)) := by
  have h := reflection_log_12702_neg
  have he : Real.log (177559970301 / 100000000000) = -Real.log (100000000000 / 177559970301) := by
    rw [show ((177559970301 / 100000000000) : ℝ) = ((100000000000 / 177559970301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12703_neg : (36191363 / 62500000) ≤ -Real.log (500000000000 / 892181785529) ∧
    -Real.log (500000000000 / 892181785529) ≤ (579061809 / 1000000000) := by
  have h := checkLog_sound (w := (392181785529 / 1392181785529)) (n := 12)
    (lo := (36191363 / 62500000)) (hi := (579061809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((892181785529 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(892181785529 / 500000000000) = 1/(500000000000 / 892181785529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12703 : Bounds (36191363 / 62500000) (579061809 / 1000000000) (Real.log (892181785529 / 500000000000)) := by
  have h := reflection_log_12703_neg
  have he : Real.log (892181785529 / 500000000000) = -Real.log (500000000000 / 892181785529) := by
    rw [show ((892181785529 / 500000000000) : ℝ) = ((500000000000 / 892181785529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12704_neg : (1180290319 / 1000000000) ≤ -Real.log (125000000000 / 406914893617) ∧
    -Real.log (125000000000 / 406914893617) ≤ (1180290321 / 1000000000) := by
  have h := checkLog_sound (w := (156914893617 / 656914893617)) (n := 12)
    (lo := (487143139 / 1000000000)) (hi := (24357157 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((406914893617 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(406914893617 / 250000000000) = 1/(125000000000 / 406914893617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12704 : Bounds (1180290319 / 1000000000) (1180290321 / 1000000000) (Real.log (406914893617 / 125000000000)) := by
  have h := reflection_log_12704_neg
  have he : Real.log (406914893617 / 125000000000) = -Real.log (125000000000 / 406914893617) := by
    rw [show ((406914893617 / 125000000000) : ℝ) = ((125000000000 / 406914893617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12705_neg : (59432631 / 50000000) ≤ -Real.log (500000000000 / 1641327623127) ∧
    -Real.log (500000000000 / 1641327623127) ≤ (594326311 / 500000000) := by
  have h := checkLog_sound (w := (641327623127 / 2641327623127)) (n := 12)
    (lo := (3096909 / 6250000)) (hi := (495505441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1641327623127 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1641327623127 / 1000000000000) = 1/(500000000000 / 1641327623127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12705 : Bounds (59432631 / 50000000) (594326311 / 500000000) (Real.log (1641327623127 / 500000000000)) := by
  have h := reflection_log_12705_neg
  have he : Real.log (1641327623127 / 500000000000) = -Real.log (500000000000 / 1641327623127) := by
    rw [show ((1641327623127 / 500000000000) : ℝ) = ((500000000000 / 1641327623127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12706_neg : (214590817 / 500000000) ≤ -Real.log (125 / 192) ∧
    -Real.log (125 / 192) ≤ (85836327 / 200000000) := by
  have h := checkLog_sound (w := (67 / 317)) (n := 12)
    (lo := (214590817 / 500000000)) (hi := (85836327 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((192 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(192 / 125) = 1/(125 / 192) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12706 : Bounds (214590817 / 500000000) (85836327 / 200000000) (Real.log (192 / 125)) := by
  have h := reflection_log_12706_neg
  have he : Real.log (192 / 125) = -Real.log (125 / 192) := by
    rw [show ((192 / 125) : ℝ) = ((125 / 192) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12707_neg : (383935363 / 500000000) ≤ -Real.log (58 / 125) ∧
    -Real.log (58 / 125) ≤ (95983841 / 125000000) := by
  have h := checkLog_sound (w := (9 / 241)) (n := 12)
    (lo := (37361773 / 500000000)) (hi := (74723547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 116) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 116) = 1/(58 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12707 : Bounds (-95983841 / 125000000) (-383935363 / 500000000) (Real.log (58 / 125)) := by
  have h := reflection_log_12707_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12708_neg : (33491 / 62500000) ≤ -Real.log (125000 / 125067) ∧
    -Real.log (125000 / 125067) ≤ (535857 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 250067)) (n := 12)
    (lo := (33491 / 62500000)) (hi := (535857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125067 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125067 / 125000) = 1/(125000 / 125067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12708 : Bounds (33491 / 62500000) (535857 / 1000000000) (Real.log (125067 / 125000)) := by
  have h := reflection_log_12708_neg
  have he : Real.log (125067 / 125000) = -Real.log (125000 / 125067) := by
    rw [show ((125067 / 125000) : ℝ) = ((125000 / 125067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12709_neg : (536143 / 1000000000) ≤ -Real.log (124933 / 125000) ∧
    -Real.log (124933 / 125000) ≤ (33509 / 62500000) := by
  have h := checkLog_sound (w := (67 / 249933)) (n := 12)
    (lo := (536143 / 1000000000)) (hi := (33509 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124933) = 1/(124933 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12709 : Bounds (-33509 / 62500000) (-536143 / 1000000000) (Real.log (124933 / 125000)) := by
  have h := reflection_log_12709_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12710_neg : (247797919 / 1000000000) ≤ -Real.log (1000000 / 1281201) ∧
    -Real.log (1000000 / 1281201) ≤ (1548737 / 6250000) := by
  have h := checkLog_sound (w := (281201 / 2281201)) (n := 12)
    (lo := (247797919 / 1000000000)) (hi := (1548737 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1281201 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1281201 / 1000000) = 1/(1000000 / 1281201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12710 : Bounds (247797919 / 1000000000) (1548737 / 6250000) (Real.log (1281201 / 1000000)) := by
  have h := reflection_log_12710_neg
  have he : Real.log (1281201 / 1000000) = -Real.log (1000000 / 1281201) := by
    rw [show ((1281201 / 1000000) : ℝ) = ((1000000 / 1281201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12711_neg : (66034703 / 200000000) ≤ -Real.log (718799 / 1000000) ∧
    -Real.log (718799 / 1000000) ≤ (82543379 / 250000000) := by
  have h := checkLog_sound (w := (281201 / 1718799)) (n := 12)
    (lo := (66034703 / 200000000)) (hi := (82543379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 718799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 718799) = 1/(718799 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12711 : Bounds (-82543379 / 250000000) (-66034703 / 200000000) (Real.log (718799 / 1000000)) := by
  have h := reflection_log_12711_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12712_neg : (249571243 / 1000000000) ≤ -Real.log (40000 / 51339) ∧
    -Real.log (40000 / 51339) ≤ (62392811 / 250000000) := by
  have h := checkLog_sound (w := (11339 / 91339)) (n := 12)
    (lo := (249571243 / 1000000000)) (hi := (62392811 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51339 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51339 / 40000) = 1/(40000 / 51339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12712 : Bounds (249571243 / 1000000000) (62392811 / 250000000) (Real.log (51339 / 40000)) := by
  have h := reflection_log_12712_neg
  have he : Real.log (51339 / 40000) = -Real.log (40000 / 51339) := by
    rw [show ((51339 / 40000) : ℝ) = ((40000 / 51339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12713_neg : (16667107 / 50000000) ≤ -Real.log (28661 / 40000) ∧
    -Real.log (28661 / 40000) ≤ (333342141 / 1000000000) := by
  have h := checkLog_sound (w := (11339 / 68661)) (n := 12)
    (lo := (16667107 / 50000000)) (hi := (333342141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 28661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 28661) = 1/(28661 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12713 : Bounds (-333342141 / 1000000000) (-16667107 / 50000000) (Real.log (28661 / 40000)) := by
  have h := reflection_log_12713_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12714_neg : (83770897 / 1000000000) ≤ -Real.log (1471427079 / 1600000000) ∧
    -Real.log (1471427079 / 1600000000) ≤ (41885449 / 500000000) := by
  have h := checkLog_sound (w := (128572921 / 3071427079)) (n := 12)
    (lo := (83770897 / 1000000000)) (hi := (41885449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1471427079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1471427079) = 1/(1471427079 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12714 : Bounds (-41885449 / 500000000) (-83770897 / 1000000000) (Real.log (1471427079 / 1600000000)) := by
  have h := reflection_log_12714_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12715_neg : (20593899 / 250000000) ≤ -Real.log (920925997599 / 1000000000000) ∧
    -Real.log (920925997599 / 1000000000000) ≤ (82375597 / 1000000000) := by
  have h := checkLog_sound (w := (79074002401 / 1920925997599)) (n := 12)
    (lo := (20593899 / 250000000)) (hi := (82375597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 920925997599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 920925997599) = 1/(920925997599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12715 : Bounds (-82375597 / 1000000000) (-20593899 / 250000000) (Real.log (920925997599 / 1000000000000)) := by
  have h := reflection_log_12715_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12716_neg : (288985717 / 500000000) ≤ -Real.log (50000000000 / 89120950363) ∧
    -Real.log (50000000000 / 89120950363) ≤ (115594287 / 200000000) := by
  have h := checkLog_sound (w := (39120950363 / 139120950363)) (n := 12)
    (lo := (288985717 / 500000000)) (hi := (115594287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89120950363 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89120950363 / 50000000000) = 1/(50000000000 / 89120950363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12716 : Bounds (288985717 / 500000000) (115594287 / 200000000) (Real.log (89120950363 / 50000000000)) := by
  have h := reflection_log_12716_neg
  have he : Real.log (89120950363 / 50000000000) = -Real.log (50000000000 / 89120950363) := by
    rw [show ((89120950363 / 50000000000) : ℝ) = ((50000000000 / 89120950363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12717_neg : (582913383 / 1000000000) ≤ -Real.log (250000000000 / 447812358257) ∧
    -Real.log (250000000000 / 447812358257) ≤ (72864173 / 125000000) := by
  have h := checkLog_sound (w := (197812358257 / 697812358257)) (n := 12)
    (lo := (582913383 / 1000000000)) (hi := (72864173 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((447812358257 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(447812358257 / 250000000000) = 1/(250000000000 / 447812358257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12717 : Bounds (582913383 / 1000000000) (72864173 / 125000000) (Real.log (447812358257 / 250000000000)) := by
  have h := reflection_log_12717_neg
  have he : Real.log (447812358257 / 250000000000) = -Real.log (250000000000 / 447812358257) := by
    rw [show ((447812358257 / 250000000000) : ℝ) = ((250000000000 / 447812358257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12718_neg : (59432631 / 50000000) ≤ -Real.log (250000000000 / 820663811563) ∧
    -Real.log (250000000000 / 820663811563) ≤ (594326311 / 500000000) := by
  have h := checkLog_sound (w := (320663811563 / 1320663811563)) (n := 12)
    (lo := (3096909 / 6250000)) (hi := (495505441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((820663811563 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(820663811563 / 500000000000) = 1/(250000000000 / 820663811563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12718 : Bounds (59432631 / 50000000) (594326311 / 500000000) (Real.log (820663811563 / 250000000000)) := by
  have h := reflection_log_12718_neg
  have he : Real.log (820663811563 / 250000000000) = -Real.log (250000000000 / 820663811563) := by
    rw [show ((820663811563 / 250000000000) : ℝ) = ((250000000000 / 820663811563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12719_neg : (29926309 / 25000000) ≤ -Real.log (250000000000 / 827586206897) ∧
    -Real.log (250000000000 / 827586206897) ≤ (598526181 / 500000000) := by
  have h := checkLog_sound (w := (327586206897 / 1327586206897)) (n := 12)
    (lo := (25195259 / 50000000)) (hi := (503905181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((827586206897 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(827586206897 / 500000000000) = 1/(250000000000 / 827586206897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12719 : Bounds (29926309 / 25000000) (598526181 / 500000000) (Real.log (827586206897 / 250000000000)) := by
  have h := reflection_log_12719_neg
  have he : Real.log (827586206897 / 250000000000) = -Real.log (250000000000 / 827586206897) := by
    rw [show ((827586206897 / 250000000000) : ℝ) = ((250000000000 / 827586206897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12720_neg : (215566427 / 500000000) ≤ -Real.log (1000 / 1539) ∧
    -Real.log (1000 / 1539) ≤ (86226571 / 200000000) := by
  have h := checkLog_sound (w := (539 / 2539)) (n := 12)
    (lo := (215566427 / 500000000)) (hi := (86226571 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1539 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1539 / 1000) = 1/(1000 / 1539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12720 : Bounds (215566427 / 500000000) (86226571 / 200000000) (Real.log (1539 / 1000)) := by
  have h := reflection_log_12720_neg
  have he : Real.log (1539 / 1000) = -Real.log (1000 / 1539) := by
    rw [show ((1539 / 1000) : ℝ) = ((1000 / 1539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12721_neg : (154871447 / 200000000) ≤ -Real.log (461 / 1000) ∧
    -Real.log (461 / 1000) ≤ (774357237 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 961)) (n := 12)
    (lo := (16242011 / 200000000)) (hi := (10151257 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 461) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 461) = 1/(461 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12721 : Bounds (-774357237 / 1000000000) (-154871447 / 200000000) (Real.log (461 / 1000)) := by
  have h := reflection_log_12721_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12722_neg : (269427 / 500000000) ≤ -Real.log (1000000 / 1000539) ∧
    -Real.log (1000000 / 1000539) ≤ (107771 / 200000000) := by
  have h := checkLog_sound (w := (539 / 2000539)) (n := 12)
    (lo := (269427 / 500000000)) (hi := (107771 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000539 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000539 / 1000000) = 1/(1000000 / 1000539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12722 : Bounds (269427 / 500000000) (107771 / 200000000) (Real.log (1000539 / 1000000)) := by
  have h := reflection_log_12722_neg
  have he : Real.log (1000539 / 1000000) = -Real.log (1000000 / 1000539) := by
    rw [show ((1000539 / 1000000) : ℝ) = ((1000000 / 1000539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12723_neg : (107829 / 200000000) ≤ -Real.log (999461 / 1000000) ∧
    -Real.log (999461 / 1000000) ≤ (269573 / 500000000) := by
  have h := checkLog_sound (w := (539 / 1999461)) (n := 12)
    (lo := (107829 / 200000000)) (hi := (269573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999461) = 1/(999461 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12723 : Bounds (-269573 / 500000000) (-107829 / 200000000) (Real.log (999461 / 1000000)) := by
  have h := reflection_log_12723_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12724_neg : (124589241 / 500000000) ≤ -Real.log (1000000 / 1282971) ∧
    -Real.log (1000000 / 1282971) ≤ (249178483 / 1000000000) := by
  have h := checkLog_sound (w := (282971 / 2282971)) (n := 12)
    (lo := (124589241 / 500000000)) (hi := (249178483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1282971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1282971 / 1000000) = 1/(1000000 / 1282971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12724 : Bounds (124589241 / 500000000) (249178483 / 1000000000) (Real.log (1282971 / 1000000)) := by
  have h := reflection_log_12724_neg
  have he : Real.log (1282971 / 1000000) = -Real.log (1000000 / 1282971) := by
    rw [show ((1282971 / 1000000) : ℝ) = ((1000000 / 1282971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12725_neg : (20789937 / 62500000) ≤ -Real.log (717029 / 1000000) ∧
    -Real.log (717029 / 1000000) ≤ (332638993 / 1000000000) := by
  have h := checkLog_sound (w := (282971 / 1717029)) (n := 12)
    (lo := (20789937 / 62500000)) (hi := (332638993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 717029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 717029) = 1/(717029 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12725 : Bounds (-332638993 / 1000000000) (-20789937 / 62500000) (Real.log (717029 / 1000000)) := by
  have h := reflection_log_12725_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12726_neg : (25095403 / 100000000) ≤ -Real.log (1000000 / 1285251) ∧
    -Real.log (1000000 / 1285251) ≤ (250954031 / 1000000000) := by
  have h := checkLog_sound (w := (285251 / 2285251)) (n := 12)
    (lo := (25095403 / 100000000)) (hi := (250954031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1285251 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1285251 / 1000000) = 1/(1000000 / 1285251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12726 : Bounds (25095403 / 100000000) (250954031 / 1000000000) (Real.log (1285251 / 1000000)) := by
  have h := reflection_log_12726_neg
  have he : Real.log (1285251 / 1000000) = -Real.log (1000000 / 1285251) := by
    rw [show ((1285251 / 1000000) : ℝ) = ((1000000 / 1285251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12727_neg : (167911923 / 500000000) ≤ -Real.log (714749 / 1000000) ∧
    -Real.log (714749 / 1000000) ≤ (335823847 / 1000000000) := by
  have h := checkLog_sound (w := (285251 / 1714749)) (n := 12)
    (lo := (167911923 / 500000000)) (hi := (335823847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 714749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 714749) = 1/(714749 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12727 : Bounds (-335823847 / 1000000000) (-167911923 / 500000000) (Real.log (714749 / 1000000)) := by
  have h := reflection_log_12727_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12728_neg : (10608727 / 125000000) ≤ -Real.log (918631866999 / 1000000000000) ∧
    -Real.log (918631866999 / 1000000000000) ≤ (84869817 / 1000000000) := by
  have h := checkLog_sound (w := (81368133001 / 1918631866999)) (n := 12)
    (lo := (10608727 / 125000000)) (hi := (84869817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 918631866999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 918631866999) = 1/(918631866999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12728 : Bounds (-84869817 / 1000000000) (-10608727 / 125000000) (Real.log (918631866999 / 1000000000000)) := by
  have h := reflection_log_12728_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12729_neg : (8346051 / 100000000) ≤ -Real.log (919927413159 / 1000000000000) ∧
    -Real.log (919927413159 / 1000000000000) ≤ (83460511 / 1000000000) := by
  have h := checkLog_sound (w := (80072586841 / 1919927413159)) (n := 12)
    (lo := (8346051 / 100000000)) (hi := (83460511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 919927413159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 919927413159) = 1/(919927413159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12729 : Bounds (-83460511 / 1000000000) (-8346051 / 100000000) (Real.log (919927413159 / 1000000000000)) := by
  have h := reflection_log_12729_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12730_neg : (23272699 / 40000000) ≤ -Real.log (100000000000 / 178928746257) ∧
    -Real.log (100000000000 / 178928746257) ≤ (145454369 / 250000000) := by
  have h := checkLog_sound (w := (78928746257 / 278928746257)) (n := 12)
    (lo := (23272699 / 40000000)) (hi := (145454369 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178928746257 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178928746257 / 100000000000) = 1/(100000000000 / 178928746257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12730 : Bounds (23272699 / 40000000) (145454369 / 250000000) (Real.log (178928746257 / 100000000000)) := by
  have h := reflection_log_12730_neg
  have he : Real.log (178928746257 / 100000000000) = -Real.log (100000000000 / 178928746257) := by
    rw [show ((178928746257 / 100000000000) : ℝ) = ((100000000000 / 178928746257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12731_neg : (146694469 / 250000000) ≤ -Real.log (500000000000 / 899092548573) ∧
    -Real.log (500000000000 / 899092548573) ≤ (586777877 / 1000000000) := by
  have h := checkLog_sound (w := (399092548573 / 1399092548573)) (n := 12)
    (lo := (146694469 / 250000000)) (hi := (586777877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((899092548573 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(899092548573 / 500000000000) = 1/(500000000000 / 899092548573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12731 : Bounds (146694469 / 250000000) (586777877 / 1000000000) (Real.log (899092548573 / 500000000000)) := by
  have h := reflection_log_12731_neg
  have he : Real.log (899092548573 / 500000000000) = -Real.log (500000000000 / 899092548573) := by
    rw [show ((899092548573 / 500000000000) : ℝ) = ((500000000000 / 899092548573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12732_neg : (29926309 / 25000000) ≤ -Real.log (500000000000 / 1655172413793) ∧
    -Real.log (500000000000 / 1655172413793) ≤ (598526181 / 500000000) := by
  have h := checkLog_sound (w := (655172413793 / 2655172413793)) (n := 12)
    (lo := (25195259 / 50000000)) (hi := (503905181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1655172413793 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1655172413793 / 1000000000000) = 1/(500000000000 / 1655172413793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12732 : Bounds (29926309 / 25000000) (598526181 / 500000000) (Real.log (1655172413793 / 500000000000)) := by
  have h := reflection_log_12732_neg
  have he : Real.log (1655172413793 / 500000000000) = -Real.log (500000000000 / 1655172413793) := by
    rw [show ((1655172413793 / 500000000000) : ℝ) = ((500000000000 / 1655172413793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12733_neg : (120549009 / 100000000) ≤ -Real.log (125000000000 / 417299349241) ∧
    -Real.log (125000000000 / 417299349241) ≤ (301372523 / 250000000) := by
  have h := checkLog_sound (w := (167299349241 / 667299349241)) (n := 12)
    (lo := (51234291 / 100000000)) (hi := (512342911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((417299349241 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(417299349241 / 250000000000) = 1/(125000000000 / 417299349241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12733 : Bounds (120549009 / 100000000) (301372523 / 250000000) (Real.log (417299349241 / 125000000000)) := by
  have h := reflection_log_12733_neg
  have he : Real.log (417299349241 / 125000000000) = -Real.log (125000000000 / 417299349241) := by
    rw [show ((417299349241 / 125000000000) : ℝ) = ((125000000000 / 417299349241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12734_neg : (17323211 / 40000000) ≤ -Real.log (500 / 771) ∧
    -Real.log (500 / 771) ≤ (108270069 / 250000000) := by
  have h := checkLog_sound (w := (271 / 1271)) (n := 12)
    (lo := (17323211 / 40000000)) (hi := (108270069 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((771 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(771 / 500) = 1/(500 / 771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12734 : Bounds (17323211 / 40000000) (108270069 / 250000000) (Real.log (771 / 500)) := by
  have h := reflection_log_12734_neg
  have he : Real.log (771 / 500) = -Real.log (500 / 771) := by
    rw [show ((771 / 500) : ℝ) = ((500 / 771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12735_neg : (390443047 / 500000000) ≤ -Real.log (229 / 500) ∧
    -Real.log (229 / 500) ≤ (48805381 / 62500000) := by
  have h := checkLog_sound (w := (21 / 479)) (n := 12)
    (lo := (43869457 / 500000000)) (hi := (17547783 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 229) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 229) = 1/(229 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12735 : Bounds (-48805381 / 62500000) (-390443047 / 500000000) (Real.log (229 / 500)) := by
  have h := reflection_log_12735_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


