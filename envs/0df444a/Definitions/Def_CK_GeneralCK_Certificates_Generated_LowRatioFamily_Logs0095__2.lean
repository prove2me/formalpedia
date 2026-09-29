-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0095__2
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0095__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T02:13:07.620905+00:00
-- url     : https://prove2.me/theorems/efba6aae-5bbd-4960-bf0b-cf3ad7c8880a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0095 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0096)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0095 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0096)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0095 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0096)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0095 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0096) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0095 (+1 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0096).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0095 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6080_neg : (93134177 / 1000000000) ≤ -Real.log (1000000 / 1097609) ∧
    -Real.log (1000000 / 1097609) ≤ (46567089 / 500000000) := by
  have h := checkLog_sound (w := (97609 / 2097609)) (n := 12)
    (lo := (93134177 / 1000000000)) (hi := (46567089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097609 / 1000000) = 1/(1000000 / 1097609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6080 : Bounds (93134177 / 1000000000) (46567089 / 500000000) (Real.log (1097609 / 1000000)) := by
  have h := reflection_log_6080_neg
  have he : Real.log (1097609 / 1000000) = -Real.log (1000000 / 1097609) := by
    rw [show ((1097609 / 1000000) : ℝ) = ((1000000 / 1097609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6081_neg : (102707371 / 1000000000) ≤ -Real.log (902391 / 1000000) ∧
    -Real.log (902391 / 1000000) ≤ (25676843 / 250000000) := by
  have h := checkLog_sound (w := (97609 / 1902391)) (n := 12)
    (lo := (102707371 / 1000000000)) (hi := (25676843 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902391) = 1/(902391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6081 : Bounds (-25676843 / 250000000) (-102707371 / 1000000000) (Real.log (902391 / 1000000)) := by
  have h := reflection_log_6081_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6082_neg : (4786597 / 500000000) ≤ -Real.log (990472483119 / 1000000000000) ∧
    -Real.log (990472483119 / 1000000000000) ≤ (1914639 / 200000000) := by
  have h := checkLog_sound (w := (9527516881 / 1990472483119)) (n := 12)
    (lo := (4786597 / 500000000)) (hi := (1914639 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990472483119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990472483119) = 1/(990472483119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6082 : Bounds (-1914639 / 200000000) (-4786597 / 500000000) (Real.log (990472483119 / 1000000000000)) := by
  have h := reflection_log_6082_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6083_neg : (9525163 / 1000000000) ≤ -Real.log (39620802271 / 40000000000) ∧
    -Real.log (39620802271 / 40000000000) ≤ (2381291 / 250000000) := by
  have h := checkLog_sound (w := (379197729 / 79620802271)) (n := 12)
    (lo := (9525163 / 1000000000)) (hi := (2381291 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39620802271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39620802271) = 1/(39620802271 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6083 : Bounds (-2381291 / 250000000) (-9525163 / 1000000000) (Real.log (39620802271 / 40000000000)) := by
  have h := reflection_log_6083_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6084_neg : (195348867 / 1000000000) ≤ -Real.log (500000000000 / 607867521201) ∧
    -Real.log (500000000000 / 607867521201) ≤ (48837217 / 250000000) := by
  have h := checkLog_sound (w := (107867521201 / 1107867521201)) (n := 12)
    (lo := (195348867 / 1000000000)) (hi := (48837217 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607867521201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607867521201 / 500000000000) = 1/(500000000000 / 607867521201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6084 : Bounds (195348867 / 1000000000) (48837217 / 250000000) (Real.log (607867521201 / 500000000000)) := by
  have h := reflection_log_6084_neg
  have he : Real.log (607867521201 / 500000000000) = -Real.log (500000000000 / 607867521201) := by
    rw [show ((607867521201 / 500000000000) : ℝ) = ((500000000000 / 607867521201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6085_neg : (195841549 / 1000000000) ≤ -Real.log (62500000000 / 76020885071) ∧
    -Real.log (62500000000 / 76020885071) ≤ (3916831 / 20000000) := by
  have h := checkLog_sound (w := (13520885071 / 138520885071)) (n := 12)
    (lo := (195841549 / 1000000000)) (hi := (3916831 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76020885071 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76020885071 / 62500000000) = 1/(62500000000 / 76020885071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6085 : Bounds (195841549 / 1000000000) (3916831 / 20000000) (Real.log (76020885071 / 62500000000)) := by
  have h := reflection_log_6085_neg
  have he : Real.log (76020885071 / 62500000000) = -Real.log (62500000000 / 76020885071) := by
    rw [show ((76020885071 / 62500000000) : ℝ) = ((62500000000 / 76020885071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6086_neg : (98037333 / 250000000) ≤ -Real.log (500000000000 / 740079365079) ∧
    -Real.log (500000000000 / 740079365079) ≤ (392149333 / 1000000000) := by
  have h := checkLog_sound (w := (240079365079 / 1240079365079)) (n := 12)
    (lo := (98037333 / 250000000)) (hi := (392149333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((740079365079 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(740079365079 / 500000000000) = 1/(500000000000 / 740079365079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6086 : Bounds (98037333 / 250000000) (392149333 / 1000000000) (Real.log (740079365079 / 500000000000)) := by
  have h := reflection_log_6086_neg
  have he : Real.log (740079365079 / 500000000000) = -Real.log (500000000000 / 740079365079) := by
    rw [show ((740079365079 / 500000000000) : ℝ) = ((500000000000 / 740079365079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6087_neg : (98089281 / 250000000) ≤ -Real.log (100000000000 / 148046632767) ∧
    -Real.log (100000000000 / 148046632767) ≤ (3138857 / 8000000) := by
  have h := checkLog_sound (w := (48046632767 / 248046632767)) (n := 12)
    (lo := (98089281 / 250000000)) (hi := (3138857 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148046632767 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148046632767 / 100000000000) = 1/(100000000000 / 148046632767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6087 : Bounds (98089281 / 250000000) (3138857 / 8000000) (Real.log (148046632767 / 100000000000)) := by
  have h := reflection_log_6087_neg
  have he : Real.log (148046632767 / 100000000000) = -Real.log (100000000000 / 148046632767) := by
    rw [show ((148046632767 / 100000000000) : ℝ) = ((100000000000 / 148046632767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6088_neg : (22142687 / 125000000) ≤ -Real.log (5000 / 5969) ∧
    -Real.log (5000 / 5969) ≤ (177141497 / 1000000000) := by
  have h := checkLog_sound (w := (969 / 10969)) (n := 12)
    (lo := (22142687 / 125000000)) (hi := (177141497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5969 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5969 / 5000) = 1/(5000 / 5969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6088 : Bounds (22142687 / 125000000) (177141497 / 1000000000) (Real.log (5969 / 5000)) := by
  have h := reflection_log_6088_neg
  have he : Real.log (5969 / 5000) = -Real.log (5000 / 5969) := by
    rw [show ((5969 / 5000) : ℝ) = ((5000 / 5969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6089_neg : (53855857 / 250000000) ≤ -Real.log (4031 / 5000) ∧
    -Real.log (4031 / 5000) ≤ (215423429 / 1000000000) := by
  have h := checkLog_sound (w := (969 / 9031)) (n := 12)
    (lo := (53855857 / 250000000)) (hi := (215423429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4031) = 1/(4031 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6089 : Bounds (-215423429 / 1000000000) (-53855857 / 250000000) (Real.log (4031 / 5000)) := by
  have h := reflection_log_6089_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6090_neg : (193781 / 1000000000) ≤ -Real.log (5000000 / 5000969) ∧
    -Real.log (5000000 / 5000969) ≤ (96891 / 500000000) := by
  have h := checkLog_sound (w := (969 / 10000969)) (n := 12)
    (lo := (193781 / 1000000000)) (hi := (96891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000969 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000969 / 5000000) = 1/(5000000 / 5000969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6090 : Bounds (193781 / 1000000000) (96891 / 500000000) (Real.log (5000969 / 5000000)) := by
  have h := reflection_log_6090_neg
  have he : Real.log (5000969 / 5000000) = -Real.log (5000000 / 5000969) := by
    rw [show ((5000969 / 5000000) : ℝ) = ((5000000 / 5000969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6091_neg : (96909 / 500000000) ≤ -Real.log (4999031 / 5000000) ∧
    -Real.log (4999031 / 5000000) ≤ (193819 / 1000000000) := by
  have h := checkLog_sound (w := (969 / 9999031)) (n := 12)
    (lo := (96909 / 500000000)) (hi := (193819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999031) = 1/(4999031 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6091 : Bounds (-193819 / 1000000000) (-96909 / 500000000) (Real.log (4999031 / 5000000)) := by
  have h := reflection_log_6091_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6092_neg : (3718333 / 40000000) ≤ -Real.log (125000 / 137177) ∧
    -Real.log (125000 / 137177) ≤ (46479163 / 500000000) := by
  have h := checkLog_sound (w := (12177 / 262177)) (n := 12)
    (lo := (3718333 / 40000000)) (hi := (46479163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137177 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137177 / 125000) = 1/(125000 / 137177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6092 : Bounds (3718333 / 40000000) (46479163 / 500000000) (Real.log (137177 / 125000)) := by
  have h := reflection_log_6092_neg
  have he : Real.log (137177 / 125000) = -Real.log (125000 / 137177) := by
    rw [show ((137177 / 125000) : ℝ) = ((125000 / 137177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6093_neg : (51246759 / 500000000) ≤ -Real.log (112823 / 125000) ∧
    -Real.log (112823 / 125000) ≤ (102493519 / 1000000000) := by
  have h := checkLog_sound (w := (12177 / 237823)) (n := 12)
    (lo := (51246759 / 500000000)) (hi := (102493519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 112823) = 1/(112823 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6093 : Bounds (-102493519 / 1000000000) (-51246759 / 500000000) (Real.log (112823 / 125000)) := by
  have h := reflection_log_6093_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6094_neg : (93180641 / 1000000000) ≤ -Real.log (50000 / 54883) ∧
    -Real.log (50000 / 54883) ≤ (46590321 / 500000000) := by
  have h := checkLog_sound (w := (4883 / 104883)) (n := 12)
    (lo := (93180641 / 1000000000)) (hi := (46590321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54883 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54883 / 50000) = 1/(50000 / 54883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6094 : Bounds (93180641 / 1000000000) (46590321 / 500000000) (Real.log (54883 / 50000)) := by
  have h := reflection_log_6094_neg
  have he : Real.log (54883 / 50000) = -Real.log (50000 / 54883) := by
    rw [show ((54883 / 50000) : ℝ) = ((50000 / 54883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6095_neg : (102763889 / 1000000000) ≤ -Real.log (45117 / 50000) ∧
    -Real.log (45117 / 50000) ≤ (10276389 / 100000000) := by
  have h := checkLog_sound (w := (4883 / 95117)) (n := 12)
    (lo := (102763889 / 1000000000)) (hi := (10276389 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45117) = 1/(45117 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6095 : Bounds (-10276389 / 100000000) (-102763889 / 1000000000) (Real.log (45117 / 50000)) := by
  have h := reflection_log_6095_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6096_neg : (598953 / 62500000) ≤ -Real.log (2476156311 / 2500000000) ∧
    -Real.log (2476156311 / 2500000000) ≤ (9583249 / 1000000000) := by
  have h := checkLog_sound (w := (23843689 / 4976156311)) (n := 12)
    (lo := (598953 / 62500000)) (hi := (9583249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2476156311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2476156311) = 1/(2476156311 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6096 : Bounds (-9583249 / 1000000000) (-598953 / 62500000) (Real.log (2476156311 / 2500000000)) := by
  have h := reflection_log_6096_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6097_neg : (1191899 / 125000000) ≤ -Real.log (15476720671 / 15625000000) ∧
    -Real.log (15476720671 / 15625000000) ≤ (9535193 / 1000000000) := by
  have h := checkLog_sound (w := (148279329 / 31101720671)) (n := 12)
    (lo := (1191899 / 125000000)) (hi := (9535193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15476720671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15476720671) = 1/(15476720671 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6097 : Bounds (-9535193 / 1000000000) (-1191899 / 125000000) (Real.log (15476720671 / 15625000000)) := by
  have h := reflection_log_6097_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6098_neg : (195451843 / 1000000000) ≤ -Real.log (500000000000 / 607930120631) ∧
    -Real.log (500000000000 / 607930120631) ≤ (48862961 / 250000000) := by
  have h := checkLog_sound (w := (107930120631 / 1107930120631)) (n := 12)
    (lo := (195451843 / 1000000000)) (hi := (48862961 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607930120631 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607930120631 / 500000000000) = 1/(500000000000 / 607930120631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6098 : Bounds (195451843 / 1000000000) (48862961 / 250000000) (Real.log (607930120631 / 500000000000)) := by
  have h := reflection_log_6098_neg
  have he : Real.log (607930120631 / 500000000000) = -Real.log (500000000000 / 607930120631) := by
    rw [show ((607930120631 / 500000000000) : ℝ) = ((500000000000 / 607930120631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6099_neg : (195944531 / 1000000000) ≤ -Real.log (7812500000 / 9503589279) ∧
    -Real.log (7812500000 / 9503589279) ≤ (48986133 / 250000000) := by
  have h := checkLog_sound (w := (1691089279 / 17316089279)) (n := 12)
    (lo := (195944531 / 1000000000)) (hi := (48986133 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9503589279 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9503589279 / 7812500000) = 1/(7812500000 / 9503589279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6099 : Bounds (195944531 / 1000000000) (48986133 / 250000000) (Real.log (9503589279 / 7812500000)) := by
  have h := reflection_log_6099_neg
  have he : Real.log (9503589279 / 7812500000) = -Real.log (7812500000 / 9503589279) := by
    rw [show ((9503589279 / 7812500000) : ℝ) = ((7812500000 / 9503589279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6100_neg : (98089281 / 250000000) ≤ -Real.log (250000000000 / 370116581917) ∧
    -Real.log (250000000000 / 370116581917) ≤ (3138857 / 8000000) := by
  have h := checkLog_sound (w := (120116581917 / 620116581917)) (n := 12)
    (lo := (98089281 / 250000000)) (hi := (3138857 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((370116581917 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(370116581917 / 250000000000) = 1/(250000000000 / 370116581917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6100 : Bounds (98089281 / 250000000) (3138857 / 8000000) (Real.log (370116581917 / 250000000000)) := by
  have h := reflection_log_6100_neg
  have he : Real.log (370116581917 / 250000000000) = -Real.log (250000000000 / 370116581917) := by
    rw [show ((370116581917 / 250000000000) : ℝ) = ((250000000000 / 370116581917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6101_neg : (15702597 / 40000000) ≤ -Real.log (100000000000 / 148077400149) ∧
    -Real.log (100000000000 / 148077400149) ≤ (196282463 / 500000000) := by
  have h := checkLog_sound (w := (48077400149 / 248077400149)) (n := 12)
    (lo := (15702597 / 40000000)) (hi := (196282463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148077400149 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148077400149 / 100000000000) = 1/(100000000000 / 148077400149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6101 : Bounds (15702597 / 40000000) (196282463 / 500000000) (Real.log (148077400149 / 100000000000)) := by
  have h := reflection_log_6101_neg
  have he : Real.log (148077400149 / 100000000000) = -Real.log (100000000000 / 148077400149) := by
    rw [show ((148077400149 / 100000000000) : ℝ) = ((100000000000 / 148077400149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6102_neg : (177225259 / 1000000000) ≤ -Real.log (10000 / 11939) ∧
    -Real.log (10000 / 11939) ≤ (8861263 / 50000000) := by
  have h := checkLog_sound (w := (1939 / 21939)) (n := 12)
    (lo := (177225259 / 1000000000)) (hi := (8861263 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11939 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11939 / 10000) = 1/(10000 / 11939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6102 : Bounds (177225259 / 1000000000) (8861263 / 50000000) (Real.log (11939 / 10000)) := by
  have h := reflection_log_6102_neg
  have he : Real.log (11939 / 10000) = -Real.log (10000 / 11939) := by
    rw [show ((11939 / 10000) : ℝ) = ((10000 / 11939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6103_neg : (107773737 / 500000000) ≤ -Real.log (8061 / 10000) ∧
    -Real.log (8061 / 10000) ≤ (8621899 / 40000000) := by
  have h := checkLog_sound (w := (1939 / 18061)) (n := 12)
    (lo := (107773737 / 500000000)) (hi := (8621899 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8061) = 1/(8061 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6103 : Bounds (-8621899 / 40000000) (-107773737 / 500000000) (Real.log (8061 / 10000)) := by
  have h := reflection_log_6103_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6104_neg : (193881 / 1000000000) ≤ -Real.log (10000000 / 10001939) ∧
    -Real.log (10000000 / 10001939) ≤ (96941 / 500000000) := by
  have h := checkLog_sound (w := (1939 / 20001939)) (n := 12)
    (lo := (193881 / 1000000000)) (hi := (96941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001939 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001939 / 10000000) = 1/(10000000 / 10001939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6104 : Bounds (193881 / 1000000000) (96941 / 500000000) (Real.log (10001939 / 10000000)) := by
  have h := reflection_log_6104_neg
  have he : Real.log (10001939 / 10000000) = -Real.log (10000000 / 10001939) := by
    rw [show ((10001939 / 10000000) : ℝ) = ((10000000 / 10001939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6105_neg : (96959 / 500000000) ≤ -Real.log (9998061 / 10000000) ∧
    -Real.log (9998061 / 10000000) ≤ (193919 / 1000000000) := by
  have h := checkLog_sound (w := (1939 / 19998061)) (n := 12)
    (lo := (96959 / 500000000)) (hi := (193919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998061) = 1/(9998061 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6105 : Bounds (-193919 / 1000000000) (-96959 / 500000000) (Real.log (9998061 / 10000000)) := by
  have h := reflection_log_6105_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6106_neg : (93004797 / 1000000000) ≤ -Real.log (1000000 / 1097467) ∧
    -Real.log (1000000 / 1097467) ≤ (46502399 / 500000000) := by
  have h := checkLog_sound (w := (97467 / 2097467)) (n := 12)
    (lo := (93004797 / 1000000000)) (hi := (46502399 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097467 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097467 / 1000000) = 1/(1000000 / 1097467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6106 : Bounds (93004797 / 1000000000) (46502399 / 500000000) (Real.log (1097467 / 1000000)) := by
  have h := reflection_log_6106_neg
  have he : Real.log (1097467 / 1000000) = -Real.log (1000000 / 1097467) := by
    rw [show ((1097467 / 1000000) : ℝ) = ((1000000 / 1097467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6107_neg : (12818753 / 125000000) ≤ -Real.log (902533 / 1000000) ∧
    -Real.log (902533 / 1000000) ≤ (4102001 / 40000000) := by
  have h := checkLog_sound (w := (97467 / 1902533)) (n := 12)
    (lo := (12818753 / 125000000)) (hi := (4102001 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902533) = 1/(902533 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6107 : Bounds (-4102001 / 40000000) (-12818753 / 125000000) (Real.log (902533 / 1000000)) := by
  have h := reflection_log_6107_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6108_neg : (46613551 / 500000000) ≤ -Real.log (1000000 / 1097711) ∧
    -Real.log (1000000 / 1097711) ≤ (93227103 / 1000000000) := by
  have h := checkLog_sound (w := (97711 / 2097711)) (n := 12)
    (lo := (46613551 / 500000000)) (hi := (93227103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097711 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097711 / 1000000) = 1/(1000000 / 1097711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6108 : Bounds (46613551 / 500000000) (93227103 / 1000000000) (Real.log (1097711 / 1000000)) := by
  have h := reflection_log_6108_neg
  have he : Real.log (1097711 / 1000000) = -Real.log (1000000 / 1097711) := by
    rw [show ((1097711 / 1000000) : ℝ) = ((1000000 / 1097711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6109_neg : (102820411 / 1000000000) ≤ -Real.log (902289 / 1000000) ∧
    -Real.log (902289 / 1000000) ≤ (25705103 / 250000000) := by
  have h := checkLog_sound (w := (97711 / 1902289)) (n := 12)
    (lo := (102820411 / 1000000000)) (hi := (25705103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902289) = 1/(902289 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6109 : Bounds (-25705103 / 250000000) (-102820411 / 1000000000) (Real.log (902289 / 1000000)) := by
  have h := reflection_log_6109_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6110_neg : (2398327 / 250000000) ≤ -Real.log (990452560479 / 1000000000000) ∧
    -Real.log (990452560479 / 1000000000000) ≤ (9593309 / 1000000000) := by
  have h := checkLog_sound (w := (9547439521 / 1990452560479)) (n := 12)
    (lo := (2398327 / 250000000)) (hi := (9593309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990452560479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990452560479) = 1/(990452560479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6110 : Bounds (-9593309 / 1000000000) (-2398327 / 250000000) (Real.log (990452560479 / 1000000000000)) := by
  have h := reflection_log_6110_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6111_neg : (9545227 / 1000000000) ≤ -Real.log (990500183911 / 1000000000000) ∧
    -Real.log (990500183911 / 1000000000000) ≤ (2386307 / 250000000) := by
  have h := checkLog_sound (w := (9499816089 / 1990500183911)) (n := 12)
    (lo := (9545227 / 1000000000)) (hi := (2386307 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990500183911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990500183911) = 1/(990500183911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6111 : Bounds (-2386307 / 250000000) (-9545227 / 1000000000) (Real.log (990500183911 / 1000000000000)) := by
  have h := reflection_log_6111_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6112_neg : (195554821 / 1000000000) ≤ -Real.log (100000000000 / 121598545427) ∧
    -Real.log (100000000000 / 121598545427) ≤ (97777411 / 500000000) := by
  have h := checkLog_sound (w := (21598545427 / 221598545427)) (n := 12)
    (lo := (195554821 / 1000000000)) (hi := (97777411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121598545427 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121598545427 / 100000000000) = 1/(100000000000 / 121598545427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6112 : Bounds (195554821 / 1000000000) (97777411 / 500000000) (Real.log (121598545427 / 100000000000)) := by
  have h := reflection_log_6112_neg
  have he : Real.log (121598545427 / 100000000000) = -Real.log (100000000000 / 121598545427) := by
    rw [show ((121598545427 / 100000000000) : ℝ) = ((100000000000 / 121598545427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6113_neg : (196047513 / 1000000000) ≤ -Real.log (31250000000 / 38018272139) ∧
    -Real.log (31250000000 / 38018272139) ≤ (98023757 / 500000000) := by
  have h := checkLog_sound (w := (6768272139 / 69268272139)) (n := 12)
    (lo := (196047513 / 1000000000)) (hi := (98023757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38018272139 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38018272139 / 31250000000) = 1/(31250000000 / 38018272139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6113 : Bounds (196047513 / 1000000000) (98023757 / 500000000) (Real.log (38018272139 / 31250000000)) := by
  have h := reflection_log_6113_neg
  have he : Real.log (38018272139 / 31250000000) = -Real.log (31250000000 / 38018272139) := by
    rw [show ((38018272139 / 31250000000) : ℝ) = ((31250000000 / 38018272139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6114_neg : (15702597 / 40000000) ≤ -Real.log (62500000000 / 92548375093) ∧
    -Real.log (62500000000 / 92548375093) ≤ (196282463 / 500000000) := by
  have h := checkLog_sound (w := (30048375093 / 155048375093)) (n := 12)
    (lo := (15702597 / 40000000)) (hi := (196282463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92548375093 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92548375093 / 62500000000) = 1/(62500000000 / 92548375093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6114 : Bounds (15702597 / 40000000) (196282463 / 500000000) (Real.log (92548375093 / 62500000000)) := by
  have h := reflection_log_6114_neg
  have he : Real.log (92548375093 / 62500000000) = -Real.log (62500000000 / 92548375093) := by
    rw [show ((92548375093 / 62500000000) : ℝ) = ((62500000000 / 92548375093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6115_neg : (196386367 / 500000000) ≤ -Real.log (250000000000 / 370270437911) ∧
    -Real.log (250000000000 / 370270437911) ≤ (78554547 / 200000000) := by
  have h := checkLog_sound (w := (120270437911 / 620270437911)) (n := 12)
    (lo := (196386367 / 500000000)) (hi := (78554547 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((370270437911 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(370270437911 / 250000000000) = 1/(250000000000 / 370270437911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6115 : Bounds (196386367 / 500000000) (78554547 / 200000000) (Real.log (370270437911 / 250000000000)) := by
  have h := reflection_log_6115_neg
  have he : Real.log (370270437911 / 250000000000) = -Real.log (250000000000 / 370270437911) := by
    rw [show ((370270437911 / 250000000000) : ℝ) = ((250000000000 / 370270437911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6116_neg : (88654507 / 500000000) ≤ -Real.log (500 / 597) ∧
    -Real.log (500 / 597) ≤ (35461803 / 200000000) := by
  have h := checkLog_sound (w := (97 / 1097)) (n := 12)
    (lo := (88654507 / 500000000)) (hi := (35461803 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597 / 500) = 1/(500 / 597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6116 : Bounds (88654507 / 500000000) (35461803 / 200000000) (Real.log (597 / 500)) := by
  have h := reflection_log_6116_neg
  have he : Real.log (597 / 500) = -Real.log (500 / 597) := by
    rw [show ((597 / 500) : ℝ) = ((500 / 597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6117_neg : (13479471 / 62500000) ≤ -Real.log (403 / 500) ∧
    -Real.log (403 / 500) ≤ (215671537 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 903)) (n := 12)
    (lo := (13479471 / 62500000)) (hi := (215671537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 403) = 1/(403 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6117 : Bounds (-215671537 / 1000000000) (-13479471 / 62500000) (Real.log (403 / 500)) := by
  have h := reflection_log_6117_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6118_neg : (193981 / 1000000000) ≤ -Real.log (500000 / 500097) ∧
    -Real.log (500000 / 500097) ≤ (96991 / 500000000) := by
  have h := checkLog_sound (w := (97 / 1000097)) (n := 12)
    (lo := (193981 / 1000000000)) (hi := (96991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500097 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500097 / 500000) = 1/(500000 / 500097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6118 : Bounds (193981 / 1000000000) (96991 / 500000000) (Real.log (500097 / 500000)) := by
  have h := reflection_log_6118_neg
  have he : Real.log (500097 / 500000) = -Real.log (500000 / 500097) := by
    rw [show ((500097 / 500000) : ℝ) = ((500000 / 500097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6119_neg : (97009 / 500000000) ≤ -Real.log (499903 / 500000) ∧
    -Real.log (499903 / 500000) ≤ (194019 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 999903)) (n := 12)
    (lo := (97009 / 500000000)) (hi := (194019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499903) = 1/(499903 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6119 : Bounds (-194019 / 1000000000) (-97009 / 500000000) (Real.log (499903 / 500000)) := by
  have h := reflection_log_6119_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6120_neg : (46525633 / 500000000) ≤ -Real.log (500000 / 548759) ∧
    -Real.log (500000 / 548759) ≤ (93051267 / 1000000000) := by
  have h := checkLog_sound (w := (48759 / 1048759)) (n := 12)
    (lo := (46525633 / 500000000)) (hi := (93051267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548759 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548759 / 500000) = 1/(500000 / 548759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6120 : Bounds (46525633 / 500000000) (93051267 / 1000000000) (Real.log (548759 / 500000)) := by
  have h := reflection_log_6120_neg
  have he : Real.log (548759 / 500000) = -Real.log (500000 / 548759) := by
    rw [show ((548759 / 500000) : ℝ) = ((500000 / 548759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6121_neg : (102606533 / 1000000000) ≤ -Real.log (451241 / 500000) ∧
    -Real.log (451241 / 500000) ≤ (51303267 / 500000000) := by
  have h := checkLog_sound (w := (48759 / 951241)) (n := 12)
    (lo := (102606533 / 1000000000)) (hi := (51303267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451241) = 1/(451241 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6121 : Bounds (-51303267 / 500000000) (-102606533 / 1000000000) (Real.log (451241 / 500000)) := by
  have h := reflection_log_6121_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6122_neg : (11659309 / 125000000) ≤ -Real.log (1000000 / 1097763) ∧
    -Real.log (1000000 / 1097763) ≤ (93274473 / 1000000000) := by
  have h := checkLog_sound (w := (97763 / 2097763)) (n := 12)
    (lo := (11659309 / 125000000)) (hi := (93274473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097763 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097763 / 1000000) = 1/(1000000 / 1097763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6122 : Bounds (11659309 / 125000000) (93274473 / 1000000000) (Real.log (1097763 / 1000000)) := by
  have h := reflection_log_6122_neg
  have he : Real.log (1097763 / 1000000) = -Real.log (1000000 / 1097763) := by
    rw [show ((1097763 / 1000000) : ℝ) = ((1000000 / 1097763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6123_neg : (102878043 / 1000000000) ≤ -Real.log (902237 / 1000000) ∧
    -Real.log (902237 / 1000000) ≤ (25719511 / 250000000) := by
  have h := checkLog_sound (w := (97763 / 1902237)) (n := 12)
    (lo := (102878043 / 1000000000)) (hi := (25719511 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902237) = 1/(902237 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6123 : Bounds (-25719511 / 250000000) (-102878043 / 1000000000) (Real.log (902237 / 1000000)) := by
  have h := reflection_log_6123_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6124_neg : (9603571 / 1000000000) ≤ -Real.log (990442395831 / 1000000000000) ∧
    -Real.log (990442395831 / 1000000000000) ≤ (2400893 / 250000000) := by
  have h := checkLog_sound (w := (9557604169 / 1990442395831)) (n := 12)
    (lo := (9603571 / 1000000000)) (hi := (2400893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990442395831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990442395831) = 1/(990442395831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6124 : Bounds (-2400893 / 250000000) (-9603571 / 1000000000) (Real.log (990442395831 / 1000000000000)) := by
  have h := reflection_log_6124_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6125_neg : (4777633 / 500000000) ≤ -Real.log (247622559919 / 250000000000) ∧
    -Real.log (247622559919 / 250000000000) ≤ (9555267 / 1000000000) := by
  have h := checkLog_sound (w := (2377440081 / 497622559919)) (n := 12)
    (lo := (4777633 / 500000000)) (hi := (9555267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247622559919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247622559919) = 1/(247622559919 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6125 : Bounds (-9555267 / 1000000000) (-4777633 / 500000000) (Real.log (247622559919 / 250000000000)) := by
  have h := reflection_log_6125_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6126_neg : (978289 / 5000000) ≤ -Real.log (100000000000 / 121611068143) ∧
    -Real.log (100000000000 / 121611068143) ≤ (195657801 / 1000000000) := by
  have h := checkLog_sound (w := (21611068143 / 221611068143)) (n := 12)
    (lo := (978289 / 5000000)) (hi := (195657801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121611068143 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121611068143 / 100000000000) = 1/(100000000000 / 121611068143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6126 : Bounds (978289 / 5000000) (195657801 / 1000000000) (Real.log (121611068143 / 100000000000)) := by
  have h := reflection_log_6126_neg
  have he : Real.log (121611068143 / 100000000000) = -Real.log (100000000000 / 121611068143) := by
    rw [show ((121611068143 / 100000000000) : ℝ) = ((100000000000 / 121611068143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6127_neg : (49038129 / 250000000) ≤ -Real.log (250000000000 / 304178115063) ∧
    -Real.log (250000000000 / 304178115063) ≤ (196152517 / 1000000000) := by
  have h := checkLog_sound (w := (54178115063 / 554178115063)) (n := 12)
    (lo := (49038129 / 250000000)) (hi := (196152517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304178115063 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304178115063 / 250000000000) = 1/(250000000000 / 304178115063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6127 : Bounds (49038129 / 250000000) (196152517 / 1000000000) (Real.log (304178115063 / 250000000000)) := by
  have h := reflection_log_6127_neg
  have he : Real.log (304178115063 / 250000000000) = -Real.log (250000000000 / 304178115063) := by
    rw [show ((304178115063 / 250000000000) : ℝ) = ((250000000000 / 304178115063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6128_neg : (196386367 / 500000000) ≤ -Real.log (500000000000 / 740540875821) ∧
    -Real.log (500000000000 / 740540875821) ≤ (78554547 / 200000000) := by
  have h := checkLog_sound (w := (240540875821 / 1240540875821)) (n := 12)
    (lo := (196386367 / 500000000)) (hi := (78554547 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((740540875821 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(740540875821 / 500000000000) = 1/(500000000000 / 740540875821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6128 : Bounds (196386367 / 500000000) (78554547 / 200000000) (Real.log (740540875821 / 500000000000)) := by
  have h := reflection_log_6128_neg
  have he : Real.log (740540875821 / 500000000000) = -Real.log (500000000000 / 740540875821) := by
    rw [show ((740540875821 / 500000000000) : ℝ) = ((500000000000 / 740540875821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6129_neg : (392980551 / 1000000000) ≤ -Real.log (250000000000 / 370347394541) ∧
    -Real.log (250000000000 / 370347394541) ≤ (49122569 / 125000000) := by
  have h := checkLog_sound (w := (120347394541 / 620347394541)) (n := 12)
    (lo := (392980551 / 1000000000)) (hi := (49122569 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((370347394541 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(370347394541 / 250000000000) = 1/(250000000000 / 370347394541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6129 : Bounds (392980551 / 1000000000) (49122569 / 125000000) (Real.log (370347394541 / 250000000000)) := by
  have h := reflection_log_6129_neg
  have he : Real.log (370347394541 / 250000000000) = -Real.log (250000000000 / 370347394541) := by
    rw [show ((370347394541 / 250000000000) : ℝ) = ((250000000000 / 370347394541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6130_neg : (177392763 / 1000000000) ≤ -Real.log (10000 / 11941) ∧
    -Real.log (10000 / 11941) ≤ (44348191 / 250000000) := by
  have h := checkLog_sound (w := (1941 / 21941)) (n := 12)
    (lo := (177392763 / 1000000000)) (hi := (44348191 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11941 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11941 / 10000) = 1/(10000 / 11941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6130 : Bounds (177392763 / 1000000000) (44348191 / 250000000) (Real.log (11941 / 10000)) := by
  have h := reflection_log_6130_neg
  have he : Real.log (11941 / 10000) = -Real.log (10000 / 11941) := by
    rw [show ((11941 / 10000) : ℝ) = ((10000 / 11941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6131_neg : (215795613 / 1000000000) ≤ -Real.log (8059 / 10000) ∧
    -Real.log (8059 / 10000) ≤ (107897807 / 500000000) := by
  have h := checkLog_sound (w := (1941 / 18059)) (n := 12)
    (lo := (215795613 / 1000000000)) (hi := (107897807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8059) = 1/(8059 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6131 : Bounds (-107897807 / 500000000) (-215795613 / 1000000000) (Real.log (8059 / 10000)) := by
  have h := reflection_log_6131_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6132_neg : (194081 / 1000000000) ≤ -Real.log (10000000 / 10001941) ∧
    -Real.log (10000000 / 10001941) ≤ (97041 / 500000000) := by
  have h := checkLog_sound (w := (1941 / 20001941)) (n := 12)
    (lo := (194081 / 1000000000)) (hi := (97041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001941 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001941 / 10000000) = 1/(10000000 / 10001941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6132 : Bounds (194081 / 1000000000) (97041 / 500000000) (Real.log (10001941 / 10000000)) := by
  have h := reflection_log_6132_neg
  have he : Real.log (10001941 / 10000000) = -Real.log (10000000 / 10001941) := by
    rw [show ((10001941 / 10000000) : ℝ) = ((10000000 / 10001941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6133_neg : (97059 / 500000000) ≤ -Real.log (9998059 / 10000000) ∧
    -Real.log (9998059 / 10000000) ≤ (194119 / 1000000000) := by
  have h := checkLog_sound (w := (1941 / 19998059)) (n := 12)
    (lo := (97059 / 500000000)) (hi := (194119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998059) = 1/(9998059 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6133 : Bounds (-194119 / 1000000000) (-97059 / 500000000) (Real.log (9998059 / 10000000)) := by
  have h := reflection_log_6133_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6134_neg : (46548867 / 500000000) ≤ -Real.log (1000000 / 1097569) ∧
    -Real.log (1000000 / 1097569) ≤ (18619547 / 200000000) := by
  have h := checkLog_sound (w := (97569 / 2097569)) (n := 12)
    (lo := (46548867 / 500000000)) (hi := (18619547 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097569 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097569 / 1000000) = 1/(1000000 / 1097569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6134 : Bounds (46548867 / 500000000) (18619547 / 200000000) (Real.log (1097569 / 1000000)) := by
  have h := reflection_log_6134_neg
  have he : Real.log (1097569 / 1000000) = -Real.log (1000000 / 1097569) := by
    rw [show ((1097569 / 1000000) : ℝ) = ((1000000 / 1097569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6135_neg : (20532609 / 200000000) ≤ -Real.log (902431 / 1000000) ∧
    -Real.log (902431 / 1000000) ≤ (51331523 / 500000000) := by
  have h := checkLog_sound (w := (97569 / 1902431)) (n := 12)
    (lo := (20532609 / 200000000)) (hi := (51331523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902431) = 1/(902431 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6135 : Bounds (-51331523 / 500000000) (-20532609 / 200000000) (Real.log (902431 / 1000000)) := by
  have h := reflection_log_6135_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6136_neg : (93320929 / 1000000000) ≤ -Real.log (500000 / 548907) ∧
    -Real.log (500000 / 548907) ≤ (9332093 / 100000000) := by
  have h := checkLog_sound (w := (48907 / 1048907)) (n := 12)
    (lo := (93320929 / 1000000000)) (hi := (9332093 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548907 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548907 / 500000) = 1/(500000 / 548907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6136 : Bounds (93320929 / 1000000000) (9332093 / 100000000) (Real.log (548907 / 500000)) := by
  have h := reflection_log_6136_neg
  have he : Real.log (548907 / 500000) = -Real.log (500000 / 548907) := by
    rw [show ((548907 / 500000) : ℝ) = ((500000 / 548907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6137_neg : (102934571 / 1000000000) ≤ -Real.log (451093 / 500000) ∧
    -Real.log (451093 / 500000) ≤ (25733643 / 250000000) := by
  have h := checkLog_sound (w := (48907 / 951093)) (n := 12)
    (lo := (102934571 / 1000000000)) (hi := (25733643 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451093) = 1/(451093 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6137 : Bounds (-25733643 / 250000000) (-102934571 / 1000000000) (Real.log (451093 / 500000)) := by
  have h := reflection_log_6137_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6138_neg : (9613641 / 1000000000) ≤ -Real.log (247608105351 / 250000000000) ∧
    -Real.log (247608105351 / 250000000000) ≤ (4806821 / 500000000) := by
  have h := checkLog_sound (w := (2391894649 / 497608105351)) (n := 12)
    (lo := (9613641 / 1000000000)) (hi := (4806821 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247608105351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247608105351) = 1/(247608105351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6138 : Bounds (-4806821 / 500000000) (-9613641 / 1000000000) (Real.log (247608105351 / 250000000000)) := by
  have h := reflection_log_6138_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6139_neg : (9565311 / 1000000000) ≤ -Real.log (990480290239 / 1000000000000) ∧
    -Real.log (990480290239 / 1000000000000) ≤ (74729 / 7812500) := by
  have h := checkLog_sound (w := (9519709761 / 1990480290239)) (n := 12)
    (lo := (9565311 / 1000000000)) (hi := (74729 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990480290239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990480290239) = 1/(990480290239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6139 : Bounds (-74729 / 7812500) (-9565311 / 1000000000) (Real.log (990480290239 / 1000000000000)) := by
  have h := reflection_log_6139_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6140_neg : (9788039 / 50000000) ≤ -Real.log (500000000000 / 608117961373) ∧
    -Real.log (500000000000 / 608117961373) ≤ (195760781 / 1000000000) := by
  have h := checkLog_sound (w := (108117961373 / 1108117961373)) (n := 12)
    (lo := (9788039 / 50000000)) (hi := (195760781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608117961373 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608117961373 / 500000000000) = 1/(500000000000 / 608117961373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6140 : Bounds (9788039 / 50000000) (195760781 / 1000000000) (Real.log (608117961373 / 500000000000)) := by
  have h := reflection_log_6140_neg
  have he : Real.log (608117961373 / 500000000000) = -Real.log (500000000000 / 608117961373) := by
    rw [show ((608117961373 / 500000000000) : ℝ) = ((500000000000 / 608117961373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6141_neg : (196255501 / 1000000000) ≤ -Real.log (250000000000 / 304209442399) ∧
    -Real.log (250000000000 / 304209442399) ≤ (98127751 / 500000000) := by
  have h := checkLog_sound (w := (54209442399 / 554209442399)) (n := 12)
    (lo := (196255501 / 1000000000)) (hi := (98127751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304209442399 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304209442399 / 250000000000) = 1/(250000000000 / 304209442399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6141 : Bounds (196255501 / 1000000000) (98127751 / 500000000) (Real.log (304209442399 / 250000000000)) := by
  have h := reflection_log_6141_neg
  have he : Real.log (304209442399 / 250000000000) = -Real.log (250000000000 / 304209442399) := by
    rw [show ((304209442399 / 250000000000) : ℝ) = ((250000000000 / 304209442399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6142_neg : (392980551 / 1000000000) ≤ -Real.log (500000000000 / 740694789081) ∧
    -Real.log (500000000000 / 740694789081) ≤ (49122569 / 125000000) := by
  have h := checkLog_sound (w := (240694789081 / 1240694789081)) (n := 12)
    (lo := (392980551 / 1000000000)) (hi := (49122569 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((740694789081 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(740694789081 / 500000000000) = 1/(500000000000 / 740694789081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6142 : Bounds (392980551 / 1000000000) (49122569 / 125000000) (Real.log (740694789081 / 500000000000)) := by
  have h := reflection_log_6142_neg
  have he : Real.log (740694789081 / 500000000000) = -Real.log (500000000000 / 740694789081) := by
    rw [show ((740694789081 / 500000000000) : ℝ) = ((500000000000 / 740694789081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6143_neg : (393188377 / 1000000000) ≤ -Real.log (500000000000 / 740848740539) ∧
    -Real.log (500000000000 / 740848740539) ≤ (196594189 / 500000000) := by
  have h := checkLog_sound (w := (240848740539 / 1240848740539)) (n := 12)
    (lo := (393188377 / 1000000000)) (hi := (196594189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((740848740539 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(740848740539 / 500000000000) = 1/(500000000000 / 740848740539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6143 : Bounds (393188377 / 1000000000) (196594189 / 500000000) (Real.log (740848740539 / 500000000000)) := by
  have h := reflection_log_6143_neg
  have he : Real.log (740848740539 / 500000000000) = -Real.log (500000000000 / 740848740539) := by
    rw [show ((740848740539 / 500000000000) : ℝ) = ((500000000000 / 740848740539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0096 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6144_neg : (35495301 / 200000000) ≤ -Real.log (5000 / 5971) ∧
    -Real.log (5000 / 5971) ≤ (88738253 / 500000000) := by
  have h := checkLog_sound (w := (971 / 10971)) (n := 12)
    (lo := (35495301 / 200000000)) (hi := (88738253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5971 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5971 / 5000) = 1/(5000 / 5971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6144 : Bounds (35495301 / 200000000) (88738253 / 500000000) (Real.log (5971 / 5000)) := by
  have h := reflection_log_6144_neg
  have he : Real.log (5971 / 5000) = -Real.log (5000 / 5971) := by
    rw [show ((5971 / 5000) : ℝ) = ((5000 / 5971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6145_neg : (107959853 / 500000000) ≤ -Real.log (4029 / 5000) ∧
    -Real.log (4029 / 5000) ≤ (215919707 / 1000000000) := by
  have h := checkLog_sound (w := (971 / 9029)) (n := 12)
    (lo := (107959853 / 500000000)) (hi := (215919707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4029) = 1/(4029 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6145 : Bounds (-215919707 / 1000000000) (-107959853 / 500000000) (Real.log (4029 / 5000)) := by
  have h := reflection_log_6145_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6146_neg : (194181 / 1000000000) ≤ -Real.log (5000000 / 5000971) ∧
    -Real.log (5000000 / 5000971) ≤ (97091 / 500000000) := by
  have h := checkLog_sound (w := (971 / 10000971)) (n := 12)
    (lo := (194181 / 1000000000)) (hi := (97091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000971 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000971 / 5000000) = 1/(5000000 / 5000971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6146 : Bounds (194181 / 1000000000) (97091 / 500000000) (Real.log (5000971 / 5000000)) := by
  have h := reflection_log_6146_neg
  have he : Real.log (5000971 / 5000000) = -Real.log (5000000 / 5000971) := by
    rw [show ((5000971 / 5000000) : ℝ) = ((5000000 / 5000971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6147_neg : (97109 / 500000000) ≤ -Real.log (4999029 / 5000000) ∧
    -Real.log (4999029 / 5000000) ≤ (194219 / 1000000000) := by
  have h := checkLog_sound (w := (971 / 9999029)) (n := 12)
    (lo := (97109 / 500000000)) (hi := (194219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999029) = 1/(4999029 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6147 : Bounds (-194219 / 1000000000) (-97109 / 500000000) (Real.log (4999029 / 5000000)) := by
  have h := reflection_log_6147_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6148_neg : (93144199 / 1000000000) ≤ -Real.log (50000 / 54881) ∧
    -Real.log (50000 / 54881) ≤ (465721 / 5000000) := by
  have h := checkLog_sound (w := (4881 / 104881)) (n := 12)
    (lo := (93144199 / 1000000000)) (hi := (465721 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54881 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54881 / 50000) = 1/(50000 / 54881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6148 : Bounds (93144199 / 1000000000) (465721 / 5000000) (Real.log (54881 / 50000)) := by
  have h := reflection_log_6148_neg
  have he : Real.log (54881 / 50000) = -Real.log (50000 / 54881) := by
    rw [show ((54881 / 50000) : ℝ) = ((50000 / 54881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6149_neg : (102719561 / 1000000000) ≤ -Real.log (45119 / 50000) ∧
    -Real.log (45119 / 50000) ≤ (51359781 / 500000000) := by
  have h := checkLog_sound (w := (4881 / 95119)) (n := 12)
    (lo := (102719561 / 1000000000)) (hi := (51359781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45119) = 1/(45119 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6149 : Bounds (-51359781 / 500000000) (-102719561 / 1000000000) (Real.log (45119 / 50000)) := by
  have h := reflection_log_6149_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6150_neg : (11670923 / 125000000) ≤ -Real.log (200000 / 219573) ∧
    -Real.log (200000 / 219573) ≤ (18673477 / 200000000) := by
  have h := checkLog_sound (w := (19573 / 419573)) (n := 12)
    (lo := (11670923 / 125000000)) (hi := (18673477 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219573 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219573 / 200000) = 1/(200000 / 219573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6150 : Bounds (11670923 / 125000000) (18673477 / 200000000) (Real.log (219573 / 200000)) := by
  have h := reflection_log_6150_neg
  have he : Real.log (219573 / 200000) = -Real.log (200000 / 219573) := by
    rw [show ((219573 / 200000) : ℝ) = ((200000 / 219573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6151_neg : (51495551 / 500000000) ≤ -Real.log (180427 / 200000) ∧
    -Real.log (180427 / 200000) ≤ (102991103 / 1000000000) := by
  have h := checkLog_sound (w := (19573 / 380427)) (n := 12)
    (lo := (51495551 / 500000000)) (hi := (102991103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180427) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180427) = 1/(180427 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6151 : Bounds (-102991103 / 1000000000) (-51495551 / 500000000) (Real.log (180427 / 200000)) := by
  have h := reflection_log_6151_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6152_neg : (4811859 / 500000000) ≤ -Real.log (39616897671 / 40000000000) ∧
    -Real.log (39616897671 / 40000000000) ≤ (9623719 / 1000000000) := by
  have h := checkLog_sound (w := (383102329 / 79616897671)) (n := 12)
    (lo := (4811859 / 500000000)) (hi := (9623719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39616897671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39616897671) = 1/(39616897671 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6152 : Bounds (-9623719 / 1000000000) (-4811859 / 500000000) (Real.log (39616897671 / 40000000000)) := by
  have h := reflection_log_6152_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6153_neg : (4787681 / 500000000) ≤ -Real.log (2476175839 / 2500000000) ∧
    -Real.log (2476175839 / 2500000000) ≤ (9575363 / 1000000000) := by
  have h := checkLog_sound (w := (23824161 / 4976175839)) (n := 12)
    (lo := (4787681 / 500000000)) (hi := (9575363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2476175839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2476175839) = 1/(2476175839 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6153 : Bounds (-9575363 / 1000000000) (-4787681 / 500000000) (Real.log (2476175839 / 2500000000)) := by
  have h := reflection_log_6153_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6154_neg : (195863761 / 1000000000) ≤ -Real.log (125000000000 / 152045147277) ∧
    -Real.log (125000000000 / 152045147277) ≤ (97931881 / 500000000) := by
  have h := checkLog_sound (w := (27045147277 / 277045147277)) (n := 12)
    (lo := (195863761 / 1000000000)) (hi := (97931881 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152045147277 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152045147277 / 125000000000) = 1/(125000000000 / 152045147277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6154 : Bounds (195863761 / 1000000000) (97931881 / 500000000) (Real.log (152045147277 / 125000000000)) := by
  have h := reflection_log_6154_neg
  have he : Real.log (152045147277 / 125000000000) = -Real.log (125000000000 / 152045147277) := by
    rw [show ((152045147277 / 125000000000) : ℝ) = ((125000000000 / 152045147277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6155_neg : (196358487 / 1000000000) ≤ -Real.log (250000000000 / 304240773277) ∧
    -Real.log (250000000000 / 304240773277) ≤ (24544811 / 125000000) := by
  have h := checkLog_sound (w := (54240773277 / 554240773277)) (n := 12)
    (lo := (196358487 / 1000000000)) (hi := (24544811 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304240773277 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304240773277 / 250000000000) = 1/(250000000000 / 304240773277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6155 : Bounds (196358487 / 1000000000) (24544811 / 125000000) (Real.log (304240773277 / 250000000000)) := by
  have h := reflection_log_6155_neg
  have he : Real.log (304240773277 / 250000000000) = -Real.log (250000000000 / 304240773277) := by
    rw [show ((304240773277 / 250000000000) : ℝ) = ((250000000000 / 304240773277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6156_neg : (393188377 / 1000000000) ≤ -Real.log (250000000000 / 370424370269) ∧
    -Real.log (250000000000 / 370424370269) ≤ (196594189 / 500000000) := by
  have h := checkLog_sound (w := (120424370269 / 620424370269)) (n := 12)
    (lo := (393188377 / 1000000000)) (hi := (196594189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((370424370269 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(370424370269 / 250000000000) = 1/(250000000000 / 370424370269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6156 : Bounds (393188377 / 1000000000) (196594189 / 500000000) (Real.log (370424370269 / 250000000000)) := by
  have h := reflection_log_6156_neg
  have he : Real.log (370424370269 / 250000000000) = -Real.log (250000000000 / 370424370269) := by
    rw [show ((370424370269 / 250000000000) : ℝ) = ((250000000000 / 370424370269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6157_neg : (393396211 / 1000000000) ≤ -Real.log (500000000000 / 741002730207) ∧
    -Real.log (500000000000 / 741002730207) ≤ (98349053 / 250000000) := by
  have h := checkLog_sound (w := (241002730207 / 1241002730207)) (n := 12)
    (lo := (393396211 / 1000000000)) (hi := (98349053 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741002730207 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741002730207 / 500000000000) = 1/(500000000000 / 741002730207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6157 : Bounds (393396211 / 1000000000) (98349053 / 250000000) (Real.log (741002730207 / 500000000000)) := by
  have h := reflection_log_6157_neg
  have he : Real.log (741002730207 / 500000000000) = -Real.log (500000000000 / 741002730207) := by
    rw [show ((741002730207 / 500000000000) : ℝ) = ((500000000000 / 741002730207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6158_neg : (177560239 / 1000000000) ≤ -Real.log (10000 / 11943) ∧
    -Real.log (10000 / 11943) ≤ (2219503 / 12500000) := by
  have h := checkLog_sound (w := (1943 / 21943)) (n := 12)
    (lo := (177560239 / 1000000000)) (hi := (2219503 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11943 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11943 / 10000) = 1/(10000 / 11943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6158 : Bounds (177560239 / 1000000000) (2219503 / 12500000) (Real.log (11943 / 10000)) := by
  have h := reflection_log_6158_neg
  have he : Real.log (11943 / 10000) = -Real.log (10000 / 11943) := by
    rw [show ((11943 / 10000) : ℝ) = ((10000 / 11943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6159_neg : (108021907 / 500000000) ≤ -Real.log (8057 / 10000) ∧
    -Real.log (8057 / 10000) ≤ (43208763 / 200000000) := by
  have h := checkLog_sound (w := (1943 / 18057)) (n := 12)
    (lo := (108021907 / 500000000)) (hi := (43208763 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8057) = 1/(8057 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6159 : Bounds (-43208763 / 200000000) (-108021907 / 500000000) (Real.log (8057 / 10000)) := by
  have h := reflection_log_6159_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6160_neg : (194281 / 1000000000) ≤ -Real.log (10000000 / 10001943) ∧
    -Real.log (10000000 / 10001943) ≤ (97141 / 500000000) := by
  have h := checkLog_sound (w := (1943 / 20001943)) (n := 12)
    (lo := (194281 / 1000000000)) (hi := (97141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001943 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001943 / 10000000) = 1/(10000000 / 10001943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6160 : Bounds (194281 / 1000000000) (97141 / 500000000) (Real.log (10001943 / 10000000)) := by
  have h := reflection_log_6160_neg
  have he : Real.log (10001943 / 10000000) = -Real.log (10000000 / 10001943) := by
    rw [show ((10001943 / 10000000) : ℝ) = ((10000000 / 10001943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6161_neg : (97159 / 500000000) ≤ -Real.log (9998057 / 10000000) ∧
    -Real.log (9998057 / 10000000) ≤ (194319 / 1000000000) := by
  have h := checkLog_sound (w := (1943 / 19998057)) (n := 12)
    (lo := (97159 / 500000000)) (hi := (194319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998057) = 1/(9998057 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6161 : Bounds (-194319 / 1000000000) (-97159 / 500000000) (Real.log (9998057 / 10000000)) := by
  have h := reflection_log_6161_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6162_neg : (46595331 / 500000000) ≤ -Real.log (1000000 / 1097671) ∧
    -Real.log (1000000 / 1097671) ≤ (93190663 / 1000000000) := by
  have h := checkLog_sound (w := (97671 / 2097671)) (n := 12)
    (lo := (46595331 / 500000000)) (hi := (93190663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097671 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097671 / 1000000) = 1/(1000000 / 1097671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6162 : Bounds (46595331 / 500000000) (93190663 / 1000000000) (Real.log (1097671 / 1000000)) := by
  have h := reflection_log_6162_neg
  have he : Real.log (1097671 / 1000000) = -Real.log (1000000 / 1097671) := by
    rw [show ((1097671 / 1000000) : ℝ) = ((1000000 / 1097671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6163_neg : (1284701 / 12500000) ≤ -Real.log (902329 / 1000000) ∧
    -Real.log (902329 / 1000000) ≤ (102776081 / 1000000000) := by
  have h := checkLog_sound (w := (97671 / 1902329)) (n := 12)
    (lo := (1284701 / 12500000)) (hi := (102776081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902329) = 1/(902329 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6163 : Bounds (-102776081 / 1000000000) (-1284701 / 12500000) (Real.log (902329 / 1000000)) := by
  have h := reflection_log_6163_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6164_neg : (93413837 / 1000000000) ≤ -Real.log (250000 / 274479) ∧
    -Real.log (250000 / 274479) ≤ (46706919 / 500000000) := by
  have h := checkLog_sound (w := (24479 / 524479)) (n := 12)
    (lo := (93413837 / 1000000000)) (hi := (46706919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274479 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274479 / 250000) = 1/(250000 / 274479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6164 : Bounds (93413837 / 1000000000) (46706919 / 500000000) (Real.log (274479 / 250000)) := by
  have h := reflection_log_6164_neg
  have he : Real.log (274479 / 250000) = -Real.log (250000 / 274479) := by
    rw [show ((274479 / 250000) : ℝ) = ((250000 / 274479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6165_neg : (25761909 / 250000000) ≤ -Real.log (225521 / 250000) ∧
    -Real.log (225521 / 250000) ≤ (103047637 / 1000000000) := by
  have h := checkLog_sound (w := (24479 / 475521)) (n := 12)
    (lo := (25761909 / 250000000)) (hi := (103047637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225521) = 1/(225521 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6165 : Bounds (-103047637 / 1000000000) (-25761909 / 250000000) (Real.log (225521 / 250000)) := by
  have h := reflection_log_6165_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6166_neg : (9633799 / 1000000000) ≤ -Real.log (61900778559 / 62500000000) ∧
    -Real.log (61900778559 / 62500000000) ≤ (48169 / 5000000) := by
  have h := checkLog_sound (w := (599221441 / 124400778559)) (n := 12)
    (lo := (9633799 / 1000000000)) (hi := (48169 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61900778559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61900778559) = 1/(61900778559 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6166 : Bounds (-48169 / 5000000) (-9633799 / 1000000000) (Real.log (61900778559 / 62500000000)) := by
  have h := reflection_log_6166_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6167_neg : (9585417 / 1000000000) ≤ -Real.log (990460375759 / 1000000000000) ∧
    -Real.log (990460375759 / 1000000000000) ≤ (4792709 / 500000000) := by
  have h := checkLog_sound (w := (9539624241 / 1990460375759)) (n := 12)
    (lo := (9585417 / 1000000000)) (hi := (4792709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990460375759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990460375759) = 1/(990460375759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6167 : Bounds (-4792709 / 500000000) (-9585417 / 1000000000) (Real.log (990460375759 / 1000000000000)) := by
  have h := reflection_log_6167_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6168_neg : (97983371 / 500000000) ≤ -Real.log (500000000000 / 608243223923) ∧
    -Real.log (500000000000 / 608243223923) ≤ (195966743 / 1000000000) := by
  have h := checkLog_sound (w := (108243223923 / 1108243223923)) (n := 12)
    (lo := (97983371 / 500000000)) (hi := (195966743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608243223923 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608243223923 / 500000000000) = 1/(500000000000 / 608243223923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6168 : Bounds (97983371 / 500000000) (195966743 / 1000000000) (Real.log (608243223923 / 500000000000)) := by
  have h := reflection_log_6168_neg
  have he : Real.log (608243223923 / 500000000000) = -Real.log (500000000000 / 608243223923) := by
    rw [show ((608243223923 / 500000000000) : ℝ) = ((500000000000 / 608243223923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6169_neg : (98230737 / 500000000) ≤ -Real.log (100000000000 / 121708843079) ∧
    -Real.log (100000000000 / 121708843079) ≤ (7858459 / 40000000) := by
  have h := checkLog_sound (w := (21708843079 / 221708843079)) (n := 12)
    (lo := (98230737 / 500000000)) (hi := (7858459 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121708843079 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121708843079 / 100000000000) = 1/(100000000000 / 121708843079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6169 : Bounds (98230737 / 500000000) (7858459 / 40000000) (Real.log (121708843079 / 100000000000)) := by
  have h := reflection_log_6169_neg
  have he : Real.log (121708843079 / 100000000000) = -Real.log (100000000000 / 121708843079) := by
    rw [show ((121708843079 / 100000000000) : ℝ) = ((100000000000 / 121708843079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6170_neg : (393396211 / 1000000000) ≤ -Real.log (250000000000 / 370501365103) ∧
    -Real.log (250000000000 / 370501365103) ≤ (98349053 / 250000000) := by
  have h := checkLog_sound (w := (120501365103 / 620501365103)) (n := 12)
    (lo := (393396211 / 1000000000)) (hi := (98349053 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((370501365103 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(370501365103 / 250000000000) = 1/(250000000000 / 370501365103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6170 : Bounds (393396211 / 1000000000) (98349053 / 250000000) (Real.log (370501365103 / 250000000000)) := by
  have h := reflection_log_6170_neg
  have he : Real.log (370501365103 / 250000000000) = -Real.log (250000000000 / 370501365103) := by
    rw [show ((370501365103 / 250000000000) : ℝ) = ((250000000000 / 370501365103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6171_neg : (393604053 / 1000000000) ≤ -Real.log (500000000000 / 741156758099) ∧
    -Real.log (500000000000 / 741156758099) ≤ (196802027 / 500000000) := by
  have h := checkLog_sound (w := (241156758099 / 1241156758099)) (n := 12)
    (lo := (393604053 / 1000000000)) (hi := (196802027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741156758099 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741156758099 / 500000000000) = 1/(500000000000 / 741156758099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6171 : Bounds (393604053 / 1000000000) (196802027 / 500000000) (Real.log (741156758099 / 500000000000)) := by
  have h := reflection_log_6171_neg
  have he : Real.log (741156758099 / 500000000000) = -Real.log (500000000000 / 741156758099) := by
    rw [show ((741156758099 / 500000000000) : ℝ) = ((500000000000 / 741156758099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6172_neg : (177643967 / 1000000000) ≤ -Real.log (1250 / 1493) ∧
    -Real.log (1250 / 1493) ≤ (2775687 / 15625000) := by
  have h := checkLog_sound (w := (243 / 2743)) (n := 12)
    (lo := (177643967 / 1000000000)) (hi := (2775687 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1493 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1493 / 1250) = 1/(1250 / 1493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6172 : Bounds (177643967 / 1000000000) (2775687 / 15625000) (Real.log (1493 / 1250)) := by
  have h := reflection_log_6172_neg
  have he : Real.log (1493 / 1250) = -Real.log (1250 / 1493) := by
    rw [show ((1493 / 1250) : ℝ) = ((1250 / 1493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6173_neg : (216167937 / 1000000000) ≤ -Real.log (1007 / 1250) ∧
    -Real.log (1007 / 1250) ≤ (108083969 / 500000000) := by
  have h := checkLog_sound (w := (243 / 2257)) (n := 12)
    (lo := (216167937 / 1000000000)) (hi := (108083969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1007) = 1/(1007 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6173 : Bounds (-108083969 / 500000000) (-216167937 / 1000000000) (Real.log (1007 / 1250)) := by
  have h := reflection_log_6173_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6174_neg : (194381 / 1000000000) ≤ -Real.log (1250000 / 1250243) ∧
    -Real.log (1250000 / 1250243) ≤ (97191 / 500000000) := by
  have h := checkLog_sound (w := (243 / 2500243)) (n := 12)
    (lo := (194381 / 1000000000)) (hi := (97191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250243 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250243 / 1250000) = 1/(1250000 / 1250243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6174 : Bounds (194381 / 1000000000) (97191 / 500000000) (Real.log (1250243 / 1250000)) := by
  have h := reflection_log_6174_neg
  have he : Real.log (1250243 / 1250000) = -Real.log (1250000 / 1250243) := by
    rw [show ((1250243 / 1250000) : ℝ) = ((1250000 / 1250243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6175_neg : (97209 / 500000000) ≤ -Real.log (1249757 / 1250000) ∧
    -Real.log (1249757 / 1250000) ≤ (194419 / 1000000000) := by
  have h := checkLog_sound (w := (243 / 2499757)) (n := 12)
    (lo := (97209 / 500000000)) (hi := (194419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249757) = 1/(1249757 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6175 : Bounds (-194419 / 1000000000) (-97209 / 500000000) (Real.log (1249757 / 1250000)) := by
  have h := reflection_log_6175_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6176_neg : (93237123 / 1000000000) ≤ -Real.log (500000 / 548861) ∧
    -Real.log (500000 / 548861) ≤ (23309281 / 250000000) := by
  have h := checkLog_sound (w := (48861 / 1048861)) (n := 12)
    (lo := (93237123 / 1000000000)) (hi := (23309281 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548861 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548861 / 500000) = 1/(500000 / 548861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6176 : Bounds (93237123 / 1000000000) (23309281 / 250000000) (Real.log (548861 / 500000)) := by
  have h := reflection_log_6176_neg
  have he : Real.log (548861 / 500000) = -Real.log (500000 / 548861) := by
    rw [show ((548861 / 500000) : ℝ) = ((500000 / 548861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6177_neg : (51416301 / 500000000) ≤ -Real.log (451139 / 500000) ∧
    -Real.log (451139 / 500000) ≤ (102832603 / 1000000000) := by
  have h := checkLog_sound (w := (48861 / 951139)) (n := 12)
    (lo := (51416301 / 500000000)) (hi := (102832603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451139) = 1/(451139 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6177 : Bounds (-102832603 / 1000000000) (-51416301 / 500000000) (Real.log (451139 / 500000)) := by
  have h := reflection_log_6177_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6178_neg : (93460287 / 1000000000) ≤ -Real.log (1000000 / 1097967) ∧
    -Real.log (1000000 / 1097967) ≤ (1460317 / 15625000) := by
  have h := checkLog_sound (w := (97967 / 2097967)) (n := 12)
    (lo := (93460287 / 1000000000)) (hi := (1460317 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097967 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097967 / 1000000) = 1/(1000000 / 1097967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6178 : Bounds (93460287 / 1000000000) (1460317 / 15625000) (Real.log (1097967 / 1000000)) := by
  have h := reflection_log_6178_neg
  have he : Real.log (1097967 / 1000000) = -Real.log (1000000 / 1097967) := by
    rw [show ((1097967 / 1000000) : ℝ) = ((1000000 / 1097967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6179_neg : (51552087 / 500000000) ≤ -Real.log (902033 / 1000000) ∧
    -Real.log (902033 / 1000000) ≤ (4124167 / 40000000) := by
  have h := checkLog_sound (w := (97967 / 1902033)) (n := 12)
    (lo := (51552087 / 500000000)) (hi := (4124167 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902033) = 1/(902033 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6179 : Bounds (-4124167 / 40000000) (-51552087 / 500000000) (Real.log (902033 / 1000000)) := by
  have h := reflection_log_6179_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6180_neg : (4821943 / 500000000) ≤ -Real.log (990402466911 / 1000000000000) ∧
    -Real.log (990402466911 / 1000000000000) ≤ (9643887 / 1000000000) := by
  have h := checkLog_sound (w := (9597533089 / 1990402466911)) (n := 12)
    (lo := (4821943 / 500000000)) (hi := (9643887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990402466911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990402466911) = 1/(990402466911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6180 : Bounds (-9643887 / 1000000000) (-4821943 / 500000000) (Real.log (990402466911 / 1000000000000)) := by
  have h := reflection_log_6180_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6181_neg : (4797739 / 500000000) ≤ -Real.log (247612602679 / 250000000000) ∧
    -Real.log (247612602679 / 250000000000) ≤ (9595479 / 1000000000) := by
  have h := checkLog_sound (w := (2387397321 / 497612602679)) (n := 12)
    (lo := (4797739 / 500000000)) (hi := (9595479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247612602679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247612602679) = 1/(247612602679 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6181 : Bounds (-9595479 / 1000000000) (-4797739 / 500000000) (Real.log (247612602679 / 250000000000)) := by
  have h := reflection_log_6181_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6182_neg : (7842789 / 40000000) ≤ -Real.log (500000000000 / 608305865819) ∧
    -Real.log (500000000000 / 608305865819) ≤ (98034863 / 500000000) := by
  have h := checkLog_sound (w := (108305865819 / 1108305865819)) (n := 12)
    (lo := (7842789 / 40000000)) (hi := (98034863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608305865819 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608305865819 / 500000000000) = 1/(500000000000 / 608305865819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6182 : Bounds (7842789 / 40000000) (98034863 / 500000000) (Real.log (608305865819 / 500000000000)) := by
  have h := reflection_log_6182_neg
  have he : Real.log (608305865819 / 500000000000) = -Real.log (500000000000 / 608305865819) := by
    rw [show ((608305865819 / 500000000000) : ℝ) = ((500000000000 / 608305865819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6183_neg : (98282231 / 500000000) ≤ -Real.log (500000000000 / 608606891323) ∧
    -Real.log (500000000000 / 608606891323) ≤ (196564463 / 1000000000) := by
  have h := checkLog_sound (w := (108606891323 / 1108606891323)) (n := 12)
    (lo := (98282231 / 500000000)) (hi := (196564463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608606891323 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608606891323 / 500000000000) = 1/(500000000000 / 608606891323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6183 : Bounds (98282231 / 500000000) (196564463 / 1000000000) (Real.log (608606891323 / 500000000000)) := by
  have h := reflection_log_6183_neg
  have he : Real.log (608606891323 / 500000000000) = -Real.log (500000000000 / 608606891323) := by
    rw [show ((608606891323 / 500000000000) : ℝ) = ((500000000000 / 608606891323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6184_neg : (393604053 / 1000000000) ≤ -Real.log (250000000000 / 370578379049) ∧
    -Real.log (250000000000 / 370578379049) ≤ (196802027 / 500000000) := by
  have h := checkLog_sound (w := (120578379049 / 620578379049)) (n := 12)
    (lo := (393604053 / 1000000000)) (hi := (196802027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((370578379049 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(370578379049 / 250000000000) = 1/(250000000000 / 370578379049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6184 : Bounds (393604053 / 1000000000) (196802027 / 500000000) (Real.log (370578379049 / 250000000000)) := by
  have h := reflection_log_6184_neg
  have he : Real.log (370578379049 / 250000000000) = -Real.log (250000000000 / 370578379049) := by
    rw [show ((370578379049 / 250000000000) : ℝ) = ((250000000000 / 370578379049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6185_neg : (6153311 / 15625000) ≤ -Real.log (500000000000 / 741310824231) ∧
    -Real.log (500000000000 / 741310824231) ≤ (78762381 / 200000000) := by
  have h := checkLog_sound (w := (241310824231 / 1241310824231)) (n := 12)
    (lo := (6153311 / 15625000)) (hi := (78762381 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741310824231 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741310824231 / 500000000000) = 1/(500000000000 / 741310824231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6185 : Bounds (6153311 / 15625000) (78762381 / 200000000) (Real.log (741310824231 / 500000000000)) := by
  have h := reflection_log_6185_neg
  have he : Real.log (741310824231 / 500000000000) = -Real.log (500000000000 / 741310824231) := by
    rw [show ((741310824231 / 500000000000) : ℝ) = ((500000000000 / 741310824231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6186_neg : (177727687 / 1000000000) ≤ -Real.log (2000 / 2389) ∧
    -Real.log (2000 / 2389) ≤ (22215961 / 125000000) := by
  have h := checkLog_sound (w := (389 / 4389)) (n := 12)
    (lo := (177727687 / 1000000000)) (hi := (22215961 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2389 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2389 / 2000) = 1/(2000 / 2389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6186 : Bounds (177727687 / 1000000000) (22215961 / 125000000) (Real.log (2389 / 2000)) := by
  have h := reflection_log_6186_neg
  have he : Real.log (2389 / 2000) = -Real.log (2000 / 2389) := by
    rw [show ((2389 / 2000) : ℝ) = ((2000 / 2389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6187_neg : (54073019 / 250000000) ≤ -Real.log (1611 / 2000) ∧
    -Real.log (1611 / 2000) ≤ (216292077 / 1000000000) := by
  have h := checkLog_sound (w := (389 / 3611)) (n := 12)
    (lo := (54073019 / 250000000)) (hi := (216292077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1611) = 1/(1611 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6187 : Bounds (-216292077 / 1000000000) (-54073019 / 250000000) (Real.log (1611 / 2000)) := by
  have h := reflection_log_6187_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6188_neg : (194481 / 1000000000) ≤ -Real.log (2000000 / 2000389) ∧
    -Real.log (2000000 / 2000389) ≤ (97241 / 500000000) := by
  have h := checkLog_sound (w := (389 / 4000389)) (n := 12)
    (lo := (194481 / 1000000000)) (hi := (97241 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000389 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000389 / 2000000) = 1/(2000000 / 2000389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6188 : Bounds (194481 / 1000000000) (97241 / 500000000) (Real.log (2000389 / 2000000)) := by
  have h := reflection_log_6188_neg
  have he : Real.log (2000389 / 2000000) = -Real.log (2000000 / 2000389) := by
    rw [show ((2000389 / 2000000) : ℝ) = ((2000000 / 2000389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6189_neg : (97259 / 500000000) ≤ -Real.log (1999611 / 2000000) ∧
    -Real.log (1999611 / 2000000) ≤ (194519 / 1000000000) := by
  have h := checkLog_sound (w := (389 / 3999611)) (n := 12)
    (lo := (97259 / 500000000)) (hi := (194519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999611) = 1/(1999611 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6189 : Bounds (-194519 / 1000000000) (-97259 / 500000000) (Real.log (1999611 / 2000000)) := by
  have h := reflection_log_6189_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6190_neg : (46641791 / 500000000) ≤ -Real.log (1000000 / 1097773) ∧
    -Real.log (1000000 / 1097773) ≤ (93283583 / 1000000000) := by
  have h := checkLog_sound (w := (97773 / 2097773)) (n := 12)
    (lo := (46641791 / 500000000)) (hi := (93283583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097773 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097773 / 1000000) = 1/(1000000 / 1097773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6190 : Bounds (46641791 / 500000000) (93283583 / 1000000000) (Real.log (1097773 / 1000000)) := by
  have h := reflection_log_6190_neg
  have he : Real.log (1097773 / 1000000) = -Real.log (1000000 / 1097773) := by
    rw [show ((1097773 / 1000000) : ℝ) = ((1000000 / 1097773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6191_neg : (102889127 / 1000000000) ≤ -Real.log (902227 / 1000000) ∧
    -Real.log (902227 / 1000000) ≤ (12861141 / 125000000) := by
  have h := checkLog_sound (w := (97773 / 1902227)) (n := 12)
    (lo := (102889127 / 1000000000)) (hi := (12861141 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902227) = 1/(902227 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6191 : Bounds (-12861141 / 125000000) (-102889127 / 1000000000) (Real.log (902227 / 1000000)) := by
  have h := reflection_log_6191_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6192_neg : (5844171 / 62500000) ≤ -Real.log (500000 / 549009) ∧
    -Real.log (500000 / 549009) ≤ (93506737 / 1000000000) := by
  have h := checkLog_sound (w := (49009 / 1049009)) (n := 12)
    (lo := (5844171 / 62500000)) (hi := (93506737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549009 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549009 / 500000) = 1/(500000 / 549009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6192 : Bounds (5844171 / 62500000) (93506737 / 1000000000) (Real.log (549009 / 500000)) := by
  have h := reflection_log_6192_neg
  have he : Real.log (549009 / 500000) = -Real.log (500000 / 549009) := by
    rw [show ((549009 / 500000) : ℝ) = ((500000 / 549009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6193_neg : (51580357 / 500000000) ≤ -Real.log (450991 / 500000) ∧
    -Real.log (450991 / 500000) ≤ (20632143 / 200000000) := by
  have h := checkLog_sound (w := (49009 / 950991)) (n := 12)
    (lo := (51580357 / 500000000)) (hi := (20632143 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450991) = 1/(450991 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6193 : Bounds (-20632143 / 200000000) (-51580357 / 500000000) (Real.log (450991 / 500000)) := by
  have h := reflection_log_6193_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6194_neg : (4826989 / 500000000) ≤ -Real.log (247598117919 / 250000000000) ∧
    -Real.log (247598117919 / 250000000000) ≤ (9653979 / 1000000000) := by
  have h := checkLog_sound (w := (2401882081 / 497598117919)) (n := 12)
    (lo := (4826989 / 500000000)) (hi := (9653979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247598117919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247598117919) = 1/(247598117919 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6194 : Bounds (-9653979 / 1000000000) (-4826989 / 500000000) (Real.log (247598117919 / 250000000000)) := by
  have h := reflection_log_6194_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6195_neg : (1921109 / 200000000) ≤ -Real.log (990440440471 / 1000000000000) ∧
    -Real.log (990440440471 / 1000000000000) ≤ (4802773 / 500000000) := by
  have h := checkLog_sound (w := (9559559529 / 1990440440471)) (n := 12)
    (lo := (1921109 / 200000000)) (hi := (4802773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990440440471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990440440471) = 1/(990440440471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6195 : Bounds (-4802773 / 500000000) (-1921109 / 200000000) (Real.log (990440440471 / 1000000000000)) := by
  have h := reflection_log_6195_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6196_neg : (196172709 / 1000000000) ≤ -Real.log (500000000000 / 608368514797) ∧
    -Real.log (500000000000 / 608368514797) ≤ (19617271 / 100000000) := by
  have h := checkLog_sound (w := (108368514797 / 1108368514797)) (n := 12)
    (lo := (196172709 / 1000000000)) (hi := (19617271 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608368514797 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608368514797 / 500000000000) = 1/(500000000000 / 608368514797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6196 : Bounds (196172709 / 1000000000) (19617271 / 100000000) (Real.log (608368514797 / 500000000000)) := by
  have h := reflection_log_6196_neg
  have he : Real.log (608368514797 / 500000000000) = -Real.log (500000000000 / 608368514797) := by
    rw [show ((608368514797 / 500000000000) : ℝ) = ((500000000000 / 608368514797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6197_neg : (196667451 / 1000000000) ≤ -Real.log (250000000000 / 304334787169) ∧
    -Real.log (250000000000 / 304334787169) ≤ (49166863 / 250000000) := by
  have h := checkLog_sound (w := (54334787169 / 554334787169)) (n := 12)
    (lo := (196667451 / 1000000000)) (hi := (49166863 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304334787169 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304334787169 / 250000000000) = 1/(250000000000 / 304334787169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6197 : Bounds (196667451 / 1000000000) (49166863 / 250000000) (Real.log (304334787169 / 250000000000)) := by
  have h := reflection_log_6197_neg
  have he : Real.log (304334787169 / 250000000000) = -Real.log (250000000000 / 304334787169) := by
    rw [show ((304334787169 / 250000000000) : ℝ) = ((250000000000 / 304334787169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6198_neg : (6153311 / 15625000) ≤ -Real.log (50000000000 / 74131082423) ∧
    -Real.log (50000000000 / 74131082423) ≤ (78762381 / 200000000) := by
  have h := checkLog_sound (w := (24131082423 / 124131082423)) (n := 12)
    (lo := (6153311 / 15625000)) (hi := (78762381 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74131082423 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74131082423 / 50000000000) = 1/(50000000000 / 74131082423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6198 : Bounds (6153311 / 15625000) (78762381 / 200000000) (Real.log (74131082423 / 50000000000)) := by
  have h := reflection_log_6198_neg
  have he : Real.log (74131082423 / 50000000000) = -Real.log (50000000000 / 74131082423) := by
    rw [show ((74131082423 / 50000000000) : ℝ) = ((50000000000 / 74131082423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6199_neg : (98504941 / 250000000) ≤ -Real.log (62500000000 / 92683116077) ∧
    -Real.log (62500000000 / 92683116077) ≤ (78803953 / 200000000) := by
  have h := checkLog_sound (w := (30183116077 / 155183116077)) (n := 12)
    (lo := (98504941 / 250000000)) (hi := (78803953 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92683116077 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92683116077 / 62500000000) = 1/(62500000000 / 92683116077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6199 : Bounds (98504941 / 250000000) (78803953 / 200000000) (Real.log (92683116077 / 62500000000)) := by
  have h := reflection_log_6199_neg
  have he : Real.log (92683116077 / 62500000000) = -Real.log (62500000000 / 92683116077) := by
    rw [show ((92683116077 / 62500000000) : ℝ) = ((62500000000 / 92683116077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6200_neg : (177811401 / 1000000000) ≤ -Real.log (5000 / 5973) ∧
    -Real.log (5000 / 5973) ≤ (88905701 / 500000000) := by
  have h := checkLog_sound (w := (973 / 10973)) (n := 12)
    (lo := (177811401 / 1000000000)) (hi := (88905701 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5973 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5973 / 5000) = 1/(5000 / 5973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6200 : Bounds (177811401 / 1000000000) (88905701 / 500000000) (Real.log (5973 / 5000)) := by
  have h := reflection_log_6200_neg
  have he : Real.log (5973 / 5000) = -Real.log (5000 / 5973) := by
    rw [show ((5973 / 5000) : ℝ) = ((5000 / 5973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6201_neg : (21641623 / 100000000) ≤ -Real.log (4027 / 5000) ∧
    -Real.log (4027 / 5000) ≤ (216416231 / 1000000000) := by
  have h := checkLog_sound (w := (973 / 9027)) (n := 12)
    (lo := (21641623 / 100000000)) (hi := (216416231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4027) = 1/(4027 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6201 : Bounds (-216416231 / 1000000000) (-21641623 / 100000000) (Real.log (4027 / 5000)) := by
  have h := reflection_log_6201_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6202_neg : (194581 / 1000000000) ≤ -Real.log (5000000 / 5000973) ∧
    -Real.log (5000000 / 5000973) ≤ (97291 / 500000000) := by
  have h := checkLog_sound (w := (973 / 10000973)) (n := 12)
    (lo := (194581 / 1000000000)) (hi := (97291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000973 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000973 / 5000000) = 1/(5000000 / 5000973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6202 : Bounds (194581 / 1000000000) (97291 / 500000000) (Real.log (5000973 / 5000000)) := by
  have h := reflection_log_6202_neg
  have he : Real.log (5000973 / 5000000) = -Real.log (5000000 / 5000973) := by
    rw [show ((5000973 / 5000000) : ℝ) = ((5000000 / 5000973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6203_neg : (97309 / 500000000) ≤ -Real.log (4999027 / 5000000) ∧
    -Real.log (4999027 / 5000000) ≤ (194619 / 1000000000) := by
  have h := checkLog_sound (w := (973 / 9999027)) (n := 12)
    (lo := (97309 / 500000000)) (hi := (194619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999027) = 1/(4999027 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6203 : Bounds (-194619 / 1000000000) (-97309 / 500000000) (Real.log (4999027 / 5000000)) := by
  have h := reflection_log_6203_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6204_neg : (46665019 / 500000000) ≤ -Real.log (31250 / 34307) ∧
    -Real.log (31250 / 34307) ≤ (93330039 / 1000000000) := by
  have h := checkLog_sound (w := (3057 / 65557)) (n := 12)
    (lo := (46665019 / 500000000)) (hi := (93330039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34307 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34307 / 31250) = 1/(31250 / 34307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6204 : Bounds (46665019 / 500000000) (93330039 / 1000000000) (Real.log (34307 / 31250)) := by
  have h := reflection_log_6204_neg
  have he : Real.log (34307 / 31250) = -Real.log (31250 / 34307) := by
    rw [show ((34307 / 31250) : ℝ) = ((31250 / 34307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6205_neg : (12868207 / 125000000) ≤ -Real.log (28193 / 31250) ∧
    -Real.log (28193 / 31250) ≤ (102945657 / 1000000000) := by
  have h := checkLog_sound (w := (3057 / 59443)) (n := 12)
    (lo := (12868207 / 125000000)) (hi := (102945657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 28193) = 1/(28193 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6205 : Bounds (-102945657 / 1000000000) (-12868207 / 125000000) (Real.log (28193 / 31250)) := by
  have h := reflection_log_6205_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6206_neg : (46776591 / 500000000) ≤ -Real.log (1000000 / 1098069) ∧
    -Real.log (1000000 / 1098069) ≤ (93553183 / 1000000000) := by
  have h := checkLog_sound (w := (98069 / 2098069)) (n := 12)
    (lo := (46776591 / 500000000)) (hi := (93553183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098069 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098069 / 1000000) = 1/(1000000 / 1098069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6206 : Bounds (46776591 / 500000000) (93553183 / 1000000000) (Real.log (1098069 / 1000000)) := by
  have h := reflection_log_6206_neg
  have he : Real.log (1098069 / 1000000) = -Real.log (1000000 / 1098069) := by
    rw [show ((1098069 / 1000000) : ℝ) = ((1000000 / 1098069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6207_neg : (51608629 / 500000000) ≤ -Real.log (901931 / 1000000) ∧
    -Real.log (901931 / 1000000) ≤ (103217259 / 1000000000) := by
  have h := checkLog_sound (w := (98069 / 1901931)) (n := 12)
    (lo := (51608629 / 500000000)) (hi := (103217259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901931) = 1/(901931 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6207 : Bounds (-103217259 / 1000000000) (-51608629 / 500000000) (Real.log (901931 / 1000000)) := by
  have h := reflection_log_6207_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


