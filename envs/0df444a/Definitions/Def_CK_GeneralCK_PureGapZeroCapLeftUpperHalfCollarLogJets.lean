-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarLogJets
-- name    : CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarLogJets
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:23:33.918108+00:00
-- url     : https://prove2.me/theorems/2e91b0c3-6a70-4738-a3b1-b5d836b1248a
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarLogJets` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarLogJets` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarLogJets` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftUpperHalfCollarLogJets (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftUpperHalfCollarLogJets.lean)

import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarBiasGeometry
import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarJetAlgebra

-- ===== source module GeneralCK.PureGapZeroCapLeftUpperHalfCollarLogJets =====
section

/-!
Unconditional real logarithm and actual-law slope estimates for the
left-upper half collar. These estimates contain no Taylor-remainder premise.
They discharge the interior-cost and endpoint-eta components of the C600
draft; the middle-entropy eta and radial-contact components remain separate.
-/

namespace GeneralCK

theorem leftUpper_log_cubic_remainder {x : ℝ} (hx : |x| < 1) :
    |Real.log (1 + x) - (x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4)| ≤
      |x| ^ 5 / (5 * (1 - |x|)) := by
  have hxpos : 0 ≤ 1 + x := by
    have := (abs_lt.mp hx).1
    linarith
  have hpoly : Complex.logTaylor 5 (x : ℂ) =
      ((x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4 : ℝ) : ℂ) := by
    norm_num [Complex.logTaylor, Finset.sum_range_succ]
    ring
  have hlog : Complex.log (1 + (x : ℂ)) = (Real.log (1 + x) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_log hxpos]
  have h := Complex.norm_log_sub_logTaylor_le 4
    (show ‖(x : ℂ)‖ < 1 by simpa using hx)
  rw [hpoly, hlog] at h
  have hc :
      (Real.log (1 + x) : ℂ) -
          ((x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4 : ℝ) : ℂ) =
        ((Real.log (1 + x) - (x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4) : ℝ) : ℂ) :=
    (Complex.ofReal_sub _ _).symm
  rw [hc, Complex.norm_real, Real.norm_eq_abs] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs, Nat.reduceAdd, Nat.cast_ofNat,
    div_eq_mul_inv, mul_inv_rev, show (4 + 1 : ℝ) = 5 by norm_num,
    mul_assoc, mul_comm (5 : ℝ)⁻¹] using h

theorem leftUpper_log_ratio_cubic_remainder {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) :
    |(Real.log (1 + t) - Real.log (1 - t)) -
        (2 * t + 2 * t ^ 3 / 3)| ≤
      2 * t ^ 5 / (5 * (1 - t)) := by
  have hp := leftUpper_log_cubic_remainder (x := t) (by simpa [abs_of_nonneg ht])
  have hm := leftUpper_log_cubic_remainder (x := -t) (by simpa [abs_of_nonneg ht])
  rw [abs_of_nonneg ht] at hp
  rw [abs_neg, abs_of_nonneg ht] at hm
  have habs := abs_sub
    (Real.log (1 + t) - (t - t ^ 2 / 2 + t ^ 3 / 3 - t ^ 4 / 4))
    (Real.log (1 + -t) - (-t - (-t) ^ 2 / 2 + (-t) ^ 3 / 3 - (-t) ^ 4 / 4))
  have heq :
      (Real.log (1 + t) - (t - t ^ 2 / 2 + t ^ 3 / 3 - t ^ 4 / 4)) -
      (Real.log (1 + -t) - (-t - (-t) ^ 2 / 2 + (-t) ^ 3 / 3 - (-t) ^ 4 / 4)) =
      (Real.log (1 + t) - Real.log (1 - t)) - (2 * t + 2 * t ^ 3 / 3) := by
    rw [sub_eq_add_neg (1 : ℝ) t]
    ring
  rw [heq] at habs
  calc
    _ ≤ t ^ 5 / (5 * (1 - t)) + t ^ 5 / (5 * (1 - t)) :=
      habs.trans (add_le_add hp hm)
    _ = 2 * t ^ 5 / (5 * (1 - t)) := by ring

theorem leftUpper_J_half_bias_log {q : ℝ} (hq : q < 1 / 2) (hqlo : -1 / 2 < q) :
    J (1 / 2 - q) =
      (Real.log (1 + 2 * q) - Real.log (1 - 2 * q)) / Real.log 2 := by
  have hm : 1 - 2 * q ≠ 0 := by linarith
  have hp : 1 + 2 * q ≠ 0 := by linarith
  have hqne : (1 / 2 : ℝ) - q ≠ 0 := by linarith
  unfold J
  rw [show (1 - (1 / 2 - q)) / (1 / 2 - q) =
      (1 + 2 * q) / (1 - 2 * q) by field_simp; ring]
  rw [Real.log_div hp hm]

theorem leftUpper_J_half_bias_cubic_remainder {q : ℝ}
    (hq : 0 ≤ q) (hqmax : q ≤ 1 / 64) :
    |J (1 / 2 - q) - (4 * q / Real.log 2 + 16 * q ^ 3 / (3 * Real.log 2))| ≤
      25 * q ^ 5 := by
  have hlog := leftUpper_log_ratio_cubic_remainder
    (show 0 ≤ 2 * q by positivity) (show 2 * q < 1 by linarith)
  have hden : 0 < 5 * (1 - 2 * q) := by linarith
  have hbound : 2 * (2 * q) ^ 5 / (5 * (1 - 2 * q)) ≤ 15 * q ^ 5 := by
    apply (div_le_iff₀ hden).2
    have hcoeff : (64 : ℝ) ≤ 15 * (5 * (1 - 2 * q)) := by linarith
    have hmul := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hq 5)
    nlinarith only [hmul]
  have hL : (3 / 5 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [leftUpper_J_half_bias_log (by linarith) (by linarith)]
  have heq :
      (Real.log (1 + 2 * q) - Real.log (1 - 2 * q)) / Real.log 2 -
        (4 * q / Real.log 2 + 16 * q ^ 3 / (3 * Real.log 2)) =
      ((Real.log (1 + 2 * q) - Real.log (1 - 2 * q)) -
        (2 * (2 * q) + 2 * (2 * q) ^ 3 / 3)) / Real.log 2 := by ring
  rw [heq, abs_div, abs_of_pos log_two_pos]
  apply (div_le_iff₀ log_two_pos).2
  have hmul := mul_le_mul_of_nonneg_right hL (show 0 ≤ 25 * q ^ 5 by positivity)
  nlinarith only [hlog.trans hbound, hmul]

theorem leftUpper_eta_half_bias_quartic_remainder {q : ℝ}
    (hq : 0 ≤ q) (hqmax : q ≤ 1 / 64) :
    |eta (H (1 / 2 - q)) / 2 - leftUpperHalfEtaBJet q (Real.log 2)| ≤
      25 * q ^ 6 := by
  by_cases hzero : q = 0
  · subst q
    norm_num only [sub_zero, H_half, eta_one, zero_div, leftUpperHalfEtaBJet,
      zero_pow, OfNat.ofNat_ne_zero, mul_zero, add_zero, sub_self, abs_zero]
  have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hzero)
  have heta := Comparison.eta_H (show 0 < 1 / 2 - q by linarith)
    (show 1 / 2 - q < 1 / 2 by linarith)
  rw [heta]
  have heq :
      (1 - 2 * (1 / 2 - q)) * J (1 / 2 - q) / 2 -
        leftUpperHalfEtaBJet q (Real.log 2) =
      q * (J (1 / 2 - q) -
        (4 * q / Real.log 2 + 16 * q ^ 3 / (3 * Real.log 2))) := by
    unfold leftUpperHalfEtaBJet
    ring
  rw [heq, abs_mul, abs_of_nonneg hq]
  calc
    _ ≤ q * (25 * q ^ 5) :=
      mul_le_mul_of_nonneg_left (leftUpper_J_half_bias_cubic_remainder hq hqmax) hq
    _ = 25 * q ^ 6 := by ring

theorem leftUpper_interior_half_bias_quartic_remainder {z w : ℝ}
    (hw : 0 ≤ w) (hwz : w ≤ z) (hzmax : z ≤ 1 / 64) :
    |interiorCost (1 / 2 - z) (1 / 2 - w) -
        leftUpperHalfInteriorJet z w (Real.log 2)| ≤ 25 * z ^ 6 := by
  have hz : 0 ≤ z := hw.trans hwz
  have hzJ := leftUpper_J_half_bias_cubic_remainder hz hzmax
  have hwJ := leftUpper_J_half_bias_cubic_remainder hw (hwz.trans hzmax)
  have hdiff : 0 ≤ (z - w) / 2 := by linarith
  have heq :
      interiorCost (1 / 2 - z) (1 / 2 - w) -
        leftUpperHalfInteriorJet z w (Real.log 2) =
      (z - w) / 2 *
        ((J (1 / 2 - z) -
            (4 * z / Real.log 2 + 16 * z ^ 3 / (3 * Real.log 2))) -
          (J (1 / 2 - w) -
            (4 * w / Real.log 2 + 16 * w ^ 3 / (3 * Real.log 2)))) := by
    unfold interiorCost leftUpperHalfInteriorJet
    ring
  rw [heq, abs_mul, abs_of_nonneg hdiff]
  calc
    _ ≤ (z - w) / 2 * (25 * z ^ 5 + 25 * w ^ 5) :=
      mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hzJ hwJ)) hdiff
    _ ≤ z / 2 * (25 * z ^ 5 + 25 * z ^ 5) := by
      gcongr
      · linarith
    _ = 25 * z ^ 6 := by ring

#print axioms leftUpper_log_cubic_remainder
#print axioms leftUpper_log_ratio_cubic_remainder
#print axioms leftUpper_J_half_bias_log
#print axioms leftUpper_J_half_bias_cubic_remainder
#print axioms leftUpper_eta_half_bias_quartic_remainder
#print axioms leftUpper_interior_half_bias_quartic_remainder

end GeneralCK

end


