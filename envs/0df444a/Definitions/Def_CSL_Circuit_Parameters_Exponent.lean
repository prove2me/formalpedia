-- Prove2me | Definitions.Def_CSL_Circuit_Parameters_Exponent
-- name    : CSL_Circuit_Parameters_Exponent
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:20:48.701897+00:00
-- url     : https://prove2.me/theorems/126d62a4-8994-4676-8ff0-2d57380e3326
-- title:
--   Coded sorting library: Circuit / Parameters / Exponent
-- statement:
--   Module `CodedSorting.Circuit.Parameters.Exponent` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   The exponent 1.5 × 10⁻⁵. This module proves the exponent inequality from the exact stream count and total edge length of the three-copy construction.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Parameters.Exponent

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Parameters_Counts
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The exponent 1.5 × 10⁻⁵. This module proves the exponent inequality from the exact stream count and total edge length of the three-copy construction. 





-/

namespace CSL.Construction

def eta : ℚ := 33 / 338432
def epsilon : ℚ := 3 / 200000

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem epsilon_pos : 0 < epsilon := by norm_num [epsilon]
theorem epsilon_lt_one : epsilon < 1 := by norm_num [epsilon]

theorem eta_identity :
    (1 : ℚ) - (rankBudget : ℚ) / ((streamCount : ℚ) * ambientDimension) = eta := by
  norm_num [rankBudget_eq, streamCount_eq, ambientDimension_eq, eta]

theorem normalized_volume_multiplier :
    (rankBudget : ℚ) / streamCount = (ambientDimension : ℚ) * (1 - eta) := by
  norm_num [rankBudget_eq, streamCount_eq, ambientDimension_eq, eta]

/-- Four terms of the exponential series already give `exp(7/10) > 2`. -/
theorem exponential_series_certificate :
    (2 : ℚ) < ∑ j ∈ Finset.range 4,
      (7 / 10 : ℚ) ^ j / (Nat.factorial j : ℚ) := by
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem logarithm_bound : Real.log (ambientDimension : ℝ) < 63 / 10 := by
  have hs : (2 : ℝ) < ∑ j ∈ Finset.range 4,
      (7 / 10 : ℝ) ^ j / (Nat.factorial j : ℝ) := by
    have hc := (Rat.cast_lt (K := ℝ)).2 exponential_series_certificate
    push_cast at hc
    exact hc
  have hexp : (2 : ℝ) < Real.exp (7 / 10) :=
    lt_of_lt_of_le hs (Real.sum_le_exp_of_nonneg (by norm_num) 4)
  have hlog : Real.log 2 < (7 / 10 : ℝ) :=
    (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).2 hexp
  have hm : (ambientDimension : ℝ) = (2 : ℝ) ^ 9 := by
    norm_num [ambientDimension_eq]
  rw [hm, Real.log_pow]
  norm_num
  linarith

theorem logarithm_margin_certificate : (63 / 10 : ℚ) * epsilon < eta := by
  norm_num [epsilon, eta]

theorem epsilon_log_lt_eta :
    (epsilon : ℝ) * Real.log (ambientDimension : ℝ) < (eta : ℝ) := by
  have heps : (0 : ℝ) < (epsilon : ℝ) := by exact_mod_cast epsilon_pos
  have h₁ := mul_lt_mul_of_pos_left logarithm_bound heps
  have h₂ : (63 / 10 : ℝ) * (epsilon : ℝ) < (eta : ℝ) := by
    norm_num [epsilon, eta]
  nlinarith

theorem strict_exponent_gap :
    (rankBudget : ℝ) / (streamCount : ℝ) <
      (ambientDimension : ℝ) ^ (1 - (epsilon : ℝ)) := by
  have hm : (0 : ℝ) < (ambientDimension : ℝ) := by norm_num [ambientDimension_eq]
  have hid : (rankBudget : ℝ) / (streamCount : ℝ) =
      (ambientDimension : ℝ) * (1 - (eta : ℝ)) := by
    norm_num [rankBudget_eq, streamCount_eq, ambientDimension_eq, eta]
  have hsmall : 1 - (eta : ℝ) <
      Real.exp (-(epsilon : ℝ) * Real.log (ambientDimension : ℝ)) := by
    have hexp := Real.add_one_le_exp (-(epsilon : ℝ) * Real.log (ambientDimension : ℝ))
    have hlog := epsilon_log_lt_eta
    linarith
  calc
    (rankBudget : ℝ) / (streamCount : ℝ) =
        (ambientDimension : ℝ) * (1 - (eta : ℝ)) := hid
    _ < (ambientDimension : ℝ) *
        Real.exp (-(epsilon : ℝ) * Real.log (ambientDimension : ℝ)) :=
      mul_lt_mul_of_pos_left hsmall hm
    _ = (ambientDimension : ℝ) ^ (1 - (epsilon : ℝ)) := by
      rw [Real.rpow_def_of_pos hm]
      have hsplit : Real.log (ambientDimension : ℝ) * (1 - (epsilon : ℝ)) =
          Real.log (ambientDimension : ℝ) +
            (-(epsilon : ℝ) * Real.log (ambientDimension : ℝ)) := by ring
      rw [hsplit, Real.exp_add, Real.exp_log hm]

end CSL.Construction


