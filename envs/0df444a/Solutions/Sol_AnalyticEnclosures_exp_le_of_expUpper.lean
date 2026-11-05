-- Prove2me | solution 1 for AnalyticEnclosures.exp_le_of_expUpper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/59cc11c7-3a0c-4f77-9d9e-5607071031cd

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Definitions.Def_AnalyticEnclosures
import Theorems.Thm_AnalyticEnclosures_expPoly_cast

set_option autoImplicit true
open AnalyticEnclosures
open scoped BigOperators
namespace AnalyticEnclosures
theorem _root_.solution (x U : ℚ) (n : ℕ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hn : 0 < n) (certificate : expUpper x n ≤ U) :
    Real.exp (x : ℝ) ≤ (U : ℝ) := by
  have h := Real.exp_bound' (x := (x : ℝ)) (by exact_mod_cast hx)
    (by exact_mod_cast hx1) hn
  have he : (expUpper x n : ℝ) =
      (∑ i ∈ Finset.range n, (x : ℝ) ^ i / (i.factorial : ℝ)) +
        (x : ℝ) ^ n * (n + 1) / ((n.factorial : ℝ) * n) := by
    simp [expUpper, expPoly_cast]
  rw [← he] at h
  exact h.trans (by exact_mod_cast certificate)
end AnalyticEnclosures
