-- Prove2me | solution 1 for AnalyticEnclosures.log_le_of_expPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/30c05269-3947-4648-ac3d-d3f499ec3cc3

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
theorem _root_.solution (q L : ℚ) (n : ℕ)
    (hq : 0 < q) (hL : 0 ≤ L) (certificate : q ≤ expPoly L n) :
    Real.log (q : ℝ) ≤ (L : ℝ) := by
  apply (Real.log_le_iff_le_exp (by exact_mod_cast hq)).mpr
  have hcert : (q : ℝ) ≤ (expPoly L n : ℝ) := by exact_mod_cast certificate
  rw [expPoly_cast] at hcert
  exact hcert.trans (Real.sum_le_exp_of_nonneg (by exact_mod_cast hL) n)
end AnalyticEnclosures
