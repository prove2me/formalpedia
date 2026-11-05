-- Prove2me | solution 1 for AnalyticEnclosures.expPoly_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/9b028715-ec06-43fc-97a1-a418a7a5ecb6

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Definitions.Def_AnalyticEnclosures

set_option autoImplicit true
open AnalyticEnclosures
open scoped BigOperators
namespace AnalyticEnclosures
theorem _root_.solution (x : ℚ) (n : ℕ) :
    (expPoly x n : ℝ) = ∑ i ∈ Finset.range n, (x : ℝ) ^ i / (i.factorial : ℝ) := by
  simp [expPoly]
end AnalyticEnclosures
