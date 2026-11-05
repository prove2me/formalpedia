-- Prove2me | solution 1 for AnalyticEnclosures.log_scale_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/efb942b1-b794-4c5e-a8b2-3affa16407d1

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
theorem _root_.solution (q r L Ltwo : ℝ) (k : ℕ)
    (hr : 0 < r) (hqr : q = (2 : ℝ) ^ k * r)
    (hrL : Real.log r ≤ L) (htwo : Real.log 2 ≤ Ltwo) :
    Real.log q ≤ (k : ℝ) * Ltwo + L := by
  rw [hqr, Real.log_mul (by positivity) hr.ne', Real.log_pow]
  exact add_le_add (mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg k)) hrL
end AnalyticEnclosures
