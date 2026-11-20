-- Prove2me | solution 1 for Aggmetrics.DataStream.tracking_lag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:30:45.067821+00:00
-- url     : https://prove2.me/submissions/35ec2824-460a-4abc-a463-fe3e9ba7a0e1

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (α a d : ℝ) (h1 : α < 1) (c : ℕ → ℝ)
    (hc : ∀ n, c (n + 1) = α * c n + (1 - α) * (a + (n + 1 : ℕ) * d)) (n : ℕ) :
    c n - (a + n * d) = -(α * d) / (1 - α) + α ^ n * (c 0 - a + α * d / (1 - α)) := by
  have h1a : (1 - α) ≠ 0 := by linarith
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [hc n]
    push_cast
    have e : c n = a + n * d - α * d / (1 - α) + α ^ n * (c 0 - a + α * d / (1 - α)) := by
      have := ih
      field_simp at this ⊢
      linarith
    rw [e]
    field_simp
    ring
end Aggmetrics.DataStream
