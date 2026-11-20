-- Prove2me | solution 1 for Aggmetrics.DataStream.abrupt_state
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:31:49.268194+00:00
-- url     : https://prove2.me/submissions/48bb6c76-62dc-4fe6-a3b0-a7f7ad9cea85

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℝ V] (α : ℝ) (B : V) (c : ℕ → V)
    (hc : ∀ n, c (n + 1) = α • c n + (1 - α) • B) (n0 s : ℕ) :
    c (n0 + s) = α ^ s • c n0 + (1 - α ^ s) • B := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [← add_assoc, hc, ih]
    module
end Aggmetrics.DataStream
