-- Prove2me | solution 1 for Aggmetrics.DataStream.outlier_response
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:33:04.230848+00:00
-- url     : https://prove2.me/submissions/dfc352ee-69c8-4888-904b-eb66b5cd9673

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℝ V] (α : ℝ) (n0 : ℕ) (s : V)
    (c : ℕ → V) (hc : ∀ n, c (n + 1) = α • c n + (1 - α) • (if n = n0 then s else 0))
    (h0 : c n0 = 0) (k : ℕ) :
    c (n0 + 1 + k) = ((1 - α) * α ^ k) • s := by
  induction k with
  | zero =>
    simp only [add_zero]
    rw [hc, h0]
    simp
  | succ k ih =>
    rw [← add_assoc, hc, ih, if_neg (by omega)]
    module
end Aggmetrics.DataStream
