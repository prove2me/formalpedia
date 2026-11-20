-- Prove2me | solution 1 for Aggmetrics.DataStream.row_prior_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:31:12.093044+00:00
-- url     : https://prove2.me/submissions/ccf5600a-6075-4193-8ea0-6fcd68fa181c

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamProb

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (π : Fin m → ℝ) (c : Fin m → Fin m → ℝ)
    (hrow : ∀ k, ∑ l, c k l = 1) (k l : Fin m) (hπ : π k ≠ 0) :
    (π k * c k l) / (∑ l', π k * c k l') = c k l := by
  rw [← Finset.mul_sum, hrow k, mul_one]
  exact mul_div_cancel_left₀ _ hπ
end Aggmetrics.DataStream
