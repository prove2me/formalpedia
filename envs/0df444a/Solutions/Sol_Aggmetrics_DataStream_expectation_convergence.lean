-- Prove2me | solution 1 for Aggmetrics.DataStream.expectation_convergence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:02:54.101178+00:00
-- url     : https://prove2.me/submissions/4e2350cd-3235-4fb7-9247-81d9d9355a7f

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStream

set_option autoImplicit true
open Finset MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (α c : ℝ) (hα1 : 0 < α) (hα2 : α < 1) :
    Filter.Tendsto (fun t : ℕ => (1 - α ^ t) * c) Filter.atTop (nhds c) := by
  have hpow : Filter.Tendsto (fun t : ℕ => α ^ t) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hα1.le hα2
  have h1 : Filter.Tendsto (fun t : ℕ => 1 - α ^ t) Filter.atTop (nhds (1 - 0)) :=
    Filter.Tendsto.const_sub 1 hpow
  simpa using h1.mul_const c
end Aggmetrics.DataStream
