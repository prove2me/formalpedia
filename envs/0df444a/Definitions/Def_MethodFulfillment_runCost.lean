-- Prove2me | Definitions.Def_MethodFulfillment_runCost
-- name    : MethodFulfillment_runCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:10.470203+00:00
-- url     : https://prove2.me/theorems/35ddc18f-8e6d-43d0-a334-dfe75a3350aa
-- title:
--   Cost of a run
-- statement:
--   The **cost of a run** is the sum, over periods with an arrival of type $q$, of the cost $c_{m\cap A}$ of the method actually used: the drawn method $m$ if it was accepted, the submethod $m\cap A$ otherwise. Periods without an arrival cost nothing.
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), §2, p.8; Algorithm 1, p.13

import Mathlib
import Definitions.Def_MethodFulfillment_Instance
import Definitions.Def_MethodFulfillment_Run

namespace MethodFulfillment

/-- The platform's cost on a run (Amil, Makhdoumi & Wei, manuscript, PDF sha256 197c13b9…, §2,
p.8, and Algorithm 1, p.13): in each period with an arrival `q`, the cost `c q (m ∩ A)` of the
method actually used (the drawn method if accepted, the submethod `m ∩ A` otherwise); `0` in
periods without an arrival. -/
def runCost {I K Q : Type} [DecidableEq I] [DecidableEq K] {T : ℕ} (P : Instance I K Q T)
    (r : Run I K Q T) : ℝ :=
  ∑ t, match (r t).1 with
    | none => 0
    | some q => P.c q ((r t).2.1 ∩ (r t).2.2)

end MethodFulfillment


