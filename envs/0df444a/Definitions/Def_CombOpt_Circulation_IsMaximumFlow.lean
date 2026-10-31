-- Prove2me | Definitions.Def_CombOpt_Circulation_IsMaximumFlow
-- name    : CombOpt_Circulation_IsMaximumFlow
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:17.651751+00:00
-- url     : https://prove2.me/theorems/1958d9ab-1602-4f8a-b4e9-ac5a0425cb56
-- title:
--   Maximum $(r,s)$-flows
-- statement:
--   A **maximum $(r,s)$-flow** is a feasible $(r,s)$-flow $x$ with $f_y(s)\le f_x(s)$ for every feasible $(r,s)$-flow $y$.
--
--   When some capacities are infinite a maximum flow need not exist, which is why the max-flow min-cut theorem assumes one.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §3.2, Maximum Flow Problem, p. 39 (PDF p. 48)

import Mathlib
import Definitions.Def_CombOpt_Circulation_MultiDigraph
import Definitions.Def_CombOpt_Circulation_excess
import Definitions.Def_CombOpt_Circulation_IsFeasibleFlow

open scoped ENNReal

namespace CombOpt.Circulation

variable {V E : Type*} [Fintype E] [DecidableEq V]

/-- A maximum `(r, s)`-flow, Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §3.2, Maximum Flow Problem, p. 39 (PDF p. 48): a feasible
`(r, s)`-flow whose value `f_x(s)` is at least the value of every feasible `(r, s)`-flow. With
infinite capacities none need exist, which is why Theorems 3.5 and 3.7 assume one. -/
def IsMaximumFlow (G : MultiDigraph V E) (u : E → ℝ≥0∞) (r s : V) (x : E → ℝ) : Prop :=
  IsFeasibleFlow G u r s x ∧ ∀ y, IsFeasibleFlow G u r s y → excess G y s ≤ excess G x s

end CombOpt.Circulation


