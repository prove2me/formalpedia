-- Prove2me | Definitions.Def_CombOpt_Circulation_IsFlow
-- name    : CombOpt_Circulation_IsFlow
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:02:00.022551+00:00
-- url     : https://prove2.me/theorems/a848f11f-f54a-4e60-9cbd-7d7248335546
-- title:
--   $(r,s)$-flows
-- statement:
--   A vector $x\in\mathbb R^E$ is an **$(r,s)$-flow** if $f_x(v)=0$ for all $v\in V\setminus\{r,s\}$. The **value** of $x$ is $f_x(s)$.
--
--   No sign or capacity constraint is part of this notion; feasibility adds them.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §3.2, (3.1), p. 38 (PDF p. 47)

import Mathlib
import Definitions.Def_CombOpt_Circulation_MultiDigraph
import Definitions.Def_CombOpt_Circulation_excess

namespace CombOpt.Circulation

variable {V E : Type*} [Fintype E] [DecidableEq V]

/-- `x ∈ ℝ^E` is an `(r, s)`-flow, Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §3.2, (3.1), p. 38 (PDF p. 47): `f_x(v) = 0` for all
`v ∈ V \ {r, s}`. The value of `x` is `f_x(s)`, that is `excess G x s`. -/
def IsFlow (G : MultiDigraph V E) (r s : V) (x : E → ℝ) : Prop :=
  ∀ v, v ≠ r → v ≠ s → excess G x v = 0

end CombOpt.Circulation


