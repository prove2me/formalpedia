-- Prove2me | Definitions.Def_CombOpt_Circulation_IsCirculation
-- name    : CombOpt_Circulation_IsCirculation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:57.92291+00:00
-- url     : https://prove2.me/theorems/3a334360-1ca0-4f4e-809f-4eaa5c65fb25
-- title:
--   Circulations
-- statement:
--   A **circulation** is a vector $x\in\mathbb R^E$ with $f_x(v)=0$ for all $v\in V$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §3.3, p. 55 (PDF p. 64)

import Mathlib
import Definitions.Def_CombOpt_Circulation_MultiDigraph
import Definitions.Def_CombOpt_Circulation_excess

namespace CombOpt.Circulation

variable {V E : Type*} [Fintype E] [DecidableEq V]

/-- A circulation, Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §3.3, p. 55 (PDF p. 64): "a vector `x ∈ ℝ^E` with `f_x(v) = 0` for all
`v ∈ V`". -/
def IsCirculation (G : MultiDigraph V E) (x : E → ℝ) : Prop :=
  ∀ v, excess G x v = 0

end CombOpt.Circulation


