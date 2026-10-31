-- Prove2me | Definitions.Def_CombOpt_Circulation_IsSolution38
-- name    : CombOpt_Circulation_IsSolution38
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:02:18.386484+00:00
-- url     : https://prove2.me/theorems/d0036b7c-5432-41fb-abc2-b14d075bfbd2
-- title:
--   Solutions of the flow feasibility system (3.8)
-- statement:
--   Given a digraph $G$, finite capacities $u\in\mathbb R^E_+$ and demands $b\in\mathbb R^V$, the system (3.8) asks for $x\in\mathbb R^E$ with
--
--   $$
--   f_x(v)=b_v\ \text{ for all } v\in V,\qquad 0\le x_e\le u_e\ \text{ for all } e\in E.
--   $$
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §3.3, (3.8), p. 54 (PDF p. 63)

import Mathlib
import Definitions.Def_CombOpt_Circulation_MultiDigraph
import Definitions.Def_CombOpt_Circulation_excess

namespace CombOpt.Circulation

variable {V E : Type*} [Fintype E] [DecidableEq V]

/-- `x` solves the flow feasibility system (3.8) of Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §3.3, p. 54 (PDF p. 63): `f_x(v) = b_v`
for all `v ∈ V` and `0 ≤ x_e ≤ u_e` for all `e ∈ E`, with `u ∈ ℝ^E_+` finite and `b ∈ ℝ^V`. -/
def IsSolution38 (G : MultiDigraph V E) (u : E → ℝ) (b : V → ℝ) (x : E → ℝ) : Prop :=
  (∀ v, excess G x v = b v) ∧ ∀ e, 0 ≤ x e ∧ x e ≤ u e

end CombOpt.Circulation


