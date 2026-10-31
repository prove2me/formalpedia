-- Prove2me | Definitions.Def_ParamSDPTraj_IsRegularPoint
-- name    : ParamSDPTraj_IsRegularPoint
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:14:50.674173+00:00
-- url     : https://prove2.me/theorems/8c39e37d-8852-48b0-96d7-b7e8a19a3864
-- title:
--   Regular point
-- statement:
--   A pair $(X^*,t^*)$ is a **regular point** of $F$ if $F(t^*)=\{X^*\}$ and there is $\varepsilon>0$ such that:
--
--   1. $F$ is single-valued and continuous at every $t\in(t^*-\varepsilon,t^*+\varepsilon)$;
--   2. $F$ is differentiable at $t^*$.
--
--   **Formalization Note** The definition is stated for a general map $F$, so the primal and dual clauses of Theorem 3.15 share it. The interval is required to lie in $T$; since $T$ is open, $\varepsilon$ can always shrink.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Definition 3.4, p.13

import Mathlib
import Definitions.Def_ParamSDPTraj_SingleValuedAt
import Definitions.Def_ParamSDPTraj_PKContinuousAt
import Definitions.Def_ParamSDPTraj_MapDifferentiableAt

namespace ParamSDPTraj

/-- **Regular point.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Definition 3.4, p.13: "At a regular point (X∗, t∗), P∗(t∗) = {X∗} and there exists ε > 0
such that • P∗(t) is single-valued and continuous for every t ∈ (t∗ − ε, t∗ + ε), for some ε > 0,
• P∗(t) is differentiable at t∗."

**Formalization Note** Stated for a general map `F`, so that the primal and dual clauses of
Theorem 3.15 share it. The interval is required to lie in `T`; T is open, so ε can always shrink. -/
def IsRegularPoint {n : ℕ} (T : Set ℝ) (F : ℝ → Set (Matrix (Fin n) (Fin n) ℝ)) (X : Matrix (Fin n) (Fin n) ℝ) (tstar : ℝ) : Prop :=
  F tstar = {X} ∧ ∃ ε > 0, Set.Ioo (tstar - ε) (tstar + ε) ⊆ T ∧
    (∀ t ∈ Set.Ioo (tstar - ε) (tstar + ε), SingleValuedAt F t ∧ PKContinuousAt T F t) ∧
    MapDifferentiableAt F tstar

end ParamSDPTraj


