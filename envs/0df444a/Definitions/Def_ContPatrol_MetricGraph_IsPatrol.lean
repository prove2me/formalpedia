-- Prove2me | Definitions.Def_ContPatrol_MetricGraph_IsPatrol
-- name    : ContPatrol_MetricGraph_IsPatrol
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:12:44.888727+00:00
-- url     : https://prove2.me/theorems/9dab0728-f9be-4abd-af3b-7dd3f9a42b16
-- title:
--   Patrols (unit speed paths) and interception
-- statement:
--   A **patrol** is a path $S(t)$, $t\ge0$, in $Q$ with
--   $$d(S(t),S(t'))\le|t-t'|\qquad\text{for all }t,t'\ge0.$$
--
--   A pure **attack** is a pair $(x,\tau)$: the point $x$ is attacked during the interval $J=[\tau,\tau+\alpha]$. The patrol **intercepts** it if $x\in S(J)$, i.e. $S(t)=x$ for some $t\in[\tau,\tau+\alpha]$. The Patroller's payoff is $1$ on interception and $0$ otherwise.
--
--   **Formalization Note** Times are real numbers; only $t\ge0$ is constrained, and attacks start at $\tau\ge0$.
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, §3, pp.5–6, display (1)

import Mathlib
import Definitions.Def_ContPatrol_MetricGraph_dist

namespace ContPatrol

namespace MetricGraph

variable {V E : Type}

/-- **Patrols.** Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*,
arXiv:2008.07369v2, §3, p.5: "The Patroller chooses a path S(t), where t ≥ 0, which we call a
patrol, satisfying d(S(t), S(t′)) ≤ |t − t′|, for all t, t′ ≥ 0. (1)"

**Formalization Note.** Times are real numbers; only the values at `t ≥ 0` are constrained, and
only those are ever used (attacks start at times `τ ≥ 0`). -/
def IsPatrol (G : MetricGraph V E) (S : ℝ → G.Point) : Prop :=
  ∀ t t' : ℝ, 0 ≤ t → 0 ≤ t' → G.dist (S t) (S t') ≤ |t - t'|

/-- **Interception.** Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*,
arXiv:2008.07369v2, §3, pp.5–6: "A patrol is said to intercept an attack if it visits the attacked
point while it is being attacked", i.e. the payoff is `1` if `x ∈ S(J)` with `J = [τ, τ + α]`.

A pure attack is a pair `a = (x, τ)`: the point `x` attacked during `[τ, τ + α]`. -/
def Intercepts (G : MetricGraph V E) (α : ℝ) (S : ℝ → G.Point) (a : G.Point × ℝ) : Prop :=
  ∃ t ∈ Set.Icc a.2 (a.2 + α), S t = a.1

end MetricGraph

end ContPatrol


