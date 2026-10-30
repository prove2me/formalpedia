-- Prove2me | Definitions.Def_OfflineStochMatching_UnitPatience_IsLPFeasible
-- name    : OfflineStochMatching_UnitPatience_IsLPFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:30:36.662039+00:00
-- url     : https://prove2.me/theorems/3ebb2dd1-aa22-46ca-9b05-8c0962fc3b33
-- title:
--   Feasible solution of the LP relaxation (3)
-- statement:
--   The weighted stochastic graph $G=(V,E)$ is finite; each edge $e$ has two distinct endpoints, a real weight $w_e$ and an activation probability $p_e\in[0,1]$, and each vertex $v$ a patience $t_v\in\mathbb N\cup\{\infty\}$; $\delta(x)$ is the set of edges incident to $x$.
--
--   A vector $y\in\mathbb R^E$ is **feasible for the LP relaxation (3)** if, with $z_e=y_ep_e$ (3d),
--
--   $$
--   0\le y_e\le 1\ (e\in E),\qquad \sum_{e\in\delta(v)} z_e\le 1\ (v\in V),\qquad \sum_{e\in\delta(v)} y_e\le t_v\ (v\in V).
--   $$
--
--   Here $y_e$ is the probability of probing $e$ and $z_e$ the probability of matching it; (3a) and (3b) are the matching and patience constraints in expectation.
--
--   **Formalization Note** The variable $z$ is eliminated through (3d). The patience constraint (3b) is imposed at vertices of finite patience only; at $t_v=\infty$ it is vacuous.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, §2, p. 7, LP (3), constraints (3a)–(3d)

import Mathlib
import Definitions.Def_OfflineStochMatching_UnitPatience_incident

namespace OfflineStochMatching.UnitPatience

/-- **Feasibility for the LP relaxation (3).**
Brubach, Grammel, Ma, MacRury, Srinivasan, *Improved Guarantees for Offline Stochastic Matching via
New Ordered Contention Resolution Schemes*, arXiv:2106.06892v3, §2, p. 7, LP (3):
`LP := max Σ_{e∈E} w_e z_e` subject to (3a) `Σ_{e∈δ(v)} z_e ≤ 1 ∀v ∈ V`;
(3b) `Σ_{e∈δ(v)} y_e ≤ t_v ∀v ∈ V`; (3c) `0 ≤ y_e ≤ 1 ∀e ∈ E`; (3d) `z_e = y_e p_e ∀e ∈ E`.

`IsLPFeasible G y` says that `y : E → ℝ` (with `z_e := y_e p_e` substituted from (3d)) satisfies
(3c), (3a) and (3b).

**Formalization Note.** The variable `z` is eliminated through (3d). Constraint (3b) is imposed
only at vertices of finite patience: at `t_v = ∞` it is vacuous, as in the paper. -/
def IsLPFeasible {V E : Type*} [Fintype E] [DecidableEq V] (G : StochGraph V E) (y : E → ℝ) :
    Prop :=
  (∀ e, 0 ≤ y e ∧ y e ≤ 1) ∧
  (∀ x, ∑ e ∈ incident G x, y e * G.p e ≤ 1) ∧
  (∀ x (n : ℕ), G.t x = n → ∑ e ∈ incident G x, y e ≤ n)

end OfflineStochMatching.UnitPatience


