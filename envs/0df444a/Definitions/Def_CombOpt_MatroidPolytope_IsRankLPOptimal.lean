-- Prove2me | Definitions.Def_CombOpt_MatroidPolytope_IsRankLPOptimal
-- name    : CombOpt_MatroidPolytope_IsRankLPOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:08:24.235489+00:00
-- url     : https://prove2.me/theorems/505cb1a0-a9fa-448e-8329-eec518d937ce
-- title:
--   Optimal solution of the rank LP (8.1)
-- statement:
--   The linear program (8.1) is
--   $$\text{maximize } \sum_{e\in S}c_e x_e \quad\text{subject to}\quad x(A)\le r(A)\ (A\subseteq S),\qquad x_e\ge 0\ (e\in S).$$
--   A vector $x$ is an **optimal solution** of (8.1) if it is feasible and $\sum_e c_e y_e\le\sum_e c_e x_e$ for every feasible $y$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.1, (8.1), p. 278 (PDF p. 285)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_rankPolytope

namespace CombOpt.MatroidPolytope

/-- **Optimal solution of the linear program (8.1).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.1, p. 278 (PDF p. 285), (8.1): "Maximize Σ(c_e x_e : e ∈ S) subject to x(A) ≤ r(A), for
all A ⊆ S; x_e ≥ 0, for all e ∈ S."

`IsRankLPOptimal I c x` says that `x` is feasible for (8.1) and that `Σ_e c_e y_e ≤ Σ_e c_e x_e`
for every feasible `y`. -/
def IsRankLPOptimal {α : Type*} [Fintype α] (I : Finset α → Prop) (c : α → ℝ) (x : α → ℝ) :
    Prop :=
  x ∈ rankPolytope I ∧ ∀ y ∈ rankPolytope I, ∑ e, c e * y e ≤ ∑ e, c e * x e

end CombOpt.MatroidPolytope


