-- Prove2me | Definitions.Def_StochApproxDyn_LimitSet_TranslationSemiflow
-- name    : StochApproxDyn_LimitSet_TranslationSemiflow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T06:42:59.525056+00:00
-- url     : https://prove2.me/theorems/cc86fff8-1c19-446f-80d4-9d9fea37deb5
-- title:
--   The translation semiflow $\Theta$, trajectories $\Phi^p$, the retraction $\hat\Phi$ and the distance on $C^0(\mathbb R_+,M)$
-- statement:
--   Let $\Phi$ be a semiflow on a metric space $(M,d)$ and let $C^0(\mathbb R_+,M)$ be the space of continuous maps $\mathbb R_+\to M$ with the topology of uniform convergence on compact intervals.
--
--   1. The **translation semiflow** is $\Theta^t(Y)(s)=Y(t+s)$ for $t,s\ge0$.
--   2. For $p\in M$, the **trajectory** $\Phi^p\in C^0(\mathbb R_+,M)$ is $\Phi^p(s)=\Phi_s(p)$, and $S_\Phi=\{\Phi^p:p\in M\}$.
--   3. The **retraction** $\hat\Phi:C^0(\mathbb R_+,M)\to S_\Phi$ is $\hat\Phi(Y)=\Phi^{Y(0)}$.
--   4. The **distance**
--   $$d(f,g)=\sum_{k\in\mathbb N}\frac1{2^k}\min\big(1,d_k(f,g)\big),\qquad d_k(f,g)=\sup_{s\in[0,k]}d(f(s),g(s)).$$
--
--   These objects recast asymptotic pseudotrajectories as points of a function space whose forward $\Theta$-orbit is attracted by $S_\Phi$ (Lemma 3.1), which is how the limit set theorem is reduced to a statement about omega limit sets.
--
--   **Formalization Note** The source works on $C^0(\mathbb R,M)$, extending $X$ by $X(t)=X(0)$ and $\Phi^p$ by $\Phi^p(t)=p$ for $t<0$, with $d_k$ a supremum over $[-k,k]$. For a semiflow this extension makes Lemma 3.1 and Theorem 3.2 false: on a periodic orbit, $X(t)=\Phi_t(x)$ is an asymptotic pseudotrajectory, yet $d(X(t+s),\Phi^{X(t)}(s))=d(X(t+s),X(t))$ for $s<0$ does not tend to $0$. The objects are therefore defined on the half-line $\mathbb R_+$, as the source's own remark after Lemma 3.1 ("a point of $C^0(\mathbb R_+,M)$") indicates. $C^0(\mathbb R_+,M)$ is Mathlib's `C(ℝ≥0, M)`, whose compact-open topology is the topology of uniform convergence on compact sets and is metrized by $d$. The sum starts at $k=0$; $d_k$ is a supremum of a continuous function over the nonempty compact interval $[0,k]$, so it is finite and attained.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 10, Section 3.1 (C⁰(ℝ, M), the distance d, translation flow Θ, trajectories Φ^p, S_Φ, retraction Φ̂), read on the half-line ℝ₊

import Mathlib

open scoped NNReal

namespace StochApproxDyn.LimitSet

/-- The translation `Θ^t(Y)(s) = Y(t + s)` on `C⁰(ℝ₊, M)`, `t ≥ 0` (Benaïm 1999, p. 10, on the
nonnegative half-line). -/
def translate {M : Type*} [MetricSpace M] (t : ℝ≥0) (Y : C(ℝ≥0, M)) : C(ℝ≥0, M) :=
  Y.comp ⟨fun s => t + s, continuous_const.add continuous_id⟩

/-- The trajectory `Φ^p : s ↦ Φ_s(p)` of `p`, an element of `C⁰(ℝ₊, M)` (p. 10). -/
def trajectory {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (p : M) : C(ℝ≥0, M) :=
  ⟨fun s => Φ s p, Φ.continuous continuous_id continuous_const⟩

/-- `S_Φ`, the set of all trajectories `Φ^p`, `p ∈ M` (p. 10). -/
def trajectorySpace {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) : Set C(ℝ≥0, M) :=
  Set.range (trajectory Φ)

/-- The retraction `Φ̂(Y) = Φ^{Y(0)}` (p. 10). -/
def retraction {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (Y : C(ℝ≥0, M)) : C(ℝ≥0, M) :=
  trajectory Φ (Y 0)

/-- `d_k(f, g) = sup_{s ∈ [0, k]} d(f(s), g(s))` (p. 10, on the nonnegative half-line). The index
set is nonempty and the supremum is of a continuous function on a compact interval, so it is a
genuine supremum. -/
noncomputable def supDistOn {M : Type*} [MetricSpace M] (k : ℕ) (f g : C(ℝ≥0, M)) : ℝ :=
  ⨆ s : Set.Icc (0 : ℝ≥0) (k : ℝ≥0), dist (f s) (g s)

/-- The distance `d(f, g) = Σ_{k ∈ ℕ} 2^{-k} min(1, d_k(f, g))` on `C⁰(ℝ₊, M)` (p. 10); `k`
starts at `0`. The series is summable since its terms are bounded by `2^{-k}`. -/
noncomputable def uniformCompactDist {M : Type*} [MetricSpace M] (f g : C(ℝ≥0, M)) : ℝ :=
  ∑' k : ℕ, (1 / 2 : ℝ) ^ k * min 1 (supDistOn k f g)

end StochApproxDyn.LimitSet


