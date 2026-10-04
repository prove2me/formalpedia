-- Prove2me | Definitions.Def_StochApproxDyn_LimitSet_Invariance
-- name    : StochApproxDyn_LimitSet_Invariance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T06:42:12.223766+00:00
-- url     : https://prove2.me/theorems/1400fe07-3a47-475e-816e-44834ee31eb4
-- title:
--   Invariant sets, the restricted semiflow $\Phi|\Lambda$, and omega limit sets
-- statement:
--   Let $\Phi=(\Phi_t)_{t\ge0}$ be a **semiflow** on a metric space $(M,d)$: a continuous map $\mathbb R_+\times M\to M$, $(t,x)\mapsto\Phi_t(x)$, with $\Phi_0=\mathrm{Id}$ and $\Phi_{t+s}=\Phi_t\circ\Phi_s$ for all $t,s\ge0$. This file introduces three notions attached to $\Phi$.
--
--   1. A set $A\subset M$ is **invariant** if
--   $$\Phi_t(A)=A\qquad\text{for all }t\ge0 .$$
--   This is equality, not the weaker inclusion $\Phi_t(A)\subset A$ (positive invariance).
--   2. If $\Lambda$ is invariant, the **restriction** $\Phi|\Lambda$ is the semiflow $(t,x)\mapsto\Phi_t(x)$ on $\Lambda$, viewed as a metric space with the distance inherited from $M$.
--   3. The **omega limit set** of $x\in M$ is the set $\omega(x)$ of all points $p=\lim_{k\to\infty}\Phi_{t_k}(x)$ for some sequence $t_k\to\infty$.
--
--   These are the basic objects of topological dynamics used throughout Section 5 of the notes: chain recurrence and attractors are defined for restricted semiflows $\Phi|\Lambda$ on invariant sets, and $\omega(x)$ is the model case of the limit set theorem.
--
--   **Formalization Note** A semiflow is Mathlib's `Flow ℝ≥0 M`, time is `ℝ≥0`. The restriction is Mathlib's `Flow.restrict` on the subtype `↥Λ`, which only needs $\Phi_t(\Lambda)\subset\Lambda$; that inclusion is derived from invariance. Sequences $t_k$ are indexed by $k\in\mathbb N$ and $t_k\to\infty$ is `Tendsto t atTop atTop`.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 9 (semiflow) and p. 20, Section 5.1 "Basic Notions of Recurrence" (invariant set, omega limit set), p. 21 (restriction Φ|Λ)

import Mathlib

open scoped NNReal

namespace StochApproxDyn.LimitSet

/-- Invariance in the sense of Benaïm (1999), p. 20: a set `A` is *invariant* for the semiflow
`Φ` if `Φ_t(A) = A` for every `t ≥ 0` (equality, not mere inclusion). -/
def IsInvariantSet {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (A : Set M) : Prop :=
  ∀ t : ℝ≥0, Φ t '' A = A

/-- The restriction `Φ|Λ` of a semiflow to an invariant set `Λ`, a semiflow on the subtype `↥Λ`
(with the subspace metric). It only uses `Φ_t(Λ) ⊆ Λ`, which follows from invariance. -/
def restrictSemiflow {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) {Λ : Set M}
    (h : IsInvariantSet Φ Λ) : Flow ℝ≥0 Λ :=
  Φ.restrict (fun t _ hx => h t ▸ Set.mem_image_of_mem (Φ t) hx)

/-- The omega limit set of `x` (p. 20): the set of points `p = lim_k Φ_{t_k}(x)` for some
sequence `t_k → ∞`. -/
def omegaLimitSet {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (x : M) : Set M :=
  {p | ∃ τ : ℕ → ℝ≥0, Filter.Tendsto τ Filter.atTop Filter.atTop ∧
    Filter.Tendsto (fun k => Φ (τ k) x) Filter.atTop (nhds p)}

end StochApproxDyn.LimitSet


