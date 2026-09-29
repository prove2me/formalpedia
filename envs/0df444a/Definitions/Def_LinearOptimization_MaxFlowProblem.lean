-- Prove2me | Definitions.Def_LinearOptimization_MaxFlowProblem
-- name    : LinearOptimization_MaxFlowProblem
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-06T14:35:43.571341+00:00
-- url     : https://prove2.me/theorems/abf74a90-5465-4786-b49e-c61c7eccd07f
-- title:
--   Maximum flow problem
-- statement:
--   **(The maximum flow problem, Bertsimas & Tsitsiklis, §7.5, pp. 301-303)** We are given a directed graph $G=(\mathcal{N},\mathcal{A})$ and an arc capacity bound $u_{ij}\in(0,\infty]$ for each arc $(i,j)\in\mathcal{A}$. Let $s$ and $t$ be two special nodes, called the *source* and *sink* node, respectively. The problem is to find the largest possible amount of flow that can be sent through the network from $s$ to $t$.
--
--   Mathematically (p. 302): maximize $b_s$ subject to
--
--   $$\mathbf{A}\mathbf{f}=\mathbf{b}, \quad b_t=-b_s, \quad b_i=0 \text{ for all } i\ne s,t, \quad\text{and}\quad 0\le f_{ij}\le u_{ij} \text{ for all } (i,j)\in\mathcal{A},$$
--
--   where $\mathbf{A}$ is the node-arc incidence matrix. Here $b_s$ is a variable to be optimized; any flow vector $\mathbf{f}$ satisfying the constraints is called a *feasible flow* and the corresponding value of $b_s$ is called the *value* of that flow (p. 303).
--
--   (The book reduces this to a minimum cost network flow problem by adding a new infinite-capacity arc $(t,s)$ with cost $c_{ts}=-1$ and all other costs zero — the circulation reformulation of p. 303; we take the direct formulation above as primary and record the reformulation as a remark.)
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, §7.5, pp. 301-303 (formulation p. 302; flow value p. 303)

import Definitions.Def_LinearOptimization_NetworkFlowProblem
import Mathlib.Data.EReal.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
The maximum flow problem.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997, §7.5 (pp. 301–303): given a directed graph
`G = (𝒩, 𝒜)`, an arc capacity `uᵢⱼ ∈ (0, ∞]` for each arc, and two
special nodes — a source `s` and a sink `t` — find the largest possible
amount of flow that can be sent through the network from `s` to `t`.
Mathematically (p. 302): maximize `b_s` subject to `Af = b`,
`b_t = −b_s`, `bᵢ = 0` for all `i ≠ s, t`, and `0 ≤ fᵢⱼ ≤ uᵢⱼ` for all
arcs, where `A` is the node-arc incidence matrix. Any flow vector `f`
satisfying the constraints is a *feasible flow*, and the corresponding
`b_s` is its *value* (p. 303). (The book's reduction to a minimum cost
network flow problem via a new infinite-capacity arc `(t, s)` with cost
`−1` — the circulation reformulation, p. 303 — is a remark; the direct
formulation above is primary.)

Design (mission design note): capacities live in `ℝ≥0∞` (`(0, ∞]` per
the book — positivity is an explicit hypothesis of the §7.5 theorems);
flows stay real, compared to capacities via `ENNReal.ofReal`. The value
of a feasible flow is the real `b_s = (Af)_s`; *the value of the maximum
flow* is the supremum of the values of feasible flows taken in the
extended reals (`EReal`) — the zero flow is always feasible (value `0`),
so the supremum is well-defined, `≥ 0`, and never `⊥`; it is `⊤` exactly
when the achievable values are unbounded (which Theorem 7.10(b) shows
happens iff every cut has infinite capacity). The constraint `b_t = −b_s`
is kept explicitly, as printed (it is implied by the others since the
rows of `A` sum to zero).
-/

open Matrix
open scoped ENNReal

namespace LinearOptimization

/-- **Bertsimas & Tsitsiklis, §7.5 (p. 303).** The value of the flow `f` with respect to the
source `s`: the net outflow `b_s = (Af)_s` out of `s`. -/
def flowValue {n m : ℕ} (arcs : Fin m → Fin n × Fin n) (s : Fin n)
    (f : Fin m → ℝ) : ℝ :=
  (incidenceMatrix arcs).mulVec f s

/-- **Bertsimas & Tsitsiklis, §7.5 (p. 302).** `f` is a feasible flow of the maximum flow
problem with capacities `u`, source `s`, and sink `t`: flow is conserved
at every node other than `s` and `t` (`bᵢ = 0`), the divergence at `t` is
the negative of the value at `s` (`b_t = −b_s`), and `0 ≤ f_k ≤ u_k` on
every arc. -/
def IsFeasibleMaxFlow {n m : ℕ} (arcs : Fin m → Fin n × Fin n)
    (u : Fin m → ℝ≥0∞) (s t : Fin n) (f : Fin m → ℝ) : Prop :=
  (∀ i, i ≠ s → i ≠ t → (incidenceMatrix arcs).mulVec f i = 0) ∧
  (incidenceMatrix arcs).mulVec f t = -flowValue arcs s f ∧
  ∀ k, 0 ≤ f k ∧ ENNReal.ofReal (f k) ≤ u k

/-- **Bertsimas & Tsitsiklis, §7.5 (pp. 302–303).** The value of the maximum flow: the
supremum, in the extended reals, of the values of the feasible flows.
The zero flow is feasible, so this is `≥ 0`; it equals `⊤` iff arbitrarily
large amounts of flow can be sent from `s` to `t`. -/
noncomputable def maxFlowValue {n m : ℕ} (arcs : Fin m → Fin n × Fin n)
    (u : Fin m → ℝ≥0∞) (s t : Fin n) : EReal :=
  ⨆ f ∈ {f | IsFeasibleMaxFlow arcs u s t f}, ((flowValue arcs s f : ℝ) : EReal)

end LinearOptimization


