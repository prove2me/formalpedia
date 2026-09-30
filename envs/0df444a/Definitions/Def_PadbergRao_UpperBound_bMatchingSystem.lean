-- Prove2me | Definitions.Def_PadbergRao_UpperBound_bMatchingSystem
-- name    : PadbergRao_UpperBound_bMatchingSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T23:14:30.99878+00:00
-- url     : https://prove2.me/theorems/6ee85364-2771-4c53-9c10-3cf033886bbf
-- title:
--   The b-matching system with upper bounds (3.1), its slacks, and the blossom inequalities (3.3)
-- statement:
--   Let $G=(V,E)$ be a finite simple undirected graph, let $b\in\mathbb{Z}_{>0}^{V}$ be node capacities and $d\in\mathbb{Z}_{>0}^{E}$ edge upper bounds, and let $A$ be the node–edge incidence matrix of $G$. The **b-matching problem with upper bounds** optimizes over the system
--
--   $$
--   Ax\le b,\qquad x\le d,\qquad x\ge 0 \tag{3.1}
--   $$
--
--   and this file fixes the objects needed to talk about a point $\bar x\in\mathbb{R}^{E}$ of its linear relaxation.
--
--   1. $\delta(i)$ is the set of edges incident to node $i$, so $(A\bar x)_i=\sum_{e\in\delta(i)}\bar x_e$.
--   2. For $W\subseteq V$, $E(W)$ is the set of edges with both ends in $W$ and $(W:V-W)$ is the **cut-set** of $W$, the edges with exactly one end in $W$.
--   3. $\bar x$ is **feasible** for (3.1) when $0\le \bar x_e\le d_e$ for every edge $e$ and $(A\bar x)_i\le b_i$ for every node $i$.
--   4. The **slack** of node $i$ is $\bar s_i=b_i-(A\bar x)_i$; for $W\subseteq V$ write $\bar s(W)=\sum_{i\in W}\bar s_i$.
--   5. A pair $(W,T)$ with $W\subseteq V$ and $T\subseteq (W:V-W)$ gives a **violated blossom inequality** when $b(W)+d(T)=\sum_{i\in W}b_i+\sum_{e\in T}d_e$ is odd and
--
--   $$
--   \bar x(W)+\bar x(T)=\sum_{e\in E(W)}\bar x_e+\sum_{e\in T}\bar x_e>\tfrac12\bigl(b(W)+d(T)-1\bigr),
--   $$
--
--   that is, $\bar x$ violates the blossom (matching) inequality (3.3) $x(W)+x(T)\le\frac12(b(W)+d(T)-1)$, which is valid for every integer solution of (3.1).
--
--   These are the objects of Section 3 of Padberg and Rao: the separation question (Q1) asks for such a pair $(W,T)$ or a proof that none exists.
--
--   **Formalization Note** The graph is a Mathlib `SimpleGraph` on a finite node type, edges are `Sym2 V` elements of `G.edgeFinset`, and $b,d$ are natural-number valued; their positivity is stated as a hypothesis in each theorem, not here. The half $\frac12(b(W)+d(T)-1)$ is computed in $\mathbb{R}$ after casting. When $W=V$ the cut-set is empty, so the paper's convention "if $W=V$, $T$ is taken to be empty" holds automatically.
-- source:
--   Padberg, Rao, Odd Minimum Cut-Sets and b-Matchings, Math. Oper. Res. 7 (1982), p. 74, Section 3, Eq. (3.1), (3.2), (3.3); slacks p. 73 and p. 75

import Mathlib

namespace PadbergRao.UpperBound

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges of `G` incident to node `i`: the support of row `i` of the node–edge incidence
matrix `A`. -/
def incidentEdges (G : SimpleGraph V) [DecidableRel G.Adj] (i : V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => i ∈ e)

/-- `E(W)`: the edges of `G` with both ends in `W`. -/
def edgesWithin (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ W)

/-- `(W : V − W)`: the cut-set of `W`, i.e. the edges of `G` with exactly one end in `W`. -/
def cutEdges (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∃ u ∈ e, ∃ v ∈ e, u ∈ W ∧ v ∉ W)

/-- `x̄` is a feasible solution of the linear relaxation of system (3.1):
`0 ≤ x ≤ d` on every edge and `Ax ≤ b` at every node. -/
def IsFeasible (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) : Prop :=
  (∀ e ∈ G.edgeFinset, 0 ≤ x e ∧ x e ≤ (d e : ℝ)) ∧
    ∀ i : V, ∑ e ∈ incidentEdges G i, x e ≤ (b i : ℝ)

/-- The slack `s̄_i = b_i − (Ax̄)_i` of the node constraint at `i`. -/
def slack (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (x : Sym2 V → ℝ) (i : V) : ℝ :=
  (b i : ℝ) - ∑ e ∈ incidentEdges G i, x e

/-- `(W, T)` gives a blossom inequality (3.3) violated by `x̄`: `T ⊆ (W : V − W)`,
`b(W) + d(T)` is odd, and `x̄(W) + x̄(T) > ½(b(W) + d(T) − 1)`, where
`x̄(W) = ∑_{e ∈ E(W)} x̄_e`. -/
def IsViolatedBlossom (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) (W : Finset V) (T : Finset (Sym2 V)) : Prop :=
  T ⊆ cutEdges G W ∧ Odd (∑ i ∈ W, b i + ∑ e ∈ T, d e) ∧
    ((∑ i ∈ W, (b i : ℝ)) + (∑ e ∈ T, (d e : ℝ)) - 1) / 2 <
      (∑ e ∈ edgesWithin G W, x e) + ∑ e ∈ T, x e

end PadbergRao.UpperBound


