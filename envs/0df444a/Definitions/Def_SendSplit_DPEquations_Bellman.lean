-- Prove2me | Definitions.Def_SendSplit_DPEquations_Bellman
-- name    : SendSplit_DPEquations_Bellman
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:00:30.382706+00:00
-- url     : https://prove2.me/theorems/1950c7a7-4d09-4672-bde2-0dc5252672bb
-- title:
--   Eq. (2)′ — simple circuits, circuit costs, and +∞-or-real solutions of Bellman's equations for minimum-cost chains
-- statement:
--   This file states Bellman's equations for minimum-cost chains to a fixed node, in the form (2)′ used in the proof of Theorem 2.
--
--   Let $G$ be a finite directed graph with arc set $\mathcal{A}$, real arc costs $a_{kj}$ for $(k,j) \in \mathcal{A}$, and a designated destination node $t$ (the node $v$ of the paper). A **simple circuit** of $G$ is a list of $m \ge 2$ distinct nodes $v_0, \dots, v_{m-1}$ such that $(v_0,v_1), \dots, (v_{m-2},v_{m-1}), (v_{m-1},v_0)$ are arcs; its **cost** is the sum of the costs of these $m$ arcs.
--
--   A **$+\infty$ or real-valued solution of Bellman's equations** is a vector $C = (C_k)$ with every $C_k \in \mathbb{R} \cup \{+\infty\}$, $C_t = 0$, and
--
--   $$C_k \;=\; \min_{(k,j) \in \mathcal{A}} \bigl[ a_{kj} + C_j \bigr] \qquad \text{for every node } k \neq t ,$$
--
--   the minimum over no arcs being $+\infty$.
--
--   In the paper the graph is $G'_I = (N \cup \{v\}, A_I \cup (N \times \{v\}))$ with costs $c_{ij}(r_I)$ on $A_I$ and $B_{iI}$ on $(i, v)$, and (2) becomes (2)′.
--
--   **Formalization Note** The graph is the platform structure `BertsekasSPGraph` (arc set, real lengths, origin $s$ and destination $t$; the origin plays no role here). An arc cost of $+\infty$ in the paper (for instance $B_{iI} = +\infty$) is represented by the absence of the arc from the arc set.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 642, Eq. (2)′

import Mathlib
import Definitions.Def_BertsekasSPGraph

namespace SendSplit.DPEquations

/-- A simple circuit of the graph `G`: a list of `m ≥ 2` distinct nodes `[v₀, …, v_{m-1}]`
such that `(v₀, v₁), …, (v_{m-2}, v_{m-1}), (v_{m-1}, v₀)` are all arcs of `G`. -/
def IsSimpleCircuit {V : Type} [Fintype V] [DecidableEq V] (G : BertsekasSPGraph V)
    (l : List V) : Prop :=
  l.Nodup ∧ 2 ≤ l.length ∧ List.IsChain (fun x y => (x, y) ∈ G.arcs) (l ++ l.take 1)

/-- The cost of traversing the circuit `[v₀, …, v_{m-1}]`: the length of the closed walk
`(v₀, …, v_{m-1}, v₀)`. -/
def circuitLength {V : Type} [Fintype V] [DecidableEq V] (G : BertsekasSPGraph V)
    (l : List V) : ℝ :=
  BertsekasWalkLength G (l ++ l.take 1)

/-- A `+∞`-or-real-valued solution of Bellman's equations for minimum-cost chains to the
node `t = G.t` (Eq. (2)′, p. 642): `C_t = 0` and, for every node `k ≠ t`,
`C_k = min_{(k,j) ∈ arcs} [a_kj + C_j]`, the minimum over no arcs being `+∞`. -/
def IsBellmanSolution {V : Type} [Fintype V] [DecidableEq V] (G : BertsekasSPGraph V)
    (C : V → EReal) : Prop :=
  (∀ k, C k ≠ ⊥) ∧ C G.t = 0 ∧
    ∀ k, k ≠ G.t →
      C k = (Finset.univ.filter (fun j => (k, j) ∈ G.arcs)).inf
        (fun j => ((G.length k j : ℝ) : EReal) + C j)

end SendSplit.DPEquations


