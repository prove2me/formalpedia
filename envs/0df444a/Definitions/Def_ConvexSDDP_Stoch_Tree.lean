-- Prove2me | Definitions.Def_ConvexSDDP_Stoch_Tree
-- name    : ConvexSDDP_Stoch_Tree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:56:45.233985+00:00
-- url     : https://prove2.me/theorems/d015725d-7ac2-4191-adc8-552c78347384
-- title:
--   §3.1, p. 12 — leaves, ascendents and node probabilities of a scenario tree
-- statement:
--   Let $\mathcal N$ be the finite set of nodes of a rooted scenario tree with root $0$, parent map $p$ and children $r(n)=\{m\neq 0 : p(m)=n\}$ (the platform definition `StochasticProg.Multistage.Tree`).
--
--   1. The set of **leaves** is $\mathcal L=\{n\in\mathcal N : r(n)=\emptyset\}$.
--   2. The set $a(m)$ of **ascendents** of a node $m$ is the set of nodes on the path from the root to $m$, including $m$ and the root:
--   $$a(m)=\{m,\ p(m),\ p(p(m)),\ \dots,\ 0\}.$$
--   3. A family $(\Phi_n)_{n\in\mathcal N}$ is a family of **node probabilities** if
--   $$\Phi_n>0\ \ (n\in\mathcal N),\qquad \Phi_0=1,\qquad \Phi_n=\sum_{m\in r(n)}\Phi_m\ \ (n\in\mathcal N\setminus\mathcal L).$$
--
--   These are the tree notions of §3.1, p. 12: a node represents a time interval and a state of the world, which has probability $\Phi_n$.
--
--   **Formalization Note** In the platform tree every non-root node has a stage one more than its parent, so the path to the root from $m$ has exactly $\mathrm{stage}(m)$ steps; the ascendents are the first $\mathrm{stage}(m)+1$ points of the path (the parent map's value at the root is not part of the tree). The conditions on $\Phi$ are what "node $n$ has probability $\Phi_n$" means on a scenario tree; the paper does not list them separately.
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, p. 12, §3.1

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree

namespace ConvexSDDP.Stoch

open StochasticProg.Multistage

variable {H : ℕ}

/-- §3.1, p. 12: a node `n` of the scenario tree `T` is a *leaf* (`n ∈ ℒ`) when it has no
children, `r(n) = ∅`. The children `r(n)` are `T.children n`, the nodes `m ≠ root` whose
parent `p(m)` (`T.anc m`) is `n`. -/
def IsLeaf (T : Tree H) (n : T.Node) : Prop :=
  T.children n = ∅

/-- §3.1, p. 12: the set `a(m)` of *ascendents* of `m`, the nodes on the path from the root to
`m`, including `m` and the root. Since the parent map lowers the stage by one, the path is
`m, p(m), p(p(m)), …` stopped after `stage m` steps, when it reaches the root (the parent map's
value at the root is not part of the tree). -/
def asc (T : Tree H) (m : T.Node) : Set T.Node :=
  {n | ∃ i : ℕ, i ≤ (T.stage m).val ∧ T.anc^[i] m = n}

/-- §3.1, p. 12: `Φ` is a family of *node probabilities* on the scenario tree `T`: every node
has positive probability, the root has probability one, and the probability of a non-leaf
node is the sum of the probabilities of its children. -/
def IsNodeProb (T : Tree H) (Φ : T.Node → ℝ) : Prop :=
  (∀ n, 0 < Φ n) ∧ Φ T.root = 1 ∧ ∀ n, ¬ IsLeaf T n → ∑ m ∈ T.children n, Φ m = Φ n

end ConvexSDDP.Stoch


