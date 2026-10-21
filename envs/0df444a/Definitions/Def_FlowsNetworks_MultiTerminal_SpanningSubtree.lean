-- Prove2me | Definitions.Def_FlowsNetworks_MultiTerminal_SpanningSubtree
-- name    : FlowsNetworks_MultiTerminal_SpanningSubtree
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:37:22.624784+00:00
-- url     : https://prove2.me/theorems/1662e503-d034-470a-b737-4adcb22c5d36
-- title:
--   Spanning subtrees, their length, maximal spanning subtrees, and condition (1.1) for out-of-tree arcs
-- statement:
--   Following Chapter IV, §1 of Ford and Fulkerson's *Flows in Networks*, this file sets up the objects of the maximality criterion for spanning subtrees. Throughout, $N$ is a finite set of nodes and graphs are undirected, without loops, with at most one arc joining two nodes.
--
--   1. A **tree** is a connected graph without cycles. A **spanning subtree** of a graph $G$ on $N$ is a tree $T$ on the same node set $N$ obtained from $G$ by deleting arcs, i.e. every arc of $T$ is an arc of $G$. The arcs of $T$ are the **in-tree** arcs, the remaining arcs of $G$ the **out-of-tree** arcs.
--   2. Each arc $\{x, y\}$ carries a real number $a(x, y)$, its **length**. The length of a graph $T$ is
--   $$a(T) = \sum_{\{x, y\} \text{ an arc of } T} a(x, y).$$
--   3. A spanning subtree $T$ of $G$ is **maximal** if $a(T') \le a(T)$ for every spanning subtree $T'$ of $G$.
--   4. **Condition (1.1) for each out-of-tree arc**: for every arc $\{x_1, x_k\}$ of $G$ that is not an arc of $T$, with $x_1, x_2, \dots, x_k$ the chain of in-tree arcs joining $x_1$ and $x_k$,
--   $$a(x_1, x_k) \le \min\,[a(x_1, x_2), a(x_2, x_3), \dots, a(x_{k-1}, x_k)].$$
--
--   These are the objects of Theorem 1.1, the cycle criterion for a maximal spanning subtree, which Chapter IV uses to build trees realizing flow functions.
--
--   **Formalization Note** Graphs are Mathlib `SimpleGraph N` on a `Fintype` with decidable equality; "spanning subtree" is `T ≤ G ∧ T.IsTree`. Lengths are a function on unordered pairs `Sym2 N`; values at pairs that are not arcs play no role. The chain of in-tree arcs is any path in $T$ from $x_1$ to $x_k$ (unique, as $T$ is a tree), and the minimum over the chain is written as "at most the length of every arc of the path".
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter IV, pp. 2–3 (§1, trees, spanning subtrees, in-tree and out-of-tree arcs, lengths, maximal spanning subtrees, Eq. (1.1))

import Mathlib

namespace FlowsNetworks.MultiTerminal

variable {N : Type} [Fintype N] [DecidableEq N]

/-- `T` is a spanning subtree of the undirected graph `G` (Ford–Fulkerson, *Flows in Networks*,
Chapter IV, §1, p. 2): `T` is obtained from `G` by deleting arcs (`T ≤ G`, on the same node set
`N`) and `T` is a tree, i.e. a connected graph without cycles. The arcs of `T` are the "in-tree"
arcs, the other arcs of `G` the "out-of-tree" arcs (p. 3). -/
def IsSpanningSubtree (G T : SimpleGraph N) : Prop :=
  T ≤ G ∧ T.IsTree

open Classical in
/-- The length of a graph `T` for the real arc lengths `a(x, y)` (Chapter IV, §1, p. 3): the sum
of `a` over the arcs of `T`. Lengths are indexed by unordered pairs `s(x, y)`, since the arcs are
undirected; values of `a` at pairs that are not arcs of `T` play no role. -/
noncomputable def length (a : Sym2 N → ℝ) (T : SimpleGraph N) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e : Sym2 N => e ∈ T.edgeSet), a e

/-- `T` is a maximal ("longest") spanning subtree of `G` for the lengths `a` (Chapter IV, §1,
p. 3): it is a spanning subtree of `G`, and no spanning subtree of `G` has larger length. -/
def IsMaximalSpanningSubtree (G T : SimpleGraph N) (a : Sym2 N → ℝ) : Prop :=
  IsSpanningSubtree G T ∧ ∀ T' : SimpleGraph N, IsSpanningSubtree G T' → length a T' ≤ length a T

/-- Condition (1.1) for every out-of-tree arc (Chapter IV, §1, p. 3): for every arc `(x₁, x_k)` of
`G` that is not an arc of `T`, and the chain `x₁, x₂, …, x_k` of in-tree arcs joining `x₁` and
`x_k`, `a(x₁, x_k) ≤ min [a(x₁, x₂), a(x₂, x₃), …, a(x_{k−1}, x_k)]`, i.e. `a(x₁, x_k)` is at most
the length of each arc of that chain. The chain is any path from `x₁` to `x_k` in `T` (in a tree
it is unique). -/
def OutOfTreeCondition (G T : SimpleGraph N) (a : Sym2 N → ℝ) : Prop :=
  ∀ x y : N, G.Adj x y → ¬ T.Adj x y →
    ∀ p : T.Walk x y, p.IsPath → ∀ e ∈ p.edges, a s(x, y) ≤ a e

end FlowsNetworks.MultiTerminal


