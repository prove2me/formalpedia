-- Prove2me | Definitions.Def_PadbergRao_OddCut_IsOddCutTree
-- name    : PadbergRao_OddCut_IsOddCutTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T22:53:34.455986+00:00
-- url     : https://prove2.me/theorems/cf319a03-8fe5-43a0-8bfe-228eb31ef354
-- title:
--   The Gomory–Hu cut-tree $G_T$ of $G$ for the odd nodes, its subtrees and edge weights $d_f$
-- statement:
--   Let $V_1$ be the (nonempty) set of odd-labelled nodes of $G$. A **cut-tree** $G_T = (N, F)$ for the odd nodes, as produced by the Gomory–Hu algorithm applied to all pairs of odd nodes, consists of:
--
--   1. a tree whose node set $N$ is in bijection with $V_1$: every tree node corresponds to one or several nodes of $G$ and contains exactly one odd node, so we identify each tree node with the odd node it contains;
--   2. an assignment $\pi : V \to V_1$ sending each node $v$ of $G$ to the tree node containing it, with $\pi(r) = r$ for every odd node $r$.
--
--   For a tree edge $f = [r, s] \in F$, removing $f$ splits $G_T$ into two subtrees; the **$r$-side subtree** $N_1$ is the set of tree nodes still reachable from $r$, and its **cardinality** is its number of tree nodes. The corresponding node set of $G$ is the **shore** $M = \{ v \in V : \pi(v) \in N_1 \}$, and the **weight** of $f$ is
--
--   $$
--   d_f \;=\; c(M : V - M).
--   $$
--
--   The defining property of the cut-tree (Gomory–Hu; Hu, Theorem 9.2) is that for every tree edge $f = [r, s]$ the cut-set $(M : V - M)$ is a minimum cut-set of $G$ separating the odd nodes $r$ and $s$:
--
--   $$
--   d_f \;\le\; c(U : V - U) \quad \text{for every } U \subseteq V \text{ with } r \in U,\ s \notin U.
--   $$
--
--   **Formalization Note** The tree is a `SimpleGraph` `H` on the subtype `{v // v ∈ odd}`; `IsOddCutTree c odd H π` states (1) `H.IsTree`, (2) `π r = r` for every odd `r`, and (3) the Gomory–Hu minimality above for every tree edge. `subtree H r s` is the set of tree nodes reachable from `r` in `H` with the edge `[r, s]` deleted, `shore H π r s` its preimage under `π`, and `treeEdgeWeight c H π r s` the cut capacity of the shore. The existence of such a tree (the Gomory–Hu theorem) is not asserted here.
-- source:
--   Padberg, Rao, Odd Minimum Cut-Sets and b-Matchings, Math. Oper. Res. 7 (1982), p. 70, Section 1 (the cut-tree G_T, citing Hu, Theorem 9.2)

import Mathlib
import Definitions.Def_PadbergRao_OddCut_cutCapacity

namespace PadbergRao.OddCut

/-- For an edge `[r, s]` of a graph `H` on the odd nodes, the `r`-side subtree: the tree nodes
still reachable from `r` once the edge `[r, s]` is removed. Its cardinality is the number of
tree nodes it contains. Padberg–Rao 1982, p. 70, Section 1. -/
noncomputable def subtree {V : Type*} {odd : Finset V} (H : SimpleGraph {v // v ∈ odd})
    (r s : {v // v ∈ odd}) : Finset {v // v ∈ odd} := by
  classical
  exact Finset.univ.filter fun t => (H.deleteEdges {s(r, s)}).Reachable r t

/-- The shore in `G` of the `r`-side subtree: the nodes `v` of `G` whose tree node `π v`
lies in `subtree H r s`. Padberg–Rao 1982, p. 70, Section 1 (the set `M` corresponding to `N₁`). -/
noncomputable def shore {V : Type*} [Fintype V] [DecidableEq V] {odd : Finset V}
    (H : SimpleGraph {v // v ∈ odd}) (π : V → {v // v ∈ odd}) (r s : {v // v ∈ odd}) :
    Finset V :=
  Finset.univ.filter fun v => π v ∈ subtree H r s

/-- The weight `d_f` of the tree edge `f = [r, s]`: the capacity of the cut-set of `G`
defined by removing `f`. Padberg–Rao 1982, p. 70, Section 1. -/
noncomputable def treeEdgeWeight {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ)
    {odd : Finset V} (H : SimpleGraph {v // v ∈ odd}) (π : V → {v // v ∈ odd})
    (r s : {v // v ∈ odd}) : ℝ :=
  cutCapacity c (shore H π r s)

/-- `(H, π)` is a Gomory–Hu cut-tree `G_T = (N, F)` of `G` for the odd-labelled nodes
(the terminals). The tree nodes are identified with the odd nodes (each node of `N` contains
exactly one odd node), `π v` is the tree node containing the node `v` of `G`, and:
1. `H` is a tree on all odd nodes;
2. every odd node lies in its own tree node;
3. for every tree edge `f = [r, s]`, the cut-set obtained by removing `f` is a minimum cut-set
   of `G` separating the odd nodes `r` and `s` (its capacity `d_f` is at most that of every
   cut-set `(U : V − U)` with `r ∈ U`, `s ∉ U`).
Padberg–Rao 1982, p. 70, Section 1 (after Hu, Theorem 9.2). -/
def IsOddCutTree {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ) (odd : Finset V)
    (H : SimpleGraph {v // v ∈ odd}) (π : V → {v // v ∈ odd}) : Prop :=
  H.IsTree ∧
    (∀ r : {v // v ∈ odd}, π r = r) ∧
    ∀ r s : {v // v ∈ odd}, H.Adj r s → ∀ U : Finset V, (r : V) ∈ U → (s : V) ∉ U →
      treeEdgeWeight c H π r s ≤ cutCapacity c U

end PadbergRao.OddCut


