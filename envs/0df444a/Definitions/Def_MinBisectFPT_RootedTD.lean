-- Prove2me | Definitions.Def_MinBisectFPT_RootedTD
-- name    : MinBisectFPT_RootedTD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:22.816196+00:00
-- url     : https://prove2.me/theorems/ddd188df-a87a-423f-a408-45422b1599de
-- title:
--   Rooted tree decomposition: cone $\gamma(t)$, adhesion $\sigma(t)$, component $\alpha(t)$, $G_t$, $B_t$
-- statement:
--   A **rooted tree decomposition** $(T,\beta)$ of $G$ is a tree $T$ with a root and a nonempty bag $\beta(t)\subseteq V(G)$ for each node, satisfying the three axioms of a tree decomposition. For a node $t$:
--
--   1. the **cone** $\gamma(t)$ is the union of the bags in the subtree rooted at $t$;
--   2. the **adhesion** is $\sigma(t):=\beta(t)\cap\beta(t')$, where $t'$ is the parent of $t$, and $\sigma(t):=\emptyset$ at the root;
--   3. the **component** is $\alpha(t):=\gamma(t)\setminus\sigma(t)$;
--   4. the **subtree graph** is $G_t:=G[\gamma(t)]-E(G[\sigma(t)])$, and the **bag graph** is $B_t=G[\beta(t)]-E(G[\sigma(t)])$.
--
--   **Formalization Note** The tree is a parent array with exactly one root, whose graph must be a tree in the sense of the published definition of a tree decomposition (Robertson–Seymour). A tree on $N$ nodes has $N-1$ edges, so such an array has no self-parent and no 2-cycle. The published definition does not ask for nonempty bags; this definition adds it, as the paper does on p.9.
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), §1.1, p.2; §3, p.9

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition
import Definitions.Def_MinBisectFPT_cutSize

open scoped Classical

namespace MinBisectFPT

/-- **Rooted decomposition data**: `N` nodes, a parent array (`none` at a root), and a bag per node.
Anand, Kipouridis, Węgrzycki, *Counting over Unbreakable Decompositions*, STOC 2027 submission
(manuscript sha256 8db80a52…), §1.1, p.2. See `IsRootedTD` for the axioms. -/
structure RootedTD (n : ℕ) where
  N : ℕ
  parent : Fin N → Option (Fin N)
  bag : Fin N → Finset (Fin n)

namespace RootedTD

variable {n : ℕ} (T : RootedTD n)

/-- The tree `T`: the graph on the nodes with an edge `{t, parent t}`. -/
def treeGraph : SimpleGraph (Fin T.N) :=
  SimpleGraph.fromRel fun t t' => T.parent t = some t'

/-- `T.Below s t`: `s` lies in the subtree rooted at `t` (`t` itself included). -/
def Below (s t : Fin T.N) : Prop :=
  Relation.ReflTransGen (fun a b => T.parent a = some b) s t

/-- The cone `γ(t)`, "the union of the bags in the subtree rooted at t" (p.2). -/
noncomputable def cone (t : Fin T.N) : Finset (Fin n) :=
  Finset.univ.filter fun v => ∃ s, T.Below s t ∧ v ∈ T.bag s

/-- The adhesion `σ(t) := β(t) ∩ β(t′)`, where `t′` is the parent of `t`, and `σ(t) := ∅` at the
root (p.2). -/
def adhesion (t : Fin T.N) : Finset (Fin n) :=
  match T.parent t with
  | none => ∅
  | some t' => T.bag t ∩ T.bag t'

/-- The component `α(t) := γ(t) \ σ(t)` (p.2). -/
noncomputable def component (t : Fin T.N) : Finset (Fin n) := T.cone t \ T.adhesion t

/-- The children of `t`. -/
noncomputable def children (t : Fin T.N) : Finset (Fin T.N) :=
  Finset.univ.filter fun c => T.parent c = some t

end RootedTD

/-- The subtree graph `G_t := G[γ(t)] − E(G[σ(t)])` (p.2), on the ambient vertex type. -/
noncomputable def subtreeGraph {n : ℕ} (G : SimpleGraph (Fin n)) (T : RootedTD n) (t : Fin T.N) :
    SimpleGraph (Fin n) :=
  restrictMinus G (T.cone t) (T.adhesion t)

/-- The bag graph `B_t = G[β(t)] − E(G[σ(t)])` (§3, p.9), on the ambient vertex type. -/
noncomputable def bagGraph {n : ℕ} (G : SimpleGraph (Fin n)) (T : RootedTD n) (t : Fin T.N) :
    SimpleGraph (Fin n) :=
  restrictMinus G (T.bag t) (T.adhesion t)

/-- **`T` is a rooted tree decomposition of `G`** (p.2): exactly one root; the graph of the parent
array with the bags satisfies the published axioms of a tree decomposition; and "all bags of a tree
decomposition are nonempty" (§3, p.9).

**Formalization Note** A tree on `N` nodes has `N − 1` edges, so a parent array with one root whose
graph is a tree has no self-parent and no 2-cycle, and every node reaches the root. -/
def IsRootedTD {n : ℕ} (G : SimpleGraph (Fin n)) (T : RootedTD n) : Prop :=
  (∃! r, T.parent r = none) ∧
    RobertsonSeymour1986.GM5.IsTreeDecomposition G T.treeGraph T.bag ∧
      ∀ t, (T.bag t).Nonempty

end MinBisectFPT


