-- Prove2me | Definitions.Def_TreeCorrMatch_ErrorFree_LocalTree
-- name    : TreeCorrMatch_ErrorFree_LocalTree
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:24:51.070127+00:00
-- url     : https://prove2.me/theorems/2a5678e7-4fc1-43e3-9133-9d95af9497cc
-- title:
--   Local trees $T^\tau_{w\setminus u,k}$ with degree cutoff $\tau\in\mathbb N\cup\{\infty\}$
-- statement:
--   Let $G$ be a graph on $[n]$, $k\ge0$ and $\tau\in\mathbb N\cup\{\infty\}$. For nodes $w,u$, the **local tree** $T^\tau_{w\setminus u,k}$ (Definition 1, with the roles: root $w$, removed node $u$) is: for $k=0$, the single node $w$; for $k\ge1$, provided that the depth-$k$ neighbourhood of $w$ in $G$ induces a tree and every node $y$ of this neighbourhood has $\deg_G(y)\le\tau$, the subgraph of $G\setminus u$ induced by the nodes at distance at most $k$ from $w$ in $G\setminus u$, rooted at $w$; otherwise the **empty tree**. With $\tau=\infty$ there is no degree condition. In TBAlign $u$ and $w$ are adjacent; the proof of Lemma 6 uses the same definition for arbitrary $u\neq w$, and App. G.3 the variant in which no node is removed.
--
--   The local tree is represented as an ordered tree whose children are ordered by increasing vertex index (the relabeling $\ell$ of App. G.2), together with its node set $V(T)\subseteq[n]$ (empty for the empty tree).
--
--   **Formalization Note** `localTree G (some u) w k τ` is `none` for the empty tree; `localTree G none w k τ` removes no node. When the neighbourhood is a tree, the subgraph is the unfolding of $G\setminus u$ from $w$ that never returns to the node it came from. `ball G w k` is the set of nodes at distance at most $k$ (extended distance, so unreachable nodes are excluded).
-- source:
--   Cheng, Wang, Ying, Near-Quadratic Error-Free Graph Matching above Otter's Threshold via Approximate Local Tree Correlation Testing, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), p. 6, Definition 1 (PDF p. 8); p. 18, proof of Lemma 6 (PDF p. 20); pp. 41–42 and 45, App. G.2–G.3 (PDF pp. 43–44, 47)

import Mathlib
import Definitions.Def_TreeCorrMatch_ErrorFree_RootedTree

/-!
Local trees `T^τ_{w∖u,k}` (Definition 1), with the degree cutoff `τ ∈ ℕ ∪ {∞}`, the extension to a
non-adjacent removed node (proof of Lemma 6) and the variant without a removed node (App. G.3).

Cheng, Wang, Ying, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), Definition 1, p. 6; proof of
Lemma 6, p. 18; App. G.2, p. 41 (the relabeling ℓ by vertex index); App. G.3, p. 45.
-/

namespace TreeCorrMatch.ErrorFree

open scoped Classical

variable {n : ℕ}

/-- `G ∖ v`: the graph `G` with every edge at `v` removed (`v` becomes isolated). -/
def delVert (G : SimpleGraph (Fin n)) (v : Fin n) : SimpleGraph (Fin n) where
  Adj a b := G.Adj a b ∧ a ≠ v ∧ b ≠ v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩

/-- `G` with the node `v` removed when `rm = some v`, and `G` itself when `rm = none`. -/
def delOpt (G : SimpleGraph (Fin n)) : Option (Fin n) → SimpleGraph (Fin n)
  | none => G
  | some v => delVert G v

/-- The depth-`k` neighbourhood `{y : dist_G(w, y) ≤ k}` of `w` in `G`. -/
def ball (G : SimpleGraph (Fin n)) (w : Fin n) (k : ℕ) : Set (Fin n) :=
  {y | G.edist w y ≤ k}

/-- The neighbours of `x` in `G`, in increasing order of vertex index. -/
noncomputable def nbrList (G : SimpleGraph (Fin n)) (x : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun y => G.Adj x y

/-- The depth-`k` unfolding of `G` from `x`, coming from `par`: the children of a vertex are its
neighbours other than the vertex it was reached from, ordered by increasing vertex index (the
paper's relabeling `ℓ`, App. G.2). When the neighbourhood is a tree this is the neighbourhood
itself, rooted at `x`. -/
noncomputable def unfold (G : SimpleGraph (Fin n)) : ℕ → Fin n → Option (Fin n) → OTree
  | 0, _, _ => OTree.leaf
  | k + 1, x, par =>
    OTree.node (((nbrList G x).filter fun y => some y ≠ par).map fun y => unfold G k y (some x))

/-- The admissibility condition of Definition 1 for a depth-`k` local tree rooted at `w`: the
depth-`k` neighbourhood of `w` in `G` induces a tree (an acyclic graph), and every node `y` of it
has `deg_G(y) ≤ τ` (no condition when `τ = ⊤ = ∞`). -/
def LocalTreeOK (G : SimpleGraph (Fin n)) (w : Fin n) (k : ℕ) (τ : ℕ∞) : Prop :=
  (G.induce (ball G w k)).IsAcyclic ∧ ∀ y ∈ ball G w k, ((G.degree y : ℕ) : ℕ∞) ≤ τ

/-- The local tree `T^τ_{w∖u,k}` (`rm = some u`) as an ordered tree, children ordered by vertex
index, or `none` for the empty tree: for `k = 0` the singleton rooted at `w`; for `k ≥ 1`, if the
depth-`k` neighbourhood of `w` in `G` is a tree and all its nodes have degree at most `τ`, the
subgraph of `G ∖ u` induced by the nodes at distance at most `k` from `w` in `G ∖ u`, rooted at `w`;
otherwise empty. With `rm = none` no node is removed (the tree of App. G.3). -/
noncomputable def localTree (G : SimpleGraph (Fin n)) (rm : Option (Fin n)) (w : Fin n) (k : ℕ)
    (τ : ℕ∞) : Option OTree :=
  if k = 0 then some OTree.leaf
  else if LocalTreeOK G w k τ then some (unfold (delOpt G rm) k w none) else none

/-- The node set `V(T^τ_{w∖u,k}) ⊆ [n]` of the local tree (empty for the empty tree). -/
def localVerts (G : SimpleGraph (Fin n)) (rm : Option (Fin n)) (w : Fin n) (k : ℕ) (τ : ℕ∞) :
    Set (Fin n) :=
  if k = 0 then {w}
  else if LocalTreeOK G w k τ then ball (delOpt G rm) w k else ∅

end TreeCorrMatch.ErrorFree


