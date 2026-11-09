-- Prove2me | Definitions.Def_ForgetAlt_Matching
-- name    : ForgetAlt_Matching
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:19:54.681063+00:00
-- url     : https://prove2.me/theorems/ec1a6d32-7117-4f4f-87c5-bf45e7ed55f7
-- title:
--   Augmenting paths, $\ell$, and (maximal) sets of disjoint shortest augmenting paths
-- statement:
--   Let $G$ be a graph and $M$ a set of edges of $G$ (a matching). A vertex is **free** if no edge of $M$ contains it; $U$ denotes the set of free vertices. An **alternating path** is a simple path $v_0,e_1,v_1,\dots,e_k,v_k$ such that, of any two consecutive edges $e_{i-1},e_i$, exactly one lies in $M$. An **augmenting path** is an alternating path joining two different free vertices.
--
--   The length of a shortest augmenting path is written $2\ell+1$:
--
--   $$2\ell+1=\min\{|P| : P \text{ an augmenting path of } (G,M)\},$$
--
--   taken in $\mathbb N\cup\{\infty\}$ (it is $\infty$ when there is no augmenting path). A **shortest augmenting path** is an augmenting path of this length.
--
--   A list $A$ of vertex sequences is a **set of vertex-disjoint shortest augmenting paths** if every member is the vertex sequence of a shortest augmenting path and any two members share no vertex. It is **maximal** if, in addition, every shortest augmenting path shares a vertex with some member (maximal under inclusion, not maximum).
--
--   These are the objects of Theorem 1.1's conclusion.
--
--   **Formalization Note** The matching is a subgraph `M : G.Subgraph`; that it is a matching is a hypothesis of the theorems. Free vertices and alternation reuse `BergeMatching.Core.IsNeutral` and `IsAlternatingWrt`, with simplicity (`IsPath`) added. `ell` is $(\text{augLen}-1)/2$ and is used only under the hypothesis that an augmenting path exists.
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Section 3.1.1, printed p.15 (PDF p.16)

import Mathlib
import Definitions.Def_BergeMatching_Core_AlternatingChain

namespace ForgetAlt

open BergeMatching.Core

/-!
# Augmenting paths, shortest augmenting paths and their disjoint families

Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…), Section 3.1.1, printed p.15 (PDF p.16).

**Formalization Note.** A matching `M` of `G` is a subgraph `M : G.Subgraph`; that it is a
matching (`M.IsMatching`) is a hypothesis of each theorem, never bundled here. A vertex is free
(`IsNeutral M v`, reused from `BergeMatching.Core`) if no edge of `M` contains it. An alternating
path is a *simple* path (`p.IsPath`) whose consecutive edges alternate between `M` and its
complement (`IsAlternatingWrt`, reused). Families of paths are lists of vertex lists (the
supports of the paths, in order); "vertex-disjoint" is `List.Disjoint` of the supports.
-/

/-- An alternating path of `(G, M)` in the paper's sense (p.15): a simple path in which, of any
two consecutive edges, exactly one lies in `M`. -/
def IsAltPath {W : Type} {H : SimpleGraph W} (S : Set (Sym2 W)) {u v : W} (p : H.Walk u v) :
    Prop :=
  p.IsPath ∧ IsAlternatingWrt S p

/-- An augmenting path of `(G, M)` (p.15): an alternating path connecting two different free
vertices. -/
def IsAugPath {V : Type} {G : SimpleGraph V} (M : G.Subgraph) {u v : V} (p : G.Walk u v) : Prop :=
  IsAltPath M.edgeSet p ∧ u ≠ v ∧ IsNeutral M u ∧ IsNeutral M v

/-- The length `2ℓ + 1` of a shortest augmenting path of `(G, M)`, as an element of `ℕ∞`; it is
`⊤` when `(G, M)` has no augmenting path (infimum of the empty set). -/
noncomputable def augLen {V : Type} {G : SimpleGraph V} (M : G.Subgraph) : ℕ∞ :=
  ⨅ (u : V) (v : V) (p : G.Walk u v) (_ : IsAugPath M p), (p.length : ℕ∞)

/-- `(G, M)` has an augmenting path. -/
def HasAugPath {V : Type} {G : SimpleGraph V} (M : G.Subgraph) : Prop :=
  ∃ (u v : V) (p : G.Walk u v), IsAugPath M p

/-- The paper's `ℓ_I` (p.15): a shortest augmenting path has length `2ℓ + 1`. Only meaningful
when `HasAugPath M` holds (then `augLen M` is finite and odd); every theorem using `ell`
assumes `HasAugPath M`. -/
noncomputable def ell {V : Type} {G : SimpleGraph V} (M : G.Subgraph) : ℕ :=
  ((augLen M).toNat - 1) / 2

/-- A shortest augmenting path: an augmenting path of length `augLen M`. -/
def IsShortestAugPath {V : Type} {G : SimpleGraph V} (M : G.Subgraph) {u v : V}
    (p : G.Walk u v) : Prop :=
  IsAugPath M p ∧ (p.length : ℕ∞) = augLen M

/-- `l` is the vertex sequence (support) of some shortest augmenting path. -/
def IsSAPSupport {V : Type} {G : SimpleGraph V} (M : G.Subgraph) (l : List V) : Prop :=
  ∃ (u v : V) (p : G.Walk u v), IsShortestAugPath M p ∧ p.support = l

/-- A set of vertex-disjoint shortest augmenting paths, given by their vertex sequences. -/
def IsDisjointSAPFamily {V : Type} {G : SimpleGraph V} (M : G.Subgraph) (A : List (List V)) :
    Prop :=
  (∀ l ∈ A, IsSAPSupport M l) ∧ A.Pairwise List.Disjoint

/-- A *maximal* set of vertex-disjoint shortest augmenting paths: no shortest augmenting path is
vertex-disjoint from all of its members (maximal under inclusion, not maximum). -/
def IsMaximalSAPFamily {V : Type} {G : SimpleGraph V} (M : G.Subgraph) (A : List (List V)) :
    Prop :=
  IsDisjointSAPFamily M A ∧
    ∀ (u v : V) (p : G.Walk u v), IsShortestAugPath M p → ∃ l ∈ A, ¬ List.Disjoint p.support l

end ForgetAlt


