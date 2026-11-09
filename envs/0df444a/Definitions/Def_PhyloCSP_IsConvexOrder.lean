-- Prove2me | Definitions.Def_PhyloCSP_IsConvexOrder
-- name    : PhyloCSP_IsConvexOrder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:22:50.944592+00:00
-- url     : https://prove2.me/theorems/a8247ba4-2838-4781-99ed-81193f99c86d
-- title:
--   Convex orders (Definition 7.10)
-- statement:
--   A total order $<$ on the leaves of a rooted tree $T$ is **$T$-convex** if, for every internal node $v$, the leaves of the subtree rooted at $v$ form an interval with respect to $<$. For a binary tree structure $C_T$ one also says that $<$ is $C_T$-convex. A point $a$ is **between** $b$ and $c$ if $b<a<c$ or $c<a<b$.
--
--   Convex orders are the left-to-right orders obtained by choosing, at each internal node, which child comes first; they connect random trees to random orders in Sections 9–10.
--
--   **Formalization Note** Internal nodes are represented by their clusters. An order on four leaves can also be given by listing the leaves, smallest first.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Definition 7.10, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_PhyloCSP_Cluster

set_option autoImplicit false

namespace PhyloCSP

/-- `a` lies strictly between `b` and `c` with respect to the order `lt`. -/
def Between {X : Type} (lt : X → X → Prop) (a b c : X) : Prop :=
  (lt b a ∧ lt a c) ∨ (lt c a ∧ lt a b)

/-- **Convex orders (Definition 7.10).**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Definition 7.10, p.23 (PDF p.25): "A total order < on the
leaves of a finite rooted tree T is T-convex if, for every internal node v, all leaves of the
subtree rooted at v form an interval w.r.t. the order <. For a binary tree structure C_T we also
say that < is C_T-convex."

**Formalization Note.** The internal nodes of the tree with relation `C` are represented by their
leaf sets `clusterSet C a b` (`a ≠ b`); an interval is a set containing every point between two of
its points. The order is any relation `lt`; statements add `IsStrictTotalOrder`. -/
def IsConvexOrder {X : Type} (C : X → X → X → Bool) (lt : X → X → Prop) : Prop :=
  ∀ a b : X, a ≠ b → ∀ x ∈ clusterSet C a b, ∀ y ∈ clusterSet C a b, ∀ z : X,
    lt x z → lt z y → z ∈ clusterSet C a b

/-- The order on `Fin 4` that lists the leaves as `l` (first element smallest). -/
def orderOfList (l : List (Fin 4)) (a b : Fin 4) : Prop := l.idxOf a < l.idxOf b

end PhyloCSP


