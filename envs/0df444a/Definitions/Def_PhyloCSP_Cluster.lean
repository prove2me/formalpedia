-- Prove2me | Definitions.Def_PhyloCSP_Cluster
-- name    : PhyloCSP_Cluster
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:22:08.102204+00:00
-- url     : https://prove2.me/theorems/86e0261a-a9a8-4f9c-8385-74035bd455aa
-- title:
--   Clusters: the leaves below a lowest common ancestor
-- statement:
--   Let $C$ be a rooted-triplet relation on $X$ and $a\neq b$ leaves. The **cluster** of $a,b$ is
--   $$
--   \mathrm{cl}_C(a,b)=\{a,b\}\cup\{z : C(z;a,b)\text{ is false}\},
--   $$
--   the set of leaves below the lowest common ancestor $a\vee b$: by Section 2, for distinct leaves, $z\mid ab$ holds exactly when $a\vee b$ is a proper descendant of $z\vee a\vee b$.
--
--   For a binary tree structure, the clusters with $a\neq b$ are exactly the leaf sets of the internal nodes (branchpoints), since every internal node is the lowest common ancestor of one leaf from each of its two children. They are used to state convexity of orders (Definition 7.10), to index the internal nodes of an input tree in a basic transformation (Definition 3.3), and to identify branchpoints in Section 10.1.
--
--   **Formalization Note** Two forms are provided: a `Set` for arbitrary leaf types and a `Finset` on finite leaf types.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Section 2, p.6 (PDF p.8): $a\mid bc$ iff $b\vee c<a\vee b\vee c$

import Mathlib

set_option autoImplicit false

namespace PhyloCSP

/-- **Clusters (leaf sets of subtrees below lowest common ancestors).**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Section 2, p.6 (PDF p.8): "for distinct leaves a, b, c, the
rooted triplet relation a | bc holds exactly when b ∨ c < a ∨ b ∨ c". Hence, for distinct `a, b`,
the leaves below the branchpoint `a ∨ b` are `a`, `b` and every `z` that is not the outgroup of
`{z, a, b}`, i.e. with `C(z; a, b)` false.

**Formalization Note.** For a tree relation, the sets `clusterSet C a b` with `a ≠ b` are exactly
the leaf sets of the internal nodes (branchpoints): every internal node of a binary tree is the
lowest common ancestor of a leaf from each of its two children. `clusterOf` is the same set as a
`Finset` on a finite leaf type. -/
def clusterSet {X : Type} (C : X → X → X → Bool) (a b : X) : Set X :=
  {z | z = a ∨ z = b ∨ C z a b = false}

/-- `clusterSet` as a `Finset` on a finite leaf type. -/
def clusterOf {X : Type} [Fintype X] [DecidableEq X] (C : X → X → X → Bool) (a b : X) :
    Finset X :=
  Finset.univ.filter (fun z => z = a ∨ z = b ∨ C z a b = false)

theorem mem_clusterOf_left {X : Type} [Fintype X] [DecidableEq X] (C : X → X → X → Bool)
    (a b : X) : a ∈ clusterOf C a b := by
  simp [clusterOf]

end PhyloCSP


