-- Prove2me | Definitions.Def_PlanarDFVSKernel_GSCA
-- name    : PlanarDFVSKernel_GSCA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:35:29.646219+00:00
-- url     : https://prove2.me/theorems/65a779b0-326e-4747-a534-ac5231cdb8c1
-- title:
--   Grouped Strong Connectivity Augmentation (GSCA)
-- statement:
--   An instance $(H,\mathcal G,k)$ of **GSCA** consists of a finite digraph $H$ (its arcs are the **base arcs**), an indexed family $\mathcal G$ of **arc groups**, each a finite set of arcs on $V(H)$, and a budget $k$. In a valid instance every group arc is absent from $H$ and has both endpoints in one weakly connected component of $H$.
--
--   The instance is a **YES-instance** if at most $k$ groups can be selected so that adding all their arcs to $H$ makes every weakly connected component of $H$ strongly connected. Each selected group costs one. The number of **group-arc entries** is $\sum_{B\in\mathcal G}|B|$; an arc shared by two groups counts twice.
--
--   GSCA is the dual form of planar DFVS: deleting a vertex corresponds to adding a group of reverse arcs in the planar dual.
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), §1.2, p.3 (PDF 4)

import Mathlib
import Definitions.Def_PlanarDFVSKernel_ArcReach

set_option autoImplicit false

namespace PlanarDFVSKernel

/-- **An instance `(H, 𝒢, k)` of Grouped Strong Connectivity Augmentation (GSCA)** (Sheng, Xiao,
*A Polynomial Kernel for Planar Directed Feedback Vertex Set*, arXiv:2609.23669 (held version,
sha256 75cfca8f…), §1.2, p.3 (PDF 4)): "Input. A finite digraph H, a family G of arc groups, and a
nonnegative integer k. Each group is a set of arcs absent from H, with all endpoints in the same
weakly connected component of H. Different groups may share arcs. […] Groups are indexed, so
different groups may contain the same arc set."

The vertices form the type `V`; `base` is the arc list of `H` (the base arcs, repeated arcs
allowed); `groups` is the indexed family of groups, each a finite set of arcs; `k` is the budget.

**Formalization Note** The condition on the groups is the predicate `GSCA.Valid`, kept separate
from the data so that constructions (Reduction Rule 7) can be stated as total functions. -/
structure GSCA (V : Type*) where
  /-- the base arcs of `H` -/
  base : List (V × V)
  /-- the indexed family of arc groups -/
  groups : List (Finset (V × V))
  /-- the budget -/
  k : ℕ

namespace GSCA

variable {V : Type*}

/-- **The group condition of GSCA** (Sheng, Xiao, arXiv:2609.23669 (held version, sha256
75cfca8f…), p.3 (PDF 4)): "Each group is a set of arcs absent from H, with all endpoints in the
same weakly connected component of H." -/
def Valid (I : GSCA V) : Prop :=
  ∀ g ∈ I.groups, ∀ a ∈ g, a ∉ I.base ∧ ArcWeakReach I.base a.1 a.2

/-- **A GSCA instance is a YES-instance** (ibid., p.3 (PDF 4)): "Question. Can we select at most k
groups from G so that adding all their arcs to H makes every weakly connected component strongly
connected? Each selected group has unit cost, regardless of how many arcs it contains."

Some set `S` of at most `k` group indices is selected such that, for any two vertices `u, v` in
one weakly connected component of `H`, `v` is reachable from `u` using base arcs and the arcs of
the selected groups.

**Formalization Note** A selection is a finite set of indices, so each group is counted once.
"Every weakly connected component" refers to the components of the base graph `H`; for a `Valid`
instance adding groups joins no two of them. -/
def Solvable (I : GSCA V) : Prop :=
  ∃ S : Finset (Fin I.groups.length), S.card ≤ I.k ∧
    ∀ u v, ArcWeakReach I.base u v →
      Relation.ReflTransGen (fun a b => (a, b) ∈ I.base ∨ ∃ i ∈ S, (a, b) ∈ I.groups[i]) u v

/-- **The number of group-arc entries** (ibid., p.3 (PDF 4)): "When measuring the representation
size, a group-arc entry is one occurrence of an arc in a group. An arc shared by two groups
contributes two entries." -/
def entries (I : GSCA V) : ℕ := (I.groups.map Finset.card).sum

end GSCA

end PlanarDFVSKernel


