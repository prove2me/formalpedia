-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_TreeCutDecomp
-- name    : AgnosticTNS_Supplement_TreeCutDecomp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:35:17.898608+00:00
-- url     : https://prove2.me/theorems/70374470-5c7c-4c59-ac7b-fcd87e912a18
-- title:
--   Tree-cut decomposition
-- statement:
--   A **near partition** of a set $X$ is a family of pairwise disjoint subsets, some possibly empty, whose union is $X$. A **tree-cut decomposition** of a graph $G$ is a pair $(\mathcal T,\mathcal X)$ where $\mathcal T$ is a tree with a distinguished root $r$ and $\mathcal X=\{X_t: t\in V(\mathcal T)\}$ is a near partition of $V(G)$; the sets $X_t$ are the bags.
--
--   **Formalization Note** Tree nodes are `Fin N`, graph vertices `Fin n`.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Definitions 6.2–6.3, p.48

import Mathlib

namespace AgnosticTNS.Supplement

/-- **A tree-cut decomposition**, Definitions 6.2–6.3, p.48 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
a rooted tree `𝒯` with root `r` and a near partition `{X_t : t ∈ V(𝒯)}` of `V(G)` (pairwise disjoint
bags, possibly empty, whose union is `V(G)`).

**Formalization Note** Tree nodes are `Fin N`; vertices of `G` are `Fin n`. The decomposition depends
only on the vertex set of `G`. -/
structure TreeCutDecomp (n : ℕ) where
  /-- the number of tree nodes -/
  N : ℕ
  /-- the tree `𝒯` -/
  T : SimpleGraph (Fin N)
  /-- the root `r` -/
  root : Fin N
  /-- the bags `X_t` -/
  X : Fin N → Finset (Fin n)
  isTree : T.IsTree
  bags_disjoint : ∀ s t, s ≠ t → Disjoint (X s) (X t)
  bags_cover : ∀ v, ∃ t, v ∈ X t

end AgnosticTNS.Supplement


