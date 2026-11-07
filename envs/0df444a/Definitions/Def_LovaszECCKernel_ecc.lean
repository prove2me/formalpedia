-- Prove2me | Definitions.Def_LovaszECCKernel_ecc
-- name    : LovaszECCKernel_ecc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:54:43.239052+00:00
-- url     : https://prove2.me/theorems/96aca812-ba68-4977-a86e-7cdedf6fbace
-- title:
--   Edge clique covers and the edge clique cover number $\mathrm{ecc}(G)$
-- statement:
--   A **clique** of a graph $G$ is a set of pairwise adjacent vertices (of any size). A family $\mathcal C$ of cliques is an **edge clique cover** if every edge $uv\in E(G)$ lies in some member, $u,v\in C\in\mathcal C$. The **edge clique cover number** $\mathrm{ecc}(G)$ is the minimum size of an edge clique cover.
--
--   On a finite vertex set the family of all edges (as two-element cliques) is a cover, so the minimum exists; $\mathrm{ecc}(G)=0$ exactly when $G$ has no edges.
--
--   **Formalization Note** Cliques are finite sets of vertices and a family is a finite set of them, so its size counts distinct cliques. `ecc` is the infimum of the sizes of covers in $\mathbb N$.
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), §2, p.15 (= PDF p.15)

import Mathlib

set_option autoImplicit false

namespace LovaszECCKernel

/-- An **edge clique cover** of `G` (Fomin, Golovach, Khargeliia, Sagunov, Simonov, *Stability Meets
Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems*, STOC 2027
submission (manuscript sha256 a9d53ab8…), §2, p.15 (= PDF p.15)): "A clique C in a graph G is a set
of pairwise adjacent vertices. A clique C covers an edge uv ∈ E(G) if u, v ∈ C. … We say that a
family of cliques C is an edge clique cover if every edge of G is covered by a clique of C".

**Formalization Note** A clique is a `Finset V` that is a clique of `G` (any size, the empty set and
singletons included); a family of cliques is a `Finset (Finset V)`, so its size counts distinct
cliques. -/
def IsEdgeCliqueCover {V : Type*} (G : SimpleGraph V) (F : Finset (Finset V)) : Prop :=
  (∀ C ∈ F, G.IsClique (C : Set V)) ∧ ∀ u v, G.Adj u v → ∃ C ∈ F, u ∈ C ∧ v ∈ C

/-- The **edge clique cover number** `ecc(G)`, the minimum size of an edge clique cover
(Fomin et al., STOC 2027 submission (manuscript sha256 a9d53ab8…), §2, p.15 (= PDF p.15): "We use
ecc(G) and ecp(G) to denote the minimum size of an edge clique cover and partition, respectively").

**Formalization Note** The infimum is over a nonempty set of naturals when `V` is finite: the family
of all 2-element sets `{u, v}` with `uv ∈ E(G)` is an edge clique cover. So `ecc G` is attained;
`ecc G = 0` exactly when `G` has no edges. -/
noncomputable def ecc {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ F : Finset (Finset V), IsEdgeCliqueCover G F ∧ F.card = k}

end LovaszECCKernel


