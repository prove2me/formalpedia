-- Prove2me | Definitions.Def_LovaszECCKernel_Supplement_ecp
-- name    : LovaszECCKernel_Supplement_ecp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:09:16.955491+00:00
-- url     : https://prove2.me/theorems/bda50614-653f-46df-bd74-c9f9e9158219
-- title:
--   Edge clique partitions and the edge clique partition number $\mathrm{ecp}(G)$
-- statement:
--   Two cliques $C_1,C_2$ of a graph $G$ are **(edge) disjoint** if $|C_1\cap C_2|\le 1$. A family $\mathcal C$ of cliques is an **edge clique partition** of $G$ if it is an edge clique cover (every edge $uv\in E(G)$ lies in some member) and its members are pairwise disjoint; equivalently, every edge of $G$ lies in exactly one member of $\mathcal C$. The **edge clique partition number** $\mathrm{ecp}(G)$ is the minimum size of an edge clique partition of $G$.
--
--   On a finite vertex set the family of all edges, viewed as two-element cliques, is an edge clique partition, so $\mathrm{ecp}(G)\le|E(G)|$ and the minimum exists; $\mathrm{ecp}(G)=0$ exactly when $G$ has no edges. This is the quantity bounded by the Erdős–Goodman–Pósa theorem.
--
--   **Formalization Note** Cliques are finite sets of vertices of any size and a family is a finite set of them (so its size counts distinct cliques). The cover condition is the published `IsEdgeCliqueCover` of this mission; disjointness says that the intersection of two distinct members has at most one element. `ecp` is the infimum of the sizes of partitions in $\mathbb N$, defined exactly like the published `ecc`.
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), §2, p.15 (= PDF p.15); Table 1, p.16

import Mathlib
import Definitions.Def_LovaszECCKernel_ecc

set_option autoImplicit false

namespace LovaszECCKernel.Supplement

/-- An **edge clique partition** of `G` (Fomin, Golovach, Khargeliia, Sagunov, Simonov, *Stability
Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems*, STOC 2027
submission (manuscript sha256 a9d53ab8…), §2, p.15 (= PDF p.15)): "Two cliques C1 and C2 are (edge)
disjoint if |C1 ∩ C2| ≤ 1 … A family of disjoint cliques C is called clique packing. We say that a
family of cliques C is an edge clique cover if every edge of G is covered by a clique of C, and C is an
edge clique partition if C is an edge clique cover and clique packing, that is, each edge is covered by
a unique clique."

**Formalization Note** The cover part is the published `IsEdgeCliqueCover` (cliques are `Finset V`s of
any size, the family a `Finset (Finset V)`); the packing part says that two distinct members share at
most one vertex. Equivalently, every edge lies in exactly one member. -/
def IsEdgeCliquePartition {V : Type*} (G : SimpleGraph V) (F : Finset (Finset V)) : Prop :=
  IsEdgeCliqueCover G F ∧
    ∀ C ∈ F, ∀ D ∈ F, C ≠ D → ((C : Set V) ∩ (D : Set V)).Subsingleton

/-- The **edge clique partition number** `ecp(G)`, the minimum size of an edge clique partition
(Fomin et al., STOC 2027 submission (manuscript sha256 a9d53ab8…), §2, p.15 (= PDF p.15): "We use
ecc(G) and ecp(G) to denote the minimum size of an edge clique cover and partition, respectively";
Table 1, p.16).

**Formalization Note** Defined exactly like the published `ecc`, as an infimum over naturals. For
finite `V` the set is nonempty (the 2-element cliques `{u, v}`, `uv ∈ E(G)`, form an edge clique
partition), so the minimum is attained; `ecp G = 0` exactly when `G` has no edges. -/
noncomputable def ecp {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ F : Finset (Finset V), IsEdgeCliquePartition G F ∧ F.card = k}

end LovaszECCKernel.Supplement


