-- Prove2me | Definitions.Def_LovaszECCKernel_partSize
-- name    : LovaszECCKernel_partSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:55:00.115562+00:00
-- url     : https://prove2.me/theorems/2b384575-b122-4a8f-8c1f-6064f0f63d6c
-- title:
--   Parts, part sizes $t_1\ge t_2\ge\cdots$ and the two largest parts $T_1,T_2$
-- statement:
--   For an integer $r\ge 2$, a graph is **complete $r$-partite** if $V(G)$ has a partition $\{V_1,\dots,V_r\}$ (some parts may be empty) such that two vertices are adjacent iff they lie in different parts. Its **parts** are the non-empty $V_i$; for a complete multipartite graph they are the classes of the equivalence relation "$u=v$ or $u,v$ non-adjacent".
--
--   The **part sizes** are listed in non-increasing order,
--   $$t_1\ge t_2\ge t_3\ge\cdots,$$
--   and $t_i=0$ when $i$ exceeds the number of non-empty parts (the empty parts of the definition). **Two largest parts** $T_1,T_2$ are disjoint sets, each a part or empty, with $|T_1|=t_1$ and $|T_2|=t_2$; with ties every such choice counts, and $T_2=\emptyset$ when there is a single part.
--
--   **Formalization Note** `parts H` is the set of classes $\{v: uv\notin E(H)\}$, which are the parts when $H$ is complete multipartite (Mathlib's `SimpleGraph.IsCompleteMultipartite`, non-adjacency transitive). `partSize H i` is $t_i$, indexed from $1$; `partSize H 0` is not used.
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), §2, p.15, §3.3, p.30, Lemma 4, p.32, and Algorithm 1, p.42 (= PDF pp.15, 30, 32, 42)

import Mathlib

set_option autoImplicit false

namespace LovaszECCKernel

open Classical in
/-- The **parts** of a complete multipartite graph (Fomin, Golovach, Khargeliia, Sagunov, Simonov,
*Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa
Theorems*, STOC 2027 submission (manuscript sha256 a9d53ab8…), §2, p.15 (= PDF p.15)): "For an
integer r ≥ 2, a graph G is an r-partite if there is a partition {V1, . . . , Vr} of V(G) (some sets
may be empty) such that the endpoints of each edge are in distinct sets of the partition. … A graph
is a complete r-partite if for every distinct i, j ∈ [r], and every u ∈ Vi and v ∈ Vj,
uv ∈ E(G)."

**Formalization Note** The set of non-empty parts: the class of `u` is the set of vertices not
adjacent to `u` (it contains `u`). When `H` is complete multipartite (Mathlib's
`SimpleGraph.IsCompleteMultipartite`: non-adjacency is transitive) these classes are exactly the
non-empty parts `V_i`, and they partition `V`. The empty parts the paper allows are not listed. -/
noncomputable def parts {V : Type*} [Fintype V] (H : SimpleGraph V) : Finset (Finset V) :=
  Finset.univ.image (fun u => Finset.univ.filter (fun v => ¬ H.Adj u v))

/-- The **part sizes** `t₁ ≥ t₂ ≥ ⋯` of a complete multipartite graph, in non-increasing order
(Fomin et al., STOC 2027 submission (manuscript sha256 a9d53ab8…), §3.3, p.30 (= PDF p.30)): "For a
complete r-partite graph, by T1, T2, . . . , Tr we denote the vertex sets of its parts. We assume
that |Ti| ≥ |Ti+1| for each i ∈ {1, . . . , r − 1}. For each i ∈ {1, . . . , r}, we define
ti := |Ti|."

**Formalization Note** `partSize H i` is `t_i` (1-indexed): the `i`-th entry of the sizes of the
non-empty parts sorted in non-increasing order, and `0` for `i` beyond the number of non-empty parts
(the paper's empty parts, p.15; this is what `t₂`, `t₃`, `t₈` mean when there are fewer parts).
`partSize H 0` is a junk value and is never used. -/
noncomputable def partSize {V : Type*} [Fintype V] (H : SimpleGraph V) (i : ℕ) : ℕ :=
  (((parts H).val.map Finset.card).sort (· ≥ ·)).getD (i - 1) 0

/-- `T₁, T₂` are **two largest parts** of the complete multipartite graph `H` (Fomin et al., STOC
2027 submission (manuscript sha256 a9d53ab8…), Lemma 4, p.32, and Algorithm 1, line 17, p.42
(= PDF pp.32, 42): "T1, T2 ← two largest parts of G△M").

**Formalization Note** `T₁` and `T₂` are disjoint, each is a part of `H` or empty, and
`|T₁| = t₁`, `|T₂| = t₂` (`partSize`). When `t₂ > 0` this makes `T₁, T₂` two distinct non-empty
parts of sizes `t₁, t₂`; when `H` has at most one non-empty part, `T₂ = ∅` (the paper's empty part).
Ties are not broken: every such choice qualifies. -/
def IsTwoLargestParts {V : Type*} [Fintype V] (H : SimpleGraph V) (T₁ T₂ : Finset V) : Prop :=
  (T₁ ∈ parts H ∨ T₁ = ∅) ∧ (T₂ ∈ parts H ∨ T₂ = ∅) ∧ Disjoint T₁ T₂ ∧
    T₁.card = partSize H 1 ∧ T₂.card = partSize H 2

end LovaszECCKernel


