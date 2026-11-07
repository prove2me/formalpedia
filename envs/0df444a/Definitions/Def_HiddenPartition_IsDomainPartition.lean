-- Prove2me | Definitions.Def_HiddenPartition_IsDomainPartition
-- name    : HiddenPartition_IsDomainPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:26:25.396538+00:00
-- url     : https://prove2.me/theorems/7c70322f-47c7-4f41-9256-a9ce9dc646aa
-- title:
--   Partition of a graph into $k$ non-empty independent domains
-- statement:
--   Let $G$ be a simple graph and $k\ge0$. A labelling $\mathrm{dom}:V(G)\to[k]$ is a **domain partition** of $G$ when
--
--   1. every domain $V_i=\mathrm{dom}^{-1}(i)$ is non-empty, i.e. $\mathrm{dom}$ is surjective, and
--   2. every domain is an independent set: $\{u,v\}\in E(G)$ implies $\mathrm{dom}(u)\ne\mathrm{dom}(v)$.
--
--   Then $V(G)=V_1\sqcup V_2\sqcup\cdots\sqcup V_k$, and we write $\mathrm{dom}(v)=i$ for $v\in V_i$. This is the input structure of the hidden-subgraph-to-partition construction: the hidden subgraph takes one vertex from each domain.
--
--   **Formalization Note** Domains are indexed by `Fin k`, i.e. $0,\dots,k-1$.
-- source:
--   H. Agrawal, P. Eua-anant, B. Haeupler, B. Laekhanukit, P. Mihov, L. Milenković, R. Santos, Z. Zhang, From One Hidden Subgraph to Dense Graph Partitions with Applications to Hardness of Clustering, STOC 2027 submission (manuscript sha256 17239d0bf911912040cb82c45ae979b179c419fb0b9e69d6d1413bf70068b601), §3.1, p.12 (pdf p.14); Theorem 1.1, p.2 (pdf p.4)

import Mathlib

set_option autoImplicit false

namespace HiddenPartition

/-- **Domain partition** (Agrawal, Eua-anant, Haeupler, Laekhanukit, Mihov, Milenković, Santos,
Zhang, *From One Hidden Subgraph to Dense Graph Partitions with Applications to Hardness of
Clustering*, STOC 2027 submission, manuscript sha256 17239d0b…, §3.1, p.12 (pdf p.14), and
Theorem 1.1, p.2 (pdf p.4)).

`dom : V → Fin k` labels each vertex of `G` with its domain, so `V(G) = V₁ ⊔ ⋯ ⊔ V_k` with
`V_i = dom⁻¹(i)`. The predicate says that every domain is non-empty (`dom` is surjective) and
independent (no edge of `G` joins two vertices of the same domain).

**Formalization Note.** Domains are indexed `0, …, k-1` (`Fin k`) rather than `1, …, k`.
Non-emptiness is part of "partitioned into `k` non-empty independent sets" (Theorem 1.1) and
of "partitioned into `k` classes" (§3.1). -/
def IsDomainPartition {V : Type*} {k : ℕ} (G : SimpleGraph V) (dom : V → Fin k) : Prop :=
  Function.Surjective dom ∧ ∀ u v, G.Adj u v → dom u ≠ dom v

end HiddenPartition


