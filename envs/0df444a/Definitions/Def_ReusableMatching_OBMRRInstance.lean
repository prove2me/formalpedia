-- Prove2me | Definitions.Def_ReusableMatching_OBMRRInstance
-- name    : ReusableMatching_OBMRRInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:29:46.75988+00:00
-- url     : https://prove2.me/theorems/42617c26-7b1f-4a9d-b2d1-f8abce58fef2
-- title:
--   An instance of online bipartite matching with reusable resources (OBMRR)
-- statement:
--   An instance of the **vertex-weighted OBMRR problem** consists of
--
--   1. a finite set $V$ of offline vertices (the reusable resources);
--   2. $n$ online vertices (the arrivals), which arrive one at a time in the order $0,1,\dots,n-1$;
--   3. a set $E\subseteq V\times\{0,\dots,n-1\}$ of edges, where $(i,j)\in E$ means that resource $i$ can be assigned to arrival $j$;
--   4. a non-negative weight $r_i\ge 0$ for every resource $i$, earned each time $i$ is matched;
--   5. a usage duration $d\ge 1$: a resource matched to arrival $j$ is unavailable for the next $d-1$ arrivals and available again at arrival $j+d$.
--
--   Every algorithm and every guarantee of this mission is stated for an arbitrary instance.
--
--   **Formalization Note** Arrivals are numbered from $0$ (the paper numbers them $1,\dots,|U|$). The adversarial arrival order of the paper is a relabelling of the arrivals, so quantifying over all instances covers it. The condition $d\ge1$ excludes $d=0$, for which the model has no meaning.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, §1 Problem Formulation, p.2; vertex-weighted setting, p.3

import Mathlib

namespace ReusableMatching

/-- **An instance of the OBMRR problem** (online bipartite matching with reusable resources), in
its vertex-weighted form (Delong, Farhadi, Niazadeh, Sivan & Udwani, *Online Bipartite Matching
with Reusable Resources*, arXiv:2110.07084v2, §1 "Problem Formulation", p.2, and the
vertex-weighted setting, p.3).

An instance consists of a bipartite graph `G = (V, U; E)` with offline side `V` (the reusable
resources) and online side `U` (the arrivals), an edge set `E`, a non-negative vertex weight `r i`
for every resource `i`, and a usage duration `d ∈ ℕ`: a resource matched to arrival `j` "remains
unavailable for the next `d − 1` periods and will be available for re-allocation upon arrival of
online vertex `j + d`" (p.2).

**Formalization Note.**
* The resources form a type `V` (finite in every statement that uses an instance).
* The arrivals are `Fin n`, numbered `0, …, n − 1` in their order of arrival (the paper's
  `1, …, |U|`, shifted by one). The adversarial order of the paper is a relabelling of `Fin n`,
  so every statement quantifies over all instances.
* `E ⊆ V × Fin n`: the pair `(i, j)` is an edge when resource `i` can serve arrival `j`.
* `r_nonneg`: the weights are non-negative (p.3).
* `one_le_d`: `d ≥ 1`. The paper's `d ∈ ℕ` with "unavailable for the next `d − 1` periods" has
  no meaning at `d = 0`. -/
structure OBMRRInstance (V : Type*) (n : ℕ) where
  /-- The edge set `E`: `(i, j) ∈ E` when resource `i` can be assigned to arrival `j`. -/
  E : Finset (V × Fin n)
  /-- The vertex weight `r i` of resource `i`. -/
  r : V → ℝ
  /-- The usage duration `d`. -/
  d : ℕ
  /-- The vertex weights are non-negative. -/
  r_nonneg : ∀ i, 0 ≤ r i
  /-- The usage duration is at least one. -/
  one_le_d : 1 ≤ d

end ReusableMatching


