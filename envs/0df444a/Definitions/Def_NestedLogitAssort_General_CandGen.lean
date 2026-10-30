-- Prove2me | Definitions.Def_NestedLogitAssort_General_CandGen
-- name    : NestedLogitAssort_General_CandGen
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:44:45.52914+00:00
-- url     : https://prove2.me/theorems/9bec0c80-bddb-4a21-bf70-b1048e160ee9
-- title:
--   Candidate collection $\{N^k_{ij}\}\cup\{\{j\}\}$ of Theorem 11
-- statement:
--   For a weight listing $\sigma$ of nest $i$, the candidate assortments of Theorem 11 are
--
--   $$
--   \{N^k_{ij}:k\in N,\ j=0,\dots,k\}\ \cup\ \{\{j\}:j\in N\},
--   $$
--
--   that is, every nested-by-revenue assortment among the $k$ lightest products, for $k=1,\dots,n$, together with every singleton. The collection has at most $1+n+n^2$ members.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, Section 6.1, p. 26 (Theorem 11)

import Mathlib
import Definitions.Def_NestedLogitAssort_General_NK

namespace NestedLogitAssort.General

/-- **The candidate collection of Theorem 11.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, Section 6.1, p. 26: the assortments
`{N^k_{ij} : k ∈ N, j = 0, …, k} ∪ {{j} : j ∈ N}` of nest `i`.

`CandGen σ` uses the weight listing `σ` of the nest (see `IsWeightOrder`); `k` ranges over
`1, …, n` and `j` over `0, …, k`. -/
def CandGen {n : ℕ} (σ : Equiv.Perm (Fin n)) : Set (Finset (Fin n)) :=
  {S | ∃ k j : ℕ, 1 ≤ k ∧ k ≤ n ∧ j ≤ k ∧ S = NK σ k j} ∪ {S | ∃ j : Fin n, S = {j}}

end NestedLogitAssort.General


