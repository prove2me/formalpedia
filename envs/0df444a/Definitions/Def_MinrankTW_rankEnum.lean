-- Prove2me | Definitions.Def_MinrankTW_rankEnum
-- name    : MinrankTW_rankEnum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:52.844229+00:00
-- url     : https://prove2.me/theorems/b6638efb-35c9-47e6-8354-dfd303c4eb01
-- title:
--   Rank enumerator $Z(z)$
-- statement:
--   The **rank enumerator** of entry constraints $S$ over $\mathbb F_q$ is the polynomial
--   $$
--   Z(z)=\sum_{M:\,M_{ij}\in S_{ij}} z^{\operatorname{rank}M}.
--   $$
--   Its coefficient of $z^r$ counts rank-$r$ completions and its least nonzero degree is the minimum completion rank. The dynamic program of Section 3 computes it at the root of a tree decomposition.
--
--   **Formalization Note** A polynomial with natural-number coefficients.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 1.2, p.5, Eq. (1)

import Mathlib
import Definitions.Def_MinrankTW_IsCompletion

namespace MinrankTW

open Polynomial

/-- The **rank enumerator** of the entry constraints `S` (Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), §1.2, p.5, Eq. (1)):
`Z(z) = ∑_{M : M_ij ∈ S_ij} z^{rank M}`.

**Formalization Note** A polynomial with natural-number coefficients; the sum ranges over the
finite set of completions of `S` in `F^{m×n}` (decidability of the completion predicate is
classical). -/
noncomputable def rankEnum {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m n : ℕ}
    (S : Fin m → Fin n → Finset F) : ℕ[X] := by
  classical
  exact ∑ M ∈ (Finset.univ : Finset (Matrix (Fin m) (Fin n) F)).filter (IsCompletion S),
    X ^ M.rank

end MinrankTW


