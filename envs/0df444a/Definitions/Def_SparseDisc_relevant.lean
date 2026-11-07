-- Prove2me | Definitions.Def_SparseDisc_relevant
-- name    : SparseDisc_relevant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:41.283519+00:00
-- url     : https://prove2.me/theorems/131ade70-f9d8-4849-be48-3054bcaf03b6
-- title:
--   Items relevant to a set function, $R(f)$
-- statement:
--   For a set function $f : 2^{\iota} \to \mathbb R$, the set $R(f)$ of items **relevant** to $f$ consists of the items $j$ that affect the value of $f$ somewhere:
--   $$
--   R(f) = \{\, j \in \iota : f(S) \ne f(S \cup \{j\}) \text{ for some } S \subseteq \iota \,\}.
--   $$
--   Sparsity and the pattern graph of a family are measured through relevance.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Section 2.1, p.11 (following [HMMS25, Definition 13]); Section 1, p.1

import Mathlib

namespace SparseDisc

open Classical in
/-- The set `R(g)` of items **relevant** to a set function `g`: the items `j` with
`g S ≠ g (S ∪ {j})` for some `S` (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive
Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81), Section 2.1, p.11; following
[HMMS25, Definition 13]). -/
noncomputable def relevant {ι : Type} [Fintype ι] [DecidableEq ι] (g : Finset ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun j => ∃ S : Finset ι, g S ≠ g (insert j S))

end SparseDisc


