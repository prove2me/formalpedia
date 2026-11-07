-- Prove2me | Definitions.Def_SparseDisc_signVec
-- name    : SparseDisc_signVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:52:41.29992+00:00
-- url     : https://prove2.me/theorems/7579d185-31e3-4910-8ce2-67b7751dd6b9
-- title:
--   Sign vector $1_S - 1_{\iota \setminus S}$
-- statement:
--   The **sign vector** of a set of items $S \subseteq \iota$ is $1_S - 1_{\iota \setminus S} \in \{\pm1\}^{\iota}$: coordinate $j$ is $1$ if $j \in S$ and $-1$ otherwise.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Lemma 2.1(b), p.11

import Mathlib
import Definitions.Def_SparseDisc_Cube

namespace SparseDisc

/-- The sign vector `1_S − 1_{ι \ S} ∈ {±1}^ι` of a set of items `S` (Zeng–Cao–Dai–Wang–Liao,
*Sparse Discrepancy Beyond Additive Functions*, STOC 2027 submission manuscript (sha256
0f09ec60…25b81), Lemma 2.1(b), p.11). -/
def signVec {ι : Type} [DecidableEq ι] (S : Finset ι) : Cube ι := fun j => if j ∈ S then 1 else -1

end SparseDisc


