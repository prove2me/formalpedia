-- Prove2me | Definitions.Def_SparseDisc_IsOneLipschitz
-- name    : SparseDisc_IsOneLipschitz
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:34.515183+00:00
-- url     : https://prove2.me/theorems/baf0e32c-5b12-461d-9361-3a7a3fb53c95
-- title:
--   1-Lipschitz set function
-- statement:
--   Let $\iota$ be a finite set of items. A set function $g : 2^{\iota} \to \mathbb R$ is **1-Lipschitz** if adding or removing one item changes its value by at most $1$:
--   $$
--   |g(S \cup \{j\}) - g(S)| \le 1 \qquad \text{for all } S \subseteq \iota,\ j \in \iota .
--   $$
--   These are the functions whose discrepancy the paper studies; additive functions $S \mapsto \sum_{j \in S} a_j$ with $|a_j| \le 1$ are the classical case.
--
--   **Formalization Note** Removing $j$ from $S$ is the case $j \in S$ read backwards, so one inequality covers both directions. No monotonicity and no normalisation $g(\emptyset) = 0$ is assumed.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Section 1, p.1

import Mathlib

namespace SparseDisc

/-- A set function `g : 2^ι → ℝ` is **1-Lipschitz**: adding or removing one item changes its value
by at most `1` (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027
submission manuscript (sha256 0f09ec60…25b81), Section 1, p.1).

**Formalization Note** The item set `[m]` is a finite type `ι`. The condition is stated as
`|g (S ∪ {j}) − g S| ≤ 1` for all `S` and `j`; removing `j` from `S` is the case `j ∈ S` read
backwards (`S = (S \ {j}) ∪ {j}`), so both directions of the page's condition are covered. No
monotonicity and no normalisation `g ∅ = 0` is assumed (the paper assumes none). -/
def IsOneLipschitz {ι : Type} [DecidableEq ι] (g : Finset ι → ℝ) : Prop :=
  ∀ (S : Finset ι) (j : ι), |g (insert j S) - g S| ≤ 1

end SparseDisc


