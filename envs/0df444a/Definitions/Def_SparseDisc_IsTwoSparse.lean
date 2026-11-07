-- Prove2me | Definitions.Def_SparseDisc_IsTwoSparse
-- name    : SparseDisc_IsTwoSparse
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:50:54.719198+00:00
-- url     : https://prove2.me/theorems/137ddfab-f113-4c05-b572-f29400af9d5e
-- title:
--   2-sparse family of set functions
-- statement:
--   A family $F = (f_v)_{v \in V}$ of set functions on a finite item set $\iota$ is **2-sparse** if every item is relevant to at most two functions:
--   $$
--   |\{ v \in V : j \in R(f_v) \}| \le 2 \qquad \text{for every item } j .
--   $$
--   This is the case $t = 2$ of the paper's $t$-sparsity, the setting of the main theorem.
--
--   **Formalization Note** The functions are indexed by a finite type $V$ (the paper's $[n]$).
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Section 1, p.1 (t-sparse with t = 2)

import Mathlib
import Definitions.Def_SparseDisc_relevant

namespace SparseDisc

/-- A family `f = (f_v)_{v ∈ V}` of set functions on the items `ι` is **2-sparse**: every item is
relevant to at most two functions (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive
Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81), Section 1, p.1, "F is
t-sparse if every item is relevant to at most t functions", with `t = 2`).

**Formalization Note** The functions are indexed by a finite type `V` (the paper's `[n]`). -/
def IsTwoSparse {V ι : Type} [Fintype V] [Fintype ι] [DecidableEq ι]
    (f : V → Finset ι → ℝ) : Prop :=
  ∀ j : ι, (Finset.univ.filter (fun v => j ∈ relevant (f v))).card ≤ 2

end SparseDisc


