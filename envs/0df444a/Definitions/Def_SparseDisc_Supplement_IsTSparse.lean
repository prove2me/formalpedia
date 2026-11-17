-- Prove2me | Definitions.Def_SparseDisc_Supplement_IsTSparse
-- name    : SparseDisc_Supplement_IsTSparse
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:00:43.893035+00:00
-- url     : https://prove2.me/theorems/8c3442d8-309f-421b-ae27-2fb174b993b8
-- title:
--   General $t$-sparse family of set functions
-- statement:
--   A finite family $F=(f_v)_{v\in V}$ is **$t$-sparse** when every item is relevant to at most $t$ functions:
--   $$
--   \bigl|\{v:j\in R(f_v)\}\bigr|\le t\qquad\text{for every item }j.
--   $$
--   This extends the published $2$-sparse predicate without changing its conventions.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), p.1 and Definition 2.2, p.12

import Mathlib
import Definitions.Def_SparseDisc_relevant

namespace SparseDisc.Supplement

/-- General `t`-sparsity for a family of set functions: every item is relevant to at most `t`
functions (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027
submission manuscript (sha256 0f09ec60…25b81), p.1 and Definition 2.2, p.12).

**Formalization Note** Functions and items are indexed by finite types. This is exactly the
published `SparseDisc.IsTwoSparse` with the constant `2` replaced by the parameter `t`. -/
def IsTSparse {V ι : Type} [Fintype V] [Fintype ι] [DecidableEq ι]
    (t : ℕ) (f : V → Finset ι → ℝ) : Prop :=
  ∀ j : ι, (Finset.univ.filter (fun v => j ∈ SparseDisc.relevant (f v))).card ≤ t

end SparseDisc.Supplement


