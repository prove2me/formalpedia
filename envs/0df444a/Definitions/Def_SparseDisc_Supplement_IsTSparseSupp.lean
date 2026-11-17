-- Prove2me | Definitions.Def_SparseDisc_Supplement_IsTSparseSupp
-- name    : SparseDisc_Supplement_IsTSparseSupp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:01:00.026463+00:00
-- url     : https://prove2.me/theorems/14105de0-d265-478e-9c10-cfbe7db0e9a3
-- title:
--   General $t$-sparse declared supports
-- statement:
--   Declared supports $(U_v)_{v\in V}$ are **$t$-sparse** if every item belongs to at most $t$ supports. Supports may strictly contain the relevant coordinates, as the paper permits.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Definition 2.2, p.12

import Mathlib

namespace SparseDisc.Supplement

/-- General `t`-sparsity for declared supports: every item lies in at most `t` supports
(Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027 submission
manuscript (sha256 0f09ec60…25b81), Definition 2.2, p.12).

**Formalization Note** Declared supports may strictly contain the relevant coordinates, as the
paper explicitly allows. -/
def IsTSparseSupp {V ι : Type} [Fintype V] [DecidableEq ι]
    (t : ℕ) (U : V → Finset ι) : Prop :=
  ∀ j : ι, (Finset.univ.filter (fun v => j ∈ U v)).card ≤ t

end SparseDisc.Supplement


