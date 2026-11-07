-- Prove2me | Definitions.Def_SparseDisc_IsTwoSparseSupp
-- name    : SparseDisc_IsTwoSparseSupp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:40.658478+00:00
-- url     : https://prove2.me/theorems/09768b03-1689-45b0-8a50-d2d5e3359e54
-- title:
--   2-sparse supports
-- statement:
--   Supports $(U_v)_{v \in V}$ in a finite item set are **2-sparse** if every item lies in at most two supports.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Definition 2.2, p.12; Definition 8.4, p.30

import Mathlib

namespace SparseDisc

/-- `IsTwoSparseSupp U`: the supports `(U_v)_{v ∈ V}` are **2-sparse** — every item lies in at most
two supports (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027
submission manuscript (sha256 0f09ec60…25b81), Definition 2.2, p.12, and Definition 8.4, p.30). -/
def IsTwoSparseSupp {V ι : Type} [Fintype V] [DecidableEq ι] (U : V → Finset ι) : Prop :=
  ∀ j : ι, (Finset.univ.filter (fun v => j ∈ U v)).card ≤ 2

end SparseDisc


