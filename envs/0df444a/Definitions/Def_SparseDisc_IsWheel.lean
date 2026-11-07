-- Prove2me | Definitions.Def_SparseDisc_IsWheel
-- name    : SparseDisc_IsWheel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:36.577032+00:00
-- url     : https://prove2.me/theorems/4a720c6c-b33e-46b8-b223-082f508dc344
-- title:
--   Wheel pattern
-- statement:
--   A graph $H$ is a **wheel** if it is isomorphic to the wheel $W_m$ with $m \ge 3$ rim vertices.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Theorem 1.9(b), p.5; Corollary 8.34(i), p.44

import Mathlib
import Definitions.Def_SparseDisc_wheel

namespace SparseDisc

/-- `IsWheel H`: `H` is (isomorphic to) a **wheel** `W_m` with `m ≥ 3` rim vertices
(Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027 submission
manuscript (sha256 0f09ec60…25b81), Theorem 1.9(b), p.5, and Corollary 8.34(i), p.44). -/
def IsWheel {V : Type} (H : SimpleGraph V) : Prop :=
  ∃ m : ℕ, 3 ≤ m ∧ Nonempty (H ≃g wheel m)

end SparseDisc


