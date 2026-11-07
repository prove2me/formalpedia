-- Prove2me | Definitions.Def_SparseDisc_IsCycle
-- name    : SparseDisc_IsCycle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:50:01.197763+00:00
-- url     : https://prove2.me/theorems/fcecaf96-cb12-4299-98b1-2b4382a03ec2
-- title:
--   Cycle graph $C_n$, $n \ge 3$
-- statement:
--   A graph $H$ is a **cycle** if it is isomorphic to the cycle $C_n$ on $n \ge 3$ vertices (Mathlib's `SimpleGraph.cycleGraph n`).
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Theorem 1.9(b), p.5

import Mathlib

namespace SparseDisc

/-- `IsCycle H`: `H` is (isomorphic to) a **cycle** `C_n`, `n ≥ 3` (Zeng–Cao–Dai–Wang–Liao,
*Sparse Discrepancy Beyond Additive Functions*, STOC 2027 submission manuscript (sha256
0f09ec60…25b81), Theorem 1.9(b), p.5: "cycles"). Uses Mathlib's `SimpleGraph.cycleGraph`. -/
def IsCycle {V : Type} (H : SimpleGraph V) : Prop :=
  ∃ n : ℕ, 3 ≤ n ∧ Nonempty (H ≃g SimpleGraph.cycleGraph n)

end SparseDisc


