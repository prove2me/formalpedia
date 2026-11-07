-- Prove2me | Definitions.Def_SparseDisc_wheel
-- name    : SparseDisc_wheel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:50:03.991378+00:00
-- url     : https://prove2.me/theorems/102e1dec-1ea6-4a03-842a-238a97664011
-- title:
--   Wheel $W_m$
-- statement:
--   The **wheel** $W_m$ consists of a hub $h$ and a rim cycle $r_0, r_1, \dots, r_{m-1}$, with the hub adjacent to every rim vertex. For $m = 3$ it is $K_4$.
--
--   **Formalization Note** The vertex type is `Option (Fin m)`: `none` is the hub and `some i` is $r_i$; the rim is Mathlib's `cycleGraph m`.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), proof of Corollary 8.34(i), p.44

import Mathlib

namespace SparseDisc

/-- The **wheel** `W_m`: a hub (`none`) joined to every vertex of a rim cycle `r₀, …, r_{m−1}`
(`some i`) (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027
submission manuscript (sha256 0f09ec60…25b81), proof of Corollary 8.34(i), p.44: "the wheel with
hub h and rim r0, . . . , rm−1 (m ≥ 3)"; `K₄ = W₃`). The rim is Mathlib's `cycleGraph m`. -/
def wheel (m : ℕ) : SimpleGraph (Option (Fin m)) :=
  SimpleGraph.fromRel (fun a b => match a, b with
    | none, some _ => True
    | some i, some j => (SimpleGraph.cycleGraph m).Adj i j
    | _, _ => False)

end SparseDisc


