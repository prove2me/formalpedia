-- Prove2me | Definitions.Def_SparseHistComm_Supplement_algorithm1Work
-- name    : SparseHistComm_Supplement_algorithm1Work
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:42:11.569561+00:00
-- url     : https://prove2.me/theorems/ff63dbe2-bc1a-400d-94a3-6bf74cbf1c4e
-- title:
--   Arithmetic-work expression for Algorithm 1
-- statement:
--   The arithmetic-work expression for Algorithm 1 is $k+1$ in the large-threshold branch. In the small-threshold branch it is
--
--   $$
--   N\bigl(t^2\lceil\log_2(n+1)\rceil+h+\lceil\log_2(N+1)\rceil\bigr),
--   $$
--
--   where $N$ is the Appendix D upper bound on the number of candidate laws in the applicable probability grid. The three terms account for truncated polynomial exponentiation, expected-level evaluation, and the lower convex hull.
--
--   **Formalization Note** This counts arithmetic operations, not bit operations. Choosing unit coefficients for the displayed work terms changes the count only by the universal multiplicative constant quantified in Theorem 6.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), proof of Theorem 6, pp.24–25

import Mathlib
import Definitions.Def_SparseHistComm_threshold

namespace SparseHistComm

namespace Supplement

/-- The arithmetic-work expression counted for Algorithm 1 in the proof of Theorem 6
(Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285
(held version, sha256 29df82a4…f27c6f), pp.24–25).

It is `k+1` in the large-threshold branch. In the small-threshold branch, `N` is the printed
upper bound for the number of enumerated laws, and the factor
`N(t²⌈log₂(n+1)⌉ + h + ⌈log₂(N+1)⌉)` records truncated polynomial exponentiation,
mean evaluation, and the lower-convex-hull computation.

**Formalization Note** This is an arithmetic-operation upper-count expression, not a bit-complexity
measure. Replacing each `O(·)` in the prose count by one copy of its displayed argument changes the
count only by the universal multiplicative constant quantified in Theorem 6. -/
noncomputable def algorithm1Work (n k : ℕ) (D δ ε : ℝ) : ℕ :=
  let tZ := threshold n k D
  let t : ℝ := tZ
  let tN : ℕ := tZ.toNat
  let h : ℕ := min k tN
  let L : ℕ := ⌈Real.logb 2 (8 / (ε * δ))⌉₊
  let B : ℝ := (4 * t + 8 * (⌈Real.logb 2 (2 / δ)⌉₊ : ℝ)) / δ
  if 64 * (L : ℝ) / ε ^ 2 ≤ t then
    k + 1
  else
    let m : ℕ := ⌈(n : ℝ) * h / (ε * (1 - δ) * t)⌉₊
    let ρ : ℝ := ε * (1 - δ) * t / (h * (h + 1))
    let N : ℕ := if (n : ℝ) ≤ B + ε * (1 - δ) * t / 2 then
      (m + 1) ^ h else (2 + ⌈B / ρ⌉₊) ^ h
    N * (tN ^ 2 * Nat.clog 2 (n + 1) + h + Nat.clog 2 (N + 1))

end Supplement

end SparseHistComm


