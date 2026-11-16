-- Prove2me | Definitions.Def_SmoothedNash_Supplement_alg3EnumCost
-- name    : SmoothedNash_Supplement_alg3EnumCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:01:20.541577+00:00
-- url     : https://prove2.me/theorems/0b3c1a16-96ad-4331-a284-7b6ced326842
-- title:
--   Enumeration cost of one candidate set (Remark 3.5)
-- statement:
--   Remark 3.5 enumerates a candidate set $C(x,k)$ through the offsets $j = (y - x)\sqrt n / r_k \in \mathbb Z^n$, coordinate by coordinate, keeping only the prefixes $(j_1, \dots, j_d)$ with
--   $$
--   j_1^2 + \cdots + j_d^2 \le 9n .
--   $$
--   The enumeration cost is the number of such prefixes over all lengths $d = 0, 1, \dots, n$. It does not depend on $x$ or $k$.
--
--   **Formalization Note** Each prefix entry satisfies $|j_l| \le 3\sqrt n \le 3n$, so the count is taken in the box $[-3n, 3n]^d$.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Remark 3.5, p.23

import Mathlib
open MeasureTheory

namespace SmoothedNash.Supplement

/-- The enumeration cost of one candidate set `C(x, k)` in the running-time analysis of
Algorithm 3 (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), Remark 3.5, p.23): the offsets `j = (y − x)√n / r_k ∈ ℤ^n` are enumerated
coordinate by coordinate, keeping only prefixes `(j_1, …, j_d)` with `j_1² + ⋯ + j_d² ≤ 9n`; the cost
is the number of such prefixes over all lengths `d = 0, …, n`.

**Formalization Note** Each prefix of length `d` is an integer vector `Fin d → ℤ`; its entries satisfy
`|j_l| ≤ 3√n ≤ 3n`, so the count is taken in the box `[−3n, 3n]^d`. The count does not depend on the
parent `x`. -/
noncomputable def alg3EnumCost (n : ℕ) : ℕ :=
  ∑ d ∈ Finset.range (n + 1),
    ((Fintype.piFinset fun _ : Fin d => Finset.Icc (-(3 * (n : ℤ))) (3 * n)).filter
      fun j => ∑ l, (j l) ^ 2 ≤ 9 * (n : ℤ)).card

end SmoothedNash.Supplement


