-- Prove2me | Definitions.Def_SmoothedNash_Supplement_alg3Candidates
-- name    : SmoothedNash_Supplement_alg3Candidates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:59:33.982109+00:00
-- url     : https://prove2.me/theorems/6b8d1627-5d17-4a2f-87b0-36dc7218ff8a
-- title:
--   Candidate set $C(x,k) = C_k \cap B(x, 3r_k)$ of Algorithm 3
-- statement:
--   For a parent $x \in D_{k-1}$ with level-$(k-1)$ integer vector $i$ (so $x = (r_k/\sqrt n)(2i)$), the **candidate set** of Algorithm 3 is
--   $$
--   C(x,k) = C_k \cap B(x, 3r_k),
--   $$
--   as a set of level-$k$ integer vectors $j$: those with $\sum_l j_l^2 \le 4^k n$ (the point lies in $B(0,1)$) and $\sum_l (j_l - 2i_l)^2 \le 9n$ (it lies within $3r_k$ of $x$).
--
--   **Formalization Note** The balls are closed. The finite set is carved out of the integer box $[-2^k n, 2^k n]^n$, which contains every admissible $j$.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Algorithm 3, line 6, p.21

import Mathlib
open MeasureTheory

namespace SmoothedNash.Supplement

/-- The candidate set `C(x, k) = C_k ∩ B(x, 3 r_k)` of Algorithm 3 (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), Algorithm 3,
line 6, p.21), for the parent `x ∈ D_{k−1}` with level-`(k−1)` integer vector `i`, as a finite set of
level-`k` integer vectors `j`.

With `y = (r_k/√n) j` and `x = (r_k/√n)(2i)`: `y ∈ B(0,1)` iff `∑_l j_l² ≤ 4^k n`, and
`‖y − x‖ ≤ 3 r_k` iff `∑_l (j_l − 2 i_l)² ≤ 9n`.

**Formalization Note** The finite set is cut out of the box `[−2^k n, 2^k n]^n`, which contains every
`j` with `∑ j_l² ≤ 4^k n` (since `|j_l| ≤ 2^k √n ≤ 2^k n`). The balls are closed. -/
noncomputable def alg3Candidates (n k : ℕ) (i : Fin n → ℤ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.Icc (-((2 : ℤ) ^ k * n)) ((2 : ℤ) ^ k * n)).filter
    fun j => ∑ l, (j l) ^ 2 ≤ (4 : ℤ) ^ k * n ∧ ∑ l, (j l - 2 * i l) ^ 2 ≤ 9 * (n : ℤ)

end SmoothedNash.Supplement


