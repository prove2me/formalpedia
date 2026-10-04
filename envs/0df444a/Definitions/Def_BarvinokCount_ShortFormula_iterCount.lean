-- Prove2me | Definitions.Def_BarvinokCount_ShortFormula_iterCount
-- name    : BarvinokCount_ShortFormula_iterCount
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T05:31:54.525984+00:00
-- url     : https://prove2.me/theorems/277afcbe-3178-40fb-a26f-301f5cbf3869
-- title:
--   T(d, Ind K) — the number of decomposition rounds in the proof of Theorem 5.4
-- statement:
--   For natural numbers $d$ and $N$ (in the paper $N=\operatorname{Ind}K$), $T(d,N)$ is the smallest integer $T$ with
--   $$T\ge\frac{-\log\log 1.9+\log\log N}{\log d-\log(d-1)},$$
--   when $N\ge 2$, and $T(d,1)=T(d,0)=0$. Logarithms are natural.
--
--   In the proof of Theorem 5.4, $T$ rounds of Lemma 5.3 bring every index below $1.9$, hence to $1$, and produce at most $(2^d)^T$ primitive cones; this number is the size bound in the goal theorem.
--
--   **Formalization Note** For $d\ge 2$ and $N\ge 2$ the ratio is positive, so the smallest integer above it is its ceiling. The case $N=1$ (the cone is already primitive; $\log\log 1$ is undefined) is pinned to $T=0$, which gives the true bound $(2^d)^0=1$. The definition is only used with $d\ge 2$, because $\log(d-1)$ is undefined at $d=1$. The base of the logarithm does not matter: it cancels in the ratio.
-- source:
--   Barvinok, A polynomial time algorithm for counting integral points in polyhedra when the dimension is fixed, Math. Oper. Res. 19 (1994), p. 777, proof of Theorem 5.4 (choice of T)

import Mathlib

namespace BarvinokCount.ShortFormula

/-- The number of iterations `T` in the proof of Theorem 5.4 (p. 777): the smallest integer
`T ≥ (−log log 1.9 + log log N) / (log d − log(d − 1))`, where `N = Ind K`.
For `N ≤ 1` (the cone is already primitive) it is `0`. Natural logarithms; only used for `d ≥ 2`. -/
noncomputable def iterCount (d N : ℕ) : ℕ :=
  if N ≤ 1 then 0
  else ⌈(-Real.log (Real.log (1.9 : ℝ)) + Real.log (Real.log (N : ℝ))) /
      (Real.log (d : ℝ) - Real.log ((d : ℝ) - 1))⌉₊

end BarvinokCount.ShortFormula


