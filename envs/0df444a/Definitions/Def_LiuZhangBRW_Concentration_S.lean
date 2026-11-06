-- Prove2me | Definitions.Def_LiuZhangBRW_Concentration_S
-- name    : LiuZhangBRW_Concentration_S
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:18:34.563291+00:00
-- url     : https://prove2.me/theorems/b096f2be-467a-4b0b-8d98-ab65eb30a731
-- title:
--   Partial sum $S_n=X_1+\dots+X_n$
-- statement:
--   For real random variables $X_1,X_2,\dots$ the partial sum is
--   $$
--   S_n=X_1+X_2+\dots+X_n=\sum_{i=1}^n X_i ,
--   $$
--   with $S_0=0$. The mission's concentration inequalities bound the deviation of $S_n$ from its mean.
--
--   **Formalization Note** The sum runs over $i\in\{1,\dots,n\}$; the coordinate $X_0$ of the Lean sequence is not used.
-- source:
--   Liu, Zhang, Concentration Inequalities for Branching Random Walks with Applications to Phase Transitions in CSPs, arXiv:1601.04794 (artifact sha256 7499631b9d550f66e791c0b3df0879f26102f111fee3052e363ebbff0c72bdcb; no version stamp), §4.2, p. 6; Theorem 5.1, p. 7; §6.2, p. 21

import Mathlib

namespace LiuZhangBRW.Concentration

/-- The partial sum `S_n = X_1 + X_2 + ⋯ + X_n` (Liu, Zhang, *Concentration Inequalities for
Branching Random Walks with Applications to Phase Transitions in CSPs*, arXiv:1601.04794,
artifact sha256 7499631b…bdcb, §4.2, p. 6, "`S_n = ∑_{j=1}^n X_j`"; Theorem 5.1, p. 7; §6.2,
p. 21, "`S_n = X_1 + X_2 + ⋯ + X_n`").

**Formalization Note** The sum runs over `Finset.Icc 1 n`, so `X 0` is never used and
`S X 0 = 0`. -/
def S {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, X i ω

end LiuZhangBRW.Concentration


