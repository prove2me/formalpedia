-- Prove2me | Definitions.Def_FoundationsML_Ranking_EmpiricalError
-- name    : FoundationsML_Ranking_EmpiricalError
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:36:19.566981+00:00
-- url     : https://prove2.me/theorems/e2872e69-358c-4d40-989a-f4c11396f2b9
-- title:
--   Empirical pairwise misranking error (Eq. 10.2)
-- statement:
--   **Eq. (10.2), p. 241, PDF p. 258.** $\hat R_S(h) = \frac1m\sum_{i=1}^m
--   \mathbb 1_{(y_i\ne0)\wedge(y_i(h(x'_i)-h(x_i))\le0)}$, for labels $y$ in $\{-1,0,+1\}$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, Eq. (10.2), p. 241 (PDF p. 258)

import Mathlib

namespace FoundationsML.Ranking

/-- The empirical pairwise misranking error of a scoring function `h : X → ℝ` on a sample of
pairs `(S1_i, S2_i)` with labels `y : Fin m → ℝ` in `{−1,0,+1}` (Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Eq. (10.2), p. 241, PDF
p. 258): `R̂_S(h) = (1/m) ∑_{i=1}^m 1_{(y_i≠0)∧(y_i(h(x'_i)−h(x_i))≤0)}`. -/
noncomputable def EmpiricalError {X : Type*} {m : ℕ}
    (S1 S2 : Fin m → X) (y : Fin m → ℝ) (h : X → ℝ) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, (if y i ≠ 0 ∧ y i * (h (S2 i) - h (S1 i)) ≤ 0 then (1 : ℝ) else 0)

end FoundationsML.Ranking


