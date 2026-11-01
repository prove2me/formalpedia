-- Prove2me | Definitions.Def_BiasVarianceMinimax_IsOptimal
-- name    : BiasVarianceMinimax_IsOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:42.272605+00:00
-- url     : https://prove2.me/theorems/bc2887d6-dfda-48e3-b82c-bc09d518d53a
-- title:
--   Problem (24) and its optimal solutions
-- statement:
--   Problem (24) at budget $n$ is the one-dimensional problem
--
--   $$\min_{a:\ (K^{2(q_1+q_2)}-\xi_{11})a^2-2\xi_{12}a-\xi_{22}\ge 0}\ |a|^{2q_2/(q_1+q_2)}\big(\xi_{11}a^2+2\xi_{12}a+\xi_{22}\big)^{q_1/(q_1+q_2)} .$$
--
--   Here `quadForm` is $\xi_{11}a^2+2\xi_{12}a+\xi_{22}$, `Feasible24` is the constraint, `objective24` is the objective, and `IsOptimal` says that $a$ is feasible and minimal among feasible points.
--
--   **Formalization Note** The feasible set can be empty at finite $n$, so the mission only uses this predicate for all large $n$.
-- source:
--   Lam, Zhang & Zhang, arXiv:1902.04673v1, Theorem 8, (24), p.20

import Mathlib
import Definitions.Def_BiasVarianceMinimax_xi

namespace BiasVarianceMinimax

/-- The quadratic `ξ₁₁ a² + 2 ξ₁₂ a + ξ₂₂` of problem (24). Lam, Zhang & Zhang,
arXiv:1902.04673v1, Theorem 8, (24), p.20. -/
noncomputable def quadForm (q₁ q₂ : ℝ) (n₀ n : ℕ) (a : ℝ) : ℝ :=
  xi q₁ q₂ n₀ n 0 0 * a ^ 2 + 2 * xi q₁ q₂ n₀ n 0 1 * a + xi q₁ q₂ n₀ n 1 1

/-- The constraint `(K^(2(q₁+q₂)) - ξ₁₁) a² - 2 ξ₁₂ a - ξ₂₂ ≥ 0` of problem (24).
Lam, Zhang & Zhang, arXiv:1902.04673v1, Theorem 8, (24), p.20. -/
def Feasible24 (q₁ q₂ K : ℝ) (n₀ n : ℕ) (a : ℝ) : Prop :=
  0 ≤ (K ^ (2 * (q₁ + q₂)) - xi q₁ q₂ n₀ n 0 0) * a ^ 2 - 2 * xi q₁ q₂ n₀ n 0 1 * a
    - xi q₁ q₂ n₀ n 1 1

/-- The objective `|a|^(2q₂/(q₁+q₂)) (ξ₁₁ a² + 2 ξ₁₂ a + ξ₂₂)^(q₁/(q₁+q₂))` of problem (24).
Lam, Zhang & Zhang, arXiv:1902.04673v1, Theorem 8, (24), p.20. -/
noncomputable def objective24 (q₁ q₂ : ℝ) (n₀ n : ℕ) (a : ℝ) : ℝ :=
  |a| ^ (2 * q₂ / (q₁ + q₂)) * quadForm q₁ q₂ n₀ n a ^ (q₁ / (q₁ + q₂))

/-- `a` is an optimal solution to problem (24) at budget `n`: it is feasible and minimal among
feasible points. Lam, Zhang & Zhang, arXiv:1902.04673v1, Theorem 8, (24), p.20.

**Formalization Note.** The feasible set can be empty at finite `n`, and `n = 1` makes `Ξ` the junk
`0`; so this predicate is only ever used "for all large `n`". -/
def IsOptimal (q₁ q₂ K : ℝ) (n₀ n : ℕ) (a : ℝ) : Prop :=
  Feasible24 q₁ q₂ K n₀ n a ∧
    ∀ b : ℝ, Feasible24 q₁ q₂ K n₀ n b → objective24 q₁ q₂ n₀ n a ≤ objective24 q₁ q₂ n₀ n b

end BiasVarianceMinimax


