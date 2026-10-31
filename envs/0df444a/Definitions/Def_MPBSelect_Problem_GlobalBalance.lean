-- Prove2me | Definitions.Def_MPBSelect_Problem_GlobalBalance
-- name    : MPBSelect_Problem_GlobalBalance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:26:20.641768+00:00
-- url     : https://prove2.me/theorems/7ce48593-80a9-416c-acb4-30bf6f23b00f
-- title:
--   The global balance condition of Theorem 3
-- statement:
--   An allocation $\boldsymbol\alpha$ satisfies the **global balance condition** if, for every $1\le b\le B$,
--   $$
--   \frac{\alpha_{i^b}^2(\theta_b)}{\lambda_{i^b}^2(\theta_b)}=\sum_{i\ne i^b,\,i^*}\frac{\alpha_i^2(\theta_b)}{\lambda_i^2(\theta_b)} .
--   $$
--   The sum runs over the solutions that are neither $i^b$ nor $i^*$; when $\theta_b\in\Theta_{i^*}$ these coincide. It says that the conditional optimum $i^b$ receives enough budget relative to the other solutions at $\theta_b$, and it coincides with the global balance condition of classical ranking and selection.
--
--   **Formalization Note** For $k=2$ and $\theta_b\notin\Theta_{i^*}$ the sum is empty, so the condition reads $\alpha_{i^b}(\theta_b)=0$.
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, Theorem 3, p.17, first bullet

import Mathlib
import Definitions.Def_MPBSelect_Problem

namespace MPBSelect

open Finset

/-- **Global balance condition** of Theorem 3.
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, Theorem 3, p.17:
"(Global balance condition) For all 1 ≤ b ≤ B, α²_{i^b}(θb)/λ²_{i^b}(θb) =
Σ_{i≠i^b,i∗} α²_i(θb)/λ²_i(θb)."

At every parameter `θ_b`, `α_{i^b}(θ_b)² / λ_{i^b}(θ_b)² = Σ_{i ∉ {i^b, i*}} α_i(θ_b)² / λ_i(θ_b)²`.

**Formalization Note** The sum runs over `i` with `i ≠ i^b` and `i ≠ i*`; when `θ_b ∈ Θ_{i*}`
these coincide. When `k = 2` and `θ_b ∉ Θ_{i*}` the sum is empty (`= 0`). `lam` is the
standard deviation, so `lam ^ 2` is the variance `λ²`. -/
def Problem.GlobalBalance {k B : ℕ} (P : Problem k B) (α : Fin k → Fin B → ℝ) : Prop :=
  ∀ b : Fin B, α (P.ib b) b ^ 2 / P.lam (P.ib b) b ^ 2 =
    ∑ i ∈ univ.filter (fun i : Fin k => i ≠ P.ib b ∧ i ≠ P.istar), α i b ^ 2 / P.lam i b ^ 2

end MPBSelect


