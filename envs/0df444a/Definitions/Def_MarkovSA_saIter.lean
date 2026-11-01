-- Prove2me | Definitions.Def_MarkovSA_saIter
-- name    : MarkovSA_saIter
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:14.608524+00:00
-- url     : https://prove2.me/theorems/e214d84c-3c4a-4635-937e-856e9a461663
-- title:
--   Iterates of Algorithm (6): $x_{k+1}=x_k+\alpha_k(F(x_k,Y_k)-x_k+w_k)$
-- statement:
--   Given stepsizes $(\alpha_k)_{k\ge0}$, an initial point $x_0\in E$, a random sequence $(Y_k)$ in $\mathcal Y$ and additive noise $(w_k)$ in $E$ on a sample space $\Omega$, the iterates of **Algorithm (6)** are defined on every sample point by
--
--   $$
--   x_0=x_0,\qquad x_{k+1}=x_k+\alpha_k\big(F(x_k,Y_k)-x_k+w_k\big).
--   $$
--
--   Every theorem of the mission is about this recursion, not about an arbitrary sequence.
--
--   **Formalization Note** The initial point is a fixed vector (the constant $c_1$ of Theorem 2.1 contains $\|x_0\|_c$); the law of $Y_0$ is arbitrary.
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, §2.1, Eq. (6), p.5

import Mathlib

namespace MarkovSA

/-- The iterates of **Algorithm (6)** (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, §2.1, p.5):
`x_0 = x₀`, `x_{k+1} = x_k + α_k (F(x_k, Y_k) − x_k + w_k)`, defined by recursion on every sample point.

**Formalization Note.** The initial point `x₀` is a fixed vector (the constant `c₁` of Theorem 2.1 contains
`‖x₀‖_c`); the law of `Y 0` is arbitrary. -/
noncomputable def saIter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {𝒴 : Type*} [Fintype 𝒴] [DecidableEq 𝒴] {Ω : Type*}
    (F : E → 𝒴 → E) (α : ℕ → ℝ) (x₀ : E) (Y : ℕ → Ω → 𝒴) (w : ℕ → Ω → E) : ℕ → Ω → E
  | 0 => fun _ => x₀
  | k + 1 => fun ω =>
      saIter F α x₀ Y w k ω + α k • (F (saIter F α x₀ Y w k ω) (Y k ω) - saIter F α x₀ Y w k ω + w k ω)

end MarkovSA


