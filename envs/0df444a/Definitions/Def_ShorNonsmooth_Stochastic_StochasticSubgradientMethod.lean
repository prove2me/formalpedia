-- Prove2me | Definitions.Def_ShorNonsmooth_Stochastic_StochasticSubgradientMethod
-- name    : ShorNonsmooth_Stochastic_StochasticSubgradientMethod
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T12:43:12.953276+00:00
-- url     : https://prove2.me/theorems/c32639d4-02c7-4630-8459-e643bc40fd4f
-- title:
--   The stochastic subgradient method $x_{k+1} = x_k - h_k(x_k)\,g_\omega(x_k)$
-- statement:
--   Throughout, $E_n$ is the $n$-dimensional Euclidean space with inner product $(x,y)$, and $f : E_n \to \mathbb{R}$ is finite everywhere.
--
--   Let $(\Omega, \mathcal F)$ be a measurable space. Given stepsize rules $h_k : E_n \to \mathbb{R}$ ($k = 0, 1, \dots$), random vectors $g_k : \Omega \to E_n$ and a deterministic starting point $x_0$, the **stochastic subgradient method** is the sequence of random vectors
--   $$
--   x_{k+1}(\omega) = x_k(\omega) - h_k\big(x_k(\omega)\big)\, g_k(\omega), \qquad k = 0, 1, \dots,
--   $$
--   where $g_k$ plays the role of the book's $g_\omega(x_k)$, the random direction drawn at iteration $k$. The stepsize $h_k(x_k)$ may depend on the current point, as in the book.
--
--   The probabilistic requirements on $g_k$ (conditional mean a subgradient, bounded conditional second moment) are stated as hypotheses of each theorem. Subgradients (inequality (1.3)) and the set $M^*$ of minimum points come from the series' shared definitions `IsSubgradient` and `MinSet`.
--
--   **Formalization Note** $E_n$ is `EuclideanSpace ℝ (Fin n)`. The iterates are defined by recursion (`stochIter h G x₀ k ω`), not postulated.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 9, inequality (1.3); p. 45, formula of the stochastic subgradient method

import Mathlib
import Definitions.Def_ShorNonsmooth_AlmostDiff_IsSubgradient
import Definitions.Def_ShorNonsmooth_SubgradMethod_SubgradientMethod

namespace ShorNonsmooth.Stochastic

/-- Shor (1985), p. 45, the formula of the **stochastic subgradient method**
`x_{k+1} = x_k - h_k(x_k) g_ω(x_k)`, `k = 0, 1, …`, started at the (deterministic) point `x₀`.
Here `h k : E_n → ℝ` is the stepsize rule of iteration `k` (the stepsize may depend on the
current point, `h_k(x_k)`), and `G k ω` is the random vector `g_ω(x_k)` drawn at iteration `k`
on the sample point `ω`. The iterate `x_k` is a random vector `Ω → E_n`. -/
noncomputable def stochIter {n : ℕ} {Ω : Type*}
    (h : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (G : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) : ℕ → Ω → EuclideanSpace ℝ (Fin n)
  | 0 => fun _ => x₀
  | k + 1 => fun ω => stochIter h G x₀ k ω - h k (stochIter h G x₀ k ω) • G k ω

end ShorNonsmooth.Stochastic


