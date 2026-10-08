-- Prove2me | Definitions.Def_ShorNonsmooth_Stochastic_NonconvexMethod
-- name    : ShorNonsmooth_Stochastic_NonconvexMethod
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T12:43:29.964535+00:00
-- url     : https://prove2.me/theorems/a175bbff-ed35-4c58-abb6-0f6bb0598aba
-- title:
--   Bazhenov's subgradient method with restarts (Theorem 2.18)
-- statement:
--   Let $f : E_n \to \mathbb{R}$. Given a selection $g_f : E_n \to E_n$ (in Theorem 2.18, of almost-gradients, from the series' shared definitions `AlmostDifferentiable` and `almostGradients`), a point $x^*$, a radius $r$, stepsizes $h_k$ and a starting point $x_0$, put $S_r = \{x : \|x - x^*\| \le r\}$ and
--   $$
--   \bar x_{k+1} = x_k - h_k \frac{g_f(x_k)}{\|g_f(x_k)\|}, \qquad
--   x_{k+1} = \begin{cases} \bar x_{k+1} & \text{if } \bar x_{k+1} \in S_r, \\ x_0 & \text{if } \bar x_{k+1} \notin S_r. \end{cases}
--   $$
--   This is the **subgradient method with restarts** of L. G. Bazhenov (Theorem 2.18).
--
--   **Formalization Note** The formula for $\bar x_{k+1}$ is undefined when $g_f(x_k) = 0$; the computation then stops, and the sequence is taken to stay at $x_k$ from then on (an explicit branch, not Lean's convention $x/0 = 0$).
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 17, Definition (almost differentiable); p. 18, Definition (almost-gradient); p. 45, formula of Theorem 2.18

import Mathlib
import Definitions.Def_ShorNonsmooth_AlmostDiff_AlmostDifferentiable
import Definitions.Def_ShorNonsmooth_AlmostDiff_almostGradients

namespace ShorNonsmooth.Stochastic

/-- Shor (1985), p. 45, the iteration of Theorem 2.18 (L. G. Bazhenov): with
`x̄_{k+1} = x_k - h_k g(x_k)/‖g(x_k)‖`, set `x_{k+1} = x̄_{k+1}` if `x̄_{k+1} ∈ S_r`
(the closed ball `{x : ‖x - xstar‖ ≤ r}`) and `x_{k+1} = x₀` otherwise.
The book's formula is undefined when `g(x_k) = 0`; the computation then stops, and here the
sequence stays at `x_k` from then on (explicit branch, not Lean's `x / 0 = 0`). -/
noncomputable def resetIter {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (h : ℕ → ℝ)
    (xstar : EuclideanSpace ℝ (Fin n)) (r : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => x₀
  | k + 1 =>
      if g (resetIter g h xstar r x₀ k) = 0 then resetIter g h xstar r x₀ k
      else
        if ‖resetIter g h xstar r x₀ k -
              (h k / ‖g (resetIter g h xstar r x₀ k)‖) • g (resetIter g h xstar r x₀ k) -
              xstar‖ ≤ r then
          resetIter g h xstar r x₀ k -
            (h k / ‖g (resetIter g h xstar r x₀ k)‖) • g (resetIter g h xstar r x₀ k)
        else x₀

end ShorNonsmooth.Stochastic


