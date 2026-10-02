-- Prove2me | Definitions.Def_ShorNonsmooth_SubgradMethod_SubgradientMethod
-- name    : ShorNonsmooth_SubgradMethod_SubgradientMethod
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T15:59:22.843385+00:00
-- url     : https://prove2.me/theorems/9fa874ef-106a-45c1-9845-b4b80a0e101c
-- title:
--   The set of minimum points and the three subgradient iterations (2.4), (2.5) and the restarted method
-- statement:
--   Throughout, $E_n$ is the $n$-dimensional Euclidean space with inner product $(x,y)$, and $f : E_n \to \mathbb{R}$ is a function finite everywhere. A vector $g \in E_n$ is a **subgradient** of $f$ at $x_0$ if $f(x) - f(x_0) \ge (g,\, x - x_0)$ for all $x \in E_n$ (inequality (1.3); this notion is imported from the separate definition of subgradients).
--
--   1. The set of **minimum points** of $f$ is $M^* = \{x \in E_n : f(x) \le f(y) \text{ for all } y \in E_n\}$.
--
--   Fix a **subgradient selection** $g_f : E_n \to E_n$ (in the theorems, $g_f(x)$ is required to be a subgradient of $f$ at $x$ for every $x$), a sequence of stepsizes $h_1, h_2, \dots$ and a starting point $x_0$. Three iterations are defined:
--
--   2. the **normalized subgradient method** (2.4):
--   $$
--   x_{k+1} = x_k - h_{k+1}\,\frac{g_f(x_k)}{\|g_f(x_k)\|}, \qquad k = 0, 1, \dots,
--   $$
--   which, when all $h_k$ equal a constant $h$, is the method with stepsizes $h_{k+1}(x_k) = h/\|g_f(x_k)\|$ of Theorem 2.1; if $g_f(x_k) = 0$ the computation stops, and the sequence is taken to stay at $x_k$ from then on;
--   3. the **subgradient method** (2.5): $x_{k+1} = x_k - h_{k+1}\, g_f(x_k)$;
--   4. the **subgradient method with restarts** of Theorem 2.4, for a constant $c$: $x_{k+1} = x_k - h_{k+1}\, g_f(x_k)$ if $h_{k+1}\|g_f(x_k)\| \le c$, and $x_{k+1} = x_0$ otherwise.
--
--   These are the objects of all convergence results of Sections 2.1–2.2.
--
--   **Formalization Note** $E_n$ is `EuclideanSpace ℝ (Fin n)`. The stepsize sequence is a function `h : ℕ → ℝ`; the value `h 0` is never used by the iterations. In (2.4) the case $g_f(x_k) = 0$ is handled by an explicit branch (the iterate is repeated), not by Lean's convention $x/0 = 0$; a zero subgradient means $x_k \in M^*$, which is where the book stops.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 9, inequality (1.3); p. 22, formula (2.1); p. 23 (stepsizes h/‖g_f(x_k)‖); p. 25, formula (2.4); p. 26, formula (2.5); p. 27, formula of Theorem 2.4

import Mathlib
import Definitions.Def_ShorNonsmooth_AlmostDiff_IsSubgradient

namespace ShorNonsmooth.SubgradMethod

/-- Shor (1985), p. 22 ff.: the set `M*` of **minimum points** of `f` on `E_n`. -/
def MinSet {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ y, f x ≤ f y}

/-- Shor (1985), p. 25, formula (2.4) (and, with a constant sequence `h k = h`, the method with
stepsizes `h_{k+1}(x_k) = h / ‖g_f(x_k)‖` of Theorem 2.1, p. 23): the **normalized subgradient
method** `x_{k+1} = x_k - h_{k+1} g(x_k) / ‖g(x_k)‖`, started at `x₀`, where `g` is a subgradient
selection (`g x` a subgradient of `f` at `x`)
and `h (k + 1)` is the stepsize used at step `k` (`h 0` is never read).
When `g(x_k) = 0` the book stops the computation (`x_k` is then a minimum point, p. 23); here the
sequence stays at `x_k` from then on, which is explicit and does not rely on division by zero. -/
noncomputable def normalizedIter {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (h : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => x₀
  | k + 1 =>
      if g (normalizedIter g h x₀ k) = 0 then normalizedIter g h x₀ k
      else normalizedIter g h x₀ k -
        (h (k + 1) / ‖g (normalizedIter g h x₀ k)‖) • g (normalizedIter g h x₀ k)

/-- Shor (1985), p. 26, formula (2.5): the **(unnormalized) subgradient method**
`x_{k+1} = x_k - h_{k+1} g(x_k)`, `k = 0, 1, …`, started at `x₀`. -/
noncomputable def plainIter {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (h : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => x₀
  | k + 1 => plainIter g h x₀ k - h (k + 1) • g (plainIter g h x₀ k)

/-- Shor (1985), p. 27, the formula of Theorem 2.4: the **subgradient method with restarts**
`x_{k+1} = x_k - h_{k+1} g(x_k)` if `h_{k+1} ‖g(x_k)‖ ≤ c`, and `x_{k+1} = x₀` otherwise. -/
noncomputable def resetIter {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (h : ℕ → ℝ) (c : ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => x₀
  | k + 1 =>
      if h (k + 1) * ‖g (resetIter g h c x₀ k)‖ ≤ c then
        resetIter g h c x₀ k - h (k + 1) • g (resetIter g h c x₀ k)
      else x₀

end ShorNonsmooth.SubgradMethod


