-- Prove2me | Definitions.Def_ShorNonsmooth_AlmostDiff_almostGradients
-- name    : ShorNonsmooth_AlmostDiff_almostGradients
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T15:53:53.890221+00:00
-- url     : https://prove2.me/theorems/6d8b5f24-f10a-49cc-a3f0-268956f09644
-- title:
--   The set $G(x_0)$ of almost-gradients of $f$ at $x_0$
-- statement:
--   Let $f : E_n \to \mathbb{R}$ and $x_0 \in E_n$. A vector $g \in E_n$ is an **almost-gradient** of $f$ at $x_0$ if there is a sequence $x_1, x_2, \dots$ in $E_n$ with
--
--   $$
--   x_k \to x_0, \qquad f \text{ differentiable at every } x_k,
--   $$
--
--   such that $g$ is an accumulation point of the sequence of gradients $\nabla f(x_1), \nabla f(x_2), \dots$. The set of all almost-gradients of $f$ at $x_0$ is denoted $G(x_0)$.
--
--   Almost-gradients generalize the gradient to functions that are differentiable only almost everywhere; at a point where $\nabla f$ is continuous on its domain and $f$ is differentiable, the gradient itself is an almost-gradient.
--
--   **Formalization Note** "Accumulation point" is a cluster point of the sequence (a limit of a subsequence), not a limit of the whole sequence. The points $x_k$ may equal $x_0$, as the book does not exclude it.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 18, Definition (almost-gradient)

import Mathlib

namespace ShorNonsmooth.AlmostDiff

/-- Shor (1985), p. 18, Definition: the set `G(x₀)` of **almost-gradients** of `f` at `x₀`.
A vector `g` is an almost-gradient of `f` at `x₀` if it is an accumulation point (cluster point)
of a sequence of gradients `∇f(x₁), ∇f(x₂), …` where `x_k → x₀` and `f` is differentiable at
every `x_k` (the points `x_k = x₀` are not excluded). -/
def almostGradients {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {g | ∃ xs : ℕ → EuclideanSpace ℝ (Fin n),
      Filter.Tendsto xs Filter.atTop (nhds x₀) ∧
      (∀ k, DifferentiableAt ℝ f (xs k)) ∧
      MapClusterPt g Filter.atTop (fun k => gradient f (xs k))}

end ShorNonsmooth.AlmostDiff


