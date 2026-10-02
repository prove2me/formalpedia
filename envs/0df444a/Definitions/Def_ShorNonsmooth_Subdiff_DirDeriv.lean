-- Prove2me | Definitions.Def_ShorNonsmooth_Subdiff_DirDeriv
-- name    : ShorNonsmooth_Subdiff_DirDeriv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T15:09:50.629749+00:00
-- url     : https://prove2.me/theorems/c1da13cf-460c-4e51-b7f5-f4c78fcd73dd
-- title:
--   One-sided directional derivative $f'_\eta(x_0)$ and direction of steepest descent
-- statement:
--   Let $f : E_n \to \mathbb{R}$ and $x_0, \eta \in E_n$. The number $d$ is the **one-sided directional derivative** of $f$ at $x_0$ in the direction $\eta$ if
--
--   $$
--   f'_\eta(x_0) = \lim_{t \to 0+} \frac{f(x_0 + t\eta) - f(x_0)}{t} = d,
--   $$
--
--   the limit being taken from the right and being finite.
--
--   A direction $\eta \neq 0$ is a **direction of steepest descent** of $f$ at $x_0$ if
--
--   $$
--   \min_{\|\xi\| = 1} f'_\xi(x_0) = \frac{1}{\|\eta\|}\, f'_\eta(x_0),
--   $$
--
--   that is, $f'_\eta(x_0)$ exists and $f'_\eta(x_0)/\|\eta\|$ is the least value of $f'_\xi(x_0)$ over unit vectors $\xi$ (the minimum is attained).
--
--   These notions describe first-order behaviour of a nonsmooth convex function along rays and underlie the max formula for directional derivatives.
--
--   **Formalization Note** The set over which the minimum is taken consists of the values $f'_\xi(x_0)$ for unit vectors $\xi$ at which the derivative exists; for a convex $f$ at an interior point of its domain it exists in every direction, so this is the book's minimum over all unit vectors.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 10 (proof of Theorem 1.8, one-sided directional derivative) and p. 12 (definition of a direction of steepest descent)

import Mathlib

open Filter Topology

namespace ShorNonsmooth.Subdiff

/-- Shor (1985), p. 10 (proof of Theorem 1.8): `f` has **one-sided directional derivative** `d`
at `x₀` in direction `η`, i.e. `f′_η(x₀) = lim_{t → 0+} (f(x₀ + tη) - f(x₀)) / t = d`
(a finite limit from the right). -/
def HasOneSidedDirDeriv {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ η : EuclideanSpace ℝ (Fin n)) (d : ℝ) : Prop :=
  Tendsto (fun t : ℝ => (f (x₀ + t • η) - f x₀) / t) (𝓝[>] 0) (𝓝 d)

/-- Shor (1985), p. 12: a direction `η ≠ 0` is a **direction of steepest descent** of `f` at
`x₀` if `min_{‖ξ‖ = 1} f′_ξ(x₀) = (1/‖η‖) f′_η(x₀)`: the one-sided directional derivative
`f′_η(x₀)` exists, and `f′_η(x₀) / ‖η‖` is the least value of `f′_ξ(x₀)` over unit vectors `ξ`
(the minimum is attained). -/
def IsSteepestDescentDir {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ η : EuclideanSpace ℝ (Fin n)) : Prop :=
  η ≠ 0 ∧ ∃ d : ℝ, HasOneSidedDirDeriv f x₀ η d ∧
    IsLeast {c : ℝ | ∃ ξ : EuclideanSpace ℝ (Fin n), ‖ξ‖ = 1 ∧ HasOneSidedDirDeriv f x₀ ξ c}
      (d / ‖η‖)

end ShorNonsmooth.Subdiff


