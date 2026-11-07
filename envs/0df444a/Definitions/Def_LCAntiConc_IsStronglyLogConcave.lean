-- Prove2me | Definitions.Def_LCAntiConc_IsStronglyLogConcave
-- name    : LCAntiConc_IsStronglyLogConcave
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:00.324856+00:00
-- url     : https://prove2.me/theorems/b22fb67f-bc69-4753-b6fb-8e7ed524c063
-- title:
--   $\kappa$-strongly log-concave random vector
-- statement:
--   A random vector $X\in\mathbb R^d$ is **$\kappa$-strongly log-concave** if its law has a density $e^{-V}$ with $V:\mathbb R^d\to\mathbb R\cup\{+\infty\}$ such that $V(x)-\kappa\|x\|_2^2/2$ is convex.
--
--   Equivalently, with the density $f=e^{-V}\ge0$, the function $g(x)=f(x)\,e^{\kappa\|x\|_2^2/2}$ satisfies
--
--   $$g\big((1-\theta)x+\theta y\big)\ge g(x)^{1-\theta}g(y)^{\theta}\qquad(x,y\in\mathbb R^d,\ \theta\in[0,1]).$$
--
--   The standard Gaussian is $1$-strongly log-concave.
--
--   **Formalization Note** Lean states the second form with the Euclidean norm.
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), §3 Notation, p.15 (PDF p.17)

import Mathlib

namespace LCAntiConc

open MeasureTheory

/-- A random vector `X ∈ ℝ^d` (law `μ`) is `κ`-strongly log-concave: it has a density `e^{-V}` with
`V(x) - κ‖x‖₂²/2` convex, `V : ℝ^d → ℝ ∪ {+∞}`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), §3 Notation, p.15 (PDF p.17).

**Formalization Note** Written with the density `f = e^{-V} ≥ 0`: the function
`g(x) = f(x) e^{κ‖x‖²/2} = e^{-(V(x) - κ‖x‖²/2)}` satisfies
`g((1-θ)x + θy) ≥ g(x)^{1-θ} g(y)^θ` for all `x, y` and `θ ∈ [0, 1]`, which is convexity of
`V - κ‖·‖²/2` with values in `ℝ ∪ {+∞}`. The norm is Euclidean. -/
def IsStronglyLogConcave {d : ℕ} (κ : ℝ) (μ : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ f : EuclideanSpace ℝ (Fin d) → ℝ, (∀ x, 0 ≤ f x) ∧
    μ = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
    ∀ x y, ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      (f x * Real.exp (κ * ‖x‖ ^ 2 / 2)) ^ (1 - θ) * (f y * Real.exp (κ * ‖y‖ ^ 2 / 2)) ^ θ ≤
        f ((1 - θ) • x + θ • y) * Real.exp (κ * ‖(1 - θ) • x + θ • y‖ ^ 2 / 2)

end LCAntiConc


