-- Prove2me | Definitions.Def_LCAntiConc_IsLogConcave
-- name    : LCAntiConc_IsLogConcave
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:58.709355+00:00
-- url     : https://prove2.me/theorems/f37f7e2d-3c76-46b9-adfb-527260aee85d
-- title:
--   Log-concave random vector
-- statement:
--   A random vector $X\in\mathbb R^d$ is **log-concave** if its law has a density $e^{-V}$ with respect to Lebesgue measure for a convex function $V:\mathbb R^d\to\mathbb R\cup\{+\infty\}$.
--
--   Equivalently, writing $f=e^{-V}\ge0$ (with $f=0$ where $V=+\infty$), the law is $f(x)\,dx$ and
--
--   $$f\big((1-\theta)x+\theta y\big)\ge f(x)^{1-\theta}f(y)^{\theta}\qquad(x,y\in\mathbb R^d,\ \theta\in[0,1]).$$
--
--   Gaussian laws, uniform laws on convex bodies and products of one-dimensional log-concave laws are examples.
--
--   **Formalization Note** Lean states the second form, with real powers of nonnegative reals; no measurability or continuity of $f$ is imposed, as on the page. A law without a Lebesgue density (a Dirac mass, a law on a hyperplane) is not log-concave in this sense.
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), §3 Notation, p.15 (PDF p.17)

import Mathlib

namespace LCAntiConc

open MeasureTheory

/-- A random vector `X ∈ ℝ^d` (law `μ`) is log-concave: it has a density `e^{-V}` with respect to
Lebesgue measure for a convex `V : ℝ^d → ℝ ∪ {+∞}`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), §3 Notation, p.15 (PDF p.17).

**Formalization Note** Written with `f = e^{-V}`: a density `f ≥ 0` (with `f = 0` where
`V = +∞`) such that `f((1-θ)x + θy) ≥ f(x)^{1-θ} f(y)^θ` for all `x, y` and `θ ∈ [0, 1]`; this is
exactly convexity of `V = -log f` with values in `ℝ ∪ {+∞}`. The powers are real powers of
nonnegative reals. No measurability or continuity of `f` is required, as on the page. -/
def IsLogConcave {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ f : EuclideanSpace ℝ (Fin d) → ℝ, (∀ x, 0 ≤ f x) ∧
    μ = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
    ∀ x y, ∀ θ ∈ Set.Icc (0 : ℝ) 1, f x ^ (1 - θ) * f y ^ θ ≤ f ((1 - θ) • x + θ • y)

end LCAntiConc


