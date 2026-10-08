-- Prove2me | Definitions.Def_SmithHitAndRun_RandomDir_RateConstants
-- name    : SmithHitAndRun_RandomDir_RateConstants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:23:19.780255+00:00
-- url     : https://prove2.me/theorems/bb227c1b-36a4-485f-ad03-3a0dee7c3e37
-- title:
--   Constants of Theorem 3: $\gamma$, $S_n(r)$, the density $f(y\mid x)$ and $\delta=2/dS_n(d)$
-- statement:
--   Let $S\subseteq\mathbb R^n$ be a region, $V$ the $n$-dimensional content and $V_n(r)$ the volume of a ball of radius $r$ in $\mathbb R^n$.
--
--   1. The **radius of the smallest enclosing ball** is $R^\star=\inf\{r:\exists c,\ S\subseteq \bar B(c,r)\}$; for bounded nonempty $S$ the infimum is attained.
--   2. The ratio
--   $$\gamma=\frac{V(S)}{V_n(R^\star)}$$
--   is the ratio of the content of $S$ to the content of the smallest ball containing $S$.
--   3. The **surface area** of a sphere of radius $r$ is $S_n(r)=n\,V_n(1)\,r^{n-1}$.
--   4. The **density** of the Random Directions transition at $y$ from $x$ is
--   $$f(y\mid x)=\frac{2}{S_n(r(x,y))\,\ell(x,y)}\in[0,\infty],$$
--   where $r(x,y)=\|y-x\|$ and $\ell(x,y)$ is the length of the line set of $S$ through $x$ in the direction $(y-x)/\|y-x\|$.
--   5. With $d=\operatorname{diam} S$, the constant $\delta=\dfrac{2}{d\,S_n(d)}$.
--
--   These are the quantities in the statement and the proof of Theorem 3.
--
--   **Formalization Note** "Sphere" in the paper's "smallest sphere containing $S$" means ball. The paper writes $d(x,y)$, the diameter of $S$ along the ray from $x$ to $y$; for non-convex $S$ the algorithm samples uniformly on the whole line set, so the length $\ell(x,y)$ of the line set is used (it equals the chord length for convex $S$). The paper's $d=\max_{x,y\in S}d(x,y)$ is taken as the diameter of $S$ (`Metric.diam S`), which bounds both $r(x,y)$ and $\ell(x,y)$ for every region. $f$ is valued in $[0,\infty]$ (`ENNReal`); its value at $y=x$ is irrelevant (a null set).
-- source:
--   Smith, Efficient Monte Carlo Procedures for Generating Points Uniformly Distributed over Bounded Regions, Oper. Res. 32(6) (1984), p. 1304, Theorem 3 and its proof

import Mathlib
import Definitions.Def_SmithHitAndRun_RandomDir_RandomDirectionsKernel

namespace SmithHitAndRun.RandomDir

open MeasureTheory

/-- The radius of the smallest (closed) ball containing `S` (Smith 1984, p. 1304, Theorem 3:
"the smallest sphere containing `S`"): `R⋆ = inf {r : ∃ c, S ⊆ B̄(c, r)}`. For a bounded nonempty
`S` the infimum is attained, so `B̄(c, R⋆)` is the smallest enclosing ball. -/
noncomputable def enclosingRadius {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  sInf {r : ℝ | ∃ c : EuclideanSpace ℝ (Fin n), S ⊆ Metric.closedBall c r}

/-- `γ` of Smith 1984, p. 1304, Theorem 3: the ratio of the `n`-dimensional content of `S` to the
`n`-dimensional content of the smallest ball containing `S`. -/
noncomputable def gammaRatio {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  (volume S).toReal /
    (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (enclosingRadius S))).toReal

/-- `S_n(r)`, the surface area of a sphere of radius `r` in `ℝⁿ` (Smith 1984, p. 1304, proof of
Theorem 3): `S_n(r) = n · V_n(1) · r^{n-1}`, where `V_n(1)` is the volume of the unit ball. -/
noncomputable def surfaceArea (n : ℕ) (r : ℝ) : ℝ :=
  n * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal * r ^ (n - 1)

/-- The transition density of the Random Directions Algorithm (Smith 1984, p. 1304, proof of
Theorem 3): `f(y | x) = 2 / (S_n(r(x,y)) · ℓ(x,y))`, where `r(x,y) = ‖y − x‖` and `ℓ(x,y)` is the
length of the line set of `S` through `x` in direction `(y − x)/‖y − x‖` (the paper's `d(x,y)`,
the diameter of `S` along that ray, for convex `S`). Valued in `[0, ∞]`. -/
noncomputable def rdDensity {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (x y : EuclideanSpace ℝ (Fin n)) : ENNReal :=
  2 / (ENNReal.ofReal (surfaceArea n ‖y - x‖) * lineLength S x (‖y - x‖⁻¹ • (y - x)))

/-- The minorization constant of the proof of Theorem 3 (Smith 1984, p. 1304):
`δ = 2 / (d · S_n(d))` with `d` the diameter of `S`. -/
noncomputable def deltaConst {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  2 / (Metric.diam S * surfaceArea n (Metric.diam S))

end SmithHitAndRun.RandomDir


