-- Prove2me | Definitions.Def_QGChasing_IsCPDBalanced
-- name    : QGChasing_IsCPDBalanced
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:28:11.533619+00:00
-- url     : https://prove2.me/theorems/0da2cdd1-63cf-4ca8-8c94-e40754f79e38
-- title:
--   Balanced step of Clipped Proximal Descent (Algorithm 1, line 7)
-- statement:
--   Let $\kappa\ge1$, $X\subseteq\mathbb R^d$, $f:\mathbb R^d\to\mathbb R$ with global minimizer $v$, $g=f-f(v)$, and let $p=x_{t-1}$ be the previous decision. A triple $(\mu,y,x)$ is **the balanced step of CPD** if
--
--   1. $\mu>0$ and $y$ is the proximal point $y(\mu)=\arg\min_{z\in X}\big(g(z)+\|z-p\|^2/(2\mu)\big)$ of (8);
--   2. $y$ is balanced: $g(y)=\beta\|y-p\|$;
--   3. $\mu$ is the smallest such parameter: no $\mu'\in(0,\mu)$ has a balanced proximal point $y(\mu')$;
--   4. with $s=\|y-p\|$, $\gamma=\frac{r^2s}{s+\beta\mu}$ and $\eta=\min\{\gamma, rs/\|y-v\|\}$,
--   $$
--   x=\Pi_{X\cap\{z:\,g(z)\le g(y)\}}\big((1-\eta)y+\eta v\big).
--   $$
--
--   Then $\mu_t=\mu$, $y_t=y$ and $x_t=x$ in line 7 of Algorithm 1. In words: the proximal step is chosen so that its hitting cost equals $\beta$ times its movement, then a clipped step toward the minimizer is taken and projected back onto the feasible sublevel set.
--
--   **Formalization Note** Item 3 encodes "the smallest $\mu_t>0$"; since the proximal point is unique for each $\mu>0$, it says exactly that $\mu$ is the least balanced parameter. The proximal point and the projection are relations; the projection is membership in the published nearest-point set `SuperPolyak.nearestPoints`.
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), Algorithm 1, line 7, p.5; pp.6, 13

import Mathlib
import Definitions.Def_SuperPolyak_solutionSet
import Definitions.Def_QGChasing_IsProxPoint
import Definitions.Def_QGChasing_cpdBeta
import Definitions.Def_QGChasing_cpdEta

namespace QGChasing

/-- The balanced case of Clipped Proximal Descent, Algorithm 1, line 7 (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), p.5; pp.6, 13).
With `g(z) = f(z) − f(v)` (`v` the global minimizer of `f`) and previous decision `p = x_{t−1}`,
the data `(μ, y, x)` is: `μ = μ_t > 0` is the **smallest** positive parameter whose proximal point
`y(μ)` (Eq. (8)) is balanced, `g(y(μ)) = β‖y(μ) − p‖`; `y = y_t = y(μ_t)`; and `x = x_t` is the
projection of `(1 − η_t) y_t + η_t v` onto `X ∩ {z : g(z) ≤ g(y_t)}`, with
`s_t = ‖y_t − p‖`, `γ_t = r²s_t/(s_t + βμ_t)`, `η_t = min{γ_t, r s_t/‖y_t − v‖}`.

**Formalization Note** "The smallest `μ_t > 0`" is the fourth clause: no `μ' ∈ (0, μ)` has a
balanced proximal point. Since the proximal point is unique for each `μ > 0` (p.13), this is
exactly minimality of `μ_t` among the balanced parameters. The proximal point and the projection
are relational (`IsProxPoint`, and the published nearest-point set `SuperPolyak.nearestPoints`). -/
def IsCPDBalanced {d : ℕ} (κ : ℝ) (X : Set (EuclideanSpace ℝ (Fin d))) (f : EuclideanSpace ℝ (Fin d) → ℝ) (p v : EuclideanSpace ℝ (Fin d)) (μ : ℝ)
    (y x : EuclideanSpace ℝ (Fin d)) : Prop :=
  0 < μ ∧
  IsProxPoint (fun z => f z - f v) X p μ y ∧
  f y - f v = cpdBeta κ * ‖y - p‖ ∧
  (∀ μ' : ℝ, 0 < μ' → μ' < μ → ∀ y' : EuclideanSpace ℝ (Fin d), IsProxPoint (fun z => f z - f v) X p μ' y' →
      f y' - f v ≠ cpdBeta κ * ‖y' - p‖) ∧
  x ∈ SuperPolyak.nearestPoints (X ∩ {z | f z - f v ≤ f y - f v})
    ((1 - cpdEta κ ‖y - p‖ μ ‖y - v‖) • y + cpdEta κ ‖y - p‖ μ ‖y - v‖ • v)

end QGChasing


