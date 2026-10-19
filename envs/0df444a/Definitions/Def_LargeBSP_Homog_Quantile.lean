-- Prove2me | Definitions.Def_LargeBSP_Homog_Quantile
-- name    : LargeBSP_Homog_Quantile
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:07:30.495023+00:00
-- url     : https://prove2.me/theorems/7ccda1a4-0c57-473d-8059-f8dc25134a0b
-- title:
--   (4), (8), p. 8–9 and p. 12 — empirical distribution function 𝔽_{x,N} and quantile function F^{-1}(s) = inf{y ≥ 0 : F(y) ≥ s}
-- statement:
--   Two general objects used throughout the mission.
--
--   1. **Empirical distribution function.** For a sequence $x = (x_1, x_2, \dots)$ of reals and $N \ge 1$,
--   $$\mathbb F_{x,N}(y) = \frac1N \sum_{n=1}^N \mathbf 1\{x_n \le y\}, \qquad y \in \mathbb R,$$
--   the fraction of the first $N$ coordinates that are at most $y$. With $x = X(\omega)$ a customer's valuations it is $\mathbb F_{X,N}$ of display (4); with $x = c$ the marginal costs it is $\mathbb F_{C,N}$ of display (8).
--
--   2. **Quantile function.** For a function $F : \mathbb R \to \mathbb R$ (a distribution function) and $s \in \mathbb R$,
--   $$F^{-1}(s) = \inf\{\, y \ge 0 : F(y) \ge s \,\}.$$
--   With $F = F_X$ this is the quantile function of $F_X$ (p. 12, for $s \in (0,1)$), and with $F = \mathbb F_{X,N}$ it is the empirical quantile function $\mathbb F^{-1}_{X,N}$ used in the proof of Theorem 2.
--
--   These are the standard empirical cdf and left-continuous generalized inverse, restricted to the nonnegative half-line as the paper does for nonnegative valuations.
--
--   **Formalization Note** Items are 0-indexed: coordinate `n < N` is the page's item $n+1$. At $N = 0$ the empirical cdf is $0/0 = 0$; every statement uses it as $N \to \infty$. When the set $\{y \ge 0 : F(y) \ge s\}$ is empty (for a distribution function: $s > 1$, or $s = 1$ when $F < 1$ everywhere) the Lean value is $\inf \emptyset = 0$; for $s \in (0,1)$ and a probability distribution function the set is nonempty and bounded below by $0$, so the value is the true infimum. All uses are at $s \in (0,1)$ or inside integrals over $(0,1)$, which do not see the endpoints.
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), (4), p. 8; (8), p. 9; §4.2, p. 12 (quantile F_X^{-1})

import Mathlib

namespace LargeBSP.Homog

/-- The empirical distribution function of the first `N` coordinates of `x`,
`𝔽_{x,N}(y) = (1/N) · #{n < N : x n ≤ y}` (Abdallah–Asadpour–Reed, (4), p. 8; with `x := c` it is
the cost version (8), p. 9). Items are 0-indexed: `n < N` is the page's item `n + 1`. At `N = 0` the
value is `0 / 0 = 0`; every statement uses it as `N → ∞`. -/
noncomputable def empCdf (x : ℕ → ℝ) (N : ℕ) (y : ℝ) : ℝ :=
  (((Finset.range N).filter (fun n => x n ≤ y)).card : ℝ) / N

/-- The quantile function `F⁻¹(s) = inf {y ≥ 0 : F(y) ≥ s}` of a distribution function `F`
(p. 12, "for s ∈ (0,1)"). Used with `F = cdf ν` (`F_X⁻¹`) and with `F = empCdf x N` (`𝔽⁻¹_{X,N}`).
When the set is empty (e.g. `s > 1`) the value is `sInf ∅ = 0`; the set is bounded below by `0`,
so whenever it is nonempty the value is its infimum. -/
noncomputable def quantile (F : ℝ → ℝ) (s : ℝ) : ℝ :=
  sInf {y : ℝ | 0 ≤ y ∧ s ≤ F y}

end LargeBSP.Homog


