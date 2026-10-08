-- Prove2me | Definitions.Def_ServiceParts_StockLevels_Basic
-- name    : ServiceParts_StockLevels_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T06:40:04.904758+00:00
-- url     : https://prove2.me/theorems/e99ba7c3-63e3-4bf7-8b81-4a328b0f578a
-- title:
--   Forward differences, the Poisson pmf and the simple-Poisson fill rate F(s)
-- statement:
--   Basic objects for stock levels $s = 0, 1, 2, \dots$ of an item managed by an $(s-1, s)$ policy.
--
--   1. For a function $f$ on the nonnegative integers, the **first and second forward differences** are
--   $$\Delta f(s) = f(s+1) - f(s), \qquad \Delta^2 f(s) = \Delta f(s+1) - \Delta f(s).$$
--   A function is discretely convex (concave) where $\Delta^2 f \ge 0$ ($\le 0$).
--   2. For a mean $a$ (in the book $a = \lambda\bar\tau$, demand rate times mean resupply time), the **Poisson probability** of the value $x$ is
--   $$p(x \mid a) = e^{-a}\,\frac{a^x}{x!}.$$
--   3. Under simple Poisson demand, the **fill rate** at stock level $s$ is the probability that fewer than $s$ units are in resupply:
--   $$F(s) = \sum_{x < s} p(x \mid a).$$
--   (The $j$-fold convolution $u^{(j)}_x$ of an order-size distribution, used by the compound Poisson demand model, is not defined here: it is `ServiceParts.Palm.convPow` of the shared module this file imports.)
--
--   These are the building blocks of the performance measures of Sections 3.2 and 3.3 of the book.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 49, 52-53, Sections 3.2-3.3 (u_x^(j), p(x|λτ̄) for simple Poisson demand, F(s) = Σ_{x<s} p(x|λτ̄), ΔF and Δ²F)

import Mathlib
import Definitions.Def_ServiceParts_Palm_CompoundResupplySystem

namespace ServiceParts.StockLevels

/-- First forward difference of a function on the stock levels `s = 0, 1, …`:
`Δf(s) = f(s + 1) - f(s)` (Muckstadt 2005, p. 53). -/
def fdiff (f : ℕ → ℝ) (s : ℕ) : ℝ := f (s + 1) - f s

/-- Second forward difference `Δ²f(s) = Δf(s + 1) - Δf(s)` (Muckstadt 2005, p. 53). -/
def fdiff2 (f : ℕ → ℝ) (s : ℕ) : ℝ := fdiff f (s + 1) - fdiff f s

/-- The Poisson probability `e^{-a} a^x / x!` of the value `x` for mean `a`
(Muckstadt 2005, p. 52: `p(x|λτ̄)` for simple Poisson demand, with `a = λτ̄`). -/
noncomputable def poissonPmf (a : ℝ) (x : ℕ) : ℝ :=
  Real.exp (-a) * a ^ x / (x.factorial : ℝ)

/-- The fill rate under simple Poisson demand, `F(s) = Σ_{x < s} p(x|a)`
(Muckstadt 2005, p. 52), for stock level `s` and mean lead-time demand `a = λτ̄`. -/
noncomputable def poissonFillRate (a : ℝ) (s : ℕ) : ℝ :=
  ∑ x ∈ Finset.range s, poissonPmf a x

end ServiceParts.StockLevels


