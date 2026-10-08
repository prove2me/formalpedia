-- Prove2me | Definitions.Def_CachonCoord_Proportional_Demand
-- name    : CachonCoord_Proportional_Demand
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:17:45.186979+00:00
-- url     : https://prove2.me/theorems/892a385d-4d3e-431c-a1f5-49463ea44d55
-- title:
--   §6.5.1, pp. 48–50 — total demand law with cdf F, density f, price p, cost c; S(q), I(q), Π(q) and the average (1/q)∫₀^q F
-- statement:
--   This is the newsvendor data of §6.5.1, the competing-newsvendor model with a fixed retail price.
--
--   1. **Total retail demand** $D$ has a law on $[0,\infty)$ with finite mean. Its distribution function $F$ satisfies $F(0)=0$, is strictly increasing on $[0,\infty)$ and is differentiable at every $y>0$ with derivative $f(y)$ (the density).
--   2. The **retail price** is $p$ and the supplier's **unit production cost** is $c$, with $0 < c < p$. The retailers' marginal cost, the goodwill costs and the salvage value are zero ($c_r = g_r = g_s = v = 0$).
--
--   From these data the section uses
--
--   $$
--   S(q) = \mathbb E[\min(q, D)], \qquad I(q) = \mathbb E[(q-D)^+], \qquad \Pi(q) = pS(q) - cq, \qquad \bar F(q) := \frac1q\int_0^q F(x)\,dx ,
--   $$
--
--   the expected sales, the expected leftover inventory, the integrated supply chain's expected profit at total stock $q$, and the average of $F$ over $[0,q]$ (the notation $\bar F$ is ours; the book writes the expression out).
--
--   Because demand is split in proportion to stock, total sales depend only on total stock, so the integrated chain faces the single newsvendor problem $\max_{q\ge0}\Pi(q)$.
--
--   **Formalization Note** $S$ and $I$ are defined as expectations; the book's integral forms ($S(q) = q - \int_0^q F$, $I(q) = \int_0^q F$) are consequences. The average $\bar F$ is written `avgF` and is meaningful only for $q > 0$ (at $q = 0$ Lean's $1/0 = 0$ makes it $0$); every theorem uses it at a positive argument. The hypotheses on $F$ are the chapter's standing assumptions (§6.2.1, p. 7: "F is differentiable, strictly increasing and F(0) = 0"; $\mu = E[D]$). The condition $c > 0$ is implicit on the page: (20) requires $F(q^o) = (p-c)/p < 1$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.1, pp. 48–50 (model paragraph, (20)); standing assumptions §6.2.1, p. 7; S(q), I(q) as on p. 10

import Mathlib

namespace CachonCoord.Proportional

open MeasureTheory ProbabilityTheory

/-- The newsvendor data of §6.5.1 (Cachon 2003, 3rd draft, pp. 48–50), with the chapter's
standing assumptions of §6.2.1 (p. 7) and the zeros `c_r = g_r = g_s = v = 0` of p. 48.

* `law` is the law of the total retail demand `D`: a probability measure on `[0, ∞)` with finite
  mean; its distribution function `F = cdf law` satisfies `F(0) = 0`, is strictly increasing on
  `[0, ∞)`, and is differentiable at every `y > 0` with derivative `density y` (the book's `f`).
* `p` is the retail price and `c` (`= c_s`, since `c_r = 0`) the supplier's unit production
  cost, with `0 < c < p`. -/
structure Model where
  /-- Law of the total retail demand `D`. -/
  law : Measure ℝ
  isProb : IsProbabilityMeasure law
  nonneg : law (Set.Iio 0) = 0
  integrable : Integrable (fun d : ℝ => d) law
  /-- `F(0) = 0`. -/
  cdf_zero : cdf law 0 = 0
  /-- `F` is strictly increasing on `[0, ∞)`. -/
  strictMonoOn_cdf : StrictMonoOn (cdf law) (Set.Ici 0)
  /-- The density `f`. -/
  density : ℝ → ℝ
  /-- `F` is differentiable on `(0, ∞)` with derivative `f`. -/
  hasDerivAt_cdf : ∀ y : ℝ, 0 < y → HasDerivAt (cdf law) (density y) y
  /-- Retail price `p`. -/
  p : ℝ
  /-- Unit production cost `c`. -/
  c : ℝ
  c_pos : 0 < c
  c_lt_p : c < p

namespace Model

variable (M : Model)

/-- The distribution function `F` of total demand. -/
noncomputable def F (y : ℝ) : ℝ := cdf M.law y

/-- Expected sales `S(q) = E[min(q, D)]` (p. 10). -/
noncomputable def S (q : ℝ) : ℝ := ∫ d, min q d ∂M.law

/-- Expected leftover inventory `I(q) = E[(q − D)⁺]` (p. 10). -/
noncomputable def I (q : ℝ) : ℝ := ∫ d, max (q - d) 0 ∂M.law

/-- The integrated supply chain's expected profit `Π(q) = pS(q) − cq` at total stock `q`. -/
noncomputable def chainProfit (q : ℝ) : ℝ := M.p * M.S q - M.c * q

/-- The average of `F` over `[0, q]`, `(1/q) ∫_0^q F(x) dx` (meaningful for `q > 0`). -/
noncomputable def avgF (q : ℝ) : ℝ := (1 / q) * ∫ x in (0 : ℝ)..q, M.F x

end Model

end CachonCoord.Proportional


