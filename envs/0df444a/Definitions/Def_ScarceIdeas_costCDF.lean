-- Prove2me | Definitions.Def_ScarceIdeas_costCDF
-- name    : ScarceIdeas_costCDF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:05.016517+00:00
-- url     : https://prove2.me/theorems/0534d389-af05-4e33-8fd1-9f2c0f468872
-- title:
--   Cumulative cost distribution $F(x)=\int_{\underline c}^{x}f$
-- statement:
--   The **cumulative cost distribution** is
--
--   $$F(x)=\int_{\underline c}^{x}f(c)\,dc .$$
--
--   An idea with cost $c$ is invested in exactly when $c\le p$, so $F(p)$ is the probability that an arriving idea is viable under the reward $p$.
--
--   **Formalization Note** An interval integral from $\underline c$; when $f$ vanishes off $[\underline c,\overline c]$ it is the distribution function on all of $\mathbb R$ ($F=0$ below $\underline c$, $F=1$ above $\overline c$).
-- source:
--   Basov, Erkal, Minehart, Scotchmer, Scarcity of Ideas and Optimal R&D Policy, SSRN 4628270, §2, pp.9–10

import Mathlib

namespace ScarceIdeas

/-- **Cumulative cost distribution `F`.**
Basov, Erkal, Minehart, Scotchmer, *Scarcity of Ideas and Optimal R&D Policy*, SSRN 4628270,
§2, p.9 ("cumulative distribution F") and p.10 ("Conditional on an idea arriving, the probability
that the idea is viable is F(p(t)), where F is the cumulative distribution of the cost density f").

$$F(x)=\int_{\underline c}^{x} f(c)\,dc .$$

**Formalization Note** An interval integral from `cL` (the page's `c̲`). For a density `f` that
vanishes off `[cL, cH]` (`CostDensity`), this is the cumulative distribution function on all of
`ℝ`: `F x = 0` for `x ≤ cL` and `F x = 1` for `x ≥ cH`. -/
noncomputable def costCDF (cL : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ c in cL..x, f c

end ScarceIdeas


