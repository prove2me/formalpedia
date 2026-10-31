-- Prove2me | Definitions.Def_KashUpgrade_Assumption2
-- name    : KashUpgrade_Assumption2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:20:52.409083+00:00
-- url     : https://prove2.me/theorems/2a35c9db-6923-404f-8b71-04ce60592894
-- title:
--   Assumption 2: support $[0,\zeta]$ and monotone hazard rate
-- statement:
--   **Assumption 2.** The support of the density $f$ is the interval $[0,\zeta]$ (or $[0,\zeta)$ if $\zeta=\infty$), and the function
--   $$
--   p\mapsto\frac{1-F(p)}{f(p)}
--   $$
--   is monotonically decreasing on this support.
--
--   This is Myerson's regularity condition of a monotone hazard rate. Every result of the mission assumes it.
--
--   **Formalization Note** Monotonicity is stated on $(0,\zeta)$, where $f>0$. With Lean's convention $x/0=0$, monotonicity on the closed interval would exclude densities such as Beta$(2,2)$, where $f(0)=0$ and the ratio is $+\infty$, although the paper lists them as satisfying the assumption.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), Assumption 2, p.13

import Mathlib
import Definitions.Def_KashUpgrade_typeCdf
import Definitions.Def_KashUpgrade_IsTypeDensity

namespace KashUpgrade

/-- **Assumption 2.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), Assumption 2, p.13: the support of the density `f` is the interval
`[0, ζ]` (or `[0, ζ)` if `ζ = ∞`) and `(1 - F p) / f p` is monotonically decreasing on this support.

**Formalization Note** Monotonicity is stated on the open interval `(0, ζ)`, where `f > 0`. With
Lean's `x / 0 = 0`, monotonicity on the closed interval would exclude densities such as Beta(2, 2),
where `f 0 = 0` and the paper's ratio is `+∞`, which the paper lists as satisfying the assumption. -/
structure Assumption2 (f : ℝ → ℝ) (ζ : ENNReal) : Prop extends IsTypeDensity f ζ where
  /-- `(1 - F) / f` is monotonically decreasing on `(0, ζ)`. -/
  antitoneOn : AntitoneOn (fun p => (1 - typeCdf f p) / f p) (typeInterior ζ)

end KashUpgrade


