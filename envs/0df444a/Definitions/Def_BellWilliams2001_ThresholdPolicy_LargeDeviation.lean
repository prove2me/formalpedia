-- Prove2me | Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation
-- name    : BellWilliams2001_ThresholdPolicy_LargeDeviation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T06:37:17.786603+00:00
-- url     : https://prove2.me/theorems/d35b5123-a575-4ead-9082-baa1df94c94c
-- title:
--   Cumulant generating function $\Lambda$ and its Legendre–Fenchel transform $\Lambda^*$ (177), (182)
-- statement:
--   Let $\zeta$ be a real random variable on a probability space $(\Omega,\mathcal F,\mathbf P)$. Its cumulant generating function is
--   $$\Lambda(l)=\log \mathbf E\big[e^{l\zeta}\big]\in(-\infty,\infty],\qquad l\in\mathbb R,$$
--   as in (177), and the Legendre–Fenchel transform of a function $\Lambda:\mathbb R\to(-\infty,\infty]$ is
--   $$\Lambda^*(x)=\sup_{l\in\mathbb R}\big(lx-\Lambda(l)\big),\qquad x\in\mathbb R,$$
--   as in (182).
--
--   These are the rate functions in the Cramér-type bounds (181) and (184) for renewal processes, which drive the large deviation estimates behind the choice of the threshold $c\log r$.
--
--   **Formalization Note** Both functions take values in the extended reals: the expectation is a lower Lebesgue integral in $[0,\infty]$, so $\Lambda(l)=+\infty$ outside the domain of the moment generating function and $\Lambda^*$ may be $+\infty$.
-- source:
--   Bell and Williams, Dynamic scheduling of a system with two parallel servers in heavy traffic with resource pooling, Ann. Appl. Probab. 11 (2001), p. 644, Appendix A, (177) and (182)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace BellWilliams2001.ThresholdPolicy

/-!
Bell and Williams (2001), Appendix A, (177) and (182) (p. 644): the cumulant generating function
and its Legendre–Fenchel transform, both with values in the extended reals.
-/

/-- `Λ(l) = log E[e^{l ζ}]` (177), with values in `(−∞, ∞]`: the expectation is a lower Lebesgue
integral in `[0,∞]` and `ENNReal.log ⊤ = ⊤`, so `Λ(l) = +∞` off the domain of the moment
generating function instead of a junk value. -/
noncomputable def logMGF {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ζ : Ω → ℝ) (l : ℝ) :
    EReal :=
  ENNReal.log (∫⁻ ω, ENNReal.ofReal (Real.exp (l * ζ ω)) ∂P)

/-- The Legendre–Fenchel transform `Λ*(x) = sup_{l ∈ ℝ} (l x − Λ(l))` (182), computed in `EReal`
(so `Λ*(x) ∈ [0, ∞]` may be `+∞`). -/
noncomputable def legendre (Λ : ℝ → EReal) (x : ℝ) : EReal :=
  ⨆ l : ℝ, ((l * x : ℝ) : EReal) - Λ l

end BellWilliams2001.ThresholdPolicy


