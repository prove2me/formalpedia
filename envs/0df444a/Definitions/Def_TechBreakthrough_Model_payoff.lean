-- Prove2me | Definitions.Def_TechBreakthrough_Model_payoff
-- name    : TechBreakthrough_Model_payoff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:33:29.397016+00:00
-- url     : https://prove2.me/theorems/2a54646e-0c75-450d-acff-3ce52533490a
-- title:
--   The reward of problem (19)
-- statement:
--   For a starting level $m$, a time $\tau$ and a path $\omega$, the reward inside (19) is
--
--   $$[1-F(M_\tau)]\,e^{-r\tau}R(X_\tau)+\int_0^\tau e^{-rt}G(M_t)f(M_t)\,dM_t.$$
--
--   The first term is the payoff of investing at $\tau$ when no breakthrough has occurred; the integral collects the discounted value of the breakthroughs over the increments of $M$.
--
--   **Formalization Note** On $\{\tau=\infty\}$ the first term is $0$ (Footnote 2), while the integral runs over $(0,\infty)$ and does not vanish: never stopping is admissible and collects the whole integral.
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, (19), p.13; Footnote 2, p.9

import Definitions.Def_TechBreakthrough_Model
import Definitions.Def_TechBreakthrough_runningMax
import Definitions.Def_TechBreakthrough_discountedAt

open MeasureTheory
open scoped NNReal

namespace TechBreakthrough

namespace Model

variable (M : Model)

/-- The integrand `e^{−rt} G(M_t) f(M_t)` of (19), arXiv:2106.05112v1, p.13. -/
noncomputable def flow (m : ℝ) (ω : M.Ω) (t : ℝ) : ℝ :=
  Real.exp (-M.r * t) * M.G (runningMax m t.toNNReal ω) * M.f (runningMax m t.toNNReal ω)

/-- The time set `(0, τ]`, which is `(0, ∞)` when `τ = ∞`. -/
def elapsed (τ : WithTop ℝ≥0) : Set ℝ := {t | 0 < t ∧ ((t.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ}

/-- The pathwise reward inside (19), arXiv:2106.05112v1, p.13:
`[1 − F(M_τ)] e^{−rτ} R(X_τ) + ∫_0^τ e^{−rt} G(M_t) f(M_t) dM_t`.

**Formalization Note** The first term is `0` on `{τ = ∞}` (Footnote 2, p.9); the integral is
then over `(0, ∞)` and does not vanish. -/
noncomputable def payoff (m : ℝ) (τ : M.Ω → WithTop ℝ≥0) (ω : M.Ω) : ℝ :=
  discountedAt M.r (fun t => (1 - M.F (runningMax m t ω)) * M.R (M.X t ω)) (τ ω) +
    ∫ t in elapsed (τ ω), M.flow m ω t ∂(dMax m ω)

end Model

end TechBreakthrough


