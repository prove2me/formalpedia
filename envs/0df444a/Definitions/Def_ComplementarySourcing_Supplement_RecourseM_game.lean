-- Prove2me | Definitions.Def_ComplementarySourcing_Supplement_RecourseM_game
-- name    : ComplementarySourcing_Supplement_RecourseM_game
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:46:27.365833+00:00
-- url     : https://prove2.me/theorems/8874747f-98c8-48a6-81ec-48091e438791
-- title:
--   Model (M) with endogenous selling price
-- statement:
--   Both firms invest before the market taste $\epsilon_i$ (probability $p_i$) is realized, the manufacturer first; after the realization the manufacturer sets the selling price $r^*_i=d_i/(2b)$, where $d_i=d(x_m,x_s,\epsilon_i)$, and pays the supplier the wholesale price $\eta r$. The supplier chooses $x_s\ge0$ to maximize
--
--   $$\sum_i p_i\,\eta\,r^*_i\,(d_i-b\,r^*_i)-\tfrac12x_s^2 ,$$
--
--   and the manufacturer earns $\sum_i p_i\,(1-\eta)\,r^*_i\,(d_i-b\,r^*_i)-\tfrac12x_m^2$. With the law $\{\epsilon_1,0\}$ and probabilities $\tfrac12,\tfrac12$ the supplier's payoff is the page's $\frac{\eta}{8b}d(x_m,x_s,\epsilon_1)^2-\tfrac12x_s^2$.
--
--   It is the manufacturer-first model of Theorem 5.
--
--   **Formalization Note** A single state: no firm observes the risk before investing.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), §4.3, p.23; §A6, p.A23

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame
import Definitions.Def_ComplementarySourcing_demand
import Definitions.Def_ComplementarySourcing_Supplement_recourseRevenue

namespace ComplementarySourcing

/-- Model (M) with endogenous selling price (§4.3, §A6): both firms invest before the risk
resolves, the manufacturer first. The supplier picks `x_s ≥ 0` maximizing
`Σ_i p_i η r*_i (d_i − b r*_i) − ½ x_s²`, the manufacturer earns
`Σ_i p_i (1 − η) r*_i (d_i − b r*_i) − ½ x_m²`, where `d_i = d(x_m, x_s, ϵ_i)` and `r*_i = d_i/(2b)`
is the manufacturer's selling price after observing `ϵ_i`; the wholesale price is `η r`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), §4.3, p.23 (PDF 23), and §A6, p.A23 (PDF 51).

**Formalization Note.** State space `Unit` (no firm observes the risk before investing). The
law `(ϵ, p)` is a parameter; on p.A23 it is `{ϵ₁, 0}` with probabilities `½, ½`, which gives the
page's `π_s = (η/8b) d(x_m, x_s, ϵ₁)² − ½ x_s²`. -/
noncomputable def Supplement.RecourseM.game {m : ℕ} (μ α b η : ℝ) (ε p : Fin m → ℝ) :
    StackelbergGame ℝ ℝ Unit where
  leaderFeasible := Set.Ici 0
  followerFeasible := Set.Ici 0
  states := Set.univ
  followerPayoff xm _ xs :=
    ∑ i, p i * Supplement.recourseRevenue b η (demand μ α xm xs (ε i)) - 1 / 2 * xs ^ 2
  leaderPayoff xm f :=
    ∑ i, p i * Supplement.recourseRevenue b (1 - η) (demand μ α xm (f ()) (ε i)) - 1 / 2 * xm ^ 2

end ComplementarySourcing


