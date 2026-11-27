-- Prove2me | Definitions.Def_ComplementarySourcing_Supplement_PersistentS_game
-- name    : ComplementarySourcing_Supplement_PersistentS_game
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:45:53.799516+00:00
-- url     : https://prove2.me/theorems/06eb55c3-3c69-4ba8-8e4a-792481b63b5a
-- title:
--   Model (S) under persistent market risk
-- statement:
--   Under persistent market risk with a fixed wholesale price $w$, the supplier chooses $x_s\ge0$ first; the manufacturer, not observing the risk, chooses $x_m\ge0$ to maximize $\sum_i p_i\,(r-w)\,d(x_m,x_s,\epsilon_i)-\tfrac12x_m^2$; the supplier earns $\sum_i p_i\,w\,d(x_m^*(x_s),x_s,\epsilon_i)-\tfrac12x_s^2$.
--
--   It is the supplier-first model of Theorem 4.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), §4.2, p.20

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame
import Definitions.Def_ComplementarySourcing_demand

namespace ComplementarySourcing

/-- Model (S) under persistent market risk with a fixed wholesale price `w` (§4.2): the supplier
leads with `x_s ≥ 0`; the manufacturer, not observing the risk, picks `x_m ≥ 0` maximizing
`Σ_i p_i (r − w) d(x_m, x_s, ϵ_i) − ½ x_m²`; the supplier earns `Σ_i p_i w d(x_m, x_s, ϵ_i) − ½ x_s²`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), §4.2, p.20 (PDF 20) ("the other case can be similarly formulated", p.8).

**Formalization Note.** State space `Unit`; the follower's payoff is an expectation. -/
noncomputable def Supplement.PersistentS.game {m : ℕ} (μ α r w : ℝ) (ε p : Fin m → ℝ) :
    StackelbergGame ℝ ℝ Unit where
  leaderFeasible := Set.Ici 0
  followerFeasible := Set.Ici 0
  states := Set.univ
  followerPayoff xs _ xm := ∑ i, p i * ((r - w) * demand μ α xm xs (ε i)) - 1 / 2 * xm ^ 2
  leaderPayoff xs f := ∑ i, p i * (w * demand μ α (f ()) xs (ε i)) - 1 / 2 * xs ^ 2

end ComplementarySourcing


