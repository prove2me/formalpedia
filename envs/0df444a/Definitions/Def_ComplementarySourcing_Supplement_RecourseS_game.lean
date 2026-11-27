-- Prove2me | Definitions.Def_ComplementarySourcing_Supplement_RecourseS_game
-- name    : ComplementarySourcing_Supplement_RecourseS_game
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:46:55.70292+00:00
-- url     : https://prove2.me/theorems/5223dc8e-0d12-4581-8d4e-58933c3f4b87
-- title:
--   Model (S) with endogenous selling price
-- statement:
--   Both firms invest before the market taste is realized, the supplier first; the manufacturer then chooses $x_m\ge0$ to maximize $\sum_i p_i\,(1-\eta)\,r^*_i\,(d_i-b\,r^*_i)-\tfrac12x_m^2$, and the supplier earns $\sum_i p_i\,\eta\,r^*_i\,(d_i-b\,r^*_i)-\tfrac12x_s^2$, with $d_i=d(x_m,x_s,\epsilon_i)$ and $r^*_i=d_i/(2b)$ set by the manufacturer after the realization.
--
--   It is the supplier-first model against which Theorem 5 compares.
--
--   **Formalization Note** The page defines the manufacturer-first order explicitly; the first-mover comparison needs this mirror order, in which the manufacturer still sets the selling price.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), §4.3, p.23

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame
import Definitions.Def_ComplementarySourcing_demand
import Definitions.Def_ComplementarySourcing_Supplement_recourseRevenue

namespace ComplementarySourcing

/-- Model (S) with endogenous selling price (§4.3): both firms invest before the risk resolves,
the supplier first; the manufacturer then picks `x_m ≥ 0` maximizing
`Σ_i p_i (1 − η) r*_i (d_i − b r*_i) − ½ x_m²`, and the supplier earns
`Σ_i p_i η r*_i (d_i − b r*_i) − ½ x_s²`, with `d_i = d(x_m, x_s, ϵ_i)`, `r*_i = d_i/(2b)` set by the
manufacturer after the risk resolves. Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), §4.3, p.23 (PDF 23).

**Formalization Note.** The page defines only the manufacturer-first order explicitly; the
first-mover comparison of Theorem 5 needs this mirror order, in which the manufacturer still sets
the selling price. -/
noncomputable def Supplement.RecourseS.game {m : ℕ} (μ α b η : ℝ) (ε p : Fin m → ℝ) :
    StackelbergGame ℝ ℝ Unit where
  leaderFeasible := Set.Ici 0
  followerFeasible := Set.Ici 0
  states := Set.univ
  followerPayoff xs _ xm :=
    ∑ i, p i * Supplement.recourseRevenue b (1 - η) (demand μ α xm xs (ε i)) - 1 / 2 * xm ^ 2
  leaderPayoff xs f :=
    ∑ i, p i * Supplement.recourseRevenue b η (demand μ α (f ()) xs (ε i)) - 1 / 2 * xs ^ 2

end ComplementarySourcing


