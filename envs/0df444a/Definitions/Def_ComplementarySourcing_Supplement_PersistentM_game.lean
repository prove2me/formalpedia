-- Prove2me | Definitions.Def_ComplementarySourcing_Supplement_PersistentM_game
-- name    : ComplementarySourcing_Supplement_PersistentM_game
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:45:24.452376+00:00
-- url     : https://prove2.me/theorems/45d5c8d6-ceca-4a7d-abd9-5ee071fb2a12
-- title:
--   Model (M) under persistent market risk
-- statement:
--   Persistent market risk (§4.2): the second mover does not observe the realized market taste before investing. With a fixed wholesale price $w$ and market taste $\epsilon_i$ of probability $p_i$, the manufacturer chooses $x_m\ge0$; the supplier chooses $x_s\ge0$ to maximize its expected profit
--
--   $$\pi_s(x_s\mid x_m)=\sum_i p_i\,w\,d(x_m,x_s,\epsilon_i)-\tfrac12x_s^2 ,$$
--
--   and the manufacturer earns $\pi_m(x_m)=\sum_i p_i\,(r-w)\,d(x_m,x_s^*(x_m),\epsilon_i)-\tfrac12x_m^2$. On p.20 the law is $\{\epsilon_1,0\}$, where $\sum_ip_i\,w\,d(\cdot,\epsilon_i)=p_1w\mu\min\{u,\epsilon_1\}$.
--
--   It is the model of Theorem 4.
--
--   **Formalization Note** The follower sees no state, so the game has a single state and the follower's payoff is already an expectation.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), §4.2, p.20

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame
import Definitions.Def_ComplementarySourcing_demand

namespace ComplementarySourcing

/-- Model (M) under persistent market risk with a fixed wholesale price `w` (§4.2): neither firm
observes the realized risk before investing. The manufacturer leads with `x_m ≥ 0`; the supplier
picks `x_s ≥ 0` maximizing its expected profit `π_s(x_s | x_m) = Σ_i p_i w d(x_m, x_s, ϵ_i) − ½ x_s²`;
the manufacturer earns `π_m(x_m) = Σ_i p_i (r − w) d(x_m, x_s, ϵ_i) − ½ x_m²`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), §4.2, p.20 (PDF 20).

**Formalization Note.** The follower sees no state, so the state space is `Unit` and the
follower's payoff is already an expectation. On p.20 the law is `{ϵ₁, 0}`, where
`p₁ w µ min{u, ϵ₁}` is this sum. -/
noncomputable def Supplement.PersistentM.game {m : ℕ} (μ α r w : ℝ) (ε p : Fin m → ℝ) :
    StackelbergGame ℝ ℝ Unit where
  leaderFeasible := Set.Ici 0
  followerFeasible := Set.Ici 0
  states := Set.univ
  followerPayoff xm _ xs := ∑ i, p i * (w * demand μ α xm xs (ε i)) - 1 / 2 * xs ^ 2
  leaderPayoff xm f := ∑ i, p i * ((r - w) * demand μ α xm (f ()) (ε i)) - 1 / 2 * xm ^ 2

end ComplementarySourcing


