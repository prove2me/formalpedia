-- Prove2me | Definitions.Def_ComplementarySourcing_Supplement_NoRiskM_game
-- name    : ComplementarySourcing_Supplement_NoRiskM_game
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:41:26.822454+00:00
-- url     : https://prove2.me/theorems/e942e524-c6eb-5005-bbe4-f2daa4026fd5
-- title:
--   Model (M) without market risk
-- statement:
--   The manufacturer-first game without market risk (§3.1). The manufacturer chooses an effort $x_m\ge0$ and a wholesale price $w\in[0,r]$. The supplier observes them and chooses its effort $x_s\ge0$ to maximize
--
--   $$\pi_s(x_s\mid x_m,w)=w\,\mu\,u(x_m,x_s)-\tfrac12x_s^2 ,$$
--
--   problem (2) with $\epsilon=\infty$. The manufacturer earns $\pi_m=(r-w)\,\mu\,u(x_m,x_s)-\tfrac12x_m^2$, problem (1) and eq. (3). Here $r$ is the unit profit and $u(x_m,x_s)=x_m+x_s+\alpha x_mx_s$.
--
--   The leader's and the follower's payoffs of this Stackelberg game are the two firms' profits in Model (M) of Theorem 1.
--
--   **Formalization Note** There is no risk to observe, so the game has a single state.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), eqs. (1)–(3), pp.8–10

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame
import Definitions.Def_ComplementarySourcing_Supplement_uncappedDemand

namespace ComplementarySourcing

/-- Model (M) without market risk (§3.1): the manufacturer leads with `(x_m, w)`, `x_m ≥ 0`,
`0 ≤ w ≤ r`; the supplier then picks `x_s ≥ 0` to maximize `w µ u(x_m, x_s) − ½ x_s²` (problem (2)
with `ϵ = ∞`); the manufacturer earns `(r − w) µ u(x_m, x_s) − ½ x_m²` (problem (1), eq. (3)).
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), eqs. (1)–(3), pp.8–10 (PDF 8–10).

**Formalization Note.** There is no risk to observe, so the state space is `Unit`. Leader and
follower payoffs are the two firms' profits in this model. -/
noncomputable def Supplement.NoRiskM.game (μ α r : ℝ) : StackelbergGame (ℝ × ℝ) ℝ Unit where
  leaderFeasible := {a | 0 ≤ a.1 ∧ 0 ≤ a.2 ∧ a.2 ≤ r}
  followerFeasible := Set.Ici 0
  states := Set.univ
  followerPayoff a _ xs := a.2 * Supplement.uncappedDemand μ α a.1 xs - 1 / 2 * xs ^ 2
  leaderPayoff a f := (r - a.2) * Supplement.uncappedDemand μ α a.1 (f ()) - 1 / 2 * a.1 ^ 2

end ComplementarySourcing


