-- Prove2me | Definitions.Def_ComplementarySourcing_Supplement_NoRiskS_game
-- name    : ComplementarySourcing_Supplement_NoRiskS_game
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:41:49.318796+00:00
-- url     : https://prove2.me/theorems/4371fda8-008c-59a1-81db-f0814dd104c5
-- title:
--   Model (S) without market risk
-- statement:
--   The supplier-first game without market risk (§3.1, Model (S)). The supplier chooses an effort $x_s\ge0$ and a wholesale price $w\in[0,r]$. The manufacturer observes them and chooses $x_m\ge0$ to maximize
--
--   $$\pi_m(x_m\mid x_s,w)=(r-w)\,\mu\,u(x_m,x_s)-\tfrac12x_m^2 ,$$
--
--   and the supplier earns $\pi_s=w\,\mu\,u(x_m,x_s)-\tfrac12x_s^2$, with $u(x_m,x_s)=x_m+x_s+\alpha x_mx_s$.
--
--   Together with Model (M) it gives the first-mover comparison of Theorem 1.
--
--   **Formalization Note** Defined directly rather than through the page's relabeling $w'=r-w$; a single state.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), Model (S), p.11

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame
import Definitions.Def_ComplementarySourcing_Supplement_uncappedDemand

namespace ComplementarySourcing

/-- Model (S) without market risk (§3.1): the supplier leads with `(x_s, w)`, `x_s ≥ 0`,
`0 ≤ w ≤ r`; the manufacturer then picks `x_m ≥ 0` to maximize `(r − w) µ u(x_m, x_s) − ½ x_m²`;
the supplier earns `w µ u(x_m, x_s) − ½ x_s²`. Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), Model (S), p.11 (PDF 11).

**Formalization Note.** Defined on its own, not by relabeling Model (M); the state space is
`Unit`. Leader and follower payoffs are the supplier's and the manufacturer's profits. -/
noncomputable def Supplement.NoRiskS.game (μ α r : ℝ) : StackelbergGame (ℝ × ℝ) ℝ Unit where
  leaderFeasible := {a | 0 ≤ a.1 ∧ 0 ≤ a.2 ∧ a.2 ≤ r}
  followerFeasible := Set.Ici 0
  states := Set.univ
  followerPayoff a _ xm := (r - a.2) * Supplement.uncappedDemand μ α xm a.1 - 1 / 2 * xm ^ 2
  leaderPayoff a f := a.2 * Supplement.uncappedDemand μ α (f ()) a.1 - 1 / 2 * a.1 ^ 2

end ComplementarySourcing


