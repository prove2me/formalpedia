-- Prove2me | Definitions.Def_ComplementarySourcing_Supplement_DiscreteS_game
-- name    : ComplementarySourcing_Supplement_DiscreteS_game
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:42:49.523819+00:00
-- url     : https://prove2.me/theorems/2cb31613-9364-41c9-a0f3-3edb8a8ca1c3
-- title:
--   Model (S) under general discrete market risk
-- statement:
--   Under the same law $\epsilon=\epsilon_i$ with probability $p_i$, in Model (S) the supplier chooses $x_s\ge0$ and $w\in[0,r]$ first. The manufacturer observes them and the realized $\epsilon_i$ and chooses $x_m\ge0$ to maximize $(r-w)\,d(x_m,x_s,\epsilon_i)-\tfrac12x_m^2$. The supplier earns
--
--   $$\pi_s(x_s,w)=w\sum_{i=1}^n p_i\,d\big(x_m^*(\epsilon_i),x_s,\epsilon_i\big)-\tfrac12x_s^2 .$$
--
--   This is the supplier-first model of Theorem A1.
--
--   **Formalization Note** Defined directly rather than by the relabeling $w'=r-w$.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), §A1.2, p.A5

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame
import Definitions.Def_ComplementarySourcing_manufacturerStageProfit

namespace ComplementarySourcing

/-- Model (S) under general discrete market risk (§A1.2): the supplier leads with `(x_s, w)`,
`x_s ≥ 0`, `0 ≤ w ≤ r`; the manufacturer observes the realized `ϵ_i` and picks `x_m ≥ 0`
maximizing `(r − w) d(x_m, x_s, ϵ_i) − ½ x_m²`; the supplier earns
`w Σ_i p_i d(x_m(ϵ_i), x_s, ϵ_i) − ½ x_s²`. Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), §A1.2, p.A5 (PDF 33).

**Formalization Note.** Defined on its own, not by the relabeling `w' = r − w`; the state is the
index of the realization. -/
noncomputable def Supplement.DiscreteS.game {m : ℕ} (μ α r : ℝ) (ε p : Fin m → ℝ) :
    StackelbergGame (ℝ × ℝ) ℝ (Fin m) where
  leaderFeasible := {a | 0 ≤ a.1 ∧ 0 ≤ a.2 ∧ a.2 ≤ r}
  followerFeasible := Set.Ici 0
  states := Set.univ
  followerPayoff a i := manufacturerStageProfit μ α r a.1 a.2 (ε i)
  leaderPayoff a f := a.2 * ∑ i, p i * demand μ α (f i) a.1 (ε i) - 1 / 2 * a.1 ^ 2

end ComplementarySourcing


