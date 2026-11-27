-- Prove2me | Definitions.Def_ComplementarySourcing_Supplement_FixedPriceS_game
-- name    : ComplementarySourcing_Supplement_FixedPriceS_game
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:44:53.613101+00:00
-- url     : https://prove2.me/theorems/7d53e654-b981-579c-a8b8-a1ce1dcaeaf5
-- title:
--   Model (S) with a fixed wholesale price
-- statement:
--   With the wholesale price $w$ fixed, the supplier chooses only its effort $x_s\ge0$; the manufacturer observes $x_s$ and the realized $\epsilon_i$ and chooses $x_m\ge0$ to maximize $(r-w)\,d(x_m,x_s,\epsilon_i)-\tfrac12x_m^2$; the supplier earns
--
--   $$\pi_s(x_s)=w\sum_i p_i\,d\big(x_m^*(\epsilon_i),x_s,\epsilon_i\big)-\tfrac12x_s^2 .$$
--
--   It is the supplier-first model of Theorems 3 and A3.
--
--   **Formalization Note** Defined directly rather than by the page's change of variables.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), §A5, Model (S), p.A23; §A4, p.A21

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame
import Definitions.Def_ComplementarySourcing_manufacturerStageProfit

namespace ComplementarySourcing

/-- Model (S) with a fixed (exogenous) wholesale price `w` (§4.1, §A4, §A5): the supplier leads
with an effort `x_s ≥ 0` only; the manufacturer observes the realized `ϵ_i` and picks `x_m ≥ 0`
maximizing `(r − w) d(x_m, x_s, ϵ_i) − ½ x_m²`; the supplier earns
`w Σ_i p_i d(x_m(ϵ_i), x_s, ϵ_i) − ½ x_s²`. Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), §A5, Model (S), p.A23 (PDF 51), and §A4,
p.A21 (PDF 49).

**Formalization Note.** Defined on its own, not by the page's change of variables. -/
noncomputable def Supplement.FixedPriceS.game {m : ℕ} (μ α r w : ℝ) (ε p : Fin m → ℝ) :
    StackelbergGame ℝ ℝ (Fin m) where
  leaderFeasible := Set.Ici 0
  followerFeasible := Set.Ici 0
  states := Set.univ
  followerPayoff xs i := manufacturerStageProfit μ α r xs w (ε i)
  leaderPayoff xs f := w * ∑ i, p i * demand μ α (f i) xs (ε i) - 1 / 2 * xs ^ 2

end ComplementarySourcing


