-- Prove2me | Definitions.Def_ComplementarySourcing_Supplement_FixedPriceM_game
-- name    : ComplementarySourcing_Supplement_FixedPriceM_game
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:44:34.439149+00:00
-- url     : https://prove2.me/theorems/ad4641b5-6c1e-44ad-8919-ee9b755afec8
-- title:
--   Model (M) with a fixed wholesale price
-- statement:
--   The wholesale price $w\in[0,r]$ is fixed (§4.1). The manufacturer chooses only its effort $x_m\ge0$; the supplier observes $x_m$ and the realized market taste $\epsilon_i$ (probability $p_i$) and chooses $x_s\ge0$ to maximize $w\,d(x_m,x_s,\epsilon_i)-\tfrac12x_s^2$; the manufacturer earns
--
--   $$\pi_m(x_m)=(r-w)\sum_i p_i\,d\big(x_m,x_s^*(\epsilon_i),\epsilon_i\big)-\tfrac12x_m^2 .$$
--
--   Theorem 3 uses the law $\epsilon\in\{\epsilon_1,0\}$ with probabilities $p_1,1-p_1$; Theorem A3 the constant law $\epsilon\equiv\epsilon_0$.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), §4.1, p.18; §A4, p.A20; §A5, p.A22

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame
import Definitions.Def_ComplementarySourcing_supplierStageProfit

namespace ComplementarySourcing

/-- Model (M) with a fixed (exogenous) wholesale price `w` (§4.1, §A4, §A5): the manufacturer
leads with an effort `x_m ≥ 0` only; the supplier observes the realized `ϵ_i` (probability
`p_i`) and picks `x_s ≥ 0` maximizing `w d(x_m, x_s, ϵ_i) − ½ x_s²`; the manufacturer earns
`(r − w) Σ_i p_i d(x_m, x_s(ϵ_i), ϵ_i) − ½ x_m²`. Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), §4.1, p.18, and §A5, p.A22 (PDF 18, 50);
the constant-risk case §A4, p.A20 (PDF 48).

**Formalization Note.** The law `(ϵ, p)` is a parameter: Theorem 3 uses `{ϵ₁, 0}` with
probabilities `p₁, 1 − p₁`, Theorem A3 the one-point law `ϵ ≡ ϵ₀`. -/
noncomputable def Supplement.FixedPriceM.game {m : ℕ} (μ α r w : ℝ) (ε p : Fin m → ℝ) :
    StackelbergGame ℝ ℝ (Fin m) where
  leaderFeasible := Set.Ici 0
  followerFeasible := Set.Ici 0
  states := Set.univ
  followerPayoff xm i := supplierStageProfit μ α xm w (ε i)
  leaderPayoff xm f := (r - w) * ∑ i, p i * demand μ α xm (f i) (ε i) - 1 / 2 * xm ^ 2

end ComplementarySourcing


