-- Prove2me | Definitions.Def_ComplementarySourcing_Supplement_DiscreteM_game
-- name    : ComplementarySourcing_Supplement_DiscreteM_game
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:42:15.785351+00:00
-- url     : https://prove2.me/theorems/bb47bf95-5985-5f31-bf69-7dc7c36976ee
-- title:
--   Model (M) under general discrete market risk
-- statement:
--   Let the market taste be $\epsilon=\epsilon_i$ with probability $p_i$, $i=1,\dots,n$. In Model (M) the manufacturer chooses $x_m\ge0$ and $w\in[0,r]$ before $\epsilon$ is known. The supplier observes $(x_m,w)$ and the realized $\epsilon_i$ and chooses $x_s\ge0$ to maximize $w\,d(x_m,x_s,\epsilon_i)-\tfrac12x_s^2$, where $d(x_m,x_s,\epsilon)=\mu\min\{x_m+x_s+\alpha x_mx_s,\epsilon\}$. The manufacturer earns
--
--   $$\pi_m(x_m,w)=(r-w)\sum_{i=1}^n p_i\,d\big(x_m,x_s^*(\epsilon_i),\epsilon_i\big)-\tfrac12x_m^2 .$$
--
--   This is the model of Theorem A1.
--
--   **Formalization Note** The state is the index $i$ of the realization; the law $(\epsilon_i,p_i)$ is a parameter and Theorem A1 states its conditions.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), §A1.1, p.A1

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame
import Definitions.Def_ComplementarySourcing_supplierStageProfit

namespace ComplementarySourcing

/-- Model (M) under general discrete market risk (§A1.1): `ϵ = ϵ_i` with probability `p_i`,
`i = 1, …, n`. The manufacturer leads with `(x_m, w)`, `x_m ≥ 0`, `0 ≤ w ≤ r`; the supplier
observes the realized `ϵ_i` and picks `x_s ≥ 0` maximizing `w d(x_m, x_s, ϵ_i) − ½ x_s²`; the
manufacturer earns `π_m(x_m, w) = (r − w) Σ_i p_i d(x_m, x_s(ϵ_i), ϵ_i) − ½ x_m²`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), §A1.1, p.A1 (PDF 29).

**Formalization Note.** The state is the index `i : Fin m` of the realization, so the follower
responds to the realized `ϵ_i`. The law `(ϵ, p)` is a parameter; the theorems state its
conditions. -/
noncomputable def Supplement.DiscreteM.game {m : ℕ} (μ α r : ℝ) (ε p : Fin m → ℝ) :
    StackelbergGame (ℝ × ℝ) ℝ (Fin m) where
  leaderFeasible := {a | 0 ≤ a.1 ∧ 0 ≤ a.2 ∧ a.2 ≤ r}
  followerFeasible := Set.Ici 0
  states := Set.univ
  followerPayoff a i := supplierStageProfit μ α a.1 a.2 (ε i)
  leaderPayoff a f := (r - a.2) * ∑ i, p i * demand μ α a.1 (f i) (ε i) - 1 / 2 * a.1 ^ 2

end ComplementarySourcing


