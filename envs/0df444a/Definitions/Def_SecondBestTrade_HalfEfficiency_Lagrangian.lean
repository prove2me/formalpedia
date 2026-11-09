-- Prove2me | Definitions.Def_SecondBestTrade_HalfEfficiency_Lagrangian
-- name    : SecondBestTrade_HalfEfficiency_Lagrangian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:11.450795+00:00
-- url     : https://prove2.me/theorems/9ccf4353-7dee-4fdf-87d5-277cef74d477
-- title:
--   Appendix A.2 — Partial Lagrangian and coefficients
-- statement:
--   For a signed mechanism $m=(x,t)$ and nonnegative multipliers $z=(\tau,\alpha)$, the partial Lagrangian is
--   $$L(m;z)=\mathrm{GFT}(x)+\tau\mathbb E_\pi\sum_a t_a+\sum_{a,s,r}\alpha_a(s,r)\bigl(U_a(s;s)-U_a(s;r)\bigr),$$
--   where $r$ ranges over support reports and the null report. Its supremum $L^*(z)$ ranges over all pointwise feasible allocation rules and unrestricted signed transfers. It takes values in the extended reals, so unbounded transfer directions give $+\infty$.
--
--   The signed-payment coefficient is $\pi(v)/f_a(v_a)\,[\tau f_a(v_a)-\operatorname{out}_a(v_a)+\operatorname{in}_a(v_a)]$. The seller-receipt coefficient has the opposite sign. The allocation coefficients $\Xi$ are computed from (A.6), including the opposite buyer and seller signs, and `XiObjective` is the prior expectation of their maximum feasible sum.
--
--   This supplies the actual optimization domain and coefficient formulas used in Lemmas A.7–A.9. No equality between the primal value, the Lagrangian supremum or virtual surplus is imposed by these definitions.
-- source:
--   Dirk Bergemann, Yang Cai, Kangning Wang, Jinzhao Wu, Renzhe Xu, STOC 2027 submission #529 (October 2026), Appendix A.2, (A.5)–(A.6) and the definitions of Ξ, printed pp. 22–24 (PDF pp. 23–25)

import Mathlib
import Definitions.Def_SecondBestTrade_HalfEfficiency_Dual

open scoped BigOperators NNReal
open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace SecondBestTrade.HalfEfficiency

def lagrangian (N : Market) (z : Dual N) (m : SignedMechanism N) : ℝ :=
  GFT N m.q + (z.tau : ℝ) * expect N (fun v => ∑ a, m.t a v) +
    ∑ a, ∑ t, ∑ r : Option (Ty N a),
      (z.flow a t r : ℝ) * (U N m a t t - reportUtility N m a t r)

/-- Extended-real supremum: non-useful multipliers can have value +infinity. -/
noncomputable def lagrangianSup (N : Market) (z : Dual N) : EReal :=
  sSup {w | ∃ m : SignedMechanism N, feasible N m.q ∧ w = (lagrangian N z m : EReal)}

/-- Coefficient of the signed payment BY an agent. Seller receipt has the opposite coefficient. -/
def paymentCoeff (N : Market) (z : Dual N) (a : Agent N) (v : Profile N) : ℝ :=
  (prior N v / N.mass a (v a)) *
    ((z.tau : ℝ) * N.mass a (v a) - outflow N z a (v a) + inflow N z a (v a))

def coefficientsVanish (N : Market) (z : Dual N) : Prop := ∀ a v, paymentCoeff N z a v = 0

def XiAgent (N : Market) (z : Dual N) (a : Agent N) (t : Ty N a) (e : Trade N) : ℝ :=
  Sum.elim (fun _ => 1) (fun _ => -1) a *
    ((coord N a t e * outflow N z a t -
      ∑ s, (z.flow a s (some t) : ℝ) * coord N a s e) / N.mass a t)
def Xi (N : Market) (z : Dual N) (v : Profile N) (e : Trade N) : ℝ :=
  gains N v e + XiAgent N z (.inl (N.buyer e)) (v (.inl (N.buyer e))) e +
    XiAgent N z (.inr (N.seller e)) (v (.inr (N.seller e))) e

def XiObjective (N : Market) (z : Dual N) : ℝ :=
  expect N (fun v => maxSurplus N (Xi N z v))

end SecondBestTrade.HalfEfficiency


