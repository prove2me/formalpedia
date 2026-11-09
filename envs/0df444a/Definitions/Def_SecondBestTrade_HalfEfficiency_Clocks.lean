-- Prove2me | Definitions.Def_SecondBestTrade_HalfEfficiency_Clocks
-- name    : SecondBestTrade_HalfEfficiency_Clocks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:18.627826+00:00
-- url     : https://prove2.me/theorems/b5df68d4-5ac3-474b-8fec-215883712b84
-- title:
--   §6 — Antithetic clocks and beta integral
-- statement:
--   Let $u$ be uniform on the open interval $(0,1)$. The coupled clocks and beta integral are
--   $$\theta_B(u)=-\log u,\quad \theta_S(u)=-\log(1-u),\quad \mathrm B(\tau)=\int_{(0,1)}u^{-\kappa}(1-u)^{-\kappa}\,du,\qquad\kappa=\frac{\tau}{1+\tau}.$$
--   `clockLaw` is the pushforward of restricted Lebesgue measure under this pair of clocks. The open interval has length one. Both component functions are measurable there; the endpoint values of Lean's total logarithm are outside the integration domain.
--
--   These definitions retain the dependence between the buyer and seller clocks. Lemma 6.1 states convergence and the strict upper bound; no integral value or distributional bound is assumed in this layer.
-- source:
--   Dirk Bergemann, Yang Cai, Kangning Wang, Jinzhao Wu, Renzhe Xu, STOC 2027 submission #529 (October 2026), §6, (6.5) and Lemma 6.1, printed p. 12 (PDF p. 13)

import Mathlib
import Definitions.Def_SecondBestTrade_HalfEfficiency_Dual

open scoped BigOperators NNReal
open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace SecondBestTrade.HalfEfficiency

/-- Antithetic clocks from (6.5). Values at the endpoints are immaterial under the open-interval law. -/
def buyerClock (u : ℝ) : ℝ := -Real.log u
def sellerClock (u : ℝ) : ℝ := -Real.log (1 - u)
def uniformClockSeed : Measure ℝ := volume.restrict (Set.Ioo 0 1)
noncomputable def clockLaw : Measure (ℝ × ℝ) :=
  Measure.map (fun u => (buyerClock u, sellerClock u)) uniformClockSeed

def betaIntegrand (tau u : ℝ) : ℝ := u ^ (-kappa tau) * (1 - u) ^ (-kappa tau)
noncomputable def betaValue (tau : ℝ) : ℝ :=
  ∫ u in Set.Ioo (0 : ℝ) 1, betaIntegrand tau u

end SecondBestTrade.HalfEfficiency


