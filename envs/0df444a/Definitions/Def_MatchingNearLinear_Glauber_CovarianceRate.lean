-- Prove2me | Definitions.Def_MatchingNearLinear_Glauber_CovarianceRate
-- name    : MatchingNearLinear_Glauber_CovarianceRate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T15:56:30.630625+00:00
-- url     : https://prove2.me/theorems/c5f1b6ff-c296-42a8-9631-6f38b69c8292
-- title:
--   The matching covariance envelope and integrated stability factor
-- statement:
--   The matching covariance envelope is the scalar function
--
--   $$\widehat C(0)=1,\qquad \widehat C(s)=\begin{cases}\min\{7+48s,(1-s)^{-1}\},&0<s<1,\\7+48s,&s\ge1.\end{cases}$$
--
--   Define $I_x=\int_0^x(\widehat C(s)-1)/s\,ds$ and $c_x=e^{-I_x}$. The integral is represented first in extended nonnegative reals; the actual displayed envelope has a finite integral for every positive finite $x$. The marginal logarithm in Corollary 4.3 is $L=\log(1+m(1+a)(1+a\Delta)^2/\lambda_{\min})$. These graph-independent rate definitions preserve both activity regimes and the sharp placement of the mixing accuracy term.
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Proposition 4.1 and Eq. (20), printed p.19 (PDF p.21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_MatchingModel

set_option autoImplicit false

namespace MatchingNearLinear.Glauber


noncomputable section
open Classical
/-- The two regimes of Proposition 4.1, with the continuous value at zero. -/
def matchingRate (s : ℝ) : ℝ :=
  if s = 0 then 1 else if s < 1 then min (7+48*s) (1/(1-s)) else 7+48*s

def matchingIntegral (x : ℝ) : ENNReal :=
  ∫⁻ s in Set.Ioc (0:ℝ) x, ENNReal.ofReal ((matchingRate s - 1)/s)

def matchingC (x : ℝ) : ℝ := Real.exp (-(matchingIntegral x).toReal)

def matchingLogFactor {n m : ℕ} (G : Input n m) (lam : Fin m → ℝ) (a : ℝ) : ℝ :=
  Real.log (1 + (m:ℝ)*(1+a)*(1+a*maxDegree G)^2 / minActivity lam)

end
end MatchingNearLinear.Glauber


