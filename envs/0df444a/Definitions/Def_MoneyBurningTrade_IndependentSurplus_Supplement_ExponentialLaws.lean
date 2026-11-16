-- Prove2me | Definitions.Def_MoneyBurningTrade_IndependentSurplus_Supplement_ExponentialLaws
-- name    : MoneyBurningTrade_IndependentSurplus_Supplement_ExponentialLaws
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:37:06.641928+00:00
-- url     : https://prove2.me/theorems/6e2e633b-8647-475a-971b-a5fbb32eb5ef
-- title:
--   Equations (23) and (25) — truncated exponential laws and the trade mass A(r)
-- statement:
--   For $t\ge4$ let $\lambda=1/(1-e^{-t})$. The buyer's law $F_b^t$ and the seller's law $F_s^t$ are supported on $[0,t]$ with densities
--
--   $$f_b^t(z)=\lambda e^{-z},\qquad f_s^t(z)=\lambda e^{z-t}\qquad(z\in[0,t]),$$
--
--   so that $F_b^t(z)=\lambda(1-e^{-z})$ and $F_s^t(z)=\lambda(e^{z-t}-e^{-t})$; this is the family of Blumrosen and Dobzinski. For a mechanism $M$ with allocation $x$ and $r\in[0,t]$, equation (25) defines
--
--   $$A(r)=\int_0^{t-r}x(v_s,v_s+r)\,dv_s,$$
--
--   the integral of the trade probability over the profiles whose gain from trade is $r$.
--
--   **Formalization Note** Each law is Lebesgue measure on $[0,t]$ with the stated density (`withDensity`); that it is a probability measure is left to theorems. $A(r)$ is an oriented interval integral.
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), §5.1, equations (23) and (25), printed p. 32 (PDF p. 33); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_SecondBestBT_Mechanism

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus.Supplement

/-- `λ = 1/(1 − e^(−t))`, equation (23), §5.1 p.32. -/
noncomputable def bdLambda (t : ℝ) : ℝ := 1 / (1 - Real.exp (-t))

/-- The buyer's law `F_b^t` of (23): density `λ e^(−z)` on `[0, t]`, zero elsewhere.
Probability normalization is left to theorems. -/
noncomputable def bdBuyerLaw (t : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Icc 0 t)).withDensity
    (fun z => ENNReal.ofReal (bdLambda t * Real.exp (-z)))

/-- The seller's law `F_s^t` of (23): density `λ e^(z−t)` on `[0, t]`, zero elsewhere.
Probability normalization is left to theorems. -/
noncomputable def bdSellerLaw (t : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Icc 0 t)).withDensity
    (fun z => ENNReal.ofReal (bdLambda t * Real.exp (z - t)))

/-- `A(r) = ∫_0^(t−r) x(v, v + r) dv`, equation (25), §5.1 p.32: the integral of the
trade probability over the profiles with gain from trade `r` (used for `r ∈ [0, t]`). -/
noncomputable def tradeMass (M : SecondBestBT.Mechanism) (t r : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..(t - r), M.x (v, v + r)

end MoneyBurningTrade.IndependentSurplus.Supplement


