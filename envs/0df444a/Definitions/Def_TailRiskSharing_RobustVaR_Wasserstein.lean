-- Prove2me | Definitions.Def_TailRiskSharing_RobustVaR_Wasserstein
-- name    : TailRiskSharing_RobustVaR_Wasserstein
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T21:01:15.286545+00:00
-- url     : https://prove2.me/theorems/bbe34892-eaf5-4584-b147-bcd9b8b4a05b
-- title:
--   §8.2, p. 28 — the quantile Wasserstein metric W_k and the robust risk measure [ρ]^k_δ of (32)
-- statement:
--   For random variables $X,Y$ with distribution functions $F,G$ and quantile functions $F^{-1}(x)=\inf\{y:F(y)\ge x\}$, $G^{-1}$, the **Wasserstein metric of order $k\ge1$** is
--
--   $$
--   W_k(X,Y)=\Big(\int_0^1\big|F^{-1}(x)-G^{-1}(x)\big|^k\,\mathrm dx\Big)^{1/k}.
--   $$
--
--   For a risk measure $\rho$ and a radius $\delta>0$, the **robust version** of $\rho$ is the worst value of $\rho$ over the Wasserstein ball of radius $\delta$ around $X$:
--
--   $$
--   [\rho]^k_\delta(X)=\sup\{\rho(Y): Y\in L^\infty,\ W_k(Y,X)\le\delta\},\qquad X\in L^\infty.
--   $$
--
--   The robust version models an agent who is uncertain about the distribution of the loss and evaluates the worst case among all distributions within transport distance $\delta$.
--
--   **Formalization Note** The quantile is written as $F^{-1}_X(x)=\mathrm{VaR}^L_{1-x}(X)$. The integrand is evaluated on $[0,1]$; its values at the two endpoints are irrelevant to the integral. The supremum is the real `sSup` of the set `robustSet` of attained values; this set always contains $\rho(X)$, and for $\rho=\mathrm{VaR}$ its boundedness from above is part of the statement of Proposition 4(iii) in this mission, so the real supremum is the paper's value there.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 28, §8.2, definition of W_k and (32)

import Mathlib
import Definitions.Def_TailRiskSharing_RobustVaR_Setting

namespace TailRiskSharing.RobustVaR

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- §8.2 p. 28: the Wasserstein metric of order `k`,
`W_k(X, Y) = (∫₀¹ |F⁻¹_X(x) − F⁻¹_Y(x)|^k dx)^{1/k}`, with the quantile `F⁻¹_X(x) = VaR^L_{1-x}(X)`. -/
noncomputable def wassersteinK (P : Measure Ω) (k : ℝ) (X Y : Ω → ℝ) : ℝ :=
  (∫ x in (0:ℝ)..1, |TailRiskSharing.VaRConv.VaRL P (1 - x) X - TailRiskSharing.VaRConv.VaRL P (1 - x) Y| ^ k) ^ (1 / k)

/-- (32) p. 28: the values `ρ(Y)` over the Wasserstein ball `{Y ∈ L^∞ : W_k(Y, X) ≤ δ}`. -/
def robustSet (P : Measure Ω) (k δ : ℝ) (ρ : (Ω → ℝ) → ℝ) (X : Ω → ℝ) : Set ℝ :=
  {r | ∃ Y ∈ TailRiskSharing.TailConv.Linf P, wassersteinK P k Y X ≤ δ ∧ r = ρ Y}

/-- (32) p. 28: the robust version `[ρ]^k_δ(X) = sup {ρ(Y) : W_k(Y, X) ≤ δ}`, `X ∈ L^∞`. -/
noncomputable def robust (P : Measure Ω) (k δ : ℝ) (ρ : (Ω → ℝ) → ℝ) (X : Ω → ℝ) : ℝ :=
  sSup (robustSet P k δ ρ X)

end TailRiskSharing.RobustVaR


