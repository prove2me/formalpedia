-- Prove2me | Definitions.Def_MarketInterferenceAudit_FluidLimit_Arrivals
-- name    : MarketInterferenceAudit_FluidLimit_Arrivals
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:41:21.960573+00:00
-- url     : https://prove2.me/theorems/436eea43-c49e-4ea8-86b5-07403e5c1ed3
-- title:
--   Common-space Poisson arrivals and normalized matching inputs
-- statement:
--   Let $\lambda\in[0,\infty)^{n_d}$ and $\pi\in[0,\infty)^{n_s}$ be demand and supply rates on a probability space $(\Omega,\mathcal F,P)$. An arrival array consists of measurable integer-valued count vectors $(D^n,S^n)$ on this same space for every positive integer density $n$, whose joint distribution is
--
--   $$\mathcal L(D^n,S^n)=\bigotimes_i\operatorname{Poisson}(n\lambda_i)\;\otimes\;\bigotimes_j\operatorname{Poisson}(n\pi_j).$$
--
--   The normalized demand and supply are $D^n/n,S^n/n$. Given the published network program $\Phi_n$, its scaled sample value is $V_n=\Phi_n(D^n,S^n)/n$. No limit or optimality property is included in this definition. The probability-space and nonnegative-rate requirements are imposed by the goal theorem; the structure itself can be parameterized by any measure and rates, using the published count law's clamping outside the admissible domain.
--
--   This interface places the paper's arrivals on one space so that almost-sure convergence is meaningful. It permits arbitrary coupling across densities, including counts from the source Poisson processes. It does not impose independence across densities. Index $r\in\mathbb N$ denotes density $n=r+1$. The normalized functions divide only by this positive density. The matching model and Poisson law are imported published definitions, not redeclared here.
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, https://arxiv.org/abs/2205.02274v4, §3.1, pp. 5–7; Theorem 1, (7), p. 12; §C.1, pp. 37–40

import Mathlib
import Definitions.Def_MarketInterference_FluidLimit_PoissonCounts

open MeasureTheory

namespace MarketInterferenceAudit.FluidLimit

/-- Common-space arrivals for arXiv:2205.02274v4, §3.1, pp. 5–7, and Theorem 1, p. 12.
Index `r : ℕ` denotes positive integer density `r + 1`. At each density the whole count vector
has the published independent-coordinate Poisson law. No cross-density independence or limit
is imposed; in particular this includes the source's Poisson process construction. -/
structure Arrivals {nd ns : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (lam : Fin nd → ℝ) (pi : Fin ns → ℝ) where
  counts : ℕ → Ω → (Fin nd → ℕ) × (Fin ns → ℕ)
  measurable_counts : ∀ r, Measurable (counts r)
  law : ∀ r, Measure.map (counts r) P =
    MarketInterference.FluidLimit.fluidLaw lam pi ((r + 1 : ℕ) : ℝ)

variable {nd ns : ℕ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} {lam : Fin nd → ℝ} {pi : Fin ns → ℝ}

/-- Demand divided by the positive density, for the unit-capacity LP. -/
noncomputable def Arrivals.demand (R : Arrivals P lam pi) (r : ℕ) (ω : Ω) : Fin nd → ℝ :=
  fun i => ((R.counts r ω).1 i : ℝ) / ((r + 1 : ℕ) : ℝ)

/-- Supply divided by the positive density, for the unit-capacity LP. -/
noncomputable def Arrivals.supply (R : Arrivals P lam pi) (r : ℕ) (ω : Ω) : Fin ns → ℝ :=
  fun j => ((R.counts r ω).2 j : ℝ) / ((r + 1 : ℕ) : ℝ)

/-- The sample value in (7): the original LP has capacity `(r+1) k`, and its optimal
value is divided by `r+1`. This is not an artificially supplied optimum or limit. -/
noncomputable def Arrivals.scaledValue {I E : Type} [Fintype E] [DecidableEq I]
    (R : Arrivals P lam pi) (N : MarketInterference.FluidBias.Network nd ns I E)
    (r : ℕ) (ω : Ω) : ℝ :=
  MarketInterference.FluidBias.Phi N ((r + 1 : ℕ) : ℝ)
    (fun i => ((R.counts r ω).1 i : ℝ)) (fun j => ((R.counts r ω).2 j : ℝ)) /
      ((r + 1 : ℕ) : ℝ)

end MarketInterferenceAudit.FluidLimit


