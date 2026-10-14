-- Prove2me | Definitions.Def_MarketInterference_FluidLimit_PoissonCounts
-- name    : MarketInterference_FluidLimit_PoissonCounts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:08.607308+00:00
-- url     : https://prove2.me/theorems/7e93deac-6812-4d03-be54-12f776ed4bec
-- title:
--   pp. 5–8 — the Poisson law of the counts (D^{τ,λ}, S^τ) and the global treatment effect Δ^τ (Definition 1)
-- statement:
--   Demand units of type $i$ and supply units of type $j$ arrive by Poisson processes with rates $\lambda_i$ and $\pi_j$ (pp. 5–6). At density $\tau$ the counts collected in one matching cycle are
--
--   $$
--   D^{\tau,\lambda}_i\sim\mathrm{Poisson}(\lambda_i\tau),\qquad S^\tau_j\sim\mathrm{Poisson}(\pi_j\tau),
--   $$
--
--   all independent. The **count law** at density $\tau$ is the joint law of $(D^{\tau,\lambda},S^\tau)$, a probability measure on $\mathbb N^{n_d}\times\mathbb N^{n_s}$.
--
--   Given a treatment that changes the demand rates from $\lambda$ (global control) to $\lambda+\beta$ (global treatment), the **global treatment effect** at density $\tau$ (Definition 1, p. 8) is
--
--   $$
--   \Delta^\tau=\frac1\tau\,\mathbb E\Big[\Phi_\tau\big(D^{\tau,\lambda+\beta},S^\tau\big)-\Phi_\tau\big(D^{\tau,\lambda},S^\tau\big)\Big].
--   $$
--
--   These are the random inputs of the fluid-limit theorem: the scaled expected value $\mathbb E[\frac1\tau\Phi_\tau(D^{\tau,\lambda},S^\tau)]$ is an expectation against the count law.
--
--   **Formalization Note** The count law is the product of the independent Poisson laws (`Measure.pi` over types, then `Measure.prod` of demand and supply); independence across types and between demand and supply is the paper's reading of "Poisson process" per type and is used by its proofs, though not written out. The Poisson means are written `Real.toNNReal (λ_i τ)`, which is the mean itself whenever $\lambda,\pi,\tau\ge 0$. Since the global-treatment and global-control markets are never observed jointly, $\Delta^\tau$ is encoded as $\frac1\tau$ times the difference of the two expectations, each under its own count law; this equals the paper's expectation of the difference under any coupling, because both integrands are bounded.
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, pp. 5–6, §3.1 (Poisson counts); p. 8, Definition 1

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_NetworkLP

namespace MarketInterference.FluidLimit

open MeasureTheory ProbabilityTheory

variable {nd ns : ℕ}

/-- The joint law of the demand and supply counts `(D^{τ,λ}, S^τ)` at density `τ`
(arXiv:2205.02274v4, pp. 5–6 and 8): independent Poisson counts, `D^{τ,λ}_i ∼ Poisson(λ_i τ)` and
`S^τ_j ∼ Poisson(π_j τ)`, as a measure on `(Fin nd → ℕ) × (Fin ns → ℕ)`. The means are clamped by
`Real.toNNReal`, which is inactive whenever `λ, π ≥ 0` and `τ ≥ 0`. -/
noncomputable def fluidLaw (lam : Fin nd → ℝ) (pi : Fin ns → ℝ) (τ : ℝ) :
    Measure ((Fin nd → ℕ) × (Fin ns → ℕ)) :=
  (Measure.pi fun i => poissonMeasure (Real.toNNReal (lam i * τ))).prod
    (Measure.pi fun j => poissonMeasure (Real.toNNReal (pi j * τ)))

variable {I E : Type} [Fintype E] [DecidableEq I]

/-- The global treatment effect `Δ^τ` of Definition 1 (p. 8):
`Δ^τ = (1/τ) (E[Φ_τ(D^{τ,λ+β}, S^τ)] − E[Φ_τ(D^{τ,λ}, S^τ)])`, each expectation taken under the
Poisson law of its own demand vector (the global-treatment and global-control markets are never
observed jointly, so only the two marginal laws enter). -/
noncomputable def globalEffect (N : MarketInterference.FluidBias.Network nd ns I E) (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ)
    (τ : ℝ) : ℝ :=
  (1 / τ) * ((∫ z, MarketInterference.FluidBias.Phi N τ (fun i => (z.1 i : ℝ)) (fun j => (z.2 j : ℝ))
      ∂(fluidLaw (fun i => lam i + beta i) pi τ)) -
    ∫ z, MarketInterference.FluidBias.Phi N τ (fun i => (z.1 i : ℝ)) (fun j => (z.2 j : ℝ)) ∂(fluidLaw lam pi τ))

end MarketInterference.FluidLimit


