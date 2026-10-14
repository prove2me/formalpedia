-- Prove2me | Definitions.Def_MarketInterference_FiniteSample_Experiment
-- name    : MarketInterference_FiniteSample_Experiment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:10.778389+00:00
-- url     : https://prove2.me/theorems/da05165e-7e85-42fc-bf5e-1e82ada2f8dd
-- title:
--   pp. 8, 20, 23, 25 — Poisson laws of the experiment, subgradients (17)–(18), the SP estimator (Definition 5) and Ψ_τ (Definition 6)
-- statement:
--   Fix a matching network, a density $\tau>0$, a control demand rate $\lambda\in\mathbb R^{n_d}_{\ge 0}$, a treatment effect $\beta$ with $\lambda+\beta\ge 0$, a supply rate $\pi\in\mathbb R^{n_s}_{\ge0}$ and a treatment fraction $\rho\in(0,1)$.
--
--   1. **Partial-treatment market.** For $\eta\in[0,1]$, $D^{\tau,\lambda+\eta\beta}$ and $S^{\tau,\pi}$ are independent vectors of independent Poisson counts, $D_i\sim\mathrm{Poisson}((\lambda_i+\eta\beta_i)\tau)$ and $S_j\sim\mathrm{Poisson}(\pi_j\tau)$.
--   2. **Experiment.** Control counts $D^{\tau,\mathrm{control}}_i\sim\mathrm{Poisson}((1-\rho)\lambda_i\tau)$, treatment counts $D^{\tau,\mathrm{treatment}}_i\sim\mathrm{Poisson}(\rho(\lambda_i+\beta_i)\tau)$ and supply counts $S^\tau_j\sim\mathrm{Poisson}(\pi_j\tau)$, all independent; the experiment demand is $D^{\tau,\mathrm{experiment}}=D^{\tau,\mathrm{control}}+D^{\tau,\mathrm{treatment}}$.
--   3. **Subgradients** (17)–(18). With $e_i$ the $i$-th unit vector,
--   $$
--   a^+_i=\Phi_\tau(d+e_i,s)-\Phi_\tau(d,s),\qquad a^-_i=\Phi_\tau(d,s)-\Phi_\tau(d-e_i,s).
--   $$
--   4. **Shadow-price estimator** (Definition 5, with the selection $A=A^-$ of p. 25):
--   $$
--   \hat\Delta^\tau_{SP}=\frac1\tau\,A^{\tau,\mathrm{experiment},-}\cdot\Big(\frac1\rho D^{\tau,\mathrm{treatment}}-\frac1{1-\rho}D^{\tau,\mathrm{control}}\Big),
--   $$
--   where $A^{\tau,\mathrm{experiment},-}_i=a^-_i$ evaluated at $(D^{\tau,\mathrm{experiment}},S^\tau)$.
--   5. **Finite-sample partial-treatment value function** (Definition 6):
--   $$
--   \Psi_\tau(\eta)=\mathbb E\Big[\frac1\tau\Phi_\tau(D^{\tau,\lambda+\eta\beta},S^{\tau,\pi})\Big].
--   $$
--
--   These are the objects of Theorem 6: the estimator is computed from the separately observed control and treatment counts, and $\Psi_\tau$ is the expected scaled matching value when a fraction $\eta$ of demand is treated.
--
--   **Formalization Note** A vector of independent Poisson counts is the product measure `Measure.pi` of Mathlib's `poissonMeasure` on `Fin n → ℕ`; the experiment law is the product of the control, treatment and supply laws, in that order. Independence across types and between demand and supply is the paper's standing reading of one Poisson process per type (p. 5). Means are passed through `Real.toNNReal`, which is inactive for the nonnegative means used here (for $\Psi_\tau$, whenever $\eta\in[0,1]$). When $d_i=0$, $\Phi_\tau(d-e_i,s)$ is infeasible and Lean's value is $0$; in the estimator this junk $a^-_i$ is multiplied by $\frac1\rho D^{\mathrm{treatment}}_i-\frac1{1-\rho}D^{\mathrm{control}}_i=0$. All expectations are of functions bounded by a constant (or of linear growth) on a countable space.
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, pp. 5–6 (Poisson counts), p. 8 (experiment), p. 20 (Definition 5), p. 23 (Definition 6), p. 25 ((17)–(18) and the selection a = a^−)

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_NetworkLP

namespace MarketInterference.FiniteSample

open MeasureTheory ProbabilityTheory

/-- The law of a vector of independent Poisson counts with means `m i`
(arXiv:2205.02274v4, pp. 5–6): the product measure `⊗ᵢ Poisson(m i)` on `Fin n → ℕ`. The mean is
clamped by `Real.toNNReal`, which is inactive whenever `m ≥ 0`. -/
noncomputable def poisLaw {n : ℕ} (m : Fin n → ℝ) : Measure (Fin n → ℕ) :=
  Measure.pi fun i => poissonMeasure (Real.toNNReal (m i))

/-- The law of the demand and supply counts `(D^{τ,λ+ηβ}, S^{τ,π})` of the partial-treatment market
(p. 23): independent `D_i ∼ Poisson((λ_i + η β_i) τ)` and `S_j ∼ Poisson(π_j τ)`. -/
noncomputable def marketLaw {nd ns : ℕ} (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ) (τ η : ℝ) :
    Measure ((Fin nd → ℕ) × (Fin ns → ℕ)) :=
  (poisLaw fun i => (lam i + η * beta i) * τ).prod (poisLaw fun j => pi j * τ)

/-- The law of the experiment data (p. 8): independent control counts
`D^{τ,control}_i ∼ Poisson((1 − ρ) λ_i τ)`, treatment counts `D^{τ,treatment}_i ∼ Poisson(ρ (λ_i + β_i) τ)`
and supply counts `S^τ_j ∼ Poisson(π_j τ)`, as a measure on
`((control counts) × (treatment counts)) × (supply counts)`. -/
noncomputable def experimentLaw {nd ns : ℕ} (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ) (ρ τ : ℝ) :
    Measure (((Fin nd → ℕ) × (Fin nd → ℕ)) × (Fin ns → ℕ)) :=
  ((poisLaw fun i => (1 - ρ) * lam i * τ).prod (poisLaw fun i => ρ * (lam i + beta i) * τ)).prod
    (poisLaw fun j => pi j * τ)

variable {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq I]

/-- The positive-demand subgradient (17), p. 25: `a⁺_i = Φ_τ(d + e_i, s) − Φ_τ(d, s)`. -/
noncomputable def Aplus (N : MarketInterference.FluidBias.Network nd ns I E) (τ : ℝ) (d : Fin nd → ℝ) (s : Fin ns → ℝ)
    (i : Fin nd) : ℝ :=
  MarketInterference.FluidBias.Phi N τ (d + Pi.single i 1) s - MarketInterference.FluidBias.Phi N τ d s

/-- The negative-demand subgradient (18), p. 25: `a⁻_i = Φ_τ(d, s) − Φ_τ(d − e_i, s)`.
When `d i = 0` the program `Φ_τ(d − e_i, s)` is infeasible and Lean's `sSup ∅ = 0` is used; every
use below multiplies `a⁻_i` by a quantity that vanishes when `d i = 0`. -/
noncomputable def Aminus (N : MarketInterference.FluidBias.Network nd ns I E) (τ : ℝ) (d : Fin nd → ℝ) (s : Fin ns → ℝ)
    (i : Fin nd) : ℝ :=
  MarketInterference.FluidBias.Phi N τ d s - MarketInterference.FluidBias.Phi N τ (d - Pi.single i 1) s

/-- The shadow-price estimator of Definition 5 (p. 20), with the selection `A = A⁻` of p. 25:
`Δ̂^τ_SP = (1/τ) A^{τ,experiment,−} · ((1/ρ) D^{τ,treatment} − (1/(1−ρ)) D^{τ,control})`,
where `A^{τ,experiment,−} = A⁻(D^{τ,control} + D^{τ,treatment}, S^τ)`. Arguments: control counts `dc`,
treatment counts `dt`, supply counts `s`. -/
noncomputable def SPest (N : MarketInterference.FluidBias.Network nd ns I E) (ρ τ : ℝ) (dc dt : Fin nd → ℕ) (s : Fin ns → ℕ) :
    ℝ :=
  (1 / τ) * ∑ i, Aminus N τ (fun i => ((dc i + dt i : ℕ) : ℝ)) (fun j => (s j : ℝ)) i *
    ((1 / ρ) * (dt i : ℝ) - (1 / (1 - ρ)) * (dc i : ℝ))

/-- The finite-sample partial-treatment value function of Definition 6 (p. 23):
`Ψ_τ(η) = E[(1/τ) Φ_τ(D^{τ,λ+ηβ}, S^{τ,π})]`. -/
noncomputable def PsiTau (N : MarketInterference.FluidBias.Network nd ns I E) (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ)
    (τ η : ℝ) : ℝ :=
  ∫ z, (1 / τ) * MarketInterference.FluidBias.Phi N τ (fun i => (z.1 i : ℝ)) (fun j => (z.2 j : ℝ)) ∂(marketLaw lam beta pi τ η)

end MarketInterference.FiniteSample


