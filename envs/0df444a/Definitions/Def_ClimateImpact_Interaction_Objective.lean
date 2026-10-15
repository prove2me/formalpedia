-- Prove2me | Definitions.Def_ClimateImpact_Interaction_Objective
-- name    : ClimateImpact_Interaction_Objective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:13.579892+00:00
-- url     : https://prove2.me/theorems/2902135f-ffc2-48ce-b690-ad9d4d8f01f9
-- title:
--   §6.2, proof of Proposition 2, p. 64 — profit function J^i, reduced objective J̃^i, date-t payoff (12), admissible schedules
-- statement:
--   The companies' optimization problem of §3.2, in the evaluated form used in the proof of Proposition 2.
--
--   There are $n$ companies. A **schedule** $\psi=(\psi_s)_{s\in[0,T]}$ gives the vector $\psi_s\in\mathbb R^n$ of emission rates at date $s$. The data are: the rate of time preference $\rho$, the final date $T$, the green investors' wealth share $\alpha$, the risk-aversion constant $\gamma^*$, the vectors $d$ and $\psi_b$ (expected terminal dividends and baseline emissions), the marginal abatement costs $c^i_s$, the covariance matrices $\Sigma_s$, and the **climate externalities** $\theta^i_s(x)$ (as internalized by green investors) and $\theta^{c,i}_s(x)$ (as internalized by companies), functions of the whole emission profile $x\in\mathbb R^n$.
--
--   1. The **profit function** of company $i$ is
--   $$\mathcal J^i(\psi)=\int_0^T e^{-\rho t}\Big(d^i+\int_0^T c^i_s(\psi^i_s-\psi^i_b)\,ds+\int_0^t\theta^{c,i}_s(\psi_s)\,ds+\alpha\int_t^T\theta^i_s(\psi_s)\,ds-\gamma^*\int_t^T[\Sigma_s\mathbf 1]_i\,ds\Big)dt .$$
--   2. The **reduced objective** is
--   $$\tilde{\mathcal J}^i(\psi)=\int_0^T e^{-\rho t}\Big(\int_0^T c^i_s\psi^i_s\,ds+\int_0^t\theta^{c,i}_s(\psi_s)\,ds+\alpha\int_t^T\theta^i_s(\psi_s)\,ds\Big)dt .$$
--   3. The **date-$t$ payoff** (12), the function $F_i$ of §6.3, is
--   $$F_i(x)=\beta^c_t\,\theta^{c,i}_t(x)+\alpha\beta_t\,\theta^i_t(x)+c^i_t x^i .$$
--   4. A schedule $\psi$ is **admissible** for company $i$ if it is Borel measurable and every company's emissions are nonnegative on $[0,T]$, and the functions $s\mapsto c^i_s\psi^i_s$, $s\mapsto\theta^i_s(\psi_s)$, $s\mapsto\theta^{c,i}_s(\psi_s)$ are integrable on $[0,T]$.
--
--   The equilibrium emission schedule of the paper, (9), is a profile from which no company can raise its profit function by changing its own schedule.
--
--   **Formalization Note** The page writes $d$ inside $\mathcal J^i$; since $d$ is a vector (p. 11), its $i$-th coordinate $d^i$ is meant. The page's measure-theoretic layer (Brownian dividends, Girsanov measures) is not formalized: $\mathcal J^i$ is the page's evaluated expected price. Borel measurability and nonnegativity of emissions are required by footnote 7 (p. 11); measurability is encoded by the zero extension of the schedule outside $[0,T]$. Integrability is not on the page; it makes every integral of $\mathcal J^i$ an integral of an integrable function (Lean's Bochner integral is $0$ otherwise). Integrals are interval integrals over $[0,T]$; $\Sigma_s\mathbf 1$ is `Matrix.mulVec (Sig s) 1`.
-- source:
--   SSRN 3562534 (25 Jun 2021), §6.2, proof of Proposition 2, p. 64; (12), p. 19; F_i, §6.3, p. 64; footnote 7, p. 11

import Mathlib
import Definitions.Def_ClimateImpact_Interaction_TimeFactors

namespace ClimateImpact.Interaction

open MeasureTheory

/-- The `i`-th company's profit function `J^i(ψ^i, ψ^{-i})` of §6.2, proof of Proposition 2
(SSRN 3562534, p. 64): the discounted expected equilibrium price under the companies' measure,
`∫_0^T e^{-ρt} (d^i + ∫_0^T c^i_s(ψ^i_s - ψ^i_b) ds + ∫_0^t θ^{c,i}_s(ψ_s) ds
  + α ∫_t^T θ^i_s(ψ_s) ds - γ^* ∫_t^T [Σ_s 1]_i ds) dt`.
Here `θ s x i` is `θ^i_s(x)`, `θc s x i` is `θ^{c,i}_s(x)`, `c i s` is `c^i_s`, `Sig s` is `Σ_s`,
and a schedule `ψ s j` is the emission rate of company `j` at date `s`. -/
noncomputable def objective {n : ℕ} (ρ T α γstar : ℝ) (θ θc : ℝ → (Fin n → ℝ) → Fin n → ℝ)
    (c : Fin n → ℝ → ℝ) (d ψb : Fin n → ℝ) (Sig : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) (ψ : ℝ → Fin n → ℝ) : ℝ :=
  ∫ t in (0)..T, Real.exp (-(ρ * t)) *
    (d i + (∫ s in (0)..T, c i s * (ψ s i - ψb i)) + (∫ s in (0)..t, θc s (ψ s) i)
      + α * (∫ s in t..T, θ s (ψ s) i) - γstar * ∫ s in t..T, Matrix.mulVec (Sig s) (fun _ => 1) i)

/-- The reduced objective `J̃^i(ψ^i, ψ^{-i})` of §6.2 (p. 64):
`∫_0^T e^{-ρt} (∫_0^T c^i_s ψ^i_s ds + ∫_0^t θ^{c,i}_s(ψ_s) ds + α ∫_t^T θ^i_s(ψ_s) ds) dt`. -/
noncomputable def reducedObjective {n : ℕ} (ρ T α : ℝ) (θ θc : ℝ → (Fin n → ℝ) → Fin n → ℝ)
    (c : Fin n → ℝ → ℝ) (i : Fin n) (ψ : ℝ → Fin n → ℝ) : ℝ :=
  ∫ t in (0)..T, Real.exp (-(ρ * t)) *
    ((∫ s in (0)..T, c i s * ψ s i) + (∫ s in (0)..t, θc s (ψ s) i)
      + α * ∫ s in t..T, θ s (ψ s) i)

/-- The date-`t` payoff (12) of Proposition 2 (p. 19), the function `F_i` of §6.3 (p. 64):
`β^c_t θ^{c,i}_t(x) + α β_t θ^i_t(x) + c^i_t x^i` at the emission profile `x ∈ ℝⁿ`. -/
noncomputable def stage12 {n : ℕ} (ρ T α : ℝ) (θ θc : ℝ → (Fin n → ℝ) → Fin n → ℝ)
    (c : Fin n → ℝ → ℝ) (i : Fin n) (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  betaC ρ T t * θc t x i + α * beta ρ T t * θ t x i + c i t * x i

/-- Admissibility of a schedule `ψ` for company `i`: Borel measurability and nonnegative emissions
of every company on `[0, T]` (footnote 7, p. 11: schedules lie in `F([0,T], ℝ₊ⁿ)`), and integrability of the
three `ψ`-dependent integrands of `J^i`, so that every integral in `J^i` is the integral of an
integrable function. -/
def IsAdmissible {n : ℕ} (T : ℝ) (θ θc : ℝ → (Fin n → ℝ) → Fin n → ℝ) (c : Fin n → ℝ → ℝ)
    (i : Fin n) (ψ : ℝ → Fin n → ℝ) : Prop :=
  Measurable ((Set.Icc 0 T).indicator ψ) ∧
    (∀ s ∈ Set.Icc 0 T, ∀ j, 0 ≤ ψ s j) ∧
    IntegrableOn (fun s => c i s * ψ s i) (Set.Icc 0 T) ∧
    IntegrableOn (fun s => θ s (ψ s) i) (Set.Icc 0 T) ∧
    IntegrableOn (fun s => θc s (ψ s) i) (Set.Icc 0 T)

end ClimateImpact.Interaction


