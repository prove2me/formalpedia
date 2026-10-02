-- Prove2me | Definitions.Def_pme_measurement_conditions
-- name    : pme_measurement_conditions
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-02T09:20:32.422996+00:00
-- url     : https://prove2.me/theorems/e2ed697f-e34d-4c70-8a98-48ee3be8fcfa
-- title:
--   Conditions EQ-MEAS, EQ-LIND, EQ-HS, EQ-KL on a black-box process $\Phi_X$
-- statement:
--   The four characterizations of the spectral equilibration process $\Phi_X$ associated with a Hermitian observable $X=\sum_x xP_x$ on $\mathbb C^n$, as properties of a map $\Phi$ on matrices (only its values on density matrices matter).
--
--   - **EQ-MEAS** (nonselective projective measurement): $\Phi(\rho)=\sum_x P_x\rho P_x$ for every density matrix $\rho$.
--   - **EQ-LIND** (spectral equilibration): for every density matrix $\rho$, the Lindblad equation $\frac{d\rho}{dt}=X\rho X-\tfrac12\{X^2,\rho\}$ with $\rho(0)=\rho$ has a solution on $t\ge0$, and $\Phi(\rho)=\lim_{t\to\infty}\rho(t)$ for every such solution.
--   - **EQ-HS** (closest commuting ensemble): for every density matrix $\rho$, $\Phi(\rho)$ is a density matrix with $[\Phi(\rho),X]=0$ attaining $\min\{\|\rho-\sigma\|_{HS}^2:\sigma\in D,\ [\sigma,X]=0\}$.
--   - **EQ-KL** (closest commuting ensemble in information): the same with the relative entropy $D(\rho\|\sigma)$ in place of $\|\rho-\sigma\|_{HS}^2$.
--
--   Here $\Phi(\rho)=\operatorname{argmin}$ is encoded as \"$\Phi(\rho)$ is a minimizer\"; uniqueness of the minimizer is part of what Theorem 1 proves.
-- source:
--   G. Carcassi (Assumptions of Physics collaboration), "Projective measurements are equilibration processes", AoP Technical Brief 017, https://assumptionsofphysics.org/resources/briefs, Section 2, Conditions EQ-MEAS, EQ-LIND, EQ-HS, EQ-KL, p. 2

import Mathlib
import Definitions.Def_pme_quantum_basics

/-!
The four characterizations EQ-MEAS, EQ-LIND, EQ-HS, EQ-KL of the black-box spectral
equilibration process `Φ_X` (Carcassi, AoP brief 017, Section 2), as predicates on a map
`Φ : Matrix n n ℂ → Matrix n n ℂ` (only its values on density matrices matter).
-/

namespace ProjectiveMeasurementEquilibration

open Matrix Filter Topology

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Condition EQ-MEAS: `Φ(ρ) = ∑ₓ Pₓ ρ Pₓ` for every density matrix `ρ`. -/
def EqMeas {X : Matrix n n ℂ} (hX : X.IsHermitian) (Φ : Matrix n n ℂ → Matrix n n ℂ) : Prop :=
  ∀ ρ, IsDensityMatrix ρ → Φ ρ = pinching hX ρ

/-- Condition EQ-LIND: for every density matrix `ρ`, the Lindblad equation
`dρ/dt = XρX − ½{X², ρ}` started at `ρ` has a solution on `t ≥ 0`, and every such solution
converges to `Φ(ρ)` as `t → ∞`. -/
def EqLind (X : Matrix n n ℂ) (Φ : Matrix n n ℂ → Matrix n n ℂ) : Prop :=
  ∀ ρ, IsDensityMatrix ρ →
    (∃ ρt : ℝ → Matrix n n ℂ, IsLindbladSolution X ρ ρt) ∧
    ∀ ρt : ℝ → Matrix n n ℂ, IsLindbladSolution X ρ ρt → Tendsto ρt atTop (𝓝 (Φ ρ))

/-- Condition EQ-HS: `Φ(ρ)` is a density matrix commuting with `X` that minimizes
`‖ρ − σ‖²_HS` over all density matrices `σ` commuting with `X`. -/
def EqHS (X : Matrix n n ℂ) (Φ : Matrix n n ℂ → Matrix n n ℂ) : Prop :=
  ∀ ρ, IsDensityMatrix ρ →
    IsDensityMatrix (Φ ρ) ∧ X * Φ ρ = Φ ρ * X ∧
    ∀ σ, IsDensityMatrix σ → X * σ = σ * X → hsDistSq ρ (Φ ρ) ≤ hsDistSq ρ σ

/-- Condition EQ-KL: `Φ(ρ)` is a density matrix commuting with `X` that minimizes
`D(ρ‖σ)` over all density matrices `σ` commuting with `X`. -/
def EqKL (X : Matrix n n ℂ) (Φ : Matrix n n ℂ → Matrix n n ℂ) : Prop :=
  ∀ ρ, IsDensityMatrix ρ →
    IsDensityMatrix (Φ ρ) ∧ X * Φ ρ = Φ ρ * X ∧
    ∀ σ, IsDensityMatrix σ → X * σ = σ * X → relEntropy ρ (Φ ρ) ≤ relEntropy ρ σ

end ProjectiveMeasurementEquilibration


