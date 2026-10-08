-- Prove2me | Definitions.Def_DisplMonoMFG_WellPosed_Space
-- name    : DisplMonoMFG_WellPosed_Space
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:28.286552+00:00
-- url     : https://prove2.me/theorems/4b14de4f-6daa-4706-bf9d-8512472f30e5
-- title:
--   $\mathcal P_2(\mathbb R^d)$, $W_2$, $\mathbb L^2$-couplings and the Lions derivative ((2.6)–(2.8))
-- statement:
--   This file fixes the measure-theoretic setting of the master equation.
--
--   1. **State space.** $\mathbb R^d$ carries its Euclidean norm $|\cdot|$.
--   2. **Wasserstein space** ((2.6)). $\mathcal P_2(\mathbb R^d)$ is the set of Borel probability measures $\mu$ on $\mathbb R^d$ with $\int_{\mathbb R^d}|x|^2\,\mu(dx)<\infty$. Functions of the measure variable are defined only on $\mathcal P_2$.
--   3. **Square-integrable couplings.** An $\mathbb L^2$-coupling at $\mu\in\mathcal P_2$ is a probability measure $\pi$ on $\mathbb R^d\times\mathbb R^d$ whose first marginal is $\mu$ and whose second coordinate is square integrable. It is the joint law of a pair $(\xi,\eta)$ with $\mathcal L_\xi=\mu$ and $\eta\in\mathbb L^2$, and $\|\eta\|_2=\big(\int|v|^2\,\pi(dx\,dv)\big)^{1/2}$.
--   4. **Distance** ((2.7)). $W_2(\mu,\nu)$ is the $2$-Wasserstein distance, the square root of the minimal value of $\int|x-y|^2\,\gamma(dx\,dy)$ over couplings $\gamma$ of $\mu$ and $\nu$. It is finite on $\mathcal P_2$. A function $f$ on $\mathcal P_2$ is in $\mathcal C^0(\mathcal P_2)$ if it is $W_2$-continuous.
--   5. **Lions derivative** ((2.8)). A map $(\mu,\tilde x)\mapsto\partial_\mu f(\mu,\tilde x)$ is a (global version of the) Wasserstein gradient of $f:\mathcal P_2\to F$ ($F$ a finite-dimensional real normed space) if, for every $\mu$, $\partial_\mu f(\mu,\cdot)\in\mathbb L^2_\mu$ and
--   $$
--   f(\mathcal L_{\xi+\eta})-f(\mu)=\mathbb E\big[\langle\partial_\mu f(\mu,\xi),\eta\rangle\big]+o(\|\eta\|_2)\qquad\text{for all }\xi,\eta\text{ with }\mathcal L_\xi=\mu,
--   $$
--   the $o(\|\eta\|_2)$ being uniform over such pairs.
--
--   These objects are the domain and the first-order calculus of every statement of the mission: the Hamiltonian, the terminal cost and the solution of the master equation are functions on $\mathbb R^k\times\mathcal P_2$.
--
--   **Formalization Note** The paper's random variables enter only through expectations, so every expectation is an integral against the joint law $\pi$ of $(\xi,\eta)$. Because the underlying probability space has no atom on $\mathcal F^1_0$ (p. 2182), these joint laws are exactly the $\mathbb L^2$-couplings, and the infimum over random variables in (2.7) equals the infimum over couplings. $W_2$ reuses the published `WassersteinDRO.Duality.wassersteinDistance` with $p=2$, converted to a real number. The derivative $\partial_\mu f(\mu,\tilde x)\in\mathbb R^d$ is stored as the linear functional $\eta\mapsto\langle\partial_\mu f(\mu,\tilde x),\eta\rangle$. The page states (2.8) for a fixed $\xi$. Here it is required uniformly over all pairs $(\xi,\eta)$, which is equivalent because the derivative of the lift depends only on the law.
-- source:
--   Gangbo, Mészáros, Mou, Zhang, Mean field games master equations with nonseparable Hamiltonians and displacement monotonicity, Ann. Probab. 50 (2022), §2.2, (2.6)–(2.8), p. 2183

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance

open MeasureTheory

/-! Gangbo, Mészáros, Mou, Zhang, *Mean field games master equations with nonseparable Hamiltonians
and displacement monotonicity*, Ann. Probab. 50 (2022), §2.2, (2.6)–(2.8), pp. 2183–2184
(PDF pp. 6–7): the Wasserstein space `𝒫₂(ℝ^d)`, the distance `W₂`, square-integrable couplings
(the joint laws of `(ξ, η)` with `ℒ_ξ = μ`) and the Lions (Wasserstein) derivative. -/

namespace DisplMonoMFG.WellPosed

/-- The state space `ℝ^d` with its Euclidean norm. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- (2.6), p. 2183: `μ` is a Borel probability measure on `ℝ^d` with finite second moment. -/
def IsP2 {d : ℕ} (μ : Measure (E d)) : Prop :=
  IsProbabilityMeasure μ ∧ ∫⁻ x, ‖x‖ₑ ^ 2 ∂μ < ⊤

/-- `𝒫₂(ℝ^d)`, p. 2183, as a subtype: functions of the measure variable are only ever defined
on `𝒫₂`. -/
def P2 (d : ℕ) := {μ : Measure (E d) // IsP2 μ}

/-- An `𝕃²`-coupling at `μ`: a probability measure `π` on `ℝ^d × ℝ^d` whose first marginal is
`μ` and whose second coordinate is square integrable. It is the joint law of a pair `(ξ, η)`
with `ℒ_ξ = μ`, `η ∈ 𝕃²`. Formalization Note: the paper's random variables enter every planned
statement only through expectations; since `ℙ¹` has no atom on `ℱ¹₀` (p. 2182), the joint laws
of such pairs are exactly these couplings. -/
def IsL2Coupling {d : ℕ} (μ : P2 d) (π : Measure (E d × E d)) : Prop :=
  IsProbabilityMeasure π ∧ π.map Prod.fst = μ.1 ∧ ∫⁻ z, ‖z.2‖ₑ ^ 2 ∂π < ⊤

/-- `‖η‖₂ = (𝔼|η|²)^{1/2}`, computed from the joint law `π` of `(ξ, η)`. -/
noncomputable def l2 {d : ℕ} (π : Measure (E d × E d)) : ℝ :=
  Real.sqrt (∫ z, ‖z.2‖ ^ 2 ∂π)

/-- (2.7), p. 2183: the 2-Wasserstein distance, through the published
`WassersteinDRO.Duality.wassersteinDistance` (an infimum over couplings). It is finite on `𝒫₂`.
Formalization Note: the paper's (2.7) is an infimum over random variables on `(Ω, ℱ_T, ℙ)`; on a
space carrying every coupling this is the same number. -/
noncomputable def W2 {d : ℕ} (μ ν : P2 d) : ℝ :=
  (WassersteinDRO.Duality.wassersteinDistance 2 μ.1 ν.1).toReal

/-- `W₂`-continuity of a function on `𝒫₂` (the space `𝒞⁰(𝒫₂)`, p. 2183). -/
def ContP {d : ℕ} {F : Type*} [NormedAddCommGroup F] (f : P2 d → F) : Prop :=
  ∀ μ : P2 d, ∀ ε > 0, ∃ δ > 0, ∀ μ' : P2 d, W2 μ μ' < δ → ‖f μ' - f μ‖ < ε

/-- The Lions derivative, (2.8), p. 2183: `D` is a (global version of the) Wasserstein gradient
of `f`, i.e. for every `μ`, `D μ ·` is square integrable against `μ` and
`f(ℒ_{ξ+η}) - f(μ) = 𝔼[⟨∂_μ f(μ, ξ), η⟩] + o(‖η‖₂)` uniformly over pairs `(ξ, η)` with
`ℒ_ξ = μ`. The vector `∂_μ f(μ, x̃) ∈ ℝ^d` is represented by the linear functional `D μ x̃`, so
`⟨∂_μ f(μ, x̃), η⟩ = D μ x̃ η` (for vector-valued `f`, `D μ x̃` is the matrix acting on `η`).
Formalization Note: the expectation is an integral against the joint law `π` of `(ξ, η)`; the
coupling form is uniform over all `ξ` of law `μ`, which is equivalent to Fréchet differentiability
of the lift at a fixed `ξ` because the lift's derivative depends only on the law. The page places
`∂_μ f(μ, ·)` in (the closure of gradients in) `𝕃²_μ`; that membership is the `MemLp` clause. -/
def HasLDeriv {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : P2 d → F) (D : P2 d → E d → (E d →L[ℝ] F)) : Prop :=
  ∀ μ : P2 d, MemLp (D μ) 2 μ.1 ∧
    ∀ ε > 0, ∃ δ > 0, ∀ π : Measure (E d × E d), IsL2Coupling μ π → l2 π < δ →
      ∀ ν : P2 d, ν.1 = π.map (fun z => z.1 + z.2) →
        ‖f ν - f μ - ∫ z, D μ z.1 z.2 ∂π‖ ≤ ε * l2 π

end DisplMonoMFG.WellPosed


