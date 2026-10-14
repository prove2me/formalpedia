-- Prove2me | Definitions.Def_MarketInterference_FluidBias_Estimators
-- name    : MarketInterference_FluidBias_Estimators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:19:11.223377+00:00
-- url     : https://prove2.me/theorems/1327ec2a-8052-4bac-8f6c-26e92e11e99f
-- title:
--   pp. 13, 20, 26 — the partial-treatment value function Ψ, the effect Δ, v̄*, and the fluid RCT, SP and SP+ estimators
-- statement:
--   Consider a matching experiment with supply arrival rate $\pi$, demand arrival rate $\lambda$ under global control and $\lambda+\beta$ under global treatment, and treatment fraction $\rho$. The **partial-treatment value function** (Definition 3) is
--   $$
--   \Psi(\eta)=\Phi(\lambda+\eta\beta,\pi),\qquad \eta\in[0,1],
--   $$
--   and the fluid global treatment effect (Corollary 1, (8)) is $\Delta=\Psi(1)-\Psi(0)=\Phi(\lambda+\beta,\pi)-\Phi(\lambda,\pi)$.
--
--   The experiment state is $\lambda^{\mathrm{experiment}}=\lambda+\rho\beta$. Given a path flow $y$ (a path decomposition of the optimal flow of $\Phi(\lambda+\rho\beta,\pi)$), the **average value** of a type-$i$ demand unit (10) is
--   $$
--   \bar v^*_i=\sum_{j=1}^{n_s}\sum_{p=1}^{n_{i,j}}\frac{y^*_{i,j,p}}{\lambda^{\mathrm{experiment}}_i}\,\nu_{i,j,p}.
--   $$
--   The fluid **RCT estimator** is $\hat\Delta_{\mathrm{RCT}}=\bar v^*\cdot\beta$ ((9)); the fluid **shadow-price (SP) estimator** is $\hat\Delta_{\mathrm{SP}}=a^\rho\cdot\beta$ ((11)), where $a^\rho$ is the demand part of an optimal solution of the dual (5) of $\Phi(\lambda+\rho\beta,\pi)$; and the **shadow-price-plus estimator** (Definition 7) is
--   $$
--   \hat\Delta_{\mathrm{SP+}}=(1-2\rho)\,\hat\Delta_{\mathrm{RCT}}+2\rho\,\hat\Delta_{\mathrm{SP}}.
--   $$
--
--   These are the objects compared by the bias results of the paper (Theorems 2, 4, 9, 10).
--
--   **Formalization Note.** The estimators are defined by the right-hand sides of (9) and (11), which Propositions 2 and 5 identify as the fluid limits of the random RCT and SP estimators; those limit statements are not part of this mission. `Psi` evaluates `Phi` with $\tau=1$ at $\lambda+\eta\beta$; it is meaningful for $\eta\in[0,1]$, where $\lambda+\eta\beta\ge0$. In `vbar`, if $\lambda_i+\rho\beta_i=0$ Lean's convention $x/0=0$ gives $\bar v^*_i=0$; this can happen only when $\lambda_i=\beta_i=0$, so the term contributes nothing to $\bar v^*\cdot\beta$. `spFluid` takes the dual solution as an argument; the theorems require it to be optimal.
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 13, Definition 3, Corollary 1 (8), Proposition 2 (9)–(10); p. 8 (λ^experiment = λ + ρβ); p. 20, Proposition 5 (11); p. 26, Definition 7

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_NetworkLP
import Definitions.Def_MarketInterference_FluidBias_PathFlow

namespace MarketInterference.FluidBias

variable {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq I]

/-- The partial-treatment value function (Definition 3, p. 13):
`Ψ(η) = Φ(λ + η β, π)`, the fluid LP value (τ = 1) at demand rate `λ + η β` and supply rate `π`.
Meaningful for `η ∈ [0, 1]`, where `λ + η β ≥ 0`. -/
noncomputable def Psi (N : Network nd ns I E) (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ)
    (η : ℝ) : ℝ :=
  Phi N 1 (lam + η • beta) pi

/-- The fluid global treatment effect `Δ = Ψ(1) − Ψ(0) = Φ(λ + β, π) − Φ(λ, π)`
(Corollary 1, (8), and p. 13). -/
noncomputable def Delta (N : Network nd ns I E) (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ) : ℝ :=
  Psi N lam beta pi 1 - Psi N lam beta pi 0

/-- The average value `v̄*_i` of a type-`i` demand unit in the experiment state ((10), p. 13):
`v̄*_i = ∑_j ∑_p y_{i,j,p} ν_{i,j,p} / λ^experiment_i` with `λ^experiment = λ + ρ β`, computed
from a path flow `y` (a path decomposition of the optimal flow of `Φ(λ + ρβ, π)`). When
`λ_i + ρ β_i = 0`, Lean's `x / 0 = 0` gives `v̄*_i = 0`. -/
noncomputable def vbar {N : Network nd ns I E} (lam beta : Fin nd → ℝ) (ρ : ℝ)
    (y : SDPath N →₀ ℝ) : Fin nd → ℝ :=
  fun i => (∑ p ∈ y.support with p.i = i, y p * pathValue p) / (lam i + ρ * beta i)

/-- The fluid RCT estimator `Δ̂_RCT = v̄* · β` ((9), p. 13). -/
noncomputable def rctFluid {N : Network nd ns I E} (lam beta : Fin nd → ℝ) (ρ : ℝ)
    (y : SDPath N →₀ ℝ) : ℝ :=
  vbar lam beta ρ y ⬝ᵥ beta

/-- The fluid shadow-price estimator `Δ̂_SP = a^ρ · β` ((11), p. 20), where `a^ρ = q.a` is the
demand part of an optimal solution `q` of the dual (5) of `Φ(λ + ρβ, π)`. -/
def spFluid (q : DualVar nd ns I E) (beta : Fin nd → ℝ) : ℝ :=
  q.a ⬝ᵥ beta

/-- The shadow-price-plus estimator (Definition 7, p. 26):
`Δ̂_SP+ = (1 − 2ρ) Δ̂_RCT + 2ρ Δ̂_SP`. -/
def spPlus (ρ rct sp : ℝ) : ℝ :=
  (1 - 2 * ρ) * rct + 2 * ρ * sp

end MarketInterference.FluidBias


