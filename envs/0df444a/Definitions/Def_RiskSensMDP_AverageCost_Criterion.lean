-- Prove2me | Definitions.Def_RiskSensMDP_AverageCost_Criterion
-- name    : RiskSensMDP_AverageCost_Criterion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:27:58.759304+00:00
-- url     : https://prove2.me/theorems/a2f75ee5-4484-4746-9f49-550c2a7faa53
-- title:
--   Power-utility average cost (5.1) J_σ, J, the risk-neutral average cost, risk-neutral optimality, and positive Harris recurrence of the MDP
-- statement:
--   In the model of §2, fix $\gamma>0$ and the power utility $U(y)=y^\gamma$ on $[0,\infty)$, so that $U^{-1}(t)=t^{1/\gamma}$.
--
--   1. The **risk-sensitive average cost** (5.1) of a policy $\sigma\in\Pi$ from the initial state $x$ is
--   $$
--   J_\sigma(x)=\limsup_{n\to\infty}\frac1n\,U^{-1}\Big(\mathbb E^\sigma_x\big[U(C^n)\big]\Big)=\limsup_{n\to\infty}\frac1n\Big(\mathbb E^\sigma_x\big[(C^n)^\gamma\big]\Big)^{1/\gamma},
--   $$
--   and the optimal value is $J(x)=\inf_{\sigma\in\Pi}J_\sigma(x)$.
--   2. The **risk-neutral average cost** of $\sigma$ is
--   $$
--   \rho_\sigma(x)=\limsup_{n\to\infty}\frac1n\,\mathbb E^\sigma_x[C^n].
--   $$
--   This is $J_\sigma(x)$ at $\gamma=1$.
--   3. A stationary policy $\pi^*=(f^*,f^*,\dots)$ is **optimal for the risk-neutral average cost problem** if $\rho_{\pi^*}(x)\le\rho_\sigma(x)$ for every $\sigma\in\Pi$ and every $x\in E$.
--   4. The MDP is **positive Harris recurrent** if, for every stationary policy $(f,f,\dots)$, the state process (the Markov chain with kernel $P_f(x,\cdot)=Q(\cdot\mid x,f(x))$) is positive Harris recurrent.
--
--   These are the criteria compared in Theorems 5.1 and 5.2. $J_\sigma$ is the certainty-equivalent cost per stage of a decision maker with constant relative risk attitude, and $\rho_\sigma$ is its risk-neutral counterpart.
--
--   **Formalization Note** The paper states (5.1) for a general continuous strictly increasing $U$ but uses it only for $U(y)=y^\gamma$ (§5.1). Here it is defined for that $U$, with $\gamma$ a parameter. Powers are real powers (`Real.rpow`) of the accumulated cost. $C^n\ge 0$ holds almost surely under every $\mathbb P^\sigma_x$, which is all the expectations see. For $n\ge1$ every term of both sequences lies in $[\underline c,\bar c]$, so the real $\limsup$ is the true one. At $n=0$ Lean's $1/0=0$ makes the term $0$, which does not affect a $\limsup$. For the same reason the family $\{J_\sigma(x)\}_\sigma$ is bounded below by $\underline c$, so $J(x)$ is a genuine infimum whenever $\Pi$ is nonempty. The paper does not define the risk-neutral average cost. It is taken as the $\limsup$, matching (5.1) at $\gamma=1$. Risk-neutral optimality is required against all history-dependent policies, as in the paper's proof of Theorem 5.2, which compares $\pi^*$ with an arbitrary $\sigma\in\Pi$.
-- source:
--   Bäuerle & Rieder, More Risk-Sensitive Markov Decision Processes, authors' manuscript (KIT repository 1000039663; published Math. Oper. Res. 39(1):105–120, 2014), p. 17, §5, display (5.1), §5.1, and the sentence before Theorem 5.2 (positive Harris recurrent MDP)

import Mathlib
import Definitions.Def_RiskSensMDP_AverageCost_Model
import Definitions.Def_RiskSensMDP_AverageCost_HarrisRecurrence

open MeasureTheory ProbabilityTheory Filter Finset

namespace RiskSensMDP.AverageCost

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- The power-utility average cost (5.1) with `U(y) = y^γ`, `γ > 0` (§5.1, p. 17):
`J_σ(x) = limsup_{n → ∞} (1/n) U⁻¹(E^σ_x[U(C^n)]) = limsup_{n → ∞} (1/n) (E^σ_x[(C^n)^γ])^{1/γ}`.
For `n ≥ 1` the terms lie in `[c̲, c̄]`, so the real `limsup` is the true one. -/
noncomputable def powerAvgCost (M : Model E A) (γ : ℝ) (σ : Policy M) (x : E) : ℝ :=
  limsup (fun n : ℕ =>
    (1 / (n : ℝ)) * (∫ ω, (cost M n ω) ^ γ ∂(pathMeasure M σ x)) ^ (1 / γ)) atTop

/-- The optimal power-utility average cost (5.1): `J(x) = inf_{σ ∈ Π} J_σ(x)`. -/
noncomputable def optPowerAvgCost (M : Model E A) (γ : ℝ) (x : E) : ℝ :=
  ⨅ σ : Policy M, powerAvgCost M γ σ x

/-- The risk-neutral average cost `ρ_σ(x) = limsup_{n → ∞} (1/n) E^σ_x[C^n]`. -/
noncomputable def riskNeutralAvgCost (M : Model E A) (σ : Policy M) (x : E) : ℝ :=
  limsup (fun n : ℕ => (1 / (n : ℝ)) * ∫ ω, cost M n ω ∂(pathMeasure M σ x)) atTop

/-- `π* = (f*, f*, …)` is an optimal stationary policy for the risk-neutral average cost problem:
`ρ_{π*}(x) ≤ ρ_σ(x)` for every history-dependent policy `σ ∈ Π` and every `x ∈ E`. -/
def IsRiskNeutralOptimal (M : Model E A) (f : StationaryRule M) : Prop :=
  ∀ (σ : Policy M) (x : E), riskNeutralAvgCost M f.toPolicy x ≤ riskNeutralAvgCost M σ x

/-- The MDP is positive Harris recurrent (§5.1, p. 17): for every stationary policy `(f, f, …)` the
state process, the Markov chain with kernel `P_f(x, ·) = Q(· | x, f(x))`, is positive Harris
recurrent. -/
def MDPPositiveHarris (M : Model E A) : Prop :=
  ∀ f : StationaryRule M, IsPositiveHarrisRecurrent (stateKernel M f)

end RiskSensMDP.AverageCost


