-- Prove2me | Definitions.Def_MechanismDesign_Dynamic_OptimalScreening
-- name    : MechanismDesign_Dynamic_OptimalScreening
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T05:52:21.983689+00:00
-- url     : https://prove2.me/theorems/2932e8cc-5c4c-479b-887f-4ea4902bfd8b
-- title:
--   Virtual valuation $\psi(\tau,\theta)$, Assumption 11.1, exercise price $p(\tau)$, and the optimal option-contract mechanism
-- statement:
--   This file defines the objects of the optimal sequential screening mechanism (§11.2.1, pp.214–218).
--
--   1. The **virtual valuation** (p.217)
--   $$\psi(\tau,\theta)=\theta+\frac{1-G(\tau)}{g(\tau)}\,\frac{\partial F(\theta\mid\tau)/\partial\tau}{f(\theta\mid\tau)} .$$
--   2. **Assumption 11.1**: $\psi(\tau,\theta)$ is increasing in $\tau$ and in $\theta$.
--   3. The **exercise price** $p(\tau)=\min\{\hat\theta\in[\underline\theta,\bar\theta]\mid\psi(\tau,\hat\theta)\ge0\}$.
--   4. For an allocation rule $q$ and a value $t(\underline\tau,\underline\theta)$, the constant of Proposition 11.5:
--   $$t_0(\tau)=t(\underline\tau,\underline\theta)-\underline\theta q(\underline\tau,\underline\theta)+\int_{\underline\tau}^{\tau}\!\int_{\underline\theta}^{\bar\theta}q(\hat\tau,\hat\theta)\frac{\partial F(\hat\theta\mid\hat\tau)}{\partial\tau}\,d\hat\theta\,d\hat\tau+\int_{\underline\theta}^{\bar\theta}\!\int_{\underline\theta}^{\hat\theta}\bigl[q(\tau,x)f(\hat\theta\mid\tau)-q(\underline\tau,x)f(\hat\theta\mid\underline\tau)\bigr]\,dx\,d\hat\theta .$$
--   5. The optimal mechanism: $q^*(\tau,\theta)=1$ if $\theta\ge p(\tau)$ and $0$ otherwise (11.10); $t^*(\tau,\theta)=t_0(\tau)+p(\tau)$ if $\theta\ge p(\tau)$ and $t_0(\tau)$ otherwise (11.11), where $t_0$ is item 4 for $q^*$ and the lowest-type payment
--   $$t(\underline\tau,\underline\theta)=\int_{p(\underline\tau)}^{\bar\theta}\hat\theta f(\hat\theta\mid\underline\tau)\,d\hat\theta-p(\underline\tau)\bigl[1-F(p(\underline\tau)\mid\underline\tau)\bigr]+\underline\theta q^*(\underline\tau,\underline\theta)\qquad(11.12).$$
--
--   The pair $(t_0(\tau),p(\tau))$ is the menu of option contracts that implements the optimal mechanism: a fee $t_0(\tau)$ now and an exercise price $p(\tau)$ later.
--
--   **Formalization Note** The page writes $\psi(\hat\theta,\tau)$ in the definition of $p$; the arguments are swapped there and are in the right order here. $p(\tau)$ is written as the infimum of the set, which equals its minimum whenever the minimum exists; the set contains $\bar\theta$ because $\partial F(\bar\theta\mid\tau)/\partial\tau=0$.
-- source:
--   Krähmer & Strausz, Ch. 11 in Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.214–218, Proposition 11.5 (t₀), Eq. (11.9)–(11.12), Assumption 11.1 (p.217)

import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model

/-!
# Virtual valuation, regularity and the optimal sequential screening mechanism
(Krähmer & Strausz, Ch. 11 in Börgers, §11.2.1, pp.214–218)
-/

namespace MechanismDesign.Dynamic

open MeasureTheory

variable {τlo τhi θlo θhi : ℝ}

/-- The **virtual valuation** (p.217):
`ψ(τ, θ) = θ + (1 − G(τ))/g(τ) · (∂F(θ|τ)/∂τ) / f(θ|τ)`. -/
noncomputable def SeqEnv.ψ (E : SeqEnv τlo τhi θlo θhi) (τ θ : ℝ) : ℝ :=
  θ + (1 - E.G τ) / E.g τ * (E.dFdτ θ τ / E.f θ τ)

/-- **Assumption 11.1** (p.217): `ψ(τ, θ)` is increasing (weakly) in `τ` and in `θ` on
`[τ̲, τ̄] × [θ̲, θ̄]`. -/
def SeqEnv.Assumption11_1 (E : SeqEnv τlo τhi θlo θhi) : Prop :=
  (∀ θ ∈ Set.Icc θlo θhi, MonotoneOn (fun τ => E.ψ τ θ) (Set.Icc τlo τhi)) ∧
  (∀ τ ∈ Set.Icc τlo τhi, MonotoneOn (fun θ => E.ψ τ θ) (Set.Icc θlo θhi))

/-- The **exercise price** (p.217): `p(τ) = min {θ̂ ∈ [θ̲, θ̄] | ψ(τ, θ̂) ≥ 0}`. (The page writes
`ψ(θ̂, τ)`, with the arguments swapped.) Written as an infimum, which equals the minimum
whenever the minimum exists; the set is nonempty because `ψ(τ, θ̄) = θ̄ > 0`. -/
noncomputable def SeqEnv.p (E : SeqEnv τlo τhi θlo θhi) (τ : ℝ) : ℝ :=
  sInf {θ | θ ∈ Set.Icc θlo θhi ∧ 0 ≤ E.ψ τ θ}

/-- The constant `t₀(τ)` of **Proposition 11.5** (p.214), for an allocation rule `q` and a
value `tlo` of the payment `t(τ̲, θ̲)` of the lowest type:
`t₀(τ) = t(τ̲, θ̲) − θ̲ q(τ̲, θ̲) + ∫_{τ̲}^{τ} ∫_{θ̲}^{θ̄} q(τ̂, θ̂) ∂F(θ̂|τ̂)/∂τ dθ̂ dτ̂`
`        + ∫_{θ̲}^{θ̄} ∫_{θ̲}^{θ̂} [q(τ, x) f(θ̂|τ) − q(τ̲, x) f(θ̂|τ̲)] dx dθ̂`. -/
noncomputable def SeqEnv.t0 (E : SeqEnv τlo τhi θlo θhi) (q : ℝ → ℝ → ℝ) (tlo τ : ℝ) : ℝ :=
  tlo - θlo * q τlo θlo +
    (∫ τ' in τlo..τ, ∫ θ' in θlo..θhi, q τ' θ' * E.dFdτ θ' τ') +
    ∫ θ' in θlo..θhi, ∫ x in θlo..θ', (q τ x * E.f θ' τ - q τlo x * E.f θ' τlo)

/-- The optimal allocation rule (11.10) (p.217): `q(τ, θ) = 1` if `θ ≥ p(τ)`, `0` otherwise. -/
noncomputable def SeqEnv.optQ (E : SeqEnv τlo τhi θlo θhi) (τ θ : ℝ) : ℝ :=
  if E.p τ ≤ θ then 1 else 0

/-- The payment of the lowest type in the optimal mechanism, (11.12) (p.218):
`t(τ̲, θ̲) = ∫_{p(τ̲)}^{θ̄} θ̂ f(θ̂|τ̲) dθ̂ − p(τ̲)[1 − F(p(τ̲)|τ̲)] + θ̲ q(τ̲, θ̲)`,
with `q` the optimal allocation rule (11.10). -/
noncomputable def SeqEnv.optTlo (E : SeqEnv τlo τhi θlo θhi) : ℝ :=
  (∫ θ' in E.p τlo..θhi, θ' * E.f θ' τlo) - E.p τlo * (1 - E.F (E.p τlo) τlo) +
    θlo * E.optQ τlo θlo

/-- The option fee `t₀(τ)` of the optimal mechanism: `t₀` of Proposition 11.5 for the allocation
rule (11.10) and the lowest-type payment (11.12). -/
noncomputable def SeqEnv.optT0 (E : SeqEnv τlo τhi θlo θhi) (τ : ℝ) : ℝ :=
  E.t0 E.optQ E.optTlo τ

/-- The optimal payment rule (11.11) (p.218): `t(τ, θ) = t₀(τ) + p(τ)` if `θ ≥ p(τ)`, and
`t₀(τ)` otherwise, with `t₀` as in `SeqEnv.optT0`. -/
noncomputable def SeqEnv.optT (E : SeqEnv τlo τhi θlo θhi) (τ θ : ℝ) : ℝ :=
  if E.p τ ≤ θ then E.optT0 τ + E.p τ else E.optT0 τ

end MechanismDesign.Dynamic


