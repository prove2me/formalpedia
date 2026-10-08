-- Prove2me | Definitions.Def_MechanismDesign_Dynamic_ObservableGamma
-- name    : MechanismDesign_Dynamic_ObservableGamma
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T05:52:48.049847+00:00
-- url     : https://prove2.me/theorems/c3254f61-3bfe-4ac3-be40-8edb3c9e74fe
-- title:
--   The additional information $\gamma=F(\theta\mid\tau)$: mechanisms $(\tilde q,\tilde t)$, incentive compatibility with observable $\gamma$, private versus public optimality
-- statement:
--   This file sets up §11.2.2 (pp.219–223). The buyer's ex post information is re-expressed as $\gamma=F(\theta\mid\tau)\in[0,1]$, which is uniformly distributed and independent of $\tau$; the valuation is $\theta=F^{-1}(\gamma\mid\tau)$. A mechanism in this representation is a pair $(\tilde q(\tau,\gamma),\tilde t(\tau,\gamma))$.
--
--   1. When $\gamma$ is **publicly observable**, ex ante type $\tau$ reporting $\tau'$ obtains $\int_0^1[F^{-1}(\gamma\mid\tau)\tilde q(\tau',\gamma)-\tilde t(\tau',\gamma)]\,d\gamma$, and $U(\tau)$ is this with $\tau'=\tau$. The mechanism is **incentive-compatible with observable $\gamma$** (p.221) if
--   $$U(\tau)\ge\int_0^1\bigl[F^{-1}(\gamma\mid\tau)\tilde q(\tau',\gamma)-\tilde t(\tau',\gamma)\bigr]\,d\gamma\quad\text{for all }\tau,\tau'\in[\underline\tau,\bar\tau],$$
--   individually rational if $U(\tau)\ge0$ for all $\tau$, and **optimal when $\gamma$ is publicly observable** if it maximizes the expected revenue $\int_{\underline\tau}^{\bar\tau}\int_0^1\tilde t(\tau,\gamma)g(\tau)\,d\gamma\,d\tau$ among such mechanisms.
--   2. When $\gamma$ is **privately observable**, the model is the sequential screening model in the coordinates $\theta=F^{-1}(\gamma\mid\tau)$ (pp.219–220): $(\tilde q,\tilde t)$ is **optimal when $\gamma$ is privately observable** if the direct mechanism $q(\tau,\theta)=\tilde q(\tau,F(\theta\mid\tau))$, $t(\tau,\theta)=\tilde t(\tau,F(\theta\mid\tau))$ is optimal in the sequential screening model.
--   3. The regularity used on pp.217–221: $f(\theta\mid\tau)$ and $\partial F(\theta\mid\tau)/\partial\tau$ are continuous in $(\tau,\theta)$.
--
--   **Formalization Note** $F^{-1}(\gamma\mid\tau)$ is written as $\inf\{\theta\in[\underline\theta,\bar\theta]\mid F(\theta\mid\tau)\ge\gamma\}$, which is the inverse of $\theta\mapsto F(\theta\mid\tau)$ for $\gamma\in[0,1]$. Admissibility adds measurability of $\tilde q$, $\tilde t$ on $[\underline\tau,\bar\tau]\times[0,1]$ and integrability of $\gamma\mapsto\tilde t(\tau,\gamma)$ on $[0,1]$ for every $\tau$, so that the expected utilities above are genuine integrals (without it a non-integrable $\tilde t$ would make every utility $0$ and incentive compatibility vacuous). The continuity condition of item 3 is what the book invokes on p.217 ("Our assumptions guarantee that $\psi(\tau,\theta)$ is continuous") and needs on pp.220–221 to differentiate $F^{-1}(\gamma\mid\tau)$ in $\tau$.
-- source:
--   Krähmer & Strausz, Ch. 11 in Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.219–223, §11.2.2 (incentive compatibility with observable γ, p.221)

import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model

/-!
# The additional information `γ = F(θ|τ)`, private or public
(Krähmer & Strausz, Ch. 11 in Börgers, §11.2.2, pp.219–223)

The buyer's ex post information is re-expressed as `γ = F(θ|τ) ∈ [0, 1]`, which is uniformly
distributed and independent of `τ`; the valuation is recovered as `θ = F⁻¹(γ|τ)`. A mechanism in
this representation is a pair `(q̃(τ, γ), t̃(τ, γ))`.
-/

namespace MechanismDesign.Dynamic

open MeasureTheory

variable {τlo τhi θlo θhi : ℝ}

/-- `F⁻¹(γ|τ)` (p.219): the inverse of the strictly increasing map `θ ↦ F(θ|τ)` from
`[θ̲, θ̄]` onto `[0, 1]`, written as `inf {θ ∈ [θ̲, θ̄] | F(θ|τ) ≥ γ}`, which is the inverse for
`γ ∈ [0, 1]`. -/
noncomputable def SeqEnv.Finv (E : SeqEnv τlo τhi θlo θhi) (γ τ : ℝ) : ℝ :=
  sInf {θ | θ ∈ Set.Icc θlo θhi ∧ γ ≤ E.F θ τ}

/-- Continuity of the densities, which the book invokes on p.217 ("Our assumptions guarantee
that `ψ(τ, θ)` is continuous in `(τ, θ)`") and uses on pp.220–221 to differentiate
`F⁻¹(γ|τ)` in `τ`: `(τ, θ) ↦ f(θ|τ)` and `(τ, θ) ↦ ∂F(θ|τ)/∂τ` are continuous on
`[τ̲, τ̄] × [θ̲, θ̄]`. -/
def SeqEnv.ContinuousDensities (E : SeqEnv τlo τhi θlo θhi) : Prop :=
  ContinuousOn (fun p : ℝ × ℝ => E.f p.2 p.1) (typeRect τlo τhi θlo θhi) ∧
  ContinuousOn (fun p : ℝ × ℝ => E.dFdτ p.2 p.1) (typeRect τlo τhi θlo θhi)

/-- A direct mechanism in the `(τ, γ)` representation (p.219): `q̃ τ γ = q̃(τ, γ)`,
`t̃ τ γ = t̃(τ, γ)`. -/
structure GammaMechanism (τlo τhi : ℝ) where
  /-- `q̃ τ γ = q̃(τ, γ)`. -/
  q : ℝ → ℝ → ℝ
  /-- `t̃ τ γ = t̃(τ, γ)`. -/
  t : ℝ → ℝ → ℝ

namespace GammaMechanism

/-- Admissibility: `q̃` maps `[τ̲, τ̄] × [0, 1]` into `[0, 1]`, `q̃`, `t̃` are measurable on
that rectangle, and for every `τ` the payment `γ ↦ t̃(τ, γ)` is integrable on `[0, 1]`, so that
the expected utilities `∫_0^1 [F⁻¹(γ|τ) q̃(τ′, γ) − t̃(τ′, γ)] dγ` of p.221 are defined (the
measurability and integrability the book omits, Ch. 2 note 2). -/
def Admissible (m : GammaMechanism τlo τhi) : Prop :=
  (∀ τ ∈ Set.Icc τlo τhi, ∀ γ ∈ Set.Icc (0 : ℝ) 1, m.q τ γ ∈ Set.Icc (0 : ℝ) 1) ∧
  Measurable (fun p : Set.Icc τlo τhi × Set.Icc (0 : ℝ) 1 => m.q p.1 p.2) ∧
  Measurable (fun p : Set.Icc τlo τhi × Set.Icc (0 : ℝ) 1 => m.t p.1 p.2) ∧
  ∀ τ ∈ Set.Icc τlo τhi, IntervalIntegrable (m.t τ) volume 0 1

/-- The expected utility of ex ante type `τ` who reports `τ′` when `γ` is publicly observed:
`∫_0^1 [F⁻¹(γ|τ) q̃(τ′, γ) − t̃(τ′, γ)] dγ` (p.221). -/
noncomputable def UobsReport (E : SeqEnv τlo τhi θlo θhi) (m : GammaMechanism τlo τhi)
    (τ' τ : ℝ) : ℝ :=
  ∫ γ in (0 : ℝ)..1, (E.Finv γ τ * m.q τ' γ - m.t τ' γ)

/-- `U(τ) = ∫_0^1 [F⁻¹(γ|τ) q̃(τ, γ) − t̃(τ, γ)] dγ` (p.221). -/
noncomputable def Uobs (E : SeqEnv τlo τhi θlo θhi) (m : GammaMechanism τlo τhi) (τ : ℝ) : ℝ :=
  m.UobsReport E τ τ

/-- **Incentive-compatible with observable `γ`** (p.221): for all `τ, τ′ ∈ [τ̲, τ̄]`,
`U(τ) ≥ ∫_0^1 [F⁻¹(γ|τ) q̃(τ′, γ) − t̃(τ′, γ)] dγ`. -/
def IsICObs (E : SeqEnv τlo τhi θlo θhi) (m : GammaMechanism τlo τhi) : Prop :=
  ∀ τ ∈ Set.Icc τlo τhi, ∀ τ' ∈ Set.Icc τlo τhi, m.UobsReport E τ' τ ≤ m.Uobs E τ

/-- Individual rationality with observable `γ`: `U(τ) ≥ 0` for all `τ ∈ [τ̲, τ̄]`. -/
def IsIRObs (E : SeqEnv τlo τhi θlo θhi) (m : GammaMechanism τlo τhi) : Prop :=
  ∀ τ ∈ Set.Icc τlo τhi, 0 ≤ m.Uobs E τ

/-- The joint distribution of `(τ, γ)`: density `g(τ)` on `[τ̲, τ̄] × [0, 1]` (`γ` is uniform
on `[0, 1]` and independent of `τ`, p.219). -/
noncomputable def lawObs (E : SeqEnv τlo τhi θlo θhi) : Measure (ℝ × ℝ) :=
  (volume.restrict (Set.Icc τlo τhi ×ˢ Set.Icc (0 : ℝ) 1)).withDensity
    fun p => ENNReal.ofReal (E.g p.1)

/-- The seller's expected revenue `∫_{τ̲}^{τ̄} ∫_0^1 t̃(τ, γ) g(τ) dγ dτ`. -/
noncomputable def revenueObs (E : SeqEnv τlo τhi θlo θhi) (m : GammaMechanism τlo τhi) : ℝ :=
  ∫ p, m.t p.1 p.2 ∂lawObs E

/-- **Optimal when `γ` is publicly observable**: admissible, incentive-compatible with
observable `γ`, individually rational, and of maximal expected revenue among all such
mechanisms. -/
def IsOptimalPublic (E : SeqEnv τlo τhi θlo θhi) (m : GammaMechanism τlo τhi) : Prop :=
  m.Admissible ∧ m.IsICObs E ∧ m.IsIRObs E ∧
    ∀ m' : GammaMechanism τlo τhi, m'.Admissible → m'.IsICObs E → m'.IsIRObs E →
      m'.revenueObs E ≤ m.revenueObs E

/-- The `(τ, θ)` direct mechanism corresponding to `(q̃, t̃)` (pp.219–220):
`q(τ, θ) = q̃(τ, F(θ|τ))`, `t(τ, θ) = t̃(τ, F(θ|τ))`. -/
def toTheta (E : SeqEnv τlo τhi θlo θhi) (m : GammaMechanism τlo τhi) :
    DirectMechanism τlo τhi θlo θhi where
  q τ θ := m.q τ (E.F θ τ)
  t τ θ := m.t τ (E.F θ τ)

/-- **Optimal when `γ` is privately observable** (pp.219–220): the buyer privately learns `γ`
after contracting, which is the sequential screening model of §11.2.1 in the coordinates
`θ = F⁻¹(γ|τ)`; `(q̃, t̃)` is optimal when the corresponding `(τ, θ)` direct mechanism is
optimal in the sequential screening model. -/
def IsOptimalPrivate (E : SeqEnv τlo τhi θlo θhi) (m : GammaMechanism τlo τhi) : Prop :=
  (m.toTheta E).IsOptimal E

end GammaMechanism

end MechanismDesign.Dynamic


