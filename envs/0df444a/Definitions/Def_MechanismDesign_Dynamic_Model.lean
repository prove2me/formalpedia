-- Prove2me | Definitions.Def_MechanismDesign_Dynamic_Model
-- name    : MechanismDesign_Dynamic_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T05:38:07.715266+00:00
-- url     : https://prove2.me/theorems/fad8ef23-e22b-4d71-9a02-a6b994a050dd
-- title:
--   Sequential screening: ex ante and ex post types, dynamic direct mechanisms, incentive compatibility, individual rationality, revenue
-- statement:
--   This file sets up the sequential screening model of §11.2.1 of Krähmer and Strausz's chapter *Dynamic Mechanism Design* in Börgers' *An Introduction to the Theory of Mechanism Design*.
--
--   A seller offers one indivisible good to one buyer. Before contracting, the buyer privately observes her **ex ante type** $\tau\in[\underline\tau,\bar\tau]$, distributed with distribution function $G$ and density $g$. After accepting the seller's mechanism she privately observes her **ex post type** (her valuation) $\theta\in[\underline\theta,\bar\theta]$, distributed conditionally on $\tau$ with distribution function $F(\theta\mid\tau)$ and density $f(\theta\mid\tau)$. The standing assumptions (p.205) are:
--
--   1. $\underline\tau<\bar\tau$, $0\le\underline\theta<\bar\theta$, $g(\tau)>0$ and $f(\theta\mid\tau)>0$ on the rectangle, $G(\tau)=\int_{\underline\tau}^{\tau}g$, $F(\theta\mid\tau)=\int_{\underline\theta}^{\theta}f(x\mid\tau)\,dx$, both densities integrating to $1$;
--   2. $F(\theta\mid\tau)$ and $f(\theta\mid\tau)$ are continuously differentiable in $\tau$, and $|\partial F(\theta\mid\tau)/\partial\tau|<K$ for some $K>0$;
--   3. first-order stochastic dominance: $\partial F(\theta\mid\tau)/\partial\tau<0$ for all $\theta\in(\underline\theta,\bar\theta)$.
--
--   A (dynamic) **direct mechanism** (Definition 11.1) is a pair $q:[\underline\tau,\bar\tau]\times[\underline\theta,\bar\theta]\to[0,1]$, $t:[\underline\tau,\bar\tau]\times[\underline\theta,\bar\theta]\to\mathbb R$. With $u(\tau,\theta)=\theta q(\tau,\theta)-t(\tau,\theta)$,
--   $$\hat U(\tau'\mid\tau)=\int_{\underline\theta}^{\bar\theta}u(\tau',\hat\theta)f(\hat\theta\mid\tau)\,d\hat\theta,\qquad U(\tau)=\hat U(\tau\mid\tau).$$
--
--   1. The mechanism is **incentive-compatible** (Definition 11.2) if (i) $u(\tau,\theta)\ge\theta q(\tau,\theta')-t(\tau,\theta')$ for all $\tau$ and $\theta,\theta'$ (Eq. (11.1)), and (ii) for all $\tau,\tau'$ and every reporting function $\theta_r:[\underline\theta,\bar\theta]\to[\underline\theta,\bar\theta]$,
--   $$U(\tau)\ge\int_{\underline\theta}^{\bar\theta}\bigl[\hat\theta q(\tau',\theta_r(\hat\theta))-t(\tau',\theta_r(\hat\theta))\bigr]f(\hat\theta\mid\tau)\,d\hat\theta .$$
--   2. It is **individually rational** (Definition 11.3) if $U(\tau)\ge0$ for all $\tau$.
--   3. The seller's **expected revenue** is $\int\!\!\int t(\tau,\theta)f(\theta\mid\tau)g(\tau)\,d\theta\,d\tau$, and a mechanism is **optimal** if it is incentive-compatible and individually rational and no other such mechanism has larger expected revenue.
--   4. A general **dynamic mechanism** is represented in reduced form: the buyer chooses $a_1\in A_1$ before learning $\theta$ and $a_2\in A_2$ after, and each pair yields a purchase probability and an expected payment. A buyer strategy $\sigma=(\sigma_1,\sigma_2)$, with $\sigma_2$ depending on $\tau$, $\theta$ and the first-stage choice, is **optimal** if $\sigma_2$ is a best second-stage choice after every first-stage choice and $\sigma_1(\tau)$ maximizes the resulting expected utility.
--
--   These objects are the vocabulary of every result of §11.2: the dynamic revelation principle, the characterization of incentive compatibility, the envelope formula in $\tau$ and the optimal sequential screening mechanism.
--
--   **Formalization Note** $F(\theta\mid\tau)$ is `F θ τ` and $q(\tau,\theta)$ is `q τ θ`. Functions are total on $\mathbb R$ or $\mathbb R^2$; every condition quantifies over the type intervals only. The book omits measurability (Börgers, Ch. 2, note 2): here the densities are jointly measurable, a mechanism is *admissible* when $q$, $t$ are measurable on the rectangle, and the reporting functions $\theta_r$ in Definition 11.2(ii) are measurable. Revenue is the integral of $t$ against the joint law with density $g(\tau)f(\theta\mid\tau)$. A direct mechanism is a dynamic mechanism with $A_1=[\underline\tau,\bar\tau]$, $A_2=[\underline\theta,\bar\theta]$.
-- source:
--   Krähmer & Strausz, Ch. 11 in Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.205–209, §11.2.1, standing assumptions (p.205), Definitions 11.1–11.3

import Mathlib

/-!
# Sequential screening (Krähmer & Strausz, Ch. 11 in Börgers, §11.2.1, pp.205–209)

A seller offers one indivisible good to one buyer. Before contracting the buyer privately
observes her **ex ante type** `τ ∈ [τ̲, τ̄]` (`τlo`, `τhi`), distributed with cumulative
distribution function `G` and density `g > 0`. After accepting the mechanism she privately
observes her **ex post type** (her valuation) `θ ∈ [θ̲, θ̄]` (`θlo`, `θhi`), `0 ≤ θ̲ < θ̄`,
distributed conditionally on `τ` with cumulative distribution function `F(θ|τ)` and density
`f(θ|τ) > 0` (p.205).

Conventions.
* `F θ τ` is `F(θ|τ)`, `f θ τ` is `f(θ|τ)`, and `dFdτ θ τ` is `∂F(θ|τ)/∂τ` (argument order as
  printed). A direct mechanism's `q τ θ`, `t τ θ` are `q(τ, θ)`, `t(τ, θ)`.
* All functions are total functions on `ℝ` (or `ℝ × ℝ`); only their values on `[τ̲, τ̄]` and
  `[θ̲, θ̄]` matter, and every condition quantifies over these intervals only.
* The book omits measurability throughout (Börgers, Ch. 2 note 2, p.235). It is added here:
  the densities are jointly measurable, a direct mechanism is *admissible* when `q` and `t` are
  measurable on the rectangle `[τ̲, τ̄] × [θ̲, θ̄]`, and the reporting functions of
  Definition 11.2(ii) are measurable.
-/

namespace MechanismDesign.Dynamic

open MeasureTheory

/-- The environment of sequential screening, with the standing assumptions of p.205:

* `g > 0` on `[τ̲, τ̄]` is a probability density with distribution function `G`;
* for every `τ ∈ [τ̲, τ̄]`, `f(·|τ) > 0` on `[θ̲, θ̄]` is a probability density with
  distribution function `F(·|τ)` (common support `[θ̲, θ̄]`, `0 ≤ θ̲ < θ̄`);
* `F(θ|τ)` and `f(θ|τ)` are continuously differentiable in `τ` on `[τ̲, τ̄]`, with derivatives
  `dFdτ`, `dfdτ`, and `|∂F(θ|τ)/∂τ| < K` for some `K > 0`;
* first-order stochastic dominance: `∂F(θ|τ)/∂τ < 0` for all `θ ∈ (θ̲, θ̄)`. -/
structure SeqEnv (τlo τhi θlo θhi : ℝ) where
  /-- Distribution function `G` of the ex ante type. -/
  G : ℝ → ℝ
  /-- Density `g` of the ex ante type. -/
  g : ℝ → ℝ
  /-- `F θ τ = F(θ|τ)`, the conditional distribution function of the ex post type. -/
  F : ℝ → ℝ → ℝ
  /-- `f θ τ = f(θ|τ)`, the conditional density of the ex post type. -/
  f : ℝ → ℝ → ℝ
  /-- `dFdτ θ τ = ∂F(θ|τ)/∂τ`. -/
  dFdτ : ℝ → ℝ → ℝ
  /-- `dfdτ θ τ = ∂f(θ|τ)/∂τ`. -/
  dfdτ : ℝ → ℝ → ℝ
  /-- The bound `K` on `|∂F(θ|τ)/∂τ|`. -/
  K : ℝ
  τlo_lt_τhi : τlo < τhi
  θlo_nonneg : 0 ≤ θlo
  θlo_lt_θhi : θlo < θhi
  /-- `g(τ) > 0` on `[τ̲, τ̄]`. -/
  g_pos : ∀ τ ∈ Set.Icc τlo τhi, 0 < g τ
  g_measurable : Measurable g
  g_integrable : IntervalIntegrable g volume τlo τhi
  g_total : ∫ τ in τlo..τhi, g τ = 1
  /-- `G(τ) = ∫_{τ̲}^{τ} g`. -/
  G_eq : ∀ τ ∈ Set.Icc τlo τhi, G τ = ∫ x in τlo..τ, g x
  /-- `f(θ|τ) > 0` for all `θ ∈ [θ̲, θ̄]`, `τ ∈ [τ̲, τ̄]`. -/
  f_pos : ∀ θ ∈ Set.Icc θlo θhi, ∀ τ ∈ Set.Icc τlo τhi, 0 < f θ τ
  /-- `(τ, θ) ↦ f(θ|τ)` is jointly measurable. -/
  f_measurable : Measurable fun p : ℝ × ℝ => f p.2 p.1
  f_integrable : ∀ τ ∈ Set.Icc τlo τhi, IntervalIntegrable (fun θ => f θ τ) volume θlo θhi
  f_total : ∀ τ ∈ Set.Icc τlo τhi, ∫ θ in θlo..θhi, f θ τ = 1
  /-- `F(θ|τ) = ∫_{θ̲}^{θ} f(x|τ) dx`. -/
  F_eq : ∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi, F θ τ = ∫ x in θlo..θ, f x τ
  /-- `τ ↦ F(θ|τ)` has derivative `∂F(θ|τ)/∂τ` on `[τ̲, τ̄]`. -/
  hasDerivWithinAt_F : ∀ θ ∈ Set.Icc θlo θhi, ∀ τ ∈ Set.Icc τlo τhi,
    HasDerivWithinAt (fun s => F θ s) (dFdτ θ τ) (Set.Icc τlo τhi) τ
  /-- `∂F(θ|τ)/∂τ` is continuous in `τ`. -/
  continuousOn_dFdτ : ∀ θ ∈ Set.Icc θlo θhi, ContinuousOn (fun s => dFdτ θ s) (Set.Icc τlo τhi)
  /-- `(τ, θ) ↦ ∂F(θ|τ)/∂τ` is jointly measurable. -/
  dFdτ_measurable : Measurable fun p : ℝ × ℝ => dFdτ p.2 p.1
  /-- `τ ↦ f(θ|τ)` has derivative `∂f(θ|τ)/∂τ` on `[τ̲, τ̄]`. -/
  hasDerivWithinAt_f : ∀ θ ∈ Set.Icc θlo θhi, ∀ τ ∈ Set.Icc τlo τhi,
    HasDerivWithinAt (fun s => f θ s) (dfdτ θ τ) (Set.Icc τlo τhi) τ
  /-- `∂f(θ|τ)/∂τ` is continuous in `τ`. -/
  continuousOn_dfdτ : ∀ θ ∈ Set.Icc θlo θhi, ContinuousOn (fun s => dfdτ θ s) (Set.Icc τlo τhi)
  K_pos : 0 < K
  /-- `|∂F(θ|τ)/∂τ| < K`. -/
  abs_dFdτ_lt : ∀ θ ∈ Set.Icc θlo θhi, ∀ τ ∈ Set.Icc τlo τhi, |dFdτ θ τ| < K
  /-- First-order stochastic dominance: `∂F(θ|τ)/∂τ < 0` for `θ ∈ (θ̲, θ̄)`. -/
  fosd : ∀ θ ∈ Set.Ioo θlo θhi, ∀ τ ∈ Set.Icc τlo τhi, dFdτ θ τ < 0

variable {τlo τhi θlo θhi : ℝ}

/-- The type rectangle `[τ̲, τ̄] × [θ̲, θ̄]`, as a set of pairs `(τ, θ)`. -/
def typeRect (τlo τhi θlo θhi : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc τlo τhi ×ˢ Set.Icc θlo θhi

/-- The joint distribution of `(τ, θ)`: density `g(τ) f(θ|τ)` on `[τ̲, τ̄] × [θ̲, θ̄]`. -/
noncomputable def SeqEnv.jointLaw (E : SeqEnv τlo τhi θlo θhi) : Measure (ℝ × ℝ) :=
  (volume.restrict (typeRect τlo τhi θlo θhi)).withDensity
    fun p => ENNReal.ofReal (E.g p.1 * E.f p.2 p.1)

/-- A (dynamic) **direct mechanism** (Definition 11.1, p.206): a purchase probability `q(τ, θ)`
and a payment `t(τ, θ)` as functions of the reported ex ante type `τ` and ex post type `θ`. -/
structure DirectMechanism (τlo τhi θlo θhi : ℝ) where
  /-- `q τ θ = q(τ, θ)`. -/
  q : ℝ → ℝ → ℝ
  /-- `t τ θ = t(τ, θ)`. -/
  t : ℝ → ℝ → ℝ

namespace DirectMechanism

/-- Admissibility: `q` maps `[τ̲, τ̄] × [θ̲, θ̄]` into `[0, 1]` (Definition 11.1), and `q`, `t`
are measurable on the rectangle (the measurability the book omits, Ch. 2 note 2). -/
def Admissible (m : DirectMechanism τlo τhi θlo θhi) : Prop :=
  (∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi, m.q τ θ ∈ Set.Icc (0 : ℝ) 1) ∧
  Measurable (fun p : Set.Icc τlo τhi × Set.Icc θlo θhi => m.q p.1 p.2) ∧
  Measurable (fun p : Set.Icc τlo τhi × Set.Icc θlo θhi => m.t p.1 p.2)

/-- `u(τ, θ) = θ q(τ, θ) − t(τ, θ)` (p.208). -/
def u (m : DirectMechanism τlo τhi θlo θhi) (τ θ : ℝ) : ℝ :=
  θ * m.q τ θ - m.t τ θ

/-- `Û(τ′|τ) = ∫_{θ̲}^{θ̄} u(τ′, θ̂) f(θ̂|τ) dθ̂` (p.208): the expected utility of ex ante type
`τ` who reports `τ′` and then reports her ex post type truthfully. Argument order:
`Uhat E m τ' τ = Û(τ′|τ)`. -/
noncomputable def Uhat (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (τ' τ : ℝ) : ℝ :=
  ∫ θ in θlo..θhi, m.u τ' θ * E.f θ τ

/-- `U(τ) = Û(τ|τ)` (p.208). -/
noncomputable def U (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (τ : ℝ) : ℝ :=
  m.Uhat E τ τ

/-- **Incentive compatibility with respect to the ex post type** (Definition 11.2(i), Eq. (11.1),
p.208): `u(τ, θ) ≥ θ q(τ, θ′) − t(τ, θ′)` for all `τ ∈ [τ̲, τ̄]` and `θ, θ′ ∈ [θ̲, θ̄]`. -/
def IsExPostIC (m : DirectMechanism τlo τhi θlo θhi) : Prop :=
  ∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi, ∀ θ' ∈ Set.Icc θlo θhi,
    θ * m.q τ θ' - m.t τ θ' ≤ m.u τ θ

/-- **Incentive compatibility with respect to the ex ante type** (Definition 11.2(ii), p.208):
for all `τ, τ′ ∈ [τ̲, τ̄]` and every (measurable) reporting function
`θ_r : [θ̲, θ̄] → [θ̲, θ̄]`,
`U(τ) ≥ ∫_{θ̲}^{θ̄} [θ̂ q(τ′, θ_r(θ̂)) − t(τ′, θ_r(θ̂))] f(θ̂|τ) dθ̂`. -/
def IsExAnteIC (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi) : Prop :=
  ∀ τ ∈ Set.Icc τlo τhi, ∀ τ' ∈ Set.Icc τlo τhi, ∀ θr : ℝ → ℝ, Measurable θr →
    (∀ θ ∈ Set.Icc θlo θhi, θr θ ∈ Set.Icc θlo θhi) →
    ∫ θ in θlo..θhi, (θ * m.q τ' (θr θ) - m.t τ' (θr θ)) * E.f θ τ ≤ m.U E τ

/-- **Incentive compatibility** (Definition 11.2, p.208): both parts (i) and (ii). -/
def IsIC (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi) : Prop :=
  m.IsExPostIC ∧ m.IsExAnteIC E

/-- **Individual rationality** (Definition 11.3, p.209): `U(τ) ≥ 0` for all `τ ∈ [τ̲, τ̄]`. -/
def IsIR (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi) : Prop :=
  ∀ τ ∈ Set.Icc τlo τhi, 0 ≤ m.U E τ

/-- The seller's expected revenue
`∫_{τ̲}^{τ̄} ∫_{θ̲}^{θ̄} t(τ, θ) f(θ|τ) g(τ) dθ dτ`, written as an integral against the joint
distribution of `(τ, θ)`. -/
noncomputable def revenue (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi) :
    ℝ :=
  ∫ p, m.t p.1 p.2 ∂E.jointLaw

/-- An **optimal** direct mechanism: admissible, incentive-compatible and individually rational,
and its expected revenue is at least that of every admissible, incentive-compatible and
individually rational direct mechanism. -/
def IsOptimal (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi) : Prop :=
  m.Admissible ∧ m.IsIC E ∧ m.IsIR E ∧
    ∀ m' : DirectMechanism τlo τhi θlo θhi, m'.Admissible → m'.IsIC E → m'.IsIR E →
      m'.revenue E ≤ m.revenue E

end DirectMechanism

/-- A general (not necessarily direct) **dynamic mechanism**, in reduced form (p.207). The seller
commits to a game form and to her own (possibly randomized) behaviour in it. The buyer acts at
two stages: before learning `θ` she chooses `a₁ ∈ A₁` (a plan for everything she does before
`θ` arrives), and after learning `θ` she chooses `a₂ ∈ A₂` (a plan for the rest of the game).
Each pair `(a₁, a₂)` results in a probability of purchase `prob a₁ a₂` and an expected payment
`pay a₁ a₂`. -/
structure DynMechanism where
  /-- The buyer's first-stage choices. -/
  A₁ : Type
  /-- The buyer's second-stage choices. -/
  A₂ : Type
  /-- The probability of purchase. -/
  prob : A₁ → A₂ → ℝ
  /-- The expected payment. -/
  pay : A₁ → A₂ → ℝ

/-- Purchase probabilities of a dynamic mechanism lie in `[0, 1]`. -/
def DynMechanism.Valid (Γ : DynMechanism) : Prop :=
  ∀ a₁ a₂, Γ.prob a₁ a₂ ∈ Set.Icc (0 : ℝ) 1

/-- `σ = (σ₁, σ₂)` is an **optimal buyer strategy** in `Γ` (pp.206–207): `σ₁(τ)` is the
first-stage choice of ex ante type `τ`, and `σ₂(τ, θ, a₁)` the second-stage choice of type
`(τ, θ)` after first-stage choice `a₁`. Optimality is sequential:

1. after every first-stage choice `a₁`, `σ₂(τ, θ, a₁)` maximizes
   `θ · prob(a₁, a₂) − pay(a₁, a₂)` over `a₂ ∈ A₂`;
2. `σ₁(τ)` maximizes the resulting expected utility
   `∫_{θ̲}^{θ̄} [θ · prob(a₁, σ₂(τ, θ, a₁)) − pay(a₁, σ₂(τ, θ, a₁))] f(θ|τ) dθ` over `a₁ ∈ A₁`. -/
def DynMechanism.IsOptimalStrategy (E : SeqEnv τlo τhi θlo θhi) (Γ : DynMechanism)
    (σ₁ : ℝ → Γ.A₁) (σ₂ : ℝ → ℝ → Γ.A₁ → Γ.A₂) : Prop :=
  (∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi, ∀ a₁ : Γ.A₁, ∀ a₂ : Γ.A₂,
    θ * Γ.prob a₁ a₂ - Γ.pay a₁ a₂ ≤ θ * Γ.prob a₁ (σ₂ τ θ a₁) - Γ.pay a₁ (σ₂ τ θ a₁)) ∧
  (∀ τ ∈ Set.Icc τlo τhi, ∀ a₁ : Γ.A₁,
    ∫ θ in θlo..θhi, (θ * Γ.prob a₁ (σ₂ τ θ a₁) - Γ.pay a₁ (σ₂ τ θ a₁)) * E.f θ τ ≤
      ∫ θ in θlo..θhi,
        (θ * Γ.prob (σ₁ τ) (σ₂ τ θ (σ₁ τ)) - Γ.pay (σ₁ τ) (σ₂ τ θ (σ₁ τ))) * E.f θ τ)

/-- A direct mechanism viewed as a dynamic mechanism: the buyer first reports `τ ∈ [τ̲, τ̄]`,
then reports `θ ∈ [θ̲, θ̄]`. -/
def DirectMechanism.toDyn (m : DirectMechanism τlo τhi θlo θhi) : DynMechanism where
  A₁ := Set.Icc τlo τhi
  A₂ := Set.Icc θlo θhi
  prob a₁ a₂ := m.q a₁ a₂
  pay a₁ a₂ := m.t a₁ a₂

end MechanismDesign.Dynamic


