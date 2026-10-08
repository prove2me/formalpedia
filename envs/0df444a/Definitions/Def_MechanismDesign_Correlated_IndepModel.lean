-- Prove2me | Definitions.Def_MechanismDesign_Correlated_IndepModel
-- name    : MechanismDesign_Correlated_IndepModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T02:29:14.40634+00:00
-- url     : https://prove2.me/theorems/852cb4ff-3fed-47da-bf35-84313c9f8405
-- title:
--   Bayesian mechanism design with independent types (Börgers §6.2–6.3): prior, direct mechanisms, interim rules, BIC, cyclical monotonicity, budget balance, equivalence
-- statement:
--   This file sets up the Bayesian mechanism design model of Börgers, §6.2, in the special case of independent types treated in §6.3.
--
--   **Environment.** A finite set $I$ of agents chooses an alternative $a$ from a set $A$ (a measurable space). Agent $i$ has a type $\theta_i$ in a type set $\Theta_i$ (an abstract measurable space) and utility $u_i(a,\theta_i) - t_i$ from alternative $a$ and payment $t_i$. Write $\Theta = \Theta_1 \times \dots \times \Theta_N$ and $\theta_{-i}$ for the types of the agents other than $i$. Types are **independent** (Definition 6.1): the conditional distribution $\mu(\cdot \mid \theta_i)$ of $\theta_{-i}$ given $\theta_i$ is the same for every $\theta_i$. Equivalently, the common prior is a product
--   $$\mu = \rho_1 \otimes \rho_2 \otimes \dots \otimes \rho_N$$
--   of probability measures $\rho_i$ on the $\Theta_i$, and this is how the prior is given.
--
--   1. A **direct mechanism** $(q, t_1, \dots, t_N)$ (Definition 6.2) consists of a decision rule $q : \Theta \to A$ and payment rules $t_i : \Theta \to \mathbb R$.
--   2. The **interim decision rule** $Q_i(\theta_i)$ (6.1) is the distribution on $A$ of $q(\theta_i, \theta_{-i})$ when $\theta_{-i}$ is drawn from $\mu(\cdot \mid \theta_i)$; the **interim expected payment** (6.2) is $T_i(\theta_i) = \int_{\Theta_{-i}} t_i(\theta_i,\theta_{-i})\,d\mu(\theta_{-i}\mid\theta_i)$.
--   3. A direct mechanism is **Bayesian incentive-compatible** (Definition 6.3) if for all $i$ and all $\theta_i, \theta_i' \in \Theta_i$
--   $$\int_{\Theta_{-i}} u_i(q(\theta_i,\theta_{-i}),\theta_i) - t_i(\theta_i,\theta_{-i})\,d\mu(\theta_{-i}\mid\theta_i) \ \ge\ \int_{\Theta_{-i}} u_i(q(\theta_i',\theta_{-i}),\theta_i) - t_i(\theta_i',\theta_{-i})\,d\mu(\theta_{-i}\mid\theta_i).$$
--   4. A decision rule is **interim cyclically monotone** (Proposition 6.1) if for every $i$ and every sequence $(\theta_i^1, \dots, \theta_i^k)$ of types of agent $i$ with $\theta_i^k = \theta_i^1$,
--   $$\sum_{\kappa=1}^{k-1}\left(\int_A u_i(a,\theta_i^{\kappa+1})\,dQ_i(\theta_i^\kappa) - \int_A u_i(a,\theta_i^\kappa)\,dQ_i(\theta_i^\kappa)\right) \le 0.$$
--   5. **Ex post budget balance** (Definition 6.5): $\sum_{i\in I} t_i(\theta) = 0$ for every $\theta\in\Theta$. **Ex ante budget balance** (Definition 6.6): $\int_\Theta \sum_{i=1}^N t_i(\theta)\,d\mu(\theta) = 0$.
--   6. Two direct mechanisms are **equivalent** (p.118) if they have the same decision rule and, for every agent $i$ and all $\theta_i, \theta_i'$, agent $i$'s expected payment conditional on type $\theta_i$ and report $\theta_i'$ is the same in both. With independent types this expected payment is $T_i(\theta_i')$ whatever $\theta_i$ is, so equivalence means equal decision rules and equal interim payment rules $T_i$.
--
--   These are the objects of Propositions 6.1–6.3.
--
--   **Formalization Note** Agents are a finite type `ι`. An integral over $\Theta_{-i}$ against $\mu(\cdot\mid\theta_i)$ of a function of $(\theta_i', \theta_{-i})$ is written as the integral over the whole product prior of the function evaluated at the type vector with coordinate $i$ overwritten by $\theta_i'$ (`Function.update θ i θi'`); since $\rho_i$ is a probability measure this is the same integral. The book omits measurability throughout (note 2 to Ch. 2, p.235); it is made explicit here as small side conditions under which the interim quantities are genuine integrals: `IsDecisionRule` (the decision rule is measurable and each $u_i(\cdot,\theta_i)$ is integrable against each $Q_i(\theta_i')$), `IsTransferRule` (each $\theta_{-i}\mapsto t_i(\theta_i',\theta_{-i})$ is integrable), and, inside `IsExAnteBB`, integrability of each $t_i$ against $\mu$.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.114–118, §6.2–6.3: setup p.114; Definition 6.1 p.114; Definitions 6.2, 6.3, 6.5 p.115; (6.1), (6.2) and interim cyclical monotonicity (Proposition 6.1) p.116; Definition 6.6 and "equivalent" p.118

import Mathlib

namespace MechanismDesign.Correlated

open MeasureTheory

namespace Indep

/-!
Bayesian mechanism design with independent types (Börgers, *An Introduction to the Theory of
Mechanism Design*, §6.2–6.3, pp.114–118).

Agents form a finite set `ι`; agent `i`'s type set `Θ i` is an abstract measurable space, and the
alternatives form a measurable space `A`. Agent `i`'s utility from alternative `a` and transfer `t`
is `u i a θᵢ - t`. Types are independent (Definition 6.1): the common prior is the product
`Measure.pi ρ` of probability measures `ρ i` on the `Θ i`, so that the conditional distribution of
`θ₋ᵢ` given `θᵢ` is the same for every `θᵢ`. An integral over `Θ₋ᵢ` against that conditional
distribution of a function of `(y, θ₋ᵢ)` is written as the integral over the whole prior of the
function evaluated at `Function.update θ i y` (which does not depend on `θ i`).
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*} [∀ i, MeasurableSpace (Θ i)]
  {A : Type*} [MeasurableSpace A]

/-- The common prior with independent types: the product of the type distributions `ρ i`. -/
noncomputable def prior (ρ : ∀ i, Measure (Θ i)) : Measure (∀ i, Θ i) :=
  Measure.pi ρ

/-- A direct mechanism (Definition 6.2, p.115): a decision rule `q : Θ → A` and a payment rule
`t i : Θ → ℝ` for every agent `i`. -/
structure DirectMechanism (ι : Type*) (Θ : ι → Type*) (A : Type*) where
  /-- the decision rule `q` -/
  q : (∀ i, Θ i) → A
  /-- the payment rule `t i` of agent `i` -/
  t : ι → (∀ i, Θ i) → ℝ

/-- The interim decision rule `Qᵢ(y)` (6.1), p.116: the distribution on `A` of the decision
`q(y, θ₋ᵢ)` when agent `i` reports `y` and the other types are drawn from the prior. -/
noncomputable def interimDist (ρ : ∀ i, Measure (Θ i)) (q : (∀ i, Θ i) → A) (i : ι) (y : Θ i) :
    Measure A :=
  (prior ρ).map fun θ => q (Function.update θ i y)

/-- The interim expected payment `Tᵢ(y)` (6.2), p.116: agent `i`'s expected payment when reporting
`y`, the other types being drawn from the prior. -/
noncomputable def interimTransfer (ρ : ∀ i, Measure (Θ i)) (t : ι → (∀ i, Θ i) → ℝ) (i : ι)
    (y : Θ i) : ℝ :=
  ∫ θ, t i (Function.update θ i y) ∂prior ρ

/-- `∫_A uᵢ(a, x) dQᵢ(y)`: the expected utility from decisions of type `x` of agent `i` when
reporting `y`. -/
noncomputable def interimValue (ρ : ∀ i, Measure (Θ i)) (u : ∀ i, A → Θ i → ℝ)
    (q : (∀ i, Θ i) → A) (i : ι) (x y : Θ i) : ℝ :=
  ∫ a, u i a x ∂interimDist ρ q i y

/-- `q` is a decision rule whose interim expectations exist: `q` is measurable (so each `Qᵢ(y)` is
a probability distribution on `A`) and each `uᵢ(·, x)` is integrable against each `Qᵢ(y)`. The book
omits measurability throughout (note 2 to Ch. 2, p.235). -/
def IsDecisionRule (ρ : ∀ i, Measure (Θ i)) (u : ∀ i, A → Θ i → ℝ) (q : (∀ i, Θ i) → A) :
    Prop :=
  Measurable q ∧ ∀ i (x y : Θ i), Integrable (fun a => u i a x) (interimDist ρ q i y)

/-- The payment rules have interim expectations: for every agent `i` and report `y`, the payment
`tᵢ(y, θ₋ᵢ)` is integrable in `θ₋ᵢ`. -/
def IsTransferRule (ρ : ∀ i, Measure (Θ i)) (t : ι → (∀ i, Θ i) → ℝ) : Prop :=
  ∀ i (y : Θ i), Integrable (fun θ => t i (Function.update θ i y)) (prior ρ)

/-- A direct mechanism all of whose interim expectations exist. -/
def IsMechanism (ρ : ∀ i, Measure (Θ i)) (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism ι Θ A) :
    Prop :=
  IsDecisionRule ρ u M.q ∧ IsTransferRule ρ M.t

/-- Bayesian incentive compatibility (Definition 6.3, p.115): for every agent `i` and all types
`x, y` of agent `i`, the interim expected utility of type `x` from reporting truthfully is at least
that from reporting `y`. -/
def IsBIC (ρ : ∀ i, Measure (Θ i)) (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism ι Θ A) : Prop :=
  ∀ i (x y : Θ i),
    ∫ θ, (u i (M.q (Function.update θ i x)) x - M.t i (Function.update θ i x)) ∂prior ρ ≥
      ∫ θ, (u i (M.q (Function.update θ i y)) x - M.t i (Function.update θ i y)) ∂prior ρ

/-- Interim cyclical monotonicity (Proposition 6.1, p.116): for every agent `i` and every finite
sequence of types `s 0, s 1, …, s m` of agent `i` with `s m = s 0`,
`∑_{κ<m} (∫_A uᵢ(a, s(κ+1)) dQᵢ(s κ) − ∫_A uᵢ(a, s κ) dQᵢ(s κ)) ≤ 0`. -/
def IsInterimCyclicallyMonotone (ρ : ∀ i, Measure (Θ i)) (u : ∀ i, A → Θ i → ℝ)
    (q : (∀ i, Θ i) → A) : Prop :=
  ∀ i (m : ℕ) (s : ℕ → Θ i), s m = s 0 →
    ∑ κ ∈ Finset.range m,
      (interimValue ρ u q i (s (κ + 1)) (s κ) - interimValue ρ u q i (s κ) (s κ)) ≤ 0

/-- Ex post budget balance (Definition 6.5, p.115): `∑ᵢ tᵢ(θ) = 0` for every type vector `θ`. -/
def IsExPostBB (M : DirectMechanism ι Θ A) : Prop :=
  ∀ θ, ∑ i, M.t i θ = 0

/-- Ex ante budget balance (Definition 6.6, p.118): `∫_Θ ∑ᵢ tᵢ(θ) dμ(θ) = 0`, the payment rules
being integrable against the prior (so that the integral exists). -/
def IsExAnteBB (ρ : ∀ i, Measure (Θ i)) (M : DirectMechanism ι Θ A) : Prop :=
  (∀ i, Integrable (M.t i) (prior ρ)) ∧ ∫ θ, ∑ i, M.t i θ ∂prior ρ = 0

/-- Equivalent direct mechanisms (p.118, as for Proposition 3.6): the same decision rule, and for
every agent `i`, all types `θᵢ` and all reports `θᵢ'`, the same expected payment of agent `i`
conditional on type `θᵢ` and report `θᵢ'`. With independent types this conditional expected
payment is `Tᵢ(θᵢ')` whatever `θᵢ` is, so the condition is `T'ᵢ = Tᵢ`. -/
def Equivalent (ρ : ∀ i, Measure (Θ i)) (M M' : DirectMechanism ι Θ A) : Prop :=
  M'.q = M.q ∧ ∀ i (y : Θ i), interimTransfer ρ M'.t i y = interimTransfer ρ M.t i y

end Indep

end MechanismDesign.Correlated


