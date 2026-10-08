-- Prove2me | Definitions.Def_MechanismDesign_Correlated_FiniteModel
-- name    : MechanismDesign_Correlated_FiniteModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T02:29:30.540992+00:00
-- url     : https://prove2.me/theorems/67d78598-5f71-441d-902c-986bcaae75b0
-- title:
--   Bayesian mechanism design with finite correlated types (Börgers §6.2, §6.4): conditional beliefs, BIC, budget balance, Crémer–McLean and identifiability conditions
-- statement:
--   This file sets up the model of Börgers, §6.4: Bayesian mechanism design with finitely many types that need not be independent.
--
--   **Environment.** A finite set $I$ of agents chooses an alternative $a$ from an arbitrary set $A$. Agent $i$ has a type $\theta_i$ in a **finite** type set $\Theta_i$ and utility $u_i(a,\theta_i) - t_i$. A distribution on $\Theta = \prod_i \Theta_i$ is a function $\nu : \Theta \to \mathbb R$ with $\nu(\theta) \ge 0$ and $\sum_\theta \nu(\theta) = 1$; the standing assumption of §6.4 (p.119) is that the common prior $\mu$ has **full support**, $\mu(\theta) > 0$ for every $\theta$. For a distribution $\nu$ with full support, the conditional probability of the other agents' types $\theta_{-i}$ given agent $i$'s type $\theta_i$ is
--   $$\nu(\theta_{-i} \mid \theta_i) = \frac{\nu(\theta_i, \theta_{-i})}{\sum_{\theta_{-i}'} \nu(\theta_i, \theta_{-i}')}.$$
--
--   1. A **direct mechanism** $(q, t_1,\dots,t_N)$ (Definition 6.2): $q : \Theta \to A$, $t_i : \Theta \to \mathbb R$.
--   2. **Bayesian incentive compatibility** (Definition 6.3): for all $i$ and $\theta_i, \theta_i' \in \Theta_i$,
--   $$\sum_{\theta_{-i}\in\Theta_{-i}} \big(u_i(q(\theta_i,\theta_{-i}),\theta_i) - t_i(\theta_i,\theta_{-i})\big)\,\mu(\theta_{-i}\mid\theta_i) \ \ge\ \sum_{\theta_{-i}\in\Theta_{-i}} \big(u_i(q(\theta_i',\theta_{-i}),\theta_i) - t_i(\theta_i',\theta_{-i})\big)\,\mu(\theta_{-i}\mid\theta_i).$$
--   3. **Ex post budget balance** (Definition 6.5): $\sum_i t_i(\theta) = 0$ for all $\theta$; **ex ante budget balance** (Definition 6.6): $\sum_\theta \mu(\theta)\sum_i t_i(\theta) = 0$.
--   4. The **Crémer–McLean condition** (Definition 6.7): there are no agent $i$, type $\theta_i \in \Theta_i$ and function $\lambda_i : \Theta_i \setminus \{\theta_i\} \to \mathbb R_+$ with
--   $$\mu(\theta_{-i}\mid\theta_i) = \sum_{\theta_i' \in \Theta_i\setminus\{\theta_i\}} \lambda(\theta_i')\,\mu(\theta_{-i}\mid\theta_i') \quad\text{for all } \theta_{-i}\in\Theta_{-i}.$$
--   5. The **identifiability condition** (Definition 6.8): for every distribution $\nu \ne \mu$ with $\nu(\theta) > 0$ for all $\theta$, there are an agent $i$ and a type $\theta_i$ such that for every collection of nonnegative coefficients $(\lambda_{\theta_i'})_{\theta_i'\in\Theta_i}$ we have $\nu(\theta_{-i}\mid\theta_i) \ne \sum_{\theta_i'\in\Theta_i} \lambda_{\theta_i'}\,\mu(\theta_{-i}\mid\theta_i')$ for at least one $\theta_{-i}$.
--
--   These are the objects of Propositions 6.4 and 6.6.
--
--   **Formalization Note** The Crémer–McLean condition uses nonnegative weights with no sum-to-one constraint, exactly as Definition 6.7 prints it (the surrounding prose speaks of a "convex combination"; the definition is the conic one). A vector $\theta_{-i}$ is represented by a full type vector $\theta$: the conditional probability `condProb ν i x θ` reads only $\theta_{-i}$ (coordinate $i$ is overwritten by $x$), and the conditional expectation `condExp ν i x g` sums $g(\theta)\,\nu(\theta_{-i}\mid x)$ over the type vectors $\theta$ with $\theta_i = x$, which are in bijection with $\Theta_{-i}$. The weights $\lambda$ of Definition 6.7 are given as a function on all of $\Theta_i$ whose value at $\theta_i$ is never used.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.114–127: setup p.114; Definitions 6.2, 6.3, 6.5 p.115; Definition 6.6 p.118; standing assumptions of §6.4.1 (finite types, μ(θ) > 0) p.119; Definition 6.7 p.120; Definition 6.8 p.126

import Mathlib

namespace MechanismDesign.Correlated

namespace FiniteTypes

/-!
Bayesian mechanism design with finite, possibly correlated types (Börgers, *An Introduction to the
Theory of Mechanism Design*, §6.2 and §6.4, pp.114–127).

Agents form a finite set `ι`; agent `i`'s type set `Θ i` is finite; the alternatives form an
arbitrary set `A`. A distribution on `Θ = ∏ᵢ Θ i` is a function `ν : Θ → ℝ`. The standing assumption
of §6.4 (p.119) is that the common prior `μ` gives every type vector positive probability.

A type vector of the other agents `θ₋ᵢ ∈ Θ₋ᵢ` is represented by any full type vector `θ`; the
functions below depend on `θ` only through `θ₋ᵢ`, because coordinate `i` is overwritten by
`Function.update θ i x`, or the sum ranges over the fibre `{θ | θ i = x}`, which is in bijection
with `Θ₋ᵢ`.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*} [∀ i, Fintype (Θ i)]
  [∀ i, DecidableEq (Θ i)]

/-- `ν` is a probability distribution on `Θ` giving every type vector positive probability. -/
def IsFullSupportDist (ν : (∀ i, Θ i) → ℝ) : Prop :=
  (∀ θ, 0 < ν θ) ∧ ∑ θ, ν θ = 1

/-- The probability `ν(θᵢ = x)` that agent `i`'s type is `x`. -/
def typeProb (ν : (∀ i, Θ i) → ℝ) (i : ι) (x : Θ i) : ℝ :=
  ∑ θ ∈ Finset.univ.filter (fun θ : ∀ j, Θ j => θ i = x), ν θ

/-- The conditional probability `ν(θ₋ᵢ | x)` of the other agents' types `θ₋ᵢ` (read off `θ`) given
that agent `i`'s type is `x`. -/
noncomputable def condProb (ν : (∀ i, Θ i) → ℝ) (i : ι) (x : Θ i) (θ : ∀ j, Θ j) : ℝ :=
  ν (Function.update θ i x) / typeProb ν i x

/-- The conditional expectation `∑_{θ₋ᵢ ∈ Θ₋ᵢ} g(x, θ₋ᵢ) ν(θ₋ᵢ | x)` of `g` given that agent `i`'s
type is `x`; the sum ranges over the type vectors `θ` with `θ i = x`. -/
noncomputable def condExp (ν : (∀ i, Θ i) → ℝ) (i : ι) (x : Θ i) (g : (∀ j, Θ j) → ℝ) : ℝ :=
  ∑ θ ∈ Finset.univ.filter (fun θ : ∀ j, Θ j => θ i = x), g θ * condProb ν i x θ

/-- A direct mechanism (Definition 6.2, p.115): a decision rule `q : Θ → A` and a payment rule
`t i : Θ → ℝ` for every agent `i`. -/
structure DirectMechanism (ι : Type*) (Θ : ι → Type*) (A : Type*) where
  /-- the decision rule `q` -/
  q : (∀ i, Θ i) → A
  /-- the payment rule `t i` of agent `i` -/
  t : ι → (∀ i, Θ i) → ℝ

variable {A : Type*}

/-- Bayesian incentive compatibility (Definition 6.3, p.115) with respect to the prior `μ` and
utilities `u i a θᵢ - tᵢ`: for every agent `i` and all types `x, y` of agent `i`,
`∑_{θ₋ᵢ} (uᵢ(q(x, θ₋ᵢ), x) − tᵢ(x, θ₋ᵢ)) μ(θ₋ᵢ | x) ≥ ∑_{θ₋ᵢ} (uᵢ(q(y, θ₋ᵢ), x) − tᵢ(y, θ₋ᵢ)) μ(θ₋ᵢ | x)`. -/
def IsBIC (μ : (∀ i, Θ i) → ℝ) (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism ι Θ A) : Prop :=
  ∀ i (x y : Θ i),
    condExp μ i x (fun θ => u i (M.q θ) x - M.t i θ) ≥
      condExp μ i x (fun θ => u i (M.q (Function.update θ i y)) x - M.t i (Function.update θ i y))

/-- Ex post budget balance (Definition 6.5, p.115): `∑ᵢ tᵢ(θ) = 0` for every type vector `θ`. -/
def IsExPostBB (M : DirectMechanism ι Θ A) : Prop :=
  ∀ θ, ∑ i, M.t i θ = 0

/-- Ex ante budget balance (Definition 6.6, p.118): `∑_θ μ(θ) ∑ᵢ tᵢ(θ) = 0`. -/
def IsExAnteBB (μ : (∀ i, Θ i) → ℝ) (M : DirectMechanism ι Θ A) : Prop :=
  ∑ θ, μ θ * ∑ i, M.t i θ = 0

/-- The Crémer–McLean condition (Definition 6.7, p.120): there are no agent `i`, type `x` of `i`
and nonnegative weights `λ(y)`, `y ∈ Θᵢ \ {x}`, with
`μ(θ₋ᵢ | x) = ∑_{y ∈ Θᵢ \ {x}} λ(y) μ(θ₋ᵢ | y)` for all `θ₋ᵢ`. (The weights are given on all of
`Θᵢ`; the value at `x` is never used.) -/
def CremerMcLean (μ : (∀ i, Θ i) → ℝ) : Prop :=
  ¬ ∃ (i : ι) (x : Θ i) (w : Θ i → ℝ), (∀ y, y ≠ x → 0 ≤ w y) ∧
    ∀ θ : ∀ j, Θ j, condProb μ i x θ = ∑ y ∈ Finset.univ.erase x, w y * condProb μ i y θ

/-- The identifiability condition (Definition 6.8, p.126): for every distribution `ν ≠ μ` on `Θ`
with `ν(θ) > 0` for all `θ`, there are an agent `i` and a type `x` of `i` such that for every
collection of nonnegative coefficients `(λ_y)_{y ∈ Θᵢ}` there is some `θ₋ᵢ` with
`ν(θ₋ᵢ | x) ≠ ∑_{y ∈ Θᵢ} λ_y μ(θ₋ᵢ | y)`. -/
def Identifiable (μ : (∀ i, Θ i) → ℝ) : Prop :=
  ∀ ν : (∀ i, Θ i) → ℝ, IsFullSupportDist ν → ν ≠ μ →
    ∃ (i : ι) (x : Θ i), ∀ w : Θ i → ℝ, (∀ y, 0 ≤ w y) →
      ∃ θ : ∀ j, Θ j, condProb ν i x θ ≠ ∑ y, w y * condProb μ i y θ

end FiniteTypes

end MechanismDesign.Correlated


