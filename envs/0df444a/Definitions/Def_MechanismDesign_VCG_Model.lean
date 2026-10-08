-- Prove2me | Definitions.Def_MechanismDesign_VCG_Model
-- name    : MechanismDesign_VCG_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T02:58:29.183788+00:00
-- url     : https://prove2.me/theorems/83c1d526-5011-4eeb-8590-c8a0b5a66f3c
-- title:
--   Dominant-strategy mechanisms: direct mechanisms, DSIC, efficiency, VCG, PAD, flexibility, ex post IR, budget balance, one-dimensional types
-- statement:
--   There are finitely many agents $i \in I$ and a set $A$ of mutually exclusive alternatives (no structure on $A$ is assumed). Each agent $i$ has an abstract set $\Theta_i$ of possible types. If alternative $a$ is chosen and agent $i$ pays the transfer $t_i$, agent $i$ of type $\theta_i$ has utility $u_i(a,\theta_i) - t_i$. A type vector is $\theta = (\theta_1,\dots,\theta_N) \in \Theta = \Theta_1 \times \dots \times \Theta_N$; $\theta_{-i}$ is $\theta$ with agent $i$'s type left out, ranging over $\Theta_{-i} = \prod_{j \ne i} \Theta_j$, and $(\theta_i', \theta_{-i})$ is $\theta$ with agent $i$'s type replaced by $\theta_i'$.
--
--   1. A **direct mechanism** $(q, t_1, \dots, t_N)$ consists of a decision rule $q : \Theta \to A$ and transfer rules $t_i : \Theta \to \mathbb R$ (Definition 7.1).
--   2. It is **dominant strategy incentive-compatible** (DSIC) if for all $\theta \in \Theta$, all $i$ and all $\theta_i' \in \Theta_i$ (Definition 7.2)
--   $$u_i(q(\theta), \theta_i) - t_i(\theta) \ge u_i(q(\theta_i', \theta_{-i}), \theta_i) - t_i(\theta_i', \theta_{-i}).$$
--   3. A decision rule $q$ is **efficient** if $\sum_{i} u_i(q(\theta), \theta_i) \ge \sum_i u_i(a, \theta_i)$ for all $\theta \in \Theta$ and $a \in A$ (Definition 7.3).
--   4. A direct mechanism is a **Vickrey–Clarke–Groves (VCG) mechanism** if $q$ is efficient and for every $i$ there is a function $\tau_i : \Theta_{-i} \to \mathbb R$ with (Definition 7.4)
--   $$t_i(\theta) = -\sum_{j \ne i} u_j(q(\theta), \theta_j) + \tau_i(\theta_{-i}) \qquad \text{for all } \theta \in \Theta.$$
--   5. $q$ satisfies **positive association of differences** (PAD) if whenever $q(\theta) = a$ and $u_i(a, \theta_i') - u_i(b, \theta_i') > u_i(a, \theta_i) - u_i(b, \theta_i)$ for all agents $i$ and all $b \ne a$, then $q(\theta') = a$ (Definition 7.5).
--   6. $q$ is **flexible** if its range $q(\Theta)$ has at least three elements (Definition 7.6).
--   7. Given outside options $a_i \in A$, the mechanism is **ex post individually rational** with respect to $(a_1,\dots,a_N)$ if $u_i(q(\theta), \theta_i) - t_i(\theta) \ge u_i(a_i, \theta_i)$ for all $i$ and $\theta$ (Definition 7.7); the constraint for a single agent $i$ is recorded separately.
--   8. It is **ex post budget balanced** if $\sum_i t_i(\theta) = 0$ for all $\theta$ (Definition 7.8).
--
--   The single-agent notions of Chapter 5 are applied agent by agent, to one agent's utility $v = u_i$ and a rule $g : \Theta_i \to A$ (in Chapter 7, $g(\theta_i) = q(\theta_i, \theta_{-i})$ for a fixed $\theta_{-i}$):
--
--   - $g$ is **weakly monotone** if $v(g(\theta^1), \theta^1) - v(g(\theta^2), \theta^1) \ge v(g(\theta^1), \theta^2) - v(g(\theta^2), \theta^2)$ for all types $\theta^1, \theta^2$ (Definition 5.4); $q$ is weakly monotone in every $\theta_i$ if every such section is.
--   - An **order** $R$ of $A$ is a complete and transitive relation; $aPb$ means $aRb$ and not $bRa$, and $aIb$ means $aRb$ and $bRa$.
--   - $\theta \succ_R \theta'$ if $v(a,\theta) - v(a',\theta) > v(a,\theta') - v(a',\theta')$ whenever $aPa'$, and $v(a,\theta) - v(a',\theta) = v(a,\theta') - v(a',\theta') = 0$ whenever $aIa'$ (Definition 5.6).
--   - $g$ is **monotone with respect to $R$** if $\theta \succ_R \theta'$ implies $g(\theta)\,R\,g(\theta')$ (Definition 5.7); the type set is **one-dimensional with respect to $R$** if any two distinct types are ordered by $\succ_R$ in at least one direction (Definition 5.8); it is **bounded** if there is $c > 0$ with $-c < v(a',\theta) - v(a,\theta) < c$ for all $a, a'$ and $\theta$ (Definition 5.9).
--
--   These are the objects of every statement of Chapter 7.
--
--   **Formalization Note** Agents form a finite type `ι` with decidable equality; the type set of agent `i` is an arbitrary type `Θ i`, and utilities are `u : ∀ i, A → Θ i → ℝ`. A profile is `θ : ∀ i, Θ i`, and $(\theta_i', \theta_{-i})$ is `Function.update θ i θ'`. $\Theta_{-i}$ is the product `Others Θ i` of the `Θ j` over `j ≠ i`, and $\theta_{-i}$ is `restrict θ i`; the VCG term $\tau_i$ is a function on `Others Θ i`, so it cannot depend on agent $i$'s own type. Flexibility uses `Set.encard`, so an infinite range counts as flexible. Definition 7.2 on p.131 prints "$\theta_i' \in \Theta_i'$"; this is read as $\theta_i' \in \Theta_i$.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.130–138, §§7.2–7.5, Definitions 7.1–7.8; pp.97, 104–106, Definitions 5.4, 5.6–5.9

import Mathlib

namespace MechanismDesign.VCG

/-!
# Dominant-strategy mechanisms (Börgers, Chapter 7)

The model of Börgers, *An Introduction to the Theory of Mechanism Design*, §7.2 (pp.130–131):
a finite set `ι` of agents (the book's `I = {1, …, N}`), a set `A` of alternatives, for each agent
`i` an abstract type set `Θ i`, and utilities `u i a θᵢ` (the book's `uᵢ(a, θᵢ)`); agent `i`'s
utility from alternative `a` and transfer `tᵢ` is `uᵢ(a, θᵢ) − tᵢ`. A type vector is
`θ : ∀ i, Θ i`. The profile `(θ'ᵢ, θ₋ᵢ)` is `Function.update θ i θ'ᵢ`.
-/

variable {ι : Type*} {A : Type*} {Θ : ι → Type*}

/-- `Θ₋ᵢ`, the set of type vectors of the agents other than `i` (p.131): the product of the
`Θ j` over `j ≠ i`. -/
def Others (Θ : ι → Type*) (i : ι) : Type _ := ∀ j : {j : ι // j ≠ i}, Θ j.1

/-- `θ₋ᵢ`, the vector `θ` with agent `i`'s type left out (p.131). -/
def restrict (θ : ∀ j, Θ j) (i : ι) : Others Θ i := fun j => θ j.1

/-- Definition 7.1 (p.131): a direct mechanism `(q, t₁, …, t_N)` consists of a decision rule
`q : Θ → A` and, for every agent `i`, a transfer rule `tᵢ : Θ → ℝ` (what agent `i` pays). -/
structure DirectMechanism (Θ : ι → Type*) (A : Type*) where
  /-- the decision rule `q` -/
  q : (∀ i, Θ i) → A
  /-- the transfer rules `tᵢ` (paid by agent `i`) -/
  t : ι → (∀ i, Θ i) → ℝ

variable [DecidableEq ι]

/-- Definition 7.2 (p.131): the direct mechanism is dominant strategy incentive-compatible if for
all `θ ∈ Θ`, all `i ∈ I` and all `θ'ᵢ ∈ Θᵢ`,
`uᵢ(q(θ), θᵢ) − tᵢ(θ) ≥ uᵢ(q(θ'ᵢ, θ₋ᵢ), θᵢ) − tᵢ(θ'ᵢ, θ₋ᵢ)`. -/
def DSIC (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism Θ A) : Prop :=
  ∀ (θ : ∀ j, Θ j) (i : ι) (θ' : Θ i),
    u i (M.q θ) (θ i) - M.t i θ ≥
      u i (M.q (Function.update θ i θ')) (θ i) - M.t i (Function.update θ i θ')

/-- Definition 7.3 (p.132): a decision rule `q` is efficient if for every `θ ∈ Θ`,
`∑ᵢ uᵢ(q(θ), θᵢ) ≥ ∑ᵢ uᵢ(a, θᵢ)` for all `a ∈ A`. -/
def IsEfficient [Fintype ι] (u : ∀ i, A → Θ i → ℝ) (q : (∀ i, Θ i) → A) : Prop :=
  ∀ (θ : ∀ j, Θ j) (a : A), ∑ i, u i (q θ) (θ i) ≥ ∑ i, u i a (θ i)

/-- Definition 7.4 (p.133): `(q, t₁, …, t_N)` is a Vickrey–Clarke–Groves mechanism if `q` is
efficient and for every `i` there is a function `τᵢ : Θ₋ᵢ → ℝ` with
`tᵢ(θ) = −∑_{j ≠ i} u_j(q(θ), θ_j) + τᵢ(θ₋ᵢ)` for all `θ ∈ Θ`. -/
def IsVCG [Fintype ι] (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism Θ A) : Prop :=
  IsEfficient u M.q ∧
    ∀ i : ι, ∃ τ : Others Θ i → ℝ, ∀ θ : ∀ j, Θ j,
      M.t i θ = -(∑ j ∈ Finset.univ.erase i, u j (M.q θ) (θ j)) + τ (restrict θ i)

/-- Definition 7.5 (p.135): `q` satisfies positive association of differences (PAD) if
`θ, θ' ∈ Θ`, `q(θ) = a` and `uᵢ(a, θ'ᵢ) − uᵢ(b, θ'ᵢ) > uᵢ(a, θᵢ) − uᵢ(b, θᵢ)` for all `i ∈ I` and
all `b ∈ A` with `b ≠ a` imply `q(θ') = a`. -/
def PAD (u : ∀ i, A → Θ i → ℝ) (q : (∀ i, Θ i) → A) : Prop :=
  ∀ (θ θ' : ∀ j, Θ j) (a : A), q θ = a →
    (∀ (i : ι) (b : A), b ≠ a → u i a (θ' i) - u i b (θ' i) > u i a (θ i) - u i b (θ i)) →
      q θ' = a

/-- Definition 7.6 (p.135): `q` is flexible if its range `q(Θ)` has at least three elements. -/
def Flexible (q : (∀ i, Θ i) → A) : Prop :=
  3 ≤ (Set.range q).encard

/-- Definition 7.7 (p.137), the constraint for one agent: `uᵢ(q(θ), θᵢ) − tᵢ(θ) ≥ uᵢ(aᵢ, θᵢ)` for
all `θ ∈ Θ`. -/
def ExPostIRAgent (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism Θ A) (i : ι) (aᵢ : A) : Prop :=
  ∀ θ : ∀ j, Θ j, u i (M.q θ) (θ i) - M.t i θ ≥ u i aᵢ (θ i)

/-- Definition 7.7 (p.137): for outside options `(a₁, …, a_N)`, the mechanism is ex post
individually rational with respect to `(a₁, …, a_N)` if the constraint holds for every agent. -/
def ExPostIR (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism Θ A) (a : ι → A) : Prop :=
  ∀ i : ι, ExPostIRAgent u M i (a i)

/-- Definition 7.8 (p.138): the mechanism is ex post budget balanced if `∑ᵢ tᵢ(θ) = 0` for all
`θ ∈ Θ` (an equality). -/
def BudgetBalanced [Fintype ι] (M : DirectMechanism Θ A) : Prop :=
  ∀ θ : ∀ j, Θ j, ∑ i, M.t i θ = 0

/-! ### Single-agent notions of Chapter 5, applied agent by agent

Here `v : A → T → ℝ` is one agent's utility on a type set `T`, and `g : T → A` a decision rule
as a function of that agent's type (in Chapter 7: `θᵢ ↦ q(θᵢ, θ₋ᵢ)` for fixed `θ₋ᵢ`). -/

/-- Definition 5.4 (p.97): `g` is weakly monotone if for all `θ₁, θ₂`, with `a₁ = g(θ₁)`,
`a₂ = g(θ₂)`, `v(a₁, θ₁) − v(a₂, θ₁) ≥ v(a₁, θ₂) − v(a₂, θ₂)`. -/
def WeaklyMonotone {T : Type*} (v : A → T → ℝ) (g : T → A) : Prop :=
  ∀ θ₁ θ₂ : T, v (g θ₁) θ₁ - v (g θ₂) θ₁ ≥ v (g θ₁) θ₂ - v (g θ₂) θ₂

/-- "`q` is weakly monotone in every `θᵢ`" (Proposition 7.5, p.135): for every agent `i` and
every `θ₋ᵢ`, the rule `θᵢ ↦ q(θᵢ, θ₋ᵢ)` is weakly monotone for agent `i`'s utility. -/
def WeaklyMonotoneInEvery (u : ∀ i, A → Θ i → ℝ) (q : (∀ i, Θ i) → A) : Prop :=
  ∀ (i : ι) (θ : ∀ j, Θ j), WeaklyMonotone (u i) (fun x : Θ i => q (Function.update θ i x))

/-- An order of `A` (p.104 and Chapter 5, note 2): a complete and transitive binary relation. -/
def IsCompleteOrder (R : A → A → Prop) : Prop :=
  (∀ a b, R a b ∨ R b a) ∧ ∀ a b c, R a b → R b c → R a c

/-- The strict order `P` derived from `R`: `aPb ⇔ [aRb and not bRa]` (p.104). -/
def StrictPart (R : A → A → Prop) (a b : A) : Prop := R a b ∧ ¬ R b a

/-- The indifference relation `I` derived from `R`: `aIb ⇔ [aRb and bRa]` (p.104). -/
def Indiff (R : A → A → Prop) (a b : A) : Prop := R a b ∧ R b a

/-- Definition 5.6 (p.104): `θ ≻_R θ'` ("`θ` is a higher type than `θ'` relative to `R`") if
`v(a, θ) − v(a', θ) > v(a, θ') − v(a', θ')` for all `a, a'` with `aPa'`, and
`v(a, θ) − v(a', θ) = v(a, θ') − v(a', θ') = 0` for all `a, a'` with `aIa'`. -/
def HigherType {T : Type*} (R : A → A → Prop) (v : A → T → ℝ) (θ θ' : T) : Prop :=
  (∀ a a', StrictPart R a a' → v a θ - v a' θ > v a θ' - v a' θ') ∧
    ∀ a a', Indiff R a a' → v a θ - v a' θ = 0 ∧ v a θ' - v a' θ' = 0

/-- Definition 5.7 (p.105): `g` is monotone with respect to `R` if `θ ≻_R θ'` implies
`g(θ) R g(θ')`. -/
def MonotoneWRT {T : Type*} (R : A → A → Prop) (v : A → T → ℝ) (g : T → A) : Prop :=
  ∀ θ θ' : T, HigherType R v θ θ' → R (g θ) (g θ')

/-- Definition 5.8 (p.105): the type set is one-dimensional with respect to `R` if any two
distinct types are ordered by `≻_R` (in at least one direction). -/
def OneDimensional {T : Type*} (R : A → A → Prop) (v : A → T → ℝ) : Prop :=
  ∀ θ θ' : T, θ ≠ θ' → HigherType R v θ θ' ∨ HigherType R v θ' θ

/-- Definition 5.9 (p.106): the type set is bounded if there is `c > 0` with
`−c < v(a', θ) − v(a, θ) < c` for all `a, a' ∈ A` and all types `θ`. -/
def BoundedTypes {T : Type*} (v : A → T → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (a a' : A) (θ : T), -c < v a' θ - v a θ ∧ v a' θ - v a θ < c

end MechanismDesign.VCG


