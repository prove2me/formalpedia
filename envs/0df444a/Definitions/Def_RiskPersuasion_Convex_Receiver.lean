-- Prove2me | Definitions.Def_RiskPersuasion_Convex_Receiver
-- name    : RiskPersuasion_Convex_Receiver
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T00:40:36.854746+00:00
-- url     : https://prove2.me/theorems/ffb7fa77-054b-4e2b-bcab-834a0b895454
-- title:
--   Risk-conscious receiver: the sets P_a, optimal strategies, problem (3), full persuasion (Secs. 2.2–2.3, 4)
-- statement:
--   This file models a receiver with an arbitrary (risk-conscious) utility over beliefs and the sender's persuasion problem (3).
--
--   Let $\Omega$ be a finite state space, $A$ a finite action set, $\rho : \Delta(\Omega) \times A \to \mathbb{R}$ the receiver's utility (no linearity or continuity assumed) and $v : \Omega \times A \to \mathbb{R}$ the sender's utility.
--
--   1. **Eq. (1).** For each action $a$, the set of beliefs at which $a$ is optimal is
--   $$P_a = \{\mu \in \Delta(\Omega) : a \in \arg\max_{a' \in A} \rho(\mu, a')\}.$$
--   2. **Optimal strategy (Eq. (2)).** A strategy $a(\cdot)$ is optimal against posteriors $\mu_s$ if $\mu_s \in P_{a(s)}$ for every signal $s$. A mixed strategy $\sigma(s) \in \Delta(A)$ is optimal if $\sigma(s)(a) > 0$ implies $\mu_s \in P_a$.
--   3. **Problem (3).** A feasible point of the sender's problem is a signal space $S$, a signaling scheme $\pi$ on $\Omega \times S$ with marginal $\mu^*$, a version of the posterior, and a measurable optimal strategy $a(\cdot)$; its value is $\mathbb{E}_\pi[v(\bar\omega, a(\bar s))]$. The set of achievable values collects these over all signal spaces, schemes and optimal strategies (the sender picks among the receiver's optimal strategies: sender-preferred equilibrium).
--   4. **Full persuasion (Definition 1).** $\Upsilon_a = \{\omega \in \Omega : v(\omega,a) \ge v(\omega,a') \text{ for all } a'\}$. A scheme $\pi$ with strategy $a(\cdot)$ fully persuades the receiver if, $\pi$-almost surely, $\bar\omega \in \Upsilon_{a(\bar s)}$. Full persuasion is possible if some scheme, posterior version and measurable optimal strategy fully persuade the receiver.
--
--   Problem (3) is the paper's starting point; Theorem 1 shows its achievable values are exactly the objective values of the convex program (7).
--
--   **Formalization Note** $\rho$ is a function on all of $\mathbb{R}^{\Omega}$, but $P_a$ only uses its values on the simplex. Signal spaces range over all measurable types in Lean's `Type`. Definition 1's "for each $\omega$, $s$ with $\pi(\omega,s) > 0$, if $a(s) = a$ then $\omega \in \Upsilon_a$" is rendered as $\pi\{(\omega,s) : \omega \notin \Upsilon_{a(s)}\} = 0$, which coincides with it for discrete signals.
-- source:
--   Anunrojwong, Iyer & Lingenbrink, Persuading Risk-Conscious Agents: A Geometric Approach, arXiv:2208.03758v3, pp. 11–13, Section 2.2 Eq. (1), Section 2.3 Eqs. (2)–(3); p. 20, Definition 1 and the sets Υ_a

import Mathlib
import Definitions.Def_RiskPersuasion_Convex_Signaling

open MeasureTheory

namespace RiskPersuasion.Convex

/-- Eq. (1): `P_a = {μ ∈ Δ(Ω) : a ∈ argmax_{a'} ρ(μ, a')}`, the beliefs at which action `a` is
optimal for the receiver with (arbitrary, possibly nonlinear) utility `ρ : Δ(Ω) × A → ℝ`.
`ρ` is given on all of `ℝ^Ω`; only its values on the simplex matter. -/
def P {Ω A : Type} [Fintype Ω] [Fintype A] (ρ : (Ω → ℝ) → A → ℝ) (a : A) : Set (Ω → ℝ) :=
  {μ | μ ∈ stdSimplex ℝ Ω ∧ ∀ a' : A, ρ μ a' ≤ ρ μ a}

/-- Eq. (2): `a(·)` is an optimal strategy for the receiver against the posterior `post`:
`a(s) ∈ argmax_a ρ(μ_s, a)`, i.e. `μ_s ∈ P_{a(s)}`, for every signal `s`. -/
def IsOptimalStrategy {Ω S A : Type} [Fintype Ω] [Fintype A]
    (ρ : (Ω → ℝ) → A → ℝ) (post : S → Ω → ℝ) (a : S → A) : Prop :=
  ∀ s : S, post s ∈ P ρ (a s)

/-- A mixed receiver strategy `σ : S → (A → ℝ)` (p. 11: "we can easily incorporate mixed
strategies") is optimal against `post` if each `σ(s)` is a probability vector on `A` that puts
positive weight only on actions optimal at `μ_s`: `σ(s)(a) > 0 ⇒ μ_s ∈ P_a`. -/
def IsOptimalMixedStrategy {Ω S A : Type} [Fintype Ω] [Fintype A]
    (ρ : (Ω → ℝ) → A → ℝ) (post : S → Ω → ℝ) (σ : S → A → ℝ) : Prop :=
  ∀ s : S, σ s ∈ stdSimplex ℝ A ∧ ∀ a : A, 0 < σ s a → post s ∈ P ρ a

/-- A feasible point of the sender's persuasion problem (3) over the signal space `S`:
a signaling scheme `π`, a version `post` of the Bayes posterior, and a measurable optimal
receiver strategy `a` (sender-preferred: the sender chooses `a` among optimal strategies). -/
def IsPersuasionOutcome {Ω S A : Type} [Fintype Ω] [Fintype A] [MeasurableSpace Ω]
    [MeasurableSpace S] (μstar : Ω → ℝ) (ρ : (Ω → ℝ) → A → ℝ) (π : Measure (Ω × S))
    (post : S → Ω → ℝ) (a : S → A) : Prop :=
  IsSignalingScheme μstar π ∧ IsPosterior π post ∧ IsOptimalStrategy ρ post a ∧
    IsMeasurableStrategy a

/-- The set of sender values achievable in problem (3): all `E_π[v(ω̄, a(s̄))]` over every
measurable signal space `S`, scheme `π`, posterior version and measurable optimal strategy. -/
def achievableValues {Ω A : Type} [Fintype Ω] [Fintype A] [MeasurableSpace Ω]
    (μstar : Ω → ℝ) (ρ : (Ω → ℝ) → A → ℝ) (v : Ω → A → ℝ) : Set ℝ :=
  {x | ∃ (S : Type) (_ : MeasurableSpace S) (π : Measure (Ω × S)) (post : S → Ω → ℝ)
      (a : S → A), IsPersuasionOutcome μstar ρ π post a ∧ senderValue v π a = x}

/-- `Υ_a = {ω ∈ Ω : v(ω, a) ≥ v(ω, a') for all a'}`, the states at which `a` is sender-optimal. -/
def Upsilon {Ω A : Type} (v : Ω → A → ℝ) (a : A) : Set Ω :=
  {ω | ∀ a' : A, v ω a' ≤ v ω a}

/-- Definition 1: `π` (with receiver strategy `a`) fully persuades the receiver if, `π`-almost
surely, the realized state lies in `Υ_{a(s̄)}`; this is the measure-theoretic form of "for each
`ω`, `s` with `π(ω, s) > 0`, if `a(s) = a` then `ω ∈ Υ_a`". -/
def FullyPersuades {Ω S A : Type} [MeasurableSpace Ω] [MeasurableSpace S]
    (v : Ω → A → ℝ) (π : Measure (Ω × S)) (a : S → A) : Prop :=
  π {p | p.1 ∉ Upsilon v (a p.2)} = 0

/-- Full persuasion is possible: some signaling scheme, together with a posterior version and a
measurable optimal receiver strategy, fully persuades the receiver. -/
def FullPersuasionPossible {Ω A : Type} [Fintype Ω] [Fintype A] [MeasurableSpace Ω]
    (μstar : Ω → ℝ) (ρ : (Ω → ℝ) → A → ℝ) (v : Ω → A → ℝ) : Prop :=
  ∃ (S : Type) (_ : MeasurableSpace S) (π : Measure (Ω × S)) (post : S → Ω → ℝ) (a : S → A),
    IsPersuasionOutcome μstar ρ π post a ∧ FullyPersuades v π a

end RiskPersuasion.Convex


