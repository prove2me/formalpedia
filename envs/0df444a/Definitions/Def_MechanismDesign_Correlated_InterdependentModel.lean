-- Prove2me | Definitions.Def_MechanismDesign_Correlated_InterdependentModel
-- name    : MechanismDesign_Correlated_InterdependentModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T02:29:44.583895+00:00
-- url     : https://prove2.me/theorems/917c7048-4552-4302-801f-2fc9e3064c45
-- title:
--   Informational interdependence (Börgers §9.3): linear interdependent utilities, independent signals on [0,1]^K, interim probabilities, BIC, first best rules
-- statement:
--   This file sets up the model of Börgers, §9.3 (after Jehiel and Moldovanu 2001), in which each agent's private signal affects the other agents' utilities.
--
--   **Environment.** A finite set $I = \{1,\dots,N\}$ of agents chooses an alternative from a finite set $A = \{a_1,\dots,a_K\}$. Agent $i$ observes a $K$-dimensional signal $\theta^i = (\theta^i_1,\dots,\theta^i_K) \in [0,1]^K$, one component per alternative. The signal $\theta^i$ has a density $f^i$ that is positive everywhere on $[0,1]^K$, and different agents' signals are independent. If alternative $a_k$ is chosen and agent $i$ pays $t_i$, agent $i$'s utility is (9.2)
--   $$\sum_{j=1}^N \alpha^j_{ki}\,\theta^j_k - t_i,$$
--   where $\alpha^j_{ki}$, the factor in front of the $k$-th component of agent $j$'s signal in agent $i$'s utility, is nonzero for all $i, j, k$.
--
--   1. A **direct mechanism** $(q, t_1,\dots,t_N)$ consists of a choice rule $q : [0,1]^{IK} \to \Delta(A)$ assigning a probability distribution over $A$ to every profile $\theta = (\theta^1,\dots,\theta^N)$ of reported signals, and transfer rules $t_i : [0,1]^{IK} \to \mathbb R$.
--   2. The **interim probability** $Q^i_a(\theta^i)$ is the probability that alternative $a$ is chosen when agent $i$'s signal is $\theta^i$ and the other signals are drawn from their distributions.
--   3. A direct mechanism is **Bayesian incentive-compatible** if for every agent $i$ and all $\theta^i, \tilde\theta^i \in [0,1]^K$, agent $i$'s expected utility from reporting $\theta^i$ is at least his expected utility from reporting $\tilde\theta^i$ when his true signal is $\theta^i$ (the others reporting truthfully).
--   4. A choice rule $q^*$ is **first best** if for every $\theta \in [0,1]^{IK}$, $q^*(\theta)$ assigns positive probability only to alternatives that maximize the sum of the agents' utilities; a direct mechanism is first best if its choice rule is.
--
--   These are the objects of Proposition 9.1.
--
--   **Formalization Note** Alternatives are a finite type `A`, and a signal is a vector `A → ℝ` indexed by alternatives (the book's index $k$ of $a_k$). The weight $\alpha^j_{ki}$ is `α j a i`. The distribution of agent $i$'s signal is Lebesgue measure on $[0,1]^K$ with density $f^i$, where $f^i$ is integrable on $[0,1]^K$ with integral $1$; the joint distribution is the product over agents. A choice rule is a function to $\mathbb R^A$ whose values on $[0,1]^{IK}$ are probability vectors. The book omits measurability (note 2 to Ch. 2); here a choice rule is measurable and each transfer $t_i(\tilde\theta^i, \theta^{-i})$ is integrable in $\theta^{-i}$, so that $Q^i_a$ and expected utilities are genuine integrals. Welfare of an alternative is the sum of the agents' utilities from it without transfers (transfers do not depend on the alternative).
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.158, §9.3 (model, (9.2), direct mechanisms, interim probabilities, incentive compatibility, first best), and note 2 to Ch. 9 p.236

import Mathlib

namespace MechanismDesign.Correlated

open MeasureTheory

namespace Interdependent

/-!
The informational-interdependence model of Börgers, *An Introduction to the Theory of Mechanism
Design*, §9.3 (p.158), after Jehiel and Moldovanu (2001).

Agents form a finite set `ι`; the alternatives form a finite set `A` (the book's
`{a₁, …, a_K}`). Agent `i` observes a signal `θⁱ = (θⁱ_a)_{a ∈ A} ∈ [0,1]^A`, one component per
alternative. A signal profile is `θ : ι → A → ℝ`, with `θ j a` the component for alternative `a` of
agent `j`'s signal. Agent `i`'s utility from alternative `a` and transfer `tᵢ` is
`∑_j α j a i * θ j a - tᵢ` (9.2), where `α j a i` is the book's `α^j_{ai}`.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*} [Fintype A] [DecidableEq A]

/-- The signal space `[0,1]^A` of one agent. -/
def cube (A : Type*) : Set (A → ℝ) :=
  Set.univ.pi fun _ => Set.Icc 0 1

/-- The space `[0,1]^{IK}` of signal profiles. -/
def profiles (ι A : Type*) : Set (ι → A → ℝ) :=
  Set.univ.pi fun _ => cube A

/-- The environment of §9.3: weights `α j a i` (all nonzero) and, for every agent `i`, a density
`f i` of agent `i`'s signal on `[0,1]^A` that is positive everywhere on `[0,1]^A` and integrates to
`1`. Signals of different agents are independent (see `prior`). -/
structure Setting (ι A : Type*) [Fintype ι] [Fintype A] where
  /-- `α j a i`: the factor in front of the `a`-th component of agent `j`'s signal in agent `i`'s
  utility -/
  α : ι → A → ι → ℝ
  /-- the density `fⁱ` of agent `i`'s signal -/
  f : ι → (A → ℝ) → ℝ
  α_ne_zero : ∀ j a i, α j a i ≠ 0
  f_pos : ∀ i, ∀ x ∈ cube A, 0 < f i x
  f_integrableOn : ∀ i, IntegrableOn (f i) (cube A)
  f_integral : ∀ i, ∫ x in cube A, f i x = 1

namespace Setting

variable (S : Setting ι A)

/-- The distribution of agent `i`'s signal: Lebesgue measure on `[0,1]^A` with density `fⁱ`. -/
noncomputable def marginal (i : ι) : Measure (A → ℝ) :=
  (volume.restrict (cube A)).withDensity fun x => ENNReal.ofReal (S.f i x)

/-- The joint distribution of the signal profile: signals are independent across agents. -/
noncomputable def prior : Measure (ι → A → ℝ) :=
  Measure.pi S.marginal

/-- Agent `i`'s utility (9.2) from alternative `a` at signal profile `θ`, before transfers:
`∑_j α^j_{ai} θ^j_a`. -/
def utility (i : ι) (a : A) (θ : ι → A → ℝ) : ℝ :=
  ∑ j, S.α j a i * θ j a

/-- Welfare of alternative `a` at signal profile `θ`: the sum of the agents' utilities (transfers
do not depend on the alternative and are left out). -/
def welfare (a : A) (θ : ι → A → ℝ) : ℝ :=
  ∑ i, S.utility i a θ

end Setting

/-- A direct mechanism (p.158): a choice rule `q` assigning to each reported signal profile a
probability vector `q θ` on `A`, and a transfer rule `t i` for every agent `i`. -/
structure Mechanism (ι A : Type*) where
  /-- the choice rule `q : [0,1]^{IK} → Δ(A)`; `q θ a` is the probability of alternative `a` -/
  q : (ι → A → ℝ) → A → ℝ
  /-- the transfer `tᵢ(θ)` paid by agent `i` -/
  t : ι → (ι → A → ℝ) → ℝ

/-- `q` is a choice rule: its value at every signal profile in `[0,1]^{IK}` is a probability
distribution on `A`. Measurability, which the book omits throughout (note 2 to Ch. 2), is made
explicit so that the interim probabilities are genuine integrals. -/
def IsChoiceRule (q : (ι → A → ℝ) → A → ℝ) : Prop :=
  Measurable q ∧ ∀ θ ∈ profiles ι A, (∀ a, 0 ≤ q θ a) ∧ ∑ a, q θ a = 1

namespace Setting

variable (S : Setting ι A)

/-- The interim probability `Qⁱ_a(x)` that alternative `a` is chosen when agent `i`'s signal is
`x` and the other agents' signals are drawn from their distributions. -/
noncomputable def interimProb (q : (ι → A → ℝ) → A → ℝ) (i : ι) (a : A) (x : A → ℝ) : ℝ :=
  ∫ θ, q (Function.update θ i x) a ∂S.prior

/-- A direct mechanism whose interim expectations exist: `q` is a choice rule and, for every agent
`i` and report `y ∈ [0,1]^A`, the transfer `tᵢ(y, θ₋ᵢ)` is integrable in `θ₋ᵢ`. -/
def IsDirect (M : Mechanism ι A) : Prop :=
  IsChoiceRule M.q ∧
    ∀ i, ∀ y ∈ cube A, Integrable (fun θ => M.t i (Function.update θ i y)) S.prior

/-- Agent `i`'s interim expected utility when his true signal is `x`, he reports `y`, and the other
agents report their signals truthfully. -/
noncomputable def expectedUtility (M : Mechanism ι A) (i : ι) (x y : A → ℝ) : ℝ :=
  ∫ θ, (∑ a, M.q (Function.update θ i y) a * S.utility i a (Function.update θ i x) -
      M.t i (Function.update θ i y)) ∂S.prior

/-- Bayesian incentive compatibility (p.158): for every agent `i` and all signals
`x, y ∈ [0,1]^A`, the expected utility of reporting `x` is at least that of reporting `y` when the
true signal is `x`. -/
def IsBIC (M : Mechanism ι A) : Prop :=
  ∀ i, ∀ x ∈ cube A, ∀ y ∈ cube A, S.expectedUtility M i x x ≥ S.expectedUtility M i x y

/-- A choice rule is first best (p.158) if for every `θ ∈ [0,1]^{IK}` it assigns positive
probability only to alternatives that maximize the sum of the agents' utilities. -/
def IsFirstBest (q : (ι → A → ℝ) → A → ℝ) : Prop :=
  ∀ θ ∈ profiles ι A, ∀ a, 0 < q θ a → ∀ b, S.welfare b θ ≤ S.welfare a θ

end Setting

end Interdependent

end MechanismDesign.Correlated


