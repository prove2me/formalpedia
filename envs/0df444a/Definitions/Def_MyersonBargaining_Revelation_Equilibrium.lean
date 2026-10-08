-- Prove2me | Definitions.Def_MyersonBargaining_Revelation_Equilibrium
-- name    : MyersonBargaining_Revelation_Equilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:30.486987+00:00
-- url     : https://prove2.me/theorems/7dfbeb84-d0e0-4087-83a6-24be69026af2
-- title:
--   Response plans, the payoffs W (12)-(13), response-plan equilibria (14), the set F** (15), the induced mechanism and the honest plans
-- statement:
--   Section 3 of the paper lets the arbitrator use a choice mechanism $\pi$ on arbitrary nonempty finite **response sets** $S_1,\dots,S_n$.
--
--   A **response plan** for player $i$ assigns to each type $a_i\in A_i$ a probability distribution over $S_i$: $\sigma_i(s_i\mid a_i)\ge 0$ and $\sum_{s_i'\in S_i}\sigma_i(s_i'\mid a_i)=1$ for every $a_i$. If the players follow plans $\sigma_1,\dots,\sigma_n$ under the mechanism $\pi$, the conditionally expected payoff of player $i$ of type $a_i$ is
--
--   $$
--   W_i(\pi,\sigma_1,\dots,\sigma_n\mid a_i)=\sum_{\alpha}\sum_{s\in S_1\times\cdots\times S_n}\sum_{c\in C}P_i(\alpha\mid a_i)\Big(\prod_{j=1}^n\sigma_j(s_j\mid\alpha_j)\Big)\pi(c\mid s)\,U_i(c,\alpha),
--   $$
--
--   and $W(\pi,\sigma_1,\dots,\sigma_n)$ is the vector of these numbers indexed by the disjoint union of the $A_i$.
--
--   The profile $(\sigma_1,\dots,\sigma_n)$ is a **response-plan equilibrium** for $\pi$ if for every player $i$, every type $a_i$ and every alternative response plan $\sigma_i'$,
--
--   $$
--   W_i(\pi,\sigma_1,\dots,\sigma_n\mid a_i)\ge W_i(\pi,\sigma_1,\dots,\sigma_{i-1},\sigma_i',\sigma_{i+1},\dots,\sigma_n\mid a_i).
--   $$
--
--   The set of **equilibrium-feasible** allocation vectors is
--
--   $$
--   F^{**}=\{W(\pi,\sigma_1,\dots,\sigma_n):\ \pi\text{ is a choice mechanism and }(\sigma_1,\dots,\sigma_n)\text{ is a response-plan equilibrium for }\pi\},
--   $$
--
--   where the response sets of $\pi$ range over all families of nonempty finite sets.
--
--   Two auxiliary constructions appear in the proof of Theorem 2. A mechanism $\pi$ and plans $\sigma$ induce the direct mechanism
--
--   $$
--   \pi'(c\mid\alpha)=\sum_{s\in S_1\times\cdots\times S_n}\pi(c\mid s)\prod_{i=1}^n\sigma_i(s_i\mid\alpha_i),
--   $$
--
--   and on the standard response sets $S_i=A_i$ the **honest** plans are $\sigma_i'(b_i\mid a_i)=1$ if $b_i=a_i$ and $0$ otherwise.
--
--   **Formalization Note** Plans and mechanisms take the event first and the condition second, as in $\sigma_i(s_i\mid a_i)$ and $\pi(c\mid s)$. The product in $W$ runs over all players, player $i$'s own plan included, evaluated at the profile $\alpha$; the paper prints $\sigma_j(s_j\mid a_j)$ there, a slip for $\alpha_j$ (only $a_i$ is in scope, and the induced mechanism on p. 66 uses $\alpha_i$). Deviations in the equilibrium condition range over all response plans, mixed ones included, compared type by type. Membership in $F^{**}$ requires that $\pi$ satisfy (2) and that every $\sigma_i$ be a response plan, and quantifies over response sets in the universe `Type` with `Fintype` and `Nonempty` instances.
-- source:
--   Myerson, Incentive compatibility and the bargaining problem, Econometrica 47 (1979), pp. 65-67, Section 3, Eqs. (12)-(15)

import Mathlib
import Definitions.Def_MyersonBargaining_NashSolution_Model

namespace MyersonBargaining.Revelation

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]

/-- Section 3, p. 65: a response plan `τ s a` = σ_i(s|a) gives, for every type `a`,
a probability distribution over the responses `s`. -/
def IsResponsePlan {Si Ai : Type} [Fintype Si] (τ : Si → Ai → ℝ) : Prop :=
  (∀ s a, 0 ≤ τ s a) ∧ ∀ a, ∑ s, τ s a = 1

/-- Equations (12)–(13): the interim payoff vector W(π, σ_1, …, σ_n), indexed by
player and type, when the players follow the response plans `σ`. -/
noncomputable def W (G : MyersonBargaining.NashSolution.Problem ι A C) {S : ι → Type} [∀ i, Fintype (S i)]
    (π : C → (∀ i, S i) → ℝ) (σ : ∀ i, S i → A i → ℝ) : (Σ i, A i) → ℝ :=
  fun k => ∑ α, ∑ s, ∑ c,
    MyersonBargaining.NashSolution.cond G.P k.1 α k.2 * (∏ j, σ j (s j) (α j)) * π c s * G.U k.1 c α

/-- Equation (14): `σ` is a response-plan equilibrium for `π` — no player type gains by
replacing the player's response plan by any other response plan. -/
def IsResponsePlanEq (G : MyersonBargaining.NashSolution.Problem ι A C) {S : ι → Type} [∀ i, Fintype (S i)]
    (π : C → (∀ i, S i) → ℝ) (σ : ∀ i, S i → A i → ℝ) : Prop :=
  ∀ i (a : A i) (τ : S i → A i → ℝ), IsResponsePlan τ →
    W G π (Function.update σ i τ) ⟨i, a⟩ ≤ W G π σ ⟨i, a⟩

/-- Equation (15): the equilibrium-feasible allocation vectors, over choice mechanisms on
arbitrary nonempty finite response sets. -/
def FStarStar (G : MyersonBargaining.NashSolution.Problem ι A C) : Set ((Σ i, A i) → ℝ) :=
  {x | ∃ (S : ι → Type) (_ : ∀ i, Fintype (S i)) (_ : ∀ i, Nonempty (S i))
    (π : C → (∀ i, S i) → ℝ) (σ : ∀ i, S i → A i → ℝ),
    MyersonBargaining.NashSolution.IsChoiceMechanism π ∧ (∀ i, IsResponsePlan (σ i)) ∧ IsResponsePlanEq G π σ ∧
      W G π σ = x}

/-- Section 3, p. 66: the direct mechanism π′(c|α) = Σ_s π(c|s) ∏_i σ_i(s_i|α_i)
induced by `π` and the response plans `σ`. -/
noncomputable def induced {S : ι → Type} [∀ i, Fintype (S i)]
    (π : C → (∀ i, S i) → ℝ) (σ : ∀ i, S i → A i → ℝ) : C → (∀ i, A i) → ℝ :=
  fun c α => ∑ s, π c s * ∏ i, σ i (s i) (α i)

/-- Section 3, p. 67: the honest response plans σ′_i(b|a) = 1 if b = a, 0 otherwise,
on the standard response sets. -/
def honest : ∀ i, A i → A i → ℝ :=
  fun _ b a => if b = a then 1 else 0

end MyersonBargaining.Revelation


