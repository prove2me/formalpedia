-- Prove2me | Definitions.Def_FirstPriceLearning_ContextLowerBound_Model
-- name    : FirstPriceLearning_ContextLowerBound_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:32:35.179553+00:00
-- url     : https://prove2.me/theorems/abc89945-ac25-4e4b-a5f2-1e9c3d199966
-- title:
--   Contextual bandits with graph feedback and cross learning, partial orders, policies and regret (5)
-- statement:
--   This file sets up the bandit model of §3.2–§3.3 of Han, Zhou and Weissman.
--
--   **Instances (Definition 2).** There are $M$ contexts $\mathcal C$, a finite action set $\mathcal A$ of size $K$, a joint reward distribution $P$ supported on $[0,1]^{\mathcal C\times\mathcal A}$ with mean rewards $R_{c,a}=\mathbb E_{r\sim P}[r_{c,a}]$, and a directed feedback graph $G=(\mathcal A,E)$ without self-loops. A set of actions is *independent* if no edge joins two of its members, and $G$ has *independence number* $\alpha$ if the largest independent set has exactly $\alpha$ elements. Likewise a partial order $(\mathcal C,\preceq_{\mathcal C})$ has independence number $\beta$ if the largest set of pairwise incomparable elements has exactly $\beta$ elements.
--
--   **Partially ordered contextual bandits (Definition 3).** The instance is partially ordered if (i) $G$ is a DAG equal to its own transitive closure, which induces the partial order $a_1\preceq_G a_2 \iff a_1=a_2$ or $(a_1,a_2)\in E$; and (ii) there is a partial order $\preceq_{\mathcal C}$ on the contexts and a choice of optimal actions $a^\star(c)\in\arg\max_a R_{c,a}$ with
--   $$c_1\preceq_{\mathcal C}c_2 \implies a^\star(c_1)\preceq_G a^\star(c_2).$$
--
--   **Interaction.** At round $t$ the learner sees the context $c_t$ (the context sequence is fixed in advance, i.e. oblivious), chooses $a_t$, and nature draws $r_t\sim P$ independently across rounds; the learner observes $(r_{t,c,a})_{c\in\mathcal C,\,a\in I_t}$ with $I_t=\{a_t\}\cup\{a:(a_t,a)\in E\}$, under *every* context (cross learning). A policy is randomized and non-anticipating: $a_t$ is a measurable function of the learner's internal randomness $u\sim\mu_U$, of $c_1,\dots,c_t$, and of the observations of rounds $1,\dots,t-1$. The regret (5) is
--   $$R_T(\pi)=\sum_{t=1}^T\Big(\max_{a\in\mathcal A}R_{c_t,a}-R_{c_t,a_t}\Big),$$
--   and $\mathbb E[R_T(\pi)]$ averages over the internal randomness and the reward vectors.
--
--   These objects are the common language of the paper's upper bounds (Theorems 4, 5) and of the lower bound of Theorem 6.
--
--   **Formalization Note.** Contexts are `Fin M` and rounds `Fin T` (paper index $=$ Lean index $+1$). Condition (i) is encoded as "no self-loops and transitive", which is equivalent to "a DAG equal to its transitive closure". The printed $a^\star(c):=\arg\max_a R_{c,a}$ is read as a selection of maximisers (it need not be unique). The observation of a round is the reward vector with unrevealed coordinates set to $0$; since the learner knows its own action, hence which coordinates are revealed, this carries exactly the revealed rewards. Policies take their internal randomness from an arbitrary probability space and must be measurable.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 14, Definition 2 and (5); pp. 16–17, Definition 3; p. 11 and p. 18 (independence numbers)

import Mathlib
import Definitions.Def_FirstPriceLearning_GraphFeedback_FeedbackGraph

open MeasureTheory

namespace FirstPriceLearning.ContextLowerBound

/-! Stochastic contextual bandits with graph feedback and cross learning (Definition 2, p. 14),
partially ordered contextual bandits (Definition 3, pp. 16–17), independence numbers (pp. 11, 18),
non-anticipating randomized policies, the interaction and the expected regret (5).

Contexts are `Fin M` (paper context `c ∈ [M]` is Lean `c + 1`), actions a finite type `A`,
rounds `Fin T` (paper time `t ∈ [T]` is Lean `t + 1`). A reward vector is an element of
`Fin M → A → ℝ`, i.e. `(r_{c,a})_{c ∈ C, a ∈ A}`. -/

/-- Definition 2: `P` is a joint reward law on `[0,1]^{C × A}` (a probability measure carried by
`[0,1]^{M × K}`) and the feedback graph `E` on the actions has no self-loops. -/
def IsGraphContextualBandit {M : ℕ} {A : Type} (E : A → A → Prop)
    (P : Measure (Fin M → A → ℝ)) : Prop :=
  IsProbabilityMeasure P ∧
  P {x | ∀ c a, x c a ∈ Set.Icc (0 : ℝ) 1}ᶜ = 0 ∧
  ∀ a, ¬ E a a

/-- The mean reward `R_{c,a} = ∫ r_{c,a} dP`. -/
noncomputable def meanReward {M : ℕ} {A : Type} (P : Measure (Fin M → A → ℝ))
    (c : Fin M) (a : A) : ℝ :=
  ∫ x, x c a ∂P

/-- The optimal mean reward `max_{a ∈ A} R_{c,a}` under context `c` (a maximum over the finite
action set). -/
noncomputable def optReward {M : ℕ} {A : Type} (P : Measure (Fin M → A → ℝ)) (c : Fin M) : ℝ :=
  ⨆ a : A, meanReward P c a

/-- `E` has independence number `α` (p. 11): the largest independent set has exactly `α`
elements. -/
def HasIndependenceNumber {A : Type} (E : A → A → Prop) (α : ℕ) : Prop :=
  (∃ S : Finset A, FirstPriceLearning.GraphFeedback.IsIndependentSet E S ∧ S.card = α) ∧
  ∀ S : Finset A, FirstPriceLearning.GraphFeedback.IsIndependentSet E S → S.card ≤ α

/-- A set `S` is an antichain of the relation `le`: any two distinct members are incomparable. -/
def IsAntichainOf {X : Type} (le : X → X → Prop) (S : Finset X) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ le x y ∧ ¬ le y x

/-- The partial order `(X, le)` has independence number `β` (p. 18): the largest set of pairwise
incomparable elements has exactly `β` elements. -/
def HasOrderIndependenceNumber {X : Type} (le : X → X → Prop) (β : ℕ) : Prop :=
  (∃ S : Finset X, IsAntichainOf le S ∧ S.card = β) ∧
  ∀ S : Finset X, IsAntichainOf le S → S.card ≤ β

/-- Definition 3 (partially ordered contextual bandit), for the Definition-2 instance `(E, P)`
and the relation `leC` on the contexts:
* `E` is a DAG whose transitive closure is itself: no self-loops (part of Definition 2) and
  transitive, which together exclude every directed cycle; the induced partial order is
  `a₁ ⪯_G a₂ ↔ a₁ = a₂ ∨ E a₁ a₂`;
* `leC` is a partial order on `C`, and there is a selection `a⋆(c)` of maximisers of
  `a ↦ R_{c,a}` with `c₁ ⪯_C c₂ → a⋆(c₁) ⪯_G a⋆(c₂)` (slip 3 of the plan: the printed
  `arg max` is read as such a selection). -/
def IsPartiallyOrderedContextualBandit {M : ℕ} {A : Type} (E : A → A → Prop)
    (P : Measure (Fin M → A → ℝ)) (leC : Fin M → Fin M → Prop) : Prop :=
  IsGraphContextualBandit E P ∧
  (∀ a b d, E a b → E b d → E a d) ∧
  IsPartialOrder (Fin M) leC ∧
  ∃ astar : Fin M → A,
    (∀ c a, meanReward P c a ≤ meanReward P c (astar c)) ∧
    ∀ c₁ c₂, leC c₁ c₂ → (astar c₁ = astar c₂ ∨ E (astar c₁) (astar c₂))

open Classical in
/-- What the learner observes when it chooses `a` and nature draws the reward vector `x`:
the rewards `(x_{c,b})_{c ∈ C, b ∈ I}` under **every** context `c` (cross learning), the other
coordinates being masked to `0`. The learner knows its own action, hence the mask, so this vector
carries exactly the revealed rewards. -/
noncomputable def reveal {M : ℕ} {A : Type} (E : A → A → Prop) (a : A)
    (x : Fin M → A → ℝ) : Fin M → A → ℝ :=
  fun c b => if FirstPriceLearning.GraphFeedback.Revealed E a b then x c b else 0

/-- A non-anticipating randomized policy with internal randomness in `U`. At round `t` (Lean
index) it reads its internal randomness `u`, the contexts `c_1, …, c_{t+1}` revealed so far
(including the current one) and the observations of the `t` earlier rounds, and returns an action.
The dependence on nothing else is enforced by the argument types. -/
structure Policy (M : ℕ) (A : Type) (U : Type) [MeasurableSpace A] [MeasurableSpace U] where
  act : (t : ℕ) → U → (Fin (t + 1) → Fin M) → (Fin t → Fin M → A → ℝ) → A
  measurable_act : ∀ t, Measurable
    (fun p : U × (Fin (t + 1) → Fin M) × (Fin t → Fin M → A → ℝ) => act t p.1 p.2.1 p.2.2)

variable {M : ℕ} {A U : Type} [MeasurableSpace A] [MeasurableSpace U]

/-- The observations of the first `t` rounds, by recursion on `t`, when the policy `π` runs with
internal randomness `u`, oblivious context sequence `c` and reward vectors `r` (one per round). -/
noncomputable def observations (E : A → A → Prop) (π : Policy M A U) {T : ℕ}
    (c : Fin T → Fin M) (u : U) (r : Fin T → Fin M → A → ℝ) :
    (t : ℕ) → t ≤ T → (Fin t → Fin M → A → ℝ)
  | 0, _ => fun i => i.elim0
  | t + 1, h =>
      let prev := observations E π c u r t (Nat.le_of_succ_le h)
      let a := π.act t u (fun i => c ⟨i.val, by omega⟩) prev
      Fin.snoc prev (reveal E a (r ⟨t, h⟩))

/-- The action `a_t` chosen at round `t`. -/
noncomputable def action (E : A → A → Prop) (π : Policy M A U) {T : ℕ}
    (c : Fin T → Fin M) (u : U) (r : Fin T → Fin M → A → ℝ) (t : Fin T) : A :=
  π.act t.val u (fun i => c ⟨i.val, by omega⟩) (observations E π c u r t.val (Nat.le_of_lt t.isLt))

/-- The regret (5) of an action sequence `a` against the context sequence `c`:
`R_T = ∑_{t=1}^T (max_a R_{c_t,a} − R_{c_t,a_t})`. -/
noncomputable def regret (P : Measure (Fin M → A → ℝ)) {T : ℕ} (c : Fin T → Fin M)
    (a : Fin T → A) : ℝ :=
  ∑ t, (optReward P (c t) - meanReward P (c t) (a t))

/-- The joint law of the internal randomness and the reward vectors: `u ∼ μU` independent of
`r_1, …, r_T` iid `∼ P`. -/
noncomputable def interactionLaw (μU : Measure U) (P : Measure (Fin M → A → ℝ)) (T : ℕ) :
    Measure (U × (Fin T → Fin M → A → ℝ)) :=
  μU.prod (Measure.pi fun _ : Fin T => P)

/-- The expected regret `𝔼[R_T(π)]` of the policy `π` (internal randomness `μU`) on the instance
`(E, P)` against the oblivious context sequence `c`. -/
noncomputable def expectedRegret (E : A → A → Prop) (P : Measure (Fin M → A → ℝ))
    (μU : Measure U) (π : Policy M A U) {T : ℕ} (c : Fin T → Fin M) : ℝ :=
  ∫ ω, regret P c (fun t => action E π c ω.1 ω.2 t) ∂(interactionLaw μU P T)

end FirstPriceLearning.ContextLowerBound


