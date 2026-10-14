-- Prove2me | Definitions.Def_FirstPriceLearning_Stochastic_ContextualBandit
-- name    : FirstPriceLearning_Stochastic_ContextualBandit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:17.673562+00:00
-- url     : https://prove2.me/theorems/7b59b363-cffd-4ae7-9ea8-07fe6f43e8c5
-- title:
--   Definitions 2–3, pp. 14, 16–17 — contextual bandits with graph feedback and cross learning; partially ordered contextual bandits
-- statement:
--   **Definition 2.** A stochastic contextual bandit with graph feedback and cross learning has a context set $\mathcal C$ with $|\mathcal C|=M$, an action set $\mathcal A$ with $|\mathcal A|=K$, a joint reward distribution $P$ supported on $[0,1]^{M\times K}$ with mean rewards $R_{c,a}=\mathbb E_P[r_{c,a}]$, and a directed feedback graph $G=(\mathcal A,E)$ without self-loops. In each round the learner sees a context $c_t$, picks $a_t$, nature draws $r_t\sim P$ iid, and the learner observes $r_{t,c,a}$ for **all** contexts $c$ and all $a\in I_t=\{a_t\}\cup\{a:(a_t,a)\in E\}$. The regret is
--
--   $$
--   R_T(\pi)=\sum_{t=1}^T\Big(\max_{a\in\mathcal A}R_{c_t,a}-R_{c_t,a_t}\Big). \qquad (5)
--   $$
--
--   **Definition 3.** The bandit is a **partially ordered contextual bandit** if (i) $G$ is a DAG equal to its transitive closure, which defines the partial order $a_1\preceq_G a_2\iff a_1=a_2$ or $(a_1,a_2)\in E$; and (ii) there is a partial order $\preceq_{\mathcal C}$ on $\mathcal C$ such that $c_1\preceq_{\mathcal C}c_2$ implies $a^\star(c_1)\preceq_G a^\star(c_2)$, where $a^\star(c)$ is an optimal action under context $c$.
--
--   The file also defines the hypotheses "the independence number of $G$ is at most $\alpha$" (every set of pairwise non-adjacent actions has at most $\alpha$ elements) and "the independence number of $(\mathcal C,\preceq_{\mathcal C})$ is at most $\beta$" (every set of pairwise incomparable contexts has at most $\beta$ elements, p. 18).
--
--   **Formalization Note.** $\mathcal C=$ `Fin M`, $\mathcal A=$ `Fin K`, and the graph is a relation `E`. "DAG equal to its transitive closure" is: `E` is transitive (it is irreflexive by Definition 2, hence acyclic). Since $\arg\max_a R_{c,a}$ need not be unique, condition (ii) is stated for **some selection** $a^\star(c)\in\arg\max_aR_{c,a}$. The independence numbers enter as upper bounds; every bound that uses them is increasing in them.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 14, Definition 2 and (5); pp. 16–17, Definition 3; p. 18 (independence number of a partial order)

import Mathlib

namespace FirstPriceLearning.Stochastic

open MeasureTheory

/-- Definition 2 (p. 14): a stochastic contextual bandit with graph feedback and cross learning,
with context space `𝒞 = Fin M` and action space `𝒜 = Fin K`. `P` is the joint law of one reward
vector `(r_{c,a})_{c ∈ 𝒞, a ∈ 𝒜}`, supported on `[0,1]^{M×K}`; `E` is the edge relation of the
directed feedback graph `G = (𝒜, E)`, without self-loops (p. 11). -/
structure ContextualBandit (M K : ℕ) where
  /-- The joint reward distribution. -/
  P : Measure (Fin M → Fin K → ℝ)
  isProb : IsProbabilityMeasure P
  supp : P {r | ∀ c a, r c a ∈ Set.Icc (0 : ℝ) 1}ᶜ = 0
  /-- The edges of the feedback graph: `E a a'` is the edge `(a, a')`. -/
  E : Fin K → Fin K → Prop
  noSelfLoop : ∀ a, ¬ E a a

namespace ContextualBandit

variable {M K : ℕ}

/-- The mean reward `R_{c,a} = 𝔼_P[r_{c,a}]`. -/
noncomputable def mean (B : ContextualBandit M K) (c : Fin M) (a : Fin K) : ℝ :=
  ∫ r, r c a ∂B.P

/-- The regret (5) of the action sequence `as` against the context sequence `cs`:
`R_T(π) = ∑_{t=1}^T (max_{a ∈ 𝒜} R_{c_t,a} - R_{c_t,a_t})`. -/
noncomputable def regret (B : ContextualBandit M K) {T : ℕ} (cs : Fin T → Fin M)
    (as : Fin T → Fin K) : ℝ :=
  ∑ t, ((⨆ a : Fin K, B.mean (cs t) a) - B.mean (cs t) (as t))

end ContextualBandit

/-- The order `⪯_G` on actions induced by the feedback graph (Definition 3): `a₁ ⪯_G a₂` iff
`a₁ = a₂` or `a₂` is a child of `a₁`. -/
def LeG {K : ℕ} (E : Fin K → Fin K → Prop) (a₁ a₂ : Fin K) : Prop :=
  a₁ = a₂ ∨ E a₁ a₂

/-- Definition 3 (pp. 16–17): a partially ordered contextual bandit, with the partial order
`leC` (`⪯_𝒞`) on the contexts.
* The feedback graph is a DAG equal to its own transitive closure: its edge relation is
  transitive (it is irreflexive by Definition 2, so it has no cycle).
* `leC` is a partial order, and some selection `a⋆(c) ∈ argmax_a R_{c,a}` of optimal actions is
  monotone: `c₁ ⪯_𝒞 c₂ → a⋆(c₁) ⪯_G a⋆(c₂)`. -/
structure IsPartiallyOrdered {M K : ℕ} (B : ContextualBandit M K)
    (leC : Fin M → Fin M → Prop) : Prop where
  trans : ∀ a₁ a₂ a₃, B.E a₁ a₂ → B.E a₂ a₃ → B.E a₁ a₃
  partialOrder : IsPartialOrder (Fin M) leC
  optimal_monotone : ∃ astar : Fin M → Fin K,
    (∀ c a, B.mean c a ≤ B.mean c (astar c)) ∧
    ∀ c₁ c₂, leC c₁ c₂ → LeG B.E (astar c₁) (astar c₂)

/-- `α` bounds the independence number of the feedback graph: every set of pairwise
non-adjacent actions has at most `α` elements. -/
def IndepNumberLe {K : ℕ} (E : Fin K → Fin K → Prop) (α : ℕ) : Prop :=
  ∀ S : Finset (Fin K), (∀ a ∈ S, ∀ a' ∈ S, ¬ E a a') → S.card ≤ α

/-- `β` bounds the independence number of the partial order `(𝒞, ⪯_𝒞)` (p. 18): every set of
pairwise incomparable contexts has at most `β` elements. -/
def OrderIndepNumberLe {M : ℕ} (leC : Fin M → Fin M → Prop) (β : ℕ) : Prop :=
  ∀ S : Finset (Fin M), (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ leC x y) → S.card ≤ β

end FirstPriceLearning.Stochastic


