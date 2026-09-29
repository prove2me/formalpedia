-- Prove2me | Definitions.Def_SocialEquilibrium_Existence_Game
-- name    : SocialEquilibrium_Existence_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:38:16.047774+00:00
-- url     : https://prove2.me/theorems/c3dc9ec5-d7b5-406c-a238-46290bb218cb
-- title:
--   Debreu's abstract economy: constrained best responses and equilibrium points
-- statement:
--   There are finitely many agents $\iota$. Agent $\iota$ chooses an action $a_\iota$ in a set $\mathfrak A_\iota\subseteq E_\iota$ of a real vector space $E_\iota$. A profile $a=(a_\iota)_\iota$ is an element of $\mathfrak A=\prod_\iota\mathfrak A_\iota$.
--
--   1. $\bar a_\iota$ denotes the actions of all agents other than $\iota$; it ranges over $\bar{\mathfrak A}_\iota=\prod_{j\ne\iota}\mathfrak A_j$. The profile obtained from $\bar a_\iota$ and an action $a_\iota$ of agent $\iota$ is written $(\bar a_\iota,a_\iota)$.
--   2. Given $\bar a_\iota$, the choice of agent $\iota$ is restricted to a set $A_\iota(\bar a_\iota)\subseteq\mathfrak A_\iota$. The payoff of agent $\iota$ is a function $f_\iota:\mathfrak A\to\overline{\mathbb R}$ into the completed real line.
--   3. The **best value** of agent $\iota$ against $\bar a_\iota$ is
--   $$\varphi_\iota(\bar a_\iota)=\sup_{a_\iota\in A_\iota(\bar a_\iota)} f_\iota(\bar a_\iota,a_\iota),$$
--   and the set of **constrained best responses** is
--   $$M_{\bar a_\iota}=\{a_\iota\in A_\iota(\bar a_\iota)\mid f_\iota(\bar a_\iota,a_\iota)=\varphi_\iota(\bar a_\iota)\}.$$
--   4. The multi-valued function $\phi$ on $\mathfrak A$ is $\phi(a)=M_{\bar a_1}\times\cdots\times M_{\bar a_\nu}$.
--   5. A profile $a^*$ is an **equilibrium point** if for every $\iota$, $a^*_\iota\in A_\iota(\bar a^*_\iota)$ and $f_\iota(a^*)=\max_{a_\iota\in A_\iota(\bar a^*_\iota)} f_\iota(\bar a^*_\iota,a_\iota)$.
--   6. $A_\iota$ is **continuous at** $\bar a^0_\iota$ if for every $a^0_\iota\in A_\iota(\bar a^0_\iota)$ and every sequence $\bar a^n_\iota\to\bar a^0_\iota$ there is a sequence $a^n_\iota\to a^0_\iota$ with $a^n_\iota\in A_\iota(\bar a^n_\iota)$ for all $n$.
--
--   These are the objects of Debreu's social equilibrium existence theorem, which generalizes Nash equilibrium to games in which each agent's feasible actions depend on the actions of the others.
--
--   **Formalization Note** $\bar{\mathfrak A}_\iota$ is the product over the subtype $\{j\mid j\ne\iota\}$, so a constraint map cannot depend on the agent's own action. Profiles and the others' actions carry the product of the subspace topologies. The completed real line is Mathlib's `EReal` with its order topology, which is the topology Debreu transports from $[-1,1]$. The best value is written as a supremum (`sSup`) in `EReal`; it equals Debreu's Max whenever the maximum is attained, as it is under the hypotheses of the theorems. An equilibrium point is stated as "$a^*_\iota\in A_\iota(\bar a^*_\iota)$ and $f_\iota(\bar a^*_\iota,b)\le f_\iota(a^*)$ for all $b\in A_\iota(\bar a^*_\iota)$", which is the same as $f_\iota(a^*)$ being the maximum.
-- source:
--   Debreu, A Social Equilibrium Existence Theorem, Proc. Natl. Acad. Sci. USA 38(10), 1952, pp. 888-889, §2 Equilibrium Points (model, Definition of equilibrium point, φ_ι, M_ā_ι, φ(a), continuity of A_ι)

import Mathlib

namespace SocialEquilibrium.Existence

open Filter Topology

variable {ι : Type*} [DecidableEq ι] {E : ι → Type*}

/-- Debreu (1952), §2, p. 888: given the action sets `𝔄_j = X j`, the set `𝔄̄_ι` of
`(ν − 1)`-tuples `ā_ι = (a_1, …, a_{ι−1}, a_{ι+1}, …, a_ν)` of actions of all agents other
than `ι`. -/
abbrev Others (X : ∀ i, Set (E i)) (i : ι) : Type _ :=
  ∀ j : {j // j ≠ i}, X j

/-- The actions `ā_ι` of all agents other than `ι` in the profile `a`. -/
def others (X : ∀ i, Set (E i)) (i : ι) (a : ∀ j, X j) : Others X i :=
  fun j => a j

/-- The profile `(ā_ι, a_ι)` obtained by joining the others' actions `ā_ι` with the action
`b = a_ι` of agent `ι`. -/
def join (X : ∀ i, Set (E i)) (i : ι) (ā : Others X i) (b : X i) : ∀ j, X j :=
  (Equiv.piSplitAt i (fun j => (X j : Type _))).symm (b, ā)

/-- Debreu (1952), §2, p. 888: `φ_ι(ā_ι) = Max_{a_ι ∈ A_ι(ā_ι)} f_ι(ā_ι, a_ι)`, the best payoff
available to agent `ι` when the others play `ā_ι`, written as a supremum in the completed real
line `EReal` (a complete lattice). -/
noncomputable def bestValue (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal) (i : ι) (ā : Others X i) : EReal :=
  sSup ((fun b => f i (join X i ā b)) '' A i ā)

/-- Debreu (1952), §2, p. 888: `M_{ā_ι} = {a_ι ∈ A_ι(ā_ι) | f_ι(ā_ι, a_ι) = φ_ι(ā_ι)}`, the set
of constrained best responses of agent `ι` to `ā_ι`. -/
def bestSet (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal) (i : ι) (ā : Others X i) : Set (X i) :=
  {b | b ∈ A i ā ∧ f i (join X i ā b) = bestValue X A f i ā}

/-- Debreu (1952), §2, p. 889: the multi-valued function `φ(a) = M_{ā_1} × ⋯ × M_{ā_ν}` on the
set of profiles `𝔄`. -/
def bestResponse (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal) (a : ∀ j, X j) : Set (∀ j, X j) :=
  {a' | ∀ i, a' i ∈ bestSet X A f i (others X i a)}

/-- Debreu (1952), §2, p. 888, Definition: `a*` is an *equilibrium point* if for every agent
`ι`, `a*_ι ∈ A_ι(ā*_ι)` and `f_ι(a*)` is the maximum of `f_ι(ā*_ι, a_ι)` over
`a_ι ∈ A_ι(ā*_ι)`. -/
def IsEquilibrium (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal) (a : ∀ j, X j) : Prop :=
  ∀ i, a i ∈ A i (others X i a) ∧
    ∀ b ∈ A i (others X i a), f i (join X i (others X i a) b) ≤ f i a

/-- Debreu (1952), §2, p. 889: the multi-valued function `A_ι` is *continuous* at `ā⁰_ι` if for
any `a⁰_ι ∈ A_ι(ā⁰_ι)` and any sequence `(āⁿ_ι)` converging to `ā⁰_ι` there is a sequence
`(aⁿ_ι)` converging to `a⁰_ι` with `aⁿ_ι ∈ A_ι(āⁿ_ι)` for all `n`. -/
def ConstraintContinuousAt {X : ∀ i, Set (E i)} [∀ i, TopologicalSpace (E i)]
    (A : ∀ i : ι, Others X i → Set (X i)) (i : ι) (ā₀ : Others X i) : Prop :=
  ∀ a₀ ∈ A i ā₀, ∀ ā : ℕ → Others X i, Tendsto ā atTop (𝓝 ā₀) →
    ∃ a : ℕ → X i, Tendsto a atTop (𝓝 a₀) ∧ ∀ n, a n ∈ A i (ā n)

end SocialEquilibrium.Existence


