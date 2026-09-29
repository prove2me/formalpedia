-- Prove2me | Definitions.Def_Aumann1974_TwoPerson_RandomizingStructure
-- name    : Aumann1974_TwoPerson_RandomizingStructure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T10:23:57.427501+00:00
-- url     : https://prove2.me/theorems/c082ec3d-5213-4ce1-8acb-e1c98921711c
-- title:
--   Aumann (1974), Sect. 3: randomizing structure, strategies, secret events, mixed and objective strategies, Assumption II
-- statement:
--   This bundle fixes the probabilistic half of Aumann's model of randomized strategies (Aumann 1974, Sect. 3, pp. 74–76, and Sect. 4, p. 77). Throughout, $N$ is a set of players.
--
--   1. **Randomizing structure.** A set $\Omega$ of *states of the world* with a $\sigma$-field $\mathcal B$ of *events*; for each player $i$ a sub-$\sigma$-field $\mathcal J_i \subseteq \mathcal B$ (the events regarding which $i$ is informed) and a probability measure $p_i$ on $(\Omega,\mathcal B)$ (the *subjective probability* of $i$). Note that $p_i$ is defined on all of $\mathcal B$, not only on $\mathcal J_i$.
--   2. **Strategy.** A (randomized) strategy of player $i$ is a function $s_i : \Omega \to S_i$ into a finite set that is measurable with respect to $\mathcal J_i$: every level set $\{s_i = a\}$ lies in $\mathcal J_i$.
--   3. **Independence.** Events $A_1,\dots,A_k$ are *$i$-independent* if $p_i(B_1\cap\dots\cap B_k) = p_i(B_1)\cdots p_i(B_k)$ whenever each $B_j$ is either $A_j$ or $\Omega$; they are *independent* if they are $i$-independent for every $i$.
--   4. **Secret events.** An event $A$ is *$i$-secret* if $A \in \mathcal J_i$ and, for every player $j \ne i$,
--   $$p_j(A\cap B) = p_j(A)\,p_j(B)\quad\text{for every } B \in \sigma\Big(\textstyle\bigcup_{k\ne i}\mathcal J_k\Big).$$
--   The family of $i$-secret events is $\mathcal S_i$.
--   5. **Mixed strategy.** A strategy $s_i$ is *mixed* if every level set $\{s_i = a\}$ is $i$-secret.
--   6. **Uncorrelated strategies.** $s_1,\dots,s_n$ are *uncorrelated* if for every pure profile $a$ the $n$ events $\{s_j = a_j\}$ are independent.
--   7. **Objective events and strategies.** An event $A$ is *objective* if all $p_i(A)$ coincide (their common value is the probability $p(A)$); a strategy is objective if all its level sets are objective.
--   8. **Non-atomicity and roulettes.** A measure $\mu$ is *non-atomic* on a $\sigma$-field $\mathcal R$ if every $A\in\mathcal R$ with $\mu(A)>0$ contains some $B\in\mathcal R$ with $0<\mu(B)<\mu(A)$. A *roulette* is a sub-$\sigma$-field $\mathcal R \subseteq \mathcal B$ on which every $p_j$ is non-atomic.
--   9. **Assumption II.** For each player $i$ there is a $\sigma$-field $\mathcal R_i$ of $i$-secret events on which every $p_j$ is non-atomic.
--
--   These are the objects about which Aumann's results on subjective and correlated randomization are stated; the payoffs and equilibrium points built on them are in the companion definition `Aumann1974.TwoPerson.Payoffs`.
--
--   **Formalization Note** Assumption I (preferences over lotteries are expected utility with a unique subjective probability $p_i$) is used by taking $p_i$ as data; the uniqueness clause is not encoded, since every statement concerns the given $p_i$. Non-atomicity is the standard notion restricted to $\mathcal R$, not Mathlib's `NoAtoms` (which only says singletons are null); the paper's gloss by finite partitions into events of arbitrarily small probability is equivalent. Measurability of a strategy into the finite set $S_i$ is stated through level sets. The $\sigma$-field $\mathcal B$ is an explicit parameter `mΩ` of the structure, so that other $\sigma$-fields ($\mathcal J_i$, a roulette) can be passed as arguments without being confused with $\mathcal B$.
-- source:
--   R. J. Aumann, Subjectivity and Correlation in Randomized Strategies, J. Math. Econ. 1 (1974) 67–96, https://doi.org/10.1016/0304-4068(74)90037-8, Sect. 3, pp. 74–76 (PDF pp. 8–10): items (5)–(7), randomized strategy, Assumption I, i-independence, i-secret events, Assumption II, mixed, uncorrelated, objective; Sect. 4, p. 77 (PDF p. 11): roulette

import Mathlib

/-!
# Aumann (1974), Sect. 3: the randomizing structure

R. J. Aumann, *Subjectivity and Correlation in Randomized Strategies*, J. Math. Econ. 1 (1974),
Sect. 3, pp. 74–76 (PDF pp. 8–10), and Sect. 4, p. 77 (PDF p. 11).

This bundle fixes the probabilistic half of Aumann's model: the states of the world `Ω` with the
σ-field `ℬ` of events, each player's information σ-field `𝒥ᵢ` and subjective probability `pᵢ`
(the triple is what the paper calls a *randomizing structure*, p. 78), strategies,
`i`-independence, `i`-secret events, mixed and objective strategies, non-atomicity, roulettes and
Assumption II.

**Formalization Note.** Players are an arbitrary type `ι` (the paper's `N = {1, …, n}`); finiteness
of `ι` is imposed where a statement needs it. `ℬ` is the `MeasurableSpace Ω` instance `mΩ` (an
implicit argument, so that σ-fields such as `𝒥ᵢ` or a roulette `ℛ` can be passed explicitly
without being mistaken for `ℬ`).
Probabilities are `ℝ≥0∞`-valued Mathlib measures, and every `pᵢ` is a probability measure.
-/

namespace Aumann1974.TwoPerson

open MeasureTheory

/-- **Randomizing structure** (Aumann 1974, J. Math. Econ. 1, Sect. 3, items (5)–(7) and
Assumption I, p. 74, PDF p. 8; the name is the paper's, p. 78, PDF p. 12).

The σ-field `mΩ` (a structure parameter) is the σ-field `ℬ` of *events* on the set `Ω` of
*states of the world* (item (5)). For each player `i`:
* `J i` is the sub-σ-field `𝒥ᵢ` of `ℬ` of events regarding which `i` is informed (item (6));
* `p i` is the subjective probability `pᵢ` of `i`, a probability measure on all of `ℬ`
  (Assumption I; footnote 11: "σ-additive non-negative measure with `pᵢ(Ω) = 1`").

**Formalization Note.** Assumption I says the preference order `≿ᵢ` of item (7) is represented
by a utility `uᵢ` and a *unique* `pᵢ`. The pair `(uᵢ, pᵢ)` is taken as data here (utilities
appear in `Aumann1974.TwoPerson.Payoffs`), and preferences are compared through expected
utility, exactly as the paper does from p. 76 on. The uniqueness clause is not encoded: it only
makes "the" subjective probability well defined, and footnote 12 notes it follows from
Assumption II anyway. -/
structure RandomizingStructure (ι : Type*) (Ω : Type*) (mΩ : MeasurableSpace Ω) where
  /-- The information σ-field `𝒥ᵢ` of player `i`. -/
  J : ι → MeasurableSpace Ω
  /-- `𝒥ᵢ` is a sub-σ-field of `ℬ`. -/
  J_le : ∀ i, J i ≤ mΩ
  /-- The subjective probability `pᵢ` of player `i`, defined on all of `ℬ`. -/
  p : ι → Measure Ω
  /-- Each `pᵢ` is a probability measure. -/
  isProb : ∀ i, IsProbabilityMeasure (p i)

attribute [instance] RandomizingStructure.isProb

variable {ι : Type*} {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Randomized strategy** (Aumann 1974, Sect. 3, p. 74, PDF p. 8): a strategy of player `i`
is a function `sᵢ : Ω → Sᵢ` that is measurable from `(Ω, 𝒥ᵢ)` to the finite set `Sᵢ`, i.e.
every level set `{sᵢ = a}` belongs to `𝒥ᵢ` ("`i` can peg his strategies only on events regarding
which he is informed").

**Formalization Note.** Measurability into a finite set is stated through the level sets, which
avoids choosing a `MeasurableSpace` instance on `Sᵢ`; with the discrete σ-algebra it is the same
notion. -/
def IsStrategy (R : RandomizingStructure ι Ω mΩ) (i : ι) {T : Type*} (s : Ω → T) : Prop :=
  ∀ a : T, MeasurableSet[R.J i] {ω | s ω = a}

/-- **`i`-independence of finitely many events** (Aumann 1974, Sect. 3, p. 75, PDF p. 9): the
events `A₁, …, A_k` are `i`-independent if `pᵢ(B₁ ∩ ⋯ ∩ B_k) = pᵢ(B₁)⋯pᵢ(B_k)` whenever each
`Bⱼ` is either `Aⱼ` or `Ω`. For two events this is `pᵢ(A ∩ B) = pᵢ(A)pᵢ(B)`.

**Formalization Note.** The events are indexed by an arbitrary finite type `κ`. -/
def IsIIndependent (R : RandomizingStructure ι Ω mΩ) (i : ι) {κ : Type*} [Fintype κ]
    (A : κ → Set Ω) : Prop :=
  ∀ B : κ → Set Ω, (∀ j, B j = A j ∨ B j = Set.univ) →
    R.p i (⋂ j, B j) = ∏ j, R.p i (B j)

/-- **Independent events** (Aumann 1974, Sect. 3, p. 75, PDF p. 9): events are independent if
they are `i`-independent for all players `i`. -/
def IsIndependent (R : RandomizingStructure ι Ω mΩ) {κ : Type*} [Fintype κ]
    (A : κ → Set Ω) : Prop :=
  ∀ i, IsIIndependent R i A

/-- **`i`-secret event** (Aumann 1974, Sect. 3, p. 75, PDF p. 9): an event `A` is `i`-secret if
it is in `𝒥ᵢ` and, for each player `j` other than `i`, it is `j`-independent of every event in
the σ-field generated by all the `𝒥_k` with `k ≠ i`, i.e. `pⱼ(A ∩ B) = pⱼ(A)pⱼ(B)` for all such
`B`. The family of `i`-secret events is the paper's `𝒮ᵢ`.

**Formalization Note.** The σ-field generated by the `𝒥_k`, `k ≠ i`, is the supremum
`⨆ k ≠ i, 𝒥_k` in the lattice of σ-algebras on `Ω`. No condition is placed on `pᵢ` itself. -/
def IsSecret (R : RandomizingStructure ι Ω mΩ) (i : ι) (A : Set Ω) : Prop :=
  MeasurableSet[R.J i] A ∧
    ∀ j, j ≠ i → ∀ B : Set Ω, MeasurableSet[⨆ (k : ι) (_ : k ≠ i), R.J k] B →
      R.p j (A ∩ B) = R.p j A * R.p j B

/-- **Mixed strategy** (Aumann 1974, Sect. 3, p. 75, PDF p. 9): a strategy `sᵢ` of `i` is mixed
if it is `𝒮ᵢ`-measurable, i.e. pegged on `i`-secret events: every level set `{sᵢ = a}` is
`i`-secret.

**Formalization Note.** `𝒮ᵢ` is the family of *all* `i`-secret events (not the σ-field `ℛᵢ` of
Assumption II). Since `i`-secret events lie in `𝒥ᵢ`, a mixed function is automatically a
strategy of `i`. -/
def IsMixed (R : RandomizingStructure ι Ω mΩ) (i : ι) {T : Type*} (s : Ω → T) : Prop :=
  ∀ a : T, IsSecret R i {ω | s ω = a}

/-- **Uncorrelated strategies** (Aumann 1974, Sect. 3, p. 75, PDF p. 9): strategies
`s₁, …, sₙ` are uncorrelated if for each pure profile `a ∈ S` the `n` events `{sⱼ = aⱼ}` are
independent (in the sense of `IsIndependent`). -/
def IsUncorrelated [Fintype ι] (R : RandomizingStructure ι Ω mΩ) {S : ι → Type*}
    (s : ∀ i, Ω → S i) : Prop :=
  ∀ a : ∀ i, S i, IsIndependent R (fun j => {ω | s j ω = a j})

/-- **Objective event** (Aumann 1974, Sect. 3, pp. 75–76, PDF pp. 9–10): an event is objective
if all the subjective probabilities `pᵢ(A)` coincide; the common value is its *probability*
`p(A)`. An event that is not objective is *subjective*. -/
def IsObjective (R : RandomizingStructure ι Ω mΩ) (A : Set Ω) : Prop :=
  ∀ i j, R.p i A = R.p j A

/-- **Objective strategy** (Aumann 1974, Sect. 3, p. 76, PDF p. 10): a strategy is objective if
it is pegged on objective events, i.e. every level set `{sᵢ = a}` is objective. -/
def IsObjectiveStrategy (R : RandomizingStructure ι Ω mΩ) {T : Type*} (s : Ω → T) : Prop :=
  ∀ a : T, IsObjective R {ω | s ω = a}

/-- **Non-atomic on a sub-σ-field** (Aumann 1974, Sect. 3, Assumption II, p. 75, PDF p. 9):
the measure `μ` is non-atomic on the σ-field `m` if every `m`-measurable set of positive measure
contains an `m`-measurable subset of strictly smaller positive measure.

**Formalization Note.** This is the standard notion of a non-atomic measure, applied to the
restriction of `μ` to `m`. It is *not* Mathlib's `NoAtoms` (which only says singletons are
null). The paper's gloss ("there exist finite partitions of `Ω` into `ℛᵢ`-events whose
`pⱼ`-probabilities are arbitrarily small") is an equivalent formulation for finite measures. -/
def NonAtomicOn (μ : Measure[mΩ] Ω) (m : MeasurableSpace Ω) : Prop :=
  ∀ A : Set Ω, MeasurableSet[m] A → 0 < μ A →
    ∃ B : Set Ω, MeasurableSet[m] B ∧ B ⊆ A ∧ 0 < μ B ∧ μ B < μ A

/-- **Roulette** (continuous chance device; Aumann 1974, Sect. 4, p. 77, PDF p. 11): a
sub-σ-field `ℛ` of `ℬ` on which each `pⱼ` is non-atomic. -/
def IsRoulette (R : RandomizingStructure ι Ω mΩ) (m : MeasurableSpace Ω) : Prop :=
  m ≤ mΩ ∧ ∀ j, NonAtomicOn (R.p j) m

/-- **Assumption II** (Aumann 1974, Sect. 3, p. 75, PDF p. 9; a standing assumption, "We
assume"): for each player `i` there is a σ-field `ℛᵢ` of `i`-secret events such that each `pⱼ`
is non-atomic on `ℛᵢ`.

**Formalization Note.** `ℛᵢ` is a σ-algebra on `Ω` all of whose measurable sets are `i`-secret;
in particular `ℛᵢ ≤ 𝒥ᵢ ≤ ℬ`, so `ℛᵢ` is an `i`-secret roulette. -/
def AssumptionII (R : RandomizingStructure ι Ω mΩ) : Prop :=
  ∀ i, ∃ m : MeasurableSpace Ω, (∀ A : Set Ω, MeasurableSet[m] A → IsSecret R i A) ∧
    ∀ j, NonAtomicOn (R.p j) m

end Aumann1974.TwoPerson


