-- Prove2me | Definitions.Def_Aumann1974_ZeroSum_RandomizingStructure
-- name    : Aumann1974_ZeroSum_RandomizingStructure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:00:30.912781+00:00
-- url     : https://prove2.me/theorems/7885d1fc-7185-492b-977b-259869ec319d
-- title:
--   Aumann (1974), Sects. 3–4: randomizing structure, strategies, secret, objective, subjective and public events, roulettes, Assumption II
-- statement:
--   This bundle fixes the probabilistic half of Aumann's model of randomized strategies (Aumann 1974, Sect. 3, pp. 74–76, and Sect. 4, p. 77), as it is used in the paper's treatment of two-person zero-sum games. Throughout, $N$ is a set of players.
--
--   1. **Randomizing structure.** A set $\Omega$ of *states of the world* with a $\sigma$-field $\mathcal B$ of *events*; for each player $i$ a sub-$\sigma$-field $\mathcal J_i \subseteq \mathcal B$ (the events regarding which $i$ is informed) and a probability measure $p_i$ on $(\Omega,\mathcal B)$ (the *subjective probability* of $i$). Each $p_i$ is defined on all of $\mathcal B$, not only on $\mathcal J_i$.
--   2. **Strategy.** A (randomized) strategy of player $i$ is a function $s_i : \Omega \to S_i$ into a finite set that is measurable with respect to $\mathcal J_i$: every level set $\{s_i = a\}$ lies in $\mathcal J_i$.
--   3. **Independence.** Two events $A, B$ are *independent* if $p_i(A\cap B) = p_i(A)\,p_i(B)$ for every player $i$.
--   4. **Secret events.** An event $A$ is *$i$-secret* if $A \in \mathcal J_i$ and, for every player $j \ne i$,
--   $$p_j(A\cap B) = p_j(A)\,p_j(B)\quad\text{for every } B \in \sigma\Big(\textstyle\bigcup_{k\ne i}\mathcal J_k\Big).$$
--   5. **Objective and subjective events.** An event $A$ is *objective* if all $p_i(A)$ coincide (their common value is the probability $p(A)$), and *subjective* otherwise; for two players, $A$ is subjective iff $p_1(A)\ne p_2(A)$.
--   6. **Non-atomicity and roulettes.** A measure $\mu$ is *non-atomic* on a $\sigma$-field $\mathcal R$ if every $A\in\mathcal R$ with $\mu(A)>0$ contains some $B\in\mathcal R$ with $0<\mu(B)<\mu(A)$. A *roulette* is a sub-$\sigma$-field $\mathcal R \subseteq \mathcal B$ on which every $p_j$ is non-atomic.
--   7. **Public events.** An event is *public* if it belongs to every $\mathcal J_i$, i.e. to $S_N=\bigcap_{i\in N}\mathcal J_i$; a *public roulette* is a roulette consisting of public events.
--   8. **Assumption II.** For each player $i$ there is a $\sigma$-field $\mathcal R_i$ of $i$-secret events on which every $p_j$ is non-atomic.
--
--   These are the objects about which the zero-sum results of the paper are stated; payoffs and the value of the game are in the companion definition `Aumann1974.ZeroSum.Payoffs`.
--
--   **Formalization Note** Assumption I (preferences over lotteries are expected utility with a unique subjective probability $p_i$) is used by taking $p_i$ as data; the uniqueness clause is not encoded. Non-atomicity is the standard notion restricted to $\mathcal R$, not Mathlib's `NoAtoms` (which only says singletons are null). Measurability of a strategy into the finite set $S_i$ is stated through level sets. The $\sigma$-field $\mathcal B$ is an explicit parameter `mΩ` of the structure. A public event is additionally required to be in $\mathcal B$, which matters only when there are no players. The same notions are defined, with the same meaning, in the companion mission's `Aumann1974.TwoPerson.RandomizingStructure`.
-- source:
--   R. J. Aumann, Subjectivity and Correlation in Randomized Strategies, J. Math. Econ. 1 (1974) 67–96, https://doi.org/10.1016/0304-4068(74)90037-8, Sect. 3, pp. 74–76 (PDF pp. 8–10): items (5)–(7), randomized strategy, Assumption I, i-independence, i-secret events, Assumption II, objective and subjective events; Sect. 4, p. 77 (PDF p. 11): public events, roulette, public roulette

import Mathlib

/-!
# Aumann (1974), Sects. 3–4: the randomizing structure (zero-sum mission)

R. J. Aumann, *Subjectivity and Correlation in Randomized Strategies*, J. Math. Econ. 1 (1974),
Sect. 3, pp. 74–76 (PDF pp. 8–10), and Sect. 4, p. 77 (PDF p. 11).

This bundle fixes the probabilistic half of Aumann's model as used in Sect. 6: the states of the
world `Ω` with the σ-field `ℬ` of events, each player's information σ-field `𝒥ᵢ` and subjective
probability `pᵢ`, strategies, independence of two events, `i`-secret events, objective and
subjective events, non-atomicity, roulettes, public events, public roulettes and Assumption II.

**Formalization Note.** Players are an arbitrary type `ι` (the paper's `N = {1, …, n}`); finiteness
of `ι` is imposed where a statement needs it. `ℬ` is the σ-field `mΩ`, an explicit parameter of the
structure, so that σ-fields such as `𝒥ᵢ` or a roulette `ℛ` can be passed explicitly without being
mistaken for `ℬ`. Probabilities are `ℝ≥0∞`-valued Mathlib measures, and every `pᵢ` is a
probability measure. The meaning of every shared notion is identical to the Sect. 3 bundle of the
companion mission (`Aumann1974.TwoPerson.RandomizingStructure`).
-/

namespace Aumann1974.ZeroSum

open MeasureTheory

/-- **Randomizing structure** (Aumann 1974, J. Math. Econ. 1, Sect. 3, items (5)–(7) and
Assumption I, p. 74, PDF p. 8; the name is the paper's, p. 78, PDF p. 12).

The σ-field `mΩ` (a structure parameter) is the σ-field `ℬ` of *events* on the set `Ω` of
*states of the world* (item (5)). For each player `i`:
* `J i` is the sub-σ-field `𝒥ᵢ` of `ℬ` of events regarding which `i` is informed (item (6));
* `p i` is the subjective probability `pᵢ` of `i`, a probability measure on all of `ℬ`
  (Assumption I; "Note that `pᵢ` is defined on all of `ℬ`, not only on `𝒥ᵢ`", p. 75).

**Formalization Note.** Assumption I says the preference order `≿ᵢ` of item (7) is represented
by a utility `uᵢ` and a *unique* `pᵢ`. The pair `(uᵢ, pᵢ)` is taken as data here (utilities
appear in `Aumann1974.ZeroSum.Payoffs`), and preferences are compared through expected utility,
exactly as the paper does from p. 76 on. The uniqueness clause is not encoded: every statement
concerns the given `pᵢ`. -/
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
every level set `{sᵢ = a}` belongs to `𝒥ᵢ`.

**Formalization Note.** Measurability into a finite set is stated through the level sets, which
avoids choosing a `MeasurableSpace` instance on `Sᵢ`; with the discrete σ-algebra it is the same
notion. -/
def IsStrategy (R : RandomizingStructure ι Ω mΩ) (i : ι) {T : Type*} (s : Ω → T) : Prop :=
  ∀ a : T, MeasurableSet[R.J i] {ω | s ω = a}

/-- **Independence of two events** (Aumann 1974, Sect. 3, p. 75, PDF p. 9): `A` and `B` are
`i`-independent if `pᵢ(A ∩ B) = pᵢ(A)pᵢ(B)`, and *independent* if they are `i`-independent for
every player `i`. -/
def IsIndependentOf (R : RandomizingStructure ι Ω mΩ) (A B : Set Ω) : Prop :=
  ∀ i, R.p i (A ∩ B) = R.p i A * R.p i B

/-- **`i`-secret event** (Aumann 1974, Sect. 3, p. 75, PDF p. 9): an event `A` is `i`-secret if
it is in `𝒥ᵢ` and, for each player `j` other than `i`, it is `j`-independent of every event in
the σ-field generated by all the `𝒥_k` with `k ≠ i`, i.e. `pⱼ(A ∩ B) = pⱼ(A)pⱼ(B)` for all such
`B`.

**Formalization Note.** The σ-field generated by the `𝒥_k`, `k ≠ i`, is the supremum
`⨆ k ≠ i, 𝒥_k` in the lattice of σ-algebras on `Ω`. No condition is placed on `pᵢ` itself. -/
def IsSecret (R : RandomizingStructure ι Ω mΩ) (i : ι) (A : Set Ω) : Prop :=
  MeasurableSet[R.J i] A ∧
    ∀ j, j ≠ i → ∀ B : Set Ω, MeasurableSet[⨆ (k : ι) (_ : k ≠ i), R.J k] B →
      R.p j (A ∩ B) = R.p j A * R.p j B

/-- **Objective event** (Aumann 1974, Sect. 3, pp. 75–76, PDF pp. 9–10): an event is objective
if all the subjective probabilities `pᵢ(A)` coincide; the common value is its *probability*
`p(A)`. -/
def IsObjective (R : RandomizingStructure ι Ω mΩ) (A : Set Ω) : Prop :=
  ∀ i j, R.p i A = R.p j A

/-- **Subjective event** (Aumann 1974, Sect. 3, p. 76, PDF p. 10): "An event or strategy is
called subjective if it is not objective." For two players this says `p₁(A) ≠ p₂(A)`. -/
def IsSubjective (R : RandomizingStructure ι Ω mΩ) (A : Set Ω) : Prop :=
  ¬ IsObjective R A

/-- **Non-atomic on a sub-σ-field** (Aumann 1974, Sect. 3, Assumption II, p. 75, PDF p. 9):
the measure `μ` is non-atomic on the σ-field `m` if every `m`-measurable set of positive measure
contains an `m`-measurable subset of strictly smaller positive measure.

**Formalization Note.** This is the standard notion of a non-atomic measure, applied to the
restriction of `μ` to `m`. It is *not* Mathlib's `NoAtoms` (which only says singletons are
null). -/
def NonAtomicOn (μ : Measure[mΩ] Ω) (m : MeasurableSpace Ω) : Prop :=
  ∀ A : Set Ω, MeasurableSet[m] A → 0 < μ A →
    ∃ B : Set Ω, MeasurableSet[m] B ∧ B ⊆ A ∧ 0 < μ B ∧ μ B < μ A

/-- **Roulette** (continuous chance device; Aumann 1974, Sect. 4, p. 77, PDF p. 11): a
sub-σ-field `ℛ` of `ℬ` on which each `pⱼ` is non-atomic. -/
def IsRoulette (R : RandomizingStructure ι Ω mΩ) (m : MeasurableSpace Ω) : Prop :=
  m ≤ mΩ ∧ ∀ j, NonAtomicOn (R.p j) m

/-- **Public event** (Aumann 1974, Sect. 4, p. 77, PDF p. 11): the members of
`S_N = ⋂_{i ∈ N} 𝒥ᵢ` are called public events — events regarding which every player is
informed.

**Formalization Note.** The clause `MeasurableSet[mΩ] A` records that a public event is an event
(it matters only when there are no players). -/
def IsPublic (R : RandomizingStructure ι Ω mΩ) (A : Set Ω) : Prop :=
  MeasurableSet[mΩ] A ∧ ∀ i, MeasurableSet[R.J i] A

/-- **Public roulette** (Aumann 1974, Sect. 4, p. 77, PDF p. 11): a roulette `ℛ` that consists
of public events. -/
def IsPublicRoulette (R : RandomizingStructure ι Ω mΩ) (m : MeasurableSpace Ω) : Prop :=
  IsRoulette R m ∧ ∀ A : Set Ω, MeasurableSet[m] A → IsPublic R A

/-- **Assumption II** (Aumann 1974, Sect. 3, p. 75, PDF p. 9; a standing assumption, "We
assume"): for each player `i` there is a σ-field `ℛᵢ` of `i`-secret events such that each `pⱼ`
is non-atomic on `ℛᵢ`.

**Formalization Note.** `ℛᵢ` is a σ-algebra on `Ω` all of whose measurable sets are `i`-secret;
in particular `ℛᵢ ≤ 𝒥ᵢ ≤ ℬ`, so `ℛᵢ` is a roulette. -/
def AssumptionII (R : RandomizingStructure ι Ω mΩ) : Prop :=
  ∀ i, ∃ m : MeasurableSpace Ω, (∀ A : Set Ω, MeasurableSet[m] A → IsSecret R i A) ∧
    ∀ j, NonAtomicOn (R.p j) m

end Aumann1974.ZeroSum


