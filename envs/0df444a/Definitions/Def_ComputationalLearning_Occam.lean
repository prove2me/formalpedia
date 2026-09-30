-- Prove2me | Definitions.Def_ComputationalLearning_Occam
-- name    : ComputationalLearning_Occam
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T03:03:18.86123+00:00
-- url     : https://prove2.me/theorems/23f1f5e7-fa4b-445f-b51b-c597f1dba133
-- title:
--   Chapter 2: the set cover problem, opt and the greedy heuristic; k-decision lists, their evaluation, useful conditions and the greedy decision-list algorithm
-- statement:
--   The objects of Chapter 2, on the framework of Mission I.
--
--   **Occam algorithms (§2.1).** Hypotheses are represented by binary strings (`List Bool`, size = length) through a representation map $R$ to concepts; an $(\alpha, \beta)$-Occam algorithm outputs, on a sample of $m$ examples labeled by $c$, a string $r$ with $R(r)$ consistent with the sample and $|r| \le (n \cdot \mathrm{size}(c))^\alpha m^\beta$. Theorems 2.1 and 2.2 are stated directly in these terms (no new definition).
--
--   **Set cover (§2.3).** For a finite universe $U$ and a collection $\mathcal{S}$ of subsets, `IsCover 𝒮 T` says $T \subseteq \mathcal{S}$ covers $U$; `optCover 𝒮` is $\mathrm{opt}(\mathcal{S})$, the cardinality of a minimum cover ($0$ if there is none); for a sequence of sets $t$, `uncovered t i` is the set of elements not in $t_0 \cup \dots \cup t_{i-1}$; `IsGreedySequence 𝒮 t` says every $t_i \in \mathcal{S}$ covers at least as many still-uncovered elements as any set of $\mathcal{S}$ (the greedy heuristic, ties arbitrary).
--
--   **$k$-decision lists (§2.4).** A condition is a conjunction of $k$ literals `Condition n k := Fin k → Fin n × Bool` (fewer by repetition), holding in $a$ iff all its literals do (`evalCondition`); a $k$-decision list is a list of (condition, bit) items with a default bit (`DecisionList n k`), evaluated as the bit of the first satisfied condition, the default if none (`evalDL`); `decisionListClass n k` is the class of their concepts. For a sample $S$ and a set $R$ of remaining example indices, `satisfying S R c` is the book's $S_z$ (the remaining examples satisfying $c$), and `IsUseful S R c b` says it is nonempty and all its examples are labeled $b$. `IsGreedyPrefix S steps R` is the relation "after choosing the items `steps` in order, each useful on the examples remaining at that moment and removing the examples it satisfies, the remaining examples are $R$"; `IsGreedyOutput S L` says the items of $L$ form such a run that has consumed every example (the default bit is then unused).
--
--   **Conventions.** Logarithms natural; the greedy relations allow arbitrary tie-breaking, so the theorems quantify over every run.
-- source:
--   Kearns and Vazirani, An Introduction to Computational Learning Theory, MIT Press 1994, doi:10.7551/mitpress/3897.001.0001, Chapter 2: §2.1 Occam algorithms, Definition 6 (p. 33), §2.3 the set cover problem and the greedy heuristic (pp. 38-39), §2.4 k-decision lists and the greedy algorithm (pp. 42-44)

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_ComputationalLearning_PAC

/-!
# Kearns and Vazirani, Chapter 2: Occam's Razor

Kearns and Vazirani, *An Introduction to Computational Learning Theory*, MIT Press 1994,
doi:10.7551/mitpress/3897.001.0001, Chapter 2 (pp. 31–48).

**Occam learning (§2.1).** An *Occam algorithm* takes a labeled sample of cardinality `m` and
outputs a hypothesis that is consistent with the sample and *short*: an `(α, β)`-Occam algorithm
(Definition 6, p. 33) outputs `h` with `size(h) ≤ (n · size(c))^α m^β`, `α ≥ 0`, `0 ≤ β < 1`,
where `size(h)` is the bit length of the representation. Theorem 2.1 (Occam's Razor) says that
such an algorithm is a PAC learning algorithm; Theorem 2.2 (cardinality version, p. 35) is the
form used in applications: an algorithm that outputs a consistent hypothesis from a finite
class `H_{n,m}` has error at most `ε` with confidence `1 − δ` once
`m ≥ (1/(bε))(log |H_{n,m}| + log(1/δ))`. Both are stated on the framework of
`Def_ComputationalLearning_PAC`; representations of hypotheses are binary strings `List Bool`
with a representation map to concepts.

**The set cover problem and the greedy heuristic (§2.3, pp. 38–39).** Given a collection `𝒮` of
subsets of a finite universe `U` that covers `U`, the greedy heuristic repeatedly picks a set
covering the most uncovered elements; after `i` steps at most `(1 − 1/opt(𝒮))^i |U|` elements
are uncovered, so `opt(𝒮) log |U|` sets suffice (Chvátal).

**Decision lists (§2.4, pp. 42–44).** A `k`-decision list is an ordered sequence
`(c₁, b₁), …, (c_l, b_l)` and a default bit `b`, each `cⱼ` a conjunction of at most `k` literals;
its value on `a` is the bit of the first satisfied condition, `b` if none is. The Occam algorithm
of Theorem 2.3 repeatedly finds a *useful* condition (satisfied by some remaining examples, all
with the same label), appends it with that label and removes those examples, until no example
is left.
-/

open MeasureTheory

namespace ComputationalLearning

/-! ### The greedy set cover heuristic (§2.3) -/

section SetCover

variable {U : Type*} [DecidableEq U] [Fintype U]

/-- `T ⊆ 𝒮` is a cover of the universe: every element lies in some set of `T`. -/
def IsCover (𝒮 T : Finset (Finset U)) : Prop :=
  T ⊆ 𝒮 ∧ ∀ u : U, ∃ t ∈ T, u ∈ t

/-- `opt(𝒮)`, the number of sets in a minimum cardinality cover (p. 39); `0` if `𝒮` is not a
cover, by the convention of `sInf` on the empty set. -/
noncomputable def optCover (𝒮 : Finset (Finset U)) : ℕ :=
  sInf {k | ∃ T, IsCover 𝒮 T ∧ T.card = k}

/-- The elements not covered by the first `i` sets `t 0, …, t (i-1)` of a sequence of sets. -/
def uncovered (t : ℕ → Finset U) (i : ℕ) : Finset U :=
  Finset.univ.filter (fun u ↦ ∀ j < i, u ∉ t j)

/-- The sequence `t` is a run of the **greedy heuristic** on `𝒮` (p. 39): each `t i` is a set of
`𝒮` covering at least as many of the elements still uncovered after `i` steps as any set of
`𝒮` (ties broken arbitrarily). -/
def IsGreedySequence (𝒮 : Finset (Finset U)) (t : ℕ → Finset U) : Prop :=
  ∀ i, t i ∈ 𝒮 ∧ ∀ s ∈ 𝒮, (s ∩ uncovered t i).card ≤ (t i ∩ uncovered t i).card

end SetCover

/-! ### Decision lists and the greedy decision-list algorithm (§2.4) -/

section DecisionLists

variable {n k : ℕ}

/-- A condition of a `k`-decision list: a conjunction of `k` literals over `x₁, …, xₙ` (fewer
literals by repetition). -/
abbrev Condition (n k : ℕ) := Fin k → Fin n × Bool

/-- The condition holds in `a` iff all its literals do. -/
def evalCondition (t : Condition n k) (a : Cube (Fin n)) : Bool :=
  decide (∀ i, a (t i).1 = (t i).2)

/-- A `k`-decision list: the ordered sequence of (condition, bit) items and the default bit. -/
abbrev DecisionList (n k : ℕ) := List (Condition n k × Bool) × Bool

/-- `L(a)`: the bit of the first item whose condition holds in `a`, the default bit if none does
(p. 42). -/
def evalDL (L : DecisionList n k) (a : Cube (Fin n)) : Bool :=
  match L.1.find? (fun p ↦ evalCondition p.1 a) with
  | some p => p.2
  | none => L.2

/-- The representation class of `k`-decision lists over `x₁, …, xₙ`. -/
def decisionListClass (n k : ℕ) : Set (Cube (Fin n) → Bool) :=
  {h | ∃ L : DecisionList n k, h = evalDL L}

/-- The examples (indices) among `R` whose instance satisfies the condition `c`, the book's
`S_z` (p. 44). -/
def satisfying {m : ℕ} (S : Fin m → Cube (Fin n) × Bool) (R : Finset (Fin m))
    (c : Condition n k) : Finset (Fin m) :=
  R.filter (fun j ↦ evalCondition c (S j).1 = true)

/-- The condition `c` is **useful** on the remaining examples `R` with the label `b` (p. 44): it is
satisfied by some remaining example, and every remaining example satisfying it is labeled `b`. -/
def IsUseful {m : ℕ} (S : Fin m → Cube (Fin n) × Bool) (R : Finset (Fin m)) (c : Condition n k)
    (b : Bool) : Prop :=
  (satisfying S R c).Nonempty ∧ ∀ j ∈ satisfying S R c, (S j).2 = b

/-- A prefix of a run of the greedy decision-list algorithm on the sample `S`: the items chosen so
far and the set `R` of examples still remaining. It starts from the empty list with all examples
remaining, and each step appends a useful condition with its label and removes the examples it
satisfies. -/
inductive IsGreedyPrefix {m : ℕ} (S : Fin m → Cube (Fin n) × Bool) :
    List (Condition n k × Bool) → Finset (Fin m) → Prop
  | nil : IsGreedyPrefix S [] Finset.univ
  | cons {steps : List (Condition n k × Bool)} {R : Finset (Fin m)} {c : Condition n k} {b : Bool} :
      IsGreedyPrefix S steps R → IsUseful S R c b →
      IsGreedyPrefix S (steps ++ [(c, b)]) (R \ satisfying S R c)

/-- `L` is an **output of the greedy decision-list algorithm** on `S`: a run that has consumed
every example (the default bit is then never used and is arbitrary). -/
def IsGreedyOutput {m : ℕ} (S : Fin m → Cube (Fin n) × Bool) (L : DecisionList n k) : Prop :=
  IsGreedyPrefix S L.1 ∅

end DecisionLists

end ComputationalLearning


