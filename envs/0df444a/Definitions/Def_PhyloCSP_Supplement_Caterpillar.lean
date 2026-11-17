-- Prove2me | Definitions.Def_PhyloCSP_Supplement_Caterpillar
-- name    : PhyloCSP_Supplement_Caterpillar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:24:23.8862+00:00
-- url     : https://prove2.me/theorems/4b8a1a36-7da1-417c-ae69-4a16fc80ec49
-- title:
--   Caterpillars, caterpillar predicates, and conjunctions of split predicates
-- statement:
--   1. A **caterpillar** is a rooted binary tree whose internal nodes form a single path starting at the root (p.3). A pattern on $x_1,\dots,x_k$ is a caterpillar iff its leaves can be listed as $y_1,\dots,y_k$ so that $y_i\mid y_jy_l$ whenever $i<j$, $i<l$, $j\neq l$: $y_1$ splits off first, then $y_2$, and so on, the last two leaves forming the bottom cherry.
--   2. A predicate $\varphi$ of arity $k$ is a **caterpillar predicate** if it is satisfied by every labeled caterpillar on its variables, i.e. every caterpillar pattern on $x_1,\dots,x_k$ lies in $\mathrm{Sat}(\varphi)$ (p.13).
--   3. A predicate $\varphi$ of arity $k$ is a **conjunction of split predicates applied to subsets of its variables** if there are finitely many admissible pairs $(S,V)$ — $S$ a set of at least two of the variables, $V\subseteq S$ nonempty of even size — such that
--   $$
--   \mathrm{Sat}(\varphi)=\{P:\ P \text{ satisfies } \mathrm{split}_V \text{ on } S \text{ for every pair }(S,V)\}.
--   $$
--   The empty family (the always-true predicate) is allowed.
--
--   These are the two tractable cases (ii) and (i) of Theorem 5.2. On four leaves there are 12 caterpillar patterns $C_{ij}$ and 3 non-caterpillar (**balanced**) patterns $P_i$ (p.14).
--
--   **Formalization Note** On at most two leaves the condition of item 1 is empty, so the unique pattern is a caterpillar. Split predicates are the published `splitHolds` with admissible indices `IsSplitIndex`.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), caterpillars p.3 (PDF p.5); caterpillar predicates and Theorem 5.2 (i), p.13 (PDF p.15); Definition 5.3, p.13 (PDF p.15); balanced patterns p.14 (PDF p.16)

import Mathlib
import Definitions.Def_PhyloCSP_Predicate
import Definitions.Def_PhyloCSP_splitHolds

set_option autoImplicit false

namespace PhyloCSP

namespace Supplement

/-- **Caterpillars.**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), p.3 (PDF p.5): "A caterpillar is a rooted binary tree whose
internal nodes form a single path starting at the root."

A pattern on `x₁, …, x_k` is a caterpillar iff its leaves can be listed as `σ 0, σ 1, …, σ (k-1)`
so that `σ i` is the outgroup of every triple `{σ i, σ j, σ l}` with `i < j, l`: `σ 0` splits off
first, then `σ 1`, and so on, the last two leaves forming the bottom cherry.

**Formalization Note.** On at most two leaves the condition is empty: the unique pattern is a
caterpillar. Since a tree relation has exactly one outgroup per triple, the condition determines
the pattern from `σ`. "Labeled caterpillar on its variables" (p.13) is any caterpillar pattern on
`Fin k`. -/
def IsCaterpillar {k : ℕ} (P : Pattern (Fin k)) : Prop :=
  ∃ σ : Equiv.Perm (Fin k), ∀ i j l : Fin k, i < j → i < l → j ≠ l → P.1 (σ i) (σ j) (σ l) = true

/-- **Caterpillar predicates.** p.13 (PDF p.15): "We call a phylogenetic predicate a caterpillar
predicate if it is satisfied by every labeled caterpillar on its variables." -/
def IsCaterpillarPredicate {k : ℕ} (φ : Predicate k) : Prop :=
  ∀ P : Pattern (Fin k), IsCaterpillar P → P ∈ φ

/-- **Conjunctions of split predicates.** Theorem 5.2 (i), p.13 (PDF p.15): "Every predicate in Π
can be expressed as a conjunction of split predicates applied to subsets of its variables."

`φ` is a conjunction of split predicates if there is a finite family of admissible split indices
`(S, V)` (`IsSplitIndex`: `S` a set of at least two of the variables, `V ⊆ S` nonempty of even size)
such that `Sat(φ)` is exactly the set of patterns satisfying every `split_V` on `S`.

**Formalization Note.** The empty family (the always-true predicate, "An empty conjunction is the
always-true predicate", Definition 5.3) is allowed. -/
def IsSplitConjunction {k : ℕ} (φ : Predicate k) : Prop :=
  ∃ E : Finset (Finset (Fin k) × Finset (Fin k)),
    (∀ e ∈ E, IsSplitIndex e.1 e.2) ∧ φ = {P | ∀ e ∈ E, splitHolds P e.1 e.2}

end Supplement

end PhyloCSP


