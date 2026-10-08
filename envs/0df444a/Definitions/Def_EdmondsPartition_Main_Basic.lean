-- Prove2me | Definitions.Def_EdmondsPartition_Main_Basic
-- name    : EdmondsPartition_Main_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:51:46.096507+00:00
-- url     : https://prove2.me/theorems/f6c206d4-2400-497e-aee4-b1b4d9d00495
-- title:
--   §1.1, §1.3–§1.5, pp. 67–70 — Axiom 2, circuits, Axiom 2', circuit axioms 1c/2c, spans, the span S(A), partitions into k independent sets
-- statement:
--   This file fixes the objects of Edmonds's 1965 paper on matroid partition. Let $M$ be a finite set of elements and let a family of subsets of $M$ be called *independent*. Axiom 1 (every subset of an independent set is independent) and the rank $r(A)$, the largest cardinality of an independent subset of $A$, are imported from Whitney's postulates.
--
--   1. **Maximal independent subsets.** $I$ is a maximal independent set contained in $A$ if $I\subseteq A$, $I$ is independent, and no independent $J$ with $I\subseteq J\subseteq A$ is larger than $I$.
--   2. **Axiom 2.** For any subset $A$, all maximal independent sets contained in $A$ have the same number of elements. A *matroid* is a system satisfying Axioms 1 and 2.
--   3. **Circuits.** A circuit is a minimal dependent set: $C$ is not independent, but every proper subset of $C$ is.
--   4. **Axiom 2'.** For any independent set $I$ and any element $e$, the set $I\cup\{e\}$ contains at most one circuit.
--   5. **Circuit axioms.** For a family $\mathcal C$ of sets called circuits: **Axiom 1c**, no circuit contains a different circuit; **Axiom 2c**, if distinct circuits $C_1, C_2$ both contain $e$, then $(C_1\cup C_2)\setminus\{e\}$ contains a circuit. Starting from circuits, a set is independent when it contains no circuit.
--   6. **Spans.** A span (closed set) $S$ is a set such that no circuit contains exactly one element not in $S$:
--   $$|C\setminus S|\neq 1\quad\text{for every circuit } C.$$
--   The span $S(A)$ of $A$ is the minimal span containing $A$, here the intersection of all spans containing $A$ (the whole of $M$ is one).
--   7. **Partitions into $k$ independent sets.** A family $I_1,\dots,I_k$ of mutually disjoint independent sets whose union is $M$; any number of the $I_i$ may be empty.
--
--   These are the objects of THEOREM 1 and of the lemmas (PROPOSITIONS 1–5) used to prove it.
--
--   **Formalization Note** The elements form a finite type $\alpha$, and $M$ is `Finset.univ`; a submatroid $A$ is just a `Finset α`. Axiom 1 is Whitney's `IndepI1` and the rank is Whitney's `rankOfIndep`, an integer. The page's formula for spans reads "$|S\cap C|\neq 1$", which contradicts the words before it and the later use in PROPOSITION 4 ($C-A=e$); the words, $|C\setminus S|\neq 1$, are formalized. A partition is an indexed family `Fin k → Finset α` of pairwise disjoint independent sets covering `univ`, with empty parts allowed.
-- source:
--   Edmonds, Minimum partition of a matroid into independent subsets, J. Res. NBS 69B (1965), pp. 67–70, Axioms 1, 2 (§1.1), §1.4 (2), (3), Axioms 2', 1c, 2c (§1.5); partition from THEOREM 1 (p. 69) and §1.6 (p. 71)

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates

namespace EdmondsPartition.Main

open WhitneyMatroid.RankIndep

variable {α : Type*} [DecidableEq α]

/-- §1.1, p. 68: `I` is a maximal independent set contained in `A`. -/
def IsMaxIndepIn (Indep : Finset α → Prop) (A I : Finset α) : Prop :=
  I ⊆ A ∧ Indep I ∧ ∀ J : Finset α, I ⊆ J → J ⊆ A → Indep J → J = I

/-- AXIOM 2, §1.1, p. 68: for any subset `A` of the elements, all maximal independent sets
contained in `A` contain the same number of elements. -/
def Axiom2 (Indep : Finset α → Prop) : Prop :=
  ∀ A I J : Finset α, IsMaxIndepIn Indep A I → IsMaxIndepIn Indep A J → I.card = J.card

/-- §1.4 (2), p. 69: a circuit is a minimal dependent set (dependent = not independent). -/
def IsCircuit (Indep : Finset α → Prop) (C : Finset α) : Prop :=
  ¬ Indep C ∧ ∀ D : Finset α, D ⊂ C → Indep D

/-- AXIOM 2', §1.5, p. 70: the union of any independent set `I` and any element `e` contains
at most one circuit. -/
def Axiom2' (Indep : Finset α → Prop) : Prop :=
  ∀ (I : Finset α) (e : α), Indep I → ∀ C₁ C₂ : Finset α,
    IsCircuit Indep C₁ → IsCircuit Indep C₂ → C₁ ⊆ insert e I → C₂ ⊆ insert e I → C₁ = C₂

/-- AXIOM 1c, §1.5, p. 70, for a family `Circ` of "circuits": no circuit contains another
(different) circuit. -/
def Axiom1c (Circ : Finset α → Prop) : Prop :=
  ∀ C₁ C₂ : Finset α, Circ C₁ → Circ C₂ → C₁ ⊆ C₂ → C₁ = C₂

/-- AXIOM 2c, §1.5, p. 70: if distinct circuits `C₁`, `C₂` both contain an element `e`, then
`C₁ ∪ C₂ − e` contains a circuit. -/
def Axiom2c (Circ : Finset α → Prop) : Prop :=
  ∀ (C₁ C₂ : Finset α) (e : α), Circ C₁ → Circ C₂ → C₁ ≠ C₂ → e ∈ C₁ → e ∈ C₂ →
    ∃ C : Finset α, Circ C ∧ C ⊆ (C₁ ∪ C₂).erase e

/-- PROPOSITION 2, §1.5, p. 70: starting with circuits, the independent sets are the sets
containing no circuit. -/
def indepOfCircuits (Circ : Finset α → Prop) (I : Finset α) : Prop :=
  ∀ C : Finset α, Circ C → ¬ C ⊆ I

/-- §1.4 (3), p. 69: a span (closed set) `S` is a set such that no circuit contains exactly
one element not in `S`. (The words of the page; the printed formula `|S ∩ C| ≠ 1` is a
misprint.) -/
def IsSpan (Indep : Finset α → Prop) (S : Finset α) : Prop :=
  ∀ C : Finset α, IsCircuit Indep C → (C \ S).card ≠ 1

open Classical in
/-- §1.4, p. 69: the span `S(A)` of `A`, the minimal span containing `A`, taken as the
intersection of all spans containing `A` (`Finset.univ` is one of them). -/
noncomputable def spanOf [Fintype α] (Indep : Finset α → Prop) (A : Finset α) : Finset α :=
  (Finset.univ.powerset.filter (fun S => A ⊆ S ∧ IsSpan Indep S)).inf id

/-- THEOREM 1, p. 69, and §1.6, p. 71: `I : Fin k → Finset α` partitions the elements
`Finset.univ` into `k` mutually disjoint independent sets; any number of them may be empty. -/
def IsPartitionInto [Fintype α] (Indep : Finset α → Prop) (k : ℕ) (I : Fin k → Finset α) :
    Prop :=
  (∀ i, Indep (I i)) ∧ (Set.univ : Set (Fin k)).PairwiseDisjoint I ∧
    Finset.univ.biUnion I = Finset.univ

end EdmondsPartition.Main


