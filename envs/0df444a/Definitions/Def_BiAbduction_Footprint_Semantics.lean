-- Prove2me | Definitions.Def_BiAbduction_Footprint_Semantics
-- name    : BiAbduction_Footprint_Semantics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:15.0243+00:00
-- url     : https://prove2.me/theorems/4afa67a2-ea3b-41a8-9be9-a8df06cb1f40
-- title:
--   §3.1.2, §3.3, Def. 3.9 — heaps, ∗, −∗, entailment, the orders ≤ and ≾, min, and best abductive solutions
-- statement:
--   This file fixes the storage model and the semantic predicates of §3.1.2 and §3.3 of Calcagno, Distefano, O'Hearn and Yang.
--
--   **Storage model.** Values are natural numbers; $0$ plays the role of nil and the **locations** are the nonzero naturals, a countably infinite set contained in the values. A **heap** $h$ is a *finite* partial map from locations to values, a **stack** $s$ maps every variable (a natural number) to a value, and a **state** is a pair $(s,h)$. A **predicate** is an arbitrary set of states, i.e. an element of $\mathcal P(\mathrm{States})$.
--
--   Write $h = h_0 \uplus h_1$ when $h_0$ and $h_1$ have disjoint domains and $h$ is their graph union, and $h' \subseteq h$ when $h'$ is a subheap of $h$ (every cell of $h'$ is a cell of $h$ with the same content).
--
--   **Connectives.** For predicates $F, G$:
--   1. $s,h \models \mathsf{emp}$ iff $h$ is empty, and $\mathsf{true}$ is the set of all states;
--   2. $s,h \models F * G$ iff $h = h_0 \uplus h_1$ with $s,h_0 \models F$ and $s,h_1 \models G$;
--   3. $s,h \models F \mathbin{-\!\!*} G$ iff for every $h'$ disjoint from $h$ with $s,h' \models F$, $s, h\uplus h' \models G$;
--   4. $F \models G$ iff every state satisfying $F$ satisfies $G$ (Definition 3.1).
--
--   **Orders.** The spatial preorder and the betterness order on predicates are
--   $$M \le M' \iff M' \models M * \mathsf{true}, \qquad M \precsim M' \iff (M \le M' \wedge M' \not\le M) \vee (M \le M' \wedge M' \le M \wedge M \models M').$$
--
--   **min (Definition 3.9).** $\min(F)$ is the set of states $(s,h)$ of $F$ such that every subheap $h' \subseteq h$ with $(s,h') \models F$ equals $h$.
--
--   **Abduction.** $M$ is a **solution** of the abduction question $F * M \models G$ ((3), p. 23) when $F * M \models G$, and the **best** (minimal w.r.t. $\precsim$) solution is a solution $M$ with $M \precsim M'$ for every solution $M'$, where $M'$ ranges over all predicates.
--
--   These objects are the semantic layer on which the paper's account of best abductive solutions (§3.3) and of footprints (§4.2.4) is stated.
--
--   **Formalization Note** Heaps are a structure with a cell map `ℕ → Option ℕ`, `cell 0 = none`, and a finite domain; finiteness is essential, since it makes the subheap order well founded. Program and logical variables are not distinguished: nothing in §3.3 or §4.2.4 depends on the distinction. Disjoint union is the relation `Heap.IsUnion h h₀ h₁` rather than a partial operation. "Minimal solution w.r.t. ≾" is encoded as the ≾-least solution (`IsLeastSolution`), which is how the proof of Theorem 3.13 uses it.
-- source:
--   Calcagno, Distefano, O'Hearn, Yang, Compositional Shape Analysis by means of Bi-Abduction, J. ACM (2011), pp. 14–15 (§3.1.2, Definition 3.1), p. 23 (§3.3, (3), ≤ and ≾), p. 24 (Definition 3.9)

import Mathlib

namespace BiAbduction.Footprint

/-!
Storage model and semantic predicates of Calcagno–Distefano–O'Hearn–Yang,
*Compositional Shape Analysis by means of Bi-Abduction*, J. ACM (2011), §3.1.2 (pp. 14–15),
§3.3 (p. 23) and Definition 3.9 (p. 24).

Conventions: values are natural numbers, `0` is nil and the locations are the nonzero naturals
(a countably infinite set included in the values); variables are natural numbers; a stack maps
every variable to a value; heaps are finite partial maps from locations to values.
-/

/-- A heap: a finite partial map from locations (nonzero naturals) to values (naturals).
`cell l = none` means that `l` is not allocated. -/
structure Heap where
  /-- the content of each address (`none` = unallocated) -/
  cell : ℕ → Option ℕ
  /-- nil (`0`) is not a location, so it is never allocated -/
  nil_unalloc : cell 0 = none
  /-- the domain is finite -/
  finite_dom : {l : ℕ | cell l ≠ none}.Finite

/-- Stacks map variables (natural numbers) to values. -/
abbrev Stack := ℕ → ℕ

/-- States are stack–heap pairs. -/
abbrev State := Stack × Heap

/-- Semantic predicates are arbitrary sets of states (p. 23: elements of `P(States)`). -/
abbrev Pred := Set State

/-- Two heaps have disjoint domains. -/
def Heap.Disjoint (h₀ h₁ : Heap) : Prop :=
  ∀ l, h₀.cell l = none ∨ h₁.cell l = none

/-- `h = h₀ ⊎ h₁`: the domains of `h₀` and `h₁` are disjoint and `h` is their graph union. -/
def Heap.IsUnion (h h₀ h₁ : Heap) : Prop :=
  Heap.Disjoint h₀ h₁ ∧ ∀ l, h.cell l = (h₀.cell l).or (h₁.cell l)

/-- `h'` is a subheap of `h` (`h' ⊆ h` as graphs). -/
def Heap.Subheap (h' h : Heap) : Prop :=
  ∀ l v, h'.cell l = some v → h.cell l = some v

/-- `emp`: the heap is empty. -/
def emp : Pred := {p | ∀ l, p.2.cell l = none}

/-- Separating conjunction `F ∗ G`. -/
def sepConj (F G : Pred) : Pred :=
  {p | ∃ h₀ h₁ : Heap, Heap.IsUnion p.2 h₀ h₁ ∧ (p.1, h₀) ∈ F ∧ (p.1, h₁) ∈ G}

/-- Separating implication `F −∗ G`: every separate heap satisfying `F`, added to the current
heap, gives a heap satisfying `G`. -/
def wand (F G : Pred) : Pred :=
  {p | ∀ h' hu : Heap, Heap.IsUnion hu p.2 h' → (p.1, h') ∈ F → (p.1, hu) ∈ G}

/-- Semantic entailment `F ⊨ G` (Definition 3.1): inclusion of sets of states. -/
def Entails (F G : Pred) : Prop := F ⊆ G

/-- The spatial preorder `M ≤ M'  :⇔  M' ⊨ M ∗ true` (p. 23). -/
def SpatialLe (M M' : Pred) : Prop := Entails M' (sepConj M Set.univ)

/-- The betterness order `M ≾ M'` (p. 23):
`(M ≤ M' ∧ M' ≰ M) ∨ (M ≤ M' ∧ M' ≤ M ∧ M ⊨ M')`. -/
def Better (M M' : Pred) : Prop :=
  (SpatialLe M M' ∧ ¬ SpatialLe M' M) ∨ (SpatialLe M M' ∧ SpatialLe M' M ∧ Entails M M')

/-- Definition 3.9: `min(F)`, the states of `F` no proper subheap of which (with the same stack)
satisfies `F`. -/
def minSet (F : Pred) : Pred :=
  {p | p ∈ F ∧ ∀ h' : Heap, Heap.Subheap h' p.2 → (p.1, h') ∈ F → h' = p.2}

/-- `M` is a solution of the abduction question `F ∗ M ⊨ G` ((3), p. 23). -/
def IsSolution (F G M : Pred) : Prop := Entails (sepConj F M) G

/-- `M` is the minimal (least) solution of `F ∗ ? ⊨ G` w.r.t. `≾`: it is a solution and it is
`≾`-below every solution, the competitors ranging over all predicates. -/
def IsLeastSolution (F G M : Pred) : Prop :=
  IsSolution F G M ∧ ∀ M' : Pred, IsSolution F G M' → Better M M'

end BiAbduction.Footprint


