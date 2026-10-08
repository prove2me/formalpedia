-- Prove2me | Definitions.Def_BiAbduction_Systematic_Semantics
-- name    : BiAbduction_Systematic_Semantics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:18.808913+00:00
-- url     : https://prove2.me/theorems/b76d7fb7-f8e2-4467-95b7-54207772c786
-- title:
--   §3.1.2, §3.3 — storage model, semantic predicates (∗, −∗, ∃, ∀), the orders ≤, ≾, ≤c, min, Elsewhere and subtraction
-- statement:
--   This file fixes the storage model of separation logic and the operations on **semantic predicates** used throughout §3.3–§3.4 of Calcagno, Distefano, O'Hearn and Yang.
--
--   **Storage model.** Values are natural numbers; $0$ is the value nil, and the **locations** are the nonzero naturals (a countably infinite set contained in the values). A **heap** $h$ is a finite partial map from locations to values, $\mathrm{Heap} = \mathrm{Loc}\rightharpoonup_{\mathrm{fin}}\mathrm{Val}$. A **stack** $s$ maps every variable to a value, and a **state** is a pair $(s,h)$. Two heaps are disjoint when their domains are disjoint, and $h = h_0\uplus h_1$ means that $h_0,h_1$ are disjoint and $h$ is their graph union. A heap $h'$ is a **subheap** of $h$ when its graph is contained in that of $h$.
--
--   **Predicates.** A predicate is an arbitrary set of states, $F\subseteq \mathrm{States}$. Negation, disjunction and conjunction are complement, union and intersection, $\mathsf{true}$ is the set of all states, and $F\models G$ is inclusion. Further,
--   $$s,h\models \mathsf{emp}\iff h=\emptyset,\qquad s,h\models F*G\iff \exists h_0,h_1.\ h=h_0\uplus h_1,\ s,h_0\models F,\ s,h_1\models G,$$
--   $$s,h\models F\mathbin{-\!\!*}G\iff \forall h'.\ (h\uplus h' \text{ defined and } s,h'\models F)\Rightarrow s,h\uplus h'\models G,$$
--   and $\exists X.F$, $\forall X.F$ quantify over the value of the variable $X$ in the stack.
--
--   **Orders and min.** The spatial preorder is $M\le M' \iff M'\models M*\mathsf{true}$, and the betterness order is
--   $$M\precsim M' \iff (M\le M'\wedge M'\not\le M)\ \vee\ (M\le M'\wedge M'\le M\wedge M\models M').$$
--   $\min(F)$ is the set of states $(s,h)\in F$ such that every subheap $h'$ of $h$ with $(s,h')\in F$ equals $h$ (Definition 3.9). $\mathrm{Elsewhere}(F)=\neg(F\mathbin{-\!\!*}\mathsf{false})$ ("some separate heap satisfies $F$") and the compatible preorder relative to $\Delta$ is $D\le_c D'\iff (D\wedge \mathrm{Elsewhere}(\Delta))\le(D'\wedge\mathrm{Elsewhere}(\Delta))$ (Definition 3.14). Subtraction is $F-G = F\wedge\neg((\neg\mathsf{emp})*G)$ (Definition 3.22), and "$X$ is not free in $F$" means that membership in $F$ does not depend on the value of $X$.
--
--   **Solutions.** $M$ is a solution of the abduction question $F*M\models G$ when $F*M\subseteq G$. It is the **minimal solution w.r.t. $\precsim$** when it is a solution and $M\precsim M'$ for every solution $M'$, where $M'$ ranges over all predicates. It is a **minimal solution w.r.t. $\le_c$** when it is a solution and $M\le_c M'$ (relative to $F$) for every solution $M'$.
--
--   These are the objects in which every statement of the mission is phrased.
--
--   **Formalization Note** Variables (program and logical) are natural numbers and a stack is a function $\mathbb N\to\mathbb N$. Heaps are functions $\mathbb N\to\mathrm{Option}\,\mathbb N$ with $0$ unallocated and finite domain. The union $h=h_0\uplus h_1$ is a relation (`Heap.IsUnion`), so $F\mathbin{-\!\!*}G$ quantifies over the separate heap $h'$ and its union with $h$.
-- source:
--   Calcagno, Distefano, O'Hearn, Yang, Compositional Shape Analysis by means of Bi-Abduction, J. ACM (2011), pp. 14–15 (§3.1.2, Definition 3.1), p. 23 (§3.3, ≤ and ≾), p. 24 (Definition 3.9), p. 26 (Definition 3.14), p. 32 (Definition 3.22)

import Mathlib

namespace BiAbduction.Systematic

/-!
Storage model and semantic predicates of Calcagno–Distefano–O'Hearn–Yang,
*Compositional Shape Analysis by means of Bi-Abduction*, §3.1.2 (pp. 14–15) and §3.3 (pp. 23–24),
Definition 3.9 (p. 24), Definition 3.14 (p. 26), Definition 3.22 (p. 32).

Conventions: values are natural numbers, `0` is nil and the locations are the nonzero naturals;
variables (program and logical) are natural numbers; a stack maps every variable to a value.
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

/-- Existential quantification `∃x. F` over the value of variable `x`. -/
def exQ (x : ℕ) (F : Pred) : Pred :=
  {p | ∃ v : ℕ, (Function.update p.1 x v, p.2) ∈ F}

/-- Universal quantification `∀x. F` over the value of variable `x`. -/
def allQ (x : ℕ) (F : Pred) : Pred :=
  {p | ∀ v : ℕ, (Function.update p.1 x v, p.2) ∈ F}

/-- Semantic entailment `F ⊨ G` (Definition 3.1). -/
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

/-- Definition 3.14: `Elsewhere(F) := ¬(F −∗ false)`, "some separate heap satisfies `F`". -/
def Elsewhere (F : Pred) : Pred := (wand F ∅)ᶜ

/-- Definition 3.14: the compatible preorder relative to `Δ`,
`D ≤c D'  :⇔  (D ∧ Elsewhere(Δ)) ≤ (D' ∧ Elsewhere(Δ))`. -/
def CompatLe (Δ D D' : Pred) : Prop :=
  SpatialLe (D ∩ Elsewhere Δ) (D' ∩ Elsewhere Δ)

/-- `M` is a solution of the abduction question `F ∗ M ⊨ G` ((3), (5)). -/
def IsSolution (F G M : Pred) : Prop := Entails (sepConj F M) G

/-- `M` is the minimal (least) solution of `F ∗ ? ⊨ G` w.r.t. `≾`: it is a solution and it is
`≾`-below every solution, the competitors ranging over all predicates. -/
def IsLeastSolution (F G M : Pred) : Prop :=
  IsSolution F G M ∧ ∀ M' : Pred, IsSolution F G M' → Better M M'

/-- `D` is a minimal solution of `Δ ∗ ? ⊨ H` w.r.t. `≤c`: a solution that is `≤c`-below every
solution (all predicates). -/
def IsCompatMinSolution (Δ H D : Pred) : Prop :=
  IsSolution Δ H D ∧ ∀ F : Pred, IsSolution Δ H F → CompatLe Δ D F

/-- Definition 3.22: subtraction `F − G := F ∧ ¬((¬emp) ∗ G)`. -/
def subP (F G : Pred) : Pred := F ∩ (sepConj empᶜ G)ᶜ

/-- p. 32: "`X` is not free in `F`": membership in `F` does not depend on the value of `X`. -/
def NotFree (X : ℕ) (F : Pred) : Prop :=
  ∀ (s : Stack) (h : Heap) (v : ℕ), (s, h) ∈ F ↔ (Function.update s X v, h) ∈ F

end BiAbduction.Systematic


