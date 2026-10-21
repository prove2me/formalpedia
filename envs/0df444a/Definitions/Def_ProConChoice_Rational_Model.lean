-- Prove2me | Definitions.Def_ProConChoice_Rational_Model
-- name    : ProConChoice_Rational_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:32.385934+00:00
-- url     : https://prove2.me/theorems/381521f9-d45b-43bf-9826-31eef4de57a1
-- title:
--   §2.1 and Definition 1, p. 5 — choice functions, orderings, pro-con models, Pros/Cons and pro-con rationality
-- statement:
--   The deterministic pro-con model of Dogan and Yildiz.
--
--   Let $X$ be a finite set of alternatives with $n = |X|$. A **choice set** is a nonempty subset $S \subseteq X$, and a **choice function** $C$ assigns to every choice set $S$ an alternative $C(S) \in S$.
--
--   An **ordering** of $X$ is a complete, transitive and antisymmetric binary relation $\succ$ on $X$, that is, a strict linear order. For a choice set $S$, $\max(S, \succ)$ is the $\succ$-top-ranked alternative of $S$, the unique $x \in S$ with $x \succ y$ for every other $y \in S$.
--
--   A **pro-con model** is a pair $\langle \succ, \rhd\rangle$ of two finite **sets** of orderings, the pro-orderings $\succ = \{\succ_1, \dots, \succ_m\}$ and the con-orderings $\rhd = \{\rhd_1, \dots, \rhd_q\}$, with no ordering in both sets. For a choice set $S$ and $x \in S$,
--   $$\mathrm{Pros}(x, S) = \{\succ_i \in \succ \,:\, x = \max(S, \succ_i)\}, \qquad \mathrm{Cons}(x, S) = \{\rhd_i \in \rhd \,:\, x = \max(S, \rhd_i)\}.$$
--   A con for $x$ at $S$ is a con-ordering whose **top** element on $S$ is $x$.
--
--   **Definition 1.** A choice function $C$ is **pro-con rational** if there is a pro-con model $\langle\succ, \rhd\rangle$ such that for every choice set $S$ and every $x \in S$,
--   $$C(S) = x \iff |\mathrm{Pros}(x, S)| > |\mathrm{Cons}(x, S)|.$$
--   The same model serves every choice set, and the equivalence is required at every alternative of $S$, not only at the chosen one.
--
--   These definitions are the vocabulary of the goal theorem (Theorem 1) and of Remark 1.
--
--   **Formalization Note** $X$ is a type with `[Fintype X] [DecidableEq X]`. An ordering is a rank bijection $\sigma : X \simeq \{0, \dots, n-1\}$, rank $0$ being the best alternative; distinct bijections are distinct linear orders, so a set of orderings is a `Finset` of bijections and no ordering can be repeated. "$x = \max(S, \sigma)$" is `IsTop σ S x`: $x \in S$ and $\sigma(x) \le \sigma(y)$ for every $y \in S$. A choice function is a map `C : Finset X → X` with `C S ∈ S` for every nonempty `S`; its value at $\emptyset$ is irrelevant. `ProConRational C` includes this choice-function condition and quantifies the model equivalence only over nonempty `S`. Disjointness of the two sets is a field of the structure.
-- source:
--   Dogan & Yildiz, Every choice function is pro-con rationalizable, SSRN 3085542 (January 10, 2021), p. 5, Section 2.1 and Definition 1

import Mathlib

namespace ProConChoice.Rational

/-- An ordering of the finite alternative set `X` (a complete, transitive, antisymmetric relation),
encoded as a rank bijection `σ : X ≃ Fin |X|`; rank `0` is the best alternative, and `x` is ranked
above `y` iff `σ x < σ y`. Distinct orderings are distinct bijections. -/
abbrev Ordering (X : Type*) [Fintype X] := X ≃ Fin (Fintype.card X)

/-- `x` is the `σ`-top-ranked alternative of `S`, i.e. `x = max(S, σ)`: `x ∈ S` and no element of
`S` has a better (smaller) rank. -/
def IsTop {X : Type*} [Fintype X] (σ : Ordering X) (S : Finset X) (x : X) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, σ x ≤ σ y

instance {X : Type*} [Fintype X] [DecidableEq X] (σ : Ordering X) (S : Finset X) (x : X) :
    Decidable (IsTop σ S x) := by
  unfold IsTop; infer_instance

/-- A (deterministic) choice function: every nonempty choice set `S` is mapped to a member of `S`.
The value at `∅` is irrelevant. -/
def IsChoiceFunction {X : Type*} (C : Finset X → X) : Prop :=
  ∀ S : Finset X, S.Nonempty → C S ∈ S

/-- A (deterministic) pro-con model ⟨≻, ▷⟩: a finite set of pro-orderings and a finite set of
con-orderings; no ordering is both a pro- and a con-ordering. -/
structure ProConModel (X : Type*) [Fintype X] where
  /-- the set `≻ = {≻₁, …, ≻ₘ}` of pro-orderings -/
  pro : Finset (Ordering X)
  /-- the set `▷ = {▷₁, …, ▷_q}` of con-orderings -/
  con : Finset (Ordering X)
  /-- an ordering that is a pro-ordering is not a con-ordering -/
  disjoint : Disjoint pro con

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `Pros(x, S) = {≻ᵢ ∈ ≻ : x = max(S, ≻ᵢ)}`. -/
def ProConModel.pros (M : ProConModel X) (x : X) (S : Finset X) : Finset (Ordering X) :=
  M.pro.filter (fun σ => IsTop σ S x)

/-- `Cons(x, S) = {▷ᵢ ∈ ▷ : x = max(S, ▷ᵢ)}`. -/
def ProConModel.cons (M : ProConModel X) (x : X) (S : Finset X) : Finset (Ordering X) :=
  M.con.filter (fun σ => IsTop σ S x)

/-- Definition 1: a choice function `C` is pro-con rational if there is a pro-con model such that
for every choice set `S` and every `x ∈ S`, `C(S) = x` iff
`|Pros(x, S)| > |Cons(x, S)|`. -/
def ProConRational (C : Finset X → X) : Prop :=
  IsChoiceFunction C ∧
    ∃ M : ProConModel X, ∀ S : Finset X, S.Nonempty → ∀ x ∈ S,
      (C S = x ↔ (M.cons x S).card < (M.pros x S).card)

end ProConChoice.Rational


