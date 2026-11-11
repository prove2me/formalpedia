-- Prove2me | Definitions.Def_ReconfRes_Frozen_Refutation
-- name    : ReconfRes_Frozen_Refutation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:20:48.012124+00:00
-- url     : https://prove2.me/theorems/805a0ab0-a0c3-49e0-a20d-55a989700fd5
-- title:
--   Resolution refutations as DAGs: axiom, resolution and weakening nodes, sink, size, width, lean, read-once, axiom multiset, pivots, isomorphism (Definition 2.1)
-- statement:
--   A **literal** is a variable $x$ or its negation $\neg x$, a **clause** is a finite set of literals and a **CNF formula** $F$ a finite set of clauses (published definition `MultiplierAssoc206_Resolution_CNF`). The **resolvent on $x$** of $C\cup\{x\}$ and $D\cup\{\neg x\}$, with $x\notin C$, $\neg x\notin D$, is $C\cup D$.
--
--   A **resolution refutation** of $F$ (Definition 2.1) is a finite directed acyclic graph with at most one edge per ordered pair of nodes, whose nodes carry clauses over the variables of $F$ and are of three kinds: an **axiom node** is a source labelled by a clause of $F$; a **resolution node** has two distinct parents and is labelled by their resolvent on some variable; a **weakening node** has one parent labelled $C'$ and is labelled by some $C\supseteq C'$. The consumers of a node are its children. A designated node, the **sink**, has no consumer and is labelled by the empty clause.
--   $$|R| = \#\text{nodes},\qquad \operatorname{width}(R)=\max_{v}|\mathrm{label}(v)|.$$
--   A node is **idle** if it is not the sink and has no consumer; $R$ is **lean** if every node is an ancestor of the sink. A lean refutation is **read-once** if it has no weakening node and every non-sink node has exactly one consumer. The **axiom multiset** counts one clause per axiom node, repeated labels included. A resolution node **has pivot $x$** when its clause is the resolvent of its two parents on $x$. Two refutations are **isomorphic** if a bijection of their nodes preserves labels, edges and the sink (pivots and premise order are not compared).
--
--   A Horn clause has at most one positive literal; a Horn formula consists of Horn clauses.
--
--   **Formalization Note.** `ProofDag V` has the nodes `Fin n`, a label function, an edge `Finset` and a sink. The kind of a node is read off its number of parents (0, 1 or 2), so it is not stored. `IsRefutationOf F` collects all conditions of Definition 2.1; unsatisfiability of $F$ follows from them by soundness (p. 19) and is not added. `IsLean` is "every node is an ancestor of the sink", which the paper gives as the equivalent form of "no idle node".
-- source:
--   Myrisiotis, Reconfiguring Resolution Refutations, STOC 2027 submission (manuscript sha256 8b5124c1…), p. 18, Definition 2.1; p. 19 (axiom multiset); p. 23 (isomorphism)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF

open MultiplierAssoc206.Resolution

namespace ReconfRes.Frozen

/-!
# Resolution refutations as DAGs (Definition 2.1)

Myrisiotis, *Reconfiguring Resolution Refutations*, STOC 2027 submission, §2.1, p. 18
(Definition 2.1), §2.2 p. 19 (axiom multiset), §3.3 p. 23 (isomorphism of refutations).

Literals, clauses and CNF formulas are those of the published definition
`MultiplierAssoc206_Resolution_CNF`: a literal over the variable type `V` is a pair `(x, b)`
(`(x, true)` is `x`, `(x, false)` is `¬x`), a clause is a `Finset` of literals and a CNF formula a
`Finset` of clauses.

A `ProofDag V` is a finite directed graph on the nodes `Fin n` (`n ≥ 1`, since a sink exists),
with a clause label on every node, a set of directed edges (so at most one edge per ordered pair)
and a designated node `sink`. The kind of a node is read off its in-degree: a node with no parent
is an axiom node, a node with one parent a weakening node, a node with two parents a resolution
node. Pivots and premise order are not stored (p. 23).
-/

/-- A finite directed graph of clause-labelled nodes `Fin n` with a designated sink. -/
structure ProofDag (V : Type) where
  /-- number of nodes -/
  n : ℕ
  /-- clause label of every node -/
  label : Fin n → Clause V
  /-- directed edges, from premise to conclusion -/
  edges : Finset (Fin n × Fin n)
  /-- the designated sink -/
  sink : Fin n

variable {V : Type} [DecidableEq V]

namespace ProofDag

variable (R : ProofDag V)

/-- The size `|R|`: the number of nodes, axiom nodes included. -/
def size : ℕ := R.n

/-- The parents (premises) of a node. -/
def parents (i : Fin R.n) : Finset (Fin R.n) := Finset.univ.filter fun j => (j, i) ∈ R.edges

/-- The consumers (children) of a node. -/
def consumers (i : Fin R.n) : Finset (Fin R.n) := Finset.univ.filter fun j => (i, j) ∈ R.edges

/-- An axiom node is a source. -/
def IsAxiomNode (i : Fin R.n) : Prop := R.parents i = ∅

/-- A weakening node has exactly one parent. -/
def IsWeakeningNode (i : Fin R.n) : Prop := (R.parents i).card = 1

/-- A resolution node has exactly two (distinct) parents. -/
def IsResolutionNode (i : Fin R.n) : Prop := (R.parents i).card = 2

/-- An inference node is a resolution or a weakening node. -/
def IsInferenceNode (i : Fin R.n) : Prop := (R.parents i).Nonempty

/-- `Anc R i j`: `i` is an ancestor of `j` (a directed path, possibly of length zero, from `i`
to `j`); equivalently `j` is a descendant of `i`. -/
def Anc (i j : Fin R.n) : Prop := Relation.ReflTransGen (fun a b => (a, b) ∈ R.edges) i j

/-- The width of a refutation: the maximum width of its clauses. -/
def width : ℕ := Finset.univ.sup fun i => (R.label i).card

/-- The axiom multiset: one clause label for each axiom node, repeated labels included (p. 19). -/
def axiomMultiset : Multiset (Clause V) :=
  ((Finset.univ.filter fun i => R.parents i = ∅).val).map R.label

/-- A node is idle if it is not the sink and has no consumer. -/
def IsIdle (i : Fin R.n) : Prop := i ≠ R.sink ∧ R.consumers i = ∅

/-- `R` is lean if it has no idle node, i.e. every node is an ancestor of the sink. -/
def IsLean : Prop := ∀ i, R.Anc i R.sink

/-- A lean refutation is read-once if it has no weakening node and every node other than the
sink has exactly one consumer (Definition 2.1). -/
def IsReadOnce : Prop :=
  R.IsLean ∧ (∀ i, ¬ R.IsWeakeningNode i) ∧ ∀ i, i ≠ R.sink → (R.consumers i).card = 1

end ProofDag

/-- `ResolventOn x A B C`: `C` is the resolvent on the variable `x` (the pivot) of `A` and `B`,
i.e. `A = A' ∪ {x}`, `B = B' ∪ {¬x}` with `x ∉ A'`, `¬x ∉ B'`, and `C = A' ∪ B'` (p. 18). -/
def ResolventOn (x : V) (A B C : Clause V) : Prop :=
  (x, true) ∈ A ∧ (x, false) ∈ B ∧ C = A.erase (x, true) ∪ B.erase (x, false)

/-- The variables occurring in a CNF formula. -/
def vars (F : CNF V) : Finset V := F.biUnion fun C => C.image Prod.fst

/-- A Horn clause has at most one positive literal. -/
def IsHornClause (C : Clause V) : Prop := (C.filter fun l => l.2 = true).card ≤ 1

/-- A Horn formula consists of Horn clauses. -/
def IsHorn (F : CNF V) : Prop := ∀ C ∈ F, IsHornClause C

namespace ProofDag

variable (R : ProofDag V)

/-- `R` is a resolution refutation of `F` (Definition 2.1): the graph is acyclic; every clause
uses only variables of `F`; every node is an axiom node labelled by a clause of `F`, a resolution
node with two distinct parents labelled by their resolvent on some variable (in either order of
the premises), or a weakening node whose label contains its parent's label; the sink has no
consumer and is labelled by the empty clause. (Unsatisfiability of `F` follows by soundness,
p. 19.) -/
def IsRefutationOf (F : CNF V) : Prop :=
  (∀ i j, (i, j) ∈ R.edges → R.Anc j i → False) ∧
  (∀ i, ∀ l ∈ R.label i, l.1 ∈ vars F) ∧
  (∀ i,
    (R.parents i = ∅ ∧ R.label i ∈ F) ∨
    (∃ p₁ p₂, p₁ ≠ p₂ ∧ R.parents i = {p₁, p₂} ∧
      ∃ x, ResolventOn x (R.label p₁) (R.label p₂) (R.label i)) ∨
    (∃ p, R.parents i = {p} ∧ R.label p ⊆ R.label i)) ∧
  R.consumers R.sink = ∅ ∧
  R.label R.sink = ∅

/-- `HasPivot R i x`: `i` is a resolution node whose label is the resolvent of its two parents on
the variable `x` (pivots are read off the clauses, p. 23, p. 73). -/
def HasPivot (i : Fin R.n) (x : V) : Prop :=
  ∃ p₁ p₂, p₁ ≠ p₂ ∧ R.parents i = {p₁, p₂} ∧ ResolventOn x (R.label p₁) (R.label p₂) (R.label i)

end ProofDag

/-- Two refutations are isomorphic if their nodes can be paired one to one preserving clause
labels, directed edges and the designated sink (p. 23). -/
def ProofDag.Iso (R R' : ProofDag V) : Prop :=
  ∃ e : Fin R.n ≃ Fin R'.n,
    (∀ i, R'.label (e i) = R.label i) ∧
    (∀ i j, (e i, e j) ∈ R'.edges ↔ (i, j) ∈ R.edges) ∧
    e R.sink = R'.sink

end ReconfRes.Frozen


