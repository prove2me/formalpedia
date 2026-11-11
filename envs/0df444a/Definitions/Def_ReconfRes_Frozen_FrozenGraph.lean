-- Prove2me | Definitions.Def_ReconfRes_Frozen_FrozenGraph
-- name    : ReconfRes_Frozen_FrozenGraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:21:35.37844+00:00
-- url     : https://prove2.me/theorems/5149acd6-5f97-4950-baf2-ee7b704f8172
-- title:
--   Blocks, frozen moves and the frozen lean graph G^fr_k(F,w,s); indexed source occurrences (Definition 3.2)
-- statement:
--   Let $R$ be a lean refutation of $F$ and $k\ge1$. The **output** of a node set $Q$ is a node of $Q$ that every node of $Q$ reaches inside $Q$. A **block** of locality $k$ is a set $Q$ of at most $k$ inference nodes plus some axiom nodes, with an output $q$, such that every node of $Q$ other than $q$ has all its consumers in $Q$; its **inputs** are the nodes outside $Q$ with a child in $Q$. A **move** replaces $Q$ by a set $Q'$ of new nodes (at most $k$ inference nodes plus axiom nodes) such that $Q'$ is a derivation whose premises outside $Q'$ are inputs of $Q$, its output carries the clause of $q$, every other node of $Q'$ has all its consumers in $Q'$, and the consumers of $q$ become consumers of the output of $Q'$. The move is **frozen** if neither $Q$ nor $Q'$ contains an axiom node.
--
--   The **frozen lean graph** $G^{fr}_k(F,w,s)$ has as vertices the lean refutations of $F$ of width at most $w$ and size at most $s$, up to renaming of nodes, and joins $R,R'$ when one is obtained from the other by a frozen move:
--   $$R\sim R' \iff R,R'\in V(G^{fr}_k(F,w,s))\ \wedge\ (R\to_{fr} R'\ \vee\ R'\to_{fr} R).$$
--
--   For Lemmas 3.60 and 3.62, an **indexed** refutation carries a bijection `pos` from an index set onto its axiom nodes, with `pos i` labelled by the inventory clause of $i$; an **indexed frozen path** is a path in which each move keeps the indices of the outside source nodes and each identification of two presentations of a proof preserves them.
--
--   **Formalization Note.** `MoveVia k R R' Q Q' φ` describes the result $R'$ concretely: `φ` identifies the nodes of $R$ outside $Q$ with those of $R'$ outside $Q'$, preserving labels and the edges among them; the only edges between kept nodes and $Q'$ go from inputs of $Q$ into $Q'$ and from the output $q'$ to the images of the consumers of $q$. That $Q'$ is a derivation and its axiom nodes carry clauses of $F$ is part of $R'$ being a vertex. Vertices are taken up to renaming: `FrozenConnected` is the reflexive-transitive closure of steps that are frozen moves (either direction) or isomorphisms, both ends being vertices.
-- source:
--   Myrisiotis, Reconfiguring Resolution Refutations, STOC 2027 submission (manuscript sha256 8b5124c1…), pp. 21–22, Definition 3.2; p. 23 (isomorphism); p. 78 (consistent indexing, Lemma 3.60)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_ReconfRes_Frozen_Refutation

open MultiplierAssoc206.Resolution

namespace ReconfRes.Frozen

/-!
# Blocks, frozen moves and the frozen lean graph `G^fr_k(F,w,s)` (Definition 3.2)

Myrisiotis, *Reconfiguring Resolution Refutations*, STOC 2027 submission, §3.2, pp. 21–22.

A move replaces a block `Q` of `R` by a set `Q'` of new nodes. Concretely, `R'` is the result
when its nodes split into the new nodes `Q'` and the kept nodes, which correspond one to one
(`φ`) to the nodes of `R` outside `Q`, with the same labels and the same edges among them; the
only edges between kept nodes and `Q'` are edges from inputs of `Q` into `Q'` and edges from the
output of `Q'` to the (images of the) consumers of the output of `Q`. Vertices are lean
refutations up to renaming of nodes: adjacency is invariant under renaming either side, and
connectivity is taken in the graph whose vertices are the isomorphism classes.
-/

variable {V : Type} [DecidableEq V]

namespace ProofDag

variable (R : ProofDag V)

/-- `AncIn R Q i j`: a directed path from `i` to `j` all of whose nodes lie in `Q`. -/
def AncIn (Q : Finset (Fin R.n)) (i j : Fin R.n) : Prop :=
  Relation.ReflTransGen (fun a b => a ∈ Q ∧ b ∈ Q ∧ (a, b) ∈ R.edges) i j

/-- `q` is an output of the node set `Q`: a node of `Q` that every node of `Q` reaches inside
`Q`. -/
def IsOutput (Q : Finset (Fin R.n)) (q : Fin R.n) : Prop :=
  q ∈ Q ∧ ∀ i ∈ Q, R.AncIn Q i q

/-- `Q` is a block of locality `k` with output `q` (Definition 3.2): at most `k` inference nodes
together with some axiom nodes, output `q`, and every node of `Q` other than `q` has all its
consumers in `Q`. -/
def IsBlock (k : ℕ) (Q : Finset (Fin R.n)) (q : Fin R.n) : Prop :=
  (Q.filter fun i => (R.parents i).Nonempty).card ≤ k ∧
  R.IsOutput Q q ∧
  ∀ i ∈ Q, i ≠ q → R.consumers i ⊆ Q

/-- The inputs of `Q`: the nodes outside `Q` that are parents of nodes of `Q`. -/
def inputs (Q : Finset (Fin R.n)) : Finset (Fin R.n) :=
  Finset.univ.filter fun i => i ∉ Q ∧ ∃ j ∈ Q, (i, j) ∈ R.edges

end ProofDag

/-- `MoveVia k R R' Q Q' φ`: `R'` is obtained from `R` by an axiom-trading move of locality `k`
replacing the block `Q` of `R` by the set `Q'` of new nodes of `R'`; `φ` identifies the nodes of
`R` outside `Q` with the nodes of `R'` outside `Q'` (Definition 3.2). The conditions are: `Q` is
a block of `R` with output `q`; `Q'` has at most `k` inference nodes plus axiom nodes, an output
`q'`, and every node of `Q'` other than `q'` has all its consumers in `Q'`; the kept nodes keep
their labels and the edges among them; every premise of a node of `Q'` outside `Q'` is (the image
of) an input of `Q`; `q'` carries the clause of `q`; the consumers of `q` become the consumers of
`q'` and no other node of `Q'` has a consumer outside `Q'`; the sink is kept, or is `q` and
becomes `q'`. That `Q'` is a derivation and its axiom nodes are labelled by clauses of `F` is
part of `R'` being a refutation of `F`, required of every vertex. -/
def MoveVia (k : ℕ) (R R' : ProofDag V) (Q : Finset (Fin R.n)) (Q' : Finset (Fin R'.n))
    (φ : {i // i ∉ Q} ≃ {j // j ∉ Q'}) : Prop :=
  ∃ q q',
    R.IsBlock k Q q ∧
    R'.IsBlock k Q' q' ∧
    R'.label q' = R.label q ∧
    (∀ i : {i // i ∉ Q}, R'.label (φ i) = R.label i) ∧
    (∀ i j : {i // i ∉ Q}, ((φ i).1, (φ j).1) ∈ R'.edges ↔ (i.1, j.1) ∈ R.edges) ∧
    (∀ i : {i // i ∉ Q}, ∀ j ∈ Q', ((φ i).1, j) ∈ R'.edges → i.1 ∈ R.inputs Q) ∧
    (∀ c : {i // i ∉ Q}, (q', (φ c).1) ∈ R'.edges ↔ (q, c.1) ∈ R.edges) ∧
    (∀ h : R.sink ∉ Q, (φ ⟨R.sink, h⟩).1 = R'.sink) ∧
    (R.sink ∈ Q → R.sink = q ∧ R'.sink = q')

/-- A frozen move: neither `Q` nor `Q'` contains an axiom node. -/
def FrozenMoveVia (k : ℕ) (R R' : ProofDag V) (Q : Finset (Fin R.n)) (Q' : Finset (Fin R'.n))
    (φ : {i // i ∉ Q} ≃ {j // j ∉ Q'}) : Prop :=
  MoveVia k R R' Q Q' φ ∧ (∀ i ∈ Q, ¬ R.IsAxiomNode i) ∧ (∀ j ∈ Q', ¬ R'.IsAxiomNode j)

/-- `R'` is obtained from `R` by a frozen move of locality `k`. -/
def FrozenMove (k : ℕ) (R R' : ProofDag V) : Prop :=
  ∃ Q Q' φ, FrozenMoveVia k R R' Q Q' φ

/-- The vertices of `G^fr_k(F,w,s)`: lean refutations of `F` of width at most `w` and size at
most `s`. -/
def IsVertex (F : CNF V) (w s : ℕ) (R : ProofDag V) : Prop :=
  R.IsRefutationOf F ∧ R.IsLean ∧ R.width ≤ w ∧ R.size ≤ s

/-- Adjacency in the frozen lean graph `G^fr_k(F,w,s)`: both are vertices and one is obtained
from the other by a frozen move of locality `k` (the graph is undirected). -/
def FrozenAdj (k : ℕ) (F : CNF V) (w s : ℕ) (R R' : ProofDag V) : Prop :=
  IsVertex F w s R ∧ IsVertex F w s R' ∧ (FrozenMove k R R' ∨ FrozenMove k R' R)

/-- One step in `G^fr_k(F,w,s)` with vertices taken up to renaming of nodes: an adjacency, or two
presentations of the same vertex (isomorphic refutations). -/
def FrozenStep (k : ℕ) (F : CNF V) (w s : ℕ) (R R' : ProofDag V) : Prop :=
  IsVertex F w s R ∧ IsVertex F w s R' ∧ (R.Iso R' ∨ FrozenMove k R R' ∨ FrozenMove k R' R)

/-- `R` and `R'` lie in one connected component of `G^fr_k(F,w,s)` (refutations up to renaming).
For vertices `R`, `R'` this is the reachability question; `ReflTransGen` also relates every
refutation to itself. -/
def FrozenConnected (k : ℕ) (F : CNF V) (w s : ℕ) (R R' : ProofDag V) : Prop :=
  Relation.ReflTransGen (FrozenStep k F w s) R R'

/-! ## Indexed source occurrences (Lemmas 3.60 and 3.62) -/

/-- `IsIndexedBy inv S R pos`: the axiom nodes of `R` are indexed by the finite index set `S`:
`pos` is injective on `S`, its image on `S` is exactly the set of axiom nodes, and the node
`pos i` carries the inventory clause `inv i`. -/
def IsIndexedBy {ι : Type} (inv : ι → Clause V) (S : Finset ι) (R : ProofDag V)
    (pos : ι → Fin R.n) : Prop :=
  Set.InjOn pos S ∧
  (∀ j, R.IsAxiomNode j ↔ ∃ i ∈ S, pos i = j) ∧
  ∀ i ∈ S, R.label (pos i) = inv i

/-- One step of an indexed frozen path: both sides are indexed vertices of `G^fr_k(F,w,s)` and
either an isomorphism (an identification of two presentations of a proof) or a frozen move in
either direction carries the index of every source occurrence to the same index. -/
def IndexedFrozenStep {ι : Type} (k : ℕ) (F : CNF V) (w s : ℕ) (inv : ι → Clause V)
    (S : Finset ι) (P P' : Σ R : ProofDag V, ι → Fin R.n) : Prop :=
  IsVertex F w s P.1 ∧ IsVertex F w s P'.1 ∧
  IsIndexedBy inv S P.1 P.2 ∧ IsIndexedBy inv S P'.1 P'.2 ∧
  ((∃ e : Fin P.1.n ≃ Fin P'.1.n,
      (∀ i, P'.1.label (e i) = P.1.label i) ∧
      (∀ i j, (e i, e j) ∈ P'.1.edges ↔ (i, j) ∈ P.1.edges) ∧
      e P.1.sink = P'.1.sink ∧ ∀ s ∈ S, e (P.2 s) = P'.2 s) ∨
   (∃ Q Q' φ, FrozenMoveVia k P.1 P'.1 Q Q' φ ∧
      ∀ s ∈ S, ∀ h : P.2 s ∉ Q, (φ ⟨P.2 s, h⟩).1 = P'.2 s) ∨
   (∃ Q Q' φ, FrozenMoveVia k P'.1 P.1 Q Q' φ ∧
      ∀ s ∈ S, ∀ h : P'.2 s ∉ Q, (φ ⟨P'.2 s, h⟩).1 = P.2 s))

/-- Two indexed refutations are joined by a frozen path with consistent indices. -/
def IndexedFrozenConnected {ι : Type} (k : ℕ) (F : CNF V) (w s : ℕ) (inv : ι → Clause V)
    (S : Finset ι) (P P' : Σ R : ProofDag V, ι → Fin R.n) : Prop :=
  Relation.ReflTransGen (IndexedFrozenStep k F w s inv S) P P'

end ReconfRes.Frozen


