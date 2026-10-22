-- Prove2me | Definitions.Def_WalledBrauer_Blocks_Diagram
-- name    : WalledBrauer_Blocks_Diagram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:42:26.595556+00:00
-- url     : https://prove2.me/theorems/d1b3258e-4649-4d95-a3de-726818252d10
-- title:
--   Brauer diagrams on $n$ strands and their product by stacking (p. 3)
-- statement:
--   A **Brauer diagram** on $n$ strands is a partition of the $2n$ nodes $\{1,\dots,n\}$ (northern) and $\{\bar 1,\dots,\bar n\}$ (southern) into $n$ pairs. Edges joining a northern and a southern node are **propagating lines**; the others are northern or southern **arcs**.
--
--   The product of two diagrams $A$ and $B$ is computed by stacking: place $A$ above $B$ and identify the southern nodes of $A$ with the northern nodes of $B$. This gives a graph on three rows of $n$ vertices. Each outer vertex (the top row, which is the northern row of $A$, and the bottom row, which is the southern row of $B$) is joined by a path to exactly one other outer vertex. These paths form a new Brauer diagram $C = A\circ B$. Some components contain no outer vertex at all: they are closed loops lying in the middle row, and $t(A,B)$ denotes their number. In the Brauer algebra $B_n(\delta)$ the product is
--
--   $$
--   A\cdot B=\delta^{\,t(A,B)}\,C .
--   $$
--
--   This file defines the diagrams, the stacked graph, the composite diagram $C$ and the loop count $t(A,B)$. It is the combinatorial input of the walled Brauer algebra.
--
--   **Formalization Note** Nodes are `Fin n ⊕ Fin n` (`Sum.inl i` is northern node $i$, `Sum.inr i` is southern node $i$, 0-based). A diagram is a fixed-point-free involution of the nodes. The stacked graph lives on `Fin 3 × Fin n` (rows 0, 1, 2) and is built with `SimpleGraph.fromRel`. The composite joins an outer node to the other outer node it is connected to, chosen with `Classical.choose`; for Brauer diagrams that node exists and is unique. The loop count is the number of connected components all of whose vertices lie in the middle row. The fallbacks in `rawComp` and `BrauerDiagram.comp` (keep `x`, return `A`) are never reached on Brauer diagrams.
-- source:
--   Cox, De Visscher, Doty & Martin, On the blocks of the walled Brauer algebra, arXiv:0709.0851v1, p. 3, Section 2 (definition of the Brauer algebra product)

import Mathlib

namespace WalledBrauer.Blocks

/-- The `2n` nodes of a Brauer diagram on `n` strands: `Sum.inl i` is the northern node `i`,
`Sum.inr i` the southern node `i` (`i : Fin n`, numbered `0, …, n-1` from left to right). -/
abbrev Node (n : ℕ) := Fin n ⊕ Fin n

/-- A map `f` on the nodes is a Brauer diagram (a partition of the `2n` nodes into pairs) when
it is a fixed-point-free involution: `x` is joined to `f x`. -/
def IsBrauerDiagram {n : ℕ} (f : Node n → Node n) : Prop :=
  ∀ x, f (f x) = x ∧ f x ≠ x

/-- Brauer diagrams on `n` strands (p. 3). -/
def BrauerDiagram (n : ℕ) := {f : Node n → Node n // IsBrauerDiagram f}

/-- The identity diagram: northern node `i` joined to southern node `i`. -/
def BrauerDiagram.one (n : ℕ) : BrauerDiagram n :=
  ⟨Sum.swap, fun x => ⟨Sum.swap_swap x, by cases x <;> simp⟩⟩

/-- Stacking `A` over `B` uses three rows of `n` vertices, `(0, i)` (top), `(1, i)` (middle),
`(2, i)` (bottom). The nodes of `A` sit on rows 0 (north) and 1 (south). -/
def embTop {n : ℕ} : Node n → Fin 3 × Fin n
  | Sum.inl i => (0, i)
  | Sum.inr i => (1, i)

/-- The nodes of `B` sit on rows 1 (north) and 2 (south): the southern nodes of `A` are
identified with the northern nodes of `B`. -/
def embBot {n : ℕ} : Node n → Fin 3 × Fin n
  | Sum.inl i => (1, i)
  | Sum.inr i => (2, i)

/-- The outer nodes of the product: the northern nodes of `A` (row 0) and the southern nodes of
`B` (row 2). -/
def embOuter {n : ℕ} : Node n → Fin 3 × Fin n
  | Sum.inl i => (0, i)
  | Sum.inr i => (2, i)

/-- The graph obtained by stacking `A` over `B`: an edge for every pair of `A` (between rows 0
and 1) and for every pair of `B` (between rows 1 and 2). -/
def stackGraph {n : ℕ} (A B : Node n → Node n) : SimpleGraph (Fin 3 × Fin n) :=
  SimpleGraph.fromRel fun u v =>
    (∃ x, u = embTop x ∧ v = embTop (A x)) ∨ (∃ x, u = embBot x ∧ v = embBot (B x))

open scoped Classical in
/-- The pairing of the outer nodes read off the stacked graph: `x` is joined to the other outer
node in its connected component (for Brauer diagrams this node exists and is unique; the
fallback `x` is never used). -/
noncomputable def rawComp {n : ℕ} (A B : Node n → Node n) (x : Node n) : Node n :=
  if h : ∃ y, y ≠ x ∧ (stackGraph A B).Reachable (embOuter x) (embOuter y) then
    Classical.choose h
  else x

/-- The number `t` of closed loops formed when `A` is stacked over `B`: the connected components
of the stacked graph containing no outer node (all their vertices lie in the middle row). -/
noncomputable def loops {n : ℕ} (A B : Node n → Node n) : ℕ :=
  Nat.card {c : (stackGraph A B).ConnectedComponent //
    ∀ v, (stackGraph A B).connectedComponentMk v = c → v.1 = 1}

open scoped Classical in
/-- The diagram `C` of the product `AB = δ^t C` (p. 3). The read-off pairing of two Brauer
diagrams is always a Brauer diagram; the fallback `A` is never used. -/
noncomputable def BrauerDiagram.comp {n : ℕ} (A B : BrauerDiagram n) : BrauerDiagram n :=
  if h : IsBrauerDiagram (rawComp A.1 B.1) then ⟨rawComp A.1 B.1, h⟩ else A

end WalledBrauer.Blocks


