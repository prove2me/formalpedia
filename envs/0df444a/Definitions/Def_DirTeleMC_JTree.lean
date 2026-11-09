-- Prove2me | Definitions.Def_DirTeleMC_JTree
-- name    : DirTeleMC_JTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:29:14.830162+00:00
-- url     : https://prove2.me/theorems/299c49df-f398-4ade-bba7-8af3a549cbdd
-- title:
--   Rooted trees labelled by vertices with a jump on every edge
-- statement:
--   A **jump tree** is a finite rooted tree whose nodes are labelled by vertices of $G$ and whose every edge carries a jump, a vertex sequence. A vertex may label several nodes. For such a tree $J$:
--   1. its **depth** is the largest number of edges on a root-to-node path;
--   2. its **load** $L_J(v)$ at a vertex $v$ is the total number of departures from $v$ along all its jumps, counting repeated traversals both within a jump and across jumps;
--   3. its **maximum load** is $\Lambda(J) = \max_{v \in V} L_J(v)$;
--   4. its arcs are the arcs traversed by its jumps.
--
--   Joining structures at a common root means taking one root node whose children are all the children of their roots. Jump arborescences and structures are jump trees with additional conditions.
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Definition 4.1, p.10 (PDF p.11); §B.4, p.21 (PDF p.22); Algorithm 1, p.23 (PDF p.24)

import Mathlib
import Definitions.Def_DirTeleMC_IsJump

namespace DirTeleMC

/-- **Rooted trees labelled by vertices, with a jump on every edge.**
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Definition 4.1, p.10 ("a rooted tree J … with edges directed away from the
root and nodes labelled by vertices of G … Each edge … carries a jump") and §B.4, p.21 (structures).

`node u cs` is a node labelled `u` whose children are listed in `cs`; an entry `(P, t)` of `cs` is the child
`t` together with the jump `P` (a vertex list) on the edge to it.

**Formalization Note.** Jump arborescences (Definition 4.1) and structures (§B.4) are both `JTree`s with
extra conditions (`IsJumpArb`, `IsStructure`). A node of a structure is a node of the unfolding `U_{η,θ}`,
i.e. the sequence of labels on its path from the root; the tree records this sequence through its labels, so
no separate sequence is stored. Several children may carry the same label. -/
inductive JTree (n : ℕ) where
  | node : Fin n → List (List (Fin n) × JTree n) → JTree n

namespace JTree

variable {n : ℕ}

theorem sizeOf_snd_lt_of_mem {e : List (Fin n) × JTree n} {cs : List (List (Fin n) × JTree n)}
    (h : e ∈ cs) : sizeOf e.2 < sizeOf cs := by
  have := List.sizeOf_lt_of_mem h
  obtain ⟨P, t⟩ := e
  simp only [Prod.mk.sizeOf_spec] at this ⊢
  omega

/-- The label of the root. -/
def label : JTree n → Fin n
  | node u _ => u

/-- The children of the root, with their jumps. -/
def children : JTree n → List (List (Fin n) × JTree n)
  | node _ cs => cs

/-- The depth: the largest number of edges on a path from the root. -/
def depth : JTree n → ℕ
  | node _ cs => (cs.attach.map fun ⟨e, _⟩ => e.2.depth + 1).foldr max 0
decreasing_by have := sizeOf_snd_lt_of_mem ‹_›; simp only [node.sizeOf_spec]; omega

/-- **The load vector** `L_J(v)`: the total number of departures from `v` along all jumps of the tree
(Definition 4.1, p.10; §B.4, p.21: "L_S(v) is the sum of L_P(v) over the jumps P of S"). -/
def loads : JTree n → Fin n → ℕ
  | node _ cs, v => (cs.attach.map fun ⟨e, _⟩ => departures e.1 v + e.2.loads v).sum
decreasing_by have := sizeOf_snd_lt_of_mem ‹_›; simp only [node.sizeOf_spec]; omega

/-- **The maximum load** `Λ(J) = max_{v ∈ V} L_J(v)` (Definition 4.1, p.10). -/
def maxLoad (J : JTree n) : ℕ := Finset.univ.sup J.loads

/-- The labels of the nodes at depth exactly `d`. -/
def labelsAt : JTree n → ℕ → Finset (Fin n)
  | node u _, 0 => {u}
  | node _ cs, d + 1 => (cs.attach.map fun ⟨e, _⟩ => e.2.labelsAt d).foldr (· ∪ ·) ∅
decreasing_by have := sizeOf_snd_lt_of_mem ‹_›; simp only [node.sizeOf_spec]; omega

/-- Every edge of the tree satisfies `R`: for an edge from a node labelled `u` to a child `t` with jump `P`,
`R u P t.label` holds. -/
def AllJumps (R : Fin n → List (Fin n) → Fin n → Prop) : JTree n → Prop
  | node u cs => ∀ e ∈ cs, R u e.1 e.2.label ∧ e.2.AllJumps R
decreasing_by have := sizeOf_snd_lt_of_mem ‹_›; simp only [node.sizeOf_spec]; omega

/-- The arcs `(P[i], P[i+1])` used by the jumps `P` of the tree. -/
def arcs : JTree n → List (Fin n × Fin n)
  | node _ cs => cs.attach.flatMap fun ⟨e, _⟩ => e.1.zip e.1.tail ++ e.2.arcs
decreasing_by have := sizeOf_snd_lt_of_mem ‹_›; simp only [node.sizeOf_spec]; omega

/-- **Joining structures at their common root** (Algorithm 1, line 11: "the node τ with the jump P and the
structures C₁, …, C_i below it"; Algorithm 2, line 6: "the union of the structures returned"): the node
labelled `u` whose children are those of all trees in the list, in order. -/
def join (u : Fin n) (l : List (JTree n)) : JTree n :=
  node u (l.flatMap children)

end JTree

end DirTeleMC


