-- Prove2me | Definitions.Def_SpreadMatchCircuit_Matching_MonotoneCircuit
-- name    : SpreadMatchCircuit_Matching_MonotoneCircuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:25:00.319106+00:00
-- url     : https://prove2.me/theorems/de49eeec-c90b-4d3f-b6c6-f3dab07f8edd
-- title:
--   Monotone Boolean circuits: finite DAGs of input, AND and OR nodes
-- statement:
--   A **monotone Boolean circuit** over a set of variables $\iota$ is a finite sequence of nodes $g_0,\dots,g_{s-1}$ together with a designated output node. Each node is either an input node reading a variable $i\in\iota$, or a binary gate $g_a\wedge g_b$ or $g_a\vee g_b$ of two earlier nodes ($a,b$ smaller than the node's own number). Earlier nodes may be reused any number of times, so the circuit is a directed acyclic graph with arbitrary fan-out, not a formula.
--
--   On an assignment $x:\iota\to\{0,1\}$ every node takes a value by the usual recursion, and the value of the circuit is the value at its output node. The **size** of the circuit is its number of nodes $s$, input nodes included.
--
--   The object is the source's circuit model, and it is independent of the matching problem, so it is reusable for other monotone lower bounds.
--
--   **Formalization Note** The acyclicity is built into the type: node $g$ may refer only to `Fin g`. No negation and no constants are available. Counting input nodes follows the source, which calls them "input gates" (p. 11). After removing nodes that do not reach the output, a circuit with $G$ binary gates has at most $3G+1$ nodes, so the two usual counting conventions differ by a constant factor.
-- source:
--   Anup Rao, STOC 2027 submission #299 (October 2026), p. 2 (monotone Boolean circuit), p. 11 (input gates, gates computed from h1, h2)

import Mathlib

namespace SpreadMatchCircuit.Matching

/-- One node of a monotone circuit whose earlier nodes are numbered by `Fin m`: an input node
reading the variable `i`, or a binary AND/OR of two earlier nodes. There are no negations and no
constants. -/
inductive MonotoneGate (ι : Type) (m : ℕ) : Type
  | input (i : ι) : MonotoneGate ι m
  | and (a b : Fin m) : MonotoneGate ι m
  | or (a b : Fin m) : MonotoneGate ι m

/-- A monotone Boolean circuit over the variables `ι`: a finite DAG listed in topological order
(node `g` only refers to nodes numbered below `g`), with arbitrary fan-out and a designated
output node. `size` counts every node, input nodes included (the source's "input gates", p. 11). -/
structure MonotoneCircuit (ι : Type) where
  size : ℕ
  gate : (g : Fin size) → MonotoneGate ι g.val
  output : Fin size

namespace MonotoneCircuit

variable {ι : Type}

/-- The value computed at a node on the assignment `x`. -/
def nodeValue (C : MonotoneCircuit ι) (x : ι → Bool) (g : Fin C.size) : Bool :=
  match C.gate g with
  | .input i => x i
  | .and a b =>
      nodeValue C x ⟨a.val, a.isLt.trans g.isLt⟩ && nodeValue C x ⟨b.val, b.isLt.trans g.isLt⟩
  | .or a b =>
      nodeValue C x ⟨a.val, a.isLt.trans g.isLt⟩ || nodeValue C x ⟨b.val, b.isLt.trans g.isLt⟩
termination_by g.val
decreasing_by
  all_goals first | exact a.isLt | exact b.isLt

/-- The value of the circuit on the assignment `x`: the value at the output node. -/
def eval (C : MonotoneCircuit ι) (x : ι → Bool) : Bool := C.nodeValue x C.output

end MonotoneCircuit

end SpreadMatchCircuit.Matching


