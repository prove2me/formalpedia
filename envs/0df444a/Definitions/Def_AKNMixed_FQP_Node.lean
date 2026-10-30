-- Prove2me | Definitions.Def_AKNMixed_FQP_Node
-- name    : AKNMixed_FQP_Node
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:17:53.8682+00:00
-- url     : https://prove2.me/theorems/f601027d-0f21-451c-a997-5c8ea51ebf10
-- title:
--   Circuit node over a pool of wire labels
-- statement:
--   Circuits are encoded over a pool of $N$ wire labels, each carrying one qubit. A **node** consists of a label (a gate of $\mathcal G$ or a subroutine of $\mathcal S$, of order $(k_v,l_v)$) and $k_v+l_v$ distinct wire labels: the first $k_v$ are its input wires, the last $l_v$ its output wires. Its **step** is the super-operator on all $N$ wires that applies the label's map to the input wires, writes the result on the output wires, resets the consumed inputs to $|0\rangle$, and is the identity elsewhere.
--
--   A list of nodes is a **valid run** from given sets of existing ("born") and unconsumed ("live") wires when, going through the list from its head, each node reads only live wires and writes only wires that do not exist yet; at the end, every wire of a prescribed result set is live.
--
--   This encodes the paper's directed acyclic graph: an edge is a wire produced by one node and read by a later one, and a valid run is a topological order.
--
--   **Formalization Note** `Node.ins`, `Node.outs`, `Node.step` and `Node.ValidRun` are the projections and the run predicate.
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, Definition 2, p. 7; Definition 3, p. 8

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_AKNMixed_FQP_Op
import Definitions.Def_AKNMixed_FQP_embedOn
import Definitions.Def_AKNMixed_FQP_consumeProduce

namespace AKNMixed.FQP

open QAlgorithms

/-- **A node of a circuit over a pool of `N` wire labels.**
Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1,
Definition 2, p. 7: "Each node v in the graph is labeled by a gate g_v ∈ G of order (k_v, l_v).
The in-degree and out-degree of v are equal k_v and l_v, respectively."

A node carries its label `op` (a gate of `G` or a subroutine of `S`) and an injective listing
`wires` of `k_v + l_v` distinct wire labels: the first `k_v` are its input wires (`Node.ins`),
the last `l_v` its output wires (`Node.outs`).

**Formalization Note (wire-pool encoding of the DAG).** An edge of the paper's graph is a wire
label produced by one node and consumed by a later one; `Node.ValidRun` (below) says that a list
of nodes is a topological order of such a graph. -/
structure Node {m p : ℕ} (G : Set QGate) (S : Set (ProbFun m p)) (N : ℕ) where
  /-- The label `g_v`. -/
  op : Op G S
  /-- Input wires (first `op.inOrd`) followed by output wires (last `op.outOrd`). -/
  wires : Fin (op.inOrd + op.outOrd) ↪ Fin N

/-- Definition 2, p. 7: the `k_v` input wires of the node, in order. -/
def Node.ins {m p : ℕ} {G : Set QGate} {S : Set (ProbFun m p)} {N : ℕ} (v : Node G S N) :
    Fin v.op.inOrd ↪ Fin N :=
  (Fin.castAddEmb v.op.outOrd).trans v.wires

/-- Definition 2, p. 7: the `l_v` output wires of the node, in order. -/
def Node.outs {m p : ℕ} {G : Set QGate} {S : Set (ProbFun m p)} {N : ℕ} (v : Node G S N) :
    Fin v.op.outOrd ↪ Fin N :=
  (Fin.natAddEmb v.op.inOrd).trans v.wires

/-- Definition 3, p. 8: the action `g_v ∘ ·` of the node on the state of all `N` wires: the
label's super-operator applied to the input wires, its output written on the output wires, the
consumed input wires reset to `|0⟩`, and the identity on every other wire
(`embedOn wires (consumeProduce op.superop)`). -/
noncomputable def Node.step {m p : ℕ} {G : Set QGate} {S : Set (ProbFun m p)} {N : ℕ}
    (v : Node G S N) : Superop (Qubits N) (Qubits N) :=
  embedOn v.wires (consumeProduce v.op.superop)

/-- Definition 2, p. 7 (a directed acyclic graph in which each node has in-degree `k_v` and
out-degree `l_v`) and Definition 3, p. 8 (a topological sort): running through the list from its
head, with `born` the wires that already exist and `live` those that exist and are not yet
consumed, every node reads only live wires and writes only fresh wires; at the end every wire in
`R` (the results) is live. -/
def Node.ValidRun {m p : ℕ} {G : Set QGate} {S : Set (ProbFun m p)} {N : ℕ} :
    List (Node G S N) → Set (Fin N) → Set (Fin N) → Set (Fin N) → Prop
  | [], _, live, R => R ⊆ live
  | v :: vs, born, live, R =>
      Set.range v.ins ⊆ live ∧ Disjoint (Set.range v.outs) born ∧
        Node.ValidRun vs (born ∪ Set.range v.outs) ((live \ Set.range v.ins) ∪ Set.range v.outs) R

end AKNMixed.FQP


