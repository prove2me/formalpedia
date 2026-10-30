-- Prove2me | Definitions.Def_AKNMixed_FQP_Circuit
-- name    : AKNMixed_FQP_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:19:10.124384+00:00
-- url     : https://prove2.me/theorems/664e27d3-9279-482b-ba0e-6c617b601d0c
-- title:
--   Quantum circuit with blank inputs and result outputs (Definition 2)
-- statement:
--   A **quantum circuit** over a gate set $\mathcal G$ (and, possibly, a set $\mathcal S$ of subroutines from $m$ to $p$ bits) with $n$ inputs and $r$ result outputs consists of
--
--   1. a pool of $N$ wire labels;
--   2. the $n$ non-blank inputs, listed in order;
--   3. a set of blank inputs;
--   4. a list of nodes, in a topological order;
--   5. the $r$ result outputs, listed in order.
--
--   It is **well formed** when inputs and blanks are distinct wires and the node list is a valid run from the inputs and blanks, ending with every result live. This is the paper's directed acyclic graph in which each node of order $(k_v,l_v)$ has in-degree $k_v$ and out-degree $l_v$, an arbitrary subset of the inputs is labeled "blank" and an arbitrary subset of the outputs is labeled "result".
--
--   The **size** is the number of nodes; `gateCount` is the number of nodes labeled by a gate of $\mathcal G$ and `subCount` the number labeled by a subroutine. For an input $i\in\{0,1\}^n$, the **input configuration** puts $i$ on the input wires and $0$ on every other wire.
--
--   **Formalization Note** Wire-pool encoding: unborn and consumed wires hold $|0\rangle$, so the reduced state on the live wires is the paper's state. Any DAG with any topological sort is such a list.
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, Definition 2, p. 7; §4.2, pp. 9–10; Theorem 2, p. 11 (gate and subroutine counts)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_AKNMixed_FQP_Node

namespace AKNMixed.FQP

open QAlgorithms

/-- **A quantum circuit with `nIn` inputs and `r` "result" outputs, possibly calling
subroutines.**
Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1,
Definition 2, p. 7: "Let G be a family of quantum gates. A Quantum circuit that uses gates from G
is a directed acyclic graph. Each node v in the graph is labeled by a gate g_v ∈ G of order
(k_v, l_v). The in-degree and out-degree of v are equal k_v and l_v, respectively. An arbitrary
subset of the inputs are labeled "blank". An arbitrary subset of the outputs are labeled
"result"."; §4.2, pp. 9–10, for subroutine nodes.

A circuit has a pool of `N` wire labels; `inputs` lists the `nIn` non-blank inputs in order;
`blanks` is the set of blank inputs; `nodes` is the list of nodes in a topological order (head
first); `results` lists the `r` result outputs in order.

**Formalization Note (wire-pool encoding).** Every wire carries one qubit. A wire is created as
an input, a blank, or an output of a node; it is consumed by at most one node. `WellFormed`
states the graph conditions. Any DAG with any topological sort is such a list, and conversely. -/
structure Circuit {m p : ℕ} (G : Set QGate) (S : Set (ProbFun m p)) (nIn r : ℕ) where
  /-- The number of wire labels. -/
  N : ℕ
  /-- The non-blank inputs, in order (the paper's `n` inputs). -/
  inputs : Fin nIn ↪ Fin N
  /-- The inputs labeled "blank". -/
  blanks : Finset (Fin N)
  /-- The nodes, in a topological order; the head is applied first. -/
  nodes : List (Node G S N)
  /-- The outputs labeled "result", in order. -/
  results : Fin r ↪ Fin N

/-- Definition 2, p. 7: the circuit is a well-formed DAG. Inputs and blanks are distinct wires;
running through the nodes from the head, each node reads only wires that exist and are not yet
consumed, and writes only wires that did not exist; every result is an output that has not been
consumed. -/
def Circuit.WellFormed {m p : ℕ} {G : Set QGate} {S : Set (ProbFun m p)} {nIn r : ℕ}
    (Q : Circuit G S nIn r) : Prop :=
  Disjoint (Set.range Q.inputs) (Q.blanks : Set (Fin Q.N)) ∧
    Node.ValidRun Q.nodes (Set.range Q.inputs ∪ Q.blanks) (Set.range Q.inputs ∪ Q.blanks)
      (Set.range Q.results)

/-- The size of the circuit: its number of nodes (gates and subroutine calls). -/
def Circuit.size {m p : ℕ} {G : Set QGate} {S : Set (ProbFun m p)} {nIn r : ℕ}
    (Q : Circuit G S nIn r) : ℕ :=
  Q.nodes.length

/-- Theorem 2, p. 11 ("uses n gates from G"): the number of nodes labeled by a gate of `G`. -/
def Circuit.gateCount {m p : ℕ} {G : Set QGate} {S : Set (ProbFun m p)} {nIn r : ℕ}
    (Q : Circuit G S nIn r) : ℕ :=
  Q.nodes.countP fun v => v.op.isLeft

/-- Theorem 2, p. 11 ("and l subroutines from S"): the number of nodes labeled by a subroutine
of `S`. -/
def Circuit.subCount {m p : ℕ} {G : Set QGate} {S : Set (ProbFun m p)} {nIn r : ℕ}
    (Q : Circuit G S nIn r) : ℕ :=
  Q.nodes.countP fun v => v.op.isRight

/-- Definition 4, p. 9: the basis configuration of all wires for the input string `i`: bit
`i t` on the input wire `inputs t`, and `0` on every other wire (blanks, and wires not yet
created). -/
noncomputable def Circuit.inputConfig {m p : ℕ} {G : Set QGate} {S : Set (ProbFun m p)}
    {nIn r : ℕ} (Q : Circuit G S nIn r) (i : Qubits nIn) : Qubits Q.N :=
  overwrite Q.inputs (fun _ => false) i

end AKNMixed.FQP


