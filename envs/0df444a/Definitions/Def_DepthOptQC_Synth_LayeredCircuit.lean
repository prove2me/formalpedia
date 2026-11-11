-- Prove2me | Definitions.Def_DepthOptQC_Synth_LayeredCircuit
-- name    : DepthOptQC_Synth_LayeredCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:11:25.259068+00:00
-- url     : https://prove2.me/theorems/02606ab6-5e86-4b18-bf24-67264a0d1458
-- title:
--   Layered circuits over a gate set: layers of gates on disjoint qubits, depth, size, unitary
-- statement:
--   Fix a gate set $\mathcal G$ and a number $n$ of qubits (wires). A **layer** is a finite list of gates of $\mathcal G$, each placed on an ordered tuple of distinct wires, such that any two gates of the layer act on disjoint sets of wires. A **layered circuit** $C = (L_1,\dots,L_d)$ is a finite sequence of layers, applied in order ($L_1$ first). Its
--
--   1. **depth** is the number $d$ of layers;
--   2. **size** (gate count) is the total number of gates over all layers;
--   3. **unitary** is the product of the gates' matrices, each tensored with the identity on the wires it does not touch, the first gate of $L_1$ acting first.
--
--   The circuits are fully unitary: there is no intermediate measurement, no postselection and no pre-supplied resource state. This is the circuit model in which every depth, size and space bound of the mission is stated.
--
--   **Formalization Note** Gates, gate applications and flat circuits are the shared `QAlgorithms` layer (`Gate` = arity and matrix, `GateApp` = a gate of the set on an injective wire tuple, `Circuit.unitary` = ordered product of embedded matrices). Gates inside one layer act on disjoint wires, so their order inside the layer does not change the unitary.
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, §1.1, p.4 (circuit model); Lemma 3's proof, p.18 (gates on disjoint qubits run in parallel)

import Definitions.Def_QAlgorithms_Defs_Circuit

namespace DepthOptQC.Synth

open QAlgorithms

/-- **A layer of gates on disjoint qubits** (Vasconcelos, *Depth-Optimal Quantum Compilation*,
arXiv:2609.34659, §1.1, p.4, and Lemma 3's proof, p.18: "The equality Toffoli and the first CNOT act
on disjoint qubits and may be performed simultaneously"). A layer over the gate set `S` on `n` wires
is a list of gate applications (gates of `S` placed on injective wire tuples, the shared
`QAlgorithms.GateApp`) whose wire sets are pairwise disjoint.

**Formalization Note.** The paper's depth counts such layers (reading R3). The order of the gates
inside a layer is immaterial for the unitary, since gates on disjoint wires commute; the list is
applied head first, like `QAlgorithms.Circuit`. -/
structure Layer (S : Set Gate) (n : ℕ) where
  /-- The gates of the layer. -/
  gates : Circuit S n
  /-- Any two distinct gates of the layer act on disjoint sets of wires. -/
  disjoint : gates.Pairwise (fun g h => Disjoint (Set.range g.wires) (Set.range h.wires))

/-- **A layered circuit** (Vasconcelos, arXiv:2609.34659, §1.1, p.4): a fully unitary circuit over
the gate set `S` on `n` wires, given as a list of layers applied in list order (head layer first).
No measurement, postselection or pre-supplied resource state is part of the model (§1.1, p.4). -/
abbrev LayeredCircuit (S : Set Gate) (n : ℕ) := List (Layer S n)

/-- **Depth** (Vasconcelos, arXiv:2609.34659, §1.1, p.4; reading R3): the number of layers. -/
def LayeredCircuit.depth {S : Set Gate} {n : ℕ} (c : LayeredCircuit S n) : ℕ :=
  c.length

/-- **Size (gate count)** (Vasconcelos, arXiv:2609.34659, Theorem 1, p.6; Eq. (99), p.25): the total
number of gate applications over all layers. -/
def LayeredCircuit.size {S : Set Gate} {n : ℕ} (c : LayeredCircuit S n) : ℕ :=
  (c.map fun l => l.gates.length).sum

/-- The flat gate list of a layered circuit: its layers concatenated, head layer first. -/
def LayeredCircuit.toCircuit {S : Set Gate} {n : ℕ} (c : LayeredCircuit S n) : Circuit S n :=
  (c.map Layer.gates).flatten

/-- **The unitary implemented by a layered circuit** (Vasconcelos, arXiv:2609.34659, §1.1, p.4):
the product of its gates' embedded matrices, the first gate of the first layer acting first
(`QAlgorithms.Circuit.unitary` of the flattened list). -/
noncomputable def LayeredCircuit.unitary {S : Set Gate} {n : ℕ} (c : LayeredCircuit S n) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  c.toCircuit.unitary

end DepthOptQC.Synth


