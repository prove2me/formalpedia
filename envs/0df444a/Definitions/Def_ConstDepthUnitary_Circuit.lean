-- Prove2me | Definitions.Def_ConstDepthUnitary_Circuit
-- name    : ConstDepthUnitary_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:45:05.475468+00:00
-- url     : https://prove2.me/theorems/4a073fd7-5b7b-457e-99b6-87544962a430
-- title:
--   Layers, circuits, depth, size
-- statement:
--   A **layer** is a list of gates with pairwise disjoint supports, and a **circuit** is a finite sequence of layers. Its **depth** is the number of layers, its **size** the total number of gates. The matrix of a layer is the product of its gates, and the matrix of a circuit with layers $l_1,\dots,l_d$ is
--   $$l_d\cdots l_2\,l_1,$$
--   so $l_1$ is applied first. A circuit is **standard** if all its gates are one- or two-qubit gates; `maxFanout` is the largest size of one of its fan-out gates ($0$ if there is none).
--
--   These are the objects whose depth every theorem of the mission bounds; without disjointness, depth one could hold any circuit.
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §3.1, p.14

import Mathlib
import Definitions.Def_ConstDepthUnitary_Gate

namespace ConstDepthUnitary

/-- A layer: a list of gates with pairwise disjoint supports. Depth counts these layers.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §3.1, p.14; p.3 (depth). -/
structure Layer (W : Type) [DecidableEq W] where
  /-- The gates of the layer. -/
  gates : List (Gate W)
  /-- The gates act on pairwise disjoint sets of wires. -/
  disjoint : gates.Pairwise fun g h => Disjoint g.support h.support

/-- The matrix of a layer: the product of its gates (they commute, by disjointness). -/
noncomputable def Layer.matrix {W : Type} [Fintype W] [DecidableEq W] (l : Layer W) :
    Matrix (W → Bool) (W → Bool) ℂ :=
  (l.gates.map Gate.matrix).prod

/-- A circuit: a list of layers, the head layer applied first. -/
abbrev Circuit (W : Type) [DecidableEq W] := List (Layer W)

namespace Circuit

variable {W : Type} [DecidableEq W]

/-- The matrix of a circuit. The head layer acts first, so it is the rightmost factor:
`matrix [l₁, …, l_d] = l_d.matrix * ⋯ * l₁.matrix`. -/
noncomputable def matrix [Fintype W] : Circuit W → Matrix (W → Bool) (W → Bool) ℂ
  | [] => 1
  | l :: ls => matrix ls * l.matrix

/-- The depth: the number of layers. -/
def depth (C : Circuit W) : ℕ := C.length

/-- The size: the total number of gates. -/
def size (C : Circuit W) : ℕ := (C.map fun l => l.gates.length).sum

/-- A circuit of the standard model: every gate is a one- or two-qubit unitary. -/
def IsStandard (C : Circuit W) : Prop := ∀ l ∈ C, ∀ g ∈ l.gates, g.IsStandard

/-- The largest number of qubits a fan-out gate of the circuit acts on (`0` if it has none). -/
def maxFanout (C : Circuit W) : ℕ :=
  (C.map fun l => (l.gates.map Gate.fanoutSize).foldr max 0).foldr max 0

end Circuit

end ConstDepthUnitary


