-- Prove2me | Definitions.Def_NKtLB_Supplement_OCircuit
-- name    : NKtLB_Supplement_OCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:33:38.427031+00:00
-- url     : https://prove2.me/theorems/4e987d76-bef0-42e7-9e93-0efa0595d0fd
-- title:
--   Boolean circuits with oracle gates
-- statement:
--   A **Boolean circuit with oracle gates** is a straight-line sequence of gates. Each gate is an input bit, a constant, a NOT, AND or OR of earlier gates, or an **oracle gate** that reads a list of earlier gates and outputs $1$ iff the string they form belongs to the oracle $O$. One gate is designated as the output. The **size** is the number of gates.
--
--   **Formalization Note** The paper fixes no circuit model. An oracle gate of any fan-in counts as one gate.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §1.2.4, p.12

import Mathlib

namespace NKtLB.Supplement

/-- **Gates of an oracle circuit** (for `SIZE^O[s]`, Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), §1.2.4, p.12: "Boolean circuits with
oracle access to `O`"): an input bit, a constant, a NOT/AND/OR of earlier wires, or an oracle gate
reading a list of earlier wires. -/
inductive OGate
  | inp (i : ℕ)
  | const (b : Bool)
  | neg (i : ℕ)
  | and (i j : ℕ)
  | or (i j : ℕ)
  | orc (is : List ℕ)

/-- The value of a gate on input `x` with oracle `O`, given the values `vals` of the earlier wires
(an out-of-range index reads `false`); an oracle gate outputs whether the string of its input wires
belongs to `O`. -/
noncomputable def OGate.eval (O : Set (List Bool)) (g : OGate) (x vals : List Bool) : Bool := by
  classical
  exact match g with
    | OGate.inp i => x.getD i false
    | OGate.const b => b
    | OGate.neg i => !(vals.getD i false)
    | OGate.and i j => vals.getD i false && vals.getD j false
    | OGate.or i j => vals.getD i false || vals.getD j false
    | OGate.orc is => decide (is.map (fun i => vals.getD i false) ∈ O)

/-- **Single-output Boolean circuits with oracle gates**: a straight-line list of gates (wire `i`
is the value of gate `i`) and an output wire. The size is the number of gates.

**Formalization Note.** The paper fixes no circuit model; an oracle gate of any fan-in counts as
one gate. -/
structure OCircuit where
  gates : List OGate
  out : ℕ

/-- The wire values on input `x` with oracle `O`. -/
noncomputable def OCircuit.wires (O : Set (List Bool)) (C : OCircuit) (x : List Bool) : List Bool :=
  C.gates.foldl (fun vals g => vals ++ [g.eval O x vals]) []

/-- The output bit on input `x` with oracle `O`. -/
noncomputable def OCircuit.eval (O : Set (List Bool)) (C : OCircuit) (x : List Bool) : Bool :=
  (C.wires O x).getD C.out false

/-- The size: the number of gates. -/
def OCircuit.size (C : OCircuit) : ℕ := C.gates.length

end NKtLB.Supplement


