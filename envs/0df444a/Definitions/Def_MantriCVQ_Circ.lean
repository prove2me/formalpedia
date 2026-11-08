-- Prove2me | Definitions.Def_MantriCVQ_Circ
-- name    : MantriCVQ_Circ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:30.89763+00:00
-- url     : https://prove2.me/theorems/0dc7f42a-9016-4f9f-8dad-41323308fa56
-- title:
--   Quantum circuits with oracle gates
-- statement:
--   A **circuit with oracle gates** over a gate set $G$ on $N$ wires is a list of instructions applied in order. An instruction is either a gate of $G$ on distinct wires, or an oracle gate with an address register given by a list of distinct wires and an answer wire outside that list, acting by
--   $$|a\rangle|b\rangle\mapsto|a\rangle|b\oplus O(a)\rangle.$$
--   The **size** of a circuit is its number of instructions, its **query count** is its number of oracle gates, and its **description** is a bit string naming each gate by its index in $G$ and each wire by its number.
--
--   **Formalization Note** The address register may have any length, because an oracle is defined on strings of every length. The wire numbers are written in unary, which only affects descriptions by a polynomial.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3.1, p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_MantriCVQ_Gate
import Definitions.Def_QAdvFew_PoQOracle_Oracle

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ

/-- One instruction of a quantum circuit with oracle gates over the gate set `G` on `N` wires
(Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3.1, p. 14 (PDF p. 16)): a gate of `G` on
pairwise distinct wires, or an oracle gate `|a⟩|b⟩ ↦ |a⟩|b + O(a)⟩` whose address register is the
list `ws` of pairwise distinct wires and whose answer qubit is the wire `t`, not among them.

**Formalization Note** The address register may have any length, since an oracle is defined on
strings of every length. -/
inductive Instr (G : List Gate) (N : ℕ) where
  | gate (i : Fin G.length) (w : Fin (G.get i).k ↪ Fin N)
  | query (ws : List (Fin N)) (t : Fin N) (hnd : ws.Nodup) (ht : t ∉ ws)

/-- The action of an instruction with the oracle `O` on a state. The query is
`|y⟩ ↦ |y[t ↦ y_t ⊕ O(y|_ws)]⟩`, which is its own inverse. -/
noncomputable def Instr.apply {G : List Gate} {N : ℕ} (O : Oracle) :
    Instr G N → QState N → QState N
  | .gate i w, ψ => (G.get i).apply w ψ
  | .query ws t _ _, ψ => fun y => ψ (Function.update y t (xor (y t) (O (ws.map y))))

/-- A bit-string description of an instruction: a tag, then the index of the gate in the list `G`
and its wires, or the answer wire and the address wires, all written with `encNat`. -/
def Instr.enc {G : List Gate} {N : ℕ} : Instr G N → Str
  | .gate i w => encNat 0 ++ encNat (i : ℕ) ++
      encStr ((List.finRange (G.get i).k).map fun j => encNat (w j : ℕ))
  | .query ws t _ _ => encNat 1 ++ encNat (t : ℕ) ++ encStr (ws.map fun j => encNat (j : ℕ))

/-- A quantum circuit with oracle gates: a list of instructions, applied left to right. -/
abbrev Circ (G : List Gate) (N : ℕ) := List (Instr G N)

/-- The state after running a circuit with the oracle `O`. -/
noncomputable def Circ.run {G : List Gate} {N : ℕ} (c : Circ G N) (O : Oracle) (ψ : QState N) :
    QState N :=
  c.foldl (fun st i => i.apply O st) ψ

/-- The size of a circuit: its number of instructions. -/
def Circ.size {G : List Gate} {N : ℕ} (c : Circ G N) : ℕ := c.length

/-- The number of oracle gates of a circuit. -/
def Circ.queries {G : List Gate} {N : ℕ} (c : Circ G N) : ℕ :=
  c.countP fun i => match i with
    | .gate _ _ => false
    | .query _ _ _ _ => true

/-- The description of a circuit: the length-prefixed list of its instructions' descriptions. -/
def Circ.enc {G : List Gate} {N : ℕ} (c : Circ G N) : Str := encStr (c.map Instr.enc)

end MantriCVQ


