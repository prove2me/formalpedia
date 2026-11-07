-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_OInstr
-- name    : QAdvFew_PoQOracle_OInstr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:57.706189+00:00
-- url     : https://prove2.me/theorems/0155e8a6-c590-4837-93c4-c93dd919ef81
-- title:
--   Oracle quantum circuits
-- statement:
--   An **oracle quantum circuit** on $m$ wires is a list of instructions, each either a Clifford+T gate ($H$, $S$, $T$, $X$, CNOT) or an oracle gate. The oracle gate on query wires $ws$ and an answer wire $a\notin ws$ acts on basis states by
--   $$
--   |x_{ws}, z_a\rangle \mapsto |x_{ws}, z_a\oplus O(x_{ws})\rangle .
--   $$
--   This module also defines the action on amplitude vectors, the bit-string code of a circuit, and basis states.
--
--   **Formalization Note** Clifford+T is the "fixed finite universal gate set" of p. 12. The oracle gate is its own inverse, and a controlled query is built from Toffoli gates or a query with extra query wires, so "controlled queries and queries to its inverse" need no separate gate.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §3.2.1–§3.2.2, p. 12 (PDF p. 14)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAdvFew_PoQOracle_Oracle

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- An instruction of an **oracle quantum circuit** on `m` wires (Goldin, Lombardi, Morimae,
*Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, §3.2.1–§3.2.2, p. 12
(PDF p. 14): "Quantum algorithms use a fixed finite universal gate set, computational basis
measurements, and ancillas initialized to `|0⟩`"; "A classical function `f` is accessed quantumly
through the map `|x, z⟩ ↦ |x, z ⊕ f(x)⟩`"): a Clifford+T gate (`QAlgorithms.Complexity.Instr`:
`H, S, T, X, CNOT`), or an oracle gate `query ws a`, which XORs onto wire `a` the oracle's answer
on the bit string read from the wires `ws` in order.

**Formalization Note** The answer wire is not among the query wires (`a ∉ ws`), so the oracle gate
is a permutation of basis states and is its own inverse. "Controlled queries and queries to its
inverse" (p. 12) therefore need no separate gate: the gate is self-inverse, and a controlled query
is a query with the control wire appended to the query wires of a modified oracle, or is built from
Toffoli gates, which Clifford+T approximates. -/
inductive OInstr (m : ℕ) where
  | gate (g : Instr m)
  | query (ws : List (Fin m)) (a : Fin m) (h : a ∉ ws)

namespace OInstr

/-- The action of an instruction on an amplitude vector, with oracle `O`. -/
noncomputable def apply {m : ℕ} (O : Oracle) : OInstr m → QState m → QState m
  | .gate g => g.apply
  | .query ws a _ => fun ψ y => ψ (Function.update y a (xor (y a) (O (ws.map y))))

/-- An instruction as a bit string: Clifford+T gates as in `QAlgorithms.Complexity.encInstr`, an
oracle gate as the tag `5`, the number of query wires, the query wires, and the answer wire, all
in unary. -/
def enc {m : ℕ} : OInstr m → Str
  | .gate g => encInstr g
  | .query ws a _ => encNat 5 ++ encNat ws.length ++ (ws.map (fun w => encNat (w : ℕ))).flatten ++
      encNat (a : ℕ)

end OInstr

/-- An oracle quantum circuit: a sequence of instructions, applied left to right. -/
abbrev OCirc (m : ℕ) := List (OInstr m)

namespace OCirc

/-- Running a circuit with oracle `O`. -/
noncomputable def run {m : ℕ} (O : Oracle) (c : OCirc m) (ψ : QState m) : QState m :=
  c.foldl (fun st g => g.apply O st) ψ

/-- The code of a circuit: the length-prefixed list of instruction codes. -/
def enc {m : ℕ} (c : OCirc m) : Str := encStr (c.map OInstr.enc)

end OCirc

/-- The computational basis state `|y₀⟩`. -/
def basisState {m : ℕ} (y₀ : Bits m) : QState m := fun y => if y = y₀ then 1 else 0

end QAdvFew.PoQOracle


