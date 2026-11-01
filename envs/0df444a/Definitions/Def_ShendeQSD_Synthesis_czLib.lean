-- Prove2me | Definitions.Def_ShendeQSD_Synthesis_czLib
-- name    : ShendeQSD_Synthesis_czLib
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:18:59.3618+00:00
-- url     : https://prove2.me/theorems/b2da8314-81e3-4344-8956-817fb6cbeab7
-- title:
--   Controlled-Z, and the gate library of one-qubit gates and controlled-Z
-- statement:
--   The **controlled-Z** gate is the two-qubit gate
--
--   $$
--   \text{Controlled-Z}=\mathrm{diag}(1,1,1,-1).
--   $$
--
--   The module defines its matrix `czMat`, the gate `czGate`, the library `czLib` of all one-qubit unitaries together with controlled-Z (on any ordered pair of distinct wires), and the **controlled-Z count** `czCount` of a circuit over that library (its number of two-qubit gates, each of which is a controlled-Z).
--
--   These are used in Appendix A.1, where the CNOTs of the multiplexed-$R_y$ circuits are replaced with controlled-Z gates.
--
--   **Formalization Note** The matrix is indexed by `Bool × Bool` with `false` $=|0\rangle$; the $-1$ sits at $|11\rangle$.
-- source:
--   Shende, Bullock, Markov, Synthesis of Quantum Logic Circuits, arXiv:quant-ph/0406176v5, Appendix A.1, Eq. (20), p. 16

import Definitions.Def_ShendeQSD_Synthesis_gateLib

namespace ShendeQSD.Synthesis

open QAlgorithms

/-- **The controlled-Z gate.**
Shende, Bullock, Markov, *Synthesis of Quantum Logic Circuits*, arXiv:quant-ph/0406176v5,
Appendix A.1, Eq. (20), p. 16: "Controlled-Z = diag(1, 1, 1, −1)".

**Formalization Note.** Indexed by `Bool × Bool` (`false` = `|0⟩`), the `−1` sits at `|11⟩`. -/
def czMat : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.diagonal fun p => if p.1 && p.2 then -1 else 1

/-- The controlled-Z gate as an arity-2 gate (Appendix A.1, p. 16). -/
def czGate : Gate :=
  Gate.ofMatrix2 czMat

/-- **The gate library of one-qubit gates and controlled-Z.**
Appendix A.1, p. 16: the circuits of Theorem 8 and Figure 2 "if all CNOTs are replaced with
controlled-Z gates".

**Formalization Note.** Every unitary one-qubit gate plus the single two-qubit gate `czGate`. -/
def czLib : Set Gate :=
  oneQubitGates ∪ {czGate}

/-- **The controlled-Z count of a circuit over `czLib`.**
**Formalization Note.** The number of arity-2 gate applications; every arity-2 gate of `czLib`
is `czGate`. -/
def czCount {n : ℕ} (c : Circuit czLib n) : ℕ :=
  c.countP fun g => g.gate.arity = 2

end ShendeQSD.Synthesis


