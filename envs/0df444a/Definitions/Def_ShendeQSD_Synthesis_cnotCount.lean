-- Prove2me | Definitions.Def_ShendeQSD_Synthesis_cnotCount
-- name    : ShendeQSD_Synthesis_cnotCount
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:18:47.606081+00:00
-- url     : https://prove2.me/theorems/096c679f-31b0-475c-a37a-c83c5b137165
-- title:
--   CNOT count of a circuit
-- statement:
--   The cost of a circuit over the gate library of one-qubit gates and CNOT is its **CNOT count**: the number of CNOT gates it contains, whichever ordered pair of wires each acts on.
--
--   This is the cost measure of the whole paper; the quantity $c_n$ of §5.3 and the bound of Eq. (19) are CNOT counts.
--
--   **Formalization Note** The count is the number of gate applications of arity two in the list of gates. Every arity-two gate of the library is the CNOT and the one-qubit gates have arity one, so this counts exactly the CNOTs.
-- source:
--   Shende, Bullock, Markov, Synthesis of Quantum Logic Circuits, arXiv:quant-ph/0406176v5, p. 2 and §5.3, p. 14

import Definitions.Def_ShendeQSD_Synthesis_gateLib

namespace ShendeQSD.Synthesis

open QAlgorithms

/-- **The CNOT count of a circuit.**
Shende, Bullock, Markov, *Synthesis of Quantum Logic Circuits*, arXiv:quant-ph/0406176v5,
p. 2 and §5.3, p. 14: the cost of a circuit is its number of CNOT gates.

**Formalization Note.** The number of gate applications of arity `2` in the circuit. Every gate
of `gateLib` of arity `2` is `cnotGate` (the one-qubit gates have arity `1`), so this is exactly
the number of CNOTs, on whichever ordered pairs of wires they act. -/
def cnotCount {n : ℕ} (c : Circuit gateLib n) : ℕ :=
  c.countP fun g => g.gate.arity = 2

end ShendeQSD.Synthesis


