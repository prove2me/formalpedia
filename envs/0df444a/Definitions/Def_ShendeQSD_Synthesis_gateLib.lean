-- Prove2me | Definitions.Def_ShendeQSD_Synthesis_gateLib
-- name    : ShendeQSD_Synthesis_gateLib
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:43.724514+00:00
-- url     : https://prove2.me/theorems/f099f3ff-20ff-4f99-a6a3-634d915e8ff8
-- title:
--   The gate library: all one-qubit unitaries and CNOT
-- statement:
--   The paper synthesizes circuits over the **gate library** consisting of
--
--   1. every one-qubit gate, i.e. every unitary $2\times2$ matrix $U\in U(2)$ (including global phases), and
--   2. the controlled-NOT gate $\mathrm{CNOT}=I\oplus\sigma_x$, $|b_1\rangle|b_2\rangle\mapsto|b_1\rangle|b_1\oplus b_2\rangle$.
--
--   Placed in a circuit, a one-qubit gate may act on any wire and a CNOT on any ordered pair of distinct wires (control, target). No other two-qubit gate belongs to the library, so the number of two-qubit gates in a circuit over this library is its number of CNOTs. The module also defines the two pieces, `oneQubitGates` (arity one, unitary) and `cnotGate`.
--
--   **Formalization Note** Gates are the published `QAlgorithms.Gate` (a matrix on a number of qubits); `cnotGate` is `Gate.ofMatrix2 QAlgorithms.cnot`, whose gate wire $0$ is the control.
-- source:
--   Shende, Bullock, Markov, Synthesis of Quantum Logic Circuits, arXiv:quant-ph/0406176v5, §3.1, Eq. (14), p. 9

import Definitions.Def_QAlgorithms_Defs_Circuit

namespace ShendeQSD.Synthesis

open QAlgorithms

/-- **One-qubit gates.**
Shende, Bullock, Markov, *Synthesis of Quantum Logic Circuits*, arXiv:quant-ph/0406176v5,
§2.2, p. 5 and §3.1, p. 9: the one-qubit gates of the gate library are all unitary `2 × 2`
matrices.

**Formalization Note.** A gate of arity `1` whose matrix is unitary; every element of `U(2)` is
allowed, so a global phase on a one-qubit gate is free. -/
def oneQubitGates : Set Gate :=
  {g | g.arity = 1 ∧ g.IsUnitary}

/-- **The CNOT gate as a two-qubit gate.**
Shende, Bullock, Markov, arXiv:quant-ph/0406176v5, §3.1, Eq. (14), p. 9:
"CNOT = I ⊕ σ_x", `|b1⟩|b2⟩ ↦ |b1⟩|b1 XOR b2⟩`.

**Formalization Note.** The published matrix `QAlgorithms.cnot` (control = first factor) turned
into an arity-2 gate; gate wire `0` is the control, gate wire `1` the target. Placed in a circuit,
it may act on any ordered pair of distinct wires. -/
def cnotGate : Gate :=
  Gate.ofMatrix2 cnot

/-- **The gate library: one-qubit gates and CNOT.**
Shende, Bullock, Markov, arXiv:quant-ph/0406176v5, §3.1, p. 9: "The CNOT, together with the
one-qubit gates defined in §2, forms a universal gate library for quantum circuits."

**Formalization Note.** Every unitary one-qubit gate, plus the single two-qubit gate `cnotGate`.
No other two-qubit gate is in the library, so counting arity-2 gates counts CNOTs. -/
def gateLib : Set Gate :=
  oneQubitGates ∪ {cnotGate}

end ShendeQSD.Synthesis


