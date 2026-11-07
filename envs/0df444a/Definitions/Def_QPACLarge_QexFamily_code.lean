-- Prove2me | Definitions.Def_QPACLarge_QexFamily_code
-- name    : QPACLarge_QexFamily_code
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:52.857205+00:00
-- url     : https://prove2.me/theorems/43890694-1791-4528-b309-1204c686eee6
-- title:
--   Description of a quantum learner
-- statement:
--   The **description** of the learner at index $i$ is the bit string listing the number of examples and the number of ancillas (in unary), then the number of output wires and the output wires, then the circuit (number of layers; per layer the number of gates; per gate its type $H, S, T, X, \mathrm{CNOT}$ and its wires), every one of these numbers in self-delimiting binary. A learner "runs in time $T$" when a machine prints this description within $T$ steps and the circuit has at most $T$ gates.
--
--   **Formalization Note** The example count is in unary and every gate contributes at least four bits, so the gate count and the example count are at most the description length; a polynomial-time generator therefore bounds both by a polynomial. Wire indices are in binary: in unary a circuit on $m$ examples would have a description of length quadratic in $m$, and no learner could be printed in time $m \cdot \mathrm{poly}(n)$ as Theorem 3.6 states.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.3, p.16

import Mathlib
import Definitions.Def_QPACLarge_QexFamily
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding

namespace QPACLarge

open QAlgorithms QAlgorithms.Complexity QAlgorithms.LocalHamiltonian

/-- **The description of a quantum learner at an index.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.3, p.16: "given `n` we can print the description of `Qₙ` in deterministic time
`T(n)`".

The description printed by a uniform generator: the example count and the ancilla count in unary
(`encNat`), then the number of output wires and the output wires, then the circuit (the number of
layers; per layer the number of instructions; per instruction its tag `H, S, T, X, CNOT` = 0–4 and
its wires), every one of these numbers in the published self-delimiting binary code `encBin`.

**Formalization Note.** The example count is in unary and every instruction contributes at least
four bits, so the example count and the gate count are at most the length of the description.
Wire indices are in binary: in unary (the published `encCirc`) a circuit on `m` examples would have
a description of length quadratic in `m`, and the time bound `m · poly(n)` of Theorem 3.6 could not
be met. -/
def QexFamily.code {ι : Type} {dim : ι → ℕ} (L : QexFamily ι dim) (i : ι) : Str :=
  encNat (L.ex i) ++ encNat (L.anc i) ++ encBin (L.out i).length ++
    ((L.out i).map fun w => encBin (w : ℕ)).flatten ++ encBin (L.circ i).length ++
    ((L.circ i).map fun l => encBin l.length ++
      (l.map fun g => match g with
        | .h j => encBin 0 ++ encBin (j : ℕ)
        | .s j => encBin 1 ++ encBin (j : ℕ)
        | .t j => encBin 2 ++ encBin (j : ℕ)
        | .x j => encBin 3 ++ encBin (j : ℕ)
        | .cnot j j' _ => encBin 4 ++ encBin (j : ℕ) ++ encBin (j' : ℕ)).flatten).flatten

end QPACLarge


