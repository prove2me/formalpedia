-- Prove2me | Definitions.Def_QPACLarge_encBoolCircuitBin
-- name    : QPACLarge_encBoolCircuitBin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:33.546206+00:00
-- url     : https://prove2.me/theorems/386012fe-dc0c-47a3-a41b-1b103d99d9fb
-- title:
--   Binary description of a Boolean circuit
-- statement:
--   The **binary description** of a Boolean circuit $C$ (AND, OR, NOT gates, one output) is the bit string listing the number of gates, then for each gate its type (AND, OR, NOT as $0, 1, 2$) and its two argument wires, then the output wire, every number in self-delimiting binary. The code is prefix-free, so a bit string begins with the description of at most one circuit. Quantum learners in this mission output their hypothesis in this code.
--
--   **Formalization Note** The published `encBoolCircuit` writes wire indices in unary, which makes the description of a circuit of size $S$ whose gates are all used at least about $S^2/2$ bits long; the majority-of-$m$ hypothesis of Theorem 3.6 could then not be printed in time $m \cdot \mathrm{poly}(n)$ for $m$ close to $2^n$. In binary the description has $O(S\log S)$ bits.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.3, p.16; Theorem 3.6, p.29

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QAlgorithms_Defs_LearningSeparation

namespace QPACLarge

open QAlgorithms QAlgorithms.Complexity QAlgorithms.Learning QAlgorithms.LocalHamiltonian

/-- **The description of a Boolean circuit, with numbers in binary.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.3, p.16: every learner of the paper "produces a classical deterministic Boolean circuit as its output hypothesis"; Theorem 3.6, p.29 and Theorem 1.2, p.5 bound the time to produce it by `m · poly(n)` and `poly(n)/η`.

The number of gates, then each gate's opcode (`and`, `or`, `not` = 0, 1, 2, the published
`boolOpCode`) and its two argument wires, then the output wire, every number in the published
self-delimiting binary code `encBin`. The code is prefix-free, so an output string begins with
the description of at most one circuit.

**Formalization Note.** The published `encBoolCircuit` writes wire indices in unary, so a circuit
with `S` gates whose gates are all used has a description of length at least about `S²/2`; a
learner that must print the majority of `m` hypotheses could then not run in time `m · poly(n)`
for `m` close to `2ⁿ`. In binary the description has `O(S log S)` bits, which is what the paper's
time bounds count. -/
def encBoolCircuitBin {n : ℕ} (C : BoolCircuit n 1) : Str :=
  encBin C.gates.length ++
    (C.gates.map fun g => encBin (boolOpCode g.op) ++ encBin g.a ++ encBin g.b).flatten ++
    encBin (C.outputs 0)

end QPACLarge


