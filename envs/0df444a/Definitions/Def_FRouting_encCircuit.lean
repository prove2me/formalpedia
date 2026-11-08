-- Prove2me | Definitions.Def_FRouting_encCircuit
-- name    : FRouting_encCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:55.951144+00:00
-- url     : https://prove2.me/theorems/11e6e8d4-75a0-4d5f-923c-116af2243c45
-- title:
--   The description of a circuit
-- statement:
--   The string a machine prints for a circuit: $d$ in self-delimiting binary, the input, output and ancilla widths in unary, the kept wires in binary, the number of gates, and the gates, each a tag followed by its wires in binary.
--
--   The description is what "prints a description" means in Definitions 1.2 and 3.6. $d$ in binary and the widths in unary place $\log d$ and the width within a printing machine's budget, the term the paper charges on p.22.
--
--   **Formalization Note** The encoding is injective and self-delimiting, proved in the mission's verification file, so printing a description determines the circuit.
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Definition 1.2, p.4; proof of Lemma 5.7, p.22

import Definitions.Def_FRouting_Circuit
import Definitions.Def_QAlgorithms_ClassicalStringComputability

set_option autoImplicit false

namespace FRouting

open QAlgorithms.Complexity

/-- A natural number in binary, self-delimiting: every bit `b` becomes `true, b`, and `false` ends
the number. Its length is `2 ⌈log₂(k + 1)⌉ + 1`. -/
def encBin (k : ℕ) : Str :=
  (k.bits.flatMap fun b => [true, b]) ++ [false]

/-- The description of one gate: a tag, then its wires in binary. -/
def encGate {d W : ℕ} : Gate d W → Str
  | .shift w => encBin 0 ++ encBin w
  | .clock w => encBin 1 ++ encBin w
  | .fourier w => encBin 2 ++ encBin w
  | .tee w => encBin 3 ++ encBin w
  | .sum c t _ => encBin 4 ++ encBin c ++ encBin t

/-- **The description of a circuit.** Renard, *Computational Bounds for f-Routing*, arXiv:2609.40278
(held copy, sha256 4a327f29…), pp.4, 22, speaks of the "description" a generator prints without fixing
it. Here: `d` in binary, the widths in unary, then the kept wires, the number of gates and the gates.

**Formalization Note** `d` is in binary and the widths in unary, so that a machine printing the
description has `log d` and the width within its budget, as p.22 charges (`T + log d`). The encoding
is injective and self-delimiting; both are proved in the verification file of this mission. -/
def encCircuit {d inW outW : ℕ} (C : Circuit d inW outW) : Str :=
  encBin d ++ encNat inW ++ encNat outW ++ encNat C.ancillas ++
    (List.ofFn C.kept).flatMap (fun w => encBin w.val) ++
    encBin C.gates.length ++ C.gates.flatMap encGate

end FRouting


