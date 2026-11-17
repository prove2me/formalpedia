-- Prove2me | Definitions.Def_FRouting_Supplement_measureProb
-- name    : FRouting_Supplement_measureProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:21:28.619659+00:00
-- url     : https://prove2.me/theorems/4f7d04ed-46c2-4734-816c-1dcf4afbfbc6
-- title:
--   Measuring the output of a qubit circuit
-- statement:
--   For a qubit circuit $C$ with no input wires and $m$ kept wires, run on $|0\cdots0\rangle$ with output state $\sigma$, measuring the kept qubits in the computational basis gives the string $o\in\{0,1\}^m$ with probability $\langle o|\sigma|o\rangle$. For a property $E$ of binary strings, $\Pr[E]=\sum_{o\in E}\langle o|\sigma|o\rangle$.
--
--   This gives the output distribution of the bounded-error quantum algorithm of Theorem 7.10: a classical machine prints a circuit, which is run and measured.
--
--   **Formalization Note** Intermediate measurements and classical post-processing are deferred into the circuit by purification, the paper's convention (footnotes 1 and 3).
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Theorem 7.10, p.35

import Definitions.Def_FRouting_Circuit
import Definitions.Def_QAlgorithms_ClassicalStringComputability

set_option autoImplicit false

open Matrix

namespace FRouting.Supplement

open QAlgorithms.Complexity

/-- A computational-basis outcome of `m` qubits as a binary string (`|1⟩ ↦ true`). -/
def bitsOf {m : ℕ} (o : Fin m → Fin 2) : Str :=
  List.ofFn fun i => decide (o i = 1)

open scoped Classical in
/-- **The probability that measuring the output of a qubit circuit gives a string in `E`.** A qubit
circuit with no input wires is run on `|0…0⟩`, and its `m` kept qubits are measured in the computational
basis: outcome `o` has the Born probability `⟨o|σ|o⟩`, `σ` the circuit's output state. Used for the
"bounded-error quantum algorithm" of Renard, *Computational Bounds for f-Routing*, arXiv:2609.40278
(held copy, sha256 4a327f29…), Theorem 7.10, p.35.

**Formalization Note** Intermediate measurements and classical post-processing are deferred into the
circuit (purification, the paper's convention, footnotes 1 and 3). -/
noncomputable def measureProb {m : ℕ} (C : Circuit 2 0 m) (E : Str → Prop) : ℝ :=
  ∑ o : Fin m → Fin 2, if E (bitsOf o) then (C.outputState o o).re else 0

end FRouting.Supplement


