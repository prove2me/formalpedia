-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_nonOracleDepth
-- name    : QuantumLTF_Membership_Supplement_nonOracleDepth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:33:24.77718+00:00
-- url     : https://prove2.me/theorems/a4bd4825-936e-4a53-ad6d-79077e15fefa
-- title:
--   Non-oracle depth of an oracle circuit
-- statement:
--   The depth of an oracle circuit with all-to-all connectivity, where oracle calls cost nothing. Every wire carries a time, initially $0$.
--
--   1. A gate on the wires $W$ gets time $1+\max_{j\in W}\tau_j$, and the wires in $W$ take that time.
--   2. An oracle call on the wires $W$, including its control wire, gets time $\max_{j\in W}\tau_j$ and sets those wires to it.
--
--   The non-oracle depth is the largest final time. Equivalently, it is the largest number of gates on a chain of steps in which consecutive steps share a wire.
--
--   This is the depth measure of Theorems 4.9 and 4.10; the companion non-oracle gate count is the number of gate steps.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorems 4.9 and 4.10, pp. 54, 56 (PDF pp. 55, 57); §C.5, p. 95 (PDF p. 96)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit

namespace QuantumLTF.Membership.Supplement

open QAlgorithms

/-- **Non-oracle depth of an oracle circuit.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorems 4.9 and 4.10, pp. 54, 56 (PDF pp. 55,
57), and §C.5, p. 95 (PDF p. 96): "`O(log n log k)` non-oracle depth, assuming all-to-all connectivity".
The depth is computed by ASAP layering over the list of steps: every wire carries a time, initially
`0`; a gate on the wires `W` gets time `1 + max_{j ∈ W} τ_j` and sets the times of `W` to it; an
oracle call on its wires `W` (including its control wire) gets time `max_{j ∈ W} τ_j` (cost `0`) and
sets the times of `W` to it. The depth is the largest final time.

**Formalization Note.** Equivalently: the largest number of gates on a chain of steps in which
consecutive steps share a wire, oracle calls counting `0` but still ordering the wires they touch.
The non-oracle gate count is the base `OracleCircuit.gateCount`. -/
def nonOracleDepth {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ} (c : OracleCircuit S a m) : ℕ :=
  let wiresOf : OracleStep S a m → Finset (Fin m) := fun st => match st with
    | .gate g => Finset.univ.image g.wires
    | .query _ _ ctl wires _ =>
        Finset.univ.image wires ∪ (match ctl with | none => ∅ | some c => {c})
  let cost : OracleStep S a m → ℕ := fun st => match st with
    | .gate _ => 1
    | .query _ _ _ _ _ => 0
  let times : Fin m → ℕ := c.foldl (fun τ st =>
    let t := (wiresOf st).sup τ + cost st
    fun j => if j ∈ wiresOf st then t else τ j) (fun _ => 0)
  Finset.univ.sup times

end QuantumLTF.Membership.Supplement


