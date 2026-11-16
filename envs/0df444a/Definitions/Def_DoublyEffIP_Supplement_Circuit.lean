-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_Circuit
-- name    : DoublyEffIP_Supplement_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:25:03.531288+00:00
-- url     : https://prove2.me/theorems/21fbe015-03b1-43b4-8df9-d4140ebcf04e
-- title:
--   An arithmetic circuit (gates and output wires)
-- statement:
--   An **arithmetic circuit** is a finite list of gates in topological order together with a list of output wires. Its **size** is the number of gates.
--
--   Applied to an input list of length $n$, wire $w<n$ is the $w$-th input and wire $n+j$ is the $j$-th gate. This is the circuit model of the paper's uniform arithmetic circuits; size is "the number of gates in the circuit".
--
--   **Formalization Note** The number of inputs is not stored in the circuit; it is fixed by the circuit's shape parameters.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3, p.8 (size); Section 3.2, p.9, Definition 3

import Mathlib
import Definitions.Def_DoublyEffIP_Supplement_Gate

set_option autoImplicit false

namespace DoublyEffIP.Supplement

/-- **An arithmetic circuit** — Definition 3 of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), Section 3.2, p.9 ("a family of arithmetic
circuits, consisting of fan-in 2 ADD and MULT gates over a field F"), with "size(V) is the number
of gates in the circuit" (p.8).

A circuit is a list of gates, in topological order, and a list of output wires. Its size is the
number of gates, `gates.length`.

**Formalization Note.** The number of inputs is not stored: a circuit is applied to an input list
of the length given by its shape parameters, and wire `w` is input `w` if `w` is below that length,
else gate `w − (number of inputs)`. -/
structure Circuit where
  /-- the gates, in topological order -/
  gates : List Gate
  /-- the output wires -/
  outputs : List ℕ

end DoublyEffIP.Supplement


