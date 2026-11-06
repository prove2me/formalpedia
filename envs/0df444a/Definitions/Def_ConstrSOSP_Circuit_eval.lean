-- Prove2me | Definitions.Def_ConstrSOSP_Circuit_eval
-- name    : ConstrSOSP_Circuit_eval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:27.949685+00:00
-- url     : https://prove2.me/theorems/3f3cea63-ea50-4ae6-b6dc-0cb91380bf82
-- title:
--   Evaluation of a Boolean circuit
-- statement:
--   The **evaluation** of a circuit on an input bit list computes the wire values gate by gate, starting from the input bits, and returns the values of the output wires in order.
--
--   **Formalization Note** A wire index out of range reads `false`; this never happens for well-formed circuits on inputs of length $n$.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §4.1, p.17

import Mathlib
import Definitions.Def_ConstrSOSP_Circuit

namespace ConstrSOSP

/-- **Evaluation of a Boolean circuit** on an input bit list (arXiv:2604.02285, 2 Nov 2026, §4.1,
p.17).

The wire values are computed gate by gate: starting from the input list, the `k`-th gate appends
the value of its gate (`∧`, `∨` of two earlier wires, `¬` of one) as wire `n + k`. The output is
the list of the values of the output wires `C.outs`.

**Formalization Note** A wire index out of range reads `false` (`List.getD`); on well-formed
circuits (`Circuit.WF`) with an input of length `n` no index is out of range. -/
def Circuit.eval (C : Circuit) (inp : List Bool) : List Bool :=
  let wires := C.gates.foldl (fun ws g =>
    ws ++ [match g with
      | Gate.andG i j => ws.getD i false && ws.getD j false
      | Gate.orG i j => ws.getD i false || ws.getD j false
      | Gate.notG i => !(ws.getD i false)]) inp
  C.outs.map (fun o => wires.getD o false)

end ConstrSOSP


