-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_circuitDepth
-- name    : DoublyEffIP_Supplement_circuitDepth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:26:20.186192+00:00
-- url     : https://prove2.me/theorems/6566eaf0-9869-4104-a207-6afdd3de55bf
-- title:
--   The depth of an arithmetic circuit
-- statement:
--   For a circuit with $n$ inputs, inputs and constant sources have depth $0$, an ADD or MULT gate has depth one more than the larger depth of its two input wires, and the **depth** of the circuit is the largest depth of an output wire ($0$ if there are no outputs). It is the length of a longest path from an input to an output.
--
--   **Formalization Note** A reference to a non-existent wire has depth $0$, matching its value $0$.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3, p.8 (depth(V) is the depth of the circuit)

import Mathlib
import Definitions.Def_DoublyEffIP_Supplement_Circuit

set_option autoImplicit false

namespace DoublyEffIP.Supplement

/-- **The depth of a circuit** — "depth(V) is the depth of the circuit" (Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), Section 3, p.8),
the length of a longest path from an input to an output.

With `n` inputs, inputs and constant sources have depth `0`, an `add`/`mul` gate has depth one more
than the larger depth of its two input wires, and the circuit's depth is the largest depth of an
output wire (`0` if there is none).

**Formalization Note.** A reference to a wire that does not exist has depth `0`, matching
`evalCircuit`, which reads it as `0`. -/
def circuitDepth (n : ℕ) (C : Circuit) : ℕ :=
  let ds := C.gates.foldl (fun ds g => ds ++ [match g with
      | .add i j => max (ds.getD i 0) (ds.getD j 0) + 1
      | .mul i j => max (ds.getD i 0) (ds.getD j 0) + 1
      | _ => 0]) (List.replicate n 0)
  C.outputs.foldl (fun m o => max m (ds.getD o 0)) 0

end DoublyEffIP.Supplement


