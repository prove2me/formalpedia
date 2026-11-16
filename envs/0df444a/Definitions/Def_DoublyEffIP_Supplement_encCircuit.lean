-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_encCircuit
-- name    : DoublyEffIP_Supplement_encCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:27:39.88573+00:00
-- url     : https://prove2.me/theorems/15778f75-ad85-4185-a3ee-dd5c17d1893e
-- title:
--   The description of a circuit as a bit string
-- statement:
--   The **description** $\langle C\rangle$ of a circuit $C$ is the self-delimiting list of its gate codes followed by the self-delimiting list of its output wires.
--
--   The encoding is self-delimiting, so a description determines its circuit. It is "the full description of the circuit $C_n$" that a uniform generating machine writes on its output.
--
--   **Formalization Note** The list encoding is the published `encodeList` of the `SubexponentialSAT` definition.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.2, p.9, Definition 3

import Mathlib
import Definitions.Def_DoublyEffIP_Supplement_Circuit
import Definitions.Def_DoublyEffIP_Supplement_encGate
import Definitions.Def_DoublyEffIP_encBin

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT

namespace DoublyEffIP.Supplement

/-- **The description of a circuit** — "the full description of the circuit C_n" that a uniform
machine outputs, Definition 3 of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), Section 3.2, p.9.

The list of gate codes followed by the list of output wires, each list in the self-delimiting list
encoding `encodeList` of the published `SubexponentialSAT` definition.

**Formalization Note.** The encoding is self-delimiting, so a description determines its circuit. -/
def encCircuit (C : Circuit) : List Bool :=
  Encoding.encodeList encGate C.gates ++ Encoding.encodeList encBin C.outputs

end DoublyEffIP.Supplement


