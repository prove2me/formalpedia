-- Prove2me | Definitions.Def_ConstrSOSP_encCircuit
-- name    : ConstrSOSP_encCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:45.252895+00:00
-- url     : https://prove2.me/theorems/31f2de2f-25f7-4150-80fe-175e3781bad8
-- title:
--   Binary code of a Boolean circuit
-- statement:
--   A circuit is written as a bit string: $n$, the number of gates, the gate codes, the number of outputs and the output wires, every number in self-delimiting binary. The length of the code is linear in the size of the circuit; it is the input format of LocalOpt and Iter.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Definitions 4.1–4.2, pp.17–18

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_ConstrSOSP_Circuit
import Definitions.Def_ConstrSOSP_encGate

namespace ConstrSOSP

open QAlgorithms.LocalHamiltonian

/-- **Binary code of a circuit**: `n`, the number of gates, the gate codes (`encGate`), the number
of outputs, and the output wires, all numbers in self-delimiting binary (`encBin`). This is how
the circuits of LocalOpt and Iter (arXiv:2604.02285, 2 Nov 2026, Definitions 4.1 and 4.2,
pp.17–18) are written as input strings; its length is linear in the size of the circuit. -/
def encCircuit (C : Circuit) : List Bool :=
  encBin C.n ++ encBin C.gates.length ++ C.gates.flatMap encGate ++
    encBin C.outs.length ++ C.outs.flatMap encBin

end ConstrSOSP


