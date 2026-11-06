-- Prove2me | Definitions.Def_ConstrSOSP_encGate
-- name    : ConstrSOSP_encGate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:58:30.168914+00:00
-- url     : https://prove2.me/theorems/16fffd60-6b7b-48ed-9993-f75ff1675c4d
-- title:
--   Binary code of a gate
-- statement:
--   A gate is written as a two-bit tag ($00$ for $\wedge$, $01$ for $\vee$, $10$ for $\neg$) followed by the indices of the wires it reads, each in self-delimiting binary.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §4.1, p.17

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_ConstrSOSP_Gate

namespace ConstrSOSP

open QAlgorithms.LocalHamiltonian

/-- **Binary code of a gate**: a two-bit tag (`00` for ∧, `01` for ∨, `10` for ¬) followed by the
wire indices in self-delimiting binary (`encBin`). Used to write circuits (arXiv:2604.02285,
2 Nov 2026, §4.1, p.17) as input strings. -/
def encGate : Gate → List Bool
  | Gate.andG i j => [false, false] ++ encBin i ++ encBin j
  | Gate.orG i j => [false, true] ++ encBin i ++ encBin j
  | Gate.notG i => [true, false] ++ encBin i

end ConstrSOSP


