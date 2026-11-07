-- Prove2me | Definitions.Def_PunctSketch_OutInput
-- name    : PunctSketch_OutInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:51.764189+00:00
-- url     : https://prove2.me/theorems/e0fce970-f86e-4b6b-a313-281e01992993
-- title:
--   Input of the streaming output machine
-- statement:
--   At the end of the stream the output machine reads $n$, $k$ and the memory, and returns the answer. The encoding writes $n$ in unary.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §5.3, pp.18–19 (PDF pp.19–20)

import Mathlib
import Definitions.Def_PunctSketch_encBits
open OnlineCRS.Combine

namespace PunctSketch

/-- **Input of the streaming output machine.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.3, pp.18–19: at the end of the stream the
algorithm post-processes the stored sketches. The machine sees `n`, `k` and the memory only.
`code` writes `n` in unary. -/
structure OutInput where
  n : ℕ
  k : ℕ
  state : List Bool

/-- The tape encoding of the output machine's input. -/
def OutInput.code (x : OutInput) : List Sym :=
  encUnary x.n ++ [3] ++ encNat x.k ++ [3] ++ encBits x.state

end PunctSketch


