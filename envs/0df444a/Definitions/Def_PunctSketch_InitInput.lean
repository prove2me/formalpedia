-- Prove2me | Definitions.Def_PunctSketch_InitInput
-- name    : PunctSketch_InitInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:36.419027+00:00
-- url     : https://prove2.me/theorems/f1973d17-b465-419f-aa65-541c9ccbf757
-- title:
--   Input of the streaming initializer
-- statement:
--   The initializer of the streaming algorithm reads $n$, $k$ and the coins, and writes the initial memory. It is the only machine that reads coins, so all randomness needed later has to be stored in the memory: "any randomness used now needs to be stored as well" (p.19). The encoding writes $n$ in unary.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §5.3, p.19 (PDF p.20)

import Mathlib
import Definitions.Def_PunctSketch_encBits
open OnlineCRS.Combine

namespace PunctSketch

/-- **Input of the streaming initializer.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.3, p.19: "any randomness used now needs to
be stored as well". Only the initializer reads coins; the update and output machines read the state.
`code` writes `n` in unary. -/
structure InitInput where
  n : ℕ
  k : ℕ
  coins : List ℕ

/-- The tape encoding of the initializer's input. -/
def InitInput.code (x : InitInput) : List Sym :=
  encUnary x.n ++ [3] ++ encNat x.k ++ [3] ++ encNatList x.coins

end PunctSketch


