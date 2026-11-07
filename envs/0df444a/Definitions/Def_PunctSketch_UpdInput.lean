-- Prove2me | Definitions.Def_PunctSketch_UpdInput
-- name    : PunctSketch_UpdInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:39.929952+00:00
-- url     : https://prove2.me/theorems/d7332d55-faf4-4a1d-9916-7e91472ae785
-- title:
--   Input of the streaming update
-- statement:
--   The update machine reads $n$, $k$, the current memory, the two endpoints of an edge and one bit that says whether the edge is inserted or deleted. It reads no coins. The encoding writes $n$ in unary.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §5.3, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_PunctSketch_encBits
open OnlineCRS.Combine

namespace PunctSketch

/-- **Input of the streaming update.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.3, p.18: "the algorithm maintains each node's
sketch dynamically and in parallel". The machine sees `n`, `k`, the current memory, the two
endpoints and whether the update inserts (`true`) or deletes (`false`); it reads no coins.
`code` writes `n` in unary. -/
structure UpdInput where
  n : ℕ
  k : ℕ
  state : List Bool
  u : ℕ
  v : ℕ
  insert : Bool

/-- The tape encoding of the update's input. -/
def UpdInput.code (x : UpdInput) : List Sym :=
  encUnary x.n ++ [3] ++ encNat x.k ++ [3] ++ encBits x.state ++ [3] ++ encNat x.u ++ [3] ++
    encNat x.v ++ [3] ++ encBits [x.insert]

end PunctSketch


