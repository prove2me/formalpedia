-- Prove2me | Definitions.Def_PunctSketch_EncInput
-- name    : PunctSketch_EncInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:21.102206+00:00
-- url     : https://prove2.me/theorems/b24adba8-de18-465b-bf5f-0566dbf83877
-- title:
--   Input of a node player
-- statement:
--   A node player knows the order $n$, the parameter $k$, its own identifier $v$, its neighbourhood $N(v)$ as a bit mask, and the public coins. The encoding writes $n$ in unary and the rest in binary, with field separators. Since the graph is not a field, a message depends on $G$ only through $N(v)$.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §2, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_PunctSketch_encBits
open OnlineCRS.Combine

namespace PunctSketch

/-- **Input of a node player.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §2, p.5: "Each vertex x ∈ V = [n] has a correspoding node
player, also denoted x, who knows the input size n, their own ID, and the IDs of all vertices in
their neighborhood". The player also reads the public coins and the parameter `k`.

`code` writes `n` in unary and the rest in binary, with the separator `3` between fields. -/
structure EncInput where
  n : ℕ
  k : ℕ
  v : ℕ
  mask : List Bool
  coins : List ℕ

/-- The tape encoding of a node player's input. -/
def EncInput.code (x : EncInput) : List Sym :=
  encUnary x.n ++ [3] ++ encNat x.k ++ [3] ++ encNat x.v ++ [3] ++ encBits x.mask ++ [3] ++
    encNatList x.coins

end PunctSketch


