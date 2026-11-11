-- Prove2me | Definitions.Def_UnequalHuffman_NPC_GraphCode
-- name    : UnequalHuffman_NPC_GraphCode
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:43:44.744207+00:00
-- url     : https://prove2.me/theorems/a9902f37-b381-445b-9a16-17d018e2922f
-- title:
--   Binary code of a simple graph on Fin n
-- statement:
--   A simple graph $G$ on the vertices $\{0,\dots,n-1\}$ (`SimpleGraph (Fin n)`) is coded by `graphCode G`: the number $n$, then the adjacency matrix row by row ($1$ for an edge, $0$ otherwise), every entry in binary over the alphabet `BSym`. This is the input code of the source problem Planar Independent Set (a simple planar graph; planarity is the published `WilliamsonShmoys.HasPlanarDrawingOn`).
-- source:
--   Chandran and Gajjala, Binary Huffman Coding with Unequal Letter Costs Is NP-Complete, arXiv:2611.04444v1, p. 7 (Planar Independent Set, the source problem)

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding

set_option autoImplicit false

namespace UnequalHuffman.NPC

open ProjSchedTW.Complexity

open Classical in
/-- The binary code of a simple graph `G` on the vertices `Fin n`: `n`, then the adjacency
matrix row by row (`1` for an edge, `0` otherwise), every entry in binary. -/
noncomputable def graphCode {n : ℕ} (G : SimpleGraph (Fin n)) : List BSym :=
  encNats ([n] ++ (List.ofFn fun i : Fin n => List.ofFn fun j : Fin n =>
    if G.Adj i j then 1 else 0).flatten)

end UnequalHuffman.NPC


