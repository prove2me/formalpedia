-- Prove2me | Definitions.Def_UnequalHuffman_NPC_Gadgets
-- name    : UnequalHuffman_NPC_Gadgets
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:44:26.622203+00:00
-- url     : https://prove2.me/theorems/e8d2f372-7d8f-4821-9650-4bc4d3ddee1c
-- title:
--   The explicit Copy, edge-check, exchange, wait and move constructions of Lemmas A.2–A.5
-- statement:
--   Leaf data of the constructions in the proofs of Lemmas A.2–A.4 and in the statement of Lemma A.5 (intervals and coefficients per level, leaves in sorted order):
--
--   - `copyData` (Lemma A.2, six levels, started from $\{b\}$): no leaves at levels 1–4; at level 5 thirty leaves with coefficient $0$ and intervals $[1,2]$ (×5), $[2,3]$ (×10), $[3,4]$ (×10), $[4,5]$ (×5); at level 6 two leaves with intervals $[0,1]$, $[6,7]$ and coefficients $1, -1$.
--   - `checkData` (Lemma A.3, three levels, started from $\{-3+a, b\}$): all coefficients $0$; intervals level 1: $[-3,-2], [1,2]$; level 2: $[-2,-1], [1,2]$; level 3: $[-1,0], \{0\}, [0,1], [1,2]$.
--   - `exchangeData` (Lemma A.4, Table 6, started from $\{-1, b\}$): two leaves per level, (interval, coefficient): level 1 $\{-1\}, 0$ and $[1,2], 2$; level 2 $\{0\}, 0$ and $[1,2], 0$; level 3 $\{1\}, 0$ and $[1,2], 0$; level 4 $[1,2], -1$ and $\{2\}, 0$; level 5 $[1,2], -1$ and $\{3\}, 0$.
--   - `waitData d r` (Lemma A.5.1): $d$ levels, one leaf per level with interval $[r+1, r+2]$, coefficients $d-1, -1, \dots, -1$ in level order.
--   - `moveData r` (Lemma A.5.2): three levels, one leaf per level, intervals $[r+1,r+2], [r+1,r+2], [r,r+1]$, coefficients $-1, 0, 1$.
-- source:
--   Chandran and Gajjala, Binary Huffman Coding with Unequal Letter Costs Is NP-Complete, arXiv:2611.04444v1, pp. 41–43, Appendix A.3–A.6 (Lemmas A.2–A.5, their proofs, Table 6)

import Mathlib
import Definitions.Def_UnequalHuffman_NPC_LocalConstruction

set_option autoImplicit false

namespace UnequalHuffman.NPC

/-- The six-level Copy construction of the proof of Lemma A.2 (p. 41), started from `{b}`:
no leaves at levels 1–4; at level 5 thirty leaves with coefficient `0` and intervals
`[1,2]` (×5), `[2,3]` (×10), `[3,4]` (×10), `[4,5]` (×5); at level 6 two leaves with intervals
`[0,1]`, `[6,7]` and coefficients `1`, `-1`. -/
def copyData : LeafData :=
  [[], [], [], [],
   List.replicate 5 (1, 2, 0) ++ List.replicate 10 (2, 3, 0) ++ List.replicate 10 (3, 4, 0) ++
     List.replicate 5 (4, 5, 0),
   [(0, 1, 1), (6, 7, -1)]]

/-- The three-level edge-check construction of the proof of Lemma A.3 (p. 41), started from
`{-3 + a, b}`; every coefficient is `0` and the sorted leaf intervals are
level 1: `[-3,-2], [1,2]`; level 2: `[-2,-1], [1,2]`; level 3: `[-1,0], {0}, [0,1], [1,2]`. -/
def checkData : LeafData :=
  [[(-3, -2, 0), (1, 2, 0)],
   [(-2, -1, 0), (1, 2, 0)],
   [(-1, 0, 0), (0, 0, 0), (0, 1, 0), (1, 2, 0)]]

/-- The five-level exchange construction of Table 6 (proof of Lemma A.4, p. 42), started from
`{-1, b}`: two leaves per level with (interval, coefficient)
level 1: `{-1}, 0` and `[1,2], 2`; level 2: `{0}, 0` and `[1,2], 0`; level 3: `{1}, 0` and
`[1,2], 0`; level 4: `[1,2], -1` and `{2}, 0`; level 5: `[1,2], -1` and `{3}, 0`. -/
def exchangeData : LeafData :=
  [[(-1, -1, 0), (1, 2, 2)],
   [(0, 0, 0), (1, 2, 0)],
   [(1, 1, 0), (1, 2, 0)],
   [(1, 2, -1), (2, 2, 0)],
   [(1, 2, -1), (3, 3, 0)]]

/-- The `d`-level wait operation of Lemma A.5.1 at base `r`: one leaf per level, interval
`[r+1, r+2]`, coefficients `d - 1, -1, …, -1` in level order. -/
def waitData (d : ℕ) (r : ℤ) : LeafData :=
  (List.range d).map fun i => [(r + 1, r + 2, if i = 0 then (d : ℤ) - 1 else -1)]

/-- The three-level move operation of Lemma A.5.2 at base `r`: leaf intervals
`[r+1, r+2], [r+1, r+2], [r, r+1]` with coefficients `-1, 0, 1`. -/
def moveData (r : ℤ) : LeafData :=
  [[(r + 1, r + 2, -1)], [(r + 1, r + 2, 0)], [(r, r + 1, 1)]]

end UnequalHuffman.NPC


