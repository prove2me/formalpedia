-- Prove2me | Definitions.Def_CumulativeCrossingBlocks
-- name    : CumulativeCrossingBlocks
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-26T22:31:11.807395+00:00
-- url     : https://prove2.me/theorems/2e6063f6-a994-4712-9078-2997b1ec0eaf
-- title:
--   A code for bounded block lists with a cumulative cell budget
-- statement:
--   A trace consists of headers and variable-length cell blocks. Store the headers in one padded stream. Store the cell blocks in a second stream with a delimiter at the end of each block and a separate padding marker.
-- source:
--   Finite encodings for sparse crossing-sequence arguments.

import Mathlib

namespace CumulativeBlockCode

variable {Header Cell : Type}

/-- Occupied-cell data counts the total length of the crossing blocks. -/
def totalCells (trace : List (Header × List Cell)) : ℕ :=
  (trace.map (fun crossing => crossing.2.length)).sum

def markBlocks : List (List Cell) → List (Option Cell)
  | [] => []
  | cells :: rest => cells.map some ++ none :: markBlocks rest

def pad {A : Type} (bound : ℕ) (xs : List A) : Fin bound → Option A :=
  fun i => xs[i.val]?

/-- Bound the number of blocks by r and all their cells together by s. -/
abbrev Code (Header Cell : Type) (r s : ℕ) :=
  (Fin r → Option Header) × (Fin (r+s) → Option (Option Cell))

/-- Separate headers from the concatenated cells, delimit each block, and pad both streams. -/
def encode (r s : ℕ) (trace : List (Header × List Cell)) : Code Header Cell r s :=
  (pad r (trace.map Prod.fst),pad (r+s) (markBlocks (trace.map Prod.snd)))


end CumulativeBlockCode


