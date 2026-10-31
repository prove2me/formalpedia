-- Prove2me | Definitions.Def_HardTilingSimple_DecisionCounting_RegionCodec
-- name    : HardTilingSimple_DecisionCounting_RegionCodec
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-31T00:31:28.279895+00:00
-- url     : https://prove2.me/theorems/fc9e8098-d2ef-45d9-ac56-c7421c0fbe4f
-- title:
--   Canonical binary encoding of unrestricted finite regions
-- statement:
--   A finite region is encoded by its number of cells followed by its distinct coordinate pairs in increasing lexicographic order, first coordinate primary. Each signed coordinate uses the zigzag binary codec. No coordinate magnitude bound is imposed, and negative coordinates and the empty region are represented.
--
--   The decoder parses the stated number of pairs and accepts only if there is no suffix and the entire input equals the canonical encoding of the resulting set. Thus it rejects repeated cells, unsorted cells, noncanonical numerals, incomplete data and trailing bits. The preliminary number-of-cells bound by the input bit length excludes no valid encoding, since every cell requires at least two bits. Complexity is measured in total input bit length, not numeric coordinate diameter.
-- source:
--   Moore and Robson, Hard Tiling Problems with Simple Tiles, Discrete & Computational Geometry 26, 573–590 (2001), published DOI https://doi.org/10.1007/s00454-001-0047-6, §2, p. 574 (PDF 2), finite subsets of the square lattice; explicit-cell binary encoding is a formalization convention.

import Definitions.Def_HardTilingSimple_DecisionCounting_Geometry
import Definitions.Def_HardTilingSimple_DecisionCounting_BinaryCodec

namespace HardTilingSimple.DecisionCounting

/-- Lexicographic coordinate order, with the first coordinate primary. -/
def sortedCells (R : Region) : List Cell :=
  ((R.image toLex).sort (· ≤ ·)).map ofLex

def encodeCell (p : Cell) : List Bool :=
  BinaryCodec.encodeInt p.1 ++ BinaryCodec.encodeInt p.2

def encodeRegion (R : Region) : List Bool :=
  ExponomialAssortment.FPTAS.encodeNat R.card ++ (sortedCells R).flatMap encodeCell

def decodeCells : ℕ → List Bool → Option (List Cell × List Bool)
  | 0, bs => some ([], bs)
  | n + 1, bs => do
    let (x, bs') ← BinaryCodec.decodeInt bs
    let (y, bs'') ← BinaryCodec.decodeInt bs'
    let (ps, rest) ← decodeCells n bs''
    pure ((x, y) :: ps, rest)

/-- Require the entire input to equal the canonical encoding of the parsed region.
This rejects duplicates, disorder, noncanonical numerals, truncation and trailing data. -/
def decodeRegion (bs : List Bool) : Option Region := do
  let (n, rest) ← BinaryCodec.decodeNat bs
  if n ≤ bs.length then
    let (ps, tail) ← decodeCells n rest
    let R := ps.toFinset
    if tail = [] ∧ encodeRegion R = bs then some R else none
  else none

end HardTilingSimple.DecisionCounting


