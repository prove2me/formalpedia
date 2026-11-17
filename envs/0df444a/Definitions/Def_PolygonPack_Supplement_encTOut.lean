-- Prove2me | Definitions.Def_PolygonPack_Supplement_encTOut
-- name    : PolygonPack_Supplement_encTOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:13:59.648896+00:00
-- url     : https://prove2.me/theorems/7d515da2-3dab-41f2-92ca-b4adea61389e
-- title:
--   Binary encoding of translation outputs and translation bin packings
-- statement:
--   A translation output, a list of entries $(k,x,y)$ with $k\in\mathbb N$ and $x,y\in\mathbb Q$, is written as a word over a four-letter alphabet: the number of entries in binary, then each entry as $k$ in binary followed by the reduced numerators and denominators of $x$ and $y$ in binary, with separator symbols between the parts. A translation bin packing is written as the list of the encodings of its bins, in the same list format.
--
--   These fixed encoders measure the output length of the polynomial-time algorithms of Theorems H.4 and 1.3; with binary numbers, a polynomial running time implies rational translations of polynomial bit length.
--
--   **Formalization Note** The encoders reuse the mission's list, point and number encoders, are fixed (never parameters) and are injective (checked in the mission's verification file).
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), H.5, p.78 (PDF p.79): "polynomial time in the binary input length and exact rational translations"; §2.7, p.13 (binary encoding length)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_PolygonPack_encInstance
import Definitions.Def_PolygonPack_Supplement_TOut
open OnlineCRS.Combine

namespace PolygonPack.Supplement

open PolygonPack

/-- One entry `(k, x, y)`: the index, `3`, the two rational coordinates separated by `3`. -/
def encTEntry (e : ℕ × ℚ × ℚ) : List Sym := encNat e.1 ++ [(3 : Sym)] ++ encPt e.2

/-- **Binary encoding of a translation output.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), H.5, p.78 (PDF p.79): "polynomial time in the binary input length and exact rational translations".

`encTOut out` is the list of its entries, each the binary index followed by the binary rational coordinates
(`encList`, `encNat`, `encPt` of the base mission). `encTBins` encodes a translation bin packing as the list of
its bins' `encTOut` words.

**Formalization Note.** Numbers are binary, so a machine with polynomial running time writes rational
translations of polynomial bit length. Encoders are fixed here and are never parameters; injectivity is
checked in `Solutions/verification/PolygonPack_Supplement_sanity.lean`. -/
def encTOut (out : TOut) : List Sym := encList encTEntry out

/-- Binary encoding of a translation bin packing: the bins' `encTOut` words, as a list. -/
def encTBins (bins : TBins) : List Sym := encList encTOut bins

end PolygonPack.Supplement


