-- Prove2me | Definitions.Def_PolygonPack_encInstance
-- name    : PolygonPack_encInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:53:14.394241+00:00
-- url     : https://prove2.me/theorems/6d5dc24f-b036-4201-90dc-9ec81ab197b6
-- title:
--   Binary encoding of an instance
-- statement:
--   An instance is written as a word over a four-letter alphabet. A list is written as its length in binary, the separator, and each element followed by the separator. A rational is written by its reduced numerator and denominator in binary, and a polygon by its vertex list and its profit.
--
--   The length of this word is the total binary encoding length of the input vertices and profits, the measure in which the paper states its running times.
--
--   **Formalization Note** The encoders are fixed definitions on top of the published `OnlineCRS.Combine` encoders of natural numbers, integers and rationals. Injectivity of `encInstance` is proved in the verification file of this mission.
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), §2.7, p.13

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_PolygonPack_Instance
open OnlineCRS.Combine

namespace PolygonPack

/-- A list: its length in binary, the separator `3`, then each word followed by `3`. -/
def encList {α : Type} (e : α → List Sym) (l : List α) : List Sym :=
  encNat l.length ++ [(3 : Sym)] ++ l.flatMap (fun a => e a ++ [(3 : Sym)])

/-- A rational point: its two coordinates, separated by `3`. -/
def encPt (z : ℚ × ℚ) : List Sym := encRat z.1 ++ [(3 : Sym)] ++ encRat z.2

/-- **Binary encoding of an instance.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), §2.7, p.13: "All running times are measured in the total
binary encoding length of the input vertices and profits".

Each polygon is written as its vertex list, the separator `3`, its profit.

**Formalization Note.** Numbers are binary, via the published `OnlineCRS.Combine.encNat`, `encRat`, so the
length of the encoding is the paper's binary input length. Encoders are fixed here and are never
parameters. `encNat 0` may be empty, so every length word is followed by `3`. Injectivity is proved in
`Solutions/verification/PolygonPack_sanity.lean`. -/
def encInstance (I : Instance) : List Sym :=
  encList (fun P => encList encPt P.1 ++ [(3 : Sym)] ++ encRat P.2) I

end PolygonPack


