-- Prove2me | Definitions.Def_PolygonPack_encOut
-- name    : PolygonPack_encOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:56:09.754379+00:00
-- url     : https://prove2.me/theorems/69c8563c-5113-4f65-a8ff-1e9b035ced58
-- title:
--   Binary encoding of an output and of the other machine inputs
-- statement:
--   An output is written as a list of entries: the index in binary and the four algebraic numbers, each given by its coefficient list and its two rational bounds. `encPolys` writes a list of polygons without profits, and `encOptOut` writes a yes-or-no answer together with a packing in the yes case.
--
--   A machine that runs in polynomial time writes such a word in polynomial time, so its description has polynomial length.
--
--   **Formalization Note** Injectivity of `encOut` is proved in the verification file of this mission.
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), §2.7, p.13; Lemma E.1, p.46

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_PolygonPack_AlgNum
import Definitions.Def_PolygonPack_Out
import Definitions.Def_PolygonPack_encInstance
open OnlineCRS.Combine

namespace PolygonPack

/-- An algebraic number: coefficients, `3`, lower bound, `3`, upper bound. -/
def encAlg (α : AlgNum) : List Sym :=
  encList encInt α.coeffs ++ [(3 : Sym)] ++ encRat α.lo ++ [(3 : Sym)] ++ encRat α.hi

/-- **Binary encoding of an output.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), §2.7, p.13: "Placements are returned as exact real algebraic
numbers of polynomial description length."

Each entry is written as its index and its four algebraic numbers, separated by `3`.

**Formalization Note.** A machine with polynomial running time writes `encOut (f I)` in full, which is
why a bound on the description length follows from the time bound. Injectivity is proved in
`Solutions/verification/PolygonPack_sanity.lean`. -/
def encOut (out : Out) : List Sym :=
  encList (fun e => encNat e.1 ++ [(3 : Sym)] ++ encAlg e.2.1 ++ [(3 : Sym)] ++ encAlg e.2.2.1 ++
    [(3 : Sym)] ++ encAlg e.2.2.2.1 ++ [(3 : Sym)] ++ encAlg e.2.2.2.2) out

/-- A list of polygons, without profits (the input of Lemma E.1). -/
def encPolys (l : List (List (ℚ × ℚ))) : List Sym := encList (encList encPt) l

/-- The answer of a decision-and-placement procedure: `0` for no, `1` followed by a packing for yes. -/
def encOptOut : Option Out → List Sym
  | none => [(0 : Sym)]
  | some out => (1 : Sym) :: encOut out

end PolygonPack


