-- Prove2me | Definitions.Def_PolygonPack_Supplement_Bins
-- name    : PolygonPack_Supplement_Bins
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:12:25.239382+00:00
-- url     : https://prove2.me/theorems/12a85f2b-c765-4ca6-b312-b031d369c0a7
-- title:
--   Bin-packing output under rotations: bins of exact algebraic poses, every polygon exactly once
-- statement:
--   A **bin-packing output** under rotations is a finite list of bins $B_1,\dots,B_N$. Each bin is an output of the knapsack setting: a list of entries $(k,a,b,x,y)$ saying that polygon $P_k$ is placed by the rigid motion $(u,v)\mapsto(au-bv+x,\;bu+av+y)$, where $a,b,x,y$ are exact real algebraic numbers (each given by an integer polynomial and a rational interval isolating one of its roots).
--
--   For a list of polygons $P_0,\dots,P_{n-1}$ the output is **sound** when
--
--   1. every bin is a sound packing in the unit square $[0,1]^2$: its indices are distinct and in range, and its poses place its polygons rigidly in the square with pairwise disjoint interiors;
--   2. every polygon is packed exactly once: the concatenation of the bins' index lists is a permutation of $0,1,\dots,n-1$.
--
--   The **cost** of the output is its number of bins $N$. The output is written in binary as the list of its bins' encodings.
--
--   This is the output format of the bin-packing algorithm of Theorem 1.2: an approximation guarantee bounds $N$, and soundness makes the bound meaningful, since an output that omits polygons would trivially use few bins.
--
--   **Formalization Note** An empty bin is allowed and counts as a bin. The encoding is injective (checked in the mission's verification file).
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), Theorem 1.2, p.73 (PDF p.74); proof, p.74 ("retain exact descriptions of their computed placements")

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_PolygonPack_Instance
import Definitions.Def_PolygonPack_Pose
import Definitions.Def_PolygonPack_Packs
import Definitions.Def_PolygonPack_AlgNum
import Definitions.Def_PolygonPack_Out
import Definitions.Def_PolygonPack_encInstance
import Definitions.Def_PolygonPack_encOut
open OnlineCRS.Combine

namespace PolygonPack.Supplement

open PolygonPack

/-- **Bin-packing output under rotations.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), Theorem 1.2, p.73 (PDF p.74): "packing convex polygons, each individually fitting into a unit square, into the minimum number of unit squares"; proof, p.74: "Both algorithms retain exact descriptions of their computed placements."

A bin-packing output is a list of bins, each bin an output `Out` of the base mission (entries `(k, a, b, x, y)`
with exact algebraic pose numbers). `bins.indices` is the concatenation of the bins' index lists.
`bins.Sound I`: every bin is a sound packing of the polygons it lists (`Out.Sound`), and every polygon of `I`
appears in exactly one bin, exactly once (the concatenated index list is a permutation of `0, …, n−1`).
The cost of an output is its number of bins, `bins.length`. `encBins` is its binary encoding, a list of
`encOut` words.

**Formalization Note.** "Exactly once" excludes both omitting a polygon (which would make every bound trivial,
the empty output having zero bins) and packing it twice. An empty bin is allowed and counts as a bin. -/
abbrev Bins : Type := List Out

/-- The concatenated polygon indices of all bins. -/
def Bins.indices (bins : Bins) : List ℕ := bins.flatMap Out.indices

/-- Every bin is a sound packing in the unit square, and every polygon is packed exactly once. -/
def Bins.Sound (bins : Bins) (I : Instance) : Prop :=
  (∀ b ∈ bins, b.Sound I) ∧ bins.indices.Perm (List.range I.n)

/-- Binary encoding of a bin-packing output: the bins' `encOut` words, as a list. -/
def encBins (bins : Bins) : List Sym := encList encOut bins

end PolygonPack.Supplement


