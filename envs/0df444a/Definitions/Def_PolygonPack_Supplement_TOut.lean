-- Prove2me | Definitions.Def_PolygonPack_Supplement_TOut
-- name    : PolygonPack_Supplement_TOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:13:18.438517+00:00
-- url     : https://prove2.me/theorems/3c271f33-b45a-4d30-acbf-35fbc7f844c5
-- title:
--   Outputs of translation algorithms: rational translations for knapsack and for bin packing
-- statement:
--   A **translation output** is a list of entries $(k,x,y)$ with $k\in\mathbb N$ and $x,y\in\mathbb Q$: polygon $P_k$ is moved by the rational vector $(x,y)$. Its **selected set** is the set of indices it lists. For polygons $P_0,\dots,P_{n-1}$ and a container $C$, the output is **sound in $C$** when its indices are distinct and smaller than $n$ and its translations pack the selected polygons in $C$ (each translate lies in $C$, interiors pairwise disjoint).
--
--   A **translation bin packing** is a list of translation outputs, one per bin. It is **sound in $C$** when every bin is sound in $C$ and every polygon is packed exactly once (the concatenated index list is a permutation of $0,\dots,n-1$). Its cost is the number of bins.
--
--   These are the outputs of the knapsack and bin-packing algorithms of Theorems H.4 and 1.3, which return exact rational translations.
--
--   **Formalization Note** Distinct indices keep a profit from being counted twice, and the exactly-once clause keeps a bin packing from omitting polygons. An empty bin counts as a bin.
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), H.5, p.78 (PDF p.79) ("exact rational translations"); Theorem H.4, p.77; Theorem 1.3, p.4

import Mathlib
import Definitions.Def_PolygonPack_Instance
import Definitions.Def_PolygonPack_Pose
import Definitions.Def_PolygonPack_Supplement_TPacks

namespace PolygonPack.Supplement

open PolygonPack

/-- **Output of a translation algorithm.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), H.5, p.78 (PDF p.79): "polynomial time in the binary input length and exact rational translations"; Theorem H.4, p.77, and Theorem 1.3, p.4.

A translation output is a list of entries `(k, x, y)`: polygon `k` is moved by the rational vector `(x, y)`.
`out.indexSet I` is the selected set. `out.Sound I C`: the indices are distinct and in range, and the listed
translations pack the selected polygons in the container `C`. A translation bin packing `TBins` is a list of
such outputs, one per bin; `bins.Sound I C` says that every bin is sound in `C` and that every polygon is
packed exactly once (the concatenated index list is a permutation of `0, …, n−1`).

**Formalization Note.** `Nodup` keeps a selected profit from being counted twice; "exactly once" keeps a bin
packing from omitting a polygon. An empty bin is allowed and counts as a bin. -/
abbrev TOut : Type := List (ℕ × ℚ × ℚ)

/-- The polygon indices of a translation output. -/
def TOut.indices (out : TOut) : List ℕ := out.map Prod.fst

/-- The set of polygons a translation output selects. -/
def TOut.indexSet (out : TOut) (I : Instance) : Finset (Fin I.n) :=
  Finset.univ.filter (fun i => i.val ∈ out.indices)

/-- The listed rational translations pack the selected polygons in `C`. -/
def TOut.Sound (out : TOut) (I : Instance) (C : Set (ℝ × ℝ)) : Prop :=
  out.indices.Nodup ∧ (∀ k ∈ out.indices, k < I.n) ∧
    ∃ t : Fin I.n → ℝ × ℝ, TPacks I C (out.indexSet I) t ∧
      ∀ e ∈ out, ∀ hk : e.1 < I.n, t ⟨e.1, hk⟩ = castPt e.2

/-- A bin packing by translations: one translation output per bin. -/
abbrev TBins : Type := List TOut

/-- The concatenated polygon indices of all bins. -/
def TBins.indices (bins : TBins) : List ℕ := bins.flatMap TOut.indices

/-- Every bin packs its polygons in `C`, and every polygon is packed exactly once. -/
def TBins.Sound (bins : TBins) (I : Instance) (C : Set (ℝ × ℝ)) : Prop :=
  (∀ b ∈ bins, b.Sound I C) ∧ bins.indices.Perm (List.range I.n)

end PolygonPack.Supplement


