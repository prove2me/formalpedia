-- Prove2me | Definitions.Def_PolygonPack_Packs
-- name    : PolygonPack_Packs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:54:17.892086+00:00
-- url     : https://prove2.me/theorems/4f790869-6f9a-4dbb-b9c0-9934d2718a95
-- title:
--   Feasible packing in the unit square and its profit
-- statement:
--   Let $S$ be a set of polygons of an instance. A family of poses $(T_i)$ **packs** $S$ if each $T_i$ with $i\in S$ is a placement of polygon $i$ in the unit square and the images of distinct polygons of $S$ have disjoint interiors. They may touch along the boundary. The set $S$ is **feasible** if some family of poses packs it, and its **profit** is
--   $$
--   \pi(S)=\sum_{i\in S}\pi_i .
--   $$
--   This is the feasibility notion of the knapsack problem and of every comparison packing in the paper.
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), §1, p.1 (a feasible packing)

import Mathlib
import Definitions.Def_PolygonPack_Instance
import Definitions.Def_PolygonPack_Pose

namespace PolygonPack

/-- **Feasible packing.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), §1, p.1: "A feasible packing places every polygon entirely within the
square, with pairwise disjoint interiors though they can touch along the boundary."

`Packs I S T`: the poses `T` place every polygon of `S` rigidly in the unit square, with pairwise
disjoint interiors. `Feasible I S`: some poses do so. `profit I S` is the total profit, `π(S)`.

**Formalization Note.** Interiors are taken in `ℝ × ℝ`, whose product topology is the usual one.
Disjointness of interiors says nothing for a polygon with empty interior; `Instance.Valid` excludes
those. -/
def Packs (I : Instance) (S : Finset (Fin I.n)) (T : Fin I.n → Pose) : Prop :=
  (∀ i ∈ S, IsPlacement (I.verts i) (T i)) ∧
    ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Disjoint (interior (placed (I.verts i) (T i))) (interior (placed (I.verts j) (T j)))

/-- The polygons of `S` can be packed in one unit square. -/
def Feasible (I : Instance) (S : Finset (Fin I.n)) : Prop := ∃ T, Packs I S T

/-- The total profit `π(S)`. -/
noncomputable def profit (I : Instance) (S : Finset (Fin I.n)) : ℝ := ∑ i ∈ S, ((I.prof i : ℚ) : ℝ)

end PolygonPack


