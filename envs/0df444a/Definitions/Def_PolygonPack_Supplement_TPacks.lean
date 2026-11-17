-- Prove2me | Definitions.Def_PolygonPack_Supplement_TPacks
-- name    : PolygonPack_Supplement_TPacks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:12:49.699488+00:00
-- url     : https://prove2.me/theorems/5bbb379d-7d9e-4c77-a34c-243eb3ced7fe
-- title:
--   Packing by translations into a container; the box $[0,w]\times[0,1]$
-- statement:
--   Fix the orientation of every polygon. For a polygon $P$ (the convex hull of a finite list of rational points) and a vector $t\in\mathbb R^2$, the **translate** $P+t$ is $\{z+t: z\in P\}$. For $w\in\mathbb R$, the **box** of width $w$ is
--   $$\mathrm{box}(w)=[0,w]\times[0,1],$$
--   so $\mathrm{box}(1)$ is the unit square and $\mathrm{box}(1+\varepsilon)$ is the $(1+\varepsilon)\times1$ rectangle of one-dimensional resource augmentation.
--
--   Given polygons $P_0,\dots,P_{n-1}$, a container $C\subseteq\mathbb R^2$, a set $S$ of indices and vectors $t_i$, the translations **pack** $S$ in $C$ when $P_i+t_i\subseteq C$ for every $i\in S$ and the interiors of $P_i+t_i$ and $P_j+t_j$ are disjoint for distinct $i,j\in S$. The set $S$ is **translation-feasible** when some real vectors pack it in the unit square.
--
--   These notions describe the translation-only problems of Appendix H and Theorem 1.3, where no rotation is allowed.
--
--   **Formalization Note** A polygon with empty interior (a point or a segment) constrains nothing through the disjointness clause, as the paper notes on p.74.
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), App. H, p.74 (PDF p.75) ("Fix the orientation of every input polygon"); §1, p.1 (feasible packing); H.5, p.78 (the $(1+\varepsilon)\times1$ rectangle)

import Mathlib
import Definitions.Def_PolygonPack_Instance
import Definitions.Def_PolygonPack_Pose

namespace PolygonPack.Supplement

open PolygonPack

/-- **Packing by translations only.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), App. H, p.74 (PDF p.75): "Fix the orientation of every input polygon." §1, p.1: a feasible packing places every polygon "entirely within the square, with pairwise disjoint interiors"; H.5, p.78: "each output bin becomes a (1 + ε) × 1 rectangle".

`translate v t` is the polygon spanned by the vertex list `v` (the base `hull v`), moved by the vector `t`.
`box w` is the rectangle `[0, w] × [0, 1]`, so `box 1` is the unit square and `box (1 + ε)` the container of
Theorem 1.3. `TPacks I C S t`: the translations `t` move every polygon of `S` into the container `C`, with
pairwise disjoint interiors. `TFeasible I S`: some real translations pack `S` in the unit square.

**Formalization Note.** No rotation and no reflection occurs: the orientation of the input is kept. Translation
vectors are real here; the algorithms' outputs (`TOut`) use rational translations. Interiors are taken in
`ℝ × ℝ`; a polygon with empty interior (a point or a segment) constrains nothing, as on p.74. -/
def translate (v : List (ℚ × ℚ)) (t : ℝ × ℝ) : Set (ℝ × ℝ) := (fun z => z + t) '' hull v

/-- The rectangle `[0, w] × [0, 1]`. -/
def box (w : ℝ) : Set (ℝ × ℝ) := Set.Icc 0 w ×ˢ Set.Icc 0 1

/-- The translations `t` pack the polygons of `S` in the container `C`. -/
def TPacks (I : Instance) (C : Set (ℝ × ℝ)) (S : Finset (Fin I.n)) (t : Fin I.n → ℝ × ℝ) : Prop :=
  (∀ i ∈ S, translate (I.verts i) (t i) ⊆ C) ∧
    ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Disjoint (interior (translate (I.verts i) (t i))) (interior (translate (I.verts j) (t j)))

/-- The polygons of `S` can be packed by translations in one unit square. -/
def TFeasible (I : Instance) (S : Finset (Fin I.n)) : Prop := ∃ t, TPacks I unitSq S t

end PolygonPack.Supplement


