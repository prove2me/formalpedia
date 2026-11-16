-- Prove2me | Definitions.Def_MinDilationTree_Sublinear_Supplement_SpineCut
-- name    : MinDilationTree_Sublinear_Supplement_SpineCut
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T14:55:24.388404+00:00
-- url     : https://prove2.me/theorems/43c50169-0e65-44e2-bd58-2dfc462beb7b
-- title:
--   The spine-cutting graph $G_{F,\mathfrak S}$, relevant vertices and good cuts
-- statement:
--   Let $F$ be a face of a junction tree of $P\in\mathcal P_r$ and $\mathfrak S\subseteq\operatorname{spines}(F)$.
--
--   1. The **spine-cutting graph** $G_{F,\mathfrak S}$ (Definition 16) has one vertex for each connected component of $F\setminus\bigcup\mathfrak S$ and one outer-face vertex with region $\mathbb R^2\setminus(\operatorname{int}(F)\cup\bigcup\operatorname{junc}(F))$. Two vertices are adjacent when some path from a point of one region to a point of the other lies in $F$, intersects at most one $F$-spine of $\mathfrak S$, intersects no $F$-nerve contained in an $F$-spine of $\mathfrak S$, and stays outside the buffer $B_{z_1}(F)$, $z_1:=4r$.
--   2. The **relevant** vertices (Definition 17) are the outer-face vertex and the vertices whose region intersects at least two junctions.
--   3. A **good cut** of $G_{F,\mathfrak S}$ (Definition 21, $z_2:=r/2$) is a planar straight-line embedded graph $C$ such that:
--      1. $C$ is contained in the $F$-spines of $\mathfrak S$ that touch junctions of $F$;
--      2. $C$ intersects neither $B_{z_2}(F)$ nor any $F$-nerve;
--      3. the union of $C$ and all vertex regions has one connected component containing the regions of all relevant vertices and all of $C$;
--      4. for every $\Sigma\in\mathfrak S$ meeting a junction, every connected component of $\Sigma\setminus C$ meets a junction;
--      5. any two junctions of $\operatorname{junc}(F)$ joined by a path in $\bigcup\mathfrak S\cup\bigcup\operatorname{junc}(F)$ are still joined by a path in that set minus $C$.
--   4. $C$ is in **midpoint form** if every vertex of $C$ is the midpoint of a Delaunay edge, every edge of $C$ joins the midpoints of two sides of one Delaunay triangle, and no Delaunay triangle carries all three such segments; then every Delaunay triangle meets $C$ in at most two segments joining edge midpoints.
--
--   The comb obstruction (Theorem 18) is stated with $G_{F,\mathfrak S}$, and Lemma 23 and Definition 28 produce good cuts.
--
--   **Formalization Note** The graph is `SimpleGraph.fromRel` of the path relation, so loops are dropped. The outer-face vertex is `none` in an `Option` type and stays distinct from component vertices even if their regions overlap. A straight-line graph is a list of vertex positions and an edge list. Midpoint form records the shape of the cut built in the proof of Lemma 23 (reading R3).
-- source:
--   Sarita de Berg, Jacobus Conradi, Peter Kramer, André Nusser, Sampson Wong, STOC 2027 submission #185 (October 2026), pp. 11–12 (PDF pp. 12–13), Definitions 16 and 17; p. 16 (PDF p. 17), Definition 21; p. 42 (PDF p. 43), construction in the proof of Lemma 23 (midpoint form)

import Mathlib
import Definitions.Def_MinDilationTree_Sublinear_Supplement_JunctionTree

open scoped ENNReal

set_option autoImplicit false

namespace MinDilationTree.Sublinear.Supplement

open MinDilationTree.Sublinear

/-- The image of a path lies in `X`. -/
def JoinsIn (X : Set Plane) (a b : Plane) : Prop :=
  ∃ γ : Path a b, Set.range γ ⊆ X

/-- Definition 16: the outer face `ℝ² \ (int(F) ∪ junc(F))`. -/
noncomputable def outerRegion (Q : JunctionTreeData) (F : BoundaryWalk) : Set Plane :=
  (F.interior ∪ ⋃₀ junc Q F.region)ᶜ

/-- Vertices of the spine-cutting graph `G_{F,𝔖}`: `none` is the outer-face vertex, `some K` is a
connected component `K` of `F \ ⋃𝔖`. -/
abbrev CutVertex (F : BoundaryWalk) (𝔖 : Set (Set Plane)) :=
  Option {K : Set Plane // K ∈ components (F.region \ ⋃₀ 𝔖)}

/-- The region of a vertex of the spine-cutting graph. -/
noncomputable def vertexRegion (Q : JunctionTreeData) (F : BoundaryWalk) (𝔖 : Set (Set Plane))
    (v : CutVertex F 𝔖) : Set Plane :=
  match v with
  | none => outerRegion Q F
  | some K => K.val

/-- Definition 16, p.11–12 (PDF 12–13): two regions are joined when some path in `F` from a point
of one to a point of the other intersects at most one `F`-spine of `𝔖`, intersects no `F`-nerve
contained in an `F`-spine of `𝔖`, and remains outside the buffer `B_{z₁}(F)`, `z₁ := 4r`. -/
def cutAdj {n : ℕ} (p : Fin n → Plane) (D : SimpleGraph (Fin n)) (Λ r : ℝ) (P : Set Plane)
    (Q : JunctionTreeData) (F : BoundaryWalk) (𝔖 : Set (Set Plane)) (u v : CutVertex F 𝔖) :
    Prop :=
  ∃ a ∈ vertexRegion Q F 𝔖 u, ∃ b ∈ vertexRegion Q F 𝔖 v,
    ∃ γ : Path a b, Set.range γ ⊆ F.region \ buffer P Q F.region (4 * r) ∧
      (∀ W ∈ 𝔖, ∀ W' ∈ 𝔖,
        (Set.range γ ∩ W).Nonempty → (Set.range γ ∩ W').Nonempty → W = W') ∧
      ∀ N ∈ fNerves p D Λ r F.region, (∃ W ∈ 𝔖, N ⊆ W) → Disjoint (Set.range γ) N

/-- Definition 16: the spine-cutting graph `G_{F,𝔖}` (loops dropped). -/
def spineCuttingGraph {n : ℕ} (p : Fin n → Plane) (D : SimpleGraph (Fin n)) (Λ r : ℝ)
    (P : Set Plane) (Q : JunctionTreeData) (F : BoundaryWalk) (𝔖 : Set (Set Plane)) :
    SimpleGraph (CutVertex F 𝔖) :=
  SimpleGraph.fromRel (cutAdj p D Λ r P Q F 𝔖)

/-- Definition 17, p.12 (PDF 13): the relevant vertices are the outer-face vertex and the vertices
whose region intersects at least two junctions. -/
def Relevant (Q : JunctionTreeData) (F : BoundaryWalk) (𝔖 : Set (Set Plane))
    (v : CutVertex F 𝔖) : Prop :=
  v = none ∨ ∃ J ∈ junc Q F.region, ∃ J' ∈ junc Q F.region, J ≠ J' ∧
    (vertexRegion Q F 𝔖 v ∩ J).Nonempty ∧ (vertexRegion Q F 𝔖 v ∩ J').Nonempty

/-- A finite straight-line graph: labelled points and an edge list over the labels. -/
structure CutData where
  size : ℕ
  point : Fin size → Plane
  edges : List (Fin size × Fin size)

/-- The point set occupied by the drawing: its vertices and its edge segments. -/
def CutData.region (C : CutData) : Set Plane :=
  Set.range C.point ∪ {x | ∃ e ∈ C.edges, x ∈ segment ℝ (C.point e.1) (C.point e.2)}

/-- A planar straight-line embedded graph: distinct vertex positions, no loops, edges meeting only
in shared endpoints, and no vertex in the relative interior of an edge. -/
def CutData.IsPlane (C : CutData) : Prop :=
  Function.Injective C.point ∧ (∀ e ∈ C.edges, e.1 ≠ e.2) ∧
    (∀ e ∈ C.edges, ∀ e' ∈ C.edges, (e.1 ≠ e'.1 ∨ e.2 ≠ e'.2) → (e.1 ≠ e'.2 ∨ e.2 ≠ e'.1) →
      segment ℝ (C.point e.1) (C.point e.2) ∩ segment ℝ (C.point e'.1) (C.point e'.2) ⊆
        ({C.point e.1, C.point e.2} ∩ {C.point e'.1, C.point e'.2})) ∧
    ∀ e ∈ C.edges, ∀ k, C.point k ∈ segment ℝ (C.point e.1) (C.point e.2) → k = e.1 ∨ k = e.2

/-- Definition 21, p.16 (PDF 17): `C` is a good cut of `G_{F,𝔖}` (`z₂ := r/2`).
1. `C` lies in the `F`-spines of `𝔖` that touch junctions of `F`;
2. `C` meets neither the `z₂`-buffer nor any `F`-nerve;
3. the union of `C` and all vertex regions has one connected component containing the regions of
   all relevant vertices and all of `C`;
4. for every `Σ ∈ 𝔖` meeting a junction, every connected component of `Σ \ C` meets a junction;
5. junctions of `junc(F)` joined by a path in `⋃𝔖 ∪ ⋃junc(F)` are still joined in that set
   minus `C`. -/
def GoodCut {n : ℕ} (p : Fin n → Plane) (D : SimpleGraph (Fin n)) (Λ r : ℝ) (P : Set Plane)
    (Q : JunctionTreeData) (F : BoundaryWalk) (𝔖 : Set (Set Plane)) (C : CutData) : Prop :=
  C.IsPlane ∧
  C.region ⊆ ⋃₀ {W ∈ 𝔖 | ∃ J ∈ junc Q F.region, (W ∩ J).Nonempty} ∧
  Disjoint C.region (buffer P Q F.region (r / 2)) ∧
  (∀ N ∈ fNerves p D Λ r F.region, Disjoint C.region N) ∧
  (∃ K ∈ components (C.region ∪ ⋃ v : CutVertex F 𝔖, vertexRegion Q F 𝔖 v),
    C.region ⊆ K ∧ ∀ v, Relevant Q F 𝔖 v → vertexRegion Q F 𝔖 v ⊆ K) ∧
  (∀ W ∈ 𝔖, (∃ J ∈ junc Q F.region, (W ∩ J).Nonempty) →
    ∀ K ∈ components (W \ C.region), ∃ J ∈ junc Q F.region, (K ∩ J).Nonempty) ∧
  ∀ J ∈ junc Q F.region, ∀ J' ∈ junc Q F.region,
    (∃ a ∈ J, ∃ b ∈ J', JoinsIn (⋃₀ 𝔖 ∪ ⋃₀ junc Q F.region) a b) →
      ∃ a ∈ J, ∃ b ∈ J', JoinsIn ((⋃₀ 𝔖 ∪ ⋃₀ junc Q F.region) \ C.region) a b

/-- Three pairwise adjacent vertices of `D` spanning a triangle with no further input point. -/
def IsDelaunayTriangle {n : ℕ} (p : Fin n → Plane) (D : SimpleGraph (Fin n)) (i j k : Fin n) :
    Prop :=
  D.Adj i j ∧ D.Adj j k ∧ D.Adj k i ∧
    ∀ l : Fin n, p l ∈ convexHull ℝ {p i, p j, p k} → l = i ∨ l = j ∨ l = k

/-- Some edge of `C` joins the points `a` and `b`. -/
def CutData.Joins (C : CutData) (a b : Plane) : Prop :=
  ∃ e ∈ C.edges, (C.point e.1 = a ∧ C.point e.2 = b) ∨ (C.point e.1 = b ∧ C.point e.2 = a)

/-- Reading R3 (Lemma 23's construction, p.42 (PDF 43)): every vertex of `C` is the midpoint of a
Delaunay edge, every edge of `C` joins the midpoints of two sides of one Delaunay triangle, and no
triangle carries all three such segments; so every Delaunay triangle meets `C` in at most two
segments joining edge midpoints. -/
def MidpointForm {n : ℕ} (p : Fin n → Plane) (D : SimpleGraph (Fin n)) (C : CutData) : Prop :=
  (∀ v : Fin C.size, ∃ i j : Fin n, D.Adj i j ∧ C.point v = midpoint ℝ (p i) (p j)) ∧
  (∀ e ∈ C.edges, ∃ i j k : Fin n, IsDelaunayTriangle p D i j k ∧
    ((C.point e.1 = midpoint ℝ (p i) (p j) ∧ C.point e.2 = midpoint ℝ (p j) (p k)) ∨
     (C.point e.1 = midpoint ℝ (p j) (p k) ∧ C.point e.2 = midpoint ℝ (p i) (p j)))) ∧
  ∀ i j k : Fin n, IsDelaunayTriangle p D i j k →
    ¬ (C.Joins (midpoint ℝ (p i) (p j)) (midpoint ℝ (p j) (p k)) ∧
       C.Joins (midpoint ℝ (p j) (p k)) (midpoint ℝ (p k) (p i)) ∧
       C.Joins (midpoint ℝ (p k) (p i)) (midpoint ℝ (p i) (p j)))

end MinDilationTree.Sublinear.Supplement


