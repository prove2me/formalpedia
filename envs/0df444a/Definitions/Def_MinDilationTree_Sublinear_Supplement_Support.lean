-- Prove2me | Definitions.Def_MinDilationTree_Sublinear_Supplement_Support
-- name    : MinDilationTree_Sublinear_Supplement_Support
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T14:53:59.641128+00:00
-- url     : https://prove2.me/theorems/cdcd7396-175e-4004-a984-44337642733a
-- title:
--   Delaunay triangulations, the $r$-support and $\Lambda$-thin point sets
-- statement:
--   Let $S=\{p_0,\ldots,p_{n-1}\}\subset\mathbb R^2$ be distinct points.
--
--   1. A segment $p_ip_j$ ($i\ne j$) is an **empty-disk edge** if some open disk with $p_i$ and $p_j$ on its boundary circle contains no point of $S$. A **Delaunay triangulation** $D$ of $S$ is an inclusion-maximal set of empty-disk edges whose segments pairwise meet only in shared endpoints. No general position is assumed: for collinear points it is the path of consecutive points, and every choice is admitted (reading R1).
--   2. For $r\in\mathbb R$, delete the edges of $D$ longer than $r$. For every connected component $K$ (embedded, isolated points included) take the closed region bounded by its outer boundary walk, namely $K$ together with the bounded connected components of $\mathbb R^2\setminus K$. The **$r$-support** $\mathcal P_r(S)$ is the set of these regions that are maximal under inclusion (Definition 2). It may contain one-point polygons.
--   3. $S$ is **$\Lambda$-thin** (with respect to $D$) if for every $r>0$ every polygon $P\in\mathcal P_r$ is $\Lambda r$-thin: every disk contained in $P$ has radius at most $\Lambda r$ (Definition 3).
--
--   The $r$-supports at the scales $r$, $r/\Lambda$ and $r/\Lambda^2$ define the polygons, spines and nerves of the junction-tree machinery.
--
--   **Formalization Note** The polygons of $\mathcal P_r$ are represented by their closed regions; the outer boundary walk of a connected plane graph bounds exactly this region and is weakly simple. Every statement that uses $D$ quantifies over every Delaunay triangulation, so the platform's general-position Delaunay definition is not used.
-- source:
--   Sarita de Berg, Jacobus Conradi, Peter Kramer, André Nusser, Sampson Wong, STOC 2027 submission #185 (October 2026), p. 3 (PDF p. 4), §2, Definition 2 (r-support), Definition 3 (Λ-thin point set); reading R1 of the mission plan

import Mathlib
import Definitions.Def_MinDilationTree_Sublinear_Supplement_Polygon

open scoped ENNReal

set_option autoImplicit false

namespace MinDilationTree.Sublinear.Supplement

open MinDilationTree.Sublinear

/-- Delaunay edge condition: some open disk contains no input point and has both endpoints on its
boundary circle. -/
def EmptyDiskEdge {n : ℕ} (p : Fin n → Plane) (i j : Fin n) : Prop :=
  i ≠ j ∧ ∃ x : Plane, ∃ R : ℝ, 0 < R ∧
    dist (p i) x = R ∧ dist (p j) x = R ∧ ∀ k : Fin n, R ≤ dist (p k) x

/-- Straight-line edges meet only in shared endpoints (collinear overlaps are excluded). -/
def PlaneGraph {n : ℕ} (p : Fin n → Plane) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ i j k l : Fin n, G.Adj i j → G.Adj k l →
    (i ≠ k ∨ j ≠ l) → (i ≠ l ∨ j ≠ k) →
    segment ℝ (p i) (p j) ∩ segment ℝ (p k) (p l) ⊆ ({p i, p j} ∩ {p k, p l})

/-- Reading R1: a Delaunay triangulation of `S` is an inclusion-maximal plane graph all of whose
edges are empty-disk edges. In general position it is the unique Delaunay triangulation; for
collinear inputs it is the path of consecutive points; every choice is admitted. -/
def IsDelaunay {n : ℕ} (p : Fin n → Plane) (D : SimpleGraph (Fin n)) : Prop :=
  PlaneGraph p D ∧ (∀ i j, D.Adj i j → EmptyDiskEdge p i j) ∧
    ∀ H : SimpleGraph (Fin n), D ≤ H → PlaneGraph p H →
      (∀ i j, H.Adj i j → EmptyDiskEdge p i j) → H = D

/-- The triangulation after removing all edges of length greater than `r`. -/
noncomputable def thresholdGraph {n : ℕ} (p : Fin n → Plane) (D : SimpleGraph (Fin n))
    (r : ℝ) : SimpleGraph (Fin n) where
  Adj i j := D.Adj i j ∧ ‖p i - p j‖ ≤ r
  symm := ⟨fun i j h => ⟨h.1.symm, by simpa [norm_sub_rev] using h.2⟩⟩
  loopless := ⟨fun i h => D.irrefl h.1⟩

/-- The embedded connected component of the graph containing `i` (isolated points included). -/
def componentTrace {n : ℕ} (p : Fin n → Plane) (G : SimpleGraph (Fin n)) (i : Fin n) :
    Set Plane :=
  {x | (∃ j : Fin n, G.Reachable i j ∧ x = p j) ∨
    ∃ j k : Fin n, G.Reachable i j ∧ G.Adj j k ∧ x ∈ segment ℝ (p j) (p k)}

/-- The closed region bounded by the outer boundary walk of a connected plane-graph component `K`:
`K` together with the bounded connected components of its complement. -/
def outerFill (K : Set Plane) : Set Plane :=
  K ∪ {x | x ∉ K ∧ Bornology.IsBounded (connectedComponentIn Kᶜ x)}

/-- The polygons bounded by the outer boundary walks of all components. -/
def componentRegions {n : ℕ} (p : Fin n → Plane) (D : SimpleGraph (Fin n)) (r : ℝ) :
    Set (Set Plane) :=
  Set.range fun i : Fin n => outerFill (componentTrace p (thresholdGraph p D r) i)

/-- Definition 2, p.3 (PDF 4): the `r`-support `P_r(S)` of `S` with respect to the Delaunay
triangulation `D`, the inclusion-wise maximal ones among those polygons. -/
def support {n : ℕ} (p : Fin n → Plane) (D : SimpleGraph (Fin n)) (r : ℝ) : Set (Set Plane) :=
  {P ∈ componentRegions p D r | ∀ Q ∈ componentRegions p D r, P ⊆ Q → Q = P}

/-- The union `⋃_{P ∈ P_r} P`. -/
def supportUnion {n : ℕ} (p : Fin n → Plane) (D : SimpleGraph (Fin n)) (r : ℝ) : Set Plane :=
  ⋃₀ support p D r

/-- Definition 3, p.3 (PDF 4): `S` is `Λ`-thin (w.r.t. `D`) if for all `r > 0` every polygon of
the `r`-support is `Λr`-thin. -/
def PointSetThin {n : ℕ} (p : Fin n → Plane) (D : SimpleGraph (Fin n)) (Λ : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ P ∈ support p D r, RegionThin P (Λ * r)

end MinDilationTree.Sublinear.Supplement


