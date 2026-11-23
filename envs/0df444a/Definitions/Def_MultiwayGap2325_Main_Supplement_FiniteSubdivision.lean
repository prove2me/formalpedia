-- Prove2me | Definitions.Def_MultiwayGap2325_Main_Supplement_FiniteSubdivision
-- name    : MultiwayGap2325_Main_Supplement_FiniteSubdivision
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:17:29.599302+00:00
-- url     : https://prove2.me/theorems/2f941e1e-22b0-4205-a738-098016c83593
-- title:
--   Exact rational ordered-region subdivision of §7.2
-- statement:
--   This module gives a computable exact-rational implementation of the ordered-region subdivision in Section 7.2. For $2\le r$ it constructs the vertices $u_j$ and $v_j$, the displayed simplices in equation (27), their Freudenthal refinement using cumulative lattice paths and the barycentric formula (28), and the recursive coning to $v_r$ and to $u_r,v_r$ above $r_0$. Cells and vertices are represented by lists of rational coordinates, so all subsequent table checks can be evaluated without floating-point arithmetic.
--
--   The subdivision is generated separately for every $r=2,\ldots,q$. This is the finite geometric input required by the integer certificate tables $H,Z,W$ of Sections 7.4–7.6; the module does not supply or assert those external tables.
-- source:
--   Dimitar Chakarov and Yury Makarychev, STOC 2027 submission #697, §7.2, pp.26–27, especially equations (27)–(28), and the coning recursion used for the cell counts on p.31.

import Mathlib.Data.List.Permutation
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace MultiwayGap2325.Main.Supplement

/-- A point in the local coordinates of an ordered region, represented exactly. -/
abbrev LocalPoint := List ℚ

/-- An ordered list of vertices of a local simplex. -/
abbrev LocalCell := List LocalPoint

/-- The vertex `uⱼ` of Section 7.2, with `j` initial coordinates `1/j`. -/
def localU (r j : ℕ) : LocalPoint :=
  (List.range r).map fun i => if i < j then (1 : ℚ) / j else 0

/-- The vertex `vⱼ` of Section 7.2, with first coordinate `T`. -/
def localV (r j : ℕ) (T : ℚ) : LocalPoint :=
  (List.range r).map fun i =>
    if i = 0 then T else if i < j then (1 - T) / (j - 1 : ℕ) else 0

/-- The ordered displayed vertices of one simplex in equation (27). -/
def initialVertices (r s : ℕ) (T : ℚ) : List LocalPoint :=
  ((List.range (s - 1)).map fun k => localU r (k + 2)) ++
    ((List.range (r + 1 - s)).map fun k => localV r (k + s) T)

/-- All weakly increasing lists of length `d` with entries below `n`. -/
def weakVectors : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | d + 1, n => (List.range n).flatMap fun a =>
      (weakVectors d n).filterMap fun zs =>
        if zs.all (fun z => decide (a ≤ z)) then some (a :: zs) else none

/-- Boolean test for a weakly increasing path vector. -/
def isWeak : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: zs => decide (a ≤ b) && isWeak (b :: zs)

/-- Add one to the `j`th coordinate of a cumulative lattice vector. -/
def bumpCoordinate (z : List ℕ) (j : ℕ) : List ℕ :=
  z.mapIdx fun i a => if i = j then a + 1 else a

/-- The path `z, z+eσ(1), …, z+(1,…,1)` in Section 7.2. -/
def cubePath (z sigma : List ℕ) : List (List ℕ) :=
  sigma.scanl bumpCoordinate z

def successiveDifferences : ℕ → List ℕ → List ℕ
  | _, [] => []
  | prev, a :: zs => (a - prev) :: successiveDifferences a zs

/-- Cumulative-to-barycentric coordinates, before division by `n` (28). -/
def barycentricNumerators (n : ℕ) (y : List ℕ) : List ℕ :=
  (n - (y.getLast?).getD 0) :: successiveDifferences 0 y

/-- Take a rational convex combination of the displayed vertices. -/
def convexCombination (r n : ℕ) (vertices : List LocalPoint)
    (coefficients : List ℕ) : LocalPoint :=
  (List.range r).map fun j =>
    ((vertices.zip coefficients).foldl
      (fun sum vc => sum + (vc.2 : ℚ) * (vc.1[j]?).getD 0) 0) / n

/-- The Freudenthal cells obtained from one displayed simplex in (27). -/
def initialMesh (r n : ℕ) (vertices : List LocalPoint) : List LocalCell :=
  (weakVectors (r - 1) n).flatMap fun z =>
    (List.range (r - 1)).permutations.flatMap fun sigma =>
      let path := cubePath z sigma
      if path.all isWeak then
        [path.map fun y =>
          convexCombination r n vertices (barycentricNumerators n y)]
      else []

/-- The complete mesh in dimensions at most `r₀`, before the coning recursion. -/
def baseMesh (r n : ℕ) (T : ℚ) : List LocalCell :=
  (List.range (r - 1)).flatMap fun k =>
    initialMesh r n (initialVertices r (k + 2) T)

def eraseVertex (cell : LocalCell) (k : ℕ) : LocalCell := cell.eraseIdx k

/-- The facets of a simplex, indexed by the deleted vertex. -/
def cellFacets (cell : LocalCell) : List LocalCell :=
  (List.range cell.length).map (eraseVertex cell)

def appendZero (x : LocalPoint) : LocalPoint := x ++ [0]

/-- The facets of a mesh on the equality hyperplane `x₀ = x₁`, without duplicates. -/
def equalityFacets (meshes : List LocalCell) : List LocalCell :=
  ((meshes.flatMap cellFacets).filter fun facet =>
    facet.all fun x => decide ((x[0]?).getD 0 = (x[1]?).getD 0)).dedup

/-- Append a zero coordinate and cone a lower cell to `vᵣ`. -/
def coneToV (r : ℕ) (T : ℚ) (cell : LocalCell) : LocalCell :=
  cell.map appendZero ++ [localV r r T]

/-- Cone an equality facet to the two new vertices `uᵣ` and `vᵣ`. -/
def coneEqualityToUV (r : ℕ) (T : ℚ) (facet : LocalCell) : LocalCell :=
  facet.map appendZero ++ [localU r r, localV r r T]

/-- Exact recursive subdivision of the ordered region `Oᵣ` in Section 7.2. -/
def orderedMesh (T : ℚ) (n r0 : ℕ) : ℕ → List LocalCell
  | 0 => []
  | 1 => []
  | r + 2 =>
      if r + 2 ≤ r0 then baseMesh (r + 2) n T else
        let lower := orderedMesh T n r0 (r + 1)
        (lower.map (coneToV (r + 2) T)) ++
          ((equalityFacets lower).map (coneEqualityToUV (r + 2) T))

/-- All local cells for `r = 2,…,q`, in increasing dimension. -/
def orderedRegionCells (q : ℕ) (T : ℚ) (n r0 : ℕ) : List LocalCell :=
  (List.range (q - 1)).flatMap fun k => orderedMesh T n r0 (k + 2)

/-- The numbers of cells in dimensions `r = 2,…,q`. -/
def orderedRegionCellCounts (q : ℕ) (T : ℚ) (n r0 : ℕ) : List ℕ :=
  (List.range (q - 1)).map fun k => (orderedMesh T n r0 (k + 2)).length

end MultiwayGap2325.Main.Supplement


