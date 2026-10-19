-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Polygons
-- name    : OAI_Combinatorics_HoneycombCorridor_Polygons
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:37:31.990991+00:00
-- url     : https://prove2.me/theorems/310553ec-984e-4315-860e-e802df8802c9
-- title:
--   Honeycomb polygons, filled domains and admissibly convex domains
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns.
--
--   1. **Turning of simple loops.** The proposition SimplePolygonTurning says that every nonempty simple closed walk has $\mathrm{turnUnits}=\pm6$, i.e. total turning $\pm2\pi$.
--   2. **Polygons.** A finite edge set $E$ is a polygon if it is the support of the word flow of a nonempty simple closed walk. A polygon carries a chosen traversal, its indicator potential with orientation $\varepsilon=\pm1$, its interior faces (the support of the potential), its vertex set, and its interior vertices: cell vertices of the interior faces that are not on the polygon.
--   3. **Polygons of a domain.** For a finite vertex set $D$, the induced edges have both ends in $D$, and $\mathrm{polygons}(D)$ is the finite set of polygons made of induced edges. $D$ is filled if every polygon of $D$ has its interior inside $D$.
--   4. **Convexity.** The three tiling coordinates of a point $z=(x,y)$ are $2y/\sqrt3$, $x-y/\sqrt3+\frac12$ and $x+y/\sqrt3+\frac12$. $D$ is admissibly convex if for integers $\ell_k<h_k$,
--   $$
--   v\in D\iff\ell_k<\mathrm{tilingCoordinate}_k(\mathrm{position}(v))<h_k\quad(k=0,1,2).
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/Polygons.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/Polygons.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HoneycombBridgeFiniteness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Contours
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Cells
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RationalPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Currents
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PotentialSupport
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Incidence
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Curvature

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def SimplePolygonTurning : Prop := ∀ (g : Germ) (w : List Bool),
  w ≠ [] → (traced g w).Nodup → terminalGerm g w = g →
    turnUnits w = 6 ∨ turnUnits w = -6

def IsPolygon (E : Finset EdgeIndex) : Prop := ∃ (g : Germ) (w : List Bool),
  w ≠ [] ∧ (traced g w).Nodup ∧ terminalGerm g w = g ∧ (wordFlow g w).support = E

abbrev Polygon := { E : Finset EdgeIndex // IsPolygon E }

namespace Polygon
noncomputable def germ (P : Polygon) : Germ := P.property.choose
noncomputable def turns (P : Polygon) : List Bool := P.property.choose_spec.choose

theorem traversal (P : Polygon) :
    P.turns ≠ [] ∧ (traced P.germ P.turns).Nodup ∧
    terminalGerm P.germ P.turns = P.germ ∧ (wordFlow P.germ P.turns).support = P.val :=
  P.property.choose_spec.choose_spec

theorem has_indicator (P : Polygon) :
    ∃ (p : FaceIndex →₀ ℤ) (ε : ℤ), RepresentsFlow p (wordFlow P.germ P.turns) ∧
      p ≠ 0 ∧ (ε = 1 ∨ ε = -1) ∧ ∀ a, p a = 0 ∨ p a = ε :=
  simple_closed_word_indicator P.germ P.turns P.traversal.1 P.traversal.2.1 P.traversal.2.2.1

noncomputable def potential (P : Polygon) : FaceIndex →₀ ℤ := P.has_indicator.choose
noncomputable def orientation (P : Polygon) : ℤ := P.has_indicator.choose_spec.choose

noncomputable def interiorFaces (P : Polygon) : Finset FaceIndex := P.potential.support

def vertices (P : Polygon) : Finset Vertex := P.val.biUnion fun e => {upEnd e,downEnd e}

noncomputable def interior (P : Polygon) : Finset Vertex :=
  cellVertices P.interiorFaces \ P.vertices

end Polygon

noncomputable def inducedEdges (D : Finset Vertex) : Finset EdgeIndex := by
  classical
  exact ((D.product Finset.univ).image edgeOf).filter fun e => upEnd e ∈ D ∧ downEnd e ∈ D

noncomputable def polygons (D : Finset Vertex) : Finset Polygon := by
  classical
  exact (inducedEdges D).powerset.subtype IsPolygon

def Filled (D : Finset Vertex) : Prop := ∀ P ∈ polygons D, P.interior ⊆ D

noncomputable def tilingCoordinate (k : Fin 3) (z : ℝ × ℝ) : ℝ :=
  if k = 0 then 2 * z.2 / Real.sqrt 3
  else if k = 1 then z.1 - z.2 / Real.sqrt 3 + 1 / 2
  else z.1 + z.2 / Real.sqrt 3 + 1 / 2

def AdmissiblyConvex (D : Finset Vertex) : Prop :=
  ∃ lo hi : Fin 3 → ℤ, ∀ v : Vertex, v ∈ D ↔ ∀ k : Fin 3,
    (lo k : ℝ) < tilingCoordinate k (position v) ∧
    tilingCoordinate k (position v) < (hi k : ℝ)

end PolynomialVacuumBridge.Corridor

end

end OAI


