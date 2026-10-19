-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Reflection
-- name    : OAI_Combinatorics_HoneycombCorridor_Reflection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T11:29:55.58488+00:00
-- url     : https://prove2.me/theorems/22109ecc-0bf4-40ed-975f-d0389f772d28
-- title:
--   Mirror symmetry of the honeycomb lattice
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns.
--
--   1. **Mirror maps.** $\mathrm{up}(i,j)\mapsto\mathrm{up}(-i-j,j)$ and $\mathrm{down}(i,j)\mapsto\mathrm{down}(-i-j-1,j)$ reflect the lattice in the vertical axis through the origin. Slots $1$ and $2$ are exchanged and slot $0$ is fixed, germs are mirrored componentwise, and words are mirrored by swapping left and right turns.
--   2. **Equivariance.** All mirror maps are involutions. The horizontal position changes sign, and mirroring commutes with neighbours, advancing, terminal germs and traces:
--   $$
--   \mathrm{traced}(\mathrm{mirror}\,g,\mathrm{mirror}\,w)=\mathrm{mirror}\bigl(\mathrm{traced}(g,w)\bigr).
--   $$
--   The bottom source is fixed.
--   3. **Domains.** The mirror domain is the image of $D$; box index $0$ is preserved and indices $1$ and $2$ are exchanged with a sign change.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/Reflection.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/Reflection.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Polygons
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionPhase
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CycleSplice
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionHistories
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PolygonGeometry
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionCancellation
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Traversals
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ReturnCycles
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionStems
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionGrouping
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Convexity
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_FaceBoundary
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryCharge
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryContainment
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryArcs
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ConvexDomains
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_VisitRecursion
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryFlux
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ConvexCuts
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RaySeparation
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_StripDecay

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def mirrorVertex : Vertex → Vertex
  | .up i j => .up (-i-j) j
  | .down i j => .down (-i-j-1) j

def mirrorSlot (k : Fin 3) : Fin 3 := if k = 0 then 0 else if k = 1 then 2 else 1

def mirrorGerm (g : Germ) : Germ := (mirrorVertex g.1,mirrorSlot g.2)
def mirrorWord (w : List Bool) : List Bool := w.map Bool.not

@[simp] theorem mirrorVertex_invol (v : Vertex) : mirrorVertex (mirrorVertex v) = v := by
  cases v <;> simp [mirrorVertex]
  omega

@[simp] theorem mirrorSlot_invol (k : Fin 3) : mirrorSlot (mirrorSlot k) = k := by
  fin_cases k <;> rfl

@[simp] theorem mirrorGerm_invol (g : Germ) : mirrorGerm (mirrorGerm g) = g := by
  simp [mirrorGerm]

@[simp] theorem mirrorWord_invol (w : List Bool) : mirrorWord (mirrorWord w) = w := by
  simp [mirrorWord,List.map_map,Function.comp_def]

@[simp] theorem mirrorWord_length (w : List Bool) : (mirrorWord w).length = w.length := by
  simp [mirrorWord]

@[simp] theorem mirror_position (v : Vertex) : (position (mirrorVertex v)).1 = -(position v).1 := by
  cases v <;> simp [mirrorVertex,position] <;> ring

@[simp] theorem mirror_neighbor (v : Vertex) (k : Fin 3) :
    mirrorVertex (neighbor v k) = neighbor (mirrorVertex v) (mirrorSlot k) := by
  cases v <;> fin_cases k <;> simp [mirrorVertex,mirrorSlot,neighbor] <;> omega

@[simp] theorem mirror_advance (g : Germ) (b : Bool) :
    mirrorGerm (advance g b) = advance (mirrorGerm g) (!b) := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> cases b <;>
    simp [mirrorGerm,mirrorVertex,mirrorSlot,advance,outgoingSlot,neighbor,
      Fin.reduceAdd,Fin.reduceEq,Fin.isValue] <;> omega

@[simp] theorem mirror_terminal (g : Germ) (w : List Bool) :
    terminalGerm (mirrorGerm g) (mirrorWord w) = mirrorGerm (terminalGerm g w) := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
    simp only [mirrorWord,List.map_cons,terminalGerm,← mirror_advance]
    exact ih _

@[simp] theorem mirror_traced (g : Germ) (w : List Bool) :
    traced (mirrorGerm g) (mirrorWord w) = (traced g w).map mirrorVertex := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
    change mirrorVertex g.1 :: traced (advance (mirrorGerm g) (!b)) (mirrorWord w) =
      mirrorVertex g.1 :: (traced (advance g b) w).map mirrorVertex
    rw [← mirror_advance,ih]

@[simp] theorem mirror_bottomSource : mirrorGerm bottomSource = bottomSource := by rfl

noncomputable def mirrorDomain (D : Finset Vertex) : Finset Vertex := D.image mirrorVertex

@[simp] theorem mem_mirrorDomain (D : Finset Vertex) (v : Vertex) :
    v ∈ mirrorDomain D ↔ mirrorVertex v ∈ D := by
  constructor
  · intro hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    simpa using hu
  · intro hv
    exact Finset.mem_image.mpr ⟨mirrorVertex v,hv,mirrorVertex_invol v⟩

@[simp] theorem mirrorDomain_invol (D : Finset Vertex) : mirrorDomain (mirrorDomain D) = D := by
  ext v
  simp

@[simp] theorem mirror_indices (v : Vertex) :
    boxIndex (mirrorVertex v) 0 = boxIndex v 0 ∧
    boxIndex (mirrorVertex v) 1 = -boxIndex v 2 ∧
    boxIndex (mirrorVertex v) 2 = -boxIndex v 1 := by
  cases v <;> simp [mirrorVertex,boxIndex] <;> omega

end PolynomialVacuumBridge.Corridor

end

end OAI


