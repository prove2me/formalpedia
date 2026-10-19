-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_FaceBoundary
-- name    : OAI_Combinatorics_HoneycombCorridor_FaceBoundary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T11:05:54.797613+00:00
-- url     : https://prove2.me/theorems/7393ef53-ac12-47a8-a971-028b9a620b81
-- title:
--   Boundary germs of a face set and the boundary-following walk
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns. Let $S$ be a finite set of hexagonal faces.
--
--   1. **Face-boundary germs.** A germ $g$ is on the boundary of $S$ if its left face is not in $S$ and its right face is in $S$, so the walk keeps $S$ on its right.
--   2. **Boundary turn.** The boundary turn at $g$ is a left turn exactly when the face to the left of the slot $g_2+1$ is outside $S$; otherwise it is a right turn. Advancing with this turn stays on the boundary, and every boundary germ sits at a cell vertex of $S$.
--   3. **Boundary walk.** Face-boundary germs form a finite set, $\mathrm{next}(g)=\mathrm{advance}(g,\mathrm{turn}(g))$ is a self-map of it, and
--   $$
--   \mathrm{faceBoundaryWord}(S,g,n)=\bigl(\mathrm{turn}(g),\mathrm{turn}(\mathrm{next}\,g),\dots\bigr)\quad(n\text{ letters})
--   $$
--   records the turns made when following the boundary of $S$ for $n$ steps.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/FaceBoundary.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/FaceBoundary.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def OnFaceBoundary (S : Finset FaceIndex) (g : Germ) : Prop :=
  leftFace g ∉ S ∧ rightFace g ∈ S

noncomputable def faceBoundaryTurn (S : Finset FaceIndex) (g : Germ) : Bool :=
  decide (leftFace (g.1,g.2+1) ∉ S)

theorem faceBoundary_advance (S : Finset FaceIndex) (g : Germ)
    (hg : OnFaceBoundary S g) :
    OnFaceBoundary S (advance g (faceBoundaryTurn S g)) := by
  classical
  rcases g with ⟨v,k⟩
  have h := hg
  simp only [OnFaceBoundary,rightFace_prev] at h
  unfold faceBoundaryTurn
  by_cases ht : leftFace (v,k+1) ∈ S
  · simp only [ht,not_true_eq_false,decide_false]
    cases v <;> fin_cases k <;>
      simp_all [OnFaceBoundary,advance,outgoingSlot,leftFace,rightFace,reverseGerm,neighbor]
  · simp only [ht,not_false_eq_true,decide_true]
    cases v <;> fin_cases k <;>
      simp_all [OnFaceBoundary,advance,outgoingSlot,leftFace,rightFace,reverseGerm,neighbor]

theorem faceBoundary_vertex_mem (S : Finset FaceIndex) (g : Germ)
    (hg : OnFaceBoundary S g) : g.1 ∈ cellVertices S := by
  apply (mem_cellVertices _ _).mpr
  exact ⟨g.2+2,by simpa only [rightFace_prev] using
    (show rightFace (g.1,g.2) ∈ S from hg.2)⟩

abbrev FaceBoundary (S : Finset FaceIndex) := {g : Germ // OnFaceBoundary S g}

noncomputable instance faceBoundaryFinite (S : Finset FaceIndex) : Finite (FaceBoundary S) := by
  let f : FaceBoundary S → (cellVertices S) × Fin 3 :=
    fun g => (⟨g.val.1,faceBoundary_vertex_mem S g.val g.property⟩,g.val.2)
  apply Finite.of_injective f
  intro g h he
  apply Subtype.ext
  have hv := congrArg (fun x : (cellVertices S) × Fin 3 => (x.1.val,x.2)) he
  exact hv

noncomputable def faceBoundaryNext (S : Finset FaceIndex) (g : FaceBoundary S) : FaceBoundary S :=
  ⟨advance g.val (faceBoundaryTurn S g.val),faceBoundary_advance S _ g.property⟩

noncomputable def faceBoundaryWord (S : Finset FaceIndex) (g : FaceBoundary S) : ℕ → List Bool
  | 0 => []
  | n+1 => faceBoundaryTurn S g.val :: faceBoundaryWord S (faceBoundaryNext S g) n

end PolynomialVacuumBridge.Corridor

end

end OAI


