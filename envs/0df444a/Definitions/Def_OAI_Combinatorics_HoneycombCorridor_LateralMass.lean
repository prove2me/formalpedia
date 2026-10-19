-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_LateralMass
-- name    : OAI_Combinatorics_HoneycombCorridor_LateralMass
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T11:31:46.914038+00:00
-- url     : https://prove2.me/theorems/24ae54d3-59e5-4f16-96ca-f5ba4c7dee28
-- title:
--   Rightward distance mass and tail constants
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns. Write $x(v)$ for the horizontal position of a vertex and $\rho=(1+\cos(3\pi/8)\sin(\pi/8))^{-1}$ for the ray contraction constant.
--
--   1. **Reaching right.** A word $w$ reaches right distance $t$ if some vertex traced from the bottom source has $x(v)\ge t$. Mirroring the word turns this into reaching $x(v)\le-t$.
--   2. **Right distance mass.** $\mathrm{rightDistanceMass}(D,t)$ is the positive mass $\sum\lambda^{|w|}$ of the source exits of $D$ that reach right distance $t$.
--   3. **Tail constants.** The tail rate and the tail constant are
--   $$
--   c=-\frac{\log\rho}2>0,\qquad C=\frac{2}{\cos(3\pi/8)}\,e^{-\log\rho}=\frac{2}{\rho\cos(3\pi/8)} .
--   $$
--   They appear in the exponential tail bound $C\,e^{-c\,t/(h+1)}$ for walks in a strip of height $h$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/LateralMass.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/LateralMass.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Reflection

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def reachesRight (t : ℝ) (w : List Bool) : Prop :=
  ∃ v ∈ traced bottomSource w, t ≤ (position v).1

noncomputable def rightDistanceMass (D : Finset Vertex) (t : ℝ) : ℝ := by
  classical
  exact positiveWordMass ((sourceExits D bottomSource).filter (reachesRight t))

noncomputable def tailRate : ℝ := -Real.log rayContraction / 2
noncomputable def tailConstant : ℝ :=
  2 * (Real.cos (3*Real.pi/8))⁻¹ * Real.exp (-Real.log rayContraction)

@[simp] theorem reachesRight_mirror (t : ℝ) (w : List Bool) :
    reachesRight t (mirrorWord w) ↔ ∃ v ∈ traced bottomSource w, t ≤ -(position v).1 := by
  have hm := mirror_traced bottomSource w
  rw [mirror_bottomSource] at hm
  simp only [reachesRight,hm,List.mem_map]
  constructor
  · rintro ⟨v,⟨u,hu,rfl⟩,ht⟩
    exact ⟨u,hu,by simpa using ht⟩
  · rintro ⟨v,hv,ht⟩
    exact ⟨mirrorVertex v,⟨v,hv,rfl⟩,by simpa using ht⟩

end PolynomialVacuumBridge.Corridor

end

end OAI


