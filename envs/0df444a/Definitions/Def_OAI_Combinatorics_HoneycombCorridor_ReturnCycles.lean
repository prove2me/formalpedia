-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ReturnCycles
-- name    : OAI_Combinatorics_HoneycombCorridor_ReturnCycles
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:53:18.296425+00:00
-- url     : https://prove2.me/theorems/7e6f1193-d990-4ce6-982a-5e7b3d1471c4
-- title:
--   Ray records, ray leaves and returning rays at a vertex
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns.
--
--   1. **Ray records.** A ray record is a pair $(k,w)$ of a slot and a word. The ray germ $\mathrm{rayGerm}(v,k)=(\mathrm{neighbor}(v,k),k)$ is the germ obtained by stepping from $v$ along slot $k$.
--   2. **Ray leaves.** For a domain $D$ and $v$, $\mathrm{rayLeaves}(D,v)$ consists of all records $(k,w)$ with $w$ stopped in $D\setminus\{v\}$ from $\mathrm{rayGerm}(v,k)$.
--   3. **Returns.** $\mathrm{rayReturns}(D,v)$ consists of those ray leaves whose terminal vertex is $v$ itself:
--   $$
--   (k,w)\in\mathrm{rayReturns}(D,v)\iff w\text{ stopped in }D\setminus\{v\}\text{ from }\mathrm{rayGerm}(v,k)\text{ and the walk ends at }v .
--   $$
--   These are the walks that leave $v$ and come back to it, closing a cycle through $v$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/ReturnCycles.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/ReturnCycles.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

abbrev RayRecord := Fin 3 × List Bool

def rayGerm (v : Vertex) (k : Fin 3) : Germ := (neighbor v k,k)

noncomputable def rayLeaves (D : Finset Vertex) (v : Vertex) : Finset RayRecord :=
  Finset.univ.biUnion fun k : Fin 3 =>
    (leaves (D.erase v) (rayGerm v k)).image fun w => (k,w)

@[simp] theorem mem_rayLeaves (D : Finset Vertex) (v : Vertex) (e : RayRecord) :
    e ∈ rayLeaves D v ↔ Stopped (D.erase v) (rayGerm v e.1) e.2 := by
  classical
  simp only [rayLeaves,Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨k,w,hw,he⟩
    subst e
    exact (mem_leaves_iff _ _ _).mp hw
  · intro h
    exact ⟨e.1,e.2,(mem_leaves_iff _ _ _).mpr h,rfl⟩

noncomputable def rayReturns (D : Finset Vertex) (v : Vertex) : Finset RayRecord := by
  classical
  exact (rayLeaves D v).filter fun e => (terminalGerm (rayGerm v e.1) e.2).1 = v

@[simp] theorem mem_rayReturns (D : Finset Vertex) (v : Vertex) (e : RayRecord) :
    e ∈ rayReturns D v ↔ Stopped (D.erase v) (rayGerm v e.1) e.2 ∧
      (terminalGerm (rayGerm v e.1) e.2).1 = v := by
  classical
  simp [rayReturns]

end PolynomialVacuumBridge.Corridor

end

end OAI


