-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryFlux
-- name    : OAI_Combinatorics_HoneycombCorridor_BoundaryFlux
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T11:20:16.384921+00:00
-- url     : https://prove2.me/theorems/c1773f29-f175-4920-bcd9-3c5458ae3564
-- title:
--   Strip geometry, lateral masses and direction codes
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns. Positions: $\mathrm{up}(i,j)$ has horizontal coordinate $i+j/2$ and $\mathrm{down}(i,j)$ has $i+j/2+\frac12$.
--
--   1. **Source.** The bottom source is the germ $(\mathrm{up}(0,0),0)$, entering the origin from below. A source exit $w\in\mathrm{sourceExits}(D,g)$ is a stopped word from $g$ ending outside $D$.
--   2. **Strip.** A vertex is in the strip of height $h$ if its layer $j$ satisfies $0\le j<h$.
--   3. **Lateral masses.** A word reaches distance $t$ if some traced vertex has $|x|\ge t$. For a domain $D$,
--   $$
--   \mathrm{lateralMass}(D,t)=\sum_{w}\lambda^{|w|},\qquad\mathrm{lateralLengthMass}(D,t)=\sum_{w}|w|\,\lambda^{|w|},
--   $$
--   both summed over source exits from the bottom source that reach distance $t$.
--   4. **Direction code.** Each germ gets a code in $\{0,\dots,5\}$ recording the direction of its incoming edge in units of $\pi/3$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/BoundaryFlux.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/BoundaryFlux.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

@[simp] theorem mem_sourceExits (D : Finset Vertex) (g : Germ) (w : List Bool) :
    w ∈ sourceExits D g ↔ Stopped D g w ∧ (terminalGerm g w).1 ∉ D := by
  classical
  simp [sourceExits,mem_leaves_iff]

def bottomSource : Germ := (.up 0 0,0)

def InStrip (h : ℕ) (v : Vertex) : Prop := 0 ≤ boxIndex v 0 ∧ boxIndex v 0 < (h : ℤ)

noncomputable def reachesDistance (t : ℝ) (w : List Bool) : Prop :=
  ∃ v ∈ traced bottomSource w, t ≤ |(position v).1|

noncomputable def lateralMass (D : Finset Vertex) (t : ℝ) : ℝ := by
  classical
  exact ∑ w ∈ sourceExits D bottomSource,
    if reachesDistance t w then criticalActivity ^ w.length else 0

noncomputable def lateralLengthMass (D : Finset Vertex) (t : ℝ) : ℝ := by
  classical
  exact ∑ w ∈ sourceExits D bottomSource,
    if reachesDistance t w then (w.length : ℝ) * criticalActivity ^ w.length else 0

def directionCode (g : Germ) : ℤ := match g.1 with
  | .up _ _ => if g.2 = 0 then 0 else if g.2 = 1 then 2 else 4
  | .down _ _ => if g.2 = 0 then 3 else if g.2 = 1 then 5 else 1

end PolynomialVacuumBridge.Corridor

end

end OAI


