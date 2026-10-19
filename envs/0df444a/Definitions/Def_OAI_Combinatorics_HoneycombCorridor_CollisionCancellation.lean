-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionCancellation
-- name    : OAI_Combinatorics_HoneycombCorridor_CollisionCancellation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:50:11.74557+00:00
-- url     : https://prove2.me/theorems/e59cd607-4bfa-41a6-b957-d48d41d94188
-- title:
--   The polygon traced by a simple closed walk
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns. A polygon is a finite set of edges that is the support of the word flow of some nonempty simple closed walk.
--
--   For a germ $g$ and a nonempty word $w$ whose trace has no repeated vertex and which returns to its starting germ ($\mathrm{terminalGerm}(g,w)=g$), the polygon of the closed walk is
--   $$
--   \mathrm{polygonOfClosed}(g,w)=\operatorname{supp}\bigl(\mathrm{wordFlow}(g,w)\bigr),
--   $$
--   packaged together with the witness $(g,w)$ showing that it is a polygon. This is the polygon closed off when a walk collides with its own past and the loop is cut out.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/CollisionCancellation.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/CollisionCancellation.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def polygonOfClosed (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g) : Polygon :=
  ⟨(wordFlow g w).support,⟨g,w,hne,hN,hc,rfl⟩⟩

end PolynomialVacuumBridge.Corridor

end

end OAI


