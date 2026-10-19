-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Convexity
-- name    : OAI_Combinatorics_HoneycombCorridor_Convexity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T11:02:32.940717+00:00
-- url     : https://prove2.me/theorems/f5e7f395-0a27-4e57-b177-fa964a954ee8
-- title:
--   Box indices of honeycomb vertices and star faces of a domain
-- statement:
--   Integer coordinates describing convex regions of the honeycomb lattice.
--
--   1. **Box indices.** Each vertex has three integer indices, one per lattice direction:
--   $$
--   \mathrm{boxIndex}(\mathrm{up}(i,j))=(j,\ i,\ i+j),\qquad\mathrm{boxIndex}(\mathrm{down}(i,j))=(j,\ i,\ i+j+1).
--   $$
--   2. **Boxes.** For integer bounds $\ell,h:\{0,1,2\}\to\mathbb Z$, a vertex is in the box if $\ell_k\le\mathrm{boxIndex}(v)_k<h_k$ for all three directions $k$. Index $0$ is the layer, so the box with only direction $0$ constrained is a horizontal strip.
--   3. **Star faces.** For a finite vertex set $D$, $\mathrm{starFaces}(D)$ is the set of all faces adjacent to some vertex of $D$, i.e. the left faces of the three germs at each $v\in D$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/Convexity.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/Convexity.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def boxIndex : Vertex → Fin 3 → ℤ
  | .up i j, k => if k = 0 then j else if k = 1 then i else i+j
  | .down i j, k => if k = 0 then j else if k = 1 then i else i+j+1

def BoxMem (lo hi : Fin 3 → ℤ) (v : Vertex) : Prop :=
  ∀ k, lo k ≤ boxIndex v k ∧ boxIndex v k < hi k

def starFaces (D : Finset Vertex) : Finset FaceIndex :=
  D.biUnion fun v => Finset.univ.image fun k : Fin 3 => leftFace (v,k)

end PolynomialVacuumBridge.Corridor

end

end OAI


