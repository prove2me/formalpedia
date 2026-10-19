-- Prove2me | Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
-- name    : OAI_GroupTheory_Hyperbolic_Links
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:51:58.421994+00:00
-- url     : https://prove2.me/theorems/83f00768-e986-4dd9-96ba-b767ba1d4979
-- title:
--   The vertex links of the triangle complex
-- statement:
--   The links at the three vertices $o,v,w$ of the triangle complex built from marked-line data, and the direction carried by each corner of a filling.
--
--   1. **Directions.** At $o$ the directions are the $l$-edges and the $r$-edges. At $v$ and at $w$ they are the $x$-triples $(i,u,v)$ together with the $l$-directions of the shift scheme at $v$, resp. $w$.
--   2. **The link graph.** The link is the disjoint union of three graphs:
--   - at $o$, the complete bipartite graph between $l$-edges and $r$-edges;
--   - at $v$ and at $w$, the bipartite link graphs of the two shift schemes.
--   3. **Corners.** Each oriented edge of the presentation determines the direction in which it leaves or enters a vertex; an $x$-edge $(i,u,v)$ is read as $(i,v,u)$ at $w$. Directions are coloured $0,1,2$ by vertex:
--   $$
--   o\mapsto0,\qquad v\mapsto1,\qquad w\mapsto2 .
--   $$
--   4. **Fillings.** For a triangle filling over the presentation and a boundary dart, the concrete ribbon is the ribbon of that filling coloured by vertices, and each active dart has the direction of its label.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Links.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Links.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TorsionFreeHyperbolic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons

namespace OAI

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

abbrev ODirections := (d.presentation hr).LEdge ⊕ (d.presentation hr).REdge
abbrev VDirections := ShiftScheme.XDirection (I := d.Label) (r := r) ⊕ (d.vShift hr).LDirection
abbrev WDirections := ShiftScheme.XDirection (I := d.Label) (r := r) ⊕ (d.wShift hr).LDirection
abbrev AllDirections := d.ODirections hr ⊕ (d.VDirections hr ⊕ d.WDirections hr)

/-- At O a larger complete bipartite graph suffices for the four-edge girth bound;
at V and W we use precisely the shifted incidence links. -/
noncomputable def allLink : SimpleGraph (d.AllDirections hr) :=
  (relationGraph (fun (_ : (d.presentation hr).LEdge) (_ : (d.presentation hr).REdge) => True)).sum
    ((d.vShift hr).link.sum (d.wShift hr).link)

def linkDirection : (d.presentation hr).OrientedEdge → d.AllDirections hr
  | (.inl (i,u,v),false) => .inr (.inl (.inl (i,u,v)))
  | (.inl (i,u,v),true) => .inr (.inr (.inl (i,v,u)))
  | (.inr (.inl l),false) => .inl (.inl l)
  | (.inr (.inl l),true) => .inr (.inl (.inr l))
  | (.inr (.inr s),false) => .inl (.inr s)
  | (.inr (.inr s),true) => .inr (.inr (.inr s))

def linkColor : d.AllDirections hr → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

end Release075.MarkedLineData

namespace Release075.MarkedLineData
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

variable {w : List (d.presentation hr).OrientedEdge}
variable (D : TriangleFilling (d.presentation hr).flipEdge (d.presentation hr).edgeTarget
  (d.presentation hr).TriangleFace w) (b : D.Dart) (hb : b ∈ D.boundary)

noncomputable abbrev concreteRibbon := D.ribbon (d.presentation hr).vertexColor
  (fun _ _ _ => BlockPresentation.TriangleFace.colors _) b hb

def dartDirection (a : D.ActiveDart) : d.AllDirections hr :=
  d.linkDirection hr (D.label a)

end Release075.MarkedLineData

end OAI


