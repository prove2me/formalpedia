-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
-- name    : OAI_Probability_CriticalZ3_EntryLayers
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:02:38.259308+00:00
-- url     : https://prove2.me/theorems/fcd7f211-ed76-4a04-9a63-1ef7964a9cd7
-- title:
--   Entry points into a box and blocked exploration
-- statement:
--   The layer of vertices just outside a box $C$ through which a cluster can enter it, in a finite lattice graph.
--
--   1. **Exterior vertices.** A vertex $y$ is exterior to $C$ if it lies outside $C$ but has a nearest neighbour inside; its entry point is such a neighbour, and its entry bit is the bond joining them (bond model) or the entry vertex itself (site model).
--   2. **Outside exploration.** Outside reachability from $o\notin C$ uses only adjacencies between vertices outside $C$, starting from an open vertex. The entrants are the exterior vertices reached in this way, and their entry bits form a finite set.
--   3. **Blocking.** The exploration from $o$ is blocked if all entry bits of its entrants are closed:
--   $$
--   \omega_e=0\quad\text{for every entry bit }e .
--   $$
--   The outside bits are the bonds with both endpoints outside $C$, or the vertices outside $C$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/EntryLayers.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/EntryLayers.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CriticalZ3 mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open Classical

noncomputable def neighborBond (x y : Vertex) : Bond :=
  if h : NearestNeighbor x y then (LatticeGraph.neighbor_incidence h).choose else (x,0)

namespace Box

def Exterior (C : Box) (y : Vertex) : Prop :=
  ¬C.Contains y ∧ ∃ z, C.Contains z ∧ NearestNeighbor y z

noncomputable def entry (C : Box) (y : Vertex) : Vertex :=
  if h : C.Exterior y then h.2.choose else C.lower

noncomputable def entryBit (C : Box) : (m : Model) → Vertex → m.Bit
  | .bond,y => neighborBond y (C.entry y)
  | .site,y => C.entry y

end Box

namespace LatticeGraph
variable (G : LatticeGraph)

def OutsideAdj (m : Model) (C : Box) (ω : m.Config) (x y : G.Node) : Prop :=
  ¬C.Contains x.1 ∧ ¬C.Contains y.1 ∧ G.Adj m ω x y

def OutsideReach (m : Model) (C : Box) (ω : m.Config) (o y : G.Node) : Prop :=
  ¬C.Contains o.1 ∧ G.Open m ω o ∧ Relation.ReflTransGen (G.OutsideAdj m C ω) o y

noncomputable def entrants (m : Model) (C : Box) (ω : m.Config) (o : G.Node) : Finset Vertex :=
  G.vertices.filter (fun y => ∃ hy : y ∈ G.vertices,
    C.Exterior y ∧ G.OutsideReach m C ω o ⟨y,hy⟩)

@[simp] theorem mem_entrants (m : Model) (C : Box) (ω : m.Config) (o y : G.Node) :
    y.1 ∈ G.entrants m C ω o ↔ C.Exterior y.1 ∧ G.OutsideReach m C ω o y := by
  simp only [entrants,Finset.mem_filter,y.2,true_and]
  exact ⟨fun ⟨_,h⟩ => h,fun h => ⟨trivial,h⟩⟩

noncomputable def entryBits (m : Model) (C : Box) (ω : m.Config) (o : G.Node) : Finset m.Bit :=
  (G.entrants m C ω o).image (C.entryBit m)

def Blocked (m : Model) (C : Box) (ω : m.Config) (o : G.Node) : Prop :=
  ∀ e ∈ G.entryBits m C ω o, ω e = false

end LatticeGraph
end CriticalZ3

namespace CriticalZ3.LatticeGraph
open Classical
variable (G : LatticeGraph)

noncomputable def outsideBits : (m : Model) → Box → Finset m.Bit
  | .bond,C => G.edges.filter (fun e => ¬C.Contains e.1 ∧ ¬C.Contains (step e.1 e.2))
  | .site,C => G.vertices.filter (fun x => ¬C.Contains x)

end CriticalZ3.LatticeGraph

end OAI


