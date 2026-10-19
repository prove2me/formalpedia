-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_ExplorationConnectivity
-- name    : OAI_Probability_CriticalZ3_ExplorationConnectivity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:40:00.224406+00:00
-- url     : https://prove2.me/theorems/fa03188a-46e1-4283-b603-11c0a25026ff
-- title:
--   The initial state of the coarse exploration
-- statement:
--   The starting configuration of the coarse exploration at scale $r$.
--
--   1. **Facing faces.** For a direction $d$ in the plane, the facing face is the quarter-face index whose normal is the coordinate of $d$ and whose signs point along $d$.
--   2. **Root packet.** The root packet sits at cell $0$ with the graph of the block $Q_r(0)$, which contains the origin.
--   3. **Initial state.** Initially the root bits are known and open, cell $0$ is processed and good, there are no bad cells, and the queue consists of the four children of the root packet:
--   $$
--   \mathrm{queue}=\bigl(\mathrm{child}(\mathrm{root},\ \mathrm{outward}(d))\bigr)_{d=0,1,2,3}.
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/ExplorationConnectivity.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/ExplorationConnectivity.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails
import Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary
import Definitions.Def_OAI_Probability_CriticalZ3_Matching
import Definitions.Def_OAI_Probability_CriticalZ3_Peierls
import Definitions.Def_OAI_Probability_CriticalZ3_Coarse
import Definitions.Def_OAI_Probability_CriticalZ3_AdaptiveReveals
import Definitions.Def_OAI_Probability_CriticalZ3_Exploration
import Definitions.Def_OAI_Probability_CriticalZ3_ExplorationInvariant

namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace LatticeGraph

end LatticeGraph

namespace Coarse

def facingFace (d : Direction) : FaceIndex :=
  (if d = 0 ∨ d = 2 then 1 else 0,fun _ => decide (d = 0 ∨ d = 3))

noncomputable def rootPacket (r : ℕ) : Packet r where
  vertex := 0
  parent := 0
  graph := LatticeGraph.ofBox (Q r 0)
  contains := LatticeGraph.ofBox_contains _
  root_mem := (Box.mem_vertices _ _).mpr (zero_in_Q r)

noncomputable def initial (m : Model) (r : ℕ) : Exploration m r where
  history := ⟨rootBits m r,fun _ => true⟩
  processed := {0}
  queue := List.ofFn (fun d : Direction => (rootPacket r).child (outward d))
  good := {0}
  bad := ∅

@[simp] theorem mem_initial_queue (m : Model) (r : ℕ) (t : Packet r) :
    t ∈ (initial m r).queue ↔ ∃ d : Direction, (rootPacket r).child (outward d) = t := by
  simp only [initial,List.mem_ofFn]

end Coarse
end CriticalZ3

end OAI


