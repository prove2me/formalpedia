-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_Exploration
-- name    : OAI_Probability_CriticalZ3_Exploration
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:35:15.229348+00:00
-- url     : https://prove2.me/theorems/51dccac8-1bec-4a75-9d73-5edf36ab699c
-- title:
--   The coarse exploration process for critical percolation
-- statement:
--   An adaptive exploration of coarse blocks $Q_r(v)$, $v\in\mathbb Z^2$, for a percolation model at scale $r$.
--
--   1. **Packets.** A packet stores a cell, its parent cell, and a finite lattice graph containing $Q_r(v)$ and the origin, namely the chain of blocks leading to it. Its event says that the origin is connected inside this graph to the inner cube $B_r(v)$. A child packet extends the graph to a neighbouring block.
--   2. **States.** An exploration state has a revealed history, processed cells, a queue of packets, and good and bad cells.
--   3. **One step.** The first packet in the queue reveals its block bits not yet known. The packet is accepted if its event holds and every unvisited neighbour's packet event has conditional probability greater than $1-\delta$:
--   $$
--   \mathbb P_q(\text{child event}\mid\text{revealed})>1-\delta .
--   $$
--   Accepted cells become good and their candidates join the queue; otherwise the cell becomes bad. This defines an adaptive revealing scheme.
--   4. **Validity.** Valid states keep the root processed, queue cells distinct, unprocessed and with processed parents, known bits within the exposed blocks, packet graphs supported on known bits plus their block, and every queued event of conditional probability greater than $1-\delta$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Exploration.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Exploration.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse

/-- A packet stores exactly the finite parent-chain graph, extended only on assignment. -/
structure Packet (r : ℕ) where
  vertex : Point
  parent : Point
  graph : LatticeGraph
  contains : graph.ContainsBox (Q r vertex)
  root_mem : (0:Vertex) ∈ graph.vertices

namespace Packet
variable {r : ℕ}
def event (t : Packet r) (m : Model) : Set m.Config :=
  {ω | t.graph.Meets m ω ⟨0,t.root_mem⟩ {y | (B r t.vertex).Contains y}}

noncomputable def child (t : Packet r) (x : Point) : Packet r where
  vertex := x
  parent := t.vertex
  graph := extendGraph r t.graph t.vertex x t.contains
  contains := extendGraph_contains r t.graph t.vertex x t.contains
  root_mem := (extendGraph_subgraph r t.graph t.vertex x t.contains).1 t.root_mem

end Packet

structure Exploration (m : Model) (r : ℕ) where
  history : History m.Bit
  processed : Finset Point
  queue : List (Packet r)
  good : Finset Point
  bad : Finset Point

namespace Exploration
variable {m : Model} {r : ℕ}
noncomputable def visited (s : Exploration m r) : Finset Point :=
  s.processed ∪ (s.queue.map Packet.vertex).toFinset
noncomputable def reveal (s : Exploration m r) : Finset m.Bit :=
  match s.queue with
  | [] => ∅
  | t::_ => block m r t.vertex t.parent \ s.history.known
noncomputable def after (s : Exploration m r) (ω : m.Config) : History m.Bit :=
  s.history.observe s.reveal ω
noncomputable def candidates (s : Exploration m r) (t : Packet r) : List (Packet r) :=
  (List.ofFn (fun d : Direction => t.child (t.vertex+outward d))).filter
    (fun u => u.vertex ∉ s.visited)
noncomputable def Accept (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ)
    (t : Packet r) (ω : m.Config) : Prop :=
  (s.after ω).values ∈ t.event m ∧ ∀ u ∈ s.candidates t,
    1-δ < (ProductCylinder.law ((s.after ω).parameter q)).real (u.event m)
noncomputable def markedBad (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ)
    (ω : m.Config) : Bool :=
  match s.queue with
  | [] => false
  | t::_ => decide (¬s.Accept q δ t ω)
noncomputable def advance (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ)
    (ω : m.Config) : Exploration m r where
  history := s.after ω
  processed := match s.queue with | [] => s.processed | t::_ => insert t.vertex s.processed
  queue := match s.queue with
    | [] => []
    | t::ts => ts ++ if s.Accept q δ t ω then s.candidates t else []
  good := match s.queue with
    | [] => s.good
    | t::_ => if s.Accept q δ t ω then insert t.vertex s.good else s.good
  bad := match s.queue with
    | [] => s.bad
    | t::_ => if s.Accept q δ t ω then s.bad else insert t.vertex s.bad

noncomputable def scheme (q : Set.Icc (0:ℝ) 1) (δ : ℝ) :
    AdaptiveReveals.Scheme m.Bit Point (Exploration m r) where
  reveal := reveal
  parameter := fun s => s.history.parameter q
  vertex := fun s => (s.queue.head?).map Packet.vertex
  bad := fun s a => s.markedBad q δ (ProductCylinder.extend s.reveal a)
  child := fun s a => s.advance q δ (ProductCylinder.extend s.reveal a)
  parameter_child := fun s _a => s.history.parameter_observe q s.reveal _

structure Valid (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) : Prop where
  root_processed : 0 ∈ s.processed
  distinct : (s.queue.map Packet.vertex).Nodup
  unprocessed : ∀ t ∈ s.queue, t.vertex ∉ s.processed
  parents : ∀ t ∈ s.queue, t.parent ∈ s.processed
  exposed : s.history.known ⊆ Coarse.exposed m r s.processed
  support : ∀ t ∈ s.queue, t.graph.bits m ⊆ s.history.known ∪ block m r t.vertex t.parent
  promise : ∀ t ∈ s.queue, 1-δ < (ProductCylinder.law (s.history.parameter q)).real (t.event m)
end Exploration
end Coarse
end CriticalZ3

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse

namespace Exploration
variable {m : Model} {r : ℕ}

@[simp] theorem mem_candidates (s : Exploration m r) (t u : Packet r) :
    u ∈ s.candidates t ↔ (∃ d : Direction, t.child (t.vertex+outward d) = u) ∧ u.vertex ∉ s.visited := by
  simp only [candidates,List.mem_filter,List.mem_ofFn,decide_eq_true_eq]

end Exploration
end Coarse
end CriticalZ3

end OAI


