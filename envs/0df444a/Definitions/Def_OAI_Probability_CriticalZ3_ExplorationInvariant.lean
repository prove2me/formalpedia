-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_ExplorationInvariant
-- name    : OAI_Probability_CriticalZ3_ExplorationInvariant
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:39:07.209149+00:00
-- url     : https://prove2.me/theorems/f2724410-de87-4258-8b8d-ac68fac096bb
-- title:
--   Runs of the exploration and their good and bad cells
-- statement:
--   Invariants and outcomes of the coarse exploration process.
--
--   1. **Frozen events.** For a state and a packet, the frozen event evaluates the packet event after replacing the known bits by their revealed values.
--   2. **Invariants.** A state is coloured if the processed cells are exactly the good and bad cells, which are disjoint. It is closed if all four neighbours of every good cell are visited, and covered if every visited cell is good or a neighbour of a good cell.
--   3. **Runs.** Running $n$ steps applies the advance map $n$ times with the same configuration $\omega$. The good cells of a run are those good at some time, and the bad event of a cell is
--   $$
--   \mathrm{Bad}(v)=\{\omega:\ v\ \text{is declared bad at some time}\}.
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/ExplorationInvariant.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/ExplorationInvariant.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse.Exploration
variable {m : Model} {r : ℕ}

noncomputable def frozenEvent (s : Exploration m r) (t : Packet r) : Set m.Config :=
  {ω | s.history.freeze ω ∈ t.event m}

end Coarse.Exploration
end CriticalZ3

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse.Exploration
variable {m : Model} {r : ℕ}

structure Colored (s : Exploration m r) : Prop where
  partition : s.processed = s.good ∪ s.bad
  disjoint : Disjoint s.good s.bad

def Closed (s : Exploration m r) : Prop :=
  ∀ v ∈ s.good, ∀ d : Direction, v+outward d ∈ s.visited

def Covered (s : Exploration m r) : Prop :=
  ∀ v ∈ s.visited, v ∈ s.good ∨ ∃ u ∈ s.good, ∃ d : Direction, v = u+outward d

noncomputable def run (q : Set.Icc (0:ℝ) 1) (δ : ℝ) : ℕ → Exploration m r → m.Config → Exploration m r
  | 0,s,_ => s
  | n+1,s,ω => run q δ n (s.advance q δ ω) ω

@[simp] theorem run_zero (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (ω : m.Config) :
    run q δ 0 s ω = s := rfl

@[simp] theorem run_succ (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (n : ℕ) (s : Exploration m r) (ω : m.Config) :
    run q δ (n+1) s ω = run q δ n (s.advance q δ ω) ω := rfl

noncomputable def Good (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (ω : m.Config) : Set Point :=
  {v | ∃ n, v ∈ (run q δ n s ω).good}
noncomputable def Bad (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (v : Point) : Set m.Config :=
  {ω | ∃ n, v ∈ (run q δ n s ω).bad}

end Coarse.Exploration
end CriticalZ3

end OAI


