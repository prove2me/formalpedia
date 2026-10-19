-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_ExplorationSurvival
-- name    : OAI_Probability_CriticalZ3_ExplorationSurvival
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:41:08.090351+00:00
-- url     : https://prove2.me/theorems/a3f49ef7-66ad-4e18-9866-0b7da706fdaf
-- title:
--   Clusters and soundness of the exploration
-- statement:
--   Notions connecting the coarse exploration with actual percolation clusters in $\mathbb Z^3$.
--
--   1. **Connections and clusters.** For either model, $x$ and $y$ are connected if they are bond-connected (bond model) or site-connected (site model), and the cluster of $x$ is
--   $$
--   \mathcal C(x)=\{y:\ x\leftrightarrow y\}.
--   $$
--   2. **Soundness.** An exploration state is sound for a configuration $\omega$ if for every good cell $v$ the origin is connected to some vertex of the inner cube $B_r(v)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/ExplorationSurvival.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/ExplorationSurvival.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_CriticalZ3_ExplorationConnectivity

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace InfiniteConditioning.History
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

end InfiniteConditioning.History

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Model

def Connected : (m : Model) → m.Config → Vertex → Vertex → Prop
  | .bond,ω,x,y => BondConnected ω x y
  | .site,ω,x,y => SiteConnected ω x y

def Cluster (m : Model) (ω : m.Config) (x : Vertex) : Set Vertex :=
  {y | m.Connected ω x y}

end Model

namespace LatticeGraph

end LatticeGraph

namespace Coarse.Exploration
variable {m : Model} {r : ℕ}

def Sound (s : Exploration m r) (ω : m.Config) : Prop :=
  ∀ v ∈ s.good, ∃ y, (B r v).Contains y ∧ m.Connected ω 0 y

end Coarse.Exploration

namespace Coarse

end Coarse
end CriticalZ3

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse

end Coarse
end CriticalZ3

end OAI


