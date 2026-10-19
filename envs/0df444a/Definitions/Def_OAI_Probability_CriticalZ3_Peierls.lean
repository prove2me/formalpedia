-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_Peierls
-- name    : OAI_Probability_CriticalZ3_Peierls
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:28:13.844231+00:00
-- url     : https://prove2.me/theorems/686cf799-bbaa-4684-9f7d-5250971dbb2a
-- title:
--   Blocked contour events
-- statement:
--   For bad events $\mathrm{Bad}(v)$ attached to planar cells $v\in\mathbb Z^2$ and a contour code $c$ of length $n$, the code is blocked at $\omega$ if every traced side has a bad inner or outer cell:
--   $$
--   \forall i<n:\quad\omega\in\mathrm{Bad}(\mathrm{inner}_i)\ \text{or}\ \omega\in\mathrm{Bad}(\mathrm{outer}_i).
--   $$
--
--   Only valid codes, those arising from actual boundaries of finite sets, are used as Peierls candidates.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Peierls.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Peierls.lean by skeleton subtraction
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

namespace OAI

universe uOmega

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

open Filter Topology

namespace PlanarBoundary
-- [generator] trimmed: open Classical _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open Classical _root_.MeasureTheory ProbabilityTheory
variable {Ω : Type uOmega} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

def blocked {n : ℕ} (Bad : Point → Set Ω) (c : Code n) : Set Ω :=
  {ω | ∀ i, ω ∈ Bad (inner c i) ∨ ω ∈ Bad (outer c i)}

/-- Codes arising from actual boundaries are the only candidates needed. -/
def candidate {n : ℕ} (Bad : Point → Set Ω) (c : {c : Code n // Valid c}) : Set Ω :=
  blocked Bad c.val

end PlanarBoundary

end OAI


