-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
-- name    : OAI_Probability_CriticalZ3_ShellProbability
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:12:59.470985+00:00
-- url     : https://prove2.me/theorems/c47674a7-2db5-4f80-b0cb-3bd59b373ab2
-- title:
--   Good relay vertices
-- statement:
--   In a finite lattice graph with percolation model $m$, parameters $p$, a finite set $J$ of revealed bits, a target set $T$ and a tolerance $\tau$, the good relays for a configuration $\omega$ are the vertices $v$ that connect to $T$ with high conditional probability given the revealed bits:
--   $$
--   \mathbb P_p\bigl(v\leadsto T\ \bigm|\ \omega_J\bigr)>1-\tau .
--   $$
--
--   These are the relays from which a cluster that reaches them is very likely to continue to the target.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/ShellProbability.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/ShellProbability.lean by skeleton subtraction
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

namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3.LatticeGraph
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

end CriticalZ3.LatticeGraph

namespace FiniteAssociation
open Classical
variable {E : Type}

end FiniteAssociation

namespace ProductCylinder
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type}

end ProductCylinder

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type}

end InfiniteConditioning

namespace CriticalZ3.LatticeGraph
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

noncomputable def goodRelays (p : m.Bit → Set.Icc (0 : ℝ) 1) (J : Finset m.Bit)
    (T : Set Vertex) (τ : ℝ) (ω : m.Config) : Set Vertex :=
  {v | ∃ a : G.Node, a.1 = v ∧ 1-τ < conditionalProbability p J {ω | G.Meets m ω a T} ω}

end CriticalZ3.LatticeGraph

end OAI


