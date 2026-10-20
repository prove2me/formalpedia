-- Prove2me | Definitions.Def_OAI_Probability_ThreeStateClauses_CompactLimits
-- name    : OAI_Probability_ThreeStateClauses_CompactLimits
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T19:47:26.464165+00:00
-- url     : https://prove2.me/theorems/beabb223-bc38-47a3-869c-c7d924174419
-- title:
--   Total variation of a posterior message from the uniform posterior
-- statement:
--   For a message $m=(m_0,m_1,m_2)$ (with $m_i\ge0$ and average $1$), define
--   $$
--   \mathrm{tv}(m)=\frac12\cdot\frac{|m_0-1|+|m_1-1|+|m_2-1|}{3}.
--   $$
--   Since the posterior is $m/3$, this equals $\frac12\sum_i\bigl|\frac{m_i}{3}-\frac13\bigr|$. It is the total variation distance between the posterior encoded by $m$ and the uniform distribution on three spins.
--
--   Integrating $\mathrm{tv}$ against the law of the posterior message gives the reconstruction advantage of an experiment. Being a bounded continuous function on the compact message set, it passes to limits of message laws.
--
--   **Formalization Note** The definition is `tvMessage m := avg (fun i ↦ |m.1 i - 1|) / 2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/CompactLimits.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/CompactLimits.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThreeStateTreeClauses mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThreeStateTreeClauses
import Definitions.Def_OAI_Probability_ThreeStateClauses_RadialAlgebra
import Definitions.Def_OAI_Probability_ThreeStateClauses_PosteriorLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_DiscreteLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_Products
import Definitions.Def_OAI_Probability_ThreeStateClauses_Degradation
import Definitions.Def_OAI_Probability_ThreeStateClauses_RegularLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_BranchMoments

namespace OAI

/-! Compact Limits. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

section Discrete
variable {α β : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]

end Discrete
end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Tree
-- [generator] trimmed: open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Radial

end ThreeState.TreeClauses.Tree

end 

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

section Limits
-- [generator] dropped: variable {ι : Type*} {F : Filter ι} [F.NeBot] {Q : ι → Law} {P : ProbabilityMeasure Message}

end Limits

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

def tvMessage (m : Message) : ℝ := avg (fun i ↦ |m.1 i-1|)/2

end ThreeState.TreeClauses.Experiment

end

end OAI


