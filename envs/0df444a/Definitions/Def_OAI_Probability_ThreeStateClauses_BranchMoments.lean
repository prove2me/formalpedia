-- Prove2me | Definitions.Def_OAI_Probability_ThreeStateClauses_BranchMoments
-- name    : OAI_Probability_ThreeStateClauses_BranchMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T19:46:32.575454+00:00
-- url     : https://prove2.me/theorems/4eb0681d-8b0a-4b7b-9bd9-01e12cd138b6
-- title:
--   Product weight of a tuple of points
-- statement:
--   Let $X$ be a type, $\iota$ a finite index set, and $a:X\to\mathbb{R}$ a weight function. For a tuple $x=(x_i)_{i\in\iota}\in X^\iota$, the product weight is
--   $$
--   \Pi_a(x)=\prod_{i\in\iota}a(x_i).
--   $$
--
--   In moment computations for the children of a vertex, $a$ is a likelihood weight. Integrating against $\Pi_a$ under a product measure tilts each child independently.
--
--   **Formalization Note** The definition is `weightProduct a x`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/BranchMoments.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/BranchMoments.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Branch Moments. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

variable {ι : Type*} [Fintype ι]

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace X]
  {μ : Measure X} [SigmaFinite μ] {a u : X → ℝ}

def weightProduct (a : X → ℝ) (x : ι → X) : ℝ := ∏ i, a (x i)

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

end ThreeState.TreeClauses.Experiment

end

end OAI


