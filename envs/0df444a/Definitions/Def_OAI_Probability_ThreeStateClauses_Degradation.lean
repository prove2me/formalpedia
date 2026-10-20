-- Prove2me | Definitions.Def_OAI_Probability_ThreeStateClauses_Degradation
-- name    : OAI_Probability_ThreeStateClauses_Degradation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T19:43:26.632443+00:00
-- url     : https://prove2.me/theorems/51c0a7c1-79cc-4ebc-993f-1eef40406788
-- title:
--   Joint law of an observation and its randomized degradation
-- statement:
--   Let $p$ be a discrete probability distribution on a type $\alpha$, and $K$ a Markov kernel assigning to each $a\in\alpha$ a discrete probability distribution $K(a)$ on $\beta$. The joint law of $(a,b)$, where $a\sim p$ and then $b\sim K(a)$, has mass
--   $$
--   P(a,b)=p(a)\,K(a)(b)\qquad(a\in\alpha,\ b\in\beta).
--   $$
--
--   The second coordinate is a degraded (further randomized) version of the first. Comparing posteriors computed from $a$ and from $b$ under this joint law shows that processing an observation cannot increase information about the spin.
--
--   **Formalization Note** `kernelJoint p K` is defined as `p.bind (fun a ↦ (K a).map (fun b ↦ (a,b)))`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/Degradation.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/Degradation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThreeStateTreeClauses mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThreeStateTreeClauses
import Definitions.Def_OAI_Probability_ThreeStateClauses_RadialAlgebra
import Definitions.Def_OAI_Probability_ThreeStateClauses_PosteriorLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_DiscreteLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_Products

namespace OAI

/-! Degradation. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

variable {α β : Type*}

def kernelJoint (p : PMF α) (K : α → PMF β) : PMF (α × β) :=
  p.bind (fun a ↦ (K a).map (fun b ↦ (a,b)))

section Measures
variable [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]

end Measures
end ThreeState.TreeClauses.Experiment

end

end OAI


