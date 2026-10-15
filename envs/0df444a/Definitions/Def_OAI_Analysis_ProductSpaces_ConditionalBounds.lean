-- Prove2me | Definitions.Def_OAI_Analysis_ProductSpaces_ConditionalBounds
-- name    : OAI_Analysis_ProductSpaces_ConditionalBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:05:27.366974+00:00
-- url     : https://prove2.me/theorems/b30c4be7-ae95-4cf8-b0ee-663df72f8e38
-- title:
--   First-exit sums of conditionally independent coefficient blocks
-- statement:
--   Let $\iota$ be a finite index set, $\Omega$ a measurable space and $\nu$ a measure on $\Omega$. Given coefficient functions $B_i:\Omega\to\mathbb R$ for $i\in\iota$, the *first-exit sum* is the function on $\Omega^\iota\times\mathbb R^\iota$ defined by
--
--   $$
--   S_{\nu,B}(b,w)=\sum_{i\in\iota}\Big(B_i(b_i)\,w_i-\int_\Omega B_i\,d\nu\Big),\qquad b=(b_i)_{i\in\iota}\in\Omega^\iota,\ w=(w_i)_{i\in\iota}\in\mathbb R^\iota .
--   $$
--
--   In the application, $\Omega$ is the sample space of the tree, the blocks $b_i$ are independent samples describing the subtrees below the first-exit vertices of a finite head, and the $w_i$ are the multipliers on the exit edges themselves, independent with a law of mean one. Conditionally on the head coordinates, a tail vector of the $L^1$ product span has exactly this form; it is linear in the exit multipliers and each summand has mean zero, which is what allows a scalar estimate in the variables $w_i$ to be integrated into an estimate in $L^1$.
--
--   **Formalization Note** The Lean definition is `firstExitSum ν B z` with `z : (ι → Ω) × (ι → ℝ)`; it depends only on `ν` and `B` (the multiplier law and its moment hypothesis are section variables used by the lemmas of the file, not by the definition).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/ConditionalBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/ConditionalBounds.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the IndependentProducts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
import Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns
import Definitions.Def_OAI_Analysis_ProductSpaces_MidpointModulus

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΛ uΩ uι

namespace IndependentProducts
section ConditionalScalar
variable {ι : Type uι} {Ω : Type uΩ} [Fintype ι] [MeasurableSpace Ω]
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (ν : Measure Ω)
variable (hμ : MemLp (fun w : ℝ => w) 2 μ)

/-- A finite first-exit polynomial on conditionally independent coefficient blocks. -/
def firstExitSum (B : ι → Ω → ℝ) (z : (ι → Ω) × (ι → ℝ)) : ℝ :=
  ∑ i, (B i (z.1 i) * z.2 i - ∫ b, B i b ∂ν)

variable [IsProbabilityMeasure ν]

end ConditionalScalar

end IndependentProducts

namespace IndependentProducts
section IntegratedConditional
variable {ι : Type uι} {Ω : Type uΩ} {Λ : Type uΛ}
  [Fintype ι] [MeasurableSpace Ω] [MeasurableSpace Λ]
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
variable (η : Measure Λ) [IsProbabilityMeasure η]

end IntegratedConditional
end IndependentProducts

end

end OAI


