-- Prove2me | Definitions.Def_OAIQ036S006
-- name    : OAIQ036S006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T04:56:17.018794+00:00
-- url     : https://prove2.me/theorems/8b46bec7-ee23-455b-bcce-dd9cc9c5d40c
-- title:
--   Definitions bundle OAIQ036S006 of the split of OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 8 definitions and 1 theorem. The definitions and types are `OAI.SK.Analytic.skAdaptivePressure`, `OAI.SK.Analytic.timeChainJointHessian`, `OAI.SK.Analytic.tripleBaseQuadratic`, `OAI.SK.Analytic.tripleCDFResponse`, `OAI.SK.Analytic.tripleCDFTrialCoefficient`, `OAI.SK.Analytic.tripleQuadraticCoefficient`, `OAI.SK.Analytic.tripleSusceptibility`, `OAI.SK.Analytic.vectorBlockHierarchyAverage`.
--
--   **Sources.** They come from these modules of lean/OAI/Probability/SKBarriers, in whole or in part: [`SKBarriers_Hierarchy_TimeChainJointHessian`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Hierarchy/TimeChainJointHessian.lean), [`SKBarriers_Interpolation_SKAdaptiveDerivative`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Interpolation/SKAdaptiveDerivative.lean), [`SKBarriers_Replicas_PairBlocks`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/PairBlocks.lean), [`SKBarriers_Replicas_TripleCDFTrial`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/TripleCDFTrial.lean), [`SKBarriers_Replicas_TripleDecoupling`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/TripleDecoupling.lean), [`SKBarriers_Replicas_TripleFiniteExpansion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/TripleFiniteExpansion.lean), [`SKBarriers_Replicas_TripleQuadraticPressure`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/TripleQuadraticPressure.lean), [`SKBarriers_Scalar_VectorBlocks`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Scalar/VectorBlocks.lean).
--
--   **Imports.** It imports the bundle `OAIQ036S004` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.SK.Analytic.exists_negative_tripleCDF_coefficient`, `OAI.SK.Analytic.tripleConstrainedPressure_quadratic` and `OAI.SK.Analytic.tripleSchedule_value_expansion`; the proofs of `OAI.SK.Analytic.exists_negative_tripleCDF_coefficient`, `OAI.SK.Analytic.narrowConstrainedPressure_scaled_gap`, `OAI.SK.Analytic.pairMismatch_pressure_gap`, `OAI.SK.Analytic.quenchedPressure_quantitative_finiteInf`, `OAI.SK.Analytic.quenchedPressure_tendsto_finiteParisiInf`, `OAI.SK.Analytic.scalarCDFJointSusceptibility_quantile_loss`, `OAI.SK.Analytic.signed_small_scale`, `OAI.SK.Analytic.tripleConstrainedPressure_quadratic` and `OAI.SK.Analytic.tripleSchedule_value_expansion`.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/SKBarriers at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ036S004

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_SKAdaptiveDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def skAdaptivePressure (N k : ℕ) (β : ℝ) (q : Fin (k+1) → ℝ) (u : ℝ) : ℝ :=
  skBlockRoot N k (β*Real.sqrt (1-u))
    (fun b => β*Real.sqrt (cumulativeGapMap k q b))/(N:ℝ)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_VectorBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def vectorBlockHierarchyAverage (r : ℕ) : (n : ℕ) → (Fin n → ℝ) → (Fin n → Fin r → E) →
    (E → ℝ) → (E → ℝ) → E → ℝ
  | 0,_,_,_,g => g
  | n+1,m,v,f,g => vectorBlockHierarchyAverage r n (fun i => m i.castSucc) (fun i => v i.castSucc)
      (vectorHierarchy r (fun _ => m (Fin.last n)) (v (Fin.last n)) f)
      (vectorHierarchyAverage r (fun _ => m (Fin.last n)) (v (Fin.last n)) f g)

end

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_TimeChainJointHessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def timeChainJointHessian (β : ℝ) (l j k : List (ℝ × ℝ≥0)) : ℝ :=
  let F := scalarTimeChain β k scalarSpinTerminal
  let H := scalarTimeChain β j F
  scalarTimeChainAverage β l H (fun x => rootHessian 0 H x*
    scalarTimeChainAverage β j F (rootHessian 0 F) x) 0

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_PairBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

@[simp] theorem vectorStepAverage_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℝ) (f g : E → ℝ) : vectorStepAverage m 0 f g=g := by
  funext x
  simp only [vectorStepAverage,smul_zero,add_zero,gaussianAverage,gaussianStepLaw,tilted_const]
  simp

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleFiniteExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def tripleBaseQuadratic (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) : ℝ :=
  let f := scalarIncrementChain t scalarSpinTerminal
  scalarIncrementAverage c (scalarIncrementChain (weightedUnderlying w) f)
    (fun x => vectorIncrementAverage w (fun q : ℝ × ℝ => f q.1) (fun q => q.2^2) (x,0)*
      scalarIncrementAverage (weightedUnderlying w) f (rootHessian 0 f) x) 0

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleDecoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def tripleSusceptibility (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) : ℝ :=
  scalarIncrementAverage (c++weightedUnderlying w) (scalarIncrementChain t scalarSpinTerminal)
    (rootHessian 0 (scalarIncrementChain t scalarSpinTerminal)) 0

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleQuadraticPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def tripleQuadraticCoefficient (β V : ℝ) (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) : ℝ :=
  let χ := tripleSusceptibility (scaleIncrementChain β c) (scaleIncrementChain β w) (scaleIncrementChain β t)
  let χ₀ := rootHessian 0 (scalarIncrementChain (scaleIncrementChain β (c++weightedUnderlying w++t)) scalarSpinTerminal) 0
  β^2*weightedVariance w*(χ-rawArea t)+
    β^2*weightedCrossPenalty w 0*(β^2*χ*(χ₀+2*V+4*V^2)-1)+
    tripleCommonError (scaleIncrementChain β c) (scaleIncrementChain β w)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleCDFTrial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def tripleCDFResponse (β : ℝ) (α : ℝ → ℝ) (s q : ℝ) : ℝ :=
  β^2*scalarCDFSusceptibilityAverage β α q*
    (scalarCDFHessian β α 0 1 0+2*(β^2*s)+4*(β^2*s)^2)-1

def tripleCDFTrialCoefficient (β : ℝ) (α : ℝ → ℝ) (K r s₁ s₂ q : ℝ) : ℝ :=
  β^2*K*(scalarCDFSusceptibilityAverage β α q-(∫ x in q..1,α x))+
    β^2*(α s₁*tripleCDFResponse β α s₂ q+max (tripleCDFResponse β α s₂ q) 0)+
    tripleTimeCommonError β K r

end SK.Analytic

end
end

end OAI
end


