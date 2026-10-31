-- Prove2me | Definitions.Def_OAIQ024S010
-- name    : OAIQ024S010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T21:21:53.034685+00:00
-- url     : https://prove2.me/theorems/defe37e9-2a0a-4234-a8c8-6a9af46f0c66
-- title:
--   Definitions bundle OAIQ024S010 of the split of OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 11 definitions and 1 instance. The definitions and types are `OAI.SKRatio.Certificate.Data.J4K0.blocks`, `OAI.SKRatio.Certificate.Data.J4K1.blocks`, `OAI.SKRatio.Certificate.Data.J4K10.blocks`, `OAI.SKRatio.Certificate.Data.J4K2.expression`, `OAI.SKRatio.Scalar.coherent`, `OAI.SKRatio.Scalar.endpointD`, `OAI.SKRatio.Scalar.endpointDPrime`, `OAI.SKRatio.Scalar.endpointK`, `OAI.SKRatio.Scalar.q`, `OAI.SKRatio.Scalar.radicand`, `OAI.SKRatioClock.Regression.regressionCLM`.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: [`SKRatio_Certificates_ScalarDataJ4K0`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K0.lean), [`SKRatio_Certificates_ScalarDataJ4K1`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K1.lean), [`SKRatio_Certificates_ScalarDataJ4K10`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K10.lean), [`SKRatio_Certificates_ScalarDataJ4K2`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K2.lean), [`SKRatio_FiniteChain_Spin`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/FiniteChain/Spin.lean), [`SKRatio_Matrices_GOERegression`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Matrices/GOERegression.lean), [`SKRatio_Variational_ScalarEnvelope`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Variational/ScalarEnvelope.lean), [`SKRatio_Variational_ScalarKernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Variational/ScalarKernel.lean), [`SKRatio_Variational_ScalarReduction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Variational/ScalarReduction.lean).
--
--   **Imports.** It imports the published bundle `Def_SKRatio`; the bundles `OAIQ024S000` and `OAIQ024S001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ024S016`; the statements `OAI.SKRatio.Certificate.endpointD_prime_lower`, `OAI.SKRatio.Certificate.endpointD_prime_upper`, `OAI.SKRatio.Certificate.endpointK_one_bound` and `OAI.SKRatio.Certificate.endpointK_zero_bound`; the proofs of `OAI.SKRatio.Bins.random_binForm_tail` and `OAI.SKRatio.Planted.augmented_norm_rare`.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_SKRatio
import Definitions.Def_OAIQ024S000
import Definitions.Def_OAIQ024S001

section
-- module Solutions.OAIQ024_SK.SKRatio_FiniteChain_Spin
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter

namespace SKRatio

section ElementaryGibbs
variable {n : ℕ}

instance disorderLaw_probability (β : ℝ) (n : ℕ) : IsProbabilityMeasure (disorderLaw β n) := by
  unfold disorderLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end ElementaryGibbs

end SKRatio
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

def q (h : ℝ) : ℝ := (w h - 3/4) / (w h + 3/4)
end SKRatio.Scalar

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarReduction
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

section Probability
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

variable {μ}

def radicand (μ : Measure ℝ) (b r : ℝ → ℝ) (h : ℝ) : ℝ :=
  (∫ t, ((v h+v t)*r t)^2 ∂μ) +
    (∫ t, ((v h+v t)*b t - (∫ s, (v h+v s)*b s ∂μ))^2 ∂μ)

end Probability

def coherent (β : ℝ) (b : ℝ → ℝ) : ℝ :=
  (∫ h, b h*h ∂fieldLaw β)*(∫ h, b h*v h ∂fieldLaw β) +
  (∫ h, b h ∂fieldLaw β)*(∫ h, b h*((h-β^2+2*β^2*m h)*v h) ∂fieldLaw β) +
  β^2*(∫ z : ℝ×ℝ, b z.1*kernel z.1 z.2*b z.2 ∂(fieldLaw β).prod (fieldLaw β)) -
  β^2/(4*(∫ h, multiplier h ∂fieldLaw β))*
    ((∫ h, b h*v h ∂fieldLaw β)+(∫ h, v h ∂fieldLaw β)*(∫ h, b h ∂fieldLaw β))^2

end SKRatio.Scalar

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K0

def blocks : ℕ → Box
  | 0 => ⟨-1/1000000,1/1000000⟩
  | 1 => ⟨-1/1000000,1/1000000⟩
  | 2 => ⟨-1/1000000,1/1000000⟩
  | 3 => ⟨-1/1000000,1/1000000⟩
  | 4 => ⟨-1/1000000,1/1000000⟩
  | 5 => ⟨-1/1000000,1/1000000⟩
  | 6 => ⟨-1/1000000,1/1000000⟩
  | 7 => ⟨-1/1000000,1/1000000⟩
  | 8 => ⟨-1/1000000,1/1000000⟩
  | 9 => ⟨-1/1000000,1/1000000⟩
  | 10 => ⟨0,1/1000000⟩
  | 11 => ⟨3/500000,1/125000⟩
  | 12 => ⟨77/1000000,41/500000⟩
  | 13 => ⟨67/100000,693/1000000⟩
  | 14 => ⟨4403/1000000,4503/1000000⟩
  | 15 => ⟨5403/250000,21923/1000000⟩
  | 16 => ⟨19471/250000,78473/1000000⟩
  | 17 => ⟨100889/500000,202261/1000000⟩
  | 18 => ⟨23017/62500,14753/40000⟩
  | 19 => ⟨117183/250000,234963/500000⟩
  | 20 => ⟨83387/200000,417801/1000000⟩
  | 21 => ⟨32761/125000,131267/500000⟩
  | 22 => ⟨118399/1000000,2383/20000⟩
  | 23 => ⟨39281/1000000,39849/1000000⟩
  | 24 => ⟨9741/1000000,2503/250000⟩
  | 25 => ⟨1827/1000000,1921/1000000⟩
  | 26 => ⟨13/50000,143/500000⟩
  | 27 => ⟨7/250000,17/500000⟩
  | 28 => ⟨1/500000,1/250000⟩
  | 29 => ⟨-1/1000000,1/1000000⟩
  | 30 => ⟨-1/1000000,1/1000000⟩
  | 31 => ⟨-1/1000000,1/1000000⟩
  | 32 => ⟨-1/1000000,1/1000000⟩
  | 33 => ⟨-1/1000000,1/1000000⟩
  | 34 => ⟨-1/1000000,1/1000000⟩
  | 35 => ⟨-1/1000000,1/1000000⟩
  | 36 => ⟨-1/1000000,1/1000000⟩
  | 37 => ⟨-1/1000000,1/1000000⟩
  | 38 => ⟨-1/1000000,1/1000000⟩
  | 39 => ⟨-1/1000000,1/1000000⟩
  | _ => Box.rat 0

end SKRatio.Certificate.Data.J4K0

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K1

def blocks : ℕ → Box
  | 0 => ⟨-1/1000000,1/1000000⟩
  | 1 => ⟨-1/1000000,1/1000000⟩
  | 2 => ⟨-1/1000000,1/1000000⟩
  | 3 => ⟨-1/1000000,1/1000000⟩
  | 4 => ⟨-1/1000000,1/1000000⟩
  | 5 => ⟨-1/1000000,1/1000000⟩
  | 6 => ⟨-1/1000000,1/1000000⟩
  | 7 => ⟨-1/1000000,1/1000000⟩
  | 8 => ⟨-1/1000000,1/1000000⟩
  | 9 => ⟨-1/1000000,1/1000000⟩
  | 10 => ⟨-1/1000000,1/1000000⟩
  | 11 => ⟨1/500000,3/1000000⟩
  | 12 => ⟨7/250000,31/1000000⟩
  | 13 => ⟨51/200000,53/200000⟩
  | 14 => ⟨1729/1000000,1771/1000000⟩
  | 15 => ⟨2217/250000,901/100000⟩
  | 16 => ⟨34073/1000000,8597/250000⟩
  | 17 => ⟨96503/1000000,48441/500000⟩
  | 18 => ⟨39577/200000,198111/1000000⟩
  | 19 => ⟨28907/100000,1159/4000⟩
  | 20 => ⟨298503/1000000,149679/500000⟩
  | 21 => ⟨217367/1000000,108949/500000⟩
  | 22 => ⟨27989/250000,56327/500000⟩
  | 23 => ⟨10317/250000,10479/250000⟩
  | 24 => ⟨5533/500000,5707/500000⟩
  | 25 => ⟨2189/1000000,2321/1000000⟩
  | 26 => ⟨161/500000,9/25000⟩
  | 27 => ⟨7/200000,11/250000⟩
  | 28 => ⟨1/500000,1/200000⟩
  | 29 => ⟨-1/1000000,1/1000000⟩
  | 30 => ⟨-1/1000000,1/1000000⟩
  | 31 => ⟨-1/1000000,1/1000000⟩
  | 32 => ⟨-1/1000000,1/1000000⟩
  | 33 => ⟨-1/1000000,1/1000000⟩
  | 34 => ⟨-1/1000000,1/1000000⟩
  | 35 => ⟨-1/1000000,1/1000000⟩
  | 36 => ⟨-1/1000000,1/1000000⟩
  | 37 => ⟨-1/1000000,1/1000000⟩
  | 38 => ⟨-1/1000000,1/1000000⟩
  | 39 => ⟨-1/1000000,1/1000000⟩
  | _ => Box.rat 0

end SKRatio.Certificate.Data.J4K1

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K10

def blocks : ℕ → Box
  | 0 => ⟨-1/1000000,1/1000000⟩
  | 1 => ⟨-1/1000000,1/1000000⟩
  | 2 => ⟨-1/1000000,1/1000000⟩
  | 3 => ⟨-1/1000000,1/1000000⟩
  | 4 => ⟨-1/1000000,1/1000000⟩
  | 5 => ⟨-1/1000000,1/1000000⟩
  | 6 => ⟨-1/1000000,1/1000000⟩
  | 7 => ⟨-1/1000000,1/1000000⟩
  | 8 => ⟨-1/1000000,1/1000000⟩
  | 9 => ⟨-1/1000000,1/1000000⟩
  | 10 => ⟨-1/1000000,1/1000000⟩
  | 11 => ⟨-1/1000000,1/1000000⟩
  | 12 => ⟨0,1/500000⟩
  | 13 => ⟨7/500000,3/200000⟩
  | 14 => ⟨9/62500,147/1000000⟩
  | 15 => ⟨1061/1000000,267/250000⟩
  | 16 => ⟨5461/1000000,137/25000⟩
  | 17 => ⟨2371/125000,18993/1000000⟩
  | 18 => ⟨2143/50000,42877/1000000⟩
  | 19 => ⟨61359/1000000,6141/100000⟩
  | 20 => ⟨3451/62500,55257/1000000⟩
  | 21 => ⟨6311/200000,31581/1000000⟩
  | 22 => ⟨2937/250000,11783/1000000⟩
  | 23 => ⟨369/125000,743/250000⟩
  | 24 => ⟨259/500000,263/500000⟩
  | 25 => ⟨13/200000,17/250000⟩
  | 26 => ⟨1/200000,7/1000000⟩
  | 27 => ⟨0,1/1000000⟩
  | 28 => ⟨-1/1000000,1/1000000⟩
  | 29 => ⟨-1/1000000,1/1000000⟩
  | 30 => ⟨-1/1000000,1/1000000⟩
  | 31 => ⟨-1/1000000,1/1000000⟩
  | 32 => ⟨-1/1000000,1/1000000⟩
  | 33 => ⟨-1/1000000,1/1000000⟩
  | 34 => ⟨-1/1000000,1/1000000⟩
  | 35 => ⟨-1/1000000,1/1000000⟩
  | 36 => ⟨-1/1000000,1/1000000⟩
  | 37 => ⟨-1/1000000,1/1000000⟩
  | 38 => ⟨-1/1000000,1/1000000⟩
  | 39 => ⟨-1/1000000,1/1000000⟩
  | _ => Box.rat 0

end SKRatio.Certificate.Data.J4K10

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K2

def expression : Expr := integrandExpr (1/2) (397973/500000) (524071/1000000) (119553/1000000) (702377/1000000) 2

end SKRatio.Certificate.Data.J4K2

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_GOERegression
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix Matrix.Norms.Elementwise

namespace SKRatioClock.Regression

noncomputable def regressionCLM {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) :
    ((Fin n × Fin n) → ℝ) →L[ℝ]
      (((Fin n × Fin n) → ℝ) × ((Fin n × Fin r) → ℝ)) :=
  (ContinuousLinearMap.pi (fun p : Fin n × Fin n =>
    ((entryCLM p.1 p.2).comp (sandwichCLM (residualProjection U) (residualProjection U))).comp
      (goeCLM n))).prod
    (ContinuousLinearMap.pi (fun p : Fin n × Fin r =>
      ((entryCLM p.1 p.2).comp (sandwichCLM (1 : Matrix (Fin n) (Fin n) ℝ) U)).comp
        (goeCLM n)))

end SKRatioClock.Regression

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarEnvelope
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

def endpointK (y : ℝ) : ℝ :=
  (1/16)*(∫ h, (1-y^2+v h)^2/multiplier h ∂fieldLaw (1/2))
def endpointD (y : ℝ) : ℝ :=
  (1/4)*(∫ h, v h^2/(2-y-m h) ∂fieldLaw (1/2))
def endpointDPrime : ℝ :=
  (1/4)*(∫ h, v h^2/(2-m h)^2 ∂fieldLaw (1/2))

end SKRatio.Scalar

end

end OAI
end


