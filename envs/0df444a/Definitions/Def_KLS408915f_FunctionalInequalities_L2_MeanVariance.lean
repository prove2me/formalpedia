-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
-- name    : KLS408915f_FunctionalInequalities_L2_MeanVariance
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:32:59.127272+00:00
-- url     : https://prove2.me/theorems/7bf186e1-e05c-488e-8532-4b6fa9f83948
-- title:
--   Mean, centering, and variance in real L²
-- statement:
--   `L2.const μ c` is the real $L^2(\mu)$ element represented almost everywhere by the constant c, and `L2.mean μ f` is its inner product with the constant-one element. `L2.center μ f` subtracts the constant equal to this mean, while `L2.variance μ f` is the `NNReal` value $\|f-\operatorname{mean}_\mu(f)\|_2^2$. The auxiliary declarations identify the almost-everywhere representative and scalar-multiplication behavior of constants.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/MeanVariance.lean#L23-L163 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.MeanVariance`, definition bundle `KLS408915f_FunctionalInequalities_L2_MeanVariance`; the repository is private at upload time).

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory
namespace FunctionalInequalities
namespace L2
variable {α : Type*} [MeasurableSpace α]
/-- The element of real `L²(μ)` represented almost everywhere by the constant `c`. -/
def const (μ : ProbabilityMeasure α) (c : ℝ) : Lp ℝ 2 (μ : Measure α) :=
  Lp.const 2 (μ : Measure α) c
/-- The `L²` constant has the expected pointwise representative almost everywhere. -/
theorem const_coeFn (μ : ProbabilityMeasure α) (c : ℝ) :
    const μ c =ᵐ[(μ : Measure α)] fun _ ↦ c := by
  change Lp.const 2 (μ : Measure α) c =ᵐ[(μ : Measure α)] Function.const α c
  exact Lp.coeFn_const 2 (μ : Measure α) c
/-- Embedding constants into real `L²` preserves scalar multiplication. -/
@[simp]
theorem const_smul (μ : ProbabilityMeasure α) (c d : ℝ) :
    const μ (c * d) = c • const μ d := by
  exact (Lp.constₗ 2 (μ : Measure α) ℝ).map_smul c d
/-- The mean of `f ∈ L²(μ)` is its real inner product with the constant one. -/
def mean (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) : ℝ :=
  inner ℝ f (const μ 1)
/-- Centering subtracts the constant `L²` element whose value is the mean. -/
def center (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    Lp ℝ 2 (μ : Measure α) :=
  f - const μ (mean μ f)
/-- The variance of `f ∈ L²(μ)` is the squared `L²` norm of its centered part. -/
def variance (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) : NNReal :=
  ‖center μ f‖₊ ^ 2
end L2
end FunctionalInequalities


