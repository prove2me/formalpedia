-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
-- name    : KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T04:57:22.693563+00:00
-- url     : https://prove2.me/theorems/a0c80a0a-9ad5-408e-8ce3-a6b021813dcb
-- title:
--   Centered covariance operator
-- statement:
--   For a complete real Hilbert space $E$ with the stated measurable and Borel structures, `Covariance.operator μ` is the continuous linear operator obtained by Riesz representation of Mathlib's centered covariance bilinear form for a measure $\mu$. Its defining identity `operator_inner` is $\langle\operatorname{operator}(\mu)x,y\rangle=\operatorname{covarianceBilin}(\mu)(x,y)$; when the second moment is available, this is the centered covariance integral, while measures without the required integrability inherit Mathlib's totalized value.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Covariance/Basic.lean#L21-L40 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Covariance.Basic`, definition bundle `KLS408915f_FunctionalInequalities_Probability_Covariance_Basic`; the repository is private at upload time).

import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Probability.Moments.CovarianceBilin

noncomputable section
open MeasureTheory ProbabilityTheory
namespace FunctionalInequalities
namespace Covariance
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
/-- The centered covariance operator, obtained by Riesz representation of
`ProbabilityTheory.covarianceBilin μ` using `InnerProductSpace.continuousLinearMapOfBilin`.

For a probability measure with `MemLp id 2 μ`, write `m = ∫ x, x ∂μ`. Then
`⟪operator μ u, v⟫ = ∫ x, ⟪u, x - m⟫ * ⟪v, x - m⟫ ∂μ`.
The definition accepts every measure; if `¬ MemLp id 2 μ`, it inherits Mathlib's zero value.

In the pinned Mathlib version, `ProbabilityTheory.covarianceOperator μ` uses the uncentered
second moment. This definition is definitionally equal to
`ProbabilityTheory.covarianceOperator (μ.map (fun x => x - ∫ y, y ∂μ))`. -/
def operator (μ : Measure E) : E →L[ℝ] E :=
  InnerProductSpace.continuousLinearMapOfBilin (covarianceBilin μ)
/-- The defining Riesz identity, from `InnerProductSpace.continuousLinearMapOfBilin_apply`.
For a finite measure with `MemLp id 2 μ`, combine it with
`ProbabilityTheory.covarianceBilin_apply` to obtain the centered integral formula. -/
@[simp]
theorem operator_inner (μ : Measure E) (x y : E) :
    inner ℝ (operator μ x) y = covarianceBilin μ x y := by
  exact InnerProductSpace.continuousLinearMapOfBilin_apply (covarianceBilin μ) x y
end Covariance
end FunctionalInequalities


