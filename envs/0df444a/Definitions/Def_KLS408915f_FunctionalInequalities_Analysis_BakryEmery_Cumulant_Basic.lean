-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
-- name    : KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:28:41.949118+00:00
-- url     : https://prove2.me/theorems/3e0714ff-4f25-4f47-ab35-268caabd572a
-- title:
--   Logarithmic Laplace transform and cumulant tensors
-- statement:
--   `FunctionalInequalities.Analysis.BakryEmery.logLaplace μ z` is $\log\int \exp(\langle z,x\rangle)\,d\mu(x)$, and `cumulant μ n` is the nth iterated Fréchet derivative of this transform at zero, represented as a continuous n-linear form. For a nonzero finite measure with all exponential radial moments, `contDiff_logLaplace` asserts that the logarithmic Laplace transform is smooth. `LetwinQuadraticBound` is an explicit hypothesis requiring, for every self-adjoint continuous operator M, the variance of $\langle Mx,x\rangle$ to be at most eight times the squared Hilbert--Schmidt coordinate norm; it is defined here rather than proved.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean#L38-L366 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
namespace FunctionalInequalities
namespace Analysis
namespace BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The logarithmic Laplace transform `Λ_μ(z) = log ∫ e^{⟪z, x⟫} dμ(x)` (BKL Section 4). -/
def logLaplace (μ : Measure E) (z : E) : ℝ :=
  Real.log (∫ x, Real.exp ⟪z, x⟫ ∂μ)
/-- The cumulant tensor `κ_m^μ = ∇^m Λ_μ(0)` (BKL Section 4), as a continuous `m`-linear form. -/
def cumulant (μ : Measure E) (n : ℕ) : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ :=
  iteratedFDeriv ℝ n (logLaplace μ) 0
section LaplaceCalculus
omit [CompleteSpace E]
/-- The logarithmic Laplace transform is smooth for a nonzero finite measure with all exponential
moments. -/
theorem contDiff_logLaplace (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) :
    ContDiff ℝ ∞ (logLaplace μ) := by
    have hZ : ContDiff ℝ ∞ (fun z : E => ∫ x, Real.exp ⟪z, x⟫ ∂μ) := by
      simpa [smul_eq_mul, mul_one] using
        (contDiff_integral_exp_inner_smul μ hexp
          (g := fun _ : E => (1 : ℝ))
          (M := 1) (k := 0)
          (hg := measurable_const.aestronglyMeasurable)
          (hgb := by
            intro x
            simp))
    have hpos : ∀ z : E, 0 < ∫ x, Real.exp ⟪z, x⟫ ∂μ := by
      intro z
      have hzint : Integrable (fun x : E => Real.exp ⟪z, x⟫) μ := by
        refine (hexp ‖z‖).mono' ?_ ?_
        · exact
            (Real.continuous_exp.comp
              (continuous_const.inner continuous_id)).aestronglyMeasurable
        · filter_upwards [] with x
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_exp.mpr (real_inner_le_norm z x)
      exact integral_exp_pos hzint
    change ContDiff ℝ ∞
      (fun z : E => Real.log (∫ x, Real.exp ⟪z, x⟫ ∂μ))
    exact hZ.log (fun z => (hpos z).ne')
end LaplaceCalculus
section ThirdCumulant
/-- The quadratic-form estimate of Letwin (2026, Theorem 1.2), stated as a property of the law `μ`:
`Var_μ⟨Mx, x⟩ ≤ 8 |M|²_HS` for every self-adjoint `M`, with `|M|²_HS = ∑_{i,j} ⟪M e_i, e_j⟫²` in an
orthonormal basis. This names the hypothesis; it is not proved here. -/
def LetwinQuadraticBound (μ : Measure E) : Prop :=
  ∀ M : E →L[ℝ] E, IsSelfAdjoint M →
    ∫ x, (⟪M x, x⟫ - ∫ y, ⟪M y, y⟫ ∂μ) ^ 2 ∂μ ≤
      8 * ∑ i, ∑ j, ⟪M (stdOrthonormalBasis ℝ E i), stdOrthonormalBasis ℝ E j⟫ ^ 2
variable (μ : Measure E) [IsProbabilityMeasure μ]
  (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
end ThirdCumulant
end BakryEmery
end Analysis
end FunctionalInequalities


