-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
-- name    : KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:23:56.881931+00:00
-- url     : https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598
-- title:
--   Logarithmic Laplace transform and cumulant tensors
-- statement:
--   `FunctionalInequalities.Analysis.BakryEmery.logLaplace μ z` is $\log\int \exp(\langle z,x\rangle)\,d\mu(x)$, and `cumulant μ n` is the nth iterated Fréchet derivative of this transform at zero, represented as a continuous n-linear form. For a nonzero finite measure with all exponential radial moments, `contDiff_logLaplace` asserts that the logarithmic Laplace transform is smooth. `LetwinQuadraticBound` is an explicit hypothesis requiring, for every self-adjoint continuous operator M, the variance of $\langle Mx,x\rangle$ to be at most eight times the squared Hilbert--Schmidt coordinate norm; it is defined here rather than proved.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable
--   import FunctionalInequalities.Analysis.BakryEmery.Tilt.Local
--   import Mathlib.Probability.Moments.Variance
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def logLaplace (μ : Measure E) (z : E) : ℝ :=
--     Real.log (∫ x, Real.exp ⟪z, x⟫ ∂μ)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/BakryEmery/Tilt/SquareIntegrable`](https://prove2.me/theorems/9b0acc03-d3b4-4825-a2f6-2c89b2d937d5), [`Analysis/BakryEmery/Tilt/Local`](https://prove2.me/theorems/d11ffd4f-fcf9-45c5-b131-86144d86211a).
--
--   Theorems in source order:
--
--   - [`tiltAverage_inner_eq_fderiv_logLaplace`](https://prove2.me/theorems/6e9a8c5a-1811-461e-b918-2514d0abe6ef)
--   - [`tiltAverage_inner_eq_fderiv_logLaplace_of_lt`](https://prove2.me/theorems/e5acfca7-aa88-4d8d-9c36-ad0061799915)
--   - [`taylorTensor_inner_eq_cumulant`](https://prove2.me/theorems/777bcca0-0906-41de-8616-b3ae233c3880)
--   - [`norm_coordTensor_taylorTensor_inner_sq_le_of_basis`](https://prove2.me/theorems/f6507f16-38d4-4c99-9d45-dccf8890a2d6)
--   - [`contDiffOn_logLaplace_ball`](https://prove2.me/theorems/dd1e2494-e9a9-46a2-a434-95c8dca4c3ef)
--   - [`cumulant_map_linearIsometryEquiv`](https://prove2.me/theorems/2c6f9c5b-4b75-4b42-9954-60d10b0a3552)
--   - [`cumulant_map_affine`](https://prove2.me/theorems/ff092742-6b2a-4aa9-b96d-052edb49e94b)
--   - [`letwinQuadraticBound_of_tendsto_moments`](https://prove2.me/theorems/6ecfa844-3974-41e9-92f3-a8a463c1d859)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean) · `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean#L38-L366 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic`, definition bundle `KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
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


