-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Comparison
-- name    : KLSModular_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Comparison
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:31:04.387614+00:00
-- url     : https://prove2.me/theorems/c8ed0dde-2117-488a-be18-6aa1ac07ea16
-- title:
--   Comparison tools for ambient and intrinsic smooth gradients
-- statement:
--   `SmoothGradient.norm_gradient_comp_le` states that composition with a smooth $1$-Lipschitz map cannot increase the pointwise gradient norm. `SmoothGradient.pullbackTest` pulls a smooth-gradient test along a measure-preserving smooth $1$-Lipschitz map and preserves its $L^2$ and gradient-square integrability conditions. `SmoothGradient.projectionCoordinates` assigns to an ambient point its orthogonal projection onto the direction space of the affine support, after subtracting a support point. These are auxiliary comparison constructions and do not by themselves assert equality of relaxed energies.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Basic
--   import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
--   import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   private def pullbackTest
--       {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
--       [MeasurableSpace X] [BorelSpace X]
--       [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y] [MeasurableSpace Y]
--       {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y} (f : Test ν)
--       (φ : X → Y) (hφ : ContDiff ℝ ∞ φ) (hlip : LipschitzWith 1 φ)
--       (hmp : MeasurePreserving φ (μ : Measure X) (ν : Measure Y)) : Test μ
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Energy/SmoothGradient/Intrinsic/Basic`](https://prove2.me/theorems/fd3da48f-6efa-4121-8307-74c1c05a7d2e).
--
--   Theorems in source order:
--
--   - [`exists_ambient_extension`](https://prove2.me/theorems/eca5f601-3244-4c7a-abb0-b647df83122f)
--   - [`relaxation_eq_intrinsic_energy`](https://prove2.me/theorems/173a210b-c07a-4836-9df1-d0ac82ab944a)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/SmoothGradient/Intrinsic/Comparison.lean) · `FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Comparison` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/SmoothGradient/Intrinsic/Comparison.lean#L37-L120 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Comparison`, definition bundle `KLSModular_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Comparison`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff
namespace FunctionalInequalities
namespace Energy
namespace SmoothGradient
open Euclidean
universe u
 theorem norm_gradient_comp_le
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    {f : Y → ℝ} {φ : X → Y} (hf : ContDiff ℝ ∞ f) (hφ : ContDiff ℝ ∞ φ)
    (hlip : LipschitzWith 1 φ) (x : X) :
    ‖gradient (f ∘ φ) x‖ ≤ ‖gradient f (φ x)‖ := by
  have hnorm : ‖fderiv ℝ φ x‖ ≤ 1 := norm_fderiv_le_of_lipschitz ℝ hlip
  calc
    ‖gradient (f ∘ φ) x‖ = ‖fderiv ℝ (f ∘ φ) x‖ := by
      rw [← toDual_gradient]
      exact ((toDual ℝ X).norm_map _).symm
    _ ≤ ‖fderiv ℝ f (φ x)‖ := by
      rw [fderiv_comp x (hf.differentiable (by simp) _) (hφ.differentiable (by simp) _)]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (by simpa using mul_le_mul_of_nonneg_left hnorm (norm_nonneg (fderiv ℝ f (φ x))))
    _ = ‖gradient f (φ x)‖ := by
      rw [← toDual_gradient]
      exact (toDual ℝ Y).norm_map _
 def pullbackTest
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y] [MeasurableSpace Y]
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y} (f : Test ν)
    (φ : X → Y) (hφ : ContDiff ℝ ∞ φ) (hlip : LipschitzWith 1 φ)
    (hmp : MeasurePreserving φ (μ : Measure X) (ν : Measure Y)) : Test μ where
  toFun := f ∘ φ
  contDiff := f.contDiff.comp hφ
  memLp_two := f.memLp_two.comp_measurePreserving hmp
  gradient_sq_integrable := by
    apply (hmp.integrable_comp_of_integrable f.gradient_sq_integrable).mono'
    · have hc : Continuous (gradient (f ∘ φ)) :=
        (toDual ℝ X).symm.continuous.comp
          ((f.contDiff.comp hφ).continuous_fderiv (by simp))
      exact (hc.norm.pow 2).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (FunctionalInequalities.Energy.SmoothGradient.norm_gradient_comp_le f.contDiff hφ hlip x) 2
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  (μ : ProbabilityMeasure E)
 def projectionCoordinates (x : E) : (Probability.affineSupport μ).direction :=
  (Probability.affineSupport μ).direction.orthogonalProjectionOnto
    (x - Probability.supportPoint μ)
end SmoothGradient
end Energy
end FunctionalInequalities


