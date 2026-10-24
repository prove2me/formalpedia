-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Comparison
-- name    : KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Comparison
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:45:28.726962+00:00
-- url     : https://prove2.me/theorems/e8a80296-e5fc-4399-b83c-f3ad33005ef5
-- title:
--   Comparison tools for ambient and intrinsic smooth gradients
-- statement:
--   `SmoothGradient.norm_gradient_comp_le` states that composition with a smooth $1$-Lipschitz map cannot increase the pointwise gradient norm. `SmoothGradient.pullbackTest` pulls a smooth-gradient test along a measure-preserving smooth $1$-Lipschitz map and preserves its $L^2$ and gradient-square integrability conditions. `SmoothGradient.projectionCoordinates` assigns to an ambient point its orthogonal projection onto the direction space of the affine support, after subtracting a support point. These are auxiliary comparison constructions and do not by themselves assert equality of relaxed energies.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/SmoothGradient/Intrinsic/Comparison.lean#L37-L120 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Comparison`, definition bundle `KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Comparison`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

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


