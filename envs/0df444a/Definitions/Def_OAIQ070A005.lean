-- Prove2me | Definitions.Def_OAIQ070A005
-- name    : OAIQ070A005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T11:21:09.582836+00:00
-- url     : https://prove2.me/theorems/dbda30b6-5e16-4177-9c8d-5fb58846aad2
-- title:
--   Definitions bundle OAIQ070A005 of the split of OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 109 declarations of OpenAI's Lean: 32 definitions, 5 instances and 72 theorems. The definitions and types are `OAI.YauCounterexamples.CompactMetricAtlas.error`, `OAI.YauCounterexamples.CompactMetricAtlas.errorBound`, `OAI.YauCounterexamples.CompactMetricAtlas.inclusion`, `OAI.YauCounterexamples.CompactMetricAtlas.intrinsicForm`, `OAI.YauCounterexamples.CompactMetricAtlas.intrinsicPairing`, `OAI.YauCounterexamples.CompactMetricAtlas.laplaceVariationTest`, `OAI.YauCounterexamples.CompactMetricAtlas.laplacianCLM`, `OAI.YauCounterexamples.CompactMetricAtlas.laplacianPatch`, `OAI.YauCounterexamples.CompactMetricAtlas.metricCoefficientSchwartz`, `OAI.YauCounterexamples.CompactMetricAtlas.patchError`, `OAI.YauCounterexamples.CompactMetricAtlas.patchErrorTail`, `OAI.YauCounterexamples.CompactMetricAtlas.realH`, `OAI.YauCounterexamples.CompactMetricAtlas.realRepresentative`, `OAI.YauCounterexamples.CompactMetricAtlas.realValue`, `OAI.YauCounterexamples.CompactMetricAtlas.scalarTestCLM`, `OAI.YauCounterexamples.MetricIntegralAtlas.mean`, `OAI.YauCounterexamples.coefficientPerturbation`, `OAI.YauCounterexamples.cutoffDerivativeSchwartz`, `OAI.YauCounterexamples.cutoffPullbackLinear`, `OAI.YauCounterexamples.firstOrderSobolev`, `OAI.YauCounterexamples.laplaceFamilyBCF`, `OAI.YauCounterexamples.manifoldSobolevInclusion`, `OAI.YauCounterexamples.metricPatchRawInverse`, `OAI.YauCounterexamples.metricPatchSource`, `OAI.YauCounterexamples.rescaledCommutatorSobolev`, `OAI.YauCounterexamples.schwartzSobolevProduct`, `OAI.YauCounterexamples.smoothMul`, `OAI.YauCounterexamples.sobolevAffineCutoff`, `OAI.YauCounterexamples.sobolevCutoffPullback`, `OAI.YauCounterexamples.sobolevFirstLower`, `OAI.YauCounterexamples.sobolevProduct`, `OAI.YauCounterexamples.sobolevSecondDerivative`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `SmoothYau_Estimates_MixedPiolaDivergenceAbs`, `SmoothYau_Estimates_RescaledCommutatorSobolev`, `SmoothYau_Estimates_RescaledDifferentialPerturbation`, `SmoothYau_Estimates_ScalarAffineDetNeZero`, `SmoothYau_Geometry_ContMDiffComplexMul`, `SmoothYau_Geometry_CoordinateGradientPairScalarCorrection`, `SmoothYau_Geometry_MetricPatchSource`, `SmoothYau_Smoothness_ChartDerivativeNeZeroTransfer`, `SmoothYau_Smoothness_ConstantComplexProductJetBound`, `SmoothYau_Smoothness_ContinuousSobolevFirstDerivative`, `SmoothYau_Smoothness_CutoffPullbackLinear`, `SmoothYau_Smoothness_FderivCofactorApply`, `SmoothYau_Smoothness_JointMetricDet`, `SmoothYau_Smoothness_LocalIntegrationParts`, `SmoothYau_Smoothness_MomentBesselLp`, `SmoothYau_Smoothness_PiolaIdentity`, `SmoothYau_Smoothness_SobolevRepresentativeOrderCongr`, `SmoothYau_Spectrum_AnisotropicConstant`, `SmoothYau_Spectrum_ContinuousEigenpairLinearization`, `SmoothYau_Spectrum_JointLocalLaplacian`, `SmoothYau_Spectrum_VaryingSpectralResolventBase`.
--
--   **Imports.** It imports the published bundle `Def_SmoothYau`; the bundles `OAIQ070A000`, `OAIQ070A001` and `OAIQ070A002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ070A009` and `OAIQ070A010`; the statements `OAI.YauCounterexamples.CompactMetricAtlas.actual_simple_eigenpair_persistence`, `OAI_YauCounterexamples_CompactMetricAtlas_eventually_positive_factor_of_jets`, `OAI_YauCounterexamples_CompactMetricAtlas_eventually_product_positive_factor_of_eventual_jets`, `OAI.YauCounterexamples.CompactMetricAtlas.laplaceVariationTest_eigen_zero`, `OAI_YauCounterexamples_CompactMetricAtlas_represented_weighted_quintic_smooth`, `OAI_YauCounterexamples_conductivity_metric_in_smooth_neighborhood` and `OAI_YauCounterexamples_productSphere_fstPower_trace`; the proofs of `OAI.YauCounterexamples.CompactMetricAtlas.eventually_product_scalar_exactification`, `OAI.YauCounterexamples.CompactMetricAtlas.eventually_scalar_exactification`, `OAI.YauCounterexamples.CompactMetricAtlas.global_cutoff_raw_controls`, `OAI_YauCounterexamples_CompactMetricAtlas_represented_weighted_quintic_smooth`, `OAI.YauCounterexamples.cutoff_exactification_in_smooth_neighborhood`, `OAI.YauCounterexamples.laplaceBeltrami_any_basis_univ`, `OAI_YauCounterexamples_productSphere_fstPower_trace`, `OAI.YauCounterexamples.roundPower_global_profile_residual_rapid_decay` and `OAI.YauCounterexamples.three_rank_separating_tensor`.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 1581d4c

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A000
import Definitions.Def_OAIQ070A001
import Definitions.Def_OAIQ070A002

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_FderivCofactorApply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma fderiv_matrix_inv_apply {A : E → Matrix ι ι ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hx : IsUnit (A x).det) (v : E) :
    fderiv ℝ (fun y => (A y)⁻¹) x v =
      -(A x)⁻¹ * (fderiv ℝ A x v) * (A x)⁻¹ := by
  have hB := differentiableAt_matrix_inv hA hx
  have hAn (i j : ι) := (differentiableAt_pi.mp (differentiableAt_pi.mp hA i)) j
  have hBn (i j : ι) := (differentiableAt_pi.mp (differentiableAt_pi.mp hB i)) j
  have hev : ∀ᶠ y in 𝓝 x, IsUnit (A y).det := by
    have hc : ContinuousAt (fun y => (A y).det) x :=
      ((differentiable_det _).comp x hA).continuousAt
    filter_upwards [hc.eventually_ne (isUnit_iff_ne_zero.mp hx)] with y hy
    exact isUnit_iff_ne_zero.mpr hy
  have heq : A x * (fderiv ℝ (fun y => (A y)⁻¹) x v) +
      (fderiv ℝ A x v) * (A x)⁻¹ = 0 := by
    ext i j
    have hloc : (fun y => ∑ k, A y i k * (A y)⁻¹ k j) =ᶠ[𝓝 x]
        (fun _ => (1 : Matrix ι ι ℝ) i j) := by
      filter_upwards [hev] with y hy
      exact congrFun (congrFun (Matrix.mul_nonsing_inv (A y) hy) i) j
    have hD := congrArg (fun D : E →L[ℝ] ℝ => D v) hloc.fderiv_eq
    rw [fderiv_const_apply] at hD
    erw [fderiv_fun_sum (u := Finset.univ) (A := fun k y => A y i k * (A y)⁻¹ k j)
      (fun k _ => (hAn i k).mul (hBn k j))] at hD
    simp only [fderiv_fun_mul (hAn _ _) (hBn _ _), _root_.sum_apply,
      _root_.add_apply, _root_.smul_apply, smul_eq_mul, _root_.zero_apply] at hD
    simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      fderiv_matrix_apply hA, fderiv_matrix_apply hB, ← Finset.sum_add_distrib,
      mul_comm] using hD
  have hh := congrArg (fun B : Matrix ι ι ℝ => (A x)⁻¹ * B) heq
  rw [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hx,
    Matrix.one_mul, Matrix.mul_zero] at hh
  exact eq_neg_of_add_eq_zero_left hh |>.trans (by simp only [Matrix.neg_mul, Matrix.mul_assoc])

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma fderiv_cofactor_apply {A : E → Matrix ι ι ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hx : IsUnit (A x).det) (v : E) (i k : ι) :
    fderiv ℝ (fun y => (A y).det * (A y)⁻¹ i k) x v =
      (A x).det * (Matrix.trace (fderiv ℝ A x v * (A x)⁻¹) * (A x)⁻¹ i k -
        ((A x)⁻¹ * (fderiv ℝ A x v) * (A x)⁻¹) i k) := by
  have hB := differentiableAt_matrix_inv hA hx
  have hBn := (differentiableAt_pi.mp (differentiableAt_pi.mp hB i)) k
  have hd : DifferentiableAt ℝ (fun y => (A y).det) x :=
    (differentiable_det _).comp x hA
  rw [fderiv_fun_mul hd hBn]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [fderiv_det_comp_apply A hA hx v, ← fderiv_matrix_apply hB,
    fderiv_matrix_inv_apply hA hx v]
  simp only [Matrix.neg_mul, Matrix.neg_apply]
  ring

lemma piola_of_curl {A : E → Matrix ι ι ℝ} {x : E} (b : ι → E)
    (hA : DifferentiableAt ℝ A x) (hx : IsUnit (A x).det)
    (hcurl : ∀ i l m, fderiv ℝ A x (b i) l m = fderiv ℝ A x (b m) l i)
    (k : ι) :
    ∑ i, fderiv ℝ (fun y => (A y).det * (A y)⁻¹ i k) x (b i) = 0 := by
  simp_rw [fderiv_cofactor_apply hA hx]
  rw [← Finset.mul_sum, piola_cancellation _ _ hcurl, mul_zero]


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_PiolaIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma piola_identity {f : E → E} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (b : Module.Basis ι ℝ E) (hx : IsUnit (jacobianMatrix b f x).det) (k : ι) :
    ∑ i, fderiv ℝ (fun y => (jacobianMatrix b f y).det *
      (jacobianMatrix b f y)⁻¹ i k) x (b i) = 0 :=
  piola_of_curl b (differentiableAt_jacobian hf b) hx (jacobian_curl hf b) k

lemma piola_divergence {f : E → E} {X : E → ι → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hX : DifferentiableAt ℝ X (f x))
    (b : Module.Basis ι ℝ E) (hx : IsUnit (jacobianMatrix b f x).det) :
    ∑ i, fderiv ℝ (fun y => ∑ k, (jacobianMatrix b f y).det *
      (jacobianMatrix b f y)⁻¹ i k * X (f y) k) x (b i) =
      (jacobianMatrix b f x).det * ∑ k, fderiv ℝ (fun z => X z k) (f x) (b k) := by
  let J := jacobianMatrix b f
  have hJ : DifferentiableAt ℝ J x := differentiableAt_jacobian hf b
  have hd : DifferentiableAt ℝ (fun y => (J y).det) x :=
    (differentiable_det _).comp x hJ
  have hB := differentiableAt_matrix_inv hJ hx
  have hC (i k : ι) : DifferentiableAt ℝ (fun y => (J y).det * (J y)⁻¹ i k) x :=
    hd.mul (differentiableAt_pi.mp (differentiableAt_pi.mp hB i) k)
  have hf' := hf.differentiableAt (by norm_num)
  have hY (k : ι) : DifferentiableAt ℝ (fun y => X (f y) k) x :=
    (differentiableAt_pi.mp hX k).comp x hf'
  change (∑ i, fderiv ℝ (fun y => ∑ k, (J y).det * (J y)⁻¹ i k * X (f y) k)
    x (b i)) = _
  have hexp (i : ι) : fderiv ℝ (fun y => ∑ k, (J y).det * (J y)⁻¹ i k * X (f y) k)
      x (b i) = ∑ k, ((J x).det * (J x)⁻¹ i k * fderiv ℝ (fun y => X (f y) k) x (b i) +
        X (f x) k * fderiv ℝ (fun y => (J y).det * (J y)⁻¹ i k) x (b i)) := by
    erw [fderiv_fun_sum (u := Finset.univ) (A := fun k y =>
      (J y).det * (J y)⁻¹ i k * X (f y) k) (fun k _ => (hC i k).mul (hY k))]
    simp only [fderiv_fun_mul (hC _ _) (hY _), _root_.sum_apply,
      _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  simp_rw [hexp, Finset.sum_add_distrib]
  have hz : (∑ i, ∑ k, X (f x) k * fderiv ℝ (fun y => (J y).det * (J y)⁻¹ i k) x (b i)) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro k _
    rw [← Finset.mul_sum, piola_identity hf b hx k, mul_zero]
  rw [hz, add_zero]
  simp_rw [fderiv_comp_basis hf' hX, mul_assoc, ← Finset.mul_sum]
  congr 1
  let D : Matrix ι ι ℝ := fun k m => fderiv ℝ (fun z => X z k) (f x) (b m)
  have ht : (∑ i, ∑ k, (J x)⁻¹ i k * ∑ m, J x m i * D k m) =
      Matrix.trace ((J x)⁻¹ * (D * J x)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    congr 1
    ext i
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    ring
  change (∑ i, ∑ k, (J x)⁻¹ i k * ∑ m, J x m i * D k m) = ∑ k, D k k
  rw [ht, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hx,
    Matrix.mul_one]
  rfl
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_MixedPiolaDivergenceAbs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma piola_divergence_abs {f : E → E} {X : E → ι → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hX : DifferentiableAt ℝ X (f x))
    (b : Module.Basis ι ℝ E) (hx : IsUnit (jacobianMatrix b f x).det) :
    ∑ i, fderiv ℝ (fun y => ∑ k, |(jacobianMatrix b f y).det| *
      (jacobianMatrix b f y)⁻¹ i k * X (f y) k) x (b i) =
      |(jacobianMatrix b f x).det| * ∑ k, fderiv ℝ (fun z => X z k) (f x) (b k) := by
  let J := jacobianMatrix b f
  have hJ : DifferentiableAt ℝ J x := differentiableAt_jacobian hf b
  have hd : ContinuousAt (fun y => (J y).det) x :=
    ((differentiable_det _).comp x hJ).continuousAt
  obtain ⟨c, hcx, hcy⟩ := local_abs_multiplier hd (isUnit_iff_ne_zero.mp hx)
  have hh (i : ι) : fderiv ℝ (fun y => ∑ k, |(J y).det| * (J y)⁻¹ i k * X (f y) k) x =
      c • fderiv ℝ (fun y => ∑ k, (J y).det * (J y)⁻¹ i k * X (f y) k) x := by
    have he : (fun y => ∑ k, |(J y).det| * (J y)⁻¹ i k * X (f y) k) =ᶠ[𝓝 x]
        (fun y => c * ∑ k, (J y).det * (J y)⁻¹ i k * X (f y) k) := by
      filter_upwards [hcy] with y hy
      simp only [hy, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [he.fderiv_eq]
    have hf' := hf.differentiableAt (by norm_num)
    have hB := differentiableAt_matrix_inv hJ hx
    have hd' : DifferentiableAt ℝ (fun y => (J y).det) x :=
      (differentiable_det _).comp x hJ
    exact fderiv_const_mul (DifferentiableAt.fun_sum (fun k _ =>
      (hd'.mul (differentiableAt_pi.mp (differentiableAt_pi.mp hB i) k)).mul
        ((differentiableAt_pi.mp hX k).comp x hf'))) c
  change (∑ i, fderiv ℝ (fun y => ∑ k, |(J y).det| * (J y)⁻¹ i k * X (f y) k) x (b i)) = _
  simp_rw [hh, _root_.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, piola_divergence hf hX b hx]
  change c * ((J x).det * _) = |(J x).det| * _
  rw [hcx, mul_assoc]

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_AnisotropicConstant
attribute [-instance] _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
namespace YauCounterexamples

variable (E F : Type*)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {E F}

theorem range_fourierSobolevDistribution (s : ℝ) (f : 𝓢'(E, F)) :
    (∃ u : FourierSobolevSpace E F s, fourierSobolevDistribution E F s u = f) ↔
      MemSobolev s 2 f := by
  rw [memSobolev_iff_exists_smulLeftCLM_fourier]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, weighted_fourier_fourierSobolevDistribution s u⟩
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    rw [fourierSobolevDistribution_apply, ← hu,
      smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
    have hw : (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (s / 2))) *
        (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2))) = fun _ => 1 := by
      ext x
      simp only [Pi.mul_apply]
      norm_cast
      rw [← Real.rpow_add (by positivity)]
      convert Real.rpow_zero _ using 2
      all_goals try with_reducible_and_instances rfl
      ring
    rw [hw, smulLeftCLM_const]
    simp

end YauCounterexamples

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_MomentBesselLp
attribute [-instance] _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
namespace YauCounterexamples

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma memLp_moment_bessel_weight {s : ℝ} (n : ℕ)
    (hs : Module.finrank ℝ E < 2 * (s - n)) :
    MemLp (fun x : E ↦ ‖x‖ ^ n * (1 + ‖x‖ ^ 2) ^ (-s / 2)) 2 := by
  refine (memLp_bessel_weight hs).mono' ?_ ?_
  · have ht : (fun x : E => (1 + ‖x‖ ^ 2) ^ (-s / 2)).HasTemperateGrowth := by
      fun_prop
    exact ((continuous_norm.pow n).mul ht.1.continuous).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact norm_pow_mul_bessel_weight_le x n s

theorem sobolev_fourier_moments {s : ℝ} (N : ℕ)
    (hs : Module.finrank ℝ E < 2 * (s - N)) (f : 𝓢'(E, F))
    (hf : MemSobolev s 2 f) :
    ∃ v : Lp F 1 (volume : Measure E), 𝓕 f = (v : 𝓢'(E, F)) ∧
      ∀ n ≤ N, Integrable (fun x : E => ‖x‖ ^ n * ‖v x‖) := by
  obtain ⟨u, hu⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.mp hf
  have hdim : (Module.finrank ℝ E : ℝ) < 2 * s := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hw : MemLp (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2))) 2 :=
    (memLp_bessel_weight hdim).ofReal
  let v : Lp F 1 (volume : Measure E) := hw.toLp _ • u
  refine ⟨v, ?_, ?_⟩
  · dsimp [v]
    rw [MeasureTheory.Lp.toTemperedDistribution_smul_eq]
    · rw [← hu, smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
      convert (smulLeftCLM_const 1 (𝓕 f)).symm using 1
      · simp
      · congr
        ext x
        rw [Pi.mul_apply]
        norm_cast
        rw [← Real.rpow_add (by positivity)]
        ring_nf
        simp
    · fun_prop
  · intro n hn
    have hsn : (Module.finrank ℝ E : ℝ) < 2 * (s - n) := by
      have hnn : (n : ℝ) ≤ N := by exact_mod_cast hn
      linarith
    have hm : MemLp (fun x : E =>
        (‖x‖ ^ n * (1 + ‖x‖ ^ 2) ^ (-s / 2)) * ‖u x‖) 1 :=
      (Lp.memLp u).norm.mul' (memLp_moment_bessel_weight n hsn)
    apply (memLp_one_iff_integrable.mp hm).congr
    filter_upwards [Lp.coeFn_lpSMul (r := (1 : ℝ≥0∞)) (hw.toLp _) u,
      hw.coeFn_toLp] with x hx hy
    change _ = ‖x‖ ^ n * ‖(hw.toLp _ • u : Lp F 1 volume) x‖
    rw [hx]
    change _ = ‖x‖ ^ n * ‖(hw.toLp _ : E → ℂ) x • u x‖
    rw [hy]
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖x‖ ^ 2) (-s / 2))]
    ring

theorem sobolev_Ck_representative {s : ℝ} (N : ℕ)
    (hs : Module.finrank ℝ E < 2 * (s - N)) (f : 𝓢'(E, F))
    (hf : MemSobolev s 2 f) :
    ∃ u : E →ᵇ F, boundedDistribution u = f ∧ ContDiff ℝ N (u : E → F) := by
  obtain ⟨v, hv, hm⟩ := sobolev_fourier_moments N hs f hf
  refine ⟨inverseFourierL1 v, ?_, ?_⟩
  · rw [inverseFourierL1_distribution, ← hv, fourierInv_fourier_eq]
  · have hd : ContDiff ℝ N (𝓕 (v : E → F)) :=
      Real.contDiff_fourier (fun n hn => hm n (by exact_mod_cast hn))
    change ContDiff ℝ N (fun x : E => 𝓕 (v : E → F) (-x))
    exact hd.comp contDiff_neg

end YauCounterexamples

open MeasureTheory
open scoped ENNReal

end

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
namespace YauCounterexamples

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma sobolevWeight_pos (s : ℝ) (x : E) : 0 < sobolevWeight s x := by
  exact Real.rpow_pos_of_pos (by positivity) _

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma sobolevWeight_add_le {s : ℝ} (hs : 0 ≤ s) (x y : E) :
    sobolevWeight s (x + y) ≤ (4 : ℝ) ^ (s / 2) *
      (sobolevWeight s x + sobolevWeight s y) := by
  have hq : 1 + ‖x + y‖ ^ 2 ≤ 4 * max (1 + ‖x‖ ^ 2) (1 + ‖y‖ ^ 2) := by
    have hnorm := norm_add_le x y
    have hsq : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hx := le_max_left (1 + ‖x‖ ^ 2) (1 + ‖y‖ ^ 2)
    have hy := le_max_right (1 + ‖x‖ ^ 2) (1 + ‖y‖ ^ 2)
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  have hm : 0 ≤ max (1 + ‖x‖ ^ 2) (1 + ‖y‖ ^ 2) := le_trans (by positivity) (le_max_left _ _)
  have hh := Real.rpow_le_rpow (by positivity) hq (by positivity : 0 ≤ s / 2)
  rw [Real.mul_rpow (by norm_num) hm,
    Real.rpow_max (by positivity) (by positivity) (by positivity)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (max_le (le_add_of_nonneg_right (le_of_lt (sobolevWeight_pos s y)))
      (le_add_of_nonneg_left (le_of_lt (sobolevWeight_pos s x)))) (by positivity))

open scoped SchwartzMap

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_weightedSchwartz (s : ℝ) (f : 𝓢(E, ℂ)) (x : E) :
    ‖weightedSchwartz s f x‖ = sobolevWeight s x * ‖f x‖ := by
  rw [weightedSchwartz_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sobolevWeight_pos s x)]

lemma weighted_convolution_pointwise {s : ℝ} (hs : 0 ≤ s) (f g : 𝓢(E, ℂ)) (x : E) :
    sobolevWeight s x * ‖∫ y, f y * g (x - y)‖ ≤
      (4 : ℝ) ^ (s / 2) *
        ((∫ y, ‖weightedSchwartz s f y‖ * ‖g (x - y)‖) +
         (∫ y, ‖f y‖ * ‖weightedSchwartz s g (x - y)‖)) := by
  have h1 := integrable_norm_mul_sub (weightedSchwartz s f) g x
  have h2 := integrable_norm_mul_sub f (weightedSchwartz s g) x
  have hm := (h1.add h2).const_mul ((4 : ℝ) ^ (s / 2))
  simp only [Pi.add_apply] at hm
  have hh := norm_integral_le_of_norm_le (f := fun y => sobolevWeight s x • (f y * g (x - y))) hm
    (by
      filter_upwards with y
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (sobolevWeight_pos s x), norm_mul,
        norm_weightedSchwartz, norm_weightedSchwartz]
      have hw := sobolevWeight_add_le hs y (x - y)
      rw [add_sub_cancel] at hw
      calc
        _ ≤ ((4 : ℝ) ^ (s / 2) * (sobolevWeight s y + sobolevWeight s (x - y))) *
            (‖f y‖ * ‖g (x - y)‖) :=
          mul_le_mul_of_nonneg_right hw (by positivity)
        _ = _ := by ring)
  rw [integral_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (sobolevWeight_pos s x),
    integral_const_mul, integral_add h1 h2] at hh
  exact hh

theorem weighted_convolution_eLpNorm {s : ℝ} (hs : 0 ≤ s) (f g : 𝓢(E, ℂ)) :
    eLpNorm (fun x => sobolevWeight s x • (∫ y, f y * g (x - y))) 2 volume ≤
      ‖((4 : ℝ) ^ (s / 2))‖ₑ *
        (eLpNorm g 1 volume * eLpNorm (weightedSchwartz s f) 2 volume +
         eLpNorm f 1 volume * eLpNorm (weightedSchwartz s g) 2 volume) := by
  let q₁ : E → ℝ := fun x => ∫ y, ‖g y‖ * ‖weightedSchwartz s f (x - y)‖
  let q₂ : E → ℝ := fun x => ∫ y, ‖f y‖ * ‖weightedSchwartz s g (x - y)‖
  have hbound : eLpNorm (fun x => sobolevWeight s x • (∫ y, f y * g (x - y))) 2 volume ≤
      eLpNorm (((4 : ℝ) ^ (s / 2)) • (q₁ + q₂)) 2 volume := by
    apply eLpNorm_mono
    intro x
    have hpoint := weighted_convolution_pointwise hs f g x
    rw [mulConvolution_comm (fun y => ‖weightedSchwartz s f y‖) (fun y => ‖g y‖) x] at hpoint
    change ‖sobolevWeight s x • (∫ y, f y * g (x - y))‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (sobolevWeight_pos s x)]
    simpa only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ (4 : ℝ) ^ (s / 2) * (q₁ x + q₂ x) from
        mul_nonneg (by positivity) (add_nonneg (integral_nonneg (fun _ => by positivity))
          (integral_nonneg (fun _ => by positivity))))] using hpoint
  have h₁ : eLpNorm q₁ 2 volume ≤ eLpNorm g 1 volume * eLpNorm (weightedSchwartz s f) 2 volume := by
    simpa only [eLpNorm_norm _,
      eLpNorm_norm _] using
      young_eLpNorm_two g.continuous.norm.measurable
      (weightedSchwartz s f).continuous.norm.measurable
  have h₂ : eLpNorm q₂ 2 volume ≤ eLpNorm f 1 volume * eLpNorm (weightedSchwartz s g) 2 volume := by
    simpa only [eLpNorm_norm _,
      eLpNorm_norm _] using
      young_eLpNorm_two f.continuous.norm.measurable
      (weightedSchwartz s g).continuous.norm.measurable
  refine hbound.trans ?_
  rw [eLpNorm_const_smul]
  exact mul_le_mul' le_rfl ((eLpNorm_add_le
    (stronglyMeasurable_mulConvolution g.continuous.norm.measurable
      (weightedSchwartz s f).continuous.norm.measurable).aestronglyMeasurable
    (stronglyMeasurable_mulConvolution f.continuous.norm.measurable
      (weightedSchwartz s g).continuous.norm.measurable).aestronglyMeasurable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add h₁ h₂))

lemma memLp_inverse_sobolevWeight {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) :
    MemLp (sobolevWeight (-s) : E → ℝ) 2 volume := by
  refine ⟨(continuous_sobolevWeight (-s)).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  suffices h : ∫⁻ a : E, ENNReal.ofReal ‖(1 + ‖a‖ ^ 2) ^ (-s)‖ < ⊤ from by
    norm_cast
    simp_rw [ofReal_norm] at h
    simp_rw [← enorm_pow]
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext x
    rw [sobolevWeight, ← Real.rpow_mul_natCast (by positivity)]
    congr 2
    ring
  apply ((integrable_rpow_neg_one_add_norm_sq hs).congr _).lintegral_lt_top
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
  congr
  ring

lemma schwartz_eLpNorm_one_le_weighted (s : ℝ) (f : 𝓢(E, ℂ)) :
    eLpNorm f 1 volume ≤ eLpNorm (sobolevWeight (-s) : E → ℝ) 2 volume *
      eLpNorm (weightedSchwartz s f) 2 volume := by
  have h := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
    (μ := (volume : Measure E))
    (f := fun x => ‖weightedSchwartz s f x‖)
    (φ := sobolevWeight (-s))
    (weightedSchwartz s f).continuous.norm.aestronglyMeasurable
    (continuous_sobolevWeight (-s)).aestronglyMeasurable
  have heq : (sobolevWeight (-s) : E → ℝ) • (fun x => ‖weightedSchwartz s f x‖) =
      fun x => ‖f x‖ := by
    ext x
    change sobolevWeight (-s) x * ‖weightedSchwartz s f x‖ = ‖f x‖
    rw [norm_weightedSchwartz]
    unfold sobolevWeight
    rw [← mul_assoc, ← Real.rpow_add (by positivity)]
    have hexp : -s / 2 + s / 2 = 0 := by ring
    rw [hexp, Real.rpow_zero, one_mul]
  rw [heq, eLpNorm_norm _,
    eLpNorm_norm _] at h
  exact h

theorem weighted_convolution_algebra_eLpNorm {s : ℝ} (hs : 0 ≤ s) (f g : 𝓢(E, ℂ)) :
    eLpNorm (fun x => sobolevWeight s x • (∫ y, f y * g (x - y))) 2 volume ≤
      (‖((4 : ℝ) ^ (s / 2))‖ₑ * 2 * eLpNorm (sobolevWeight (-s) : E → ℝ) 2 volume) *
        eLpNorm (weightedSchwartz s f) 2 volume * eLpNorm (weightedSchwartz s g) 2 volume := by
  refine (weighted_convolution_eLpNorm hs f g).trans ?_
  have hf := schwartz_eLpNorm_one_le_weighted s f
  have hg := schwartz_eLpNorm_one_le_weighted s g
  calc
    _ ≤ ‖((4 : ℝ) ^ (s / 2))‖ₑ *
        ((eLpNorm (sobolevWeight (-s) : E → ℝ) 2 volume * eLpNorm (weightedSchwartz s g) 2 volume) *
          eLpNorm (weightedSchwartz s f) 2 volume +
        (eLpNorm (sobolevWeight (-s) : E → ℝ) 2 volume * eLpNorm (weightedSchwartz s f) 2 volume) *
          eLpNorm (weightedSchwartz s g) 2 volume) := by gcongr
    _ = _ := by ring

open FourierTransform

end YauCounterexamples

end

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
namespace YauCounterexamples
open FourierTransform MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma denseRange_schwartzToSobolev (s : ℝ) :
    DenseRange (schwartzToSobolev (E := E) s) := by
  have hd : DenseRange (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E)) :=
    SchwartzMap.denseRange_toLpCLM (by norm_num)
  apply hd.mono
  rintro _ ⟨f, rfl⟩
  refine ⟨𝓕⁻ (weightedSchwartz (-s) f), ?_⟩
  rw [schwartzToSobolev_apply, fourier_fourierInv_eq, weightedSchwartz_neg_cancel]
  rfl

lemma sobolevAlgebraConstant_nonneg (s : ℝ) : 0 ≤ sobolevAlgebraConstant (E := E) s :=
  ENNReal.toReal_nonneg

lemma schwartz_sobolev_product_bound {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (f g : 𝓢(E, ℂ)) :
    ‖schwartzToSobolev s (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g)‖ ≤
      sobolevAlgebraConstant (E := E) s * ‖schwartzToSobolev s f‖ *
        ‖schwartzToSobolev s g‖ := by
  have hs0 : 0 ≤ s := by have := (Nat.cast_nonneg (Module.finrank ℝ E) : (0 : ℝ) ≤ _); linarith
  have hb := weighted_convolution_algebra_eLpNorm hs0 (𝓕 f) (𝓕 g)
  have hw : (fun x => sobolevWeight s x • (∫ y, (𝓕 f) y * (𝓕 g) (x - y))) =
      (weightedSchwartz s (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 f) (𝓕 g)) : E → ℂ) := by
    ext x
    rw [weightedSchwartz_apply]
    simp only [SchwartzMap.convolution_apply, MeasureTheory.convolution,
      ContinuousLinearMap.mul_apply']
    exact Complex.real_smul
  rw [hw, ← schwartz_fourier_product f g] at hb
  have hfin : (‖((4 : ℝ) ^ (s / 2))‖ₑ * 2 * eLpNorm (sobolevWeight (-s) : E → ℝ) 2 volume) *
        eLpNorm (weightedSchwartz s (𝓕 f)) 2 volume *
        eLpNorm (weightedSchwartz s (𝓕 g)) 2 volume ≠ ⊤ := by
    apply ENNReal.mul_ne_top _ (SchwartzMap.memLp _ _ _).eLpNorm_ne_top
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by finiteness) (memLp_inverse_sobolevWeight hs).eLpNorm_ne_top)
      (SchwartzMap.memLp _ _ _).eLpNorm_ne_top
  have hr := ENNReal.toReal_mono hfin hb
  simpa only [schwartzToSobolev_apply, SchwartzMap.norm_toLp,
    ENNReal.toReal_mul, sobolevAlgebraConstant] using hr

def schwartzSobolevProduct (s : ℝ) :
    𝓢(E, ℂ) →ₗ[ℂ] 𝓢(E, ℂ) →ₗ[ℂ] FourierSobolevSpace E ℂ s where
  toFun f := (schwartzToSobolev s).toLinearMap.comp
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f).toLinearMap
  map_add' f g := by ext h; simp
  map_smul' c f := by ext h; simp

def sobolevProduct {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) :
    FourierSobolevSpace E ℂ s →L[ℂ]
      FourierSobolevSpace E ℂ s →L[ℂ] FourierSobolevSpace E ℂ s :=
  bilinearExtension (schwartzSobolevProduct s) (schwartzToSobolev s).toLinearMap
    (denseRange_schwartzToSobolev s) (sobolevAlgebraConstant (E := E) s)
    (schwartz_sobolev_product_bound hs)

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContinuousSobolevFirstDerivative
attribute [-instance] _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open scoped LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def sobolevSecondDerivative (s : ℝ) (v w : E) :
    FourierSobolevSpace E ℂ s →L[ℂ] FourierSobolevSpace E ℂ (s - 2) :=
  sobolevDerivative (s - 1) v ∘L sobolevDerivative s w


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
open Set Filter
open scoped Topology LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma contDiff_sobolevRepresentative {s : ℝ} (N : ℕ)
    (hs : Module.finrank ℝ E < 2 * (s - N)) (ht : Module.finrank ℝ E < 2 * s)
    (u : FourierSobolevSpace E ℂ s) : ContDiff ℝ N (sobolevRepresentative ht u : E → ℂ) := by
  obtain ⟨v, hv, hvc⟩ := sobolev_Ck_representative N hs
    (fourierSobolevDistribution E ℂ s u)
    ((range_fourierSobolevDistribution s _).mp ⟨u, rfl⟩)
  have he : v = sobolevRepresentative ht u := boundedDistribution_injective
    (hv.trans (sobolevRepresentative_distribution ht u).symm)
  rwa [he] at hvc

lemma sobolevDerivative_representative {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * (s - 1))
    (ht : Module.finrank ℝ E < 2 * s)
    (u : FourierSobolevSpace E ℂ s) (v x : E) :
    sobolevRepresentative hs (sobolevDerivative s v u) x =
      fderiv ℝ (sobolevRepresentative ht u : E → ℂ) x v := by
  obtain ⟨w, hw, hwu⟩ := mem_closure_iff_seq_limit.mp
    ((denseRange_schwartzToSobolev (E := E) s) u)
  choose f hf using hw
  have hfu : Tendsto (fun n => schwartzToSobolev s (f n)) atTop (𝓝 u) := by
    simpa only [hf] using hwu
  have hc : Tendsto (fun n => sobolevRepresentative ht (schwartzToSobolev s (f n)))
      atTop (𝓝 (sobolevRepresentative ht u)) :=
    (sobolevRepresentative ht).continuous.continuousAt.tendsto.comp hfu
  have hd : Tendsto (fun n => sobolevRepresentative hs
      (sobolevDerivative s v (schwartzToSobolev s (f n)))) atTop
      (𝓝 (sobolevRepresentative hs (sobolevDerivative s v u))) :=
    (sobolevRepresentative hs).continuous.continuousAt.tendsto.comp
      ((sobolevDerivative s v).continuous.continuousAt.tendsto.comp hfu)
  have hc' : TendstoUniformly (fun n => (f n : E → ℂ)) (sobolevRepresentative ht u) atTop := by
    have h := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hc
    simp only [sobolevRepresentative_schwartz] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ext n y
    exact (SchwartzMap.toBoundedContinuousFunction_apply _ _).symm
  have hd' : TendstoUniformly (fun n x => (∂_{v} (f n) : 𝓢(E, ℂ)) x)
      (sobolevRepresentative hs (sobolevDerivative s v u)) atTop := by
    have h := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hd
    simp only [sobolevDerivative_schwartz, sobolevRepresentative_schwartz] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ext n y
    exact (SchwartzMap.toBoundedContinuousFunction_apply _ _).symm
  have hline (t : ℝ) : HasDerivAt (fun t : ℝ => x + t • v) v t := by
    simpa using (hasDerivAt_id t).smul_const v |>.const_add x
  have hlim : HasDerivAt (fun t : ℝ => sobolevRepresentative ht u (x + t • v))
      (sobolevRepresentative hs (sobolevDerivative s v u) x) 0 := by
    have hh := hasDerivAt_of_tendstoUniformly
      (hd'.comp (fun t : ℝ => x + t • v))
      (Filter.Eventually.of_forall (fun n t => by
        simp only [Function.comp_def, SchwartzMap.lineDerivOp_apply,
          (f n).differentiableAt.lineDeriv_eq_fderiv]
        exact (f n).hasFDerivAt (x + t • v) |>.comp_hasDerivAt t (hline t)))
      (fun t => hc'.tendsto_at (x + t • v)) 0
    simpa only [Function.comp_def, zero_smul, add_zero, SchwartzMap.lineDerivOp_apply] using hh
  have hu := (contDiff_sobolevRepresentative 1 (by simpa using hs) ht u).differentiable
    (by norm_num)
  have hh := (hu (x + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt 0 (hline 0)
  simp only [zero_smul, add_zero] at hh
  exact hlim.unique hh


open Matrix ContinuousLinearMap
open scoped InnerProductSpace

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
open Matrix ContinuousLinearMap
open scoped InnerProductSpace
open FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Real
open scoped LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sobolevInclusion_representative (s t : ℝ) (h : t ≤ s)
    (hs : Module.finrank ℝ E < 2 * s) (ht : Module.finrank ℝ E < 2 * t)
    (u : FourierSobolevSpace E ℂ s) :
    sobolevRepresentative ht (sobolevInclusion s t h u) = sobolevRepresentative hs u := by
  apply boundedDistribution_injective
  rw [sobolevRepresentative_distribution, sobolevInclusion_distribution,
    sobolevRepresentative_distribution]

lemma sobolevRepresentative_congr (s t : ℝ) (h : s = t)
    (hs : Module.finrank ℝ E < 2 * s) (ht : Module.finrank ℝ E < 2 * t) :
    sobolevRepresentative hs = sobolevRepresentative ht := by
  subst t
  rfl


end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SobolevRepresentativeOrderCongr
attribute [-instance] _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped SchwartzMap BoundedContinuousFunction
section FirstOrderSobolev
open scoped SchwartzMap BoundedContinuousFunction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι]

def firstOrderSobolev {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (β₀ : 𝓢(E, ℂ)) (β : ι → 𝓢(E, ℂ)) (b : ι → E) :
    FourierSobolevSpace E ℂ (s + 1) →L[ℂ] FourierSobolevSpace E ℂ s :=
  (sobolevProduct hs (schwartzToSobolev s β₀)) ∘L
      sobolevInclusion (s + 1) s (by linarith) +
    ∑ i, (sobolevProduct hs (schwartzToSobolev s (β i))) ∘L
      sobolevDerivative (s + 1) (b i)

end FirstOrderSobolev

section CompactDifferentialCoefficients
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

lemma contDiff_euclideanElliptic (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    {χ : E → ℂ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (euclideanElliptic b a c χ) := by
  apply ContDiff.add
  · apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro j _
    exact (Complex.ofRealCLM.contDiff.comp (ha i j)).mul
      (contDiff_directional (contDiff_directional hχ (b j)) (b i))
  · apply ContDiff.sum
    intro i _
    exact (Complex.ofRealCLM.contDiff.comp (hc i)).mul (contDiff_directional hχ (b i))

def cutoffDerivativeSchwartz {χ : E → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) {a : E → ℝ} (ha : ContDiff ℝ ∞ a) (b : E) : 𝓢(E, ℂ) :=
  (show HasCompactSupport (fun x => (a x : ℂ) * fderiv ℝ χ x b) from
    (hχc.fderiv_apply ℝ b).mul_left).toSchwartzMap
      ((Complex.ofRealCLM.contDiff.comp ha).mul (contDiff_directional hχ b))
@[simp] lemma cutoffDerivativeSchwartz_apply {χ : E → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) {a : E → ℝ} (ha : ContDiff ℝ ∞ a) (b x : E) :
    cutoffDerivativeSchwartz hχ hχc ha b x = (a x : ℂ) * fderiv ℝ χ x b := rfl
end CompactDifferentialCoefficients



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RescaledCommutatorSobolev
attribute [-instance] _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
namespace YauCounterexamples
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι]

def rescaledCommutatorSobolev {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (p : E) (r : ℝ) (hr : r ≠ 0) :
    FourierSobolevSpace E ℂ (s + 1) →L[ℂ] FourierSobolevSpace E ℂ s :=
  firstOrderSobolev hs
    (affineSchwartz (euclideanElliptic b a c χ) (contDiff_euclideanElliptic b a c ha hc hχ)
      (hasCompactSupport_euclideanElliptic b a c hχc) p r hr)
    (fun ij : ι × ι => (r : ℂ)⁻¹ • affineSchwartz
      (cutoffDerivativeSchwartz hχ hχc (ha ij.1 ij.2) (b ij.1))
      ((cutoffDerivativeSchwartz hχ hχc (ha ij.1 ij.2) (b ij.1)).smooth ⊤)
      (by exact (hχc.fderiv_apply ℝ (b ij.1)).mul_left) p r hr)
    (fun ij : ι × ι => b ij.2) +
  firstOrderSobolev hs 0
    (fun ij : ι × ι => (r : ℂ)⁻¹ • affineSchwartz
      (cutoffDerivativeSchwartz hχ hχc (ha ij.1 ij.2) (b ij.2))
      ((cutoffDerivativeSchwartz hχ hχc (ha ij.1 ij.2) (b ij.2)).smooth ⊤)
      (by exact (hχc.fderiv_apply ℝ (b ij.2)).mul_left) p r hr)
    (fun ij : ι × ι => b ij.1)

end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RescaledDifferentialPerturbation
attribute [-instance] _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
open Matrix ContinuousLinearMap
open scoped InnerProductSpace
open FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Real
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def sobolevFirstLower (s : ℝ) (v : E) :
    FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s :=
  sobolevInclusion (s + 2 - 1) s (by linarith) ∘L sobolevDerivative (s + 2) v

def coefficientPerturbation {ι : Type*} [Fintype ι] (b : ι → E) {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * s)
    (a : ι → ι → FourierSobolevSpace E ℂ s) (c : ι → FourierSobolevSpace E ℂ s) :
    FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s :=
  (∑ i, ∑ j, (sobolevProduct hs (a i j)) ∘L sobolevSecondDerivative (s + 2) (b i) (b j)) +
    ∑ i, (sobolevProduct hs (c i)) ∘L sobolevFirstLower s (b i)


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
open Matrix ContinuousLinearMap
open scoped InnerProductSpace
open FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Real
open scoped SchwartzMap




end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CutoffPullbackLinear
attribute [-instance] _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def cutoffPullbackLinear (η : E → ℂ) (hηc : HasCompactSupport η) (hη : ContDiff ℝ ∞ η)
    (φ : E → E) (hφ : ContDiff ℝ ∞ φ) : 𝓢(E, ℂ) →ₗ[ℂ] 𝓢(E, ℂ) where
  toFun := cutoffPullback η hηc hη φ hφ
  map_add' f g := by ext x; simp [cutoffPullback, mul_add]
  map_smul' c f := by ext x; simp [cutoffPullback, mul_left_comm]

def sobolevCutoffPullback (η : E → ℂ) (hηc : HasCompactSupport η) (hη : ContDiff ℝ ∞ η)
    (φ : E → E) (hφ : ContDiff ℝ ∞ φ) (k : ℕ) :
    FourierSobolevSpace E ℂ (2 * (k : ℝ)) →L[ℂ] FourierSobolevSpace E ℂ (2 * (k : ℝ)) :=
  ((schwartzToSobolev (2 * (k : ℝ))).toLinearMap.comp
    (cutoffPullbackLinear η hηc hη φ hφ)).extendOfNorm
    (schwartzToSobolev (2 * (k : ℝ))).toLinearMap

end YauCounterexamples

open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ScalarAffineDetNeZero
attribute [-instance] _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def sobolevAffineCutoff (η : E → ℂ) (hηc : HasCompactSupport η)
    (hη : ContDiff ℝ ∞ η) (p : E) (r : ℝ) (k : ℕ) :
    FourierSobolevSpace E ℂ (2 * (k : ℝ)) →L[ℂ]
      FourierSobolevSpace E ℂ (2 * (k : ℝ)) :=
  sobolevCutoffPullback η hηc hη (fun y => p + r • y) (by fun_prop) k

end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LocalIntegrationParts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma localLaplacian_expansion {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    localLaplacian g u p y =
      (∑ i, ∑ j, (metricCoefficients g p y)⁻¹ i j *
        fderiv ℝ (fun z => fderiv ℝ (u ∘ (chartAt E p).symm) z (Module.finBasis ℝ E j)) y
          (Module.finBasis ℝ E i)) +
      ∑ j, metricFirstCoefficient g p j y *
        fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j) := by
  classical
  let ρ := fun z => Real.sqrt (metricCoefficients g p z).det
  let A := metricCoefficients g p
  let v := u ∘ (chartAt E p).symm
  let b := Module.finBasis ℝ E
  have hρ : DifferentiableAt ℝ ρ y := ((contDiffOn_metricDensity g p).contDiffAt
    ((chartAt E p).open_target.mem_nhds hy)).differentiableAt (by simp)
  have hA (i j : CoordIndex E) : DifferentiableAt ℝ (fun z => (A z)⁻¹ i j) y :=
    ((contDiffOn_metricInverse g p i j).contDiffAt
      ((chartAt E p).open_target.mem_nhds hy)).differentiableAt (by simp)
  have hv : DifferentiableAt ℝ (fderiv ℝ v) y :=
    ((contDiffAt_inChart hu p hy).fderiv_right (m := 1) (by rw [one_add_one_eq_two]; exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).differentiableAt one_ne_zero
  have he (i : CoordIndex E) : (fun z => metricFlux g u p z i) =
      fun z => ∑ j, (ρ z * (A z)⁻¹ i j) * fderiv ℝ v z (b j) := by
    funext z
    simp only [metricFlux, ρ, A, v, b, Finset.mul_sum, mul_assoc]
  have hder (i : CoordIndex E) : fderiv ℝ (fun z => metricFlux g u p z i) y (b i) =
      ∑ j, ((ρ y * (A y)⁻¹ i j) * fderiv ℝ (fun z => fderiv ℝ v z (b j)) y (b i) +
        fderiv ℝ v y (b j) * fderiv ℝ (fun z => ρ z * (A z)⁻¹ i j) y (b i)) := by
    rw [he]
    erw [fderiv_fun_sum (u := Finset.univ)
      (A := fun j z => (ρ z * (A z)⁻¹ i j) * fderiv ℝ v z (b j))
      (fun j _ => (hρ.mul (hA i j)).mul (hv.clm_apply (differentiableAt_const _)))]
    simp only [_root_.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    erw [fderiv_mul (c := fun z => ρ z * (A z)⁻¹ i j)
      (d := fun z => fderiv ℝ v z (b j)) (hρ.mul (hA i j))
      (hv.clm_apply (differentiableAt_const _))]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  change (ρ y)⁻¹ * ∑ i, fderiv ℝ (fun z => metricFlux g u p z i) y (b i) = _
  simp_rw [hder, Finset.sum_add_distrib]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  have hn : ρ y ≠ 0 := (Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hy)).ne'
  have hmain : (∑ i, (ρ y)⁻¹ * ∑ j, ρ y * (A y)⁻¹ i j *
      fderiv ℝ (fun z => fderiv ℝ v z (b j)) y (b i)) =
      ∑ i, ∑ j, (A y)⁻¹ i j * fderiv ℝ (fun z => fderiv ℝ v z (b j)) y (b i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  rw [hmain]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [metricFirstCoefficient, ρ, A, b, v, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ConstantComplexProductJetBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M]
  {ι : Type*} [Fintype ι]
variable (p : ι → M) (η : ι → M → ℂ)
    (hηc : ∀ i, HasCompactSupport (η i))
    (hηs : ∀ i, tsupport (η i) ⊆ (chartAt E (p i)).source)
    (hηm : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η i))

lemma manifold_sobolev_sup_bound (hηone : ∀ x, ∑ i, η i x = 1)
    {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) (u : ManifoldSmoothFunctions E M) :
    ‖smoothToBounded u‖ ≤ ((Fintype.card ι : ℝ) * ‖sobolevRepresentative (E := E) hs‖) *
      ‖smoothToManifoldSobolev p η hηc hηs hηm s u‖ := by
  classical
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  change ‖u x‖ ≤ _
  have hterm (i : ι) : ‖η i x * u x‖ ≤ ‖sobolevRepresentative (E := E) hs‖ *
      ‖smoothToManifoldSobolev p η hηc hηs hηm s u‖ := by
    by_cases hx : x ∈ (chartAt E (p i)).source
    · rw [← chartSchwartz_apply (p i) (η i) u (hηc i) (hηs i) (hηm i) u.contMDiff x hx]
      let v := atlasSobolevLocalization p η hηc hηs hηm s u
      have hv : (sobolevRepresentative hs (v i)) (chartAt E (p i) x) =
          chartSchwartz (p i) (η i) u (hηc i) (hηs i) (hηm i) u.contMDiff (chartAt E (p i) x) := by
        rw [show v i = schwartzToSobolev s
          (chartSchwartz (p i) (η i) u (hηc i) (hηs i) (hηm i) u.contMDiff) from rfl,
          sobolevRepresentative_schwartz]
        rfl
      rw [← hv]
      calc
        _ ≤ ‖sobolevRepresentative hs (v i)‖ := BoundedContinuousFunction.norm_coe_le_norm _ _
        _ ≤ ‖sobolevRepresentative (E := E) hs‖ * ‖v i‖ := (sobolevRepresentative hs).le_opNorm _
        _ ≤ _ := mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (norm_nonneg _)
    · have hzero : η i x = 0 := by
        by_contra hn
        exact hx (hηs i (subset_tsupport (η i) hn))
      simp only [hzero, zero_mul, norm_zero]
      positivity
  have hsum : u x = ∑ i, η i x * u x := by rw [← Finset.sum_mul, hηone x, one_mul]
  rw [hsum]
  calc
    _ ≤ ∑ i, ‖η i x * u x‖ := norm_sum_le _ _
    _ ≤ ∑ i : ι, ‖sobolevRepresentative (E := E) hs‖ *
        ‖smoothToManifoldSobolev p η hηc hηs hηm s u‖ := Finset.sum_le_sum fun i _ => hterm i
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

lemma manifoldSobolevRepresentative_smooth (hηone : ∀ x, ∑ i, η i x = 1)
    {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) (u : ManifoldSmoothFunctions E M) :
    manifoldSobolevRepresentative p η hηc hηs hηm s
      (smoothToManifoldSobolev p η hηc hηs hηm s u) = smoothToBounded u :=
  LinearMap.extendOfNorm_eq (denseRange_smoothToManifoldSobolev p η hηc hηs hηm s)
    ⟨_, manifold_sobolev_sup_bound p η hηc hηs hηm hηone hs⟩ u


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] {ι : Type*} [Fintype ι]
variable (p : ι → M) (η : ι → M → ℂ)
    (hηc : ∀ i, HasCompactSupport (η i))
    (hηs : ∀ i, tsupport (η i) ⊆ (chartAt E (p i)).source)
    (hηm : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η i))

omit [CompactSpace M] in
lemma norm_smoothToManifoldSobolev_mono (s t : ℝ) (h : t ≤ s)
    (f : ManifoldSmoothFunctions E M) :
    ‖smoothToManifoldSobolev p η hηc hηs hηm t f‖ ≤
      ‖smoothToManifoldSobolev p η hηc hηs hηm s f‖ := by
  change ‖(smoothToManifoldSobolev p η hηc hηs hηm t f).val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  change ‖schwartzToSobolev t (chartSchwartz (p i) (η i) f (hηc i) (hηs i) (hηm i) f.contMDiff)‖ ≤ _
  exact (norm_schwartzToSobolev_mono s t h _).trans
    (norm_le_pi_norm (smoothToManifoldSobolev p η hηc hηs hηm s f).val i)

def manifoldSobolevInclusion (s t : ℝ) :
    ManifoldSobolev p η hηc hηs hηm s →L[ℝ] ManifoldSobolev p η hηc hηs hηm t :=
  (smoothToManifoldSobolev p η hηc hηs hηm t).extendOfNorm
    (smoothToManifoldSobolev p η hηc hηs hηm s)

omit [CompactSpace M] in
lemma manifoldSobolevInclusion_smooth (s t : ℝ) (h : t ≤ s)
    (f : ManifoldSmoothFunctions E M) :
    manifoldSobolevInclusion p η hηc hηs hηm s t
      (smoothToManifoldSobolev p η hηc hηs hηm s f) =
      smoothToManifoldSobolev p η hηc hηs hηm t f := by
  apply LinearMap.extendOfNorm_eq (denseRange_smoothToManifoldSobolev p η hηc hηs hηm s)
  refine ⟨1, fun u => ?_⟩
  simpa only [one_mul] using norm_smoothToManifoldSobolev_mono p η hηc hηs hηm s t h u

lemma manifoldSobolevInclusion_representative (hηone : ∀ x, ∑ i, η i x = 1)
    (s t : ℝ) (h : t ≤ s) (ht : Module.finrank ℝ E < 2 * t)
    (u : ManifoldSobolev p η hηc hηs hηm s) :
    manifoldSobolevRepresentative p η hηc hηs hηm t
        (manifoldSobolevInclusion p η hηc hηs hηm s t u) =
      manifoldSobolevRepresentative p η hηc hηs hηm s u := by
  have hs : Module.finrank ℝ E < 2 * s := by linarith
  refine (denseRange_smoothToManifoldSobolev p η hηc hηs hηm s).induction_on u ?_ ?_
  · apply isClosed_eq
    · exact (manifoldSobolevRepresentative p η hηc hηs hηm t).continuous.comp
        (manifoldSobolevInclusion p η hηc hηs hηm s t).continuous
    · exact (manifoldSobolevRepresentative p η hηc hηs hηm s).continuous
  · intro f
    rw [manifoldSobolevInclusion_smooth p η hηc hηs hηm s t h,
      manifoldSobolevRepresentative_smooth p η hηc hηs hηm hηone ht,
      manifoldSobolevRepresentative_smooth p η hηc hηs hηm hηone hs]



end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ContMDiffComplexMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_controlled_coordinate_extension (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ ∞ e e.source) (he' : ContDiffOn ℝ ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hs : K ⊆ e.source) :
    ∃ ψ : E → E, ContDiff ℝ ∞ ψ ∧ e =ᶠ[𝓝ˢ K] ψ ∧ Set.InjOn ψ K ∧
      ∃ J : ℝ≥0, ∀ x ∈ K, 1 ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(fderiv ℝ ψ x).det| := by
  obtain ⟨ψ, hψ, heq⟩ := smooth_extension_near_compact hK e.open_source hs he
  have heqx (x : E) (hx : x ∈ K) : (e : E → E) =ᶠ[𝓝 x] ψ :=
    heq.filter_mono (nhds_le_nhdsSet hx)
  refine ⟨ψ, hψ, heq, ?_, ?_⟩
  · intro x hx y hy hxy
    apply e.injOn (hs hx) (hs hy)
    simpa only [(heqx x hx).eq_of_nhds, (heqx y hy).eq_of_nhds] using hxy
  · apply compact_jacobian_bound hK hψ
    intro x hx
    rw [← (heqx x hx).fderiv_eq]
    exact local_diffeomorphism_det_ne_zero e he he' (hs hx)


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open scoped SchwartzMap ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [T2Space M] in

theorem chartLift_localization_bound (p q : M) (η χ : M → ℂ)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ (chartAt E p).source)
    (hηm : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ η)
    (hχs : tsupport χ ⊆ (chartAt E q).source)
    (hχm : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ χ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : 𝓢(E, ℂ),
      ‖schwartzToSobolev (2 * (k : ℝ))
        (chartSchwartz p η (chartLift q χ f) hηc hηs hηm
          (contMDiff_chartLift q χ hχs hχm (f.smooth ⊤)))‖ ≤
        C * ‖schwartzToSobolev (2 * (k : ℝ)) f‖ := by
  let κ := chartLocalize (E := E) p (η * χ) (fun _ => 1)
  have hpc : HasCompactSupport (η * χ) := hηc.mul_right
  have hps : tsupport (η * χ) ⊆ (chartAt E p).source := tsupport_mul_subset_left.trans hηs
  have hκc : HasCompactSupport κ := hasCompactSupport_chartLocalize p _ _ hpc hps
  have hκm : ContDiff ℝ ∞ κ := contDiff_chartLocalize p _ _ hpc hps
    (contMDiff_complex_mul hηm hχm) contMDiff_const
  let e := (chartAt E p).symm.trans (chartAt E q)
  have he : ContDiffOn ℝ ∞ e e.source := contDiffOn_chartTransition p q
  have he' : ContDiffOn ℝ ∞ e.symm e.target := contDiffOn_chartTransition q p
  have hκs : tsupport κ ⊆ e.source := chart_overlap_cutoff_support p q η χ hηc hηs hχs
  obtain ⟨ψ, hψ, heψ, hψinj, J, hJ⟩ := exists_controlled_coordinate_extension e he he' hκc hκs
  obtain ⟨C, hC, hb⟩ := cutoffPullback_sobolev_bound κ hκc hκm ψ hψ hψinj J hJ k
  refine ⟨C, hC, fun f => ?_⟩
  have hid : chartSchwartz p η (chartLift q χ f) hηc hηs hηm
      (contMDiff_chartLift q χ hχs hχm (f.smooth ⊤)) = cutoffPullback κ hκc hκm ψ hψ f := by
    ext y
    change chartLocalize p η (chartLift q χ f) y = κ y * f (ψ y)
    rw [chartLocalize_chartLift]
    change κ y * f (e y) = κ y * f (ψ y)
    by_cases hy : y ∈ tsupport κ
    · rw [(heψ.filter_mono (nhds_le_nhdsSet hy)).eq_of_nhds]
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, zero_mul]
  rw [hid]
  exact hb f



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_MetricPatchSource
attribute [-instance] _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
namespace YauCounterexamples
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def metricPatchSource (p : M) (r : ℝ) (k : ℕ) :
    FourierSobolevSpace E ℂ (2 * (k : ℝ)) →L[ℂ] FourierSobolevSpace E ℂ (2 * (k : ℝ)) :=
  (r : ℂ) ^ 2 • sobolevAffineCutoff (complexUnitBump E) (hasCompactSupport_complexUnitBump E)
    (contDiff_complexUnitBump E) ((chartAt E p) p) r k

def metricPatchRawInverse (g : SmoothMetric E M) (p : M) (k : ℕ)
    (hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ)))
    (D : LocalMetricInverse g p (2 * (k : ℝ)) hs)
    (α : ℝ) (hα : 1 ≤ α * D.radius ^ 2) :
    FourierSobolevSpace E ℂ (2 * (k : ℝ)) →L[ℂ]
      FourierSobolevSpace E ℂ (2 * (k : ℝ) + 2) :=
  D.inverse (α * D.radius ^ 2) hα ∘L metricPatchSource (E := E) p D.radius k

lemma metricPatchRawInverse_half_bound (g : SmoothMetric E M) (p : M) (k : ℕ)
    (hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ)))
    (D : LocalMetricInverse g p (2 * (k : ℝ)) hs)
    (α : ℝ) (hα : 1 ≤ α * D.radius ^ 2)
    (f : FourierSobolevSpace E ℂ (2 * (k : ℝ))) :
    ‖sobolevInclusion (2 * (k : ℝ) + 2) (2 * (k : ℝ) + 1) (by linarith)
        (metricPatchRawInverse g p k hs D α hα f)‖ ≤
      (D.bound * ‖metricPatchSource (E := E) p D.radius k‖) *
        (Real.sqrt (α * D.radius ^ 2))⁻¹ * ‖f‖ := by
  apply (D.half_bound _ hα _).trans
  calc
    D.bound * (Real.sqrt (α * D.radius ^ 2))⁻¹ * ‖metricPatchSource (E := E) p D.radius k f‖ ≤
      D.bound * (Real.sqrt (α * D.radius ^ 2))⁻¹ *
        (‖metricPatchSource (E := E) p D.radius k‖ * ‖f‖) :=
      mul_le_mul_of_nonneg_left ((metricPatchSource (E := E) p D.radius k).le_opNorm f)
        (mul_nonneg D.bound_pos.le (inv_nonneg.mpr (Real.sqrt_nonneg _)))
    _ = _ := by ring

end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartDerivativeNeZeroTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] {ι : Type*} [Fintype ι]
variable (p : ι → M) (η : ι → M → ℂ)
    (hηc : ∀ i, HasCompactSupport (η i))
    (hηs : ∀ i, tsupport (η i) ⊆ (chartAt E (p i)).source)
    (hηm : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η i))
    (hηone : ∀ x, ∑ i, η i x = 1)

include hηone

theorem manifoldSobolevRepresentative_localize
    {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (u : ManifoldSobolev p η hηc hηs hηm s) (i : ι) (y : E) :
    sobolevRepresentative hs (u.val i) y = chartLocalize (E := E) (p i) (η i)
      (manifoldSobolevRepresentative p η hηc hηs hηm s u) y := by
  classical
  refine (denseRange_smoothToManifoldSobolev p η hηc hηs hηm s).induction_on u ?_ ?_
  · apply isClosed_eq
    · exact (BoundedContinuousFunction.evalCLM ℂ y).continuous.comp
        ((sobolevRepresentative hs).continuous.comp
          ((continuous_apply i).comp continuous_subtype_val))
    · unfold chartLocalize
      split_ifs <;> fun_prop
  · intro f
    rw [manifoldSobolevRepresentative_smooth p η hηc hηs hηm hηone hs]
    change sobolevRepresentative hs
      (schwartzToSobolev s (chartSchwartz (p i) (η i) f (hηc i) (hηs i) (hηm i) f.contMDiff)) y = _
    rw [sobolevRepresentative_schwartz]
    rfl

theorem manifoldSobolevRepresentative_injective
    {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) :
    Function.Injective (manifoldSobolevRepresentative p η hηc hηs hηm s) := by
  intro u v huv
  apply Subtype.ext
  funext i
  apply fourierSobolevDistribution_injective
  rw [← sobolevRepresentative_distribution hs, ← sobolevRepresentative_distribution hs]
  congr 1
  ext y
  simp only [manifoldSobolevRepresentative_localize p η hηc hηs hηm hηone hs, huv]


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open scoped SchwartzMap ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] {ι : Type*} [Fintype ι]
variable (p : ι → M) (η : ι → M → ℂ)
    (hηc : ∀ i, HasCompactSupport (η i))
    (hηs : ∀ i, tsupport (η i) ⊆ (chartAt E (p i)).source)
    (hηm : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η i))
variable (q : M) (χ : M → ℂ) (hχs : tsupport χ ⊆ (chartAt E q).source)
    (hχm : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ χ)

omit [CompactSpace M] in
lemma chartLiftToManifoldSobolev_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝓢(E, ℂ),
      ‖chartLiftToManifoldSobolev p η hηc hηs hηm q χ hχs hχm (2 * (k : ℝ)) f‖ ≤
        C * ‖schwartzToSobolev (2 * (k : ℝ)) f‖ := by
  classical
  choose C hC hb using fun i => chartLift_localization_bound
    (p i) q (η i) χ (hηc i) (hηs i) (hηm i) hχs hχm k
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => (hC i).le), fun f => ?_⟩
  change ‖(chartLiftToManifoldSobolev p η hηc hηs hηm q χ hχs hχm (2 * (k : ℝ)) f).val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg (fun i _ => (hC i).le)) (norm_nonneg _))).mpr
  intro i
  exact (hb i f).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)) (norm_nonneg _))

omit [CompactSpace M] in
lemma sobolevChartLift_schwartz (k : ℕ) (f : 𝓢(E, ℂ)) :
    sobolevChartLift p η hηc hηs hηm q χ hχs hχm k (schwartzToSobolev (2 * (k : ℝ)) f) =
      smoothToManifoldSobolev p η hηc hηs hηm (2 * (k : ℝ))
        (chartLiftSmoothLinear q χ hχs hχm f) := by
  obtain ⟨C, _, hC⟩ := chartLiftToManifoldSobolev_bound p η hηc hηs hηm q χ hχs hχm k
  exact LinearMap.extendOfNorm_eq
    (f := chartLiftToManifoldSobolev p η hηc hηs hηm q χ hχs hχm (2 * (k : ℝ)))
    (e := ((schwartzToSobolev (2 * (k : ℝ))).restrictScalars ℝ).toLinearMap)
    (denseRange_schwartzToSobolev (E := E) (2 * (k : ℝ))) ⟨C, hC⟩ f

lemma sobolevChartLift_representative (hηone : ∀ x, ∑ i, η i x = 1)
    (k : ℕ) (hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ)))
    (u : FourierSobolevSpace E ℂ (2 * (k : ℝ))) (x : M) :
    manifoldSobolevRepresentative p η hηc hηs hηm (2 * (k : ℝ))
      (sobolevChartLift p η hηc hηs hηm q χ hχs hχm k u) x =
      χ x * sobolevRepresentative hs u (chartAt E q x) := by
  refine (denseRange_schwartzToSobolev (E := E) (2 * (k : ℝ))).induction_on u ?_ ?_
  · apply isClosed_eq
    · exact (BoundedContinuousFunction.evalCLM ℝ x).continuous.comp
        ((manifoldSobolevRepresentative p η hηc hηs hηm (2 * (k : ℝ))).continuous.comp
          (sobolevChartLift p η hηc hηs hηm q χ hχs hχm k).continuous)
    · exact continuous_const.mul ((BoundedContinuousFunction.evalCLM ℂ (chartAt E q x)).continuous.comp
        (sobolevRepresentative hs).continuous)
  · intro f
    rw [sobolevChartLift_schwartz, manifoldSobolevRepresentative_smooth p η hηc hηs hηm hηone hs,
      sobolevRepresentative_schwartz]
    rfl


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M]
  {ι : Type*} [Fintype ι]
variable (p : ι → M) (η : ι → M → ℂ)
    (hηc : ∀ i, HasCompactSupport (η i))
    (hηs : ∀ i, tsupport (η i) ⊆ (chartAt E (p i)).source)
    (hηm : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η i))
    (χ : ι → M → ℂ) (hχs : ∀ i, tsupport (χ i) ⊆ (chartAt E (p i)).source)
    (hχm : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (χ i))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompactSpace M]
  [Fintype ι] in
lemma contMDiff_chartLift_finite (q : M) (ξ : M → ℂ)
    (hξs : tsupport ξ ⊆ (chartAt E q).source)
    (hξ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ ξ) (N : ℕ)
    {f : E → ℂ} (hf : ContDiff ℝ N f) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) N (chartLift (E := E) q ξ f) := by
  have hN : (N : ℕ∞ω) ≤ (∞ : ℕ∞ω) := ENat.natCast_le_of_coe_top_le_withTop le_rfl N
  apply contMDiff_of_tsupport
  intro x hx
  have hxs : x ∈ (chartAt E q).source := hξs (tsupport_mul_subset_left hx)
  exact ((ContinuousLinearMap.mul ℝ ℂ).contMDiff.contMDiffAt.comp x
    (hξ.of_le hN).contMDiffAt).clm_apply
    ((contMDiff_iff_contDiff.mpr hf).contMDiffAt.comp x
      ((contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) hxs).of_le hN))

include hηs hχs in
lemma manifoldSobolevRepresentative_eq_sum
    (hηone : ∀ x, ∑ i, η i x = 1) (hχone : ∀ i, EqOn (χ i) 1 (tsupport (η i)))
    {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (u : ManifoldSobolev p η hηc hηs hηm s) (x : M) :
    manifoldSobolevRepresentative p η hηc hηs hηm s u x =
      ∑ i, chartLift (E := E) (p i) (χ i) (sobolevRepresentative hs (u.val i)) x := by
  have he (i : ι) : (sobolevRepresentative hs (u.val i) : E → ℂ) =
      chartLocalize (E := E) (p i) (η i)
        (manifoldSobolevRepresentative p η hηc hηs hηm s u) := by
    funext y
    exact manifoldSobolevRepresentative_localize p η hηc hηs hηm hηone hs u i y
  simp only [he]
  exact (atlasGluing_partition_identity p η hηs χ hχs hηone hχone _ x).symm

include hχs hχm in

theorem contMDiff_manifoldSobolevRepresentative
    (hηone : ∀ x, ∑ i, η i x = 1) (hχone : ∀ i, EqOn (χ i) 1 (tsupport (η i)))
    {s : ℝ} (N : ℕ) (hs : Module.finrank ℝ E < 2 * (s - N))
    (u : ManifoldSobolev p η hηc hηs hηm s) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) N
      (manifoldSobolevRepresentative p η hηc hηs hηm s u : M → ℂ) := by
  have ht : Module.finrank ℝ E < 2 * s := by
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have he : (manifoldSobolevRepresentative p η hηc hηs hηm s u : M → ℂ) =
      fun x => ∑ i, chartLift (E := E) (p i) (χ i) (sobolevRepresentative ht (u.val i)) x := by
    funext x
    exact manifoldSobolevRepresentative_eq_sum p η hηc hηs hηm χ hχs hηone hχone ht u x
  rw [he]
  apply ContMDiff.sum
  intro i _
  exact contMDiff_chartLift_finite (p i) (χ i) (hχs i) (hχm i) N
    (contDiff_sobolevRepresentative N hs ht (u.val i))



end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma lift_representative (q : M) (ξ : M → ℂ) (hξs : tsupport ξ ⊆ (chartAt E q).source)
    (hξ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ ξ) (l : ℕ)
    (hl : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (f : FourierSobolevSpace E ℂ (2 * (l : ℝ))) (x : M) :
    A.representative (2 * (l : ℝ)) (A.lift q ξ hξs hξ l f) x =
      ξ x * sobolevRepresentative hl f ((chartAt E q) x) :=
  sobolevChartLift_representative A.p A.η
    (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η
    q ξ hξs hξ A.sum_η l hl f x

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def patchErrorTail (i : A.t) (B : A.PatchCoefficients i) :
    FourierSobolevSpace E ℂ (2 * (k : ℝ) + 1) →L[ℝ] A.H (2 * (k : ℝ)) :=
  A.lift (A.p i) (A.ψ i) (A.chart_ψ i) (A.smooth_ψ i) k ∘L
    (sobolevAffineCutoff (A.ψcoord i) (A.compact_ψcoord i) (A.smooth_ψcoord i)
      (-((A.localInverse i).radius⁻¹ • (chartAt E (A.p i)) (A.p i)))
      (A.localInverse i).radius⁻¹ k).restrictScalars ℝ ∘L
    (rescaledCommutatorSobolev hs (Module.finBasis ℝ E) B.a B.c B.smooth_a B.smooth_c
      (A.χcoord i) (A.smooth_χcoord i) (A.compact_χcoord i)
      ((chartAt E (A.p i)) (A.p i)) (A.localInverse i).radius
      (A.localInverse i).radius_pos.ne').restrictScalars ℝ

def patchError (α : ℝ) (i : A.t) (B : A.PatchCoefficients i)
    (hα : 1 ≤ α * (A.localInverse i).radius ^ 2) :
    A.H (2 * (k : ℝ)) →L[ℝ] A.H (2 * (k : ℝ)) :=
  A.patchErrorTail i B ∘L
    (sobolevInclusion (2 * (k : ℝ) + 2) (2 * (k : ℝ) + 1) (by linarith)).restrictScalars ℝ ∘L
    (metricPatchRawInverse g (A.p i) k hs (A.localInverse i) α hα).restrictScalars ℝ ∘L
    A.localize (2 * (k : ℝ)) i

omit [T2Space M] in
lemma patchError_bound (α : ℝ) (i : A.t) (B : A.PatchCoefficients i)
    (hα : 1 ≤ α * (A.localInverse i).radius ^ 2) (f : A.H (2 * (k : ℝ))) :
    ‖A.patchError α i B hα f‖ ≤
      (‖A.patchErrorTail i B‖ * ((A.localInverse i).bound *
        ‖metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k‖)) *
      (Real.sqrt (α * (A.localInverse i).radius ^ 2))⁻¹ * ‖f‖ := by
  have hf : ‖f.val i‖ ≤ ‖f‖ := norm_le_pi_norm f.val i
  apply ((A.patchErrorTail i B).le_opNorm _).trans
  apply (mul_le_mul_of_nonneg_left
    (metricPatchRawInverse_half_bound g (A.p i) k hs (A.localInverse i) α hα (f.val i))
    (norm_nonneg _)).trans
  calc
    _ ≤ ‖A.patchErrorTail i B‖ *
        (((A.localInverse i).bound * ‖metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k‖) *
          (Real.sqrt (α * (A.localInverse i).radius ^ 2))⁻¹ * ‖f‖) := by
      apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf
        (mul_nonneg (mul_nonneg (A.localInverse i).bound_pos.le (norm_nonneg _))
          (inv_nonneg.mpr (Real.sqrt_nonneg _)))) (norm_nonneg _)
    _ = _ := by ring
end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma localize_representative (u : A.H (2 * (k : ℝ))) (i : A.t) (y : E) :
    sobolevRepresentative hs (u.val i) y =
      chartLocalize (E := E) (A.p i) (A.η i) (A.representative (2 * (k : ℝ)) u) y :=
  manifoldSobolevRepresentative_localize A.p A.η
    (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η A.sum_η hs u i y

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def error (B : ∀ i, A.PatchCoefficients i) (α : ℝ)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2) :
    A.H (2 * (k : ℝ)) →L[ℝ] A.H (2 * (k : ℝ)) :=
  ∑ i, A.patchError α i (B i) (hα i)

def errorBound (B : ∀ i, A.PatchCoefficients i) (α : ℝ) : ℝ :=
  ∑ i, (‖A.patchErrorTail i (B i)‖ * ((A.localInverse i).bound *
    ‖metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k‖)) *
    (Real.sqrt (α * (A.localInverse i).radius ^ 2))⁻¹

omit [T2Space M] in
lemma errorBound_nonneg (B : ∀ i, A.PatchCoefficients i) (α : ℝ) : 0 ≤ A.errorBound B α := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (A.patchErrorTail i (B i)).opNorm_nonneg (mul_nonneg (A.localInverse i).bound_pos.le
    (metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k).opNorm_nonneg)) (inv_nonneg.mpr (Real.sqrt_nonneg _))

omit [T2Space M] in
lemma error_norm_bound (B : ∀ i, A.PatchCoefficients i) (α : ℝ)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2) :
    ‖A.error B α hα‖ ≤ A.errorBound B α := by
  apply ContinuousLinearMap.opNorm_le_bound _ (A.errorBound_nonneg B α)
  intro u
  calc
    ‖A.error B α hα u‖ ≤ ∑ i, ‖A.patchError α i (B i) (hα i) u‖ := by
      simpa only [error, sum_apply] using norm_sum_le _ _
    _ ≤ ∑ i, (‖A.patchErrorTail i (B i)‖ * ((A.localInverse i).bound *
        ‖metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k‖)) *
        (Real.sqrt (α * (A.localInverse i).radius ^ 2))⁻¹ * ‖u‖ :=
      Finset.sum_le_sum (fun i _ => A.patchError_bound α i (B i) (hα i) u)
    _ = A.errorBound B α * ‖u‖ := (Finset.sum_mul ..).symm

omit [T2Space M] in
lemma representative_C2 (u : A.H (2 * ((k + 1 : ℕ) : ℝ))) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2
      (A.representative (2 * ((k + 1 : ℕ) : ℝ)) u : M → ℂ) := by
  apply contMDiff_manifoldSobolevRepresentative A.p A.η
    (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η
    A.χ A.chart_χ A.smooth_χ A.sum_η
    (fun i x hx => (A.one_χ i).self_of_nhdsSet hx) 2 _ u
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  linarith

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma error_lt_one (B : ∀ i, A.PatchCoefficients i) (α : ℝ)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) :
    ‖ContinuousLinearMap.id ℝ (A.H (2 * (k : ℝ))) ∘L A.error B α hα‖ < 1 := by
  rw [ContinuousLinearMap.id_comp]
  exact lt_of_le_of_lt ((A.error_norm_bound B α hα).trans he) (by norm_num)

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma ofSmooth_representative (s : ℝ) (ht : Module.finrank ℝ E < 2 * s)
    (f : ManifoldSmoothFunctions E M) :
    (A.representative s (A.ofSmooth s f) : M → ℂ) = f := by
  exact congrArg (fun z : M →ᵇ ℂ => (z : M → ℂ))
    (manifoldSobolevRepresentative_smooth A.p A.η
      (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η A.sum_η ht f)

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction SchwartzMap
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
def smoothMul (f h : ManifoldSmoothFunctions E M) : ManifoldSmoothFunctions E M :=
  ⟨fun x => f x * h x, contMDiff_complex_mul f.contMDiff h.contMDiff⟩

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma smoothCutoffLocalization_bound (q : M) (ξ : M → ℂ)
    (hξs : tsupport ξ ⊆ (chartAt E q).source)
    (hξ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ ξ) (l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ManifoldSmoothFunctions E M,
      ‖smoothCutoffLocalization q ξ hξs hξ l f‖ ≤ C * ‖A.ofSmooth (2 * (l : ℝ)) f‖ := by
  choose C hC hb using fun i => chartLift_localization_bound q (A.p i) ξ (A.χ i)
    (HasCompactSupport.of_compactSpace ξ) hξs hξ (A.chart_χ i) (A.smooth_χ i) l
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => (hC i).le), fun f => ?_⟩
  have he := congrArg (smoothCutoffLocalization q ξ hξs hξ l) (A.smooth_partition f)
  rw [map_sum] at he
  rw [← he]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i, C i * ‖schwartzToSobolev (2 * (l : ℝ))
        (chartSchwartzLinear (A.p i) (A.η i) (HasCompactSupport.of_compactSpace _)
          (A.chart_η i) (A.smooth_η i) f)‖ := Finset.sum_le_sum (fun i _ => hb i _)
    _ ≤ ∑ i, C i * ‖A.ofSmooth (2 * (l : ℝ)) f‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hC i).le
      exact norm_le_pi_norm (A.ofSmooth (2 * (l : ℝ)) f).val i
    _ = _ := (Finset.sum_mul ..).symm

omit [T2Space M] in
lemma cutoffLocalization_smooth (q : M) (ξ : M → ℂ)
    (hξs : tsupport ξ ⊆ (chartAt E q).source)
    (hξ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ ξ) (l : ℕ) (f : ManifoldSmoothFunctions E M) :
    A.cutoffLocalization q ξ hξs hξ l (A.ofSmooth (2 * (l : ℝ)) f) =
      smoothCutoffLocalization q ξ hξs hξ l f := by
  obtain ⟨C, _, hb⟩ := A.smoothCutoffLocalization_bound q ξ hξs hξ l
  exact LinearMap.extendOfNorm_eq
    (denseRange_smoothToManifoldSobolev A.p A.η
      (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η _) ⟨C, hb⟩ f

omit [T2Space M] in
lemma cutoffLocalization_representative (q : M) (ξ : M → ℂ)
    (hξs : tsupport ξ ⊆ (chartAt E q).source)
    (hξ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ ξ) (l : ℕ)
    (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ))) (f : A.H (2 * (l : ℝ))) (y : E) :
    sobolevRepresentative ht (A.cutoffLocalization q ξ hξs hξ l f) y =
      chartLocalize (E := E) q ξ (A.representative (2 * (l : ℝ)) f) y := by
  refine (denseRange_smoothToManifoldSobolev A.p A.η
    (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η _).induction_on f ?_ ?_
  · apply isClosed_eq
    · exact (BoundedContinuousFunction.evalCLM ℂ y).continuous.comp
        ((sobolevRepresentative ht).continuous.comp (A.cutoffLocalization q ξ hξs hξ l).continuous)
    · unfold chartLocalize
      split_ifs <;> fun_prop
  · intro u
    change sobolevRepresentative ht
      (A.cutoffLocalization q ξ hξs hξ l (A.ofSmooth (2 * (l : ℝ)) u)) y = _
    rw [A.cutoffLocalization_smooth]
    change sobolevRepresentative ht (schwartzToSobolev (2 * (l : ℝ))
      (chartSchwartzLinear q ξ (HasCompactSupport.of_compactSpace ξ) hξs hξ u)) y = _
    rw [sobolevRepresentative_schwartz]
    change chartLocalize (E := E) q ξ u y =
      chartLocalize (E := E) q ξ (A.representative (2 * (l : ℝ)) (A.ofSmooth (2 * (l : ℝ)) u)) y
    rw [A.ofSmooth_representative _ ht u]

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction SchwartzMap
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
lemma chartLocalize_eventually_eq (p : M) (χ u : M → ℂ) {x : M}
    (hx : x ∈ (chartAt E p).source) (hχ : χ =ᶠ[𝓝 x] 1) :
    chartLocalize (E := E) p χ u =ᶠ[𝓝 ((chartAt E p) x)] u ∘ (chartAt E p).symm := by
  have hy := (chartAt E p).map_source hx
  have hc' := ((chartAt E p).continuousAt_symm hy).tendsto
  rw [(chartAt E p).left_inv hx] at hc'
  have hc := hχ.comp_tendsto hc'
  filter_upwards [hc, (chartAt E p).open_target.mem_nhds hy] with y hcy hty
  change χ ((chartAt E p).symm y) = 1 at hcy
  rw [chartLocalize_eq _ _ _ hty, hcy, one_mul]
  rfl

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def metricCoefficientSchwartz (i : A.t) (f : E → ℝ) (hf : ContDiff ℝ ∞ f) : 𝓢(E, ℂ) :=
  (show HasCompactSupport (fun y => A.χcoord i y * (f y : ℂ)) from
    (A.compact_χcoord i).mul_right).toSchwartzMap
    ((A.smooth_χcoord i).mul (Complex.ofRealCLM.contDiff.comp hf))

def laplacianPatch (i : A.t) (B : A.PatchCoefficients i) :
    FourierSobolevSpace E ℂ (2 * ((k + 1 : ℕ) : ℝ)) →L[ℝ] A.H (2 * (k : ℝ)) :=
  A.lift (A.p i) (A.η i) (A.chart_η i) (A.smooth_η i) k ∘L
    (coefficientPerturbation (Module.finBasis ℝ E) hs
      (fun j l => schwartzToSobolev (2 * (k : ℝ))
        (A.metricCoefficientSchwartz i (B.a j l) (B.smooth_a j l)))
      (fun j => schwartzToSobolev (2 * (k : ℝ))
        (A.metricCoefficientSchwartz i (B.c j) (B.smooth_c j)))).restrictScalars ℝ

def laplacianCLM (B : ∀ i, A.PatchCoefficients i) :
    A.H (2 * ((k + 1 : ℕ) : ℝ)) →L[ℝ] A.H (2 * (k : ℝ)) :=
  ∑ i, A.laplacianPatch i (B i) ∘L
    A.cutoffLocalization (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i) (k + 1)

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

abbrev realH (s : ℝ) : Submodule ℝ (A.H s) where
  carrier := {u | ∀ x, (A.representative s u x).im = 0}
  zero_mem' := by simp
  add_mem' := by intro u v hu hv x; simp only [map_add, BoundedContinuousFunction.add_apply, Complex.add_im, hu x, hv x, add_zero]
  smul_mem' := by intro c u hu x; simp only [map_smul, BoundedContinuousFunction.smul_apply, Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hu x, mul_zero, zero_mul, add_zero]

@[reducible] instance realH_nacg (s : ℝ) : NormedAddCommGroup (A.realH s) := inferInstance
@[reducible] instance realH_snacg (s : ℝ) : SeminormedAddCommGroup (A.realH s) := inferInstance
@[reducible] instance realH_acg (s : ℝ) : AddCommGroup (A.realH s) := inferInstance
@[reducible] instance realH_ns (s : ℝ) : NormedSpace ℝ (A.realH s) := inferInstance
@[reducible] instance realH_mod (s : ℝ) : Module ℝ (A.realH s) := inferInstance

omit [T2Space M] in
lemma realH_coe_representative (s : ℝ) (u : A.realH s) (x : M) :
    (((A.representative s u x).re : ℝ) : ℂ) = A.representative s u x := by
  apply Complex.ext
  · rfl
  · exact (u.property x).symm

def inclusion : A.H (2 * ((k + 1 : ℕ) : ℝ)) →L[ℝ] A.H (2 * (k : ℝ)) :=
  manifoldSobolevInclusion A.p A.η (fun _ => HasCompactSupport.of_compactSpace _)
    A.chart_η A.smooth_η _ _

omit [T2Space M] in
lemma inclusion_representative (u : A.H (2 * ((k + 1 : ℕ) : ℝ))) :
    A.representative (2 * (k : ℝ)) (A.inclusion u) =
      A.representative (2 * ((k + 1 : ℕ) : ℝ)) u :=
  manifoldSobolevInclusion_representative A.p A.η
    (fun _ => HasCompactSupport.of_compactSpace _) A.chart_η A.smooth_η A.sum_η _ _
    (by push_cast; linarith) hs u

end CompactMetricAtlas

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def realValue (s : ℝ) (u : A.realH s) (x : M) : ℝ := (A.representative s u x).re

omit [T2Space M] in
lemma ofReal_realValue (s : ℝ) (u : A.realH s) (x : M) :
    (A.realValue s u x : ℂ) = A.representative s u x := A.realH_coe_representative s u x

end CompactMetricAtlas

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)
omit [CompactSpace M] [T2Space M] in
lemma highIndex_bound : Module.finrank ℝ E < 2*A.highIndex := by
  have h := hs
  dsimp [highIndex]; push_cast; linarith
end CompactMetricAtlas

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_JointMetricDet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction SchwartzMap
namespace YauCounterexamples
section JointMetricCoefficients
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
variable (q : ℝ → SmoothMetric E M) (p : M)
variable (hq : ∀ t y, y ∈ (chartAt E p).target → ∀ i j,
  ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (q z.1) p z.2 i j) (t,y))

include hq
lemma joint_metricDet (t : ℝ) {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => (metricCoefficients (q z.1) p z.2).det) (t,y) := by
  classical
  simp only [Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ _
  apply contDiffAt_const.mul
  apply contDiffAt_prod
  intro i _
  exact hq t y hy _ _

lemma joint_metricDensity (t : ℝ) {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => Real.sqrt (metricCoefficients (q z.1) p z.2).det) (t,y) :=
  (joint_metricDet q p hq t hy).sqrt (metricCoefficients_det_pos (q t) p hy).ne'

lemma joint_metricInverse (t : ℝ) {y : E} (hy : y ∈ (chartAt E p).target) (i j : CoordIndex E) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => (metricCoefficients (q z.1) p z.2)⁻¹ i j) (t,y) := by
  classical
  have hadj : ContDiffAt ℝ ∞ (fun z : ℝ × E =>
      (metricCoefficients (q z.1) p z.2).adjugate i j) (t,y) := by
    simp only [Matrix.adjugate_apply, Matrix.det_apply']
    apply ContDiffAt.sum
    intro σ _
    apply contDiffAt_const.mul
    apply contDiffAt_prod
    intro k _
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact contDiffAt_const
    · exact hq t y hy _ _
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
  exact ((joint_metricDet q p hq t hy).inv (metricCoefficients_det_pos (q t) p hy).ne').mul hadj

lemma joint_metricFirstCoefficient (t : ℝ) {y : E} (hy : y ∈ (chartAt E p).target) (j : CoordIndex E) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => metricFirstCoefficient (q z.1) p j z.2) (t,y) := by
  have hd := joint_metricDensity q p hq t hy
  have hn := (Real.sqrt_pos.mpr (metricCoefficients_det_pos (q t) p hy)).ne'
  apply (hd.inv hn).mul
  apply ContDiffAt.sum
  intro i _
  have ha := joint_metricInverse q p hq t hy i j
  have hf : ContDiffAt ℝ ∞ (fun w : (ℝ × E) × E =>
      Real.sqrt (metricCoefficients (q w.1.1) p w.2).det *
      (metricCoefficients (q w.1.1) p w.2)⁻¹ i j) ((t,y),y) := by
    simpa only [Function.comp_def] using (hd.mul ha).comp ((t,y),y)
      (show ContDiffAt ℝ ∞ (fun w : (ℝ × E) × E => (w.1.1,w.2)) ((t,y),y) from
        contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact (hf.fderiv contDiffAt_snd (by simp)).clm_apply contDiffAt_const
end JointMetricCoefficients

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_JointLocalLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma differentiableAt_metricFlux {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    DifferentiableAt ℝ (metricFlux g u p) y := by
  apply differentiableAt_pi.mpr
  intro i
  have hd := ((contDiffOn_metricDensity g p).contDiffAt
    ((chartAt E p).open_target.mem_nhds hy)).differentiableAt (by simp)
  apply hd.mul
  apply DifferentiableAt.fun_sum
  intro j _
  have ha := ((contDiffOn_metricInverse g p i j).contDiffAt
    ((chartAt E p).open_target.mem_nhds hy)).differentiableAt (by simp)
  have hu' := ((contDiffAt_inChart hu p hy).fderiv_right (m := 1) (by rw [one_add_one_eq_two]; exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).differentiableAt one_ne_zero
  exact ha.mul (hu'.clm_apply (differentiableAt_const _))

lemma localLaplacian_change {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p q : M) {y : E} (hy : y ∈ (chartAt E q).target)
    (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    localLaplacian g u q y = localLaplacian g u p (chartTransition p q y) := by
  classical
  have he (i : CoordIndex E) : (fun z => metricFlux g u q z i) =ᶠ[𝓝 y]
      (fun z => ∑ k, |(coordinateTransitionMatrix p q z).det| *
        (coordinateTransitionMatrix p q z)⁻¹ i k * metricFlux g u p (chartTransition p q z) k) := by
    filter_upwards [chart_overlap_nhds p q hy hp] with z hz
    exact metricFlux_change hu g p q hz.1 hz.2 i
  have hJ : IsUnit (coordinateTransitionMatrix p q y).det :=
    isUnit_iff_ne_zero.mpr (coordinateTransitionMatrix_det_ne_zero g p q hy hp)
  have hi := piola_divergence_abs ((contDiffAt_chartTransition p q hy hp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (differentiableAt_metricFlux hu g p ((chartAt E p).map_source hp))
    (Module.finBasis ℝ E) hJ
  change (∑ i, fderiv ℝ (fun z => ∑ k, |(coordinateTransitionMatrix p q z).det| *
    (coordinateTransitionMatrix p q z)⁻¹ i k * metricFlux g u p (chartTransition p q z) k) y
      (Module.finBasis ℝ E i)) = _ at hi
  simp only [localLaplacian, (he _).fderiv_eq]
  rw [hi, metricDensity_change g p q hy hp]
  have hn := abs_ne_zero.mpr (coordinateTransitionMatrix_det_ne_zero g p q hy hp)
  change (|(coordinateTransitionMatrix p q y).det| * _)⁻¹ *
    (|(coordinateTransitionMatrix p q y).det| * _) = _
  field_simp

lemma laplaceBeltrami_inChart {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p x : M) (hx : x ∈ (chartAt E p).source) :
    laplaceBeltrami g u x = localLaplacian g u p (chartAt E p x) := by
  change localLaplacian g u x (chartAt E x x) = _
  have he := localLaplacian_change hu g p x ((chartAt E x).map_source (mem_chart_source E x))
    (by simpa only [(chartAt E x).left_inv (mem_chart_source E x)] using hx)
  simpa only [chartTransition, Function.comp_apply, (chartAt E x).left_inv (mem_chart_source E x)] using he

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction
section JointLocalLaplacian
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
variable (q : ℝ → SmoothMetric E M)
variable (hq : ∀ p t y, y ∈ (chartAt E p).target → ∀ i j,
  ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (q z.1) p z.2 i j) (t,y))
variable {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
include hq hu
lemma joint_localLaplacian (t : ℝ) (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => localLaplacian (q z.1) u p z.2) (t,y) := by
  classical
  have hv := contDiffAt_inChart hu p hy
  have hd (j : CoordIndex E) :=
    (hv.fderiv_right (m := ∞) (by simp)).clm_apply (contDiffAt_const (c := Module.finBasis ℝ E j))
  have hdd (i j : CoordIndex E) :=
    ((hd j).fderiv_right (m := ∞) (by simp)).clm_apply (contDiffAt_const (c := Module.finBasis ℝ E i))
  have hh : ContDiffAt ℝ ∞ (fun z : ℝ × E =>
      (∑ i, ∑ j, (metricCoefficients (q z.1) p z.2)⁻¹ i j *
        fderiv ℝ (fun y => fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j)) z.2
          (Module.finBasis ℝ E i)) + ∑ j, metricFirstCoefficient (q z.1) p j z.2 *
        fderiv ℝ (u ∘ (chartAt E p).symm) z.2 (Module.finBasis ℝ E j)) (t,y) := by
    apply ContDiffAt.add
    · apply ContDiffAt.sum
      intro i _
      apply ContDiffAt.sum
      intro j _
      apply (joint_metricInverse q p (hq p) t hy i j).mul
      simpa only [Function.comp_def] using (hdd i j).comp (t,y) contDiffAt_snd
    · apply ContDiffAt.sum
      intro j _
      apply (joint_metricFirstCoefficient q p (hq p) t hy j).mul
      simpa only [Function.comp_def] using (hd j).comp (t,y) contDiffAt_snd
  apply hh.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.eventually ((chartAt E p).open_target.mem_nhds hy)] with z hz
  exact localLaplacian_expansion hu (q z.1) p hz

lemma joint_laplaceBeltrami_chart (t : ℝ) (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => laplaceBeltrami (q z.1) u ((chartAt E p).symm z.2)) (t,y) := by
  apply (joint_localLaplacian q hq hu t p hy).congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.eventually ((chartAt E p).open_target.mem_nhds hy)] with z hz
  rw [laplaceBeltrami_inChart hu (q z.1) p _ ((chartAt E p).map_target hz),
    (chartAt E p).right_inv hz]
end JointLocalLaplacian

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
variable (q : ℝ → SmoothMetric E M)
variable (hq : ∀ p t y, y ∈ (chartAt E p).target → ∀ i j,
  ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (q z.1) p z.2 i j) (t,y))
variable {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
include hq hu
lemma continuous_joint_laplaceBeltrami :
    Continuous (fun z : ℝ × M => laplaceBeltrami (q z.1) u z.2) := by
  apply continuous_joint_of_chart (E := E) (fun t x => laplaceBeltrami (q t) u x)
  intro t p
  exact (joint_laplaceBeltrami_chart q hq hu t p ((chartAt E p).map_source (mem_chart_source E p))).continuousAt

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_CoordinateGradientPairScalarCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff BoundedContinuousFunction

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
   [CompactSpace M]
namespace MetricIntegralAtlas
variable (A : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)

def mean (f : M → ℝ) : ℝ :=
  ∑ i : A.t, metricChartIntegral g (i : M) (fun x => A.ρ i x * f x)

end MetricIntegralAtlas

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ContinuousEigenpairLinearization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def realRepresentative (s : ℝ) : A.realH s →L[ℝ] (M →ᵇ ℝ) :=
  Complex.reCLM.compLeftContinuousBounded M ∘L A.representative s ∘L (A.realH s).subtypeL

omit [T2Space M] in
lemma realRepresentative_injective (s : ℝ) (ht : Module.finrank ℝ E < 2 * s) :
    Injective (A.realRepresentative s) := by
  intro u v huv
  apply Subtype.ext
  apply manifoldSobolevRepresentative_injective A.p A.η
    (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η A.sum_η ht
  ext x
  change A.representative s u x = A.representative s v x
  rw [← A.ofReal_realValue s u x, ← A.ofReal_realValue s v x]
  exact congrArg (fun f : M →ᵇ ℝ => (f x : ℂ)) huv

def intrinsicForm (I : MetricIntegralAtlas (E := E) (M := M)) (s : ℝ) :
    A.realH s →L[ℝ] A.realH s →L[ℝ] ℝ :=
  ContinuousLinearMap.compL ℝ (A.realH s) (M →ᵇ ℝ) ℝ (I.integralCLM g) ∘L
    (ContinuousLinearMap.mul ℝ (M →ᵇ ℝ)).bilinearComp (A.realRepresentative s) (A.realRepresentative s)

omit [T2Space M] in
lemma intrinsicForm_apply (I : MetricIntegralAtlas (E := E) (M := M)) (s : ℝ)
    (u v : A.realH s) :
    A.intrinsicForm I s u v = I.mean g (fun x => A.realValue s u x * A.realValue s v x) := rfl

def intrinsicPairing (I : MetricIntegralAtlas (E := E) (M := M)) (s : ℝ)
    (ht : Module.finrank ℝ E < 2 * s) : PositivePairing (X := A.realH s) where
  form := A.intrinsicForm I s
  symmetric := by
    intro u v
    rw [A.intrinsicForm_apply, A.intrinsicForm_apply]
    congr 1
    funext x
    exact mul_comm _ _
  positive := by
    intro u hu
    change 0 < I.integral g (A.realRepresentative s u * A.realRepresentative s u)
    apply I.integral_pos g (fun x => mul_self_nonneg _)
    have hne : A.realRepresentative s u ≠ 0 := by
      intro he
      apply hu
      apply A.realRepresentative_injective s ht
      simpa using he
    have hx : ∃ x, A.realRepresentative s u x ≠ 0 := by
      by_contra! hh
      apply hne
      ext x
      exact hh x
    obtain ⟨x,hx⟩ := hx
    exact ⟨x, mul_self_pos.mpr hx⟩

end CompactMetricAtlas

end

open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_VaryingSpectralResolventBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs) (I : MetricIntegralAtlas (E := E) (M := M))

def scalarTestCLM (s : ℝ) : (M →ᵇ ℝ) →L[ℝ] A.realH s →L[ℝ] ℝ :=
  ContinuousLinearMap.compL ℝ (A.realH s) (M →ᵇ ℝ) ℝ (I.integralCLM g) ∘L
    (ContinuousLinearMap.mul ℝ (M →ᵇ ℝ)).bilinearComp
      (ContinuousLinearMap.id ℝ (M →ᵇ ℝ)) (A.realRepresentative s)

end CompactMetricAtlas

variable (q : ℝ → SmoothMetric E M)
variable (hq : ∀ p t y, y ∈ (chartAt E p).target → ∀ i j,
  ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (q z.1) p z.2 i j) (t,y))
variable {a : M → ℝ} (ha : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ a)

def laplaceFamilyBCF (t : ℝ) : M →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
  ⟨laplaceBeltrami (q t) a,(continuous_joint_laplaceBeltrami q hq ha).comp
    (continuous_const.prodMk continuous_id)⟩

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs) (I : MetricIntegralAtlas (E := E) (M := M))

def laplaceVariationTest (s t : ℝ) : A.realH s →L[ℝ] ℝ :=
  A.scalarTestCLM I s (t⁻¹ • (laplaceFamilyBCF q hq ha t-laplaceFamilyBCF q hq ha 0))

end CompactMetricAtlas
end


open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end


