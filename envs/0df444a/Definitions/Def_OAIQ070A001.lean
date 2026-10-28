-- Prove2me | Definitions.Def_OAIQ070A001
-- name    : OAIQ070A001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T11:15:59.586335+00:00
-- url     : https://prove2.me/theorems/1912b855-cc6e-4cf0-98cb-aafa79137c0d
-- title:
--   Definitions bundle OAIQ070A001 of the split of OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 74 declarations of OpenAI's Lean: 16 definitions, 2 inductive types or structures and 56 theorems. The definitions and types are `OAI.YauCounterexamples.MetricIntegralAtlas`, `OAI.YauCounterexamples.MetricIntegralAtlas.integral`, `OAI.YauCounterexamples.MetricIntegralAtlas.integralCLM`, `OAI.YauCounterexamples.PositivePairing`, `OAI.YauCounterexamples.bilinearExtension`, `OAI.YauCounterexamples.chartTransition`, `OAI.YauCounterexamples.complexUnitBump`, `OAI.YauCounterexamples.coordinateTransitionMatrix`, `OAI.YauCounterexamples.determinantMultilinear`, `OAI.YauCounterexamples.euclideanElliptic`, `OAI.YauCounterexamples.instSizeOfSmoothPartitionOfUnitySubtypeMemFinsetModelWithCornersSelfRealUniv_solutions`, `OAI.YauCounterexamples.inverseChartDerivative`, `OAI.YauCounterexamples.jacobianMatrix`, `OAI.YauCounterexamples.localLaplacian`, `OAI.YauCounterexamples.metricChartIntegral`, `OAI.YauCounterexamples.metricFlux`, `OAI.YauCounterexamples.partialBilinearExtension`, `OAI.YauCounterexamples.unitBump`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `SmoothYau_DifferentialEq_JacobianMatrix`, `SmoothYau_DifferentialEq_LocalDiffeomorphismDetNeZero`, `SmoothYau_Estimates_MixedPiolaDivergenceAbs`, `SmoothYau_Estimates_PartialBilinearExtension`, `SmoothYau_Geometry_CoefficientGradientApply`, `SmoothYau_Geometry_MetricDetChange`, `SmoothYau_Smoothness_ChartTransition`, `SmoothYau_Smoothness_ExistsFinitePatchPartition`, `SmoothYau_Smoothness_FderivCofactorApply`, `SmoothYau_Smoothness_LocalIntegrationParts`, `SmoothYau_Smoothness_MomentBesselLp`, `SmoothYau_Smoothness_PiolaIdentity`, `SmoothYau_Smoothness_SobolevRepresentativeOrderCongr`, `SmoothYau_Smoothness_SphericalBaseProfileRadius`, `SmoothYau_Spectrum_ContinuousEigenpairLinearization`, `SmoothYau_Spectrum_JointLocalLaplacian`.
--
--   **Imports.** It imports the published bundle `Def_SmoothYau`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ070A005`, `OAIQ070A006` and `OAIQ070A007`; the proofs of `OAI_YauCounterexamples_cutoff_raw_bounded_by_near_one`, `OAI_YauCounterexamples_regular_quotient_at_zero`, `OAI_YauCounterexamples_roundPower_dominant_perturbation_jet_lower`, `OAI.YauCounterexamples.spherical_cutoff_control_bounds`, `OAI.YauCounterexamples.three_cutoff_control_bounds`, `OAI_YauCounterexamples_three_cutoff_raw_bounded_by_near_one` and `OAI_YauCounterexamples_three_regular_quotient_at_zero`.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 1581d4c

import Mathlib
import Definitions.Def_SmoothYau

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

def determinantMultilinear : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
  { (Matrix.detRowAlternating : (ι → ℝ) [⋀^ι]→ₗ[ℝ] ℝ).toMultilinearMap with
    cont := by
      change Continuous (fun A : Matrix ι ι ℝ => A.det)
      simp only [Matrix.det_apply']
      fun_prop }

lemma det_updateRow_eq (A : Matrix ι ι ℝ) (hA : IsUnit A.det) (i : ι) (v : ι → ℝ) :
    (A.updateRow i v).det = (v ᵥ* A⁻¹) i * A.det := by
  have hv : v = ∑ k, (v ᵥ* A⁻¹) k • A k := by
    ext j
    have hh := congrFun (Matrix.vecMul_vecMul v A⁻¹ A) j
    rw [Matrix.nonsing_inv_mul _ hA, Matrix.vecMul_one] at hh
    simpa only [Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hh.symm
  conv_lhs => arg 1; arg 3; rw [hv]
  exact Matrix.det_updateRow_sum A i (v ᵥ* A⁻¹)


lemma fderiv_det_apply (A H : Matrix ι ι ℝ) (hA : IsUnit A.det) :
    fderiv ℝ (Matrix.det : Matrix ι ι ℝ → ℝ) A H =
      A.det * Matrix.trace (H * A⁻¹) := by
  have hd := determinantMultilinear.hasFDerivAt A
  have hd' := hd.fderiv
  change fderiv ℝ (determinantMultilinear (ι := ι)) A H = _
  rw [hd']
  change (determinantMultilinear.linearDeriv A) H = _
  erw [ContinuousMultilinearMap.linearDeriv_apply]
  change (∑ i, (A.updateRow i (H i)).det) = _
  simp only [det_updateRow_eq A hA, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma differentiable_det : Differentiable ℝ (Matrix.det : Matrix ι ι ℝ → ℝ) :=
  fun A => (determinantMultilinear.hasFDerivAt A).differentiableAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma fderiv_det_comp_apply (A : E → Matrix ι ι ℝ) {x : E}
    (hA : DifferentiableAt ℝ A x) (hx : IsUnit (A x).det) (v : E) :
    fderiv ℝ (fun y => (A y).det) x v =
      (A x).det * Matrix.trace ((fderiv ℝ A x v) * (A x)⁻¹) := by
  change fderiv ℝ (Matrix.det ∘ A) x v = _
  rw [fderiv_comp x (differentiable_det (A x)) hA]
  exact fderiv_det_apply _ _ hx

end

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

lemma differentiableAt_matrix_inv {A : E → Matrix ι ι ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hx : IsUnit (A x).det) :
    DifferentiableAt ℝ (fun y => (A y)⁻¹) x := by
  have he (i j : ι) : DifferentiableAt ℝ (fun y => A y i j) x :=
    (differentiableAt_pi.mp (differentiableAt_pi.mp hA i)) j
  have hd : DifferentiableAt ℝ (fun y => (A y).det) x :=
    (differentiable_det _).comp x hA
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  apply (hd.inv (isUnit_iff_ne_zero.mp hx)).mul
  simp only [Matrix.det_apply']
  apply DifferentiableAt.fun_sum
  intro σ _
  apply (differentiableAt_const _).mul
  have hp (k : ι) : DifferentiableAt ℝ
      (fun y => (A y).updateRow j (Pi.single i 1) (σ k) k) x := by
    by_cases hk : σ k = j
    · simp only [hk, Matrix.updateRow_self]
      exact differentiableAt_const _
    · simp only [Matrix.updateRow_ne hk]
      exact he _ _
  exact (HasFDerivAt.finsetProd (u := Finset.univ)
    (fun k _ => (hp k).hasFDerivAt)).differentiableAt

omit [DecidableEq ι] in
lemma fderiv_matrix_apply {A : E → Matrix ι ι ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (v : E) (i j : ι) :
    fderiv ℝ A x v i j = fderiv ℝ (fun y => A y i j) x v := by
  have hr (i : ι) := differentiableAt_pi.mp hA i
  have hc (i j : ι) := differentiableAt_pi.mp (hr i) j
  change (fderiv ℝ (fun y i => A y i) x v) i j = _
  rw [fderiv_pi hr]
  change (fderiv ℝ (fun y j => A y i j) x v) j = _
  rw [fderiv_pi (hc i)]
  rfl

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


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_JacobianMatrix
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

def jacobianMatrix (b : Module.Basis ι ℝ E) (f : E → E) (x : E) : Matrix ι ι ℝ :=
  LinearMap.toMatrix b b (fderiv ℝ f x).toLinearMap

omit [FiniteDimensional ℝ E] in
lemma jacobianMatrix_apply (b : Module.Basis ι ℝ E) (f : E → E) (x : E) (i j : ι) :
    jacobianMatrix b f x i j = b.coord i (fderiv ℝ f x (b j)) := by
  simp only [jacobianMatrix, LinearMap.toMatrix_apply, Module.Basis.coord_apply,
    ContinuousLinearMap.coe_coe]

lemma differentiableAt_jacobian {f : E → E} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (b : Module.Basis ι ℝ E) :
    DifferentiableAt ℝ (jacobianMatrix b f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  let L : E →L[ℝ] ℝ := (b.coord i).toContinuousLinearMap
  simp only [jacobianMatrix_apply]
  change DifferentiableAt ℝ (fun y => L (fderiv ℝ f y (b j))) x
  exact L.differentiableAt.comp x (hd.clm_apply (differentiableAt_const _))

lemma fderiv_jacobian_apply {f : E → E} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (b : Module.Basis ι ℝ E) (v : E) (i j : ι) :
    fderiv ℝ (jacobianMatrix b f) x v i j =
      b.coord i (fderiv ℝ (fderiv ℝ f) x v (b j)) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [fderiv_matrix_apply (differentiableAt_jacobian hf b)]
  let L : E →L[ℝ] ℝ := (b.coord i).toContinuousLinearMap
  simp only [jacobianMatrix_apply]
  change fderiv ℝ (fun y => L (fderiv ℝ f y (b j))) x v = _
  rw [show (fun y => L (fderiv ℝ f y (b j))) =
      L ∘ (fun y => fderiv ℝ f y (b j)) from rfl,
    fderiv_comp x L.differentiableAt (hd.clm_apply (differentiableAt_const _)),
    L.fderiv, fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  rfl

lemma jacobian_curl {f : E → E} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (b : Module.Basis ι ℝ E) (i l m : ι) :
    fderiv ℝ (jacobianMatrix b f) x (b i) l m =
      fderiv ℝ (jacobianMatrix b f) x (b m) l i := by
  rw [fderiv_jacobian_apply hf, fderiv_jacobian_apply hf,
    (hf.isSymmSndFDerivAt (by norm_num)).eq]
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_LocalDiffeomorphismDetNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
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
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma local_diffeomorphism_det_ne_zero (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ ∞ e e.source) (he' : ContDiffOn ℝ ∞ e.symm e.target)
    {x : E} (hx : x ∈ e.source) : (fderiv ℝ e x).det ≠ 0 := by
  have hf := ((he x hx).contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp)
  have hg := ((he' (e x) (e.map_source hx)).contDiffAt
    (e.open_target.mem_nhds (e.map_source hx))).differentiableAt (by simp)
  have hid : (fun y => e.symm (e y)) =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact e.left_inv hy
  have hder : (fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x) = ContinuousLinearMap.id ℝ E := by
    apply HasFDerivAt.unique ((hg.hasFDerivAt.comp x hf.hasFDerivAt).congr_of_eventuallyEq hid.symm)
    exact hasFDerivAt_id x
  have hd := congrArg ContinuousLinearMap.det hder
  change LinearMap.det ((fderiv ℝ e.symm (e x)).toLinearMap.comp
    (fderiv ℝ e x).toLinearMap) = LinearMap.det (LinearMap.id : E →ₗ[ℝ] E) at hd
  rw [LinearMap.det_comp, LinearMap.det_id] at hd
  intro h
  simp only [h, mul_zero] at hd
  exact zero_ne_one hd

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

omit [FiniteDimensional ℝ E] in
lemma fderiv_comp_basis {f : E → E} {X : E → ι → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hX : DifferentiableAt ℝ X (f x))
    (b : Module.Basis ι ℝ E) (k i : ι) :
    fderiv ℝ (fun y => X (f y) k) x (b i) =
      ∑ m, jacobianMatrix b f x m i * fderiv ℝ (fun z => X z k) (f x) (b m) := by
  have hk := differentiableAt_pi.mp hX k
  rw [show (fun y => X (f y) k) = (fun z => X z k) ∘ f from rfl,
    fderiv_comp x hk hf, ContinuousLinearMap.comp_apply,
    ← b.sum_repr (fderiv ℝ f x (b i))]
  simp only [map_sum, map_smul, smul_eq_mul, jacobianMatrix_apply]
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

omit [FiniteDimensional ℝ E] [NormedSpace ℝ E] in
lemma local_abs_multiplier {d : E → ℝ} {x : E} (hd : ContinuousAt d x) (hx : d x ≠ 0) :
    ∃ c : ℝ, |d x| = c * d x ∧ ∀ᶠ y in 𝓝 x, |d y| = c * d y := by
  rcases lt_or_gt_of_ne hx with hn | hp
  · refine ⟨-1, by rw [abs_of_neg hn]; ring, ?_⟩
    filter_upwards [hd.eventually_lt continuousAt_const hn] with y hy
    rw [abs_of_neg hy]
    ring
  · refine ⟨1, by rw [abs_of_pos hp, one_mul], ?_⟩
    filter_upwards [continuousAt_const.eventually_lt hd hp] with y hy
    rw [abs_of_pos hy, one_mul]

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_PartialBilinearExtension
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
open MeasureTheory
open scoped ENNReal
namespace YauCounterexamples
variable {𝕜 P E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup P] [Module 𝕜 P]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  (B : P →ₗ[𝕜] P →ₗ[𝕜] F) (e : P →ₗ[𝕜] E) (hd : DenseRange e)
  (C : ℝ) (hb : ∀ p q, ‖B p q‖ ≤ C * ‖e p‖ * ‖e q‖)

def partialBilinearExtension : P →ₗ[𝕜] (E →L[𝕜] F) where
  toFun p := (B p).extendOfNorm e
  map_add' p q := by
    ext x
    exact congrFun (hd.equalizer (by fun_prop) (by fun_prop) (by
      funext r
      change (B (p + q)).extendOfNorm e (e r) =
        (B p).extendOfNorm e (e r) + (B q).extendOfNorm e (e r)
      rw [LinearMap.extendOfNorm_eq hd ⟨C * ‖e (p + q)‖, hb (p + q)⟩,
        LinearMap.extendOfNorm_eq hd ⟨C * ‖e p‖, hb p⟩,
        LinearMap.extendOfNorm_eq hd ⟨C * ‖e q‖, hb q⟩]
      simp)) x
  map_smul' c p := by
    ext x
    exact congrFun (hd.equalizer (by fun_prop) (by fun_prop) (by
      funext r
      change (B (c • p)).extendOfNorm e (e r) = c • (B p).extendOfNorm e (e r)
      rw [LinearMap.extendOfNorm_eq hd ⟨C * ‖e (c • p)‖, hb (c • p)⟩,
        LinearMap.extendOfNorm_eq hd ⟨C * ‖e p‖, hb p⟩]
      simp)) x

def bilinearExtension : E →L[𝕜] E →L[𝕜] F :=
  (partialBilinearExtension B e hd C hb).extendOfNorm e

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ExistsFinitePatchPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Function Filter
open scoped Topology Manifold ContDiff
namespace YauCounterexamples
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def unitBump : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩

def complexUnitBump (x : E) : ℂ := (unitBump E x : ℂ)

lemma contDiff_complexUnitBump : ContDiff ℝ ∞ (complexUnitBump E) :=
  Complex.ofRealCLM.contDiff.comp (unitBump E).contDiff

lemma hasCompactSupport_complexUnitBump : HasCompactSupport (complexUnitBump E) := by
  apply (unitBump E).hasCompactSupport.mono
  intro x hx
  exact fun h => hx (by simp [complexUnitBump, h])

end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartTransition
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
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

def chartTransition (p q : M) : E → E := (chartAt E p) ∘ (chartAt E q).symm

def coordinateTransitionMatrix (p q : M) (y : E) :
    Matrix (CoordIndex E) (CoordIndex E) ℝ :=
  LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E)
    (fderiv ℝ (chartTransition p q) y).toLinearMap

def inverseChartDerivative (p : M) (y : E) : E →L[ℝ] E :=
  mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm y

omit [FiniteDimensional ℝ E] in
lemma invChart_derivative_change (p q : M) {y : E}
    (hy : y ∈ (chartAt E q).target) (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    (inverseChartDerivative p (chartTransition p q y)).comp
      (fderiv ℝ (chartTransition p q) y) =
      inverseChartDerivative q y := by
  have hpc := mdifferentiable_chart (I := 𝓘(ℝ, E)) p
  have hqc := mdifferentiable_chart (I := 𝓘(ℝ, E)) q
  have hc := mfderiv_comp y (hpc.mdifferentiableAt hp) (hqc.mdifferentiableAt_symm hy)
  rw [mfderiv_eq_fderiv] at hc
  change fderiv ℝ (chartTransition p q) y = _ at hc
  unfold inverseChartDerivative
  erw [hc, ← ContinuousLinearMap.comp_assoc, hpc.symm_comp_deriv hp,
    ContinuousLinearMap.id_comp]

lemma coordinateVector_change (p q : M) {y : E}
    (hy : y ∈ (chartAt E q).target) (hp : (chartAt E q).symm y ∈ (chartAt E p).source)
    (i : CoordIndex E) :
    coordinateVector q y i = ∑ k, coordinateTransitionMatrix p q y k i •
      coordinateVector p (chartTransition p q y) k := by
  have hh := congrArg (fun L : E →L[ℝ] E => L (Module.finBasis ℝ E i))
    (invChart_derivative_change p q hy hp)
  change _ = coordinateVector q y i at hh
  rw [← hh]
  change (inverseChartDerivative p (chartTransition p q y))
    ((fderiv ℝ (chartTransition p q) y) (Module.finBasis ℝ E i)) = _
  rw [← (Module.finBasis ℝ E).sum_repr ((fderiv ℝ (chartTransition p q) y) (Module.finBasis ℝ E i))]
  simp only [map_sum, map_smul, coordinateTransitionMatrix, LinearMap.toMatrix_apply]
  rfl

omit [FiniteDimensional ℝ E] in
lemma bilinear_sum_matrix {ι : Type*} [Fintype ι]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a : ι → ι → ℝ) (v : ι → E) (i j : ι) :
    B (∑ k, a k i • v k) (∑ k, a k j • v k) =
      ∑ k, ∑ l, a l i * B (v l) (v k) * a k j := by
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma metricCoefficients_change (g : SmoothMetric E M) (p q : M) {y : E}
    (hy : y ∈ (chartAt E q).target) (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    metricCoefficients g q y = (coordinateTransitionMatrix p q y).transpose *
      metricCoefficients g p (chartTransition p q y) * coordinateTransitionMatrix p q y := by
  ext i j
  have he : (chartAt E p).symm (chartTransition p q y) = (chartAt E q).symm y :=
    (chartAt E p).left_inv hp
  simp only [Matrix.mul_apply, Matrix.transpose_apply, metricCoefficients, Finset.sum_mul]
  rw [he]
  let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner ((chartAt E q).symm y)
  change B (coordinateVector q y i) (coordinateVector q y j) = _
  rw [coordinateVector_change p q hy hp i, coordinateVector_change p q hy hp j]
  change B (∑ k : CoordIndex E, coordinateTransitionMatrix p q y k i •
    (coordinateVector p (chartTransition p q y) k : E))
    (∑ k : CoordIndex E, coordinateTransitionMatrix p q y k j •
    (coordinateVector p (chartTransition p q y) k : E)) = _
  exact bilinear_sum_matrix B (coordinateTransitionMatrix p q y)
    (fun k => (coordinateVector p (chartTransition p q y) k : E)) i j
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SphericalBaseProfileRadius
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma contMDiffAt_coordinateVector (p : M) (i : CoordIndex E) {y : E}
    (hy : y ∈ (chartAt E p).target) :
    ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z : E => TotalSpace.mk' E ((chartAt E p).symm z) (coordinateVector p z i)) y := by
  have hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (chartAt E p).symm y :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy
  have hd := hf.mfderiv_const (m := ∞) (by simp)
  have hv : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z : E => TotalSpace.mk' E (E := TangentSpace 𝓘(ℝ, E)) z (Module.finBasis ℝ E i : TangentSpace 𝓘(ℝ, E) z)) y := by
    rw [contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_id, ?_⟩
    simpa only [trivializationAt_model_space_apply] using
      (contMDiffAt_const : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun _ : E => Module.finBasis ℝ E i) y)
  exact hd.clm_apply_of_inCoordinates hv hf

lemma contDiffOn_metricCoefficient (g : SmoothMetric E M) (p : M) (i j : CoordIndex E) :
    ContDiffOn ℝ ∞ (fun y => metricCoefficients g p y i j) (chartAt E p).target := by
  intro y hy
  have hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (chartAt E p).symm y :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy
  have h : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞
      (fun z => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) ((chartAt E p).symm z)
        (metricCoefficients g p z i j)) y := by
    exact (g.contMDiff.contMDiffAt.comp y hf).clm_bundle_apply₂
      (contMDiffAt_coordinateVector p i hy) (contMDiffAt_coordinateVector p j hy)
  rw [contMDiffAt_totalSpace] at h
  exact (contMDiffAt_iff_contDiffAt.mp h.2).contDiffWithinAt


end

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma metricCoefficients_posDef (g : SmoothMetric E M) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) : (metricCoefficients g p y).PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    exact g.symm _ _ _
  · intro a ha
    change (0 : ℝ) < a ⬝ᵥ (metricCoefficients g p y).mulVec a
    have he : (chartAt E p).MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
      ⟨(contMDiffOn_chart (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableOn (by simp),
        (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableOn (by simp)⟩
    let D : E →L[ℝ] TangentSpace 𝓘(ℝ, E) ((chartAt E p).symm y) :=
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm y
    have hinj : Function.Injective D := he.symm.mfderiv_injective hy
    have hn : D ((Module.finBasis ℝ E).equivFun.symm a) ≠ 0 := by
      intro h
      apply ha
      have hz : (Module.finBasis ℝ E).equivFun.symm a = 0 :=
        hinj (h.trans (map_zero _).symm)
      exact (Module.finBasis ℝ E).equivFun.symm.injective (hz.trans (map_zero _).symm)
    have hp : 0 < g.inner ((chartAt E p).symm y)
        (D ((Module.finBasis ℝ E).equivFun.symm a))
        (D ((Module.finBasis ℝ E).equivFun.symm a)) :=
      g.pos ((chartAt E p).symm y) _ hn
    rw [Module.Basis.equivFun_symm_apply] at hp
    have hD := map_sum D
      (fun i => a i • Module.finBasis ℝ E i) Finset.univ
    rw [hD] at hp
    simp only [map_smul, map_sum, sum_apply,
      smul_apply, smul_eq_mul] at hp
    have hb (i : CoordIndex E) : coordinateVector p y i = D (Module.finBasis ℝ E i) := rfl
    simpa [metricCoefficients, hb, Matrix.mulVec, dotProduct,
      Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm, g.symm] using hp

lemma metricCoefficients_det_pos (g : SmoothMetric E M) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) : 0 < Matrix.det (metricCoefficients g p y) :=
  (metricCoefficients_posDef g p hy).det_pos

lemma contDiffOn_metricDet (g : SmoothMetric E M) (p : M) :
    ContDiffOn ℝ ∞ (fun y => Matrix.det (metricCoefficients g p y)) (chartAt E p).target := by
  classical
  simp only [Matrix.det_apply']
  apply ContDiffOn.sum
  intro σ _
  apply contDiffOn_const.mul
  apply contDiffOn_prod
  intro i _
  exact contDiffOn_metricCoefficient g p _ _

lemma contDiffOn_metricDensity (g : SmoothMetric E M) (p : M) :
    ContDiffOn ℝ ∞ (fun y => Real.sqrt (Matrix.det (metricCoefficients g p y)))
      (chartAt E p).target :=
  (contDiffOn_metricDet g p).sqrt (fun _ hy => (metricCoefficients_det_pos g p hy).ne')


end

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma contDiffOn_metricAdjugate (g : SmoothMetric E M) (p : M) (i j : CoordIndex E) :
    ContDiffOn ℝ ∞ (fun y => (metricCoefficients g p y).adjugate i j) (chartAt E p).target := by
  classical
  simp only [Matrix.adjugate_apply, Matrix.det_apply']
  apply ContDiffOn.sum
  intro σ _
  apply contDiffOn_const.mul
  apply contDiffOn_prod
  intro k _
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact contDiffOn_metricCoefficient g p _ _

lemma contDiffOn_metricInverse (g : SmoothMetric E M) (p : M) (i j : CoordIndex E) :
    ContDiffOn ℝ ∞ (fun y => (metricCoefficients g p y)⁻¹ i j) (chartAt E p).target := by
  classical
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact ((contDiffOn_metricDet g p).inv (fun _ hy => (metricCoefficients_det_pos g p hy).ne')).mul
    (contDiffOn_metricAdjugate g p i j)


end

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
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter Manifold BoxIntegral
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_MetricDetChange
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
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma metricDet_change (g : SmoothMetric E M) (p q : M) {y : E}
    (hy : y ∈ (chartAt E q).target) (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    (metricCoefficients g q y).det = (coordinateTransitionMatrix p q y).det ^ 2 *
      (metricCoefficients g p (chartTransition p q y)).det := by
  rw [metricCoefficients_change g p q hy hp, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

lemma coordinateTransitionMatrix_det_ne_zero (g : SmoothMetric E M) (p q : M) {y : E}
    (hy : y ∈ (chartAt E q).target) (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    (coordinateTransitionMatrix p q y).det ≠ 0 := by
  intro h
  have hd := metricDet_change g p q hy hp
  rw [h, zero_pow (by omega), zero_mul] at hd
  exact (metricCoefficients_det_pos g q hy).ne' hd

lemma metricDensity_change (g : SmoothMetric E M) (p q : M) {y : E}
    (hy : y ∈ (chartAt E q).target) (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    Real.sqrt (metricCoefficients g q y).det = |(coordinateTransitionMatrix p q y).det| *
      Real.sqrt (metricCoefficients g p (chartTransition p q y)).det := by
  rw [metricDet_change g p q hy hp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

lemma metricInverse_change (g : SmoothMetric E M) (p q : M) {y : E}
    (hy : y ∈ (chartAt E q).target) (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    coordinateTransitionMatrix p q y * (metricCoefficients g q y)⁻¹ *
      (coordinateTransitionMatrix p q y).transpose =
        (metricCoefficients g p (chartTransition p q y))⁻¹ := by
  classical
  have hd : IsUnit (coordinateTransitionMatrix p q y).det :=
    isUnit_iff_ne_zero.mpr (coordinateTransitionMatrix_det_ne_zero g p q hy hp)
  have ht : IsUnit (coordinateTransitionMatrix p q y).transpose.det := by
    simpa only [Matrix.det_transpose] using hd
  rw [metricCoefficients_change g p q hy hp, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
    Matrix.nonsing_inv_mul_cancel_right _ _ ht]
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

omit [FiniteDimensional ℝ E] in
lemma contDiffAt_chartTransition (p q : M) {y : E}
    (hy : y ∈ (chartAt E q).target) (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    ContDiffAt ℝ ∞ (chartTransition p q) y := by
  exact contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hp).comp y
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) hy))

omit [FiniteDimensional ℝ E] in
lemma contDiffAt_inChart {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (u ∘ (chartAt E p).symm) y :=
  contMDiffAt_iff_contDiffAt.mp (hu.contMDiffAt.comp y
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy))

omit [FiniteDimensional ℝ E] [NormedSpace ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
lemma chart_overlap_nhds (p q : M) {y : E}
    (hy : y ∈ (chartAt E q).target) (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    ∀ᶠ z in 𝓝 y, z ∈ (chartAt E q).target ∧
      (chartAt E q).symm z ∈ (chartAt E p).source := by
  have hc := (chartAt E q).continuousAt_symm hy
  filter_upwards [(chartAt E q).open_target.mem_nhds hy,
    hc.eventually ((chartAt E p).open_source.mem_nhds hp)] with z hz hz'
  exact ⟨hz, hz'⟩

lemma fderiv_inChart_change {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (p q : M) {y : E} (hy : y ∈ (chartAt E q).target)
    (hp : (chartAt E q).symm y ∈ (chartAt E p).source) (i : CoordIndex E) :
    fderiv ℝ (u ∘ (chartAt E q).symm) y (Module.finBasis ℝ E i) =
      ∑ k, fderiv ℝ (u ∘ (chartAt E p).symm) (chartTransition p q y)
        (Module.finBasis ℝ E k) * coordinateTransitionMatrix p q y k i := by
  have he : (u ∘ (chartAt E q).symm) =ᶠ[𝓝 y]
      ((u ∘ (chartAt E p).symm) ∘ chartTransition p q) := by
    filter_upwards [chart_overlap_nhds p q hy hp] with z hz
    simp only [Function.comp_apply, chartTransition, (chartAt E p).left_inv hz.2]
  rw [he.fderiv_eq]
  have hf := (contDiffAt_chartTransition p q hy hp).differentiableAt (by simp)
  have hu' := (contDiffAt_inChart hu p ((chartAt E p).map_source hp)).differentiableAt (by simp)
  rw [fderiv_comp y hu' hf, ContinuousLinearMap.comp_apply,
    ← (Module.finBasis ℝ E).sum_repr (fderiv ℝ (chartTransition p q) y (Module.finBasis ℝ E i))]
  simp only [map_sum, map_smul, smul_eq_mul, coordinateTransitionMatrix,
    LinearMap.toMatrix_apply, ContinuousLinearMap.coe_coe]
  apply Finset.sum_congr rfl
  intro k _
  ring

def metricFlux (g : SmoothMetric E M) (u : M → ℝ) (p : M) (y : E) (i : CoordIndex E) : ℝ :=
  Real.sqrt (metricCoefficients g p y).det *
    ∑ j, (metricCoefficients g p y)⁻¹ i j *
      fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j)

def localLaplacian (g : SmoothMetric E M) (u : M → ℝ) (p : M) (y : E) : ℝ :=
  (Real.sqrt (metricCoefficients g p y).det)⁻¹ *
    ∑ i, fderiv ℝ (fun z => metricFlux g u p z i) y (Module.finBasis ℝ E i)

lemma metricInverse_change_left (g : SmoothMetric E M) (p q : M) {y : E}
    (hy : y ∈ (chartAt E q).target) (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    (metricCoefficients g q y)⁻¹ * (coordinateTransitionMatrix p q y).transpose =
      (coordinateTransitionMatrix p q y)⁻¹ *
        (metricCoefficients g p (chartTransition p q y))⁻¹ := by
  have hd : IsUnit (coordinateTransitionMatrix p q y).det :=
    isUnit_iff_ne_zero.mpr (coordinateTransitionMatrix_det_ne_zero g p q hy hp)
  rw [← metricInverse_change g p q hy hp, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]

lemma metricFlux_change {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (g : SmoothMetric E M) (p q : M) {y : E} (hy : y ∈ (chartAt E q).target)
    (hp : (chartAt E q).symm y ∈ (chartAt E p).source) (i : CoordIndex E) :
    metricFlux g u q y i = ∑ k, |(coordinateTransitionMatrix p q y).det| *
      (coordinateTransitionMatrix p q y)⁻¹ i k * metricFlux g u p (chartTransition p q y) k := by
  classical
  let d : CoordIndex E → ℝ := fun j =>
    fderiv ℝ (u ∘ (chartAt E p).symm) (chartTransition p q y) (Module.finBasis ℝ E j)
  have hh := congrArg (fun A : Matrix (CoordIndex E) (CoordIndex E) ℝ => A.mulVec d i)
    (metricInverse_change_left g p q hy hp)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hh
  simp only [metricFlux, fderiv_inChart_change hu p q hy hp,
    metricDensity_change g p q hy hp]
  have hs : (∑ j, (metricCoefficients g q y)⁻¹ i j *
      ∑ k, d k * coordinateTransitionMatrix p q y k j) =
      ∑ k, (coordinateTransitionMatrix p q y)⁻¹ i k *
        ∑ j, (metricCoefficients g p (chartTransition p q y))⁻¹ k j * d j := by
    simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm] using hh
  change (_ * _) * (∑ j, (metricCoefficients g q y)⁻¹ i j *
    ∑ k, d k * coordinateTransitionMatrix p q y k j) = _
  rw [hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [d]
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
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_CoefficientGradientApply
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
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def metricChartIntegral (g : SmoothMetric E M) (p : M) (f : M → ℝ) : ℝ :=
  ∫ y in (chartAt E p).target, Real.sqrt (metricCoefficients g p y).det *
    f ((chartAt E p).symm y)

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

lemma metricChart_integrable (g : SmoothMetric E M) (p : M) {f : M → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ (chartAt E p).source) :
    IntegrableOn (fun y => Real.sqrt (metricCoefficients g p y).det *
      f ((chartAt E p).symm y)) (chartAt E p).target := by
  let K := (chartAt E p) '' tsupport f
  have hK : IsCompact K := hc.image_of_continuousOn ((chartAt E p).continuousOn.mono hs)
  have hKt : K ⊆ (chartAt E p).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (chartAt E p).map_source (hs hx)
  apply IntegrableOn.of_inter_support (chartAt E p).open_target.measurableSet
  apply (((contDiffOn_metricDensity g p).continuousOn.mono hKt).mul
    (hf.comp_continuousOn ((chartAt E p).continuousOn_symm.mono hKt))).integrableOn_compact hK |>.mono_set
  intro y hy
  refine ⟨(chartAt E p).symm y, ?_, (chartAt E p).right_inv hy.1⟩
  apply subset_tsupport
  intro hz
  exact hy.2 (by simp only [hz, mul_zero])

lemma metricChartIntegral_nonneg (g : SmoothMetric E M) (p : M) {f : M → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ metricChartIntegral g p f := by
  apply integral_nonneg
  intro y
  exact mul_nonneg (Real.sqrt_nonneg _) (hf _)


end

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

section
-- Preserve the structural size when Lean generates the atlas SizeOf instance.
local instance instSizeOfSmoothPartitionOfUnitySubtypeMemFinsetModelWithCornersSelfRealUniv_solutions [SizeOf E] [SizeOf M] (t : Finset M) :
    SizeOf (SmoothPartitionOfUnity t 𝓘(ℝ, E) M univ) :=
  @SmoothPartitionOfUnity._sizeOf_inst t E _ _ E _ 𝓘(ℝ, E) M _ _ univ _ _ _ _
    (fun _ => inferInstance)

structure MetricIntegralAtlas where
  t : Finset M
  ρ : SmoothPartitionOfUnity t 𝓘(ℝ, E) M univ
  subordinate : ρ.IsSubordinate (fun i => (chartAt E (i : M)).source)
end

namespace MetricIntegralAtlas
variable (A : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)

omit [T2Space M] in
lemma local_integrable (i : A.t) (f : M →ᵇ ℝ) :
    IntegrableOn (fun y => Real.sqrt (metricCoefficients g (i : M) y).det *
      (A.ρ i ((chartAt E (i : M)).symm y) * f ((chartAt E (i : M)).symm y)))
      (chartAt E (i : M)).target :=
  metricChart_integrable g i ((A.ρ i).property.continuous.mul f.continuous)
    (HasCompactSupport.of_compactSpace _) (tsupport_mul_subset_left.trans (A.subordinate i))

def integral (f : M →ᵇ ℝ) : ℝ :=
  ∑ i : A.t, metricChartIntegral g (i : M) (fun x => A.ρ i x * f x)

omit [T2Space M] in
lemma integral_add (f h : M →ᵇ ℝ) : A.integral g (f + h) = A.integral g f + A.integral g h := by
  simp only [integral, metricChartIntegral, BoundedContinuousFunction.add_apply, mul_add,
    MeasureTheory.integral_add (A.local_integrable g _ f) (A.local_integrable g _ h), Finset.sum_add_distrib]

omit [T2Space M] [CompactSpace M] in
lemma integral_smul (c : ℝ) (f : M →ᵇ ℝ) : A.integral g (c • f) = c * A.integral g f := by
  simp only [integral, metricChartIntegral, BoundedContinuousFunction.smul_apply, smul_eq_mul]
  simp_rw [show ∀ i : A.t, ∀ y, Real.sqrt (metricCoefficients g (i : M) y).det *
      (A.ρ i ((chartAt E (i : M)).symm y) * (c * f ((chartAt E (i : M)).symm y))) =
      c * (Real.sqrt (metricCoefficients g (i : M) y).det *
        (A.ρ i ((chartAt E (i : M)).symm y) * f ((chartAt E (i : M)).symm y))) by
    intros; ring]
  simp only [integral_const_mul, Finset.mul_sum]

omit [T2Space M] in
lemma integral_mono {f h : M →ᵇ ℝ} (hfh : ∀ x, f x ≤ h x) : A.integral g f ≤ A.integral g h := by
  unfold integral
  apply Finset.sum_le_sum
  intro i _
  apply setIntegral_mono_on (A.local_integrable g i f) (A.local_integrable g i h)
    (chartAt E (i : M)).open_target.measurableSet
  intro y _
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hfh _) (A.ρ.nonneg i _))
    (Real.sqrt_nonneg _)

omit [T2Space M] in
lemma integral_bound (f : M →ᵇ ℝ) : |A.integral g f| ≤ A.integral g 1 * ‖f‖ := by
  rw [abs_le]
  have h1 : A.integral g (‖f‖ • (1 : M →ᵇ ℝ)) = A.integral g 1 * ‖f‖ := by
    rw [A.integral_smul]; ring
  have h2 : A.integral g ((-‖f‖) • (1 : M →ᵇ ℝ)) = -(A.integral g 1 * ‖f‖) := by
    rw [A.integral_smul]; ring
  constructor
  · rw [← h2]
    apply A.integral_mono
    intro x
    simpa using (abs_le.mp ((Real.norm_eq_abs (f x)) ▸ f.norm_coe_le_norm x)).1
  · rw [← h1]
    apply A.integral_mono
    intro x
    simpa using (abs_le.mp ((Real.norm_eq_abs (f x)) ▸ f.norm_coe_le_norm x)).2

def integralCLM : (M →ᵇ ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := A.integral g
      map_add' := A.integral_add g
      map_smul' := fun c f => by simpa using A.integral_smul g c f }
    (A.integral g 1) (A.integral_bound g)

omit [T2Space M] in
lemma integral_pos {f : M →ᵇ ℝ} (hf : ∀ x, 0 ≤ f x) (hx : ∃ x, 0 < f x) :
    0 < A.integral g f := by
  classical
  obtain ⟨x, hx⟩ := hx
  obtain ⟨i, hi⟩ := A.ρ.exists_pos_of_mem (mem_univ x)
  have hxi : x ∈ (chartAt E (i : M)).source := A.subordinate i (subset_tsupport _ hi.ne')
  let F : E → ℝ := fun y => Real.sqrt (metricCoefficients g (i : M) y).det *
    (A.ρ i ((chartAt E (i : M)).symm y) * f ((chartAt E (i : M)).symm y))
  have hFc : ContinuousOn F (chartAt E (i : M)).target :=
    (contDiffOn_metricDensity g i).continuousOn.mul
      (((A.ρ i).property.continuous.mul f.continuous).comp_continuousOn
        (chartAt E (i : M)).continuousOn_symm)
  have hFo : IsOpen ({y | 0 < F y} ∩ (chartAt E (i : M)).target) := by
    rw [Set.inter_comm]
    exact hFc.isOpen_inter_preimage (chartAt E (i : M)).open_target isOpen_Ioi
  have hFx : (chartAt E (i : M)) x ∈ {y | 0 < F y} ∩ (chartAt E (i : M)).target := by
    refine ⟨?_, (chartAt E (i : M)).map_source hxi⟩
    dsimp [F]
    rw [(chartAt E (i : M)).left_inv hxi]
    exact mul_pos (Real.sqrt_pos.2 (metricCoefficients_posDef g i
      ((chartAt E (i : M)).map_source hxi)).det_pos) (mul_pos hi hx)
  have hpos : 0 < metricChartIntegral g (i : M) (fun x => A.ρ i x * f x) := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ (fun y => mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (A.ρ.nonneg i _) (hf _))))
      (A.local_integrable g i f)).2
    apply lt_of_lt_of_le (hFo.measure_pos volume ⟨_, hFx⟩)
    exact measure_mono (fun y hy => ⟨hy.1.ne', hy.2⟩)
  change 0 < ∑ j : A.t, metricChartIntegral g (j : M) (fun x => A.ρ j x * f x)
  exact lt_of_lt_of_le hpos (Finset.single_le_sum
    (fun (j : A.t) _ => metricChartIntegral_nonneg g j (fun x => mul_nonneg (A.ρ.nonneg j x) (hf x)))
    (Finset.mem_univ i))

end MetricIntegralAtlas

end

open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_MomentBesselLp
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

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_pow_mul_bessel_weight_le (x : E) (n : ℕ) (s : ℝ) :
    ‖x‖ ^ n * (1 + ‖x‖ ^ 2) ^ (-s / 2) ≤
      (1 + ‖x‖ ^ 2) ^ (-(s - n) / 2) := by
  have hp : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hnorm : ‖x‖ ≤ Real.sqrt (1 + ‖x‖ ^ 2) := by
    apply (Real.le_sqrt (norm_nonneg _) (le_of_lt hp)).mpr
    linarith
  calc
    _ ≤ (Real.sqrt (1 + ‖x‖ ^ 2)) ^ n * (1 + ‖x‖ ^ 2) ^ (-s / 2) := by
      gcongr
    _ = (1 + ‖x‖ ^ 2) ^ (-(s - n) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hp.le, ← Real.rpow_add hp]
      congr 1
      ring

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

lemma lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ x, f x * g x ∂μ) ^ (2 : ℕ) ≤
      (∫⁻ x, f x ∂μ) * ∫⁻ x, f x * g x ^ (2 : ℕ) ∂μ := by
  have h := ENNReal.lintegral_mul_norm_pow_le hf (hf.mul (hg.pow_const (2 : ℕ)))
    (p := (1 / 2 : ℝ)) (q := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have heq : (fun x => f x ^ (1 / 2 : ℝ) * (f x * g x ^ (2 : ℕ)) ^ (1 / 2 : ℝ)) =
      fun x => f x * g x := by
    ext x
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← mul_assoc,
      ← ENNReal.rpow_add_of_nonneg (1 / 2) (1 / 2) (by norm_num) (by norm_num)]
    norm_num [← ENNReal.rpow_natCast_mul]
  simp only [Pi.mul_apply] at h
  rw [heq] at h
  have hs := pow_le_pow_left' h 2
  simpa [mul_pow, ← ENNReal.rpow_mul_natCast] using hs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem young_lintegral_sq {f g : E → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, (∫⁻ y, f y * g (x - y)) ^ (2 : ℕ)) ≤
      (∫⁻ y, f y) ^ (2 : ℕ) * ∫⁻ x, g x ^ (2 : ℕ) := by
  calc
    _ ≤ ∫⁻ x, (∫⁻ y, f y) * ∫⁻ y, f y * g (x - y) ^ (2 : ℕ) := by
      apply lintegral_mono
      intro x
      exact lintegral_mul_sq_le volume hf.aemeasurable (by fun_prop)
    _ = (∫⁻ y, f y) * ∫⁻ x, ∫⁻ y, f y * g (x - y) ^ (2 : ℕ) := by
      rw [lintegral_const_mul'' _ (by fun_prop)]
    _ = (∫⁻ y, f y) * ∫⁻ y, ∫⁻ x, f y * g (x - y) ^ (2 : ℕ) := by
      rw [lintegral_lintegral_swap (by fun_prop)]
    _ = (∫⁻ y, f y) ^ (2 : ℕ) * ∫⁻ x, g x ^ (2 : ℕ) := by
      have hmeas (y : E) : AEMeasurable (fun x : E => g (x - y) ^ (2 : ℕ)) volume :=
        ((hg.comp (measurable_id.sub_const y)).pow_const 2).aemeasurable
      have hshift (y : E) : (∫⁻ x, g (x - y) ^ (2 : ℕ)) = ∫⁻ x, g x ^ (2 : ℕ) :=
        lintegral_sub_right_eq_self (fun x => g x ^ (2 : ℕ)) y
      simp_rw [lintegral_const_mul'' _ (hmeas _), hshift]
      rw [lintegral_mul_const'' _ hf.aemeasurable]
      ring

theorem young_eLpNorm_two {𝕜 : Type*} [RCLike 𝕜] {f g : E → 𝕜} (hf : Measurable f) (hg : Measurable g) :
    eLpNorm (fun x => ∫ y, f y * g (x - y)) 2 volume ≤
      eLpNorm f 1 volume * eLpNorm g 2 volume := by
  have hmeas : StronglyMeasurable (Function.uncurry (fun x y : E => f y * g (x - y))) :=
    ((hf.comp measurable_snd).mul (hg.comp (measurable_fst.sub measurable_snd))).stronglyMeasurable
  have hpoint (x : E) : ‖∫ y, f y * g (x - y)‖ₑ ≤ ∫⁻ y, ‖f y‖ₑ * ‖g (x - y)‖ₑ := by
    simpa only [enorm_mul] using enorm_integral_le_lintegral_enorm
      (fun y => f y * g (x - y))
  have hsq : (∫⁻ x, ‖∫ y, f y * g (x - y)‖ₑ ^ (2 : ℕ)) ≤
      (∫⁻ y, ‖f y‖ₑ) ^ (2 : ℕ) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℕ) := by
    exact (lintegral_mono fun x => pow_le_pow_left' (hpoint x) 2).trans
      (young_lintegral_sq hf.enorm hg.enorm)
  have hh := ENNReal.rpow_le_rpow hsq (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast_mul] at hh
  norm_num only [Nat.cast_ofNat, mul_one_div_cancel (by norm_num : (2 : ℝ) ≠ 0),
    ENNReal.rpow_one] at hh
  simpa only [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (1 : ℝ≥0∞) ≠ 0)
      (by norm_num : (1 : ℝ≥0∞) ≠ ⊤),
    ENNReal.toReal_ofNat, ENNReal.toReal_one, one_div_one, ENNReal.rpow_one,
    ENNReal.rpow_ofNat] using hh

open scoped SchwartzMap

lemma integrable_norm_mul_sub (f g : 𝓢(E, ℂ)) (x : E) :
    Integrable (fun y => ‖f y‖ * ‖g (x - y)‖) volume := by
  apply f.integrable.norm.mul_bdd
  · exact (g.continuous.comp (continuous_const.sub continuous_id)).norm.aestronglyMeasurable
  · filter_upwards with y
    simpa only [norm_norm] using SchwartzMap.norm_le_seminorm ℝ g (x - y)

lemma stronglyMeasurable_mulConvolution {𝕜 : Type*} [RCLike 𝕜] {f g : E → 𝕜}
    (hf : Measurable f) (hg : Measurable g) :
    StronglyMeasurable (fun x => ∫ y, f y * g (x - y)) := by
  have hm : StronglyMeasurable (Function.uncurry (fun x y : E => f y * g (x - y))) := by
    apply Measurable.stronglyMeasurable
    exact (hf.comp measurable_snd).mul (hg.comp (measurable_fst.sub measurable_snd))
  exact hm.integral_prod_right

lemma mulConvolution_comm {𝕜 : Type*} [RCLike 𝕜] (f g : E → 𝕜) (x : E) :
    (∫ y, f y * g (x - y)) = ∫ y, g y * f (x - y) := by
  rw [← integral_sub_left_eq_self (fun y => f y * g (x - y)) volume x]
  simp_rw [sub_sub_self, mul_comm]

open FourierTransform

lemma schwartz_fourierInv_convolution (f g : 𝓢(E, ℂ)) :
    𝓕⁻ (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f g) =
      SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕⁻ f) (𝓕⁻ g) := by
  ext x
  simp only [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg,
    ← SchwartzMap.fourier_coe, SchwartzMap.fourier_convolution,
    SchwartzMap.pairing_apply_apply, ContinuousLinearMap.mul_apply']

lemma schwartz_fourier_product (f g : 𝓢(E, ℂ)) :
    𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g) =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 f) (𝓕 g) := by
  have h := schwartz_fourierInv_convolution (𝓕 f) (𝓕 g)
  simpa only [fourierInv_fourier_eq, fourier_fourierInv_eq] using
    (congrArg (fun u : 𝓢(E, ℂ) => 𝓕 u) h).symm

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SobolevRepresentativeOrderCongr
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
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Filter Set Matrix Unitary
open scoped Topology ContDiff
open Set Function Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

def euclideanElliptic (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    (u : E → ℂ) (x : E) : ℂ :=
  (∑ i, ∑ j, (a i j x : ℂ) *
    fderiv ℝ (fun y => fderiv ℝ u y (b j)) x (b i)) +
    ∑ i, (c i x : ℂ) * fderiv ℝ u x (b i)


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped SchwartzMap BoundedContinuousFunction

section CompactDifferentialCoefficients
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

lemma hasCompactSupport_euclideanElliptic (b : ι → E) (a : ι → ι → E → ℝ)
    (c : ι → E → ℝ) {χ : E → ℂ} (hχ : HasCompactSupport χ) :
    HasCompactSupport (euclideanElliptic b a c χ) := by
  apply hχ.mono'
  intro x hx
  by_contra hn
  have hd : fderiv ℝ χ x = 0 := fderiv_of_notMem_tsupport ℝ hn
  have hdd (j : ι) : fderiv ℝ (fun y => fderiv ℝ χ y (b j)) x = 0 :=
    fderiv_of_notMem_tsupport ℝ (fun hh => hn (tsupport_fderiv_apply_subset ℝ (b j) hh))
  exact hx (by simp only [euclideanElliptic, hd, hdd, zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero])

end CompactDifferentialCoefficients



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

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction
section ChartContinuity
variable {E M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace F]
omit [NormedSpace ℝ E] in
lemma continuous_joint_of_chart (f : ℝ → M → F)
    (hf : ∀ t p, ContinuousAt (fun z : ℝ × E => f z.1 ((chartAt E p).symm z.2)) (t,chartAt E p p)) :
    Continuous (fun z : ℝ × M => f z.1 z.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t,p⟩
  have hc : ContinuousAt (fun z : ℝ × M => (z.1,chartAt E p z.2)) (t,p) :=
    continuousAt_fst.prodMk (((chartAt E p).continuousAt (mem_chart_source E p)).comp continuousAt_snd)
  apply ((hf t p).comp (f := fun z : ℝ × M => (z.1,chartAt E p z.2)) (x := (t,p)) hc).congr
  filter_upwards [continuous_snd.continuousAt.eventually ((chartAt E p).open_source.mem_nhds (mem_chart_source E p))] with z hz
  simp only [Function.comp_apply,(chartAt E p).left_inv hz]
end ChartContinuity

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
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

structure PositivePairing where
  form : X →L[ℝ] X →L[ℝ] ℝ
  symmetric : ∀ x y, form x y = form y x
  positive : ∀ x, x ≠ 0 → 0 < form x x

end

open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology


end YauCounterexamples
end

end OAI
end


