-- Prove2me | Definitions.Def_OAIQ1Mp000
-- name    : OAIQ1Mp000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T21:16:33.587848+00:00
-- url     : https://prove2.me/theorems/3e026e01-db8e-4f85-bbae-1a9a5ae9fa56
-- title:
--   Definitions bundle OAIQ1Mp000 of the split of OpenAI, Memory and precision in noiseless Gaussian regression
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MemoryPrecision.main`, carved from OpenAI's openai/math development (OpenAI, *Memory and precision in noiseless Gaussian regression*, OpenAI Math Release, September 27, 2026, result family 140, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 225 declarations of OpenAI's Lean: 57 definitions, 15 instances and 153 theorems. The definitions and types are `OAI.MemoryPrecision.BallAverage`, `OAI.MemoryPrecision.BlockCount`, `OAI.MemoryPrecision.CubeAmbient`, `OAI.MemoryPrecision.CubeBlockConstant`, `OAI.MemoryPrecision.CubeStep`, `OAI.MemoryPrecision.CubeStepConstant`, `OAI.MemoryPrecision.CubeSuccessConstant`, `OAI.MemoryPrecision.GaussianAmplitude`, `OAI.MemoryPrecision.GaussianConvolution`, `OAI.MemoryPrecision.Kernel.CubeSuccessEstimate`, `OAI.MemoryPrecision.Kernel.PointwisePrecisionEstimate`, `OAI.MemoryPrecision.Kernel.Policy.Borel`, `OAI.MemoryPrecision.Kernel.Policy.FixedSuccess`, `OAI.MemoryPrecision.Kernel.Policy.cont`, `OAI.MemoryPrecision.Kernel.Policy.marginal`, `OAI.MemoryPrecision.Kernel.Policy.version`, `OAI.MemoryPrecision.Kernel.Policy.versionCoordinates`, `OAI.MemoryPrecision.Kernel.SourceCubeStatement`, `OAI.MemoryPrecision.Kernel.SourceStreamStatement`, `OAI.MemoryPrecision.PiGaussianConvolution`, `OAI.MemoryPrecision.RealStep`, `OAI.MemoryPrecision.StepConstant`, `OAI.MemoryPrecision.StreamConstant`, `OAI.MemoryPrecision.SuccessConstant`, `OAI.MemoryPrecision.averageTranslate`, `OAI.MemoryPrecision.boxScalar`, `OAI.MemoryPrecision.cubeProject`, `OAI.MemoryPrecision.fiberSmoothing`, `OAI.MemoryPrecision.gaussianPeak`, `OAI.MemoryPrecision.labelTranslate`, `OAI.MemoryPrecision.radialExpand`, `OAI.MemoryPrecision.radialShrink`, `OAI.MemoryPrecision.realNormalize`, `OAI.MemoryPrecision.stochCont`, `OAI.MemoryPrecision.stochRoute`, `OAI.NoiselessRegression.HasLocalMassBound`, `OAI.NoiselessRegression.PolynomialMass`, `OAI.NoiselessRegression.Samples`, `OAI.NoiselessRegression.ambientSphereLaw`, `OAI.NoiselessRegression.capWeight` and 17 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `GaussianRegression_Blocks`, `GaussianRegression_Caps`, `GaussianRegression_GaussianKernel`, `GaussianRegression_Gram`, `GaussianRegression_Nets`, `GaussianRegression_Projection`, `GaussianRegression_ReplicaMoments`, `GaussianRegression_Rotational`, `GaussianRegression_Smoothing`, `GaussianRegression_Sphere`, `GaussianRegression_Support`, `MemoryPrecision_AmbientGram`, `MemoryPrecision_BallAverages`, `MemoryPrecision_CoefficientStep`, `MemoryPrecision_CubeArithmetic`, `MemoryPrecision_CubeBlock`, `MemoryPrecision_CubeContinuation`, `MemoryPrecision_CubeExperiment`, `MemoryPrecision_CubeGeometry`, `MemoryPrecision_CubeSuccess`, `MemoryPrecision_DensityPassage`, `MemoryPrecision_FiberDensity`, `MemoryPrecision_FiniteDensity`, `MemoryPrecision_GaussianConvolution`, `MemoryPrecision_KernelAdmissibility`, `MemoryPrecision_KernelCaps`, `MemoryPrecision_KernelEvaluation`, `MemoryPrecision_KernelModel`, `MemoryPrecision_KernelStream`, `MemoryPrecision_KernelVersion`, `MemoryPrecision_LabelTranslations`, `MemoryPrecision_MeasurableTests`, `MemoryPrecision_RadialMixture`, `MemoryPrecision_RealContinuation`, `MemoryPrecision_SharpGaussian`, `MemoryPrecision_SphericalProjection`, `MemoryPrecision_StochasticContinuation`, `MemoryPrecision_StreamArithmetic`, `MemoryPrecision_SuccessArithmetic`, `MemoryPrecision_WeightedImage`, `MemoryPrecision_WeightedSelection`, `ProjectionMoments_Model`, `ProjectionMoments_Polar`.
--
--   **Imports.** It imports the published bundle `Def_MemoryPrecision`.
--
--   **Imported by** (directly, in this split): the statement `OAI.MemoryPrecision.Kernel.source_cube_success`; the proofs of `OAI.MemoryPrecision.Kernel.source_cube_success` and `OAI.MemoryPrecision.main`.
-- source:
--   OpenAI, Memory and precision in noiseless Gaussian regression, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Memory-and-precision-in-noiseless-Gaussian-regression-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_MemoryPrecision

section
-- module Solutions.OAIQ1_Mem.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ1_Mem.ProjectionMoments_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section InlineMainProof

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal NNReal RealInnerProductSpace

universe u

namespace NoiselessRegression

abbrev Samples (d T : ℕ) := Fin T → Vector d

def sampleLaw (d T : ℕ) : Measure (Samples d T) :=
  Measure.pi fun _ => stdGaussian (Vector d)

def observationReference (d : ℕ) : Measure (Vector d × ℝ) :=
  (stdGaussian (Vector d)).prod volume

open scoped Topology

open InnerProductSpace

section SphereBounds

open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def sphereLaw : Measure (Metric.sphere (0 : E) 1) :=
  let σ := (volume : Measure E).toSphere
  (σ Set.univ)⁻¹ • σ

end SphereBounds

open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def ambientSphereLaw : Measure E := (sphereLaw (E := E)).map Subtype.val

end NoiselessRegression

end InlineMainProof

open scoped ENNReal NNReal RealInnerProductSpace Topology MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology

open MeasureTheory ProbabilityTheory Set Filter unitInterval
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace

open NoiselessRegression

open scoped ENNReal NNReal RealInnerProductSpace Topology

universe u

end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.GaussianRegression_Gram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Gram determinants, orthogonal distances, and product integration.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section GramFactorization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι : Type*} [Fintype ι]
lemma gram_linear_combination (w : ι → E) (T : Matrix ι ι ℝ) :
    Matrix.gram ℝ (fun j => ∑ i, (T i j) • w i) =
      T.transpose * Matrix.gram ℝ w * T := by
  ext a b
  simp only [Matrix.gram_apply, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply]
  simp only [Finset.sum_mul]
  congr 1
  ext j
  congr 1
  ext i
  ring

variable (n : ℕ)
def gsUpper (v : Fin n → E) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  (if i = j then 1 else 0) +
    if i < j then ⟪gramSchmidt ℝ v i, v j⟫ / ‖gramSchmidt ℝ v i‖ ^ 2 else 0

lemma gsUpper_expansion (v : Fin n → E) (j : Fin n) :
    ∑ i, (gsUpper n v i j) • gramSchmidt ℝ v i = v j := by
  simp only [gsUpper, add_smul, Finset.sum_add_distrib]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  conv_rhs => rw [gramSchmidt_def'' ℝ v j]
  congr 1
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

lemma gsUpper_det (v : Fin n → E) : (gsUpper n v).det = 1 := by
  have htri : (gsUpper n v).IsUpperTriangular := by
    intro i j hij
    change j < i at hij
    simp [gsUpper, (ne_of_gt hij), (not_lt_of_ge hij.le)]
  rw [Matrix.det_of_isUpperTriangular htri]
  simp [gsUpper]

lemma gram_gramSchmidt_diagonal (v : Fin n → E) :
    Matrix.gram ℝ (gramSchmidt ℝ v) = Matrix.diagonal (fun i => ‖gramSchmidt ℝ v i‖ ^ 2) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.gram_apply]
  · simp [Matrix.gram_apply, hij,
      gramSchmidt_orthogonal ℝ v hij]

theorem det_gram_eq_prod_gramSchmidt (v : Fin n → E) :
    (Matrix.gram ℝ v).det = ∏ i, ‖gramSchmidt ℝ v i‖ ^ 2 := by
  have hv : (fun j => ∑ i, (gsUpper n v i j) • gramSchmidt ℝ v i) = v :=
    funext (gsUpper_expansion n v)
  have h := gram_linear_combination (gramSchmidt ℝ v) (gsUpper n v)
  rw [hv] at h
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, gsUpper_det,
    one_mul, mul_one, gram_gramSchmidt_diagonal, Matrix.det_diagonal]
end GramFactorization

section GramDistances
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}
omit [FiniteDimensional ℝ E] in
lemma sub_gramSchmidt_mem_span (v : Fin n → E) (j : Fin n) :
    v j - gramSchmidt ℝ v j ∈ Submodule.span ℝ (v '' Set.Iio j) := by
  rw [← span_gramSchmidt_Iio ℝ v j]
  conv => arg 2; lhs; rw [gramSchmidt_def'' ℝ v j]
  rw [add_sub_cancel_left]
  exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, Finset.mem_Iio.mp hi, rfl⟩)

omit [FiniteDimensional ℝ E] in
lemma gramSchmidt_mem_span_orthogonal (v : Fin n → E) (j : Fin n) :
    gramSchmidt ℝ v j ∈ (Submodule.span ℝ (v '' Set.Iio j))ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨i, hi, rfl⟩
    exact gramSchmidt_inv_triangular ℝ v hi
  | zero => simp
  | add x y _ _ hx hy => simp [inner_add_right, hx, hy]
  | smul c x _ hx => simp [inner_smul_right, hx]

lemma gramSchmidt_eq_sub_starProjection (v : Fin n → E) (j : Fin n) :
    gramSchmidt ℝ v j = v j -
      (Submodule.span ℝ (v '' Set.Iio j)).starProjection (v j) := by
  have h := (Submodule.span ℝ (v '' Set.Iio j)).eq_starProjection_of_mem_orthogonal
    (u := v j) (sub_gramSchmidt_mem_span v j)
    (by simpa using gramSchmidt_mem_span_orthogonal v j)
  rw [h, sub_sub_cancel]

lemma norm_gramSchmidt_eq_infDist (v : Fin n → E) (j : Fin n) :
    ‖gramSchmidt ℝ v j‖ = Metric.infDist (v j)
      (Submodule.span ℝ (v '' Set.Iio j) : Set E) := by
  rw [gramSchmidt_eq_sub_starProjection, Submodule.starProjection_minimal,
    Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  rfl
lemma infDist_affine_mk' (p x : E) (K : Submodule ℝ E) :
    Metric.infDist x (AffineSubspace.mk' p K : Set E) =
      Metric.infDist (x - p) (K : Set E) := by
  rw [← EuclideanGeometry.dist_orthogonalProjection_eq_infDist,
    EuclideanGeometry.orthogonalProjection_apply_mem _ (AffineSubspace.self_mem_mk' p K),
    dist_eq_norm, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  change ‖x - _‖ = ⨅ y : K, ‖(x - p) - y‖
  rw [← Submodule.starProjection_minimal]
  simp only [AffineSubspace.direction_mk', vsub_eq_sub, vadd_eq_add,
    Submodule.coe_orthogonalProjectionOnto_apply]
  congr 1
  abel

lemma norm_gramSchmidt_sub_eq_affine_infDist (p : E) (t : Fin n → E) (j : Fin n) :
    ‖gramSchmidt ℝ (fun i => t i - p) j‖ =
      Metric.infDist (t j) (AffineSubspace.mk' p
        (Submodule.span ℝ ((fun i => t i - p) '' Set.Iio j)) : Set E) := by
  rw [infDist_affine_mk', norm_gramSchmidt_eq_infDist]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma image_Iio_castSucc (v : Fin (n+1) → E) (j : Fin n) :
    v '' Set.Iio j.castSucc = (fun i => v i.castSucc) '' Set.Iio j := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hin : i.val < n := lt_trans hi j.isLt
    exact ⟨⟨i.val, hin⟩, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.castSucc, hi, rfl⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma image_Iio_last (v : Fin (n+1) → E) :
    v '' Set.Iio (Fin.last n) = Set.range (fun i : Fin n => v i.castSucc) := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i.val, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.castSucc, i.isLt, rfl⟩

lemma gramSchmidt_castSucc (v : Fin (n+1) → E) (j : Fin n) :
    gramSchmidt ℝ v j.castSucc = gramSchmidt ℝ (fun i => v i.castSucc) j := by
  rw [gramSchmidt_eq_sub_starProjection, gramSchmidt_eq_sub_starProjection,
    image_Iio_castSucc]

variable [MeasurableSpace E] [BorelSpace E]
lemma measurable_gramSchmidt (j : Fin n) :
    Measurable (fun v : Fin n → E => gramSchmidt ℝ v j) := by
  refine (wellFounded_lt : WellFounded ((· < ·) : Fin n → Fin n → Prop)).induction
    (C := fun j : Fin n => Measurable (fun v : Fin n → E => gramSchmidt ℝ v j)) j ?_
  intro j ih
  have heq : (fun v : Fin n → E => gramSchmidt ℝ v j) =
      fun v => v j - ∑ i ∈ Finset.Iio j,
        (⟪gramSchmidt ℝ v i, v j⟫ / ‖gramSchmidt ℝ v i‖ ^ 2) • gramSchmidt ℝ v i := by
    ext v
    rw [gramSchmidt_def]
    simp only [Submodule.starProjection_singleton]
    rfl
  rw [heq]
  apply (measurable_pi_apply j).sub
  apply Finset.measurable_sum
  intro i hi
  have hi' := ih i (Finset.mem_Iio.mp hi)
  exact ((hi'.inner (measurable_pi_apply j)).div (hi'.norm.pow_const 2)).smul hi'
end GramDistances

variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]
lemma lintegral_pi_snoc (f : (Fin (n+1) → E) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ v, f v ∂Measure.pi (fun _ => ν) =
      ∫⁻ v : Fin n → E, ∫⁻ x, f (Fin.snoc v x) ∂ν ∂Measure.pi (fun _ => ν) := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) (Fin.last n)).symm
  rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) f,
    lintegral_prod_symm]
  · congr 1
    ext v
    congr 1
    ext x
    congr 1
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    exact Fin.insertNth_last' x v
  · exact (hf.comp (MeasurableEquiv.measurable _)).aemeasurable

end NoiselessRegression

end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.GaussianRegression_GaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Gaussian coordinate domination and replica kernel bounds.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section GaussianDomination
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma orthonormal_gaussian_map {n : ℕ} {u : Fin n → E} (hu : Orthonormal ℝ u) :
    (stdGaussian E).map (fun x => fun i => ⟪u i, x⟫) =
      Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  let f : E → EuclideanSpace ℝ (Fin n) := fun x => WithLp.toLp 2 (fun i => ⟪u i, x⟫)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have he : (stdGaussian E).map f = stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    apply Measure.ext_of_charFun
    ext t
    have hi (x : E) : ⟪f x, t⟫ = ⟪x, ∑ i, t i • u i⟫ := by
      simp [f, PiLp.inner_apply, inner_sum, inner_smul_right, real_inner_comm x]
    have hn : ‖∑ i, t i • u i‖ ^ 2 = ‖t‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hu.inner_sum, EuclideanSpace.real_norm_sq_eq]
      simp [pow_two]
    rw [charFun_apply, integral_map hf.aemeasurable (by fun_prop)]
    simp_rw [hi]
    change charFun (stdGaussian E) (∑ i, t i • u i) = _
    rw [charFun_stdGaussian, charFun_stdGaussian]
    congr 2
    exact_mod_cast congrArg Neg.neg hn
  have h := congrArg (Measure.map (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ))) he
  rw [← map_pi_eq_stdGaussian] at h
  simpa [Measure.map_map (WithLp.measurable_ofLp _ _) hf,
    Measure.map_map (WithLp.measurable_ofLp _ _) (WithLp.measurable_toLp _ _),
    Function.comp_def, f, WithLp.ofLp_toLp, Measure.map_id] using h

lemma measure_pi_mono {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] {μ ν : ∀ i, Measure (X i)}
    (h : ∀ i, μ i ≤ ν i) : Measure.pi μ ≤ Measure.pi ν := by
  have ho : OuterMeasure.pi (fun i => (μ i).toOuterMeasure) ≤
      OuterMeasure.pi (fun i => (ν i).toOuterMeasure) := by
    apply OuterMeasure.le_pi.mpr
    intro s _
    exact (OuterMeasure.pi_pi_le _ s).trans (Finset.prod_le_prod' fun i _ => h i (s i))
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.pi_def, Measure.pi_def, toMeasure_apply _ _ hs, toMeasure_apply _ _ hs]
  exact ho s

lemma measure_pi_smul {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (c : ℝ≥0∞) (hc : c ≠ ∞) :
    Measure.pi (fun i => c • μ i) = c ^ Fintype.card ι • Measure.pi μ := by
  lift c to ℝ≥0 using hc
  simp_rw [Measure.coe_nnreal_smul]
  apply Measure.pi_eq
  intro s _
  simp only [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]

end GaussianDomination

section ReplicaKernel
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

lemma lintegral_fin_prod (n : ℕ) (f : Fin n → X → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → X, ∏ i, f i (x i) ∂Measure.pi (fun _ => μ) =
      ∏ i, ∫⁻ x, f i x ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [lintegral_pi_snoc μ _ (by fun_prop)]
    simp_rw [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
    simp_rw [lintegral_const_mul _ (hf (Fin.last n))]
    rw [lintegral_mul_const _ (by fun_prop), ih _ (fun i => hf i.castSucc)]

lemma lintegral_pow_pi (f : X → ℝ≥0∞) (hf : Measurable f) (n : ℕ) :
    (∫⁻ x, f x ∂μ)^n =
      ∫⁻ x : Fin n → X, ∏ i, f (x i) ∂Measure.pi (fun _ => μ) := by
  rw [lintegral_fin_prod μ n _ (fun _ => hf)]
  simp

lemma lintegral_product_differences (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ)
    (hφ1 : ∫⁻ x, φ x = 1) (m n : ℕ) (y : Fin m → ℝ) :
    ∫⁻ z : Fin m → Fin n → ℝ,
      ∏ j, φ (y j) * ∏ i, φ (y j - z j i) = ∏ j, φ (y j) := by
  rw [volume_pi, lintegral_fin_prod (volume : Measure (Fin n → ℝ)) m
    (fun j z => φ (y j) * ∏ i, φ (y j - z i)) (by intro i; fun_prop)]
  apply Finset.prod_congr rfl
  intro j _
  rw [lintegral_const_mul _ (by fun_prop), volume_pi,
    lintegral_fin_prod (volume : Measure ℝ) n
      (fun _ z => φ (y j - z)) (by intro i; fun_prop)]
  simp_rw [lintegral_sub_left_eq_self φ (y j), hφ1]
  simp

end ReplicaKernel

end NoiselessRegression

end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.GaussianRegression_Nets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Local mass bounds and quantitative finite Euclidean nets.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

noncomputable section

universe u

namespace NoiselessRegression

section FrostmanGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def HasLocalMassBound (ν : Measure E) (a : ℝ) : Prop :=
  ∀ t ∈ ν.support, ∀ r : ℝ, 0 < r →
    ν (Metric.closedBall t r) ≤ ENNReal.ofReal (r ^ a)

theorem card_le_volume_ratio (s : Finset E) {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hs : ∀ x ∈ s, ‖x‖ ≤ R)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ dist x y) :
    (s.card : ℝ) ≤ ((R + r / 2) / (r / 2)) ^ Module.finrank ℝ E := by
  classical
  let ν : Measure E := Measure.addHaar
  let δ : ℝ := r / 2
  let ρ : ℝ := R + r / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let A : Set E := ⋃ c ∈ s, Metric.ball c δ
  have hd : Set.Pairwise (s : Set E) (fun c d => Disjoint (Metric.ball c δ) (Metric.ball d δ)) := by
    intro c hc d hd hcd
    apply Metric.ball_disjoint_ball
    simpa [δ] using hsep c hc d hd hcd
  have hsub : A ⊆ Metric.ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ?_
    apply Metric.ball_subset_ball'
    dsimp [δ, ρ]
    rw [dist_zero_right]
    linarith [hs x hx]
  have I :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ Module.finrank ℝ E) * ν (Metric.ball 0 1) ≤
        ENNReal.ofReal (ρ ^ Module.finrank ℝ E) * ν (Metric.ball 0 1) := by
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ Module.finrank ℝ E) * ν (Metric.ball 0 1) = ν A := by
        dsimp only [A]
        rw [measure_biUnion_finset hd (fun _ _ => Metric.isOpen_ball.measurableSet)]
        simp only [ν.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ ν (Metric.ball (0 : E) ρ) := measure_mono hsub
      _ = _ := ν.addHaar_ball_of_pos 0 hρ
  have J : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ Module.finrank ℝ E) ≤
      ENNReal.ofReal (ρ ^ Module.finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (Metric.measure_ball_pos ν 0 zero_lt_one).ne'
      measure_ball_lt_top.ne).mp I
  have K : (s.card : ℝ) * δ ^ Module.finrank ℝ E ≤ ρ ^ Module.finrank ℝ E := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg hδ.le _)] using
      ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) J
  rw [div_pow]
  exact (le_div_iff₀ (pow_pos hδ _)).mpr K

end FrostmanGeometry

section FiniteNets

variable {E : Type*} [PseudoMetricSpace E]

theorem exists_net_of_finite_packing_bound (A : Set E) {r : ℝ} (hr : 0 ≤ r) (N : ℕ)
    (hcard : ∀ s : Finset E, (∀ x ∈ s, x ∈ A) →
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r < dist x y) → s.card ≤ N) :
    ∃ s : Finset E, (∀ x ∈ s, x ∈ A) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r < dist x y) ∧
      ∀ x ∈ A, ∃ y ∈ s, dist x y ≤ r := by
  classical
  let S : Set ℕ := {n | ∃ s : Finset E, (∀ x ∈ s, x ∈ A) ∧
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r < dist x y) ∧ s.card = n}
  have hS : S.Finite := (Set.finite_Iic N).subset (by
    rintro n ⟨s, hs, hsep, rfl⟩
    exact hcard s hs hsep)
  have hS0 : S.Nonempty := ⟨0, ∅, by simp⟩
  obtain ⟨n, hn, hmax⟩ := Set.exists_max_image S id hS hS0
  obtain ⟨s, hs, hsep, rfl⟩ := hn
  refine ⟨s, hs, hsep, ?_⟩
  intro x hx
  by_contra! hnot
  have hxs : x ∉ s := by
    intro h
    have := hnot x h
    simpa using lt_of_le_of_lt hr this
  have hins : ∀ y ∈ insert x s, y ∈ A := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hx
    · exact hs y hy
  have hsep' : ∀ y ∈ insert x s, ∀ z ∈ insert x s, y ≠ z → r < dist y z := by
    intro y hy z hz hne
    rcases Finset.mem_insert.mp hy with hxy | hys
    · subst y
      rcases Finset.mem_insert.mp hz with hxz | hzs
      · exact (hne hxz.symm).elim
      · exact hnot z hzs
    · rcases Finset.mem_insert.mp hz with hxz | hzs
      · subst z
        simpa [dist_comm] using hnot y hys
      · exact hsep y hys z hzs hne
  have hinS : (insert x s).card ∈ S := ⟨insert x s, hins, hsep', rfl⟩
  have hh := hmax _ hinS
  simp only [id_eq, Finset.card_insert_of_notMem hxs] at hh
  omega

end FiniteNets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_unit_ball_net {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ s : Finset E, (∀ x ∈ s, ‖x‖ ≤ 1) ∧
      (s.card : ℝ) ≤ (3 / r) ^ Module.finrank ℝ E ∧
      ∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ s, dist x y ≤ r := by
  classical
  have hbound : ∀ s : Finset E, (∀ x ∈ s, ‖x‖ ≤ 1) →
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r < dist x y) →
      (s.card : ℝ) ≤ (3 / r) ^ Module.finrank ℝ E := by
    intro s hs hsep
    refine (card_le_volume_ratio s hr zero_le_one hs
      (fun x hx y hy hne => (hsep x hx y hy hne).le)).trans ?_
    apply pow_le_pow_left₀ (by positivity)
    apply (div_le_div_iff₀ (by positivity : 0 < r / 2) hr).mpr
    nlinarith
  obtain ⟨s, hs, hsep, hnet⟩ := exists_net_of_finite_packing_bound
    {x : E | ‖x‖ ≤ 1} hr.le ⌈(3 / r) ^ Module.finrank ℝ E⌉₊
    (by
      intro s hs hsep
      exact_mod_cast (hbound s hs hsep).trans (Nat.le_ceil _))
  exact ⟨s, hs, hbound s hs hsep, hnet⟩

end NoiselessRegression

end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.GaussianRegression_ReplicaMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Inverse Gram moments and almost-everywhere replica independence.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section ReplicaMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def replicaWeight (m : ℕ) (p : E) {n : ℕ} (v : Fin n → E) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal ((‖gramSchmidt ℝ (fun j => v j - p) i‖)⁻¹ ^ m)

lemma measurable_replicaWeight (m : ℕ) (p : E) (n : ℕ) :
    Measurable (replicaWeight m p (n := n)) := by
  have hs : Measurable (fun v : Fin n → E => fun j => v j - p) := by fun_prop
  exact Finset.measurable_prod _ fun i _ =>
    (((measurable_gramSchmidt i).comp hs).norm.inv.pow_const m).ennreal_ofReal

omit [MeasurableSpace E] [BorelSpace E] in
lemma replicaWeight_snoc (m : ℕ) (p : E) {n : ℕ} (v : Fin n → E) (x : E) :
    replicaWeight m p (Fin.snoc v x) = replicaWeight m p v *
      ENNReal.ofReal ((Metric.infDist x (AffineSubspace.mk' p
        (Submodule.span ℝ (Set.range (fun i => v i - p))) : Set E))⁻¹ ^ m) := by
  unfold replicaWeight
  rw [Fin.prod_univ_castSucc]
  simp only [gramSchmidt_castSucc, Fin.snoc_castSucc]
  rw [norm_gramSchmidt_sub_eq_affine_infDist, image_Iio_last]
  simp only [Fin.snoc_last, Fin.snoc_castSucc]

def replicaConstant (ν : Measure E) (a : ℝ) (m : ℕ) : ℝ≥0∞ :=
  ν Set.univ + ENNReal.ofReal ((3 : ℝ) ^ Module.finrank ℝ E * (4 : ℝ) ^ a) *
    (2 : ℝ≥0∞) ^ (m+1)

end ReplicaMoments
section AePiLast
variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]
lemma ae_pi_snoc {P : (Fin (n+1) → E) → Prop} (hP : MeasurableSet {v | P v}) :
    (∀ᵐ v ∂Measure.pi (fun _ => ν), P v) ↔
      ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => ν), ∀ᵐ x ∂ν, P (Fin.snoc v x) := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) (Fin.last n)).symm
  rw [← hp.map_eq, MeasurableEmbedding.ae_map_iff (MeasurableEquiv.measurableEmbedding _)]
  have heq : (fun z : E × (Fin n → E) =>
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) (Fin.last n)).symm z) =
      fun z => Fin.snoc z.2 z.1 := by
    ext z : 1
    change (Fin.last n).insertNth (α := fun _ => E) z.1 z.2 = _
    exact Fin.insertNth_last' z.1 z.2
  have hm : Measurable (fun z : E × (Fin n → E) => Fin.snoc (α := fun _ => E) z.2 z.1) := by
    rw [← heq]
    exact hp.measurable
  change (∀ᵐ z ∂ν.prod (Measure.pi (fun _ : Fin n => ν)),
      P ((fun z => (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E)
        (Fin.last n)).symm z) z)) ↔ _
  have hPP : MeasurableSet {z : E × (Fin n → E) | P (Fin.snoc z.2 z.1)} := hP.preimage hm
  rw [heq, Measure.ae_prod_iff_ae_ae hPP]
  exact Measure.ae_ae_comm hPP
end AePiLast

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma measurableSet_gramSchmidt_ne_zero (p : E) (n : ℕ) :
    MeasurableSet {v : Fin n → E | ∀ i, gramSchmidt ℝ (fun j => v j - p) i ≠ 0} := by
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  have h := (measurable_gramSchmidt i).comp
    (show Measurable (fun v : Fin n → E => fun j => v j - p) by fun_prop)
  exact (measurableSet_eq_fun h measurable_const).compl

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma sqrt_det_gram (n : ℕ) (v : Fin n → E) :
    Real.sqrt (Matrix.gram ℝ v).det = ∏ i, ‖gramSchmidt ℝ v i‖ := by
  rw [det_gram_eq_prod_gramSchmidt, Real.sqrt_prod _ (fun _ _ => sq_nonneg _)]
  simp only [Real.sqrt_sq (norm_nonneg _)]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma replicaWeight_eq_det (m : ℕ) (p : E) {n : ℕ} (v : Fin n → E) :
    replicaWeight m p v = ENNReal.ofReal
      ((Real.sqrt (Matrix.gram ℝ (fun j => v j - p)).det)⁻¹ ^ m) := by
  rw [sqrt_det_gram, ← Finset.prod_inv_distrib, ← Finset.prod_pow]
  exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)).symm

end NoiselessRegression

end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.GaussianRegression_Smoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Projection smoothing, Gaussian noise, and bounds under weak limits.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section SmoothingMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def projectionSmoothing (ν : Measure E) (φ : ℝ → ℝ≥0∞) (m : ℕ)
    (z : (Fin m → E) × (Fin m → ℝ)) : ℝ≥0∞ :=
  ∫⁻ t, ∏ j, φ (z.2 j - ⟪t, z.1 j⟫) ∂ν

lemma measurable_projectionSmoothing (ν : Measure E) [SFinite ν]
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (m : ℕ) :
    Measurable (projectionSmoothing ν φ m) := by
  apply Measurable.lintegral_prod_right
  fun_prop

lemma projectionSmoothing_pow (ν : Measure E) [SigmaFinite ν]
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (m n : ℕ)
    (z : (Fin m → E) × (Fin m → ℝ)) :
    (projectionSmoothing ν φ m z)^(n+1) =
      ∫⁻ w : E × (Fin n → E),
        (∏ j, φ (z.2 j - ⟪w.1, z.1 j⟫)) *
          ∏ i, ∏ j, φ (z.2 j - ⟪w.2 i, z.1 j⟫)
        ∂ν.prod (Measure.pi (fun _ => ν)) := by
  rw [lintegral_prod _ (by fun_prop)]
  have hG : Measurable (fun v : Fin n → E =>
      ∏ i, ∏ j, φ (z.2 j - ⟪v i, z.1 j⟫)) := by fun_prop
  simp_rw [lintegral_const_mul _ hG]
  rw [lintegral_mul_const _ (by fun_prop), ← lintegral_pow_pi ν
    (fun t : E => ∏ j, φ (z.2 j - ⟪t, z.1 j⟫)) (by fun_prop) n]
  exact pow_succ' _ _

end SmoothingMoments

section ProductDensity
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

lemma measure_pi_withDensity (n : ℕ) (f : Fin n → X → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) [∀ i, SigmaFinite (μ.withDensity (f i))] :
    Measure.pi (fun i => μ.withDensity (f i)) =
      (Measure.pi (fun _ : Fin n => μ)).withDensity (fun x => ∏ i, f i (x i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have he (x : Fin n → X) :
      (Set.univ.pi s).indicator (fun x => ∏ i, f i (x i)) x =
        ∏ i, (s i).indicator (f i) (x i) := by
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ =>
        (Set.indicator_of_mem (hx i (Set.mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem hx]
      have : ∃ i, x i ∉ s i := by simpa only [Set.mem_univ_pi, not_forall] using hx
      obtain ⟨i, hi⟩ := this
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  simp_rw [he]
  rw [lintegral_fin_prod μ n _ (fun i => (hf i).indicator (hs i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [lintegral_indicator (hs i), withDensity_apply _ (hs i)]
end ProductDensity

lemma pi_gaussian_map_scale (m : ℕ) (δ : ℝ) :
    (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map
      (fun u => fun j => δ * u j) =
      Measure.pi (fun _ : Fin m => gaussianReal 0 (NNReal.mk (δ^2) (sq_nonneg δ))) := by
  rw [Measure.pi_map_pi (f := fun _ : Fin m => fun x : ℝ => δ * x)
    (fun _ => (by fun_prop : Measurable (fun x : ℝ => δ * x)).aemeasurable)]
  simp_rw [gaussianReal_map_const_mul, mul_zero, mul_one]

lemma pi_gaussian_withDensity (m : ℕ) (v : ℝ≥0) (hv : v ≠ 0) :
    Measure.pi (fun _ : Fin m => gaussianReal 0 v) =
      (volume : Measure (Fin m → ℝ)).withDensity (fun y => ∏ j, gaussianPDF 0 v (y j)) := by
  simp_rw [gaussianReal_of_var_ne_zero _ hv]
  have : SigmaFinite ((volume : Measure ℝ).withDensity (gaussianPDF 0 v)) := by
    rw [← gaussianReal_of_var_ne_zero 0 hv]
    infer_instance
  rw [measure_pi_withDensity (volume : Measure ℝ) m
    (fun _ => gaussianPDF 0 v) (fun _ => measurable_gaussianPDF 0 v)]
  rfl
lemma lintegral_gaussian_shift_scale (m : ℕ) (δ : ℝ) (hδ : δ ≠ 0)
    (a : Fin m → ℝ) (f : (Fin m → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ u : Fin m → ℝ, f (fun j => a j + δ * u j)
      ∂Measure.pi (fun _ => gaussianReal 0 1) =
    ∫⁻ y : Fin m → ℝ, (∏ j, gaussianPDF 0 (NNReal.mk (δ^2) (sq_nonneg δ)) (y j - a j)) * f y := by
  let v : ℝ≥0 := NNReal.mk (δ^2) (sq_nonneg δ)
  have hv : v ≠ 0 := by
    rw [← NNReal.coe_ne_zero]
    exact pow_ne_zero 2 hδ
  have he :
      (∫⁻ u : Fin m → ℝ, f (fun j => a j + δ * u j)
        ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫⁻ y : Fin m → ℝ, f (a + y) ∂Measure.pi (fun _ => gaussianReal 0 v) := by
    rw [← pi_gaussian_map_scale m δ, lintegral_map (by fun_prop) (by fun_prop)]
    rfl
  rw [he, pi_gaussian_withDensity m v hv,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  have hh (y : Fin m → ℝ) :
      (∏ j, gaussianPDF 0 v (y j)) * f (a + y) =
      (fun z : Fin m → ℝ => (∏ j, gaussianPDF 0 v (z j - a j)) * f z) (a + y) := by
    simp only [Pi.add_apply, add_sub_cancel_left]
  exact (lintegral_congr (μ := volume) hh).trans (lintegral_add_left_eq_self
    (μ := volume) (fun z : Fin m → ℝ => (∏ j, gaussianPDF 0 v (z j - a j)) * f z) a)

section HolderSet
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
lemma withDensity_apply_le_moment (f : X → ℝ≥0∞) (hf : Measurable f)
    {p : ℝ} (hp : 1 < p) {C : ℝ≥0∞}
    (hC : ∫⁻ x, f x ^ p ∂μ ≤ C) (S : Set X) (hS : MeasurableSet S) :
    μ.withDensity f S ≤ C^(1/p) * (μ S)^(1 - 1/p) := by
  have hpq := Real.HolderConjugate.conjExponent hp
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict S) hpq
    hf.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
  have he : 1 / (Real.conjExponent p) = 1 - 1/p := by
    have hh := hpq.inv_add_inv_eq_one
    simpa only [one_div] using (eq_sub_of_add_eq' hh)
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply_univ, one_mul, he] at h
  rw [withDensity_apply _ hS]
  exact h.trans (mul_le_mul' (ENNReal.rpow_le_rpow
    ((lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)).trans hC) (by positivity)) le_rfl)
end HolderSet

section LimitSet
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace Y] [BorelSpace Y]
  (ρ : Measure X) (τ : Measure Y)

lemma map_apply_open_le_of_tendsto (F : X → Y) (Fₖ : ℕ → X → Y)
    (hF : Measurable F) (hFₖ : ∀ k, Measurable (Fₖ k))
    (ht : ∀ x, Tendsto (fun k => Fₖ k x) atTop (𝓝 (F x)))
    (C : ℝ≥0∞) (α : ℝ)
    (hbound : ∀ k U, IsOpen U → (ρ.map (Fₖ k)) U ≤ C * (τ U)^α)
    (U : Set Y) (hU : IsOpen U) :
    (ρ.map F) U ≤ C * (τ U)^α := by
  let f : ℕ → X → ℝ≥0∞ := fun k => (Fₖ k ⁻¹' U).indicator (fun _ => 1)
  have hf : ∀ k, Measurable (f k) := fun k =>
    measurable_const.indicator (hU.measurableSet.preimage (hFₖ k))
  have hind : ∀ x, (F ⁻¹' U).indicator (fun _ => (1 : ℝ≥0∞)) x ≤
      atTop.liminf (fun k => f k x) := by
    intro x
    by_cases hx : F x ∈ U
    · rw [Set.indicator_of_mem (show x ∈ F ⁻¹' U from hx)]
      apply le_liminf_of_le (by isBoundedDefault)
      filter_upwards [(ht x).eventually (hU.mem_nhds hx)] with k hk
      change 1 ≤ (Fₖ k ⁻¹' U).indicator (fun _ => (1 : ℝ≥0∞)) x
      rw [Set.indicator_of_mem (show x ∈ Fₖ k ⁻¹' U from hk)]
    · rw [Set.indicator_of_notMem (show x ∉ F ⁻¹' U from hx)]
      exact zero_le
  calc
    (ρ.map F) U = ∫⁻ x, (F ⁻¹' U).indicator (fun _ => (1 : ℝ≥0∞)) x ∂ρ := by
      rw [Measure.map_apply hF hU.measurableSet,
        lintegral_indicator (hU.measurableSet.preimage hF)]
      simp
    _ ≤ ∫⁻ x, atTop.liminf (fun k => f k x) ∂ρ := lintegral_mono hind
    _ ≤ atTop.liminf (fun k => ∫⁻ x, f k x ∂ρ) := lintegral_liminf_le hf
    _ ≤ _ := by
      apply liminf_le_of_frequently_le (hu_le := by isBoundedDefault)
      apply Filter.Eventually.frequently
      filter_upwards [] with k
      have hk := hbound k U hU
      simpa [f, lintegral_indicator (hU.measurableSet.preimage (hFₖ k)),
        Measure.map_apply (hFₖ k) hU.measurableSet] using hk
end LimitSet

variable {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]

lemma ennreal_rpow_iInf {ι : Sort*} (f : ι → ℝ≥0∞) {α : ℝ} (hα : 0 < α) :
    (⨅ i, f i)^α = ⨅ i, (f i)^α :=
  (ENNReal.orderIsoRpow α hα).map_iInf f

lemma measure_apply_le_of_isOpen (μ τ : Measure Y) [τ.OuterRegular]
    {C : ℝ≥0∞} (hC : C ≠ ∞) {α : ℝ} (hα : 0 < α)
    (hbound : ∀ U, IsOpen U → μ U ≤ C * (τ U)^α) (S : Set Y) :
    μ S ≤ C * (τ S)^α := by
  by_cases hC0 : C = 0
  · simp only [hC0, zero_mul] at hbound ⊢
    exact (measure_mono (Set.subset_univ S)).trans (hbound Set.univ isOpen_univ)
  rw [S.measure_eq_iInf_isOpen τ]
  simp_rw [ennreal_rpow_iInf _ hα, ENNReal.mul_iInf_of_ne hC0 hC]
  exact le_iInf fun U => le_iInf fun hSU => le_iInf fun hU =>
    (measure_mono hSU).trans (hbound U hU)

end NoiselessRegression

end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.GaussianRegression_Projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Exact noiseless projection laws and completed-event bounds.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section ProjectionCoupling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def matrixLabelReference (m : ℕ) : Measure ((Fin m → E) × (Fin m → ℝ)) :=
  (Measure.pi (fun _ => stdGaussian E)).prod volume

def projectionLaw (ν : Measure E) (m : ℕ) : Measure ((Fin m → E) × (Fin m → ℝ)) :=
  ((Measure.pi (fun _ => stdGaussian E)).prod ν).map
    (fun z => (z.1, fun j => ⟪z.2, z.1 j⟫))

def gaussianCoupling (ν : Measure E) (m : ℕ) :
    Measure ((Fin m → E) × (E × (Fin m → ℝ))) :=
  (Measure.pi (fun _ => stdGaussian E)).prod
    (ν.prod (Measure.pi (fun _ => gaussianReal 0 1)))

def noisyObservation (m : ℕ) (δ : ℝ)
    (z : (Fin m → E) × (E × (Fin m → ℝ))) : (Fin m → E) × (Fin m → ℝ) :=
  (z.1, fun j => ⟪z.2.1, z.1 j⟫ + δ * z.2.2 j)

lemma measurable_noisyObservation (m : ℕ) (δ : ℝ) :
    Measurable (noisyObservation (E := E) m δ) := by
  unfold noisyObservation
  fun_prop

lemma gaussianCoupling_map_noisyObservation_zero (ν : Measure E) [SigmaFinite ν] (m : ℕ) :
    (gaussianCoupling ν m).map (noisyObservation m 0) = projectionLaw ν m := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_noisyObservation m 0),
    projectionLaw, lintegral_map hf (by fun_prop)]
  dsimp [gaussianCoupling, noisyObservation]
  simp only [zero_mul, add_zero]
  rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro A
  rw [lintegral_prod _ (by fun_prop)]
  simp

lemma gaussianCoupling_map_noisyObservation (ν : Measure E) [SigmaFinite ν]
    (m : ℕ) (δ : ℝ) (hδ : δ ≠ 0) :
    (gaussianCoupling ν m).map (noisyObservation m δ) =
      (matrixLabelReference (E := E) m).withDensity
        (projectionSmoothing ν (gaussianPDF 0 (NNReal.mk (δ^2) (sq_nonneg δ))) m) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_noisyObservation m δ),
    lintegral_withDensity_eq_lintegral_mul _
      (measurable_projectionSmoothing _ _ (measurable_gaussianPDF _ _) _) hf]
  dsimp [gaussianCoupling, matrixLabelReference, noisyObservation]
  rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by
    exact ((measurable_projectionSmoothing _ _ (measurable_gaussianPDF _ _) _).mul hf).aemeasurable)]
  apply lintegral_congr
  intro A
  rw [lintegral_prod _ (by fun_prop)]
  have he (p : E) := lintegral_gaussian_shift_scale m δ hδ
    (fun j => ⟪p, A j⟫) (fun y => f (A, y)) (hf.comp (measurable_const.prodMk measurable_id))
  simp_rw [he]
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_congr
  intro y
  rw [lintegral_mul_const _ (by fun_prop)]
  rfl
lemma matrixLabelReference_outerRegular (m : ℕ) :
    (matrixLabelReference (E := E) m).OuterRegular := by
  unfold matrixLabelReference
  exact (Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _).toOuterRegular

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma tendsto_noisyObservation (m : ℕ)
    (z : (Fin m → E) × (E × (Fin m → ℝ))) :
    Tendsto (fun k : ℕ => noisyObservation m (1 / ((k : ℝ) + 1)) z)
      atTop (𝓝 (noisyObservation m 0 z)) := by
  apply Filter.Tendsto.prodMk_nhds tendsto_const_nhds
  apply tendsto_pi_nhds.mpr
  intro j
  exact tendsto_const_nhds.add
    (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const _)

end ProjectionCoupling

end NoiselessRegression

end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.GaussianRegression_Support
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite-volume enclosures for Gaussian matrix observations.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

open scoped Pointwise

def coordinateNorm {m : ℕ} (y : Fin m → ℝ) : ℝ := ‖WithLp.toLp 2 y‖

@[fun_prop] lemma continuous_coordinateNorm {m : ℕ} :
    Continuous (coordinateNorm (m := m)) := by
  unfold coordinateNorm
  fun_prop

lemma coordinateNorm_sq {m : ℕ} (y : Fin m → ℝ) :
    coordinateNorm y ^ 2 = ∑ j, (y j)^2 := by
  exact EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 y)

lemma coordinateNorm_smul {m : ℕ} (c : ℝ) (y : Fin m → ℝ) :
    coordinateNorm (c • y) = |c| * coordinateNorm y := by
  simp [coordinateNorm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

def coordinateBall (m : ℕ) (r : ℝ) : Set (Fin m → ℝ) :=
  {y | coordinateNorm y ≤ r}

lemma measurableSet_coordinateBall (m : ℕ) (r : ℝ) :
    MeasurableSet (coordinateBall m r) :=
  measurableSet_le continuous_coordinateNorm.measurable measurable_const

lemma coordinateBall_smul (m : ℕ) (c r : ℝ) (hc : 0 < c) :
    coordinateBall m (c * r) = c • coordinateBall m r := by
  ext y
  constructor
  · intro hy
    refine ⟨c⁻¹ • y, ?_, by simp [hc.ne']⟩
    change coordinateNorm (c⁻¹ • y) ≤ r
    rw [coordinateNorm_smul, abs_of_pos (inv_pos.mpr hc)]
    exact (inv_mul_le_iff₀ hc).mpr hy
  · rintro ⟨y, hy, rfl⟩
    change coordinateNorm (c • y) ≤ c * r
    rw [coordinateNorm_smul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left hy hc.le

lemma volume_coordinateBall_smul (m : ℕ) (c r : ℝ) (hc : 0 < c) :
    volume (coordinateBall m (c * r)) =
      ENNReal.ofReal (c^m) * volume (coordinateBall m r) := by
  rw [coordinateBall_smul m c r hc, Measure.addHaar_smul_of_nonneg volume hc.le]
  simp

lemma gaussianPDF_le_exp (x : ℝ) :
    gaussianPDF 0 1 x ≤ ENNReal.ofReal (Real.exp (-(x^2)/2)) := by
  apply ENNReal.ofReal_le_ofReal
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  apply mul_le_of_le_one_left (Real.exp_nonneg _)
  apply inv_le_one_of_one_le₀
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  nlinarith [Real.pi_gt_three]

lemma lintegral_quarterGaussian_le :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(x^2)/4))) ≤ 4 := by
  have he : (fun x : ℝ => Real.exp (-(x^2)/4)) =
      (fun x : ℝ => Real.exp (-(1/4 : ℝ) * x^2)) := by
    ext x
    congr 1
    ring
  simp_rw [show ∀ x : ℝ, Real.exp (-(x^2)/4) = Real.exp (-(1/4 : ℝ) * x^2) from congrFun he]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_neg_mul_sq (by norm_num)) (by filter_upwards [] with x; positivity),
    integral_gaussian]
  have hs : Real.sqrt (Real.pi / (1/4 : ℝ)) ≤ 4 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · nlinarith [Real.pi_lt_four]
  exact (ENNReal.ofReal_le_ofReal hs).trans_eq (by norm_num)

lemma gaussian_density_pair_bound {m : ℕ} (x y : Fin m → ℝ)
    (h : coordinateNorm y ≤ coordinateNorm x) :
    (∏ j, gaussianPDF 0 1 (x j)) ≤
      (∏ j, ENNReal.ofReal (Real.exp (-(x j)^2/4))) *
      ∏ j, ENNReal.ofReal (Real.exp (-(y j)^2/4)) := by
  calc
    _ ≤ ∏ j, ENNReal.ofReal (Real.exp (-(x j)^2/2)) :=
      Finset.prod_le_prod' fun j _ => gaussianPDF_le_exp (x j)
    _ = ENNReal.ofReal (Real.exp (- (∑ j, (x j)^2) / 2)) := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.exp_nonneg _), ← Real.exp_sum]
      congr 2
      rw [← Finset.sum_div, Finset.sum_neg_distrib]
    _ ≤ ENNReal.ofReal (Real.exp (- (∑ j, (x j)^2)/4 - (∑ j, (y j)^2)/4)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hn : 0 ≤ coordinateNorm y := norm_nonneg _
      have hs := pow_le_pow_left₀ hn h 2
      rw [coordinateNorm_sq, coordinateNorm_sq] at hs
      linarith
    _ = _ := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.exp_nonneg _),
        ← ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.exp_nonneg _),
        ← Real.exp_sum, ← Real.exp_sum, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
        ← Real.exp_add]
      congr 2
      simp only [← Finset.sum_div, Finset.sum_neg_distrib]
      ring

lemma measurable_coordinateVolume (m : ℕ) : Measurable (fun x : Fin m → ℝ => volume (coordinateBall m (coordinateNorm x))) := by
  have : Measurable (fun z : (Fin m → ℝ) × (Fin m → ℝ) =>
      ({z | coordinateNorm z.2 ≤ coordinateNorm z.1} : Set _).indicator
        (fun _ => (1 : ℝ≥0∞)) z) :=
    measurable_const.indicator (measurableSet_le (by fun_prop) (by fun_prop))
  change Measurable (Function.uncurry (fun x y : Fin m → ℝ =>
    (coordinateBall m (coordinateNorm x)).indicator (fun _ => (1 : ℝ≥0∞)) y)) at this
  convert this.lintegral_prod_right (ν := (volume : Measure (Fin m → ℝ))) using 1
  ext x
  rw [lintegral_indicator (measurableSet_coordinateBall m _)]
  simp

lemma gaussian_expected_coordinate_volume (m : ℕ) :
    (∫⁻ x : Fin m → ℝ, volume (coordinateBall m (coordinateNorm x))
      ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤ (16 : ℝ≥0∞)^m := by
  have hB := measurable_coordinateVolume m
  rw [pi_gaussian_withDensity m 1 (by norm_num),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hB]
  have hi (x : Fin m → ℝ) :
      (∏ j, gaussianPDF 0 1 (x j)) * volume (coordinateBall m (coordinateNorm x)) =
      ∫⁻ y : Fin m → ℝ, (coordinateBall m (coordinateNorm x)).indicator
        (fun _ => ∏ j, gaussianPDF 0 1 (x j)) y := by
    rw [lintegral_indicator (measurableSet_coordinateBall m _)]
    simp
  simp only [Pi.mul_apply]
  simp_rw [hi]
  calc
    _ ≤ ∫⁻ x : Fin m → ℝ, ∫⁻ y : Fin m → ℝ,
      (∏ j, ENNReal.ofReal (Real.exp (-(x j)^2/4))) *
        ∏ j, ENNReal.ofReal (Real.exp (-(y j)^2/4)) := by
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ coordinateBall m (coordinateNorm x)
      · rw [Set.indicator_of_mem hy]
        exact gaussian_density_pair_bound x y hy
      · rw [Set.indicator_of_notMem hy]
        exact zero_le
    _ = ((∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-(z^2)/4)))^m)^2 := by
      have hJ : (∫⁻ y : Fin m → ℝ, ∏ j, ENNReal.ofReal (Real.exp (-(y j)^2/4))) =
          (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-(z^2)/4)))^m := by
        rw [volume_pi, lintegral_fin_prod volume m
          (fun _ => fun z : ℝ => ENNReal.ofReal (Real.exp (-(z^2)/4))) (fun _ => by fun_prop)]
        simp
      have hj (x : Fin m → ℝ) := lintegral_const_mul (μ := volume)
        (∏ j, ENNReal.ofReal (Real.exp (-(x j)^2/4)))
        (by fun_prop : Measurable (fun y : Fin m → ℝ =>
          ∏ j, ENNReal.ofReal (Real.exp (-(y j)^2/4))))
      simp_rw [hj, hJ]
      rw [lintegral_mul_const _ (by fun_prop), hJ, pow_two]
    _ ≤ ((4 : ℝ≥0∞)^m)^2 := pow_le_pow_left₀ (by positivity)
      (pow_le_pow_left₀ (by positivity) lintegral_quarterGaussian_le m) 2
    _ = _ := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num

section Rows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma stdGaussian_inner_map (u : E) :
    (stdGaussian E).map (fun x => ⟪u, x⟫) =
      gaussianReal 0 (NNReal.mk (‖u‖^2) (sq_nonneg ‖u‖)) := by
  have h := IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) (innerSL ℝ u)
  have he : (⇑(innerSL ℝ u)) = (fun x => ⟪u, x⟫) := by
    ext x
    exact innerSL_apply_apply ℝ u x
  simp only [integral_strongDual_stdGaussian, variance_dual_stdGaussian, innerSL_apply_norm] at h
  rw [he] at h
  have hh : (‖u‖^2).toNNReal = NNReal.mk (‖u‖^2) (sq_nonneg ‖u‖) := by
    ext
    simp
  simpa only [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
    innerSL_apply_norm, hh] using h

lemma rows_inner_map (u : E) (m : ℕ) :
    (Measure.pi (fun _ : Fin m => stdGaussian E)).map
      (fun A => fun j => ⟪u, A j⟫) =
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map
        (fun x => ‖u‖ • x) := by
  rw [Measure.pi_map_pi (f := fun _ : Fin m => fun x : E => ⟪u, x⟫)
    (fun _ => (by fun_prop : Measurable (fun x : E => ⟪u, x⟫)).aemeasurable)]
  simp_rw [stdGaussian_inner_map]
  exact (pi_gaussian_map_scale m ‖u‖).symm

lemma rows_expected_coordinate_volume (u : E) (hu : ‖u‖ ≤ 1) (m : ℕ) :
    (∫⁻ A : Fin m → E, volume (coordinateBall m (coordinateNorm (fun j => ⟪u, A j⟫)))
      ∂Measure.pi (fun _ => stdGaussian E)) ≤ (16 : ℝ≥0∞)^m := by
  have h := congrArg (fun μ : Measure (Fin m → ℝ) =>
    ∫⁻ y, volume (coordinateBall m (coordinateNorm y)) ∂μ) (rows_inner_map u m)
  rw [lintegral_map (measurable_coordinateVolume m) (by fun_prop),
    lintegral_map (measurable_coordinateVolume m) (by fun_prop)] at h
  rw [h]
  apply le_trans _ (gaussian_expected_coordinate_volume m)
  apply lintegral_mono
  intro x
  apply measure_mono
  intro y hy
  change coordinateNorm y ≤ coordinateNorm x
  apply le_trans hy
  rw [coordinateNorm_smul, abs_of_nonneg (norm_nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg _) hu

def rowOperator {m : ℕ} (A : Fin m → E) : E →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j => innerSL ℝ (A j)))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rowOperator_apply {m : ℕ} (A : Fin m → E) (t : E) :
    rowOperator A t = WithLp.toLp 2 (fun j => ⟪t, A j⟫) := by
  ext j
  exact real_inner_comm _ _

def netProjectionSupport (s : Finset E) (m : ℕ) :
    Set ((Fin m → E) × (Fin m → ℝ)) :=
  ⋃ u ∈ s, {z | coordinateNorm z.2 ≤ 2 * coordinateNorm (fun j => ⟪u, z.1 j⟫)}

lemma measurableSet_netProjectionSupport (s : Finset E) (m : ℕ) :
    MeasurableSet (netProjectionSupport s m) := by
  apply MeasurableSet.biUnion s.countable_toSet
  intro u _
  exact measurableSet_le (by fun_prop) (by fun_prop)

lemma netProjectionSupport_volume (s : Finset E) (hs : ∀ u ∈ s, ‖u‖ ≤ 1) (m : ℕ) :
    matrixLabelReference (E := E) m (netProjectionSupport s m) ≤
      (s.card : ℝ≥0∞) * (32 : ℝ≥0∞)^m := by
  classical
  apply (measure_biUnion_finset_le s _).trans
  calc
    _ ≤ ∑ _u ∈ s, (32 : ℝ≥0∞)^m := by
      apply Finset.sum_le_sum
      intro u hu
      rw [matrixLabelReference, Measure.prod_apply (measurableSet_le (by fun_prop) (by fun_prop))]
      change (∫⁻ A : Fin m → E,
        volume (coordinateBall m (2 * coordinateNorm (fun j => ⟪u, A j⟫)))
        ∂Measure.pi (fun _ => stdGaussian E)) ≤ _
      simp_rw [volume_coordinateBall_smul m 2 _ (by norm_num)]
      have hme : Measurable (fun A : Fin m → E =>
          volume (coordinateBall m (coordinateNorm (fun j => ⟪u, A j⟫)))) :=
        (measurable_coordinateVolume m).comp (by fun_prop)
      rw [lintegral_const_mul _ hme]
      calc
        _ ≤ ENNReal.ofReal ((2 : ℝ)^m) * (16 : ℝ≥0∞)^m :=
          mul_le_mul' le_rfl (rows_expected_coordinate_volume u (hs u hu) m)
        _ = _ := by rw [ENNReal.ofReal_pow (by norm_num)]; norm_num [← mul_pow]
    _ = _ := by simp
end Rows

section NetNorm
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma opNorm_le_twice_net (f : E →L[ℝ] F) (s : Finset E)
    (hnet : ∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ s, dist x y ≤ 1/2) :
    ‖f‖ ≤ 2 * (s.sup (fun u => ‖f u‖₊) : ℝ≥0) := by
  classical
  let K : ℝ := (s.sup (fun u => ‖f u‖₊) : ℝ≥0)
  have hK : 0 ≤ K := NNReal.coe_nonneg _
  have hbound : ‖f‖ ≤ K + ‖f‖/2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hnet x hx.le
    have hfy : ‖f y‖ ≤ K := by
      exact_mod_cast (Finset.le_sup (f := fun u => ‖f u‖₊) hy)
    calc
      ‖f x‖ = ‖f y + f (x-y)‖ := by rw [map_sub]; congr 1; abel
      _ ≤ ‖f y‖ + ‖f (x-y)‖ := norm_add_le _ _
      _ ≤ K + ‖f‖ * (1/2) := add_le_add hfy
        ((f.le_opNorm (x-y)).trans (mul_le_mul_of_nonneg_left
          (by simpa [dist_eq_norm] using hxy) (norm_nonneg _)))
      _ = _ := by ring
  dsimp [K] at hbound
  linarith
end NetNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_projection_support (m : ℕ) (hm : m ≤ Module.finrank ℝ E) :
    ∃ D : Set ((Fin m → E) × (Fin m → ℝ)), MeasurableSet D ∧
      (∀ A t, ‖t‖ ≤ 1 → (A, fun j => ⟪t, A j⟫) ∈ D) ∧
      matrixLabelReference (E := E) m D ≤ (192 : ℝ≥0∞)^(Module.finrank ℝ E) := by
  classical
  obtain ⟨s, hs, hc, hnet⟩ := exists_unit_ball_net (E := E)
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)
  have hsne : s.Nonempty := by
    obtain ⟨u, hu, _⟩ := hnet 0 (by simp)
    exact ⟨u, hu⟩
  refine ⟨netProjectionSupport s m, measurableSet_netProjectionSupport s m, ?_, ?_⟩
  · intro A t ht
    obtain ⟨u, hu, he⟩ := s.exists_mem_eq_sup hsne (fun u => ‖rowOperator A u‖₊)
    refine Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨hu, ?_⟩⟩
    change coordinateNorm (fun j => ⟪t, A j⟫) ≤
      2 * coordinateNorm (fun j => ⟪u, A j⟫)
    change ‖WithLp.toLp 2 (fun j => ⟪t, A j⟫)‖ ≤
      2 * ‖WithLp.toLp 2 (fun j => ⟪u, A j⟫)‖
    rw [← rowOperator_apply, ← rowOperator_apply]
    calc
      _ ≤ ‖rowOperator A‖ * ‖t‖ := (rowOperator A).le_opNorm t
      _ ≤ ‖rowOperator A‖ := mul_le_of_le_one_right (norm_nonneg _) ht
      _ ≤ _ := by simpa [he] using opNorm_le_twice_net (rowOperator A) s hnet
  · apply (netProjectionSupport_volume s hs m).trans
    have hcard : (s.card : ℝ≥0∞) ≤ (6 : ℝ≥0∞)^(Module.finrank ℝ E) := by
      have h : (s.card : ℝ) ≤ (6 : ℝ)^(Module.finrank ℝ E) := by norm_num at hc ⊢; exact hc
      simpa using ENNReal.ofReal_le_ofReal h
    calc
      _ ≤ (6 : ℝ≥0∞)^Module.finrank ℝ E * (32 : ℝ≥0∞)^Module.finrank ℝ E :=
        mul_le_mul' hcard (pow_le_pow_right₀ (by norm_num) hm)
      _ = _ := by rw [← mul_pow]; norm_num

end NoiselessRegression

end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.GaussianRegression_Blocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Localization, finite selection, and block mass propagation.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section Block
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def PolynomialMass (ν : Measure E) (a : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ z : E, ∀ r : ℝ, 0 < r → ν (Metric.closedBall z r) ≤ C * ENNReal.ofReal (r^a)

lemma finite_rpow_holder {J : Type*} [Fintype J] (a : J → ℝ≥0∞) {q : ℝ} (hq : 1 < q) :
    (∑ j, a j ^ (1 - 1/q)) ≤
      (Fintype.card J : ℝ≥0∞)^(1/q) * (∑ j, a j)^(1-1/q) := by
  have hh := Real.HolderConjugate.conjExponent hq
  have hq' : q.conjExponent ≠ 0 := ne_of_gt hh.symm.pos
  have hex : 1 - 1/q = q.conjExponent⁻¹ := by simpa only [one_div] using hh.one_sub_inv
  rw [hex]
  simpa only [one_mul, one_div, ENNReal.one_rpow, ENNReal.rpow_inv_rpow hq',
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
    ENNReal.inner_le_Lp_mul_Lq Finset.univ (fun _ : J => (1 : ℝ≥0∞))
      (fun j => a j ^ q.conjExponent⁻¹) hh

lemma projectionLaw_smul (ν : Measure E) [SFinite ν] (m : ℕ) (c : ℝ≥0∞) :
    projectionLaw (c • ν) m = c • projectionLaw ν m := by
  rw [projectionLaw, Measure.prod_smul_right, Measure.map_smul]
  rfl

lemma projectionLaw_affine (ν : Measure E) [SFinite ν] (m : ℕ) (z : E) (r : ℝ) :
    projectionLaw (ν.map (fun t => z + r • t)) m =
      (projectionLaw ν m).map (fun x => (x.1, fun j => ⟪z,x.1 j⟫ + r * x.2 j)) := by
  unfold projectionLaw
  rw [← Measure.map_id (μ := Measure.pi (fun _ : Fin m => stdGaussian E)),
    Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_id, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  ext x <;> simp [inner_add_left, real_inner_smul_left]

end Block

end NoiselessRegression

end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.GaussianRegression_Sphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Normalized spherical surface measure, cap bounds, and rotational symmetry.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section SphereBounds
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def unitBallLaw : Measure E :=
  ((volume : Measure E) (Metric.ball 0 1))⁻¹ • volume.restrict (Metric.closedBall 0 1)

instance unitBallLaw_probability : IsProbabilityMeasure (unitBallLaw : Measure E) := by
  constructor
  rw [unitBallLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
    Measure.addHaar_closedBall _ _ (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [one_pow, ENNReal.ofReal_one, one_mul]
  exact ENNReal.inv_mul_cancel (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
    measure_ball_lt_top.ne

instance sphereLaw_probability [Nontrivial E] : IsProbabilityMeasure (sphereLaw (E := E)) := by
  constructor
  rw [sphereLaw, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.inv_mul_cancel _ (measure_ne_top _ _)
  rw [Measure.toSphere_apply_univ]
  exact mul_ne_zero (by exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E)).ne')
    (Metric.measure_ball_pos volume 0 zero_lt_one).ne'

end SphereBounds

open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

instance ambientSphereLaw_probability [Nontrivial E] : IsProbabilityMeasure (ambientSphereLaw (E := E)) :=
  inferInstanceAs (IsProbabilityMeasure ((sphereLaw (E := E)).map Subtype.val))

def sphereIsometry (e : E ≃ₗᵢ[ℝ] E) : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1 :=
  e.toHomeomorph.subtype (fun x => by
    simp only [mem_sphere_zero_iff_norm]
    change ‖x‖ = 1 ↔ ‖e x‖ = 1
    rw [e.norm_map])

end NoiselessRegression

end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.GaussianRegression_Caps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Spherical cap mass bounds along sequential routes.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section StreamCaps
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]

def capWeight (y : E) (ε : ℝ) : E → ℝ≥0∞ :=
  (Metric.closedBall y ε).indicator (fun _ => 1)

end StreamCaps

end NoiselessRegression

end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.GaussianRegression_Rotational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Fubini bounds and rotational lower bounds for sequential estimation.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

instance sampleLaw_probability (d T : ℕ) : IsProbabilityMeasure (sampleLaw d T) := by
  unfold sampleLaw
  infer_instance

end NoiselessRegression

end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_AmbientGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v



open MeasureTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision

lemma sharp_inverse_unit {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {m a C : ℝ} (hm : 0 < m) (ha : m < a) (hC : 0 ≤ C)
    (htube : ∀ t : ℝ, 0 < t → t ≤ 1 →
      μ {x | f x ≤ t} ≤ ENNReal.ofReal (C * t^a)) :
    (∫⁻ x, ENNReal.ofReal (f x ^ (-m)) ∂μ) ≤
      μ univ + ENNReal.ofReal (C * m / (a-m)) := by
  have htail (t : ℝ) (ht : 1 < t) :
      μ {x | t < f x ^ (-m)} ≤ ENNReal.ofReal (C * t ^ (-a/m)) := by
    have ht0 : 0 < t := by linarith
    have hr0 : 0 < t ^ ((-m)⁻¹) := Real.rpow_pos_of_pos ht0 _
    have hr1 : t ^ ((-m)⁻¹) ≤ 1 := by
      calc
        _ ≤ t ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht.le (inv_nonpos.mpr (by linarith))
        _ = 1 := Real.rpow_zero _
    have hsub : {x | t < f x ^ (-m)} ⊆ {x | f x ≤ t ^ ((-m)⁻¹)} := by
      intro x hx
      have hfx : 0 < f x := by
        by_contra h
        have heq : f x = 0 := le_antisymm (le_of_not_gt h) (hf0 x)
        simp only [mem_ofPred_eq, heq, Real.zero_rpow (neg_ne_zero.mpr hm.ne')] at hx
        linarith
      exact ((Real.lt_rpow_inv_iff_of_neg hfx ht0 (by linarith)).2 hx).le
    calc
      _ ≤ μ {x | f x ≤ t ^ ((-m)⁻¹)} := measure_mono hsub
      _ ≤ ENNReal.ofReal (C * (t ^ ((-m)⁻¹)) ^ a) := htube _ hr0 hr1
      _ = _ := by
        rw [← Real.rpow_mul ht0.le]
        congr 2
        ring_nf
  have hb : -a/m < -1 := by
    rw [div_lt_iff₀ hm]
    linarith
  have hint : IntegrableOn (fun t : ℝ => C * t ^ (-a/m)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt hb (by norm_num)).const_mul C
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (1:ℝ))] (fun t : ℝ => C * t ^ (-a/m)) := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
    exact mul_nonneg hC (Real.rpow_nonneg (by have ht' : (1:ℝ) < t := ht; linarith : 0 ≤ t) _)
  have htailint : (∫⁻ t in Ioi (1:ℝ), ENNReal.ofReal (C * t ^ (-a/m))) =
      ENNReal.ofReal (C * m / (a-m)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul,
      integral_Ioi_rpow_of_lt hb (by norm_num), Real.one_rpow]
    congr 1
    field_simp [hm.ne', show a - m ≠ 0 by linarith, show -a + m ≠ 0 by linarith]
    ring
  have hsplit : Ioi (0:ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext t
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro ht
      by_cases h : t ≤ 1
      · exact Or.inl ⟨ht,h⟩
      · exact Or.inr (lt_of_not_ge h)
    · rintro (⟨ht,_⟩ | ht) <;> linarith
  rw [lintegral_eq_lintegral_meas_lt μ
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hf0 x) _) (hf.pow_const _).aemeasurable,
    hsplit]
  apply (lintegral_union_le _ _ _).trans
  apply add_le_add
  · calc
      _ ≤ ∫⁻ _t in Ioc (0:ℝ) 1, μ univ := lintegral_mono fun t => measure_mono (subset_univ _)
      _ = μ univ := by simp [Real.volume_Ioc]
  · calc
      _ ≤ ∫⁻ t in Ioi (1:ℝ), ENNReal.ofReal (C * t ^ (-a/m)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
        exact htail t ht
      _ = _ := htailint

lemma ae_pos_of_power_tube {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) {a C : ℝ} (ha : 0 < a)
    (htube : ∀ t : ℝ, 0 < t → t ≤ 1 →
      μ {x | f x ≤ t} ≤ ENNReal.ofReal (C * t^a)) : ∀ᵐ x ∂μ, 0 < f x := by
  have hb (n : ℕ) : μ {x | f x ≤ 0} ≤ ENNReal.ofReal (C * ((1/2 : ℝ)^n)^a) := by
    calc
      μ {x | f x ≤ 0} ≤ μ {x | f x ≤ (1/2 : ℝ)^n} :=
        measure_mono fun x hx => (show f x ≤ 0 from hx).trans (by positivity)
      _ ≤ _ := htube _ (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (C * ((1/2 : ℝ)^n)^a)) atTop (𝓝 (0:ℝ≥0∞)) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).rpow_const_nhds_zero ha
    simpa using ENNReal.tendsto_ofReal (tendsto_const_nhds.mul h)
  have hz := le_antisymm (ge_of_tendsto' hlim hb) (bot_le : (0:ℝ≥0∞) ≤ μ {x | f x ≤ 0})
  simpa only [ae_iff, not_lt] using hz

lemma sharp_inverse_scaled {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {m a B C R : ℝ} (hm : 0 < m) (ha : m < a)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hR : 0 < R)
    (hmass : μ univ ≤ ENNReal.ofReal B)
    (htube : ∀ t : ℝ, 0 < t → t ≤ 1 →
      μ {x | f x ≤ R*t} ≤ ENNReal.ofReal (C * t^a)) :
    (∀ᵐ x ∂μ, 0 < f x) ∧
    (∫⁻ x, (ENNReal.ofReal (f x)) ^ (-m) ∂μ) ≤
      ENNReal.ofReal ((B + C*m/(a-m)) * R^(-m)) := by
  have hg0 (x : X) : 0 ≤ f x / R := div_nonneg (hf0 x) hR.le
  have hg : Measurable (fun x => f x / R) := hf.div_const R
  have hgtube (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
      μ {x | f x / R ≤ t} ≤ ENNReal.ofReal (C*t^a) := by
    have heq : {x | f x / R ≤ t} = {x | f x ≤ R*t} := by
      ext x
      simp only [mem_ofPred_eq, div_le_iff₀ hR, mul_comm]
    rw [heq]
    exact htube t ht ht1
  have hgp := ae_pos_of_power_tube μ (fun x => f x / R) (hm.trans ha) hgtube
  have hfp : ∀ᵐ x ∂μ, 0 < f x := by
    filter_upwards [hgp] with x hx
    exact (div_pos_iff_of_pos_right hR).mp hx
  refine ⟨hfp, ?_⟩
  have hi := sharp_inverse_unit μ (fun x => f x/R) hg hg0 hm ha hC hgtube
  have hcpos : 0 < R^(-m) := Real.rpow_pos_of_pos hR _
  calc
    _ = ∫⁻ x, ENNReal.ofReal (R^(-m)) * ENNReal.ofReal ((f x/R)^(-m)) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hfp] with x hx
      rw [ENNReal.ofReal_rpow_of_pos hx, ← ENNReal.ofReal_mul hcpos.le,
        Real.div_rpow hx.le hR.le]
      congr 1
      exact (mul_div_cancel₀ _ hcpos.ne').symm
    _ = ENNReal.ofReal (R^(-m)) * (∫⁻ x, ENNReal.ofReal ((f x/R)^(-m)) ∂μ) :=
      lintegral_const_mul _ (hg.pow_const _).ennreal_ofReal
    _ ≤ ENNReal.ofReal (R^(-m)) *
        (ENNReal.ofReal B + ENNReal.ofReal (C*m/(a-m))) :=
      mul_le_mul' le_rfl (hi.trans (add_le_add hmass le_rfl))
    _ = _ := by
      rw [← ENNReal.ofReal_add hB (by positivity), ← ENNReal.ofReal_mul hcpos.le]
      congr 1
      ring

section Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma affine_tube_cover_radius (L : AffineSubspace ℝ E) [Nonempty L]
    (z : E) {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (htR : t ≤ R) :
    ∃ s : Finset L.direction,
      (s.card : ℝ) ≤ (3*R/t)^Module.finrank ℝ L.direction ∧
      ∀ x : E, dist x z ≤ R → Metric.infDist x L ≤ t →
        ∃ y ∈ s, dist x (R • (y:E) + (orthogonalProjection L z : E)) ≤ 2*t := by
  classical
  have hr : 0 < t/R := div_pos ht hR
  have hr1 : t/R ≤ 1 := (div_le_one hR).2 htR
  obtain ⟨s, _, hcard, hnet⟩ := NoiselessRegression.exists_unit_ball_net
    (E := L.direction) hr hr1
  refine ⟨s, ?_, ?_⟩
  · convert hcard using 1
    congr 1
    field_simp
  · intro x hx hdist
    let v : L.direction := L.direction.orthogonalProjectionOnto (x-z)
    have hv : ‖v‖ ≤ R := by
      apply (L.direction.norm_orthogonalProjectionOnto_apply_le (x-z)).trans
      simpa only [dist_eq_norm] using hx
    have hvnorm : ‖R⁻¹ • v‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
      calc
        _ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hR.le)
        _ = 1 := inv_mul_cancel₀ hR.ne'
    obtain ⟨y, hy, hclose⟩ := hnet (R⁻¹ • v) hvnorm
    refine ⟨y, hy, ?_⟩
    have hscaled : dist (v:E) (R • (y:E)) ≤ t := by
      have heq : (v:E) = R • (R⁻¹ • (v:E)) := by simp [smul_smul, hR.ne']
      rw [heq, dist_smul₀, Real.norm_eq_abs, abs_of_pos hR]
      calc
        _ ≤ R * (t/R) := mul_le_mul_of_nonneg_left hclose hR.le
        _ = t := mul_div_cancel₀ _ hR.ne'
    have hproj : (orthogonalProjection L x : E) =
        (v:E) + (orthogonalProjection L z : E) := by
      have h := (orthogonalProjection L).map_vadd z (x-z)
      simpa only [vadd_eq_add, sub_add_cancel, orthogonalProjection_contLinear,
        AffineSubspace.coe_vadd] using congrArg (fun q : L => (q:E)) h
    have hpd : dist (orthogonalProjection L x : E)
        (R • (y:E) + (orthogonalProjection L z : E)) ≤ t := by
      rw [hproj, dist_add_right]
      exact hscaled
    have hxp : dist x (orthogonalProjection L x : E) ≤ t := by
      rwa [dist_orthogonalProjection_eq_infDist]
    calc
      _ ≤ dist x (orthogonalProjection L x : E) +
          dist (orthogonalProjection L x : E) (R • (y:E) + (orthogonalProjection L z : E)) :=
        dist_triangle _ _ _
      _ ≤ t+t := add_le_add hxp hpd
      _ = 2*t := by ring

end Geometry

section AmbientMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma ambient_tube_radius_factors (j : ℕ) (β : ℝ) {R t : ℝ} (ht : 0 < t) :
    (3*R/t)^j * (2*t)^β = (3:ℝ)^j * (2:ℝ)^β * R^j * t^(β-(j:ℝ)) := by
  rw [div_pow, mul_pow, Real.mul_rpow (by norm_num) ht.le,
    Real.rpow_sub_natCast ht.ne']
  ring

lemma ambient_tube {μ : Measure E} {H β R : ℝ} {z : E}
    (hR : 0 < R) (hsupport : μ.support ⊆ Metric.closedBall z R)
    (hball : ∀ x : E, ∀ r : ℝ, 0 < r →
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal (H*r^β))
    (L : AffineSubspace ℝ E) [Nonempty L] {t : ℝ} (ht : 0 < t) (htR : t ≤ R) :
    μ {x | Metric.infDist x L ≤ t} ≤ ENNReal.ofReal
      ((3:ℝ)^Module.finrank ℝ L.direction * (2:ℝ)^β * H *
        R^Module.finrank ℝ L.direction * t^(β-(Module.finrank ℝ L.direction:ℝ))) := by
  classical
  obtain ⟨s, hcard, hcover⟩ := affine_tube_cover_radius L z hR ht htR
  let c : L.direction → E := fun y => R • (y:E) + (orthogonalProjection L z : E)
  have hsub : {x | Metric.infDist x L ≤ t} ≤ᵐ[μ]
      ⋃ y ∈ s, Metric.closedBall (c y) (2*t) := by
    filter_upwards [μ.support_mem_ae] with x hx
    intro hxL
    have hxR : dist x z ≤ R := hsupport hx
    obtain ⟨y, hy, hxy⟩ := hcover x hxR hxL
    exact mem_iUnion₂.mpr ⟨y, hy, hxy⟩
  calc
    _ ≤ μ (⋃ y ∈ s, Metric.closedBall (c y) (2*t)) := measure_mono_ae hsub
    _ ≤ ∑ y ∈ s, μ (Metric.closedBall (c y) (2*t)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ s, ENNReal.ofReal (H*(2*t)^β) :=
      Finset.sum_le_sum fun y _ => hball (c y) _ (by positivity)
    _ = (s.card : ℝ≥0∞) * ENNReal.ofReal (H*(2*t)^β) := by simp
    _ ≤ ENNReal.ofReal ((3*R/t)^Module.finrank ℝ L.direction) *
        ENNReal.ofReal (H*(2*t)^β) := by
      gcongr
      exact_mod_cast ENNReal.ofReal_le_ofReal hcard
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      calc
        _ = H * ((3*R/t)^Module.finrank ℝ L.direction * (2*t)^β) := by ring
        _ = _ := by rw [ambient_tube_radius_factors _ _ ht]; ring

omit [BorelSpace E] in
lemma ambient_mass_bound {μ : Measure E} {H β R : ℝ} {z : E}
    (hR : 0 < R) (hsupport : μ.support ⊆ Metric.closedBall z R)
    (hball : ∀ x : E, ∀ r : ℝ, 0 < r →
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal (H*r^β)) :
    μ univ ≤ ENNReal.ofReal (H * R^β) := by
  calc
    _ ≤ μ (Metric.closedBall z R) := by
      apply measure_mono_ae
      filter_upwards [μ.support_mem_ae] with x hx
      intro _
      exact hsupport hx
    _ ≤ _ := hball z R hR

lemma ambient_tube_scaled {μ : Measure E} {H β R : ℝ} {z : E}
    (hR : 0 < R) (hsupport : μ.support ⊆ Metric.closedBall z R)
    (hball : ∀ x : E, ∀ r : ℝ, 0 < r →
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal (H*r^β))
    (L : AffineSubspace ℝ E) [Nonempty L] {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    μ {x | Metric.infDist x L ≤ R*t} ≤ ENNReal.ofReal
      (((3:ℝ)^Module.finrank ℝ L.direction * (2:ℝ)^β * H * R^β) *
        t^(β-(Module.finrank ℝ L.direction:ℝ))) := by
  refine (ambient_tube hR hsupport hball L (mul_pos hR ht)
    (by nlinarith)).trans_eq ?_
  congr 1
  rw [Real.mul_rpow hR.le ht.le]
  have heq : R^Module.finrank ℝ L.direction * R^(β-(Module.finrank ℝ L.direction:ℝ)) = R^β := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hR]
    congr 1
    ring
  calc
    _ = ((3:ℝ)^Module.finrank ℝ L.direction * (2:ℝ)^β * H) *
      (R^Module.finrank ℝ L.direction * R^(β-(Module.finrank ℝ L.direction:ℝ))) *
      t^(β-(Module.finrank ℝ L.direction:ℝ)) := by ring
    _ = _ := by rw [heq]

lemma ambient_inverse_moment {μ : Measure E} {H β R : ℝ} {z : E}
    (hH : 0 < H) (hR : 0 < R) (hsupport : μ.support ⊆ Metric.closedBall z R)
    (hball : ∀ x : E, ∀ r : ℝ, 0 < r →
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal (H*r^β))
    (L : AffineSubspace ℝ E) [Nonempty L] {m : ℕ} (hm : 0 < m)
    (hgap : (Module.finrank ℝ L.direction:ℝ) + (m:ℝ) < β) :
    (∀ᵐ x ∂μ, 0 < Metric.infDist x L) ∧
    (∫⁻ x, (ENNReal.ofReal (Metric.infDist x L)) ^ (-(m:ℝ)) ∂μ) ≤
      ENNReal.ofReal (J β m (Module.finrank ℝ L.direction) * H * R^(β-(m:ℝ))) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hi := sharp_inverse_scaled μ (fun x => Metric.infDist x L)
    (Metric.continuous_infDist_pt _).measurable (fun _ => Metric.infDist_nonneg)
    hm' (show (m:ℝ) < β-(Module.finrank ℝ L.direction:ℝ) by linarith)
    (show 0 ≤ H*R^β by positivity)
    (show 0 ≤ (3:ℝ)^Module.finrank ℝ L.direction * (2:ℝ)^β * H * R^β by positivity)
    hR (ambient_mass_bound hR hsupport hball)
    (fun t ht ht1 => ambient_tube_scaled hR hsupport hball L ht ht1)
  refine ⟨hi.1, hi.2.trans_eq ?_⟩
  congr 1
  have heq : H*R^β + ((3:ℝ)^Module.finrank ℝ L.direction * (2:ℝ)^β * H * R^β) *
      (m:ℝ)/(β-(Module.finrank ℝ L.direction:ℝ)-(m:ℝ)) =
      J β m (Module.finrank ℝ L.direction) * H * R^β := by
    unfold J
    ring
  rw [heq, mul_assoc, ← Real.rpow_add hR]
  congr 2

end AmbientMoments

lemma J_pos {β : ℝ} {m j : ℕ} (hgap : (j:ℝ)+(m:ℝ)<β) : 0 < J β m j := by
  unfold J
  have hd : 0 < β-(j:ℝ)-(m:ℝ) := by linarith
  positivity

lemma J_mono {β : ℝ} {m j k : ℕ} (hjk : j ≤ k)
    (hgap : (k:ℝ)+(m:ℝ)<β) : J β m j ≤ J β m k := by
  have hjk' : (j:ℝ) ≤ k := by exact_mod_cast hjk
  unfold J
  apply add_le_add le_rfl
  apply div_le_div₀
  · positivity
  · gcongr
    norm_num
  · linarith
  · linarith

section ReplicaExact
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
open NoiselessRegression InnerProductSpace

lemma ambient_inverse_moment_le {μ : Measure E} {H β R : ℝ} {z : E}
    (hH : 0 < H) (hR : 0 < R) (hsupport : μ.support ⊆ Metric.closedBall z R)
    (hball : ∀ x : E, ∀ r : ℝ, 0 < r →
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal (H*r^β))
    (L : AffineSubspace ℝ E) [Nonempty L] {m k : ℕ} (hm : 0 < m)
    (hdim : Module.finrank ℝ L.direction ≤ k) (hgap : (k:ℝ)+(m:ℝ)<β) :
    (∫⁻ x, ENNReal.ofReal ((Metric.infDist x L)⁻¹ ^ m) ∂μ) ≤
      ENNReal.ofReal (J β m k * H * R^(β-(m:ℝ))) := by
  have hdim' : (Module.finrank ℝ L.direction:ℝ) ≤ k := by exact_mod_cast hdim
  obtain ⟨ha, hi⟩ := ambient_inverse_moment hH hR hsupport hball L hm (by linarith)
  calc
    _ = ∫⁻ x, (ENNReal.ofReal (Metric.infDist x L)) ^ (-(m:ℝ)) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ha] with x hx
      rw [ENNReal.ofReal_rpow_of_pos hx, Real.rpow_neg hx.le, Real.rpow_natCast, inv_pow]
    _ ≤ ENNReal.ofReal (J β m (Module.finrank ℝ L.direction) * H * R^(β-(m:ℝ))) := hi
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      gcongr
      exact J_mono hdim hgap

lemma replica_integral_exact {μ : Measure E} [IsFiniteMeasure μ] {H β R : ℝ} {z : E}
    (hH : 0 < H) (hR : 0 < R) (hsupport : μ.support ⊆ Metric.closedBall z R)
    (hball : ∀ x : E, ∀ r : ℝ, 0 < r →
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal (H*r^β))
    {m : ℕ} (hm : 0 < m) (p : E) (n : ℕ)
    (hgap : (n:ℝ)+(m:ℝ)-1<β) :
    (∫⁻ v : Fin n → E, replicaWeight m p v ∂Measure.pi (fun _ => μ)) ≤
      ∏ j : Fin n, ENNReal.ofReal (J β m j * H * R^(β-(m:ℝ))) := by
  induction n with
  | zero => simp [replicaWeight]
  | succ n ih =>
    have hngap : (n:ℝ)+(m:ℝ)<β := by push_cast at hgap; linarith
    have hinner (v : Fin n → E) :
        (∫⁻ x, replicaWeight m p (Fin.snoc v x) ∂μ) ≤
          replicaWeight m p v * ENNReal.ofReal (J β m n * H * R^(β-(m:ℝ))) := by
      simp_rw [replicaWeight_snoc]
      rw [lintegral_const_mul _ (by fun_prop)]
      apply mul_le_mul' le_rfl
      apply ambient_inverse_moment_le hH hR hsupport hball _ hm _ hngap
      rw [AffineSubspace.direction_mk']
      simpa only [Fintype.card_fin, Set.finrank] using
        finrank_range_le_card (R := ℝ) (fun i : Fin n => v i - p)
    calc
      _ = ∫⁻ v : Fin n → E, ∫⁻ x, replicaWeight m p (Fin.snoc v x) ∂μ
          ∂Measure.pi (fun _ => μ) := lintegral_pi_snoc μ _ (measurable_replicaWeight m p (n+1))
      _ ≤ ∫⁻ v : Fin n → E, replicaWeight m p v *
          ENNReal.ofReal (J β m n * H * R^(β-(m:ℝ))) ∂Measure.pi (fun _ => μ) :=
        lintegral_mono hinner
      _ = (∫⁻ v : Fin n → E, replicaWeight m p v ∂Measure.pi (fun _ => μ)) *
          ENNReal.ofReal (J β m n * H * R^(β-(m:ℝ))) :=
        lintegral_mul_const _ (measurable_replicaWeight m p n)
      _ ≤ (∏ j : Fin n, ENNReal.ofReal (J β m j * H * R^(β-(m:ℝ)))) *
          ENNReal.ofReal (J β m n * H * R^(β-(m:ℝ))) :=
        mul_le_mul' (ih (by linarith)) le_rfl
      _ = _ := by rw [Fin.prod_univ_castSucc]; rfl

lemma ae_replica_nondegenerate_exact {μ : Measure E} [IsFiniteMeasure μ] {H β R : ℝ} {z : E}
    (hH : 0 < H) (hR : 0 < R) (hsupport : μ.support ⊆ Metric.closedBall z R)
    (hball : ∀ x : E, ∀ r : ℝ, 0 < r →
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal (H*r^β))
    {m : ℕ} (hm : 0 < m) (p : E) (n : ℕ)
    (hgap : (n:ℝ)+(m:ℝ)-1<β) :
    ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => μ),
      ∀ i, gramSchmidt ℝ (fun j => v j-p) i ≠ 0 := by
  induction n with
  | zero => exact Filter.Eventually.of_forall fun _ i => Fin.elim0 i
  | succ n ih =>
    rw [ae_pi_snoc μ (measurableSet_gramSchmidt_ne_zero p (n+1))]
    have hngap : (n:ℝ)+(m:ℝ)<β := by push_cast at hgap; linarith
    filter_upwards [ih (by linarith)] with v hv
    let L := AffineSubspace.mk' p (Submodule.span ℝ (Set.range (fun i : Fin n => v i-p)))
    have hdim : (Module.finrank ℝ L.direction:ℝ) ≤ n := by
      dsimp [L]
      rw [AffineSubspace.direction_mk']
      have hh := finrank_range_le_card (R := ℝ) (fun i : Fin n => v i-p)
      simp only [Fintype.card_fin, Set.finrank] at hh
      exact_mod_cast hh
    have ha := (ambient_inverse_moment hH hR hsupport hball L hm (by linarith)).1
    filter_upwards [ha] with x hx
    intro i
    induction i using Fin.lastCases with
    | last =>
      apply norm_ne_zero_iff.mp
      rw [norm_gramSchmidt_sub_eq_affine_infDist, image_Iio_last]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact hx.ne'
    | cast j => simpa only [gramSchmidt_castSucc, Fin.snoc_castSucc] using hv j

lemma measurable_joint_replicaWeight (m n : ℕ) :
    Measurable (fun v : E × (Fin n → E) => replicaWeight m v.1 v.2) := by
  have hs : Measurable (fun v : E × (Fin n → E) => fun j => v.2 j-v.1) := by fun_prop
  exact Finset.measurable_prod _ fun i _ =>
    (((measurable_gramSchmidt i).comp hs).norm.inv.pow_const m).ennreal_ofReal

lemma ae_joint_replica_independent {μ : Measure E} [IsFiniteMeasure μ] {H β R : ℝ} {z : E}
    (hH : 0 < H) (hR : 0 < R) (hsupport : μ.support ⊆ Metric.closedBall z R)
    (hball : ∀ x : E, ∀ r : ℝ, 0 < r →
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal (H*r^β))
    {m : ℕ} (hm : 0 < m) (n : ℕ)
    (hgap : (n:ℝ)+(m:ℝ)-1<β) :
    ∀ᵐ v : E × (Fin n → E) ∂μ.prod (Measure.pi (fun _ => μ)),
      LinearIndependent ℝ (fun j => v.2 j-v.1) := by
  have hmeas : MeasurableSet {v : E × (Fin n → E) |
      ∀ i, gramSchmidt ℝ (fun j => v.2 j-v.1) i ≠ 0} := by
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    have h := (measurable_gramSchmidt i).comp
      (show Measurable (fun v : E × (Fin n → E) => fun j => v.2 j-v.1) by fun_prop)
    exact (measurableSet_eq_fun h measurable_const).compl
  have ha : ∀ᵐ v : E × (Fin n → E) ∂μ.prod (Measure.pi (fun _ => μ)),
      ∀ i, gramSchmidt ℝ (fun j => v.2 j-v.1) i ≠ 0 := by
    rw [Measure.ae_prod_iff_ae_ae hmeas]
    exact Filter.Eventually.of_forall fun p =>
      ae_replica_nondegenerate_exact hH hR hsupport hball hm p n hgap
  filter_upwards [ha] with v hv
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  rw [det_gram_eq_prod_gramSchmidt]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (hv i))

lemma joint_replica_integral_exact {μ : Measure E} [IsFiniteMeasure μ] {H β R : ℝ} {z : E}
    (hH : 0 < H) (hR : 0 < R) (hsupport : μ.support ⊆ Metric.closedBall z R)
    (hball : ∀ x : E, ∀ r : ℝ, 0 < r →
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal (H*r^β))
    {m : ℕ} (hm : 0 < m) (n : ℕ)
    (hgap : (n:ℝ)+(m:ℝ)-1<β) :
    (∫⁻ v : E × (Fin n → E), replicaWeight m v.1 v.2
      ∂μ.prod (Measure.pi (fun _ => μ))) ≤
      ENNReal.ofReal (H^(n+1) * R^(β*(n+1:ℕ)-(m:ℝ)*(n:ℝ)) *
        ∏ j : Fin n, J β m j) := by
  have hJ (j : Fin n) : 0 < J β m j := by
    apply J_pos
    have hj : (j:ℝ)+1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt j.isLt
    linarith
  have hfac (j : Fin n) : 0 ≤ J β m j * H * R^(β-(m:ℝ)) := by
    exact le_of_lt (mul_pos (mul_pos (hJ j) hH) (Real.rpow_pos_of_pos hR _))
  calc
    _ = ∫⁻ p, ∫⁻ v : Fin n → E, replicaWeight m p v
        ∂Measure.pi (fun _ => μ) ∂μ :=
      lintegral_prod _ (measurable_joint_replicaWeight m n).aemeasurable
    _ ≤ ∫⁻ _p, ∏ j : Fin n, ENNReal.ofReal (J β m j * H * R^(β-(m:ℝ))) ∂μ :=
      lintegral_mono fun p => replica_integral_exact hH hR hsupport hball hm p n hgap
    _ = (∏ j : Fin n, ENNReal.ofReal (J β m j * H * R^(β-(m:ℝ)))) * μ univ :=
      lintegral_const _
    _ ≤ (∏ j : Fin n, ENNReal.ofReal (J β m j * H * R^(β-(m:ℝ)))) *
        ENNReal.ofReal (H*R^β) := mul_le_mul' le_rfl (ambient_mass_bound hR hsupport hball)
    _ = _ := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => hfac j),
        ← ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ => hfac j)]
      congr 1
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← Real.rpow_mul_natCast hR.le]
      have heq : R^((β-(m:ℝ))*(n:ℝ)) * R^β =
          R^(β*(n+1:ℕ)-(m:ℝ)*(n:ℝ)) := by
        rw [← Real.rpow_add hR]
        congr 1
        push_cast
        ring
      calc
        _ = (H^n*H) * (R^((β-(m:ℝ))*(n:ℝ)) * R^β) * ∏ j : Fin n, J β m j := by ring
        _ = _ := by rw [← pow_succ, heq]

end ReplicaExact

lemma specialized_J_bound (d m p : ℕ) (hd : 16 ≤ d) (hp : p=d/8)
    (_ : 1 ≤ m) (hmp : m ≤ p) (β : ℝ)
    (hβlo : ((d:ℝ)-1)/2 ≤ β) (hβhi : β ≤ (d:ℝ)/2) :
    ∀ j : ℕ, j ≤ p-2 →
      ((d:ℝ)-1)/2 - 2*(p:ℝ) + 2 ≤ β-(j:ℝ)-(m:ℝ) ∧
      (d:ℝ)/4 + 3/2 ≤ ((d:ℝ)-1)/2 - 2*(p:ℝ) + 2 ∧
      J β m j ≤ (7:ℝ)^d := by
  have hp2 : 2 ≤ p := by omega
  have hp8 : p*8 ≤ d := by rw [hp]; exact Nat.div_mul_le_self d 8
  have hp8' : (p:ℝ)*8 ≤ d := by exact_mod_cast hp8
  have hd' : (16:ℝ) ≤ d := by exact_mod_cast hd
  have hm' : (m:ℝ) ≤ p := by exact_mod_cast hmp
  intro j hj
  have hj' : (j:ℝ)+2 ≤ p := by exact_mod_cast (show j+2 ≤ p by omega)
  have hmargin : ((d:ℝ)-1)/2-2*(p:ℝ)+2 ≤ β-(j:ℝ)-(m:ℝ) := by linarith
  have hdim : (d:ℝ)/4+3/2 ≤ ((d:ℝ)-1)/2-2*(p:ℝ)+2 := by linarith
  refine ⟨hmargin, hdim, ?_⟩
  have hgap : 0 < β-(j:ℝ)-(m:ℝ) := by linarith
  have hquot : (m:ℝ)/(β-(j:ℝ)-(m:ℝ)) ≤ 1 := by
    rw [div_le_one hgap]
    linarith
  have h3 : (3:ℝ)^j ≤ (3:ℝ)^d := by
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have h2 : (2:ℝ)^β ≤ (2:ℝ)^d := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  calc
    J β m j = 1 + (3:ℝ)^j * (2:ℝ)^β * ((m:ℝ)/(β-(j:ℝ)-(m:ℝ))) := by unfold J; ring
    _ ≤ 1 + (3:ℝ)^j * (2:ℝ)^β * 1 := by gcongr
    _ ≤ 1 + (3:ℝ)^d * (2:ℝ)^d := by rw [mul_one]; gcongr
    _ = 1 + (6:ℝ)^d := by rw [← mul_pow]; norm_num
    _ ≤ (7:ℝ)^d := by
      simpa only [one_pow, show (1:ℝ)+6=7 by norm_num] using pow_add_pow_le (show (0:ℝ) ≤ 1 by norm_num)
        (show (0:ℝ) ≤ 6 by norm_num) (show d ≠ 0 by omega)

end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_CubeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

lemma cubeSet_closed (n : ℕ) : IsClosed (CubeSet n) := by
  change IsClosed {u : Space n | ∀ i, |u i| ≤ 1/2}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun i => isClosed_le (by fun_prop) continuous_const)

lemma cubeSet_measurable (n : ℕ) : MeasurableSet (CubeSet n) :=
  (cubeSet_closed n).measurableSet

lemma cubeLaw_probability (d : ℕ) : IsProbabilityMeasure (CubeLaw d) := by
  constructor
  rw [CubeLaw, comap_subtype_coe_apply (cubeSet_measurable _), Set.image_univ,
    Subtype.range_coe]
  have he : CubeSet (d/2) = WithLp.ofLp ⁻¹' (Set.univ.pi (fun _ : Fin (d/2) => Icc (-1/2:ℝ) (1/2))) := by
    ext u
    change (∀ i, |u i| ≤ (1/2 : ℝ)) ↔ _
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_Icc, abs_le]
    norm_num
  rw [he, (PiLp.volume_preserving_ofLp (Fin (d/2))).measure_preimage (by measurability)]
  rw [volume_pi, Measure.pi_pi]
  norm_num [Real.volume_Icc]

instance instIsProbabilityMeasureElemEuclideanSpaceRealFinHDivNatOfNatCubeCubeLaw (d : ℕ) : IsProbabilityMeasure (CubeLaw d) := cubeLaw_probability d

lemma cubeRaw_continuous (d : ℕ) : Continuous (cubeRaw d) := by
  unfold cubeRaw
  refine Continuous.const_smul (c := (Real.sqrt (d/2:ℕ))⁻¹) ?_
  apply (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
  apply continuous_pi
  intro i
  dsimp
  split_ifs <;> fun_prop

lemma cubeEmbedding_continuous (d : ℕ) : Continuous (CubeEmbedding d) :=
  (cubeRaw_continuous d).comp continuous_subtype_val

lemma cubeEmbedding_measurable (d : ℕ) : Measurable (CubeEmbedding d) :=
  (cubeEmbedding_continuous d).measurable

lemma sqrt_pair_lipschitz {a b : ℝ} (ha : |a| ≤ 1/2) (hb : |b| ≤ 1/2) :
    |Real.sqrt (1-a^2) - Real.sqrt (1-b^2)| ≤ |a-b| := by
  have ha2 : a^2 ≤ 1/4 := by rcases abs_le.mp ha with ⟨ha₁,ha₂⟩; nlinarith
  have hb2 : b^2 ≤ 1/4 := by rcases abs_le.mp hb with ⟨hb₁,hb₂⟩; nlinarith
  have hsa := Real.sq_sqrt (show 0 ≤ 1-a^2 by linarith)
  have hsb := Real.sq_sqrt (show 0 ≤ 1-b^2 by linarith)
  have has : 1/2 ≤ Real.sqrt (1-a^2) := by nlinarith [Real.sqrt_nonneg (1-a^2)]
  have hbs : 1/2 ≤ Real.sqrt (1-b^2) := by nlinarith [Real.sqrt_nonneg (1-b^2)]
  have hab : |a+b| ≤ 1 := (abs_add_le a b).trans (by linarith)
  have he : (Real.sqrt (1-a^2)-Real.sqrt (1-b^2)) *
      (Real.sqrt (1-a^2)+Real.sqrt (1-b^2)) = -(a-b)*(a+b) := by nlinarith
  calc
    _ ≤ |Real.sqrt (1-a^2)-Real.sqrt (1-b^2)| *
        |Real.sqrt (1-a^2)+Real.sqrt (1-b^2)| := by
      apply le_mul_of_one_le_right (abs_nonneg _)
      rw [abs_of_nonneg (by positivity)]
      linarith
    _ = |a-b| * |a+b| := by rw [← abs_mul, he, abs_mul, abs_neg]
    _ ≤ |a-b| := mul_le_of_le_one_right (abs_nonneg _) hab

lemma cubeCoords_sub_norm (d : ℕ) (u v : Cube d) :
    ‖cubeCoords d u.val - cubeCoords d v.val‖ ≤ 2 * ‖u.val-v.val‖ := by
  have hs : ‖cubeCoords d u.val - cubeCoords d v.val‖^2 =
      (∑ i : Fin (d/2), (u.val i-v.val i)^2) +
      ∑ i : Fin (d/2), (Real.sqrt (1-u.val i^2)-Real.sqrt (1-v.val i^2))^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, sum_fin_split (show d/2 ≤ d by omega)]
    simp only [PiLp.sub_apply, cubeCoords_first]
    rw [sum_fin_split (show d/2 ≤ d-d/2 by omega)]
    simp only [cubeCoords_second]
    have hz : (∑ i : Fin (d-d/2-d/2),
      (cubeCoords d u.val ⟨d/2+(d/2+i.val),by omega⟩ -
        cubeCoords d v.val ⟨d/2+(d/2+i.val),by omega⟩)^2) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [cubeCoords_tail d u.val _ (show 2*(d/2) ≤ d/2+(d/2+i.val) by omega),
        cubeCoords_tail d v.val _ (show 2*(d/2) ≤ d/2+(d/2+i.val) by omega)]
      norm_num
    rw [hz, add_zero]
  have hsq : (∑ i : Fin (d/2), (Real.sqrt (1-u.val i^2)-Real.sqrt (1-v.val i^2))^2) ≤
      ∑ i : Fin (d/2), (u.val i-v.val i)^2 := by
    apply Finset.sum_le_sum
    intro i _
    exact (sq_le_sq).2 (sqrt_pair_lipschitz (u.property i) (v.property i))
  have hv : ‖u.val-v.val‖^2 = ∑ i : Fin (d/2), (u.val i-v.val i)^2 := by
    simp [EuclideanSpace.real_norm_sq_eq]
  nlinarith [norm_nonneg (cubeCoords d u.val-cubeCoords d v.val), norm_nonneg (u.val-v.val)]

lemma cubeEmbedding_dist {d : ℕ} (hd : 2 ≤ d) (u v : Cube d) :
    dist (CubeEmbedding d u) (CubeEmbedding d v) ≤
      2 / Real.sqrt (d/2:ℕ) * dist u.val v.val := by
  have hr : 0 < Real.sqrt (d/2:ℕ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < d/2 by omega))
  change dist ((Real.sqrt (d/2:ℕ))⁻¹ • cubeCoords d u.val)
    ((Real.sqrt (d/2:ℕ))⁻¹ • cubeCoords d v.val) ≤ _
  rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, dist_eq_norm]
  calc
    _ ≤ (Real.sqrt (d/2:ℕ))⁻¹ * (2*‖u.val-v.val‖) :=
      mul_le_mul_of_nonneg_left (cubeCoords_sub_norm d u v) (inv_nonneg.mpr hr.le)
    _ = _ := by ring

def cubeProject (d : ℕ) (x : Space d) : Space (d/2) :=
  WithLp.toLp 2 (fun i : Fin (d/2) => x ⟨i.val,by omega⟩)

lemma cubeProject_norm (d : ℕ) (x : Space d) : ‖cubeProject d x‖ ≤ ‖x‖ := by
  have h : ‖cubeProject d x‖^2 ≤ ‖x‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      sum_fin_split (show d/2 ≤ d by omega)]
    change (∑ i : Fin (d/2), x ⟨i.val,by omega⟩^2) ≤ _
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  nlinarith [norm_nonneg (cubeProject d x), norm_nonneg x]

lemma cubeProject_sub (d : ℕ) (x y : Space d) : cubeProject d (x-y) = cubeProject d x-cubeProject d y := by
  ext i
  rfl

lemma cubeProject_embedding (d : ℕ) (u : Cube d) :
    cubeProject d (CubeEmbedding d u) = (Real.sqrt (d/2:ℕ))⁻¹ • u.val := by
  ext i
  simp [cubeProject, CubeEmbedding, cubeRaw]

lemma cubeProject_parameter_dist {d : ℕ} (hd : 2 ≤ d) (u : Cube d) (x : Space d) :
    dist u.val (Real.sqrt (d/2:ℕ) • cubeProject d x) ≤
      Real.sqrt (d/2:ℕ) * dist (CubeEmbedding d u) x := by
  have hr : 0 < Real.sqrt (d/2:ℕ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < d/2 by omega))
  have he : u.val - Real.sqrt (d/2:ℕ) • cubeProject d x =
      Real.sqrt (d/2:ℕ) • cubeProject d (CubeEmbedding d u-x) := by
    rw [cubeProject_sub, cubeProject_embedding, smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos hr, dist_eq_norm]
  exact mul_le_mul_of_nonneg_left (cubeProject_norm d _) hr.le
end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_WeightedImage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

section WeightedImage
variable {X : Type*} [MeasurableSpace X] {d m N : ℕ}

lemma weighted_image_finite (μ : Measure X) [IsFiniteMeasure μ] (ι : X → Space d)
    (h : X → ℝ≥0∞) (hh1 : ∀ x, h x ≤ 1) :
    IsFiniteMeasure ((μ.withDensity h).map ι) := by
  let := isFiniteMeasure_withDensity (μ := μ) (ne_of_lt ((lintegral_mono hh1).trans_lt (by simp)))
  infer_instance

lemma weighted_image_ball (μ : Measure X) {ι : X → Space d} (hι : Measurable ι)
    (h : X → ℝ≥0∞) (z : Space d) (r : ℝ) :
    (μ.withDensity h).map ι (Metric.closedBall z r) =
      ∫⁻ x in {x | dist (ι x) z ≤ r}, h x ∂μ := by
  rw [Measure.map_apply hι Metric.isClosed_closedBall.measurableSet,
    withDensity_apply _ (hι Metric.isClosed_closedBall.measurableSet)]
  rfl

lemma projectionLaw_lintegral (ν : Measure (Space d)) [SFinite ν]
    (g : ((Fin m → Space d) × (Fin m → ℝ)) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x, g x ∂projectionLaw ν m) =
      ∫⁻ s, ∫⁻ A, g (A,fun j => ⟪s,A j⟫)
        ∂Measure.pi (fun _ : Fin m => stdGaussian (Space d)) ∂ν := by
  have hobs : Measurable (fun x : (Fin m → Space d) × Space d => g (x.1,fun j => ⟪x.2,x.1 j⟫)) :=
    hg.comp (by fun_prop)
  rw [projectionLaw, lintegral_map hg (by fun_prop)]
  exact lintegral_prod_symm _ hobs.aemeasurable

lemma weightedBlock_mass_identity (μ : Measure X) [IsFiniteMeasure μ]
    {ι : X → Space d} (hι : Measurable ι)
    {h : Fin N → X → ℝ≥0∞} (hh : ∀ w, Measurable (h w)) (hh1 : ∀ w x, h w x ≤ 1)
    {g : Fin N → ((Fin m → Space d) × (Fin m → ℝ)) → ℝ≥0∞}
    (hg : ∀ w, Measurable (g w)) {B : Set (Space d)} (hB : MeasurableSet B) :
    (∫⁻ x in ι ⁻¹' B, WeightedBlock ι h g x ∂μ) =
      ∑ w, ∫⁻ x, g w x ∂projectionLaw (((μ.withDensity (h w)).map ι).restrict B) m := by
  classical
  let (w : Fin N) : IsFiniteMeasure (μ.withDensity (h w)) :=
    isFiniteMeasure_withDensity (ne_of_lt ((lintegral_mono (hh1 w)).trans_lt (by simp)))
  let G (w : Fin N) (x : X) (A : Fin m → Space d) := g w (A, fun j => ⟪ι x,A j⟫) * h w x
  have hG (w) : Measurable (Function.uncurry (G w)) :=
    ((hg w).comp (by fun_prop)).mul ((hh w).comp measurable_fst)
  have he (w) : (∫⁻ u, g w u ∂projectionLaw (((μ.withDensity (h w)).map ι).restrict B) m) =
      ∫⁻ x in ι ⁻¹' B, ∫⁻ A, G w x A
        ∂Measure.pi (fun _ : Fin m => stdGaussian (Space d)) ∂μ := by
    have hobs : Measurable (fun x : (Fin m → Space d) × Space d =>
        g w (x.1,fun j => ⟪x.2,x.1 j⟫)) := (hg w).comp (by fun_prop)
    have htech : Measurable (fun x : (Fin m → Space d) × X =>
        g w (x.1,fun j => ⟪ι x.2,x.1 j⟫)) := (hg w).comp (by fun_prop)
    rw [projectionLaw_lintegral _ _ (hg w), Measure.restrict_map hι hB,
      lintegral_map hobs.lintegral_prod_left hι,
      restrict_withDensity (hι hB), lintegral_withDensity_eq_lintegral_mul _ (hh w)
        htech.lintegral_prod_left]
    apply lintegral_congr
    intro x
    simp only [Pi.mul_apply]
    rw [← lintegral_const_mul' _ _ (ne_of_lt ((hh1 w x).trans_lt (by simp)))]
    apply lintegral_congr
    intro A
    exact mul_comm _ _
  simp_rw [he]
  rw [← lintegral_finsetSum _ (fun w _ => (hG w).lintegral_prod_right)]
  apply lintegral_congr
  intro x
  unfold WeightedBlock
  exact lintegral_finsetSum _ (fun w _ => (hG w).comp (measurable_const.prodMk measurable_id))
end WeightedImage
end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_DensityPassage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

section FiberSmoothing
variable {Ω Y : Type*} [MeasurableSpace Ω] [NormedAddCommGroup Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  (γ : Measure Ω) (τ : Measure Y) [SigmaFinite τ]

def fiberSmoothing (F : Ω × Y → ℝ≥0∞) (ρ : Y → ℝ≥0∞) (z : Ω × Y) : ℝ≥0∞ :=
  ∫⁻ b, ρ (z.2 - b) * F (z.1, b) ∂τ

@[fun_prop] lemma measurable_fiberSmoothing {F : Ω × Y → ℝ≥0∞} {ρ : Y → ℝ≥0∞}
    (hF : Measurable F) (hρ : Measurable ρ) :
    Measurable (fiberSmoothing τ F ρ) := by
  unfold fiberSmoothing
  exact Measurable.lintegral_prod_right (by fun_prop)

lemma lintegral_fiberSmoothing_test {F : Ω × Y → ℝ≥0∞} {ρ : Y → ℝ≥0∞}
    (hF : Measurable F) (hρ : Measurable ρ) (f : Ω × Y → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, fiberSmoothing τ F ρ z * f z ∂γ.prod τ) =
      ∫⁻ z, (∫⁻ y, ρ (y - z.2) * f (z.1, y) ∂τ) ∂(γ.prod τ).withDensity F := by
  have hK : Measurable (fun z : Ω × Y => ∫⁻ y, ρ (y-z.2) * f (z.1,y) ∂τ) :=
    Measurable.lintegral_prod_right (by fun_prop)
  rw [lintegral_withDensity_eq_lintegral_mul _ hF hK]
  simp only [Pi.mul_apply]
  rw [lintegral_prod (fun z => fiberSmoothing τ F ρ z * f z)
      ((measurable_fiberSmoothing τ hF hρ).mul hf).aemeasurable,
    lintegral_prod (fun z => F z * ∫⁻ y, ρ (y-z.2) * f (z.1,y) ∂τ)
      (hF.mul hK).aemeasurable]
  apply lintegral_congr
  intro A
  dsimp only [fiberSmoothing]
  have hmul (y : Y) : (∫⁻ b, ρ (y-b) * F (A,b) ∂τ) * f (A,y) =
      ∫⁻ b, (ρ (y-b) * F (A,b)) * f (A,y) ∂τ :=
    (lintegral_mul_const _ (by fun_prop)).symm
  simp_rw [hmul]
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_congr
  intro b
  rw [← lintegral_const_mul _ (by fun_prop : Measurable (fun y => ρ (y-b) * f (A,y)))]
  apply lintegral_congr
  intro y
  ring
end FiberSmoothing

section ProjectionSmoothing
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local instance density_reference_sigmaFinite (m : ℕ) :
    SigmaFinite (matrixLabelReference (E := E) m) := by
  unfold matrixLabelReference
  infer_instance

lemma lintegral_projectionSmoothing_test (ν : Measure E) [SigmaFinite ν]
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (m : ℕ)
    (f : (Fin m → E) × (Fin m → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, projectionSmoothing ν φ m z * f z ∂matrixLabelReference m) =
      ∫⁻ z, (∫⁻ y : Fin m → ℝ, (∏ j, φ (y j - z.2 j)) * f (z.1, y))
        ∂projectionLaw ν m := by
  have hK : Measurable (fun z : (Fin m → E) × (Fin m → ℝ) =>
      ∫⁻ y : Fin m → ℝ, (∏ j, φ (y j-z.2 j)) * f (z.1,y)) :=
    Measurable.lintegral_prod_right (by fun_prop)
  rw [projectionLaw, lintegral_map hK (by fun_prop), matrixLabelReference,
    lintegral_prod (fun z => projectionSmoothing ν φ m z * f z)
      ((measurable_projectionSmoothing ν φ hφ m).mul hf).aemeasurable,
    lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro A
  dsimp only [projectionSmoothing]
  have hmul (y : Fin m → ℝ) : (∫⁻ t : E, ∏ j, φ (y j-⟪t,A j⟫) ∂ν) * f (A,y) =
      ∫⁻ t : E, (∏ j, φ (y j-⟪t,A j⟫)) * f (A,y) ∂ν :=
    (lintegral_mul_const _ (by fun_prop)).symm
  simp_rw [hmul]
  rw [lintegral_lintegral_swap (by fun_prop)]

lemma projectionSmoothing_ae_eq_fiberSmoothing (ν : Measure E) [SigmaFinite ν]
    (m : ℕ) (F : (Fin m → E) × (Fin m → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (hden : (matrixLabelReference m).withDensity F = projectionLaw ν m)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    projectionSmoothing ν φ m =ᵐ[matrixLabelReference m]
      fiberSmoothing volume F (fun y : Fin m → ℝ => ∏ j, φ (y j)) := by
  apply (withDensity_eq_iff_of_sigmaFinite
    (measurable_projectionSmoothing ν φ hφ m).aemeasurable
    (measurable_fiberSmoothing volume hF (by fun_prop)).aemeasurable).mp
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_withDensity_eq_lintegral_mul _
    (measurable_projectionSmoothing ν φ hφ m) hf,
    lintegral_withDensity_eq_lintegral_mul _
      (measurable_fiberSmoothing volume hF (by fun_prop)) hf]
  simp only [Pi.mul_apply]
  rw [lintegral_projectionSmoothing_test ν φ hφ m f hf]
  change _ = ∫⁻ z, fiberSmoothing volume F (fun y : Fin m → ℝ => ∏ j, φ (y j)) z * f z
    ∂(Measure.pi (fun _ : Fin m => stdGaussian E)).prod volume
  rw [lintegral_fiberSmoothing_test _ volume hF (by fun_prop) f hf]

  unfold matrixLabelReference at hden
  rw [hden]
  rfl
end ProjectionSmoothing

def boxScalar (δ : ℝ) (t : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (2*δ))⁻¹ * (Icc (-δ) δ).indicator 1 t

@[fun_prop] lemma measurable_boxScalar (δ : ℝ) : Measurable (boxScalar δ) := by
  exact measurable_const.mul (measurable_const.indicator measurableSet_Icc)

lemma lintegral_boxScalar {δ : ℝ} (hδ : 0 < δ) : ∫⁻ t, boxScalar δ t = 1 := by
  unfold boxScalar
  rw [lintegral_const_mul _ (show Measurable ((Icc (-δ) δ).indicator (1 : ℝ → ℝ≥0∞)) from
    measurable_one.indicator measurableSet_Icc), lintegral_indicator measurableSet_Icc]
  simp only [Pi.one_apply, lintegral_const, one_mul, Measure.restrict_apply_univ,
    Real.volume_Icc, sub_neg_eq_add]
  rw [← two_mul]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top

lemma box_product_eq (m : ℕ) {δ : ℝ} (hδ : 0 < δ) (y : Fin m → ℝ) :
    (∏ j, boxScalar δ (y j)) =
      ((volume : Measure (Fin m → ℝ)) (Metric.closedBall 0 δ))⁻¹ *
        (Metric.closedBall 0 δ).indicator 1 y := by
  have hv : (volume : Measure (Fin m → ℝ)) (Metric.closedBall 0 δ) =
      (ENNReal.ofReal (2*δ))^m := by
    rw [volume_pi, closedBall_pi _ hδ.le, Measure.pi_pi]
    simp [Real.closedBall_eq_Icc, ← two_mul]
  rw [hv]
  simp only [boxScalar, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.inv_pow]
  congr 1
  by_cases hy : y ∈ Metric.closedBall (0 : Fin m → ℝ) δ
  · rw [Set.indicator_of_mem hy]
    have hy' : ∀ j, y j ∈ Icc (-δ) δ := by
      intro j
      rw [closedBall_pi _ hδ.le] at hy
      simpa [Real.closedBall_eq_Icc] using hy j (mem_univ j)
    simp [hy']
  · rw [Set.indicator_of_notMem hy]
    have hy' : ∃ j, y j ∉ Icc (-δ) δ := by
      by_contra h
      apply hy
      rw [closedBall_pi _ hδ.le]
      intro j _
      have hh := not_not.mp (not_exists.mp h j)
      simpa [Real.closedBall_eq_Icc] using hh
    obtain ⟨j,hj⟩ := hy'
    exact Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem hj _)

section Differentiation
variable {Ω : Type*} [MeasurableSpace Ω]

lemma fiberSmoothing_box_eq_average (m : ℕ)
    (F : Ω × (Fin m → ℝ) → ℝ≥0∞) (hF : Measurable F)
    {δ : ℝ} (hδ : 0 < δ) (A : Ω) (y : Fin m → ℝ) :
    fiberSmoothing volume F (fun x : Fin m → ℝ => ∏ j, boxScalar δ (x j)) (A,y) =
      (∫⁻ b in Metric.closedBall y δ, F (A,b)) /
        (volume : Measure (Fin m → ℝ)) (Metric.closedBall y δ) := by
  unfold fiberSmoothing
  simp_rw [box_product_eq m hδ]
  have he (b : Fin m → ℝ) :
      (Metric.closedBall (0 : Fin m → ℝ) δ).indicator (1 : (Fin m → ℝ) → ℝ≥0∞) (y-b) * F (A,b) =
      (Metric.closedBall y δ).indicator (fun b => F (A,b)) b := by
    have hb : y-b ∈ Metric.closedBall (0 : Fin m → ℝ) δ ↔ b ∈ Metric.closedBall y δ := by
      simp [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    by_cases h : b ∈ Metric.closedBall y δ
    · rw [Set.indicator_of_mem (hb.mpr h), Set.indicator_of_mem h]; simp
    · rw [Set.indicator_of_notMem (mt hb.mp h), Set.indicator_of_notMem h]; simp
  simp_rw [mul_assoc, he]
  rw [lintegral_const_mul _ (show Measurable ((Metric.closedBall y δ).indicator
    (fun b => F (A,b))) from (hF.comp (measurable_const.prodMk measurable_id)).indicator
      Metric.isClosed_closedBall.measurableSet), lintegral_indicator Metric.isClosed_closedBall.measurableSet,
    div_eq_mul_inv, Measure.addHaar_closedBall_center volume y δ, mul_comm]

lemma ae_tendsto_fiberSmoothing_box (γ : Measure Ω) [SigmaFinite γ] (m : ℕ)
    (F : Ω × (Fin m → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (hfin : (∫⁻ z, F z ∂γ.prod volume) ≠ ∞) :
    ∀ᵐ z ∂γ.prod volume,
      Tendsto (fun k : ℕ => fiberSmoothing volume F
        (fun x : Fin m → ℝ => ∏ j, boxScalar (1 / ((k:ℝ)+1)) (x j)) z)
        atTop (𝓝 (F z)) := by
  have hmeas (k : ℕ) : Measurable (fiberSmoothing volume F
      (fun x : Fin m → ℝ => ∏ j, boxScalar (1 / ((k:ℝ)+1)) (x j))) :=
    measurable_fiberSmoothing volume hF (by fun_prop)
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_tendsto_fun hmeas hF)]
  have hinner : (∫⁻ A, ∫⁻ y : Fin m → ℝ, F (A,y) ∂volume ∂γ) ≠ ∞ := by
    rwa [← lintegral_prod _ hF.aemeasurable]
  filter_upwards [ae_lt_top (Measurable.lintegral_prod_right
    (show Measurable (fun z : Ω × (Fin m → ℝ) => F (z.1,z.2)) from hF)) hinner] with A hA
  have hFA : Measurable (fun y : Fin m → ℝ => F (A,y)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  filter_upwards [(Besicovitch.vitaliFamily (volume : Measure (Fin m → ℝ))).ae_tendsto_lintegral_div
    hFA.aemeasurable hA.ne] with y hy
  have hδ : Tendsto (fun k : ℕ => 1 / ((k:ℝ)+1)) atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Filter.Eventually.of_forall (fun k => by change 0 < 1 / ((k:ℝ)+1); positivity)⟩
  convert (hy.comp (Besicovitch.tendsto_filterAt volume y)).comp hδ using 1
  ext k
  exact fiberSmoothing_box_eq_average m F hF (by positivity) A y
end Differentiation

section MomentPassage
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
local instance passage_reference_sigmaFinite (m : ℕ) :
    SigmaFinite (matrixLabelReference (E := E) m) := by
  unfold matrixLabelReference
  infer_instance
local instance passage_projection_finite (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ) :
    IsFiniteMeasure (projectionLaw ν m) := by
  unfold projectionLaw
  infer_instance

lemma projectionLaw_set_bound_of_moment (ν : Measure E) [IsFiniteMeasure ν]
    (m n : ℕ) (hn : 1 ≤ n) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hbound : ∀ φ : ℝ → ℝ≥0∞, Measurable φ → (∫⁻ x, φ x = 1) →
      (∫⁻ Ay, projectionSmoothing ν φ m Ay ^ (n+1) ∂matrixLabelReference m) ≤ C)
    (S : Set ((Fin m → E) × (Fin m → ℝ))) :
    projectionLaw ν m S ≤ C^(1 / ((n : ℝ) + 1)) *
      (matrixLabelReference (E := E) m S)^(1 - 1 / ((n : ℝ) + 1)) := by
  have hp : 1 < (n : ℝ) + 1 := by exact_mod_cast (by omega : 1 < n + 1)
  have hα : 0 < 1 - 1 / ((n : ℝ) + 1) := by
    exact sub_pos.mpr ((div_lt_one (by positivity)).mpr hp)
  have := matrixLabelReference_outerRegular (E := E) m
  apply measure_apply_le_of_isOpen _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity) hC) hα
  intro U hU
  rw [← gaussianCoupling_map_noisyObservation_zero ν m]
  apply map_apply_open_le_of_tendsto (gaussianCoupling ν m)
    (matrixLabelReference (E := E) m) (noisyObservation m 0)
    (fun k => noisyObservation m (1 / ((k : ℝ) + 1)))
    (measurable_noisyObservation m 0) (fun k => measurable_noisyObservation m _)
    (tendsto_noisyObservation m) _ _ (U := U) (hU := hU)
  intro k V hV
  have hδ : (1 / ((k : ℝ) + 1)) ≠ 0 := by positivity
  rw [gaussianCoupling_map_noisyObservation ν m _ hδ]
  apply withDensity_apply_le_moment _ _
    (measurable_projectionSmoothing _ _ (measurable_gaussianPDF _ _) _) hp _ _ hV.measurableSet
  have hv : (NNReal.mk ((1 / ((k : ℝ) + 1)) ^ 2)
      (sq_nonneg (1 / ((k : ℝ) + 1)))) ≠ 0 := by
    rw [← NNReal.coe_ne_zero]
    exact pow_ne_zero 2 hδ
  simpa only [← ENNReal.rpow_natCast, Nat.cast_add, Nat.cast_one] using
    hbound (gaussianPDF 0 (NNReal.mk ((1 / ((k : ℝ) + 1)) ^ 2)
      (sq_nonneg (1 / ((k : ℝ) + 1))))) (measurable_gaussianPDF _ _)
      (lintegral_gaussianPDF_eq_one _ hv)

lemma projectionLaw_ac_of_moment (ν : Measure E) [IsFiniteMeasure ν]
    (m n : ℕ) (hn : 1 ≤ n) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hbound : ∀ φ : ℝ → ℝ≥0∞, Measurable φ → (∫⁻ x, φ x = 1) →
      (∫⁻ Ay, projectionSmoothing ν φ m Ay ^ (n+1) ∂matrixLabelReference m) ≤ C) :
    projectionLaw ν m ≪ matrixLabelReference m := by
  intro S hS
  have hh := projectionLaw_set_bound_of_moment ν m n hn C hC hbound S
  have hα : 0 < 1 - 1 / ((n : ℝ) + 1) := by
    have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
    exact sub_pos.mpr ((div_lt_one (by positivity)).mpr (by linarith))
  rw [hS, ENNReal.zero_rpow_of_pos hα, mul_zero] at hh
  exact le_zero_iff.mp hh

lemma projectionLaw_rnDeriv_moment (ν : Measure E) [IsFiniteMeasure ν]
    (m n : ℕ) (hn : 1 ≤ n) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hbound : ∀ φ : ℝ → ℝ≥0∞, Measurable φ → (∫⁻ x, φ x = 1) →
      (∫⁻ Ay, projectionSmoothing ν φ m Ay ^ (n+1) ∂matrixLabelReference m) ≤ C) :
    (∫⁻ Ay, ((projectionLaw ν m).rnDeriv (matrixLabelReference m) Ay)^(n+1)
      ∂matrixLabelReference m) ≤ C := by
  let F := (projectionLaw ν m).rnDeriv (matrixLabelReference m)
  have hF : Measurable F := Measure.measurable_rnDeriv _ _
  have hden : (matrixLabelReference m).withDensity F = projectionLaw ν m :=
    Measure.withDensity_rnDeriv_eq _ _ (projectionLaw_ac_of_moment ν m n hn C hC hbound)
  let f : ℕ → ((Fin m → E) × (Fin m → ℝ)) → ℝ≥0∞ := fun k =>
    projectionSmoothing ν (boxScalar (1/((k:ℝ)+1))) m
  have hf (k : ℕ) : Measurable (f k) :=
    measurable_projectionSmoothing ν _ (measurable_boxScalar _) m
  have heq (k : ℕ) : f k =ᵐ[matrixLabelReference m]
      fiberSmoothing volume F (fun y : Fin m → ℝ => ∏ j, boxScalar (1/((k:ℝ)+1)) (y j)) :=
    projectionSmoothing_ae_eq_fiberSmoothing ν m F hF hden _ (measurable_boxScalar _)
  have ht : ∀ᵐ Ay ∂matrixLabelReference m, Tendsto (fun k => f k Ay) atTop (𝓝 (F Ay)) := by
    filter_upwards [ae_all_iff.mpr heq,
      ae_tendsto_fiberSmoothing_box (Measure.pi (fun _ : Fin m => stdGaussian E)) m F hF
        (Measure.lintegral_rnDeriv_lt_top (projectionLaw ν m) (matrixLabelReference m)).ne]
      with Ay he ht
    exact ht.congr (fun k => (he k).symm)
  calc
    _ = ∫⁻ Ay, atTop.liminf (fun k => (f k Ay)^(n+1)) ∂matrixLabelReference m := by
      apply lintegral_congr_ae
      filter_upwards [ht] with Ay hAy
      exact (((ENNReal.continuous_pow (n+1)).tendsto _ |>.comp hAy).liminf_eq).symm
    _ ≤ atTop.liminf (fun k => ∫⁻ Ay, (f k Ay)^(n+1) ∂matrixLabelReference m) :=
      lintegral_liminf_le (fun k => (hf k).pow_const _)
    _ ≤ C := by
      apply liminf_le_of_frequently_le (hu_le := by isBoundedDefault)
      exact (Filter.Eventually.of_forall (fun k =>
        hbound _ (measurable_boxScalar _) (lintegral_boxScalar (by positivity)))).frequently
end MomentPassage

end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_SharpGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression InnerProductSpace

def gaussianPeak : ℝ≥0∞ := ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹)

lemma sharp_gaussianReal_le_volume :
    gaussianReal 0 1 ≤ gaussianPeak • (volume : Measure ℝ) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num)]
  calc
    _ ≤ (volume : Measure ℝ).withDensity (fun _ => gaussianPeak) := by
      apply withDensity_mono
      filter_upwards [] with x
      apply ENNReal.ofReal_le_ofReal
      unfold gaussianPDFReal
      simp only [NNReal.coe_one, mul_one, sub_zero]
      exact mul_le_of_le_one_right (by positivity)
        (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (sq_nonneg x)) (by positivity)))
    _ = _ := by rw [withDensity_const]

lemma sharp_pi_gaussianReal_le_volume (n : ℕ) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) ≤
      gaussianPeak ^ n • (volume : Measure (Fin n → ℝ)) := by
  have h := measure_pi_mono (fun _ : Fin n => sharp_gaussianReal_le_volume)
  rw [measure_pi_smul _ _ (show gaussianPeak ≠ ∞ from ENNReal.ofReal_ne_top)] at h
  simpa only [Fintype.card_fin, volume_pi] using h

section Gaussian
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
local instance sharp_reference_sigmaFinite (m : ℕ) :
    SigmaFinite (matrixLabelReference (E := E) m) := by
  unfold matrixLabelReference
  infer_instance

lemma sharp_gaussian_pairings_le {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℝ v) :
    (stdGaussian E).map (fun x => fun i => ⟪v i, x⟫) ≤
      (gaussianPeak ^ n * ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹)) •
        (volume : Measure (Fin n → ℝ)) := by
  let u := gramSchmidtNormed ℝ v
  let R : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i => ‖gramSchmidt ℝ v i‖) * gsUpper n v
  have hu : Orthonormal ℝ u := gramSchmidtNormed_orthonormal hv
  have hn (i : Fin n) : ‖gramSchmidt ℝ v i‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i hv)
  have hexp (j : Fin n) : ∑ i, R i j • u i = v j := by
    rw [← gsUpper_expansion n v j]
    apply Finset.sum_congr rfl
    intro i _
    simp only [R, u, Matrix.diagonal_mul, gramSchmidtNormed, smul_smul]
    congr 1
    simp [hn i, mul_comm]
  have hdet : R.transpose.det = ∏ i, ‖gramSchmidt ℝ v i‖ := by
    dsimp only [R]
    rw [Matrix.det_transpose, Matrix.det_mul, Matrix.det_diagonal, gsUpper_det, mul_one]
  have hd : R.transpose.det ≠ 0 := by
    rw [hdet]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hn i)
  have hpos : 0 ≤ R.transpose.det := by rw [hdet]; positivity
  have hf : Measurable (Matrix.toLin' R.transpose) :=
    (Matrix.toLin' R.transpose).continuous_of_finiteDimensional.measurable
  have heq : (fun x : E => fun j => ⟪v j, x⟫) =
      (Matrix.toLin' R.transpose) ∘ (fun x => fun i => ⟪u i, x⟫) := by
    funext x j
    rw [← hexp j]
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, sum_inner,
      inner_smul_left]
  rw [heq, ← Measure.map_map hf (by fun_prop), orthonormal_gaussian_map hu]
  calc
    _ ≤ (gaussianPeak ^ n • (volume : Measure (Fin n → ℝ))).map
        (Matrix.toLin' R.transpose) :=
      Measure.map_mono (sharp_pi_gaussianReal_le_volume n) hf
    _ = _ := by
      rw [Measure.map_smul, Real.map_matrix_volume_pi_eq_smul_volume_pi hd,
        abs_of_nonneg (inv_nonneg.mpr hpos), hdet, smul_smul]

lemma sharp_gaussian_rows_pairings_le {n : ℕ} (v : Fin n → E)
    (hv : LinearIndependent ℝ v) (m : ℕ) :
    (Measure.pi (fun _ : Fin m => stdGaussian E)).map
      (fun A => fun j i => ⟪v i, A j⟫) ≤
      ((gaussianPeak ^ n * ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹)) ^ m) •
        (volume : Measure (Fin m → Fin n → ℝ)) := by
  rw [Measure.pi_map_pi (fun _ => (by fun_prop : Measurable
    (fun x : E => fun i => ⟪v i, x⟫)).aemeasurable)]
  have h := measure_pi_mono (fun _ : Fin m => sharp_gaussian_pairings_le v hv)
  rw [measure_pi_smul _ _ (ENNReal.mul_ne_top (ENNReal.pow_ne_top
    (show gaussianPeak ≠ ∞ from ENNReal.ofReal_ne_top)) ENNReal.ofReal_ne_top)] at h
  simpa only [Fintype.card_fin, volume_pi] using h
lemma sharp_gaussian_rows_kernel_bound {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℝ v)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ z, φ z = 1)
    (m : ℕ) (y : Fin m → ℝ) :
    ∫⁻ A : Fin m → E, (∏ j, φ (y j)) * ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫)
      ∂Measure.pi (fun _ => stdGaussian E) ≤
      ((gaussianPeak ^ n * ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹)) ^ m) * ∏ j, φ (y j) := by
  let H : (Fin m → Fin n → ℝ) → ℝ≥0∞ :=
    fun z => ∏ j, φ (y j) * ∏ i, φ (y j - z j i)
  have hH : Measurable H := by dsimp [H]; fun_prop
  have heq (A : Fin m → E) :
      (∏ j, φ (y j)) * ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫) =
      H (fun j i => ⟪v i, A j⟫) := by
    dsimp [H]
    rw [Finset.prod_mul_distrib, Finset.prod_comm]
  simp_rw [heq]
  rw [← lintegral_map hH (by fun_prop)]
  calc
    _ ≤ ∫⁻ z, H z ∂(((gaussianPeak ^ n * ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹)) ^ m) •
        (volume : Measure (Fin m → Fin n → ℝ))) :=
      lintegral_mono' (sharp_gaussian_rows_pairings_le v hv m) (fun _ => le_rfl)
    _ = _ := by
      rw [lintegral_smul_measure]
      change _ * (∫⁻ z : Fin m → Fin n → ℝ, ∏ j, φ (y j) * ∏ i, φ (y j - z j i)) = _
      rw [lintegral_product_differences φ hφ hφ1]

lemma sharp_gaussian_replica_kernel_bound {n : ℕ} (p : E) (v : Fin n → E)
    (hv : LinearIndependent ℝ (fun i => v i - p))
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ z, φ z = 1) (m : ℕ) :
    ∫⁻ A : Fin m → E, ∫⁻ y : Fin m → ℝ,
      (∏ j, φ (y j - ⟪p, A j⟫)) * ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫)
      ∂volume ∂Measure.pi (fun _ => stdGaussian E) ≤
      ((gaussianPeak ^ n * ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ (fun i => v i - p) i‖)⁻¹)) ^ m) := by
  have ht (A : Fin m → E) :
      (∫⁻ y : Fin m → ℝ, (∏ j, φ (y j - ⟪p, A j⟫)) *
        ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫)) =
      ∫⁻ y : Fin m → ℝ, (∏ j, φ (y j)) * ∏ i, ∏ j, φ (y j - ⟪v i - p, A j⟫) := by
    have he (y : Fin m → ℝ) (i : Fin n) (j : Fin m) :
        y j - ⟪p, A j⟫ - ⟪v i - p, A j⟫ = y j - ⟪v i, A j⟫ := by
      rw [inner_sub_left]
      ring
    simpa only [Pi.sub_apply, he] using
      lintegral_sub_right_eq_self
        (fun y : Fin m → ℝ => (∏ j, φ (y j)) * ∏ i, ∏ j, φ (y j - ⟪v i - p, A j⟫))
        (fun j => ⟪p, A j⟫)
  simp_rw [ht]
  rw [lintegral_lintegral_swap (by fun_prop)]
  calc
    _ ≤ ∫⁻ y : Fin m → ℝ,
      ((gaussianPeak ^ n * ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ (fun i => v i - p) i‖)⁻¹)) ^ m) *
        ∏ j, φ (y j) := lintegral_mono fun y =>
          sharp_gaussian_rows_kernel_bound (fun i => v i - p) hv φ hφ hφ1 m y
    _ = _ := by
      rw [lintegral_const_mul _ (by fun_prop), volume_pi,
        lintegral_fin_prod volume m (fun _ => φ) (fun _ => hφ)]
      simp [hφ1]

lemma sharp_projectionSmoothing_moment {ν : Measure E} [IsFiniteMeasure ν]
    {H β R : ℝ} {z : E} (hH : 0 < H) (hR : 0 < R)
    (hsupport : ν.support ⊆ Metric.closedBall z R)
    (hball : ∀ x : E, ∀ r : ℝ, 0 < r →
      ν (Metric.closedBall x r) ≤ ENNReal.ofReal (H*r^β))
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ x, φ x = 1)
    {m : ℕ} (hm : 0 < m) (n : ℕ) (hgap : (n:ℝ)+(m:ℝ)-1 < β) :
    (∫⁻ Ay : (Fin m → E) × (Fin m → ℝ),
      (projectionSmoothing ν φ m Ay)^(n+1) ∂matrixLabelReference m) ≤
      gaussianPeak ^ (n*m) * ENNReal.ofReal
        (H^(n+1) * R^(β*(n+1:ℕ)-(m:ℝ)*(n:ℝ)) * ∏ j : Fin n, J β m j) := by
  simp_rw [projectionSmoothing_pow ν φ hφ m n]
  rw [lintegral_lintegral_swap (by fun_prop)]
  calc
    _ ≤ ∫⁻ w : E × (Fin n → E), gaussianPeak ^ (n*m) * replicaWeight m w.1 w.2
        ∂ν.prod (Measure.pi (fun _ => ν)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_joint_replica_independent hH hR hsupport hball hm n hgap] with w hw
      rw [matrixLabelReference, lintegral_prod _ (by fun_prop)]
      convert sharp_gaussian_replica_kernel_bound w.1 w.2 hw φ hφ hφ1 m using 1
      rw [mul_pow, ← pow_mul, replicaWeight_eq_det, sqrt_det_gram,
        ENNReal.ofReal_pow (by positivity)]
    _ = gaussianPeak ^ (n*m) *
        (∫⁻ w : E × (Fin n → E), replicaWeight m w.1 w.2
          ∂ν.prod (Measure.pi (fun _ => ν))) :=
      lintegral_const_mul _ (measurable_joint_replicaWeight m n)
    _ ≤ _ := mul_le_mul' le_rfl
      (joint_replica_integral_exact hH hR hsupport hball hm n hgap)

end Gaussian
end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_FiniteDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

lemma isClosed_projectedEllipsoid {d m : ℕ} (z : Space d) (R : ℝ) :
    IsClosed (ProjectedEllipsoid (m := m) z R) := by
  let K := Metric.closedBall (0 : Space d) R
  have hK : IsCompact K := isCompact_closedBall _ _
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let D : Set (((Fin m → Space d) × (Fin m → ℝ)) × K) :=
    {w | w.1.2 = fun j => ⟪z, w.1.1 j⟫ + ⟪(w.2 : Space d), w.1.1 j⟫}
  have hD : IsClosed D := isClosed_eq (by fun_prop) (by fun_prop)
  have he : ProjectedEllipsoid (m := m) z R = Prod.fst '' D := by
    ext Ay
    constructor
    · rintro ⟨v, hv, he⟩
      exact ⟨(Ay, ⟨v,hv⟩), he, rfl⟩
    · rintro ⟨⟨Ay,v⟩, hv, rfl⟩
      exact ⟨v, v.property, hv⟩
  rw [he]
  exact isClosedMap_fst_of_compactSpace D hD

lemma projectionLaw_ellipsoid_compl {d m : ℕ} (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {z : Space d} {R : ℝ} (hsupport : μ.support ⊆ Metric.closedBall z R) :
    projectionLaw μ m (ProjectedEllipsoid z R)ᶜ = 0 := by
  rw [projectionLaw, Measure.map_apply (by fun_prop)
    (isClosed_projectedEllipsoid z R).measurableSet.compl]
  apply measure_mono_null (t := Set.univ ×ˢ μ.supportᶜ)
  · rintro ⟨A,s⟩ hs
    refine ⟨mem_univ _, ?_⟩
    intro hss
    apply hs
    refine ⟨s-z, ?_, ?_⟩
    · change dist (s - z) (0 : Space d) ≤ R
      simpa [Metric.mem_closedBall, dist_eq_norm] using hsupport hss
    · ext j
      simp [inner_sub_left]
  · rw [Measure.prod_prod]
    simp [μ.measure_compl_support]

lemma moment_root_eq_scale {m p : ℕ} {H β R : ℝ} (hp : 2 ≤ p) (hH : 0 < H)
    (hR : 0 < R) (hgap : (m:ℝ)+(p:ℝ)-2 < β) :
    (gaussianPeak ^ ((p-1)*m) * ENNReal.ofReal
      (H^p * R^(β*(p:ℝ)-(m:ℝ)*((p-1:ℕ):ℝ)) * ∏ j : Fin (p-1), J β m j)) ^ (1/(p:ℝ)) =
      ENNReal.ofReal (ProjectionNormScale m p H β R) := by
  have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hp1 : 1 ≤ p := by omega
  have hprod : 0 < ∏ j : Fin (p-1), J β m j := by
    apply Finset.prod_pos
    intro j _
    apply J_pos
    have hj : (j:ℝ)+2 ≤ p := by exact_mod_cast (show (j:ℕ)+2 ≤ p by have := j.isLt; omega)
    linarith
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), gaussianPeak,
    ← ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_rpow_of_pos (by positivity),
    ENNReal.ofReal_rpow_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.mul_rpow (by positivity : 0 ≤ H^p * R^(β*p-m*((p-1:ℕ):ℝ))) hprod.le,
    Real.mul_rpow (by positivity : 0 ≤ H^p) (by positivity),
    ← Real.rpow_natCast_mul hH.le, mul_one_div_cancel hp0, Real.rpow_one,
    ← Real.rpow_mul hR.le,
    ← Real.rpow_natCast_mul (by positivity : 0 ≤ (Real.sqrt (2*Real.pi))⁻¹),
    Real.inv_rpow (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_mul hpi.le,
    ← Real.rpow_neg hpi.le]
  have he1 : -(1/2 * (((p-1:ℕ):ℝ)*(m:ℝ) * (1/(p:ℝ)))) =
      -(m:ℝ)*((p:ℝ)-1)/(2*(p:ℝ)) := by rw [Nat.cast_sub hp1]; push_cast; ring
  have he2 : (β*(p:ℝ)-(m:ℝ)*((p-1:ℕ):ℝ)) * (1/(p:ℝ)) =
      β-(m:ℝ)*(1-1/(p:ℝ)) := by rw [Nat.cast_sub hp1]; push_cast; field_simp
  simp only [Nat.cast_mul] at *
  rw [he1, he2, Fin.prod_univ_eq_prod_range]
  unfold ProjectionNormScale
  ring

local instance final_reference_sigmaFinite (d m : ℕ) :
    SigmaFinite (matrixLabelReference (E := Space d) m) := by
  unfold matrixLabelReference
  infer_instance
local instance final_projection_finite {d : ℕ} (μ : Measure (Space d)) [IsFiniteMeasure μ] (m : ℕ) :
    IsFiniteMeasure (projectionLaw μ m) := by
  unfold projectionLaw
  infer_instance

lemma exact_finite_density (d m p : ℕ) (hp : 2 ≤ p) (hm : 1 ≤ m)
    (β H R : ℝ) (hgap : (m:ℝ)+(p:ℝ)-2 < β) (hH : 0 < H) (hR : 0 < R)
    (z : Space d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hsupport : μ.support ⊆ Metric.closedBall z R) (hball : AmbientBallBound μ H β) :
    ∃ F : ((Fin m → Space d) × (Fin m → ℝ)) → ℝ,
      Measurable F ∧ (∀ x, 0 ≤ F x) ∧
      (MatrixLabelReference d m).withDensity (fun x => ENNReal.ofReal (F x)) =
        ProjectionLaw μ m ∧
      (∀ᵐ x ∂MatrixLabelReference d m, x ∉ ProjectedEllipsoid z R → F x = 0) ∧
      eLpNorm F (p : ℝ≥0∞) (MatrixLabelReference d m) ≤
        ENNReal.ofReal (ProjectionNormScale m p H β R) := by
  let C := gaussianPeak ^ ((p-1)*m) * ENNReal.ofReal
    (H^p * R^(β*(p:ℝ)-(m:ℝ)*((p-1:ℕ):ℝ)) * ∏ j : Fin (p-1), J β m j)
  have hC : C ≠ ∞ := by unfold C gaussianPeak; finiteness
  have hp1 : p-1+1 = p := by omega
  have hmom : ∀ φ : ℝ → ℝ≥0∞, Measurable φ → (∫⁻ x, φ x = 1) →
      (∫⁻ Ay, projectionSmoothing μ φ m Ay ^ (p-1+1) ∂matrixLabelReference m) ≤ C := by
    intro φ hφ hφ1
    have hg : ((p-1:ℕ):ℝ)+(m:ℝ)-1 < β := by
      rw [Nat.cast_sub (by omega : 1 ≤ p)]
      push_cast
      linarith
    simpa only [hp1] using sharp_projectionSmoothing_moment hH hR hsupport hball φ hφ hφ1 hm (p-1) hg
  have hac := projectionLaw_ac_of_moment μ m (p-1) (by omega) C hC hmom
  let G := (projectionLaw μ m).rnDeriv (matrixLabelReference m)
  have hG : Measurable G := Measure.measurable_rnDeriv _ _
  have hden : (matrixLabelReference m).withDensity G = projectionLaw μ m :=
    Measure.withDensity_rnDeriv_eq _ _ hac
  have hGtop : ∀ᵐ x ∂matrixLabelReference m, G x ≠ ∞ := Measure.rnDeriv_ne_top _ _
  have hGmom : (∫⁻ x, G x^p ∂matrixLabelReference m) ≤ C := by
    simpa only [hp1] using projectionLaw_rnDeriv_moment μ m (p-1) (by omega) C hC hmom
  let F := fun x => (G x).toReal
  have hFG : (fun x => ENNReal.ofReal (F x)) =ᵐ[matrixLabelReference m] G := by
    filter_upwards [hGtop] with x hx
    exact ENNReal.ofReal_toReal hx
  refine ⟨F, hG.ennreal_toReal, fun _ => ENNReal.toReal_nonneg, ?_, ?_, ?_⟩
  · change (matrixLabelReference m).withDensity _ = projectionLaw μ m
    rw [withDensity_congr_ae hFG, hden]
  · have hnull := projectionLaw_ellipsoid_compl μ hsupport (m := m)
    rw [← hden, withDensity_apply _ (isClosed_projectedEllipsoid z R).measurableSet.compl] at hnull
    have hz := (lintegral_eq_zero_iff' hG.aemeasurable).mp hnull
    change ∀ᵐ x ∂(matrixLabelReference m).restrict (ProjectedEllipsoid z R)ᶜ, G x = 0 at hz
    rw [ae_restrict_iff' (isClosed_projectedEllipsoid z R).measurableSet.compl] at hz
    filter_upwards [hz] with x hx hnot
    dsimp [F]
    rw [hx hnot]
    rfl
  · change eLpNorm F (p:ℝ≥0∞) (matrixLabelReference m) ≤ _
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by exact_mod_cast (by omega : p ≠ 0))
      (by finiteness)]
    simp only [ENNReal.toReal_natCast]
    have he : (fun x => ‖F x‖ₑ ^ (p:ℝ)) =ᵐ[matrixLabelReference m] (fun x => G x^p) := by
      filter_upwards [hFG] with x hx
      rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, hx, ENNReal.rpow_natCast]
    rw [lintegral_congr_ae he]
    exact (ENNReal.rpow_le_rpow hGmom (by positivity)).trans_eq
      (moment_root_eq_scale hp hH hR hgap)

end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_MeasurableTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision

section TestTransfer
variable {X : Type*} [mX : MeasurableSpace X]

lemma original_le_completion (ν : Measure X) :
    mX ≤ (inferInstance : MeasurableSpace (NullMeasurableSpace X ν)) :=
  fun _ hs => hs.nullMeasurableSet

lemma density_test_bound (ν : Measure X) (F : X → ℝ) (hF : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x) (p : ℕ) (hp : 2 ≤ p) (B : ℝ≥0∞)
    (hnorm : eLpNorm F (p:ℝ≥0∞) ν ≤ B) (S : Set X) (hS : MeasurableSet S)
    (hsupp : ∀ᵐ x ∂ν, x ∉ S → F x = 0)
    (φ : X → ℝ≥0∞) (hφ : AEMeasurable φ ν) (hφ1 : ∀ x, φ x ≤ 1) :
    (∫⁻ x, φ x ∂ν.withDensity (fun x => ENNReal.ofReal (F x))) ≤
      B * (∫⁻ x in S, φ x ∂ν)^(1-1/(p:ℝ)) := by
  have hp' : 1 < (p:ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hpq := Real.HolderConjugate.conjExponent hp'
  have hq : 1 / Real.conjExponent (p:ℝ) = 1-1/(p:ℝ) := by
    simpa only [one_div] using (eq_sub_of_add_eq' hpq.inv_add_inv_eq_one)
  let K := S.indicator φ
  have hK : AEMeasurable K ν := hφ.indicator hS
  have hK1 : ∀ x, K x ≤ 1 := by
    intro x
    exact (Set.indicator_le (g := fun _ => 1) (fun _ _ => hφ1 _)) x
  rw [lintegral_withDensity_eq_lintegral_mul₀ (hF.ennreal_ofReal.aemeasurable) hφ]
  have he : (fun x => ENNReal.ofReal (F x) * φ x) =ᵐ[ν]
      (fun x => ENNReal.ofReal (F x) * K x) := by
    filter_upwards [hsupp] with x hx
    by_cases hxS : x ∈ S
    · simp [K, Set.indicator_of_mem hxS]
    · simp [K, Set.indicator_of_notMem hxS, hx hxS]
  simp only [Pi.mul_apply]
  rw [lintegral_congr_ae he]
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq hF.ennreal_ofReal.aemeasurable hK
  have hnormeq : (∫⁻ x, ENNReal.ofReal (F x) ^ (p:ℝ) ∂ν) ^ (1/(p:ℝ)) =
      eLpNorm F (p:ℝ≥0∞) ν := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by exact_mod_cast (by omega : p ≠ 0))
      (by finiteness)]
    simp only [ENNReal.toReal_natCast, Real.enorm_eq_ofReal (hF0 _)]
  rw [hnormeq, hq] at hholder
  refine hholder.trans (mul_le_mul' hnorm ?_)
  apply ENNReal.rpow_le_rpow _ (by rw [← hq]; exact hpq.symm.one_div_nonneg)
  calc
    (∫⁻ x, K x ^ Real.conjExponent (p:ℝ) ∂ν) ≤ ∫⁻ x, K x ∂ν :=
      lintegral_mono (fun x => ENNReal.rpow_le_self_of_le_one (hK1 x) hpq.symm.lt.le)
    _ = _ := lintegral_indicator hS _

end TestTransfer

end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_WeightedSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

def realNormalize {d : ℕ} (ν : Measure (Space d)) (β H : ℝ) (z : Space d) (r : ℝ) :
    Measure (Space d) :=
  (ENNReal.ofReal (H * r^β))⁻¹ •
    (ν.restrict (Metric.closedBall z r)).map (fun x => r⁻¹ • (x-z))

lemma realNormalize_local {d : ℕ} {ν : Measure (Space d)} {β H : ℝ}
    (hν : AmbientBallBound ν H β) (hH : 0 < H) (z : Space d) {r : ℝ} (hr : 0 < r) :
    AmbientBallBound (realNormalize ν β H z r) 1 β := by
  have hc0 : ENNReal.ofReal (H*r^β) ≠ 0 := by positivity
  intro t ρ hρ
  rw [realNormalize, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (by fun_prop) Metric.isClosed_closedBall.measurableSet]
  have hsub : (fun x : Space d => r⁻¹ • (x-z)) ⁻¹' Metric.closedBall t ρ ⊆
      Metric.closedBall (z + r • t) (r*ρ) := by
    intro x hx
    have he : x-(z+r•t) = r • (r⁻¹ • (x-z)-t) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      abel
    rw [Metric.mem_closedBall, dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm] using hx) hr.le
  calc
    _ ≤ (ENNReal.ofReal (H*r^β))⁻¹ * ν (Metric.closedBall (z+r•t) (r*ρ)) :=
      mul_le_mul' le_rfl ((Measure.restrict_le_self _).trans (measure_mono hsub))
    _ ≤ (ENNReal.ofReal (H*r^β))⁻¹ * ENNReal.ofReal (H*(r*ρ)^β) :=
      mul_le_mul' le_rfl (hν _ _ (mul_pos hr hρ))
    _ = ENNReal.ofReal (1*ρ^β) := by
      rw [Real.mul_rpow hr.le hρ.le, ← mul_assoc,
        ENNReal.ofReal_mul (by positivity : 0 ≤ H*r^β), ← mul_assoc,
        ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_mul, one_mul]

lemma realNormalize_support {d : ℕ} (ν : Measure (Space d)) (β H : ℝ)
    (z : Space d) {r : ℝ} (hr : 0 < r) :
    (realNormalize ν β H z r).support ⊆ Metric.closedBall 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_closedBall
  rw [mem_ae_iff, realNormalize, Measure.smul_apply, Measure.map_apply (by fun_prop)
    Metric.isClosed_closedBall.measurableSet.compl,
    Measure.restrict_apply ((by fun_prop : Measurable (fun x : Space d => r⁻¹ • (x-z)))
      Metric.isClosed_closedBall.measurableSet.compl)]
  have he : (fun x : Space d => r⁻¹ • (x-z)) ⁻¹' (Metric.closedBall 0 1)ᶜ ∩
      Metric.closedBall z r = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x ⟨hx,hb⟩
    apply hx
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
    exact (inv_mul_le_iff₀ hr).2 (by simpa [dist_eq_norm] using hb)
  rw [he, measure_empty, smul_zero]

lemma realNormalize_finite {d : ℕ} (ν : Measure (Space d)) [IsFiniteMeasure ν]
    {β H : ℝ} (hH : 0 < H) (z : Space d) {r : ℝ} (hr : 0 < r) :
    IsFiniteMeasure (realNormalize ν β H z r) := by
  constructor
  rw [realNormalize, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.mul_lt_top
  · exact ENNReal.inv_lt_top.mpr (by positivity)
  · exact measure_lt_top _ _

lemma realNormalize_reconstruct {d : ℕ} (ν : Measure (Space d)) {β H : ℝ}
    (hH : 0 < H) (z : Space d) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (H*r^β) • (realNormalize ν β H z r).map (fun t => z+r•t) =
      ν.restrict (Metric.closedBall z r) := by
  have hc0 : ENNReal.ofReal (H*r^β) ≠ 0 := by positivity
  rw [realNormalize, Measure.map_smul, smul_smul,
    ENNReal.mul_inv_cancel hc0 ENNReal.ofReal_ne_top, one_smul,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun t : Space d => z+r•t) ∘ (fun x => r⁻¹ • (x-z)) = id := by
    ext x
    simp [smul_smul, hr.ne']
  rw [he, Measure.map_id]

lemma normalized_scale_le {d m p : ℕ} (hp : 2 ≤ p) {β K : ℝ} (hK : 1 ≤ K)
    (hgap : (m:ℝ)+(p:ℝ)-2 < β)
    (hJ : ∀ j : ℕ, j ≤ p-2 → J β m j ≤ K^d) :
    ProjectionNormScale m p 1 β 1 ≤ K^d := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hprod0 : 0 ≤ ∏ j ∈ Finset.range (p-1), J β m j := by
    apply Finset.prod_nonneg
    intro j hj
    apply (J_pos ?_).le
    have hj' : (j:ℝ)+2 ≤ p := by exact_mod_cast (show j+2 ≤ p by have := Finset.mem_range.mp hj; omega)
    linarith
  have hprod : (∏ j ∈ Finset.range (p-1), J β m j) ≤ (K^d)^(p-1) := by
    calc
      _ ≤ ∏ _j ∈ Finset.range (p-1), K^d := by
        apply Finset.prod_le_prod
        · intro j hj
          apply (J_pos ?_).le
          have hj' : (j:ℝ)+2 ≤ p := by exact_mod_cast (show j+2 ≤ p by have := Finset.mem_range.mp hj; omega)
          linarith
        · intro j hj
          exact hJ j (by have := Finset.mem_range.mp hj; omega)
      _ = _ := by simp
  have hpeak : (2*Real.pi) ^ (-(m:ℝ)*((p:ℝ)-1)/(2*(p:ℝ))) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · linarith [Real.pi_gt_three]
    · have : (1:ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
      apply div_nonpos_of_nonpos_of_nonneg
      · exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg m)) (by linarith)
      · positivity
  unfold ProjectionNormScale
  simp only [mul_one, Real.one_rpow]
  calc
    _ ≤ 1 * (∏ j ∈ Finset.range (p-1), J β m j)^(1/(p:ℝ)) :=
      mul_le_mul_of_nonneg_right hpeak (Real.rpow_nonneg hprod0 _)
    _ ≤ ((K^d)^(p-1))^(1/(p:ℝ)) := by rw [one_mul]; exact Real.rpow_le_rpow hprod0 hprod (by positivity)
    _ = (K^d)^(((p-1:ℕ):ℝ)/(p:ℝ)) := by
      rw [← Real.rpow_natCast_mul (by positivity : 0 ≤ K^d)]
      congr 1
      ring
    _ ≤ (K^d)^(1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hK)
      rw [div_le_one hp0]
      exact_mod_cast Nat.sub_le p 1
    _ = _ := Real.rpow_one _

lemma normalized_weighted_selection {d m p N : ℕ} (ν : Fin N → Measure (Space d))
    [∀ w, IsFiniteMeasure (ν w)] (hp : 2 ≤ p) (hm : 1 ≤ m) (hmd : m ≤ d)
    {β K : ℝ} (hK : 1 ≤ K) (hgap : (m:ℝ)+(p:ℝ)-2 < β)
    (hJ : ∀ j : ℕ, j ≤ p-2 → J β m j ≤ K^d)
    (hball : ∀ w, AmbientBallBound (ν w) 1 β)
    (hsupport : ∀ w, (ν w).support ⊆ Metric.closedBall 0 1)
    (g : Fin N → ((Fin m → Space d) × (Fin m → ℝ)) → ℝ≥0∞)
    (hg : ∀ w, Measurable (g w)) (hgsum : ∀ x, ∑ w, g w x ≤ 1) :
    (∑ w, ∫⁻ x, g w x ∂projectionLaw (ν w) m) ≤
      ENNReal.ofReal (K*192)^d * (N:ℝ≥0∞)^(1/(p:ℝ)) := by
  classical
  obtain ⟨D,hD,hDs,hDV⟩ := exists_projection_support (E := Space d) m (by simpa using hmd)
  have hg1 (w) (x) : g w x ≤ 1 :=
    (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ w)).trans (hgsum x)
  have hpoint (w) : (∫⁻ x, g w x ∂projectionLaw (ν w) m) ≤
      ENNReal.ofReal (K^d) * (∫⁻ x in D, g w x ∂matrixLabelReference m)^(1-1/(p:ℝ)) := by
    obtain ⟨F,hF,hF0,hden,_,hnorm⟩ := exact_finite_density d m p hp hm β 1 1 hgap
      (by norm_num) (by norm_num) 0 (ν w) (hsupport w) (hball w)
    have hFD : ∀ᵐ x ∂matrixLabelReference m, x ∉ D → F x = 0 := by
      have hz : projectionLaw (ν w) m Dᶜ = 0 := by
        rw [← compl_mem_ae_iff, compl_compl]
        unfold projectionLaw
        apply (ae_map_iff (by fun_prop) hD).2
        filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ν w).support_mem_ae] with x hx
        exact hDs x.1 x.2 (by simpa using hsupport w hx)
      change (matrixLabelReference m).withDensity _ = projectionLaw (ν w) m at hden
      rw [← hden, withDensity_apply _ hD.compl] at hz
      have ha := (lintegral_eq_zero_iff' hF.ennreal_ofReal.aemeasurable).mp hz
      change ∀ᵐ x ∂(matrixLabelReference m).restrict Dᶜ, ENNReal.ofReal (F x) = 0 at ha
      rw [ae_restrict_iff' hD.compl] at ha
      filter_upwards [ha] with x hx hnot
      exact le_antisymm (ENNReal.ofReal_eq_zero.mp (hx hnot)) (hF0 x)
    have hn : eLpNorm F (p:ℝ≥0∞) (matrixLabelReference m) ≤ ENNReal.ofReal (K^d) :=
      hnorm.trans (ENNReal.ofReal_le_ofReal (normalized_scale_le hp hK hgap hJ))
    have ht := density_test_bound (matrixLabelReference m) F hF hF0 p hp
      (ENNReal.ofReal (K^d)) hn D hD hFD (g w) (hg w).aemeasurable (hg1 w)
    change (matrixLabelReference m).withDensity _ = projectionLaw (ν w) m at hden
    rwa [hden] at ht
  have hq0 : 0 ≤ 1-1/(p:ℝ) := by
    have hp1 : (1:ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
    linarith [one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hp1]
  have hsum : (∑ w, ∫⁻ x in D, g w x ∂matrixLabelReference m) ≤
      matrixLabelReference (E := Space d) m D := by
    rw [← lintegral_finsetSum _ (fun w _ => hg w)]
    simpa using lintegral_mono (μ := (matrixLabelReference (E := Space d) m).restrict D) hgsum
  have hv : (matrixLabelReference (E := Space d) m D)^(1-1/(p:ℝ)) ≤ (192:ℝ≥0∞)^d := by
    calc
      _ ≤ ((192:ℝ≥0∞)^d)^(1-1/(p:ℝ)) := ENNReal.rpow_le_rpow (by simpa using hDV) hq0
      _ ≤ ((192:ℝ≥0∞)^d)^(1:ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (sub_le_self _ (by positivity))
      _ = _ := ENNReal.rpow_one _
  calc
    _ ≤ ∑ w, ENNReal.ofReal (K^d) * (∫⁻ x in D, g w x ∂matrixLabelReference m)^(1-1/(p:ℝ)) :=
      Finset.sum_le_sum (fun w _ => hpoint w)
    _ = ENNReal.ofReal (K^d) * ∑ w, (∫⁻ x in D, g w x ∂matrixLabelReference m)^(1-1/(p:ℝ)) := by rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal (K^d) * ((N:ℝ≥0∞)^(1/(p:ℝ)) *
        (∑ w, ∫⁻ x in D, g w x ∂matrixLabelReference m)^(1-1/(p:ℝ))) := by
      apply mul_le_mul' le_rfl
      simpa using finite_rpow_holder (fun w => ∫⁻ x in D, g w x ∂matrixLabelReference m)
        (by exact_mod_cast (by omega : 1 < p))
    _ ≤ ENNReal.ofReal (K^d) * ((N:ℝ≥0∞)^(1/(p:ℝ)) * (192:ℝ≥0∞)^d) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl ((ENNReal.rpow_le_rpow hsum hq0).trans hv))
    _ = _ := by
      rw [ENNReal.ofReal_pow (by linarith : 0 ≤ K), mul_left_comm, ← mul_pow,
        ENNReal.ofReal_mul (by linarith : 0 ≤ K)]
      norm_num
      ring
lemma localized_weighted_selection {d m p N : ℕ} (ν : Fin N → Measure (Space d))
    [∀ w, IsFiniteMeasure (ν w)] (hp : 2 ≤ p) (hm : 1 ≤ m) (hmd : m ≤ d)
    {β K H : ℝ} (hK : 1 ≤ K) (hH : 0 < H) (hgap : (m:ℝ)+(p:ℝ)-2 < β)
    (hJ : ∀ j : ℕ, j ≤ p-2 → J β m j ≤ K^d)
    (hball : ∀ w, AmbientBallBound (ν w) H β)
    (g : Fin N → ((Fin m → Space d) × (Fin m → ℝ)) → ℝ≥0∞)
    (hg : ∀ w, Measurable (g w)) (hgsum : ∀ x, ∑ w, g w x ≤ 1)
    (z : Space d) {r : ℝ} (hr : 0 < r) :
    (∑ w, ∫⁻ x, g w x ∂projectionLaw ((ν w).restrict (Metric.closedBall z r)) m) ≤
      ENNReal.ofReal ((K*192)^d * (N:ℝ)^(1/(p:ℝ)) * H * r^β) := by
  let τ w := realNormalize (ν w) β H z r
  let (w : Fin N) : IsFiniteMeasure (τ w) := realNormalize_finite (ν w) hH z hr
  let F : ((Fin m → Space d) × (Fin m → ℝ)) → ((Fin m → Space d) × (Fin m → ℝ)) :=
    fun x => (x.1, fun i => ⟪z,x.1 i⟫ + r*x.2 i)
  have hF : Measurable F := by fun_prop
  have hb := normalized_weighted_selection τ hp hm hmd hK hgap hJ
    (fun w => realNormalize_local (hball w) hH z hr)
    (fun w => realNormalize_support (ν w) β H z hr)
    (fun w => g w ∘ F) (fun w => (hg w).comp hF) (fun x => hgsum (F x))
  have he (w) : (∫⁻ x, g w x ∂projectionLaw ((ν w).restrict (Metric.closedBall z r)) m) =
      ENNReal.ofReal (H*r^β) * ∫⁻ x, g w (F x) ∂projectionLaw (τ w) m := by
    rw [← realNormalize_reconstruct (ν w) (β := β) hH z hr, projectionLaw_smul,
      projectionLaw_affine, lintegral_smul_measure, smul_eq_mul, lintegral_map (hg w) hF]
  simp_rw [he]
  rw [← Finset.mul_sum]
  refine (mul_le_mul' le_rfl hb).trans_eq ?_
  rw [← ENNReal.ofReal_natCast N, ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) (by positivity),
    ← ENNReal.ofReal_pow (by positivity : 0 ≤ K*192),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (K*192)^d),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ H*r^β)]
  congr 1
  ring

end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_CubeBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

lemma cube_J_bound {d k : ℕ} (hd : 16 ≤ d) (hk : k ≤ (d/2)/4) :
    ∀ j : ℕ, j ≤ (d/2)/4-2 → J (3*(d/2:ℕ)/4:ℝ) k j ≤ (7:ℝ)^d := by
  have hp2 : 2 ≤ (d/2)/4 := by omega
  have hn4 : (((d/2)/4:ℕ):ℝ)*4 ≤ (d/2:ℕ) := by exact_mod_cast Nat.div_mul_le_self (d/2) 4
  have hn : ((d/2:ℕ):ℝ) ≤ d := by exact_mod_cast Nat.div_le_self d 2
  have hm : (k:ℝ) ≤ ((d/2)/4:ℕ) := by exact_mod_cast hk
  intro j hj
  have hj' : (j:ℝ)+2 ≤ ((d/2)/4:ℕ) := by exact_mod_cast (show j+2 ≤ (d/2)/4 by omega)
  have hgap : 0 < (3*(d/2:ℕ)/4:ℝ)-(j:ℝ)-(k:ℝ) := by linarith
  have hquot : (k:ℝ)/((3*(d/2:ℕ)/4:ℝ)-(j:ℝ)-(k:ℝ)) ≤ 1 := by
    rw [div_le_one hgap]
    linarith
  have h3 : (3:ℝ)^j ≤ (3:ℝ)^d := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (2:ℝ)^(3*(d/2:ℕ)/4:ℝ) ≤ (2:ℝ)^d := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  calc
    J (3*(d/2:ℕ)/4:ℝ) k j = 1+(3:ℝ)^j*(2:ℝ)^(3*(d/2:ℕ)/4:ℝ)*
      ((k:ℝ)/((3*(d/2:ℕ)/4:ℝ)-(j:ℝ)-(k:ℝ))) := by unfold J; ring
    _ ≤ 1+(3:ℝ)^j*(2:ℝ)^(3*(d/2:ℕ)/4:ℝ)*1 := by gcongr
    _ ≤ 1+(3:ℝ)^d*(2:ℝ)^d := by rw [mul_one]; gcongr
    _ = 1+(6:ℝ)^d := by rw [← mul_pow]; norm_num
    _ ≤ (7:ℝ)^d := by
      simpa only [one_pow, show (1:ℝ)+6=7 by norm_num] using
        pow_add_pow_le (show (0:ℝ) ≤ 1 by norm_num) (show (0:ℝ) ≤ 6 by norm_num) (show d ≠ 0 by omega)

lemma cube_weighted_ambient {d : ℕ} (hd : 2 ≤ d) {f : Cube d → ℝ≥0∞}
    {L : ℝ} (hf : CubeLocal f L) :
    AmbientBallBound (((CubeLaw d).withDensity f).map (CubeEmbedding d)) L (3*(d/2:ℕ)/4:ℝ) := by
  intro x r hr
  rw [weighted_image_ball _ (cubeEmbedding_measurable d)]
  apply (lintegral_mono_set (show {u | dist (CubeEmbedding d u) x ≤ r} ⊆
    CubeBall d (Real.sqrt (d/2:ℕ) • cubeProject d x) r from ?_)).trans
    (hf _ _ hr)
  intro u hu
  exact (cubeProject_parameter_dist hd u x).trans
    (mul_le_mul_of_nonneg_left hu (Real.sqrt_nonneg _))

lemma cubeBall_embedding_subset {d : ℕ} (hd : 2 ≤ d) (z : Space (d/2)) {r : ℝ}
    (u₀ : Cube d) (hu₀ : u₀ ∈ CubeBall d z r) :
    CubeBall d z r ⊆ CubeEmbedding d ⁻¹' Metric.closedBall (CubeEmbedding d u₀) (4*r) := by
  have hs : 0 < Real.sqrt (d/2:ℕ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < d/2 by omega))
  intro u hu
  have hu' : dist u.val z ≤ Real.sqrt (d/2:ℕ)*r := hu
  have hu₀' : dist u₀.val z ≤ Real.sqrt (d/2:ℕ)*r := hu₀
  have hab : dist u.val u₀.val ≤ 2*Real.sqrt (d/2:ℕ)*r := by
    have := dist_triangle u.val z u₀.val
    rw [dist_comm z u₀.val] at this
    linarith
  apply (cubeEmbedding_dist hd u u₀).trans
  calc
    _ ≤ 2/Real.sqrt (d/2:ℕ)*(2*Real.sqrt (d/2:ℕ)*r) :=
      mul_le_mul_of_nonneg_left hab (by positivity)
    _ = 4*r := by field_simp [ne_of_gt hs]; ring

lemma weightedBlock_le_sum {X : Type*} {d m N : ℕ}
    (ι : X → Space d) (f : Fin N → X → ℝ≥0∞)
    {g : Fin N → ((Fin m → Space d) × (Fin m → ℝ)) → ℝ≥0∞}
    (hg : ∀ x, ∑ w, g w x ≤ 1) (x : X) : WeightedBlock ι f g x ≤ ∑ w, f w x := by
  unfold WeightedBlock
  calc
    _ ≤ ∫⁻ _A : Fin m → Space d, (∑ w, f w x) ∂Measure.pi (fun _ => stdGaussian (Space d)) := by
      apply lintegral_mono
      intro A
      apply Finset.sum_le_sum
      intro w _
      exact mul_le_of_le_one_left' ((Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ w)).trans (hg _))
    _ = _ := by simp

def CubeBlockConstant : ℝ := 4*1344^3
lemma cubeBlockConstant_one : 1 ≤ CubeBlockConstant := by norm_num [CubeBlockConstant]

lemma cube_constant_scale {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) :
    (1344:ℝ)^d * (4*r)^(3*(d/2:ℕ)/4:ℝ) ≤ CubeBlockConstant^(d/2) * r^(3*(d/2:ℕ)/4:ℝ) := by
  rw [Real.mul_rpow (by norm_num) hr.le]
  have hp : (1344:ℝ)^d ≤ (1344^3:ℝ)^(d/2) := by
    rw [← pow_mul]
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have h4 : (4:ℝ)^(3*(d/2:ℕ)/4:ℝ) ≤ (4:ℝ)^(d/2) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have := Nat.cast_nonneg (α := ℝ) (d/2)
    linarith
  calc
    _ = ((1344:ℝ)^d*(4:ℝ)^(3*(d/2:ℕ)/4:ℝ))*r^(3*(d/2:ℕ)/4:ℝ) := by ring
    _ ≤ ((1344^3:ℝ)^(d/2)*(4:ℝ)^(d/2))*r^(3*(d/2:ℕ)/4:ℝ) := by gcongr
    _ = _ := by rw [← mul_pow]; congr 2; norm_num [CubeBlockConstant]

theorem cube_block : CubeBlockStatement := by
  refine ⟨CubeBlockConstant, cubeBlockConstant_one, ?_⟩
  intro d k N hd hk hkp hN L hL f hf hf1 hloc g hg hgs z r hr
  by_cases hL0 : L = 0
  · simp only [hL0, mul_zero, zero_mul, ENNReal.ofReal_zero]
    calc
      _ ≤ ∫⁻ u in CubeBall d z r, ∑ w, f w u ∂CubeLaw d :=
        lintegral_mono (weightedBlock_le_sum _ _ hgs)
      _ = ∑ w, ∫⁻ u in CubeBall d z r, f w u ∂CubeLaw d :=
        lintegral_finsetSum _ (fun w _ => hf w)
      _ ≤ ∑ _w : Fin N, ENNReal.ofReal (L*r^(3*(d/2:ℕ)/4:ℝ)) :=
        Finset.sum_le_sum (fun w _ => hloc w z r hr)
      _ = 0 := by simp [hL0]
  have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
  by_cases hempty : CubeBall d z r = ∅
  · simp [hempty]
  obtain ⟨u₀,hu₀⟩ := Set.nonempty_iff_ne_empty.mpr hempty
  let ν (w : Fin N) := ((CubeLaw d).withDensity (f w)).map (CubeEmbedding d)
  let (w : Fin N) : IsFiniteMeasure (ν w) := weighted_image_finite (CubeLaw d) (CubeEmbedding d) (f w) (hf1 w)
  have hν w : AmbientBallBound (ν w) L (3*(d/2:ℕ)/4:ℝ) := cube_weighted_ambient (by omega) (hloc w)
  have hp : 2 ≤ (d/2)/4 := by omega
  have hkd : k ≤ d := by omega
  have hgap : (k:ℝ)+(((d/2)/4:ℕ):ℝ)-2 < (3*(d/2:ℕ)/4:ℝ) := by
    have hp' : (((d/2)/4:ℕ):ℝ)*4 ≤ (d/2:ℕ) := by exact_mod_cast Nat.div_mul_le_self (d/2) 4
    have hk' : (k:ℝ) ≤ ((d/2)/4:ℕ) := by exact_mod_cast hkp
    have hn' : (8:ℝ) ≤ (d/2:ℕ) := by exact_mod_cast (show 8 ≤ d/2 by omega)
    linarith
  have hsel := localized_weighted_selection ν hp hk hkd (by norm_num : (1:ℝ) ≤ 7)
    hLpos hgap (cube_J_bound hd hkp) hν g hg hgs (CubeEmbedding d u₀) (by positivity : 0 < 4*r)
  have he := weightedBlock_mass_identity (CubeLaw d) (cubeEmbedding_measurable d) hf hf1 hg
    (show MeasurableSet (Metric.closedBall (CubeEmbedding d u₀) (4*r)) from Metric.isClosed_closedBall.measurableSet)
  apply (lintegral_mono_set (cubeBall_embedding_subset (by omega) z u₀ hu₀)).trans
  rw [he]
  apply hsel.trans (ENNReal.ofReal_le_ofReal ?_)
  have hscale := cube_constant_scale (d := d) (by omega) hr
  norm_num only [show (7:ℝ)*192=1344 by norm_num]
  calc
    _ = ((1344:ℝ)^d*(4*r)^(3*(d/2:ℕ)/4:ℝ))*((N:ℝ)^(1/(((d/2)/4:ℕ):ℝ))*L) := by ring
    _ ≤ (CubeBlockConstant^(d/2)*r^(3*(d/2:ℕ)/4:ℝ))*((N:ℝ)^(1/(((d/2)/4:ℕ):ℝ))*L) :=
      mul_le_mul_of_nonneg_right hscale (by positivity)
    _ = _ := by ring
end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_KernelModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel

namespace Policy
instance instIsProbabilityMeasureElemVectorSphereOutput {d M T : ℕ} (K : Policy d M T) (t : ℕ) (j : State M) :
    IsProbabilityMeasure (K.output t j) := K.output_probability t j

def Borel {d M T : ℕ} (K : Policy d M T) : Prop :=
  ∀ t j a, Measurable (fun obs => K.transition t j obs a)

end Policy
end MemoryPrecision.Kernel


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_CoefficientStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision

theorem coefficient_step : CoefficientStepStatement := by
  refine ⟨1344, by norm_num, ?_⟩
  intro d m N hd hm hmp hN α H hαlo hαhi hH h hh hh1 hb g hg hgsum z r hr
  have : NeZero d := ⟨by omega⟩
  have : IsProbabilityMeasure (SpherePrior d) :=
    (show IsProbabilityMeasure (NoiselessRegression.sphereLaw (E := Space d)) from inferInstance)
  let ν (w : Fin N) := ((SpherePrior d).withDensity (h w)).map Subtype.val
  let (w : Fin N) : IsFiniteMeasure (ν w) :=
    weighted_image_finite (SpherePrior d) Subtype.val (h w) (hh1 w)
  have hν (w) : AmbientBallBound (ν w) H α := by
    intro x ρ hρ
    rw [show ν w = ((SpherePrior d).withDensity (h w)).map Subtype.val from rfl,
      weighted_image_ball _ measurable_subtype_coe]
    exact hb w x ρ hρ
  have hp : 2 ≤ d/8 := by omega
  have hmd : m ≤ d := hmp.trans (Nat.div_le_self _ _)
  have hgap : (m:ℝ)+((d/8:ℕ):ℝ)-2 < α := by
    have hm' : (m:ℝ) ≤ (d/8:ℕ) := by exact_mod_cast hmp
    have hp' : ((d/8:ℕ):ℝ)*8 ≤ d := by exact_mod_cast Nat.div_mul_le_self d 8
    have hd' : (16:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hJ := fun j hj => (specialized_J_bound d m (d/8) hd rfl hm hmp α hαlo hαhi j hj).2.2
  have hsel := localized_weighted_selection ν hp hm hmd (by norm_num : (1:ℝ) ≤ 7)
    hH hgap hJ hν g hg hgsum z hr
  have he := weightedBlock_mass_identity (SpherePrior d) measurable_subtype_coe hh hh1 hg
    (show MeasurableSet (Metric.closedBall z r) from Metric.isClosed_closedBall.measurableSet)
  change (∫⁻ s in Subtype.val ⁻¹' Metric.closedBall z r,
    WeightedBlock Subtype.val h g s ∂SpherePrior d) ≤ _
  rw [he]
  convert hsel using 1
  norm_num [ν, mul_assoc]

end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_RealContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

def BlockCount (T p : ℕ) : ℕ := ⌈(T:ℝ)/(p:ℝ)⌉₊
@[simp] lemma blockCount_zero (p : ℕ) : BlockCount 0 p = 0 := by simp [BlockCount]

def StepConstant : ℝ := Classical.choose coefficient_step

def RealStep (d N : ℕ) : ℝ := StepConstant^d * (N:ℝ)^(1/((d/8:ℕ):ℝ))

end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_CubeContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression
def CubeStepConstant : ℝ := Classical.choose cube_block

def CubeStep (d N : ℕ) : ℝ := CubeStepConstant^(d/2) * (N:ℝ)^(1/(((d/2)/4:ℕ):ℝ))

end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_RadialMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

def GaussianAmplitude (m : ℕ) (δ : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi * δ^2)) ^ m

end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_BallAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

def BallAverage {m : ℕ} (ν : Measure (Space m)) (y : Space m) (r : ℝ) : ℝ :=
  (ν (Metric.ball y r)).toReal / (UnitBallVolume m * r^m)

end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_CubeArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision

def CubeSuccessConstant : ℝ := max 12 (2*CubeStepConstant*2^72)
end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.ProjectionMoments_Polar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open scoped ENNReal NNReal RealInnerProductSpace Topology MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

instance realMatrixMeasurableSpace (k : ℕ) : MeasurableSpace (Matrix (Fin k) (Fin k) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin k → Fin k → ℝ))
instance realMatrixBorelSpace (k : ℕ) : BorelSpace (Matrix (Fin k) (Fin k) ℝ) :=
  inferInstanceAs (BorelSpace (Fin k → Fin k → ℝ))

end

end ProjectionMoments

end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_CubeExperiment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

def CubeAmbient (d : ℕ) : Measure (Space d) := (CubeLaw d).map (CubeEmbedding d)
instance instIsProbabilityMeasureSpaceCubeAmbient (d : ℕ) : IsProbabilityMeasure (CubeAmbient d) :=
  Measure.isProbabilityMeasure_map (cubeEmbedding_measurable d).aemeasurable

end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_StochasticContinuation
attribute [-instance] _root_.OAI.MemoryPrecision.instIsProbabilityMeasureSpaceCubeAmbient _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression
section Stochastic
variable {J X : Type*} [Fintype J] {d : ℕ}

def stochRoute (δ : ℕ → J → (Space d × ℝ) → J → ℝ≥0∞) (n : ℕ) :
    (k : ℕ) → J → ((Fin k → Space d) × (Fin k → ℝ)) → J → ℝ≥0∞
  | 0, j, _, w => by classical exact if j = w then 1 else 0
  | k+1, j, x, w => ∑ a, δ (n+1) j (x.1 0,x.2 0) a *
      stochRoute δ (n+1) k a (Fin.tail x.1,Fin.tail x.2) w

def stochCont (δ : ℕ → J → (Space d × ℝ) → J → ℝ≥0∞)
    (w : ℕ → J → X → ℝ≥0∞) (ι : X → Space d) (n : ℕ) : ℕ → J → X → ℝ≥0∞
  | 0, j, s => w n j s
  | k+1, j, s => ∫⁻ x, ∑ a, δ (n+1) j (x,⟪ι s,x⟫) a *
      stochCont δ w ι (n+1) k a s ∂stdGaussian (Space d)

end Stochastic
end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_KernelEvaluation
attribute [-instance] _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
namespace Policy
variable {d M T : ℕ} (K : Policy d M T)

def marginal (n : ℕ) (j : State M) (obs : Vector d × ℝ) (a : State M) : ℝ≥0∞ :=
  ∑ b : Bool, K.transition n j obs (b,a)

section Evaluation
variable {X : Type*} [MeasurableSpace X]
variable (w : ℕ → State M → X → ℝ≥0∞) (ι : X → Vector d)

def cont (n : ℕ) : ℕ → State M → X → ℝ≥0∞
  | 0, j, s => w n j s
  | k+1, j, s => ∫⁻ x, ∑ a : Action M, K.transition (n+1) j (x,⟪ι s,x⟫) a *
      if a.1 then w (n+1) a.2 s else cont (n+1) k a.2 s ∂stdGaussian (Vector d)

end Evaluation
end Policy
end MemoryPrecision.Kernel


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_KernelCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
open MemoryPrecision NoiselessRegression
instance instIsProbabilityMeasureElemVectorSphereUniformSphereOfNeZeroNat {d : ℕ} [NeZero d] : IsProbabilityMeasure (UniformSphere d) :=
  (show IsProbabilityMeasure (NoiselessRegression.sphereLaw (E := Vector d)) from inferInstance)
instance instIsProbabilityMeasureRowsRowLaw (d T : ℕ) : IsProbabilityMeasure (RowLaw d T) := by unfold RowLaw; infer_instance

end MemoryPrecision.Kernel


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_KernelVersion
attribute [-instance] _root_.OAI.MemoryPrecision.Kernel.instIsProbabilityMeasureElemVectorSphereUniformSphereOfNeZeroNat _root_.OAI.MemoryPrecision.Kernel.instIsProbabilityMeasureRowsRowLaw _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
namespace Policy
variable {d M T : ℕ} (K : Policy d M T)
def versionCoordinates (hK : K.Completed) (t : ℕ) (j : State M)
    (obs : Vector d × ℝ) (a : Action M) : ℝ≥0∞ :=
  (hK t j a).mk (fun obs => K.transition t j obs a) obs

def version (hK : K.Completed) : Policy d M T where
  initial := K.initial
  initial_sum := K.initial_sum
  transition := fun t j obs a => if ∑ b, K.versionCoordinates hK t j obs b = 1
    then K.versionCoordinates hK t j obs a else if a = (false,0) then 1 else 0
  transition_sum := by
    intro t j obs
    split_ifs with h
    · exact h
    · simp
  output := K.output
  output_probability := K.output_probability

end Policy
end MemoryPrecision.Kernel


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_KernelAdmissibility
attribute [-instance] _root_.OAI.MemoryPrecision.Kernel.instIsProbabilityMeasureElemVectorSphereUniformSphereOfNeZeroNat _root_.OAI.MemoryPrecision.Kernel.instIsProbabilityMeasureRowsRowLaw _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
namespace Policy

def FixedSuccess {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (K : Ω → Policy d M T) (ρ : Measure Ω) (ε : ℝ) (s : Sphere d) : ℝ≥0∞ :=
  let rowMeasurable := @MeasurableSpace.pi (Fin T) (fun _ => Vector d)
    (fun _ => @WithLp.measurableSpace
      (@OfNat.ofNat ℝ≥0∞ 2
        (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance))
      (Fin d → ℝ) inferInstance)
  @lintegral (Ω × Rows d T)
    (@Prod.instMeasurableSpace Ω (Rows d T) inferInstance rowMeasurable)
    (@Measure.prod Ω (Rows d T) inferInstance rowMeasurable ρ (RowLaw d T))
    (fun z => experiment K (angleTest ε) (s,z))

end Policy
end MemoryPrecision.Kernel


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_SuccessArithmetic
attribute [-instance] _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision

def SuccessConstant : ℝ := 6*StepConstant

end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_StreamArithmetic
attribute [-instance] _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision

def StreamConstant : ℝ := 3*(SuccessConstant+21)

end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_KernelStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
open MemoryPrecision Policy

def SourceStreamStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, 0 < d₀ ∧
  ∀ d M T : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1/10 →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
  ∀ L : Ω → MemoryPrecision.Kernel.Policy d M T,
    MemoryPrecision.Kernel.Policy.Admissible L ρ (MemoryPrecision.Kernel.UniformSphere d) →
    MemoryPrecision.Kernel.Policy.Success L ρ (MemoryPrecision.Kernel.UniformSphere d) ε ≤ min 1 (ENNReal.ofReal
      ((2*ε*Real.exp (C*(1+(M:ℝ)/(d:ℝ)^2)*(MemoryPrecision.Kernel.BlockCount T ((d-1)/8):ℝ)))^(((d:ℝ)-1)/2)))

end MemoryPrecision.Kernel


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_CubeSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
open MemoryPrecision NoiselessRegression Policy

def CubeSuccessEstimate {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (D : ℝ) (hd : 2 ≤ d) (ε : ℝ) (K : Ω → Policy d M T) (ρ : Measure Ω) : Prop :=
  Policy.Success K ρ (CubePrior hd) ε ≤ min 1 (ENNReal.ofReal
    (D^((d/2)*(MemoryPrecision.Kernel.BlockCount T ((d/2)/4)+1)) * ε^((d/2:ℕ)/4:ℝ)))

def PointwisePrecisionEstimate {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (c ε : ℝ) (K : Ω → Policy d M T) (ρ : Measure Ω) : Prop :=
  (∀ signal : MemoryPrecision.Kernel.Sphere d,
      (@OfNat.ofNat ℝ≥0∞ 2
        (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance)) /
      (@OfNat.ofNat ℝ≥0∞ 3
        (@instOfNatAtLeastTwo ℝ≥0∞ 3 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance)) ≤
        Policy.FixedSuccess K ρ ε signal) → c*(d:ℝ)*Real.log (1/ε) ≤ (T:ℝ)

abbrev SourceCubeStatement : Prop :=
  ∃ D : ℝ, Real.exp 1 ≤ D ∧ ∃ d₀ : ℕ, ∃ hd₀ : 16 ≤ d₀, ∃ c : ℝ, 0 < c ∧
  ∀ d M T : ℕ, ∀ hd : d₀ ≤ d, M ≤ d^2 → ∀ ε : ℝ, 0 < ε → ε ≤ 1/10 →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
  ∀ K : Ω → MemoryPrecision.Kernel.Policy d M T, Policy.ModelAdmissible.{u} K ρ →
    CubeSuccessEstimate.{u} D (cubePrior_dimension hd₀ hd) ε K ρ ∧
    PointwisePrecisionEstimate.{u} c ε K ρ

end MemoryPrecision.Kernel


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_GaussianConvolution
attribute [-instance] _root_.OAI.MemoryPrecision.instIsProbabilityMeasureSpaceCubeAmbient _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

def GaussianConvolution {m : ℕ} (ν : Measure (Space m)) (δ : ℝ) (y : Space m) : ℝ :=
  ∫ x, GaussianKernel m δ (y-x) ∂ν

end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_LabelTranslations
attribute [-instance] _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
section Translation
variable {Ω Y : Type*}
  [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [R1Space Ω]
  [NormedAddCommGroup Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  (γ : Measure Ω) [SFinite γ] (τ : Measure Y) [SFinite τ] [τ.IsAddRightInvariant]

def labelTranslate (u : Y) : C(Ω × Y, Ω × Y) :=
  ⟨fun x => (x.1, x.2 + u), by fun_prop⟩

variable [(γ.prod τ).InnerRegularCompactLTTop] [IsLocallyFiniteMeasure (γ.prod τ)]

variable [NormedSpace ℝ Y]

def averageTranslate (κ : Measure Y) (δ : ℝ) (F : Ω × Y → ℝ) (x : Ω × Y) : ℝ :=
  ∫ u, F (x.1, x.2 + δ • u) ∂κ

end Translation
end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_SphericalProjection
attribute [-instance] _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

section RadialCoordinates
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def radialShrink (c : ℝ) (v : E) : E :=
  (Real.sqrt (‖v‖^2 + c^2))⁻¹ • v

def radialExpand (c : ℝ) (u : E) : E :=
  (c / Real.sqrt (1 - ⟪u,u⟫)) • u

end RadialCoordinates

end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_FiberDensity
attribute [-instance] _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

def PiGaussianConvolution {m : ℕ} (ν : Measure (Fin m → ℝ)) (δ : ℝ) (y : Fin m → ℝ) : ℝ :=
  ∫ x, ∏ j, gaussianPDFReal 0 ⟨δ^2,sq_nonneg δ⟩ (y j - x j) ∂ν

end MemoryPrecision


end

end OAI
end


