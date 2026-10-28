-- Prove2me | Definitions.Def_OAIQ6El002
-- name    : OAIQ6El002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T10:18:20.875463+00:00
-- url     : https://prove2.me/theorems/61d5b687-3873-43df-9482-06950114a429
-- title:
--   Definitions bundle OAIQ6El002 of the split of OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 107 declarations of OpenAI's Lean: 70 definitions, 3 instances and 34 theorems. The definitions and types are `OAI.ElasticityBoundaryTaylor.radialTaylor`, `OAI.ElasticityCompact.curryCompact`, `OAI.ElasticityCompact.flipLinear`, `OAI.ElasticityCompact.toLinfCompact`, `OAI.ElasticityCompact.zeroExtend`, `OAI.ElasticityConic.C3`, `OAI.ElasticityConic.Mat3`, `OAI.ElasticityConic.chartCoord`, `OAI.ElasticityConic.chartDiagonal`, `OAI.ElasticityConic.chartTheta`, `OAI.ElasticityConic.chartVector`, `OAI.ElasticityConic.chartZ₀`, `OAI.ElasticityConic.chartZ₁`, `OAI.ElasticityConic.conicChart`, `OAI.ElasticityConic.finiteCoordinates`, `OAI.ElasticityConic.finiteVector`, `OAI.ElasticityConic.h₁`, `OAI.ElasticityConic.h₂`, `OAI.ElasticityConic.null`, `OAI.ElasticityConic.theta`, `OAI.ElasticityCoordinates.linearPull`, `OAI.ElasticityCoordinates.planeSplit`, `OAI.ElasticityCoordinates.pullLp`, `OAI.ElasticityFiniteType.coordL`, `OAI.ElasticityFiniteType.d`, `OAI.ElasticityFiniteType.matrixCLM`, `OAI.ElasticityFiniteType.systemCLM`, `OAI.ElasticityFrame.Amp`, `OAI.ElasticityFrame.Fiber`, `OAI.ElasticityFrame.X`, `OAI.ElasticityFrame.connection`, `OAI.ElasticityFrame.fiber`, `OAI.ElasticityFrame.normal`, `OAI.ElasticityFrame.nullVector`, `OAI.ElasticityFrame.scalarPr`, `OAI.ElasticityFrame.scalarVector`, `OAI.ElasticityFrame.tangentProjection`, `OAI.ElasticityFrame.vectorPr`, `OAI.ElasticityGeneralSlicing.PL2`, `OAI.ElasticityGeneralSlicing.productTest` and 30 more.
--
--   **Sources.** They come from these modules of lean/OAI/MathematicalPhysics, in whole or in part: `Elasticity_BoundaryLayers`, `Elasticity_Compact`, `Elasticity_Conic`, `Elasticity_ForcedTransport`, `Elasticity_Homotopy`, `Elasticity_ODE`, `Elasticity_Planar`, `Elasticity_Recovery`, `Elasticity_Regularity`, `Elasticity_Rigidity`, `Elasticity_Smoothing`, `Elasticity_Solvability`, `Elasticity_Supported`, `Elasticity_Transport`, `Elasticity_WeakLimits`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ6El004` and `OAIQ6El005`; the statements `OAI.ElasticityAugmented.exists_physical_leading_frame`, `OAI_ElasticityBoundaryOrderBound_OrderBound_square_mass`, `OAI.ElasticityFrame.exists_constraint_columns`, `OAI.ElasticityFrame.exists_constraint_transport`, `OAI.ElasticityGeneralSlicing.cylinder_weak_slices`, `OAI.ElasticityGeneralSlicing.smooth_cylinder_representative`, `OAI.ElasticityGeneralSlicing.smooth_supported_of_cylinder`, `OAI_ElasticityPlanar_classical_parameter_smooth`, `OAI_ElasticityRegularity_exists_bounded_integer_multiplier`, `OAI.ElasticityRegularity.exists_localized_derivative` and `OAI.ElasticityRegularity.quantitative_cutoff_gain`; the proofs of `OAI_ElasticityBoundaryOrderBound_OrderBound_square_mass`, `OAI.ElasticityCoordinates.planar_smooth_representative`, `OAI.ElasticityFrame.exists_constraint_columns`, `OAI.ElasticityFrame.exists_constraint_transport`, `OAI.ElasticityGeneralSlicing.cylinder_weak_slices`, `OAI_ElasticityPlanar_exists_spatial_linear_frame`, `OAI_ElasticityRegularity_exists_bounded_integer_multiplier`, `OAI.ElasticityRegularity.exists_localized_derivative`, `OAI_ElasticityRegularity_laplacian_product_divergence` and `OAI.ElasticityRegularity.quantitative_cutoff_gain`.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/MathematicalPhysics at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryLayers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Uniform multivariable Taylor estimates for anisotropically rescaled boundary
layers. The constants are proved for actual smooth compactly supported physical
coefficient extensions; no symbol/asymptotic identification is assumed. -/
noncomputable section
open Set
open scoped BigOperators
namespace ElasticityBoundaryTaylor
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def radialTaylor (f : E → F) (n : ℕ) (z : E) : F :=
  ∑ k ∈ Finset.range (n+1), (k.factorial : ℝ)⁻¹ •
    iteratedFDeriv ℝ k f 0 (fun _ => z)

end ElasticityBoundaryTaylor

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter Topology
namespace ElasticityCompact
variable {A P F : Type*} [TopologicalSpace A] [CompactSpace A]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Interchanging a compact continuous-variable slot and a bounded linear slot. -/
def flipLinear (q : C(A,P →L[ℝ] F)) : P →L[ℝ] C(A,F) :=
  LinearMap.mkContinuous
    ({ toFun := fun p => ⟨fun a => q a p,q.continuous.clm_apply continuous_const⟩
       map_add' := fun v w => by ext a; exact map_add (q a) v w
       map_smul' := fun c v => by ext a; exact map_smul (q a) c v } : P →ₗ[ℝ] C(A,F))
    ‖q‖ (fun p => by
      change ‖(⟨fun a => q a p,q.continuous.clm_apply continuous_const⟩ : C(A,F))‖ ≤ ‖q‖ * ‖p‖
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg q) (norm_nonneg p))).mpr
      intro a
      exact (q a).le_opNorm p |>.trans (mul_le_mul_of_nonneg_right
        (q.norm_coe_le_norm a) (norm_nonneg p)))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def curryCompact (f : P × E → F) (hf : Continuous f) (j : A → E) (hj : Continuous j) :
    P → C(A,F) :=
  fun p => ⟨fun a => f (p,j a),hf.comp (continuous_const.prodMk hj)⟩
end ElasticityCompact

end
end
section
noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal
namespace ElasticityCompact
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {S : Set E} [CompactSpace S]
def zeroExtend (f : C(S,ℂ)) : E → ℂ := Function.extend Subtype.val f 0
omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompactSpace S] in
lemma zeroExtend_mem (f : C(S,ℂ)) (x : S) : zeroExtend f x=f x :=
  Subtype.val_injective.extend_apply f 0 x
omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompactSpace S] in
lemma zeroExtend_notMem (f : C(S,ℂ)) {x : E} (hx : x∉S) : zeroExtend f x=0 := by
  apply Function.extend_apply'
  rintro ⟨y,rfl⟩
  exact hx y.property
omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma zeroExtend_norm (f : C(S,ℂ)) (x : E) : ‖zeroExtend f x‖ ≤ ‖f‖ := by
  by_cases hx : x∈S
  · exact (zeroExtend_mem f ⟨x,hx⟩) ▸ f.norm_coe_le_norm ⟨x,hx⟩
  · rw [zeroExtend_notMem f hx,norm_zero]; exact norm_nonneg _
omit [NormedSpace ℝ E] in
lemma zeroExtend_memLp (hS : MeasurableSet S) (μ : Measure E) (f : C(S,ℂ)) :
    MemLp (zeroExtend f) ∞ μ := by
  apply memLp_top_of_bound _ ‖f‖ (Eventually.of_forall (zeroExtend_norm f))
  exact ((MeasurableEmbedding.subtype_coe hS).stronglyMeasurable_extend
    f.continuous.stronglyMeasurable stronglyMeasurable_const).aestronglyMeasurable
omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompactSpace S] in
lemma zeroExtend_add (f g : C(S,ℂ)) : zeroExtend (f+g)=zeroExtend f+zeroExtend g := by
  funext x
  by_cases hx : x∈S
  · change zeroExtend (f+g) (⟨x,hx⟩ : S)=zeroExtend f (⟨x,hx⟩ : S)+zeroExtend g (⟨x,hx⟩ : S)
    rw [zeroExtend_mem (f+g) ⟨x,hx⟩,zeroExtend_mem f ⟨x,hx⟩,zeroExtend_mem g ⟨x,hx⟩]
    rfl
  · simp only [Pi.add_apply,zeroExtend_notMem _ hx,add_zero]
omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompactSpace S] in
lemma zeroExtend_smul (c : ℂ) (f : C(S,ℂ)) : zeroExtend (c • f)=c • zeroExtend f := by
  funext x
  by_cases hx : x∈S
  · change zeroExtend (c • f) (⟨x,hx⟩ : S)=c • zeroExtend f (⟨x,hx⟩ : S)
    rw [zeroExtend_mem (c • f) ⟨x,hx⟩,zeroExtend_mem f ⟨x,hx⟩]
    rfl
  · simp only [Pi.smul_apply,zeroExtend_notMem _ hx,smul_zero]
def toLinfCompact (hS : MeasurableSet S) (μ : Measure E) : C(S,ℂ) →L[ℂ] Lp ℂ ∞ μ :=
  LinearMap.mkContinuous
    ({ toFun := fun f => (zeroExtend_memLp hS μ f).toLp (zeroExtend f)
       map_add' := fun f g => by
         apply Lp.ext
         filter_upwards [MemLp.coeFn_toLp (zeroExtend_memLp hS μ (f+g)),
           MemLp.coeFn_toLp (zeroExtend_memLp hS μ f),MemLp.coeFn_toLp (zeroExtend_memLp hS μ g),
           Lp.coeFn_add ((zeroExtend_memLp hS μ f).toLp _) ((zeroExtend_memLp hS μ g).toLp _)] with x ha hb hc hd
         rw [ha,hd]
         simp only [Pi.add_apply,hb,hc,zeroExtend_add]
       map_smul' := fun c f => by
         apply Lp.ext
         filter_upwards [MemLp.coeFn_toLp (zeroExtend_memLp hS μ (c • f)),
           MemLp.coeFn_toLp (zeroExtend_memLp hS μ f),
           Lp.coeFn_smul c ((zeroExtend_memLp hS μ f).toLp _)] with x ha hb hc
         simp only [RingHom.id_apply]
         rw [ha,hc]
         simp only [Pi.smul_apply,hb,zeroExtend_smul] } : C(S,ℂ) →ₗ[ℂ] Lp ℂ ∞ μ) 1 (fun f => by
      rw [one_mul]
      change ‖(zeroExtend_memLp hS μ f).toLp (zeroExtend f)‖ ≤ ‖f‖
      rw [Lp.norm_toLp]
      have h := eLpNorm_le_of_ae_bound (p := ∞) (μ := μ)
        (Eventually.of_forall (zeroExtend_norm f))
      simp only [ENNReal.toReal_top,inv_zero,ENNReal.rpow_zero,one_mul] at h
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq
        (ENNReal.toReal_ofReal (norm_nonneg f)))
end ElasticityCompact

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_ODE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace ElasticityODE
abbrev Time := Icc (0:ℝ) 1
instance instFactLeRealOfNat_solutions : Fact ((0:ℝ) ≤ 1) := ⟨zero_le_one⟩
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def extend (f : C(Time,F)) : C(ℝ,F) := ContinuousMap.IccExtendCM f
omit [NormedSpace ℝ F] [CompleteSpace F] in
lemma extend_norm_le (f : C(Time,F)) (t : ℝ) : ‖extend f t‖ ≤ ‖f‖ :=
  f.norm_coe_le_norm _

lemma weighted_continuous (k : ℝ) (f : C(Time,F)) :
    Continuous (fun t : ℝ => Real.exp (-k*t) • ∫ s in (0:ℝ)..t, Real.exp (k*s) • extend f s) := by
  have hc : Continuous (fun s : ℝ => Real.exp (k*s) • extend f s) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul (extend f).continuous
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    (intervalIntegral.differentiable_integral_of_continuous hc).continuous

def weighted (k : ℝ) (f : C(Time,F)) : C(Time,F) :=
  ⟨fun t => Real.exp (-k*(t:ℝ)) • ∫ s in (0:ℝ)..(t:ℝ), Real.exp (k*s) • extend f s,
    (weighted_continuous k f).comp continuous_subtype_val⟩

lemma integral_exp_mul (k t : ℝ) (hk : k ≠ 0) :
    ∫ s in (0:ℝ)..t, Real.exp (k*s)=(Real.exp (k*t)-1)/k := by
  have hd (s : ℝ) : HasDerivAt (fun s => Real.exp (k*s)/k) (Real.exp (k*s)) s := by
    convert ((Real.hasDerivAt_exp (k*s)).comp s ((hasDerivAt_id s).const_mul k)).div_const k using 1 <;> first | rfl | simp [hk]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 t)
  simpa only [mul_zero,Real.exp_zero,sub_div] using h

end ElasticityODE

end
end
section
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace ElasticityODE
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
def pointwise (b : C(Time,F →L[ℝ] F)) (f : C(Time,F)) : C(Time,F) :=
  ⟨fun t => b t (f t),b.continuous.clm_apply f.continuous⟩
omit [CompleteSpace F] in
lemma pointwise_bound (b : C(Time,F →L[ℝ] F)) (f : C(Time,F)) : ‖pointwise b f‖ ≤ ‖b‖*‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg b) (norm_nonneg f))).mpr
  intro t
  exact (b t).le_opNorm (f t) |>.trans (mul_le_mul (b.norm_coe_le_norm t)
    (f.norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg _))
omit [CompleteSpace F] in
def pointwiseLM : C(Time,F →L[ℝ] F) →ₗ[ℝ] (C(Time,F) →ₗ[ℝ] C(Time,F)) where
  toFun b :=
    { toFun := pointwise b
      map_add' := fun f g => by ext t; exact map_add (b t) (f t) (g t)
      map_smul' := fun c f => by ext t; exact map_smul (b t) c (f t) }
  map_add' b c := by ext f t; rfl
  map_smul' c b := by ext f t; rfl
omit [CompleteSpace F] in
def pointwiseCLM : C(Time,F →L[ℝ] F) →L[ℝ] (C(Time,F) →L[ℝ] C(Time,F)) :=
  LinearMap.mkContinuous₂ (σ₁₃ := RingHom.id ℝ) (σ₂₃ := RingHom.id ℝ)
    (pointwiseLM (F := F)) 1 (fun (b : C(Time,F →L[ℝ] F)) (f : C(Time,F)) => by
    change ‖pointwise b f‖ ≤ 1*‖b‖*‖f‖
    simpa only [one_mul] using pointwise_bound (F := F) b f)

omit [CompleteSpace F] in
def expScale (k : ℝ) : C(Time,F) →L[ℝ] C(Time,F) :=
  pointwiseCLM ⟨fun t => Real.exp (k*(t:ℝ)) • ContinuousLinearMap.id ℝ F,
    ((Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)).smul continuous_const)⟩
end ElasticityODE

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Regularity
attribute [-instance] _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Actual distributional elliptic regularity dependencies of the physical and
planar weak-limit constructions. No regularity assumption on an L2 unknown is
used in the gain of Sobolev order below. -/
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal
namespace ElasticityRegularity

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma schwartz_leibniz {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (m : E) (hd : (fun x => fderiv ℝ g x m).HasTemperateGrowth) (φ : 𝓢(E,ℂ)) :
    ∂_{m} (SchwartzMap.smulLeftCLM ℂ g φ) =
      SchwartzMap.smulLeftCLM ℂ (fun x => fderiv ℝ g x m) φ +
        SchwartzMap.smulLeftCLM ℂ g (∂_{m} φ) := by
  ext x
  simp only [add_apply,SchwartzMap.smulLeftCLM_apply_apply hd,
    SchwartzMap.smulLeftCLM_apply_apply hg,SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.smulLeftCLM_apply hg]
  change fderiv ℝ (g*(φ : E → ℂ)) x m =
    fderiv ℝ g x m*φ x+g x*fderiv ℝ (φ : E → ℂ) x m
  rw [fderiv_mul (hg.1.differentiable (by simp) x) φ.differentiableAt]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

omit [CompleteSpace F] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma distribution_leibniz {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (m : E) (hd : (fun x => fderiv ℝ g x m).HasTemperateGrowth) (u : 𝓢'(E,F)) :
    ∂_{m} (smulLeftCLM F g u) =
      smulLeftCLM F (fun x => fderiv ℝ g x m) u+smulLeftCLM F g (∂_{m} u) := by
  ext φ
  simp only [lineDerivOp_apply_apply,smulLeftCLM_apply_apply,add_apply,
    schwartz_leibniz hg m hd,map_neg,map_add]
  abel

lemma compact_bounded_multiplier {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) : MemLp g ∞ (volume : Measure E) := by
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuousOn hg.continuous.continuousOn
  refine memLp_top_of_bound hg.continuous.aestronglyMeasurable (max C 0)
    (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ tsupport g
  · exact (hC x hx).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx,norm_zero]
    exact le_max_right _ _

end ElasticityRegularity

open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators

open scoped SchwartzMap LineDeriv BigOperators
open scoped SchwartzMap LineDeriv Laplacian BigOperators

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Solvability
attribute [-instance] _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The Hahn--Banach / Riesz step used by the physical solvability argument.
This proves the functional-analytic implication, rather than postulating
existence of a right inverse. The physical test estimate is proved separately. -/

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
namespace ElasticityPhysicalDual

def adjPhase (z : Fin 3 → ℂ) (i : Fin 3) : ℂ := -star (z i)

end ElasticityPhysicalDual

open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators
open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv

open scoped BigOperators

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Planar
attribute [-instance] _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityPlanar
open MeasureTheory Complex

def testSubmodule : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f}
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f at hf
    change ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g at hg
    exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  zero_mem' := by
    exact ⟨contDiff_const (c := (0 : ℂ)), HasCompactSupport.zero⟩
  smul_mem' := by
    intro a f hf
    change ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f at hf
    constructor
    · exact hf.1.const_smul a
    · change HasCompactSupport (fun z => a * f z)
      exact hf.2.mul_left

abbrev Test := testSubmodule

instance instCoeFunSubtypeForallComplexMemSubmoduleTest : CoeFun Test (fun _ => ℂ → ℂ) := ⟨fun f => f.val⟩

lemma smooth (f : Test) : ContDiff ℝ (⊤ : ℕ∞) (f : ℂ → ℂ) := f.property.1
lemma compact (f : Test) : HasCompactSupport (f : ℂ → ℂ) := f.property.2

def d (v : ℂ) : Test →ₗ[ℂ] Test where
  toFun f := ⟨fun z => fderiv ℝ (f : ℂ → ℂ) z v, by
    constructor
    · exact ((smooth f).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
    · exact (compact f).fderiv_apply ℝ v⟩
  map_add' f g := by
    apply Subtype.ext
    funext z
    exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v)
      (fderiv_add ((smooth f).differentiable (by simp) z)
        ((smooth g).differentiable (by simp) z))
  map_smul' a f := by
    apply Subtype.ext
    funext z
    exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v)
      (fderiv_const_smul ((smooth f).differentiable (by simp) z) a)

@[simp] lemma d_apply (v : ℂ) (f : Test) (z : ℂ) :
    (d v f : ℂ → ℂ) z = fderiv ℝ (f : ℂ → ℂ) z v := rfl

def mulSmooth (a : ℂ → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a) : Test →ₗ[ℂ] Test where
  toFun f := ⟨fun z => a z * f z, ⟨ha.mul (smooth f), (compact f).mul_left⟩⟩
  map_add' f g := by
    apply Subtype.ext
    funext z
    exact mul_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext z
    change a z * (c * f z) = c * (a z * f z)
    ring

def Z : Test →ₗ[ℂ] Test := mulSmooth id contDiff_id
def Zbar : Test →ₗ[ℂ] Test := mulSmooth star Complex.conjCLE.contDiff

@[simp] lemma Z_apply (f : Test) (z : ℂ) : (Z f : ℂ → ℂ) z = z * f z := rfl
@[simp] lemma Zbar_apply (f : Test) (z : ℂ) : (Zbar f : ℂ → ℂ) z = star z * f z := rfl

def gaussian (t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (((t : ℂ) / 2) * (z * star z))

lemma smooth_gaussian (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (gaussian t) := by
  exact (contDiff_const.mul (contDiff_id.mul Complex.conjCLE.contDiff)).cexp

def W (t : ℝ) : Test →ₗ[ℂ] Test := mulSmooth (gaussian t) (smooth_gaussian t)

@[simp] lemma W_apply (t : ℝ) (f : Test) (z : ℂ) :
    (W t f : ℂ → ℂ) z = gaussian t z * f z := rfl

open scoped BigOperators

end ElasticityPlanar
namespace ElasticityPlanar
open MeasureTheory Complex Set
open scoped SchwartzMap ENNReal BigOperators

def toSchwartz : Test →ₗ[ℂ] 𝓢(ℂ,ℂ) where
  toFun f := (compact f).toSchwartzMap (smooth f)
  map_add' _ _ := by ext z; rfl
  map_smul' _ _ := by ext z; rfl
@[simp] lemma toSchwartz_apply (f : Test) (z : ℂ) : toSchwartz f z=f z := rfl

def L2 : Test →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℂ)).toLinearMap.comp toSchwartz

def cj (f : Test) : Test := ⟨fun z => star (f z),
  ⟨Complex.conjCLE.contDiff.comp (smooth f),(compact f).comp_left (star_zero ℂ)⟩⟩
@[simp] lemma cj_apply (f : Test) (z : ℂ) : cj f z=star (f z) := rfl
@[simp] lemma cj_cj (f : Test) : cj (cj f)=f := by ext z; simp

variable {n : Type*}
abbrev Hilbert (n : Type*) := PiLp 2 (fun _ : n => Lp ℂ 2 (volume : Measure ℂ))
def embed : (n → Test) →ₗ[ℂ] Hilbert n where
  toFun u := WithLp.toLp 2 (fun i => L2 (u i))
  map_add' _ _ := by apply PiLp.ext; intro i; exact map_add L2 _ _
  map_smul' _ _ := by apply PiLp.ext; intro i; exact map_smul L2 _ _
@[simp] lemma embed_apply (u : n → Test) (i : n) : embed u i = L2 (u i) := rfl
end ElasticityPlanar
section
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv
namespace ElasticityRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- H^s is represented isometrically by L2 via J^{-s}; its injection is into the
actual space of tempered distributions. -/
def sobolevInjection (s : ℝ) : Lp ℂ 2 (volume : Measure E) →L[ℂ] 𝓢'(E,ℂ) :=
  (besselPotential E ℂ (-s)).comp (Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2)

end ElasticityRegularity

end

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Homotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
namespace ElasticityODE
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
def coefficientDbar (b : ℂ → C(Time,R)) (p : ℂ) : C(Time,R) :=
  fderiv ℝ b p 1+Complex.I • fderiv ℝ b p Complex.I
end ElasticityODE

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Transport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityParameter
open scoped BigOperators InnerProductSpace

abbrev X := EuclideanSpace ℝ (Fin 3)
def basis (i : Fin 3) : X := EuclideanSpace.single i 1
end ElasticityParameter
namespace ElasticityFrame
open Set Complex Module
open scoped BigOperators
abbrev X := EuclideanSpace ℝ (Fin 3)
abbrev Amp := (Fin 3 → ℂ) × ℂ

def normal (θ : Fin 3 → ℂ) : Amp →ₗ[ℂ] ℂ where
  toFun v := ∑ i, θ i*v.1 i
  map_add' v w := by simp only [Prod.fst_add,Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Prod.smul_fst,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
def fiber (θ : Fin 3 → ℂ) : Submodule ℂ Amp := (normal θ).ker
abbrev Fiber (θ : Fin 3 → ℂ) := ↥(fiber θ)

def scalarVector (θ : Fin 3 → ℂ) : Fiber θ := ⟨(0,1),by simp [fiber,normal,LinearMap.mem_ker]⟩
def nullVector (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) : Fiber θ := ⟨(θ,0),hθ⟩
def scalarPr (θ : Fin 3 → ℂ) : Fiber θ →L[ℂ] ℂ :=
  (ContinuousLinearMap.snd ℂ (Fin 3 → ℂ) ℂ).comp (fiber θ).subtypeL
def vectorPr (θ : Fin 3 → ℂ) (i : Fin 3) : Fiber θ →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj i).comp ((ContinuousLinearMap.fst ℂ (Fin 3 → ℂ) ℂ).comp (fiber θ).subtypeL)
def connection (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (t : ℂ) (q : Fin 3 → ℂ) :
    Fiber θ →L[ℂ] Fiber θ :=
  (scalarPr θ).smulRight (nullVector θ hθ)+
    t • (scalarPr θ).smulRight (scalarVector θ)+
      ∑ i, q i • (vectorPr θ i).smulRight (scalarVector θ)

end ElasticityFrame

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_ForcedTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace ElasticityFrame

def tangentProjection (θ n : Fin 3 → ℂ) (hn : ∑ i,θ i*n i=1) : Amp →ₗ[ℂ] Fiber θ :=
  (LinearMap.id-(normal θ).smulRight (n,0)).codRestrict (fiber θ) (by
    intro v
    change normal θ (v-normal θ v • (n,0))=0
    rw [map_sub,map_smul]
    have he : normal θ (n,0)=1 := hn
    rw [he,smul_eq_mul,mul_one,sub_self])
end ElasticityFrame

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Recovery
attribute [-instance] _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Matrix

namespace ElasticityConic

abbrev C3 := Fin 3 → ℂ
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℂ

def null (v : C3) : Prop := dotProduct v v = 0

def theta (z₀ z₁ : ℂ) : C3 :=
  ![z₀ ^ 2 - z₁ ^ 2, Complex.I * (z₀ ^ 2 + z₁ ^ 2), 2 * z₀ * z₁]

def h₁ (z₀ z₁ : ℂ) : C3 := ![z₀, Complex.I * z₀, z₁]
def h₂ (z₀ z₁ : ℂ) : C3 := ![-z₁, Complex.I * z₁, z₀]

lemma dot3 (a b : C3) : dotProduct a b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp [dotProduct, Fin.sum_univ_succ, add_assoc]

lemma theta_dot_h₁ (z₀ z₁ : ℂ) : dotProduct (theta z₀ z₁) (h₁ z₀ z₁) = 0 := by
  simp only [dot3, theta, h₁, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (z₀ ^ 2 + z₁ ^ 2) * z₀ * Complex.I_sq

lemma theta_dot_h₂ (z₀ z₁ : ℂ) : dotProduct (theta z₀ z₁) (h₂ z₀ z₁) = 0 := by
  simp only [dot3, theta, h₂, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (z₀ ^ 2 + z₁ ^ 2) * z₁ * Complex.I_sq

end ElasticityConic

/-! Finite-type uniqueness used in the last step of the elasticity proof.
All spaces and coefficient fields below are actual functions, not axioms. -/
noncomputable section
open Set Filter Module
open scoped BigOperators Topology

namespace ElasticityFiniteType

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section CoordinateSystems
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [FiniteDimensional ℝ E]

def matrixCLM (M : κ → κ → ℝ) : (κ → ℝ) →L[ℝ] (κ → ℝ) :=
  ContinuousLinearMap.pi fun a => ∑ b, M a b • ContinuousLinearMap.proj b

def coordL (b : Basis ι ℝ E) (s : ι) : E →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj s).comp b.equivFunL.toContinuousLinearMap

def systemCLM (b : Basis ι ℝ E) (M : E → ι → κ → κ → ℝ) (x : E) :
    E →L[ℝ] (κ → ℝ) →L[ℝ] (κ → ℝ) :=
  ∑ s, (coordL b s).smulRight (matrixCLM (M x s))

end CoordinateSystems

section Closure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def d (B : ι → ι → ι → E → ℝ) (s i : ι) (x : E) : ℝ :=
  B s i i x - B i i s x

end Closure

end ElasticityFiniteType

end
end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_WeakLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityGeneralSlicing
/-! Actual transverse slicing of weak planar equations. All planar tests share
one exceptional null set. No uncountable a.e. intersection is used. -/
open Set MeasureTheory Filter
open scoped SchwartzMap ENNReal InnerProductSpace
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    [FiniteDimensional ℝ P] [MeasureSpace P] [BorelSpace P]
    [Measure.IsAddHaarMeasure (volume : Measure P)]
open ElasticityPlanar

abbrev PL2 := Lp ℂ 2 (volume : Measure ℂ)
def sliceLp (u : P × ℂ → ℂ) (t : P) : PL2 :=
  by classical exact if h : MemLp (fun z => u (t,z)) 2 volume then h.toLp _ else 0

def testDbar (φ : Test) : Test := d (1:ℂ) φ+Complex.I • d Complex.I φ

def testGraph (φ : Test) : PL2 × PL2 := (L2 (cj φ),L2 (cj (testDbar φ)))

def slicePair (u w : P × ℂ → ℂ) (t : P) (q : PL2 × PL2) : ℂ :=
  inner ℂ q.1 (sliceLp w t)-inner ℂ q.2 (sliceLp u t)

end ElasticityGeneralSlicing
namespace ElasticityGeneralSlicing
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    [FiniteDimensional ℝ P] [MeasureSpace P] [BorelSpace P]
    [Measure.IsAddHaarMeasure (volume : Measure P)]
open ElasticityPlanar

instance cylinder_temperate : (volume : Measure (P × ℂ)).HasTemperateGrowth := by
  change ((volume : Measure P).prod (volume : Measure ℂ)).HasTemperateGrowth
  infer_instance

omit [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)] in
lemma compact_product_test (η : P → ℝ) (hcη : HasCompactSupport η) (φ : Test) :
    HasCompactSupport (fun q : P × ℂ => (η q.1 : ℂ)*φ q.2) := by
  apply HasCompactSupport.intro (hcη.prod (compact φ))
  intro q hq
  by_cases ht : q.1∈tsupport η
  · have hz : q.2∉tsupport (φ : ℂ → ℂ) := fun hz => hq ⟨ht,hz⟩
    rw [image_eq_zero_of_notMem_tsupport hz,mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport ht,Complex.ofReal_zero,zero_mul]

def productTest (η : P → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hcη : HasCompactSupport η) (φ : Test) : 𝓢(P × ℂ,ℂ) :=
  (compact_product_test η hcη φ).toSchwartzMap
    ((Complex.ofRealCLM.contDiff.comp (hη.comp contDiff_fst)).mul
      ((smooth φ).comp contDiff_snd))

end ElasticityGeneralSlicing

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Supported
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/- The exact extension proofs are reused from their canonical original module. -/

namespace ElasticityGraph
open Set
open ElasticityRegularity
variable {E F P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

  [NormedAddCommGroup P] [NormedSpace ℝ P]
local instance instNormedSpaceReal_solutions_1 : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ ℂ F
end ElasticityGraph

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Smoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityCoordinates
/-! Actual Haar/L2 and tempered-distribution change of linear coordinates.
The Jacobian is derived from Haar uniqueness, not silently set equal to one. -/
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal NNReal LineDeriv
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]

omit [FiniteDimensional ℝ F] in
lemma linear_haar (L : F ≃L[ℝ] E) :
    ∃ c : ℝ≥0,0 < c ∧ (volume : Measure F).map L=c • (volume : Measure E) := by
  have : Measure.IsAddHaarMeasure ((volume : Measure F).map L) := L.isAddHaarMeasure_map volume
  exact ⟨Measure.addHaarScalarFactor ((volume : Measure F).map L) (volume : Measure E),
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _,
    Measure.isAddLeftInvariant_eq_smul _ _⟩

omit [FiniteDimensional ℝ F] in
lemma memLp_linear (L : F ≃L[ℝ] E) {u : E → ℂ} {p : ℝ≥0∞}
    (hu : MemLp u p volume) : MemLp (u ∘ L) p volume := by
  obtain ⟨c,_,hc⟩ := linear_haar L
  apply MemLp.comp_of_map _ L.continuous.measurable.aemeasurable
  rw [hc]
  exact hu.smul_measure ENNReal.coe_ne_top

variable [(volume : Measure E).HasTemperateGrowth] [(volume : Measure F).HasTemperateGrowth]

def linearPull (L : F ≃L[ℝ] E) (D : 𝓢'(E,ℂ)) : 𝓢'(F,ℂ) :=
  D.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm)

def pullLp (L : F ≃L[ℝ] E) (u : Lp ℂ 2 (volume : Measure E)) : Lp ℂ 2 (volume : Measure F) :=
  (memLp_linear L (Lp.memLp u)).toLp (u ∘ L)

end ElasticityCoordinates
namespace ElasticityCoordinates
open Set MeasureTheory
open scoped ENNReal SchwartzMap LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- The actual characteristic plane and its transverse kernel are complementary.
No orthonormal-coordinate or slicing-existence premise is imposed. -/
def planeSplit (J : ℂ →L[ℝ] E) (K : E →L[ℝ] ℂ) (hK : Function.LeftInverse K J) :
    E ≃L[ℝ] LinearMap.ker K.toLinearMap × ℂ :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun x => (⟨x-J (K x),by
      change K (x-J (K x))=0
      rw [map_sub,hK,sub_self]⟩,K x)
    invFun := fun q => (q.1 : E)+J q.2
    left_inv := fun x => sub_add_cancel x (J (K x))
    right_inv := fun q => by
      have hk : K (q.1 : E)=0 := q.1.property
      apply Prod.ext
      · apply Subtype.ext
        change (q.1 : E)+J q.2-J (K ((q.1 : E)+J q.2))=(q.1 : E)
        rw [map_add,hk,zero_add,hK q.2,add_sub_cancel_right]
      · change K ((q.1 : E)+J q.2)=q.2
        rw [map_add,hk,zero_add,hK q.2]
    map_add' := fun x y => by
      apply Prod.ext
      · apply Subtype.ext
        change x+y-J (K (x+y))=(x-J (K x))+(y-J (K y))
        simp only [map_add]
        abel
      · exact map_add K x y
    map_smul' := fun c x => by
      apply Prod.ext
      · apply Subtype.ext
        change c • x-J (K (c • x))=c • (x-J (K x))
        simp only [map_smul,smul_sub]
      · exact map_smul K c x }

end ElasticityCoordinates
open Set Filter TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Conic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Matrix
namespace ElasticityConic
open ElasticityFrame

/-- Polynomial coordinates on the finite chart of the actual constrained
rank-three fiber, including its scalar component. -/
def finiteCoordinates (z : ℂ) (p : Amp) : Fin 3 → ℂ :=
  ![(p.1 0-Complex.I*p.1 1)/2,p.1 2-z*((p.1 0-Complex.I*p.1 1)/2),p.2]
def finiteVector (z : ℂ) (c : Fin 3 → ℂ) : Amp :=
  (c 0 • h₁ 1 z+c 1 • h₂ 1 z,c 2)
lemma finiteVector_coordinates (z : ℂ) (p : Amp)
    (hp : ElasticityFrame.normal (theta 1 z) p=0) :
    finiteVector z (finiteCoordinates z p)=p := by
  have hh : (1-z^2)*p.1 0+Complex.I*(1+z^2)*p.1 1+2*z*p.1 2=0 := by
    simpa [ElasticityFrame.normal,theta,Fin.sum_univ_three] using hp
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [finiteVector,finiteCoordinates,h₁,h₂,smul_eq_mul]
    · linear_combination -hh/2
    · linear_combination Complex.I*hh/2-p.1 1*Complex.I_sq
    · ring
  · rfl

end ElasticityConic

end
end
section
noncomputable section
open scoped BigOperators Matrix
namespace ElasticityConic
open ElasticityFrame

def chartZ₀ (b : Bool) (z : ℂ) : ℂ := if b then z else 1
def chartZ₁ (b : Bool) (z : ℂ) : ℂ := if b then 1 else z
def chartTheta (b : Bool) (z : ℂ) := theta (chartZ₀ b z) (chartZ₁ b z)
def chartVector (b : Bool) (z : ℂ) (c : Fin 3 → ℂ) : Amp :=
  (c 0 • h₁ (chartZ₀ b z) (chartZ₁ b z)+c 1 • h₂ (chartZ₀ b z) (chartZ₁ b z),c 2)
def chartCoord {A : Type*} [AddCommGroup A] [Module ℂ A] (b : Bool) (z : ℂ) (p : Fin 3 → A) (s : A) : Fin 3 → A :=
  if b then
    let c := -(1/2 : ℂ) • (p 0+Complex.I • p 1)
    ![p 2-z • c,c,s]
  else
    let c := (1/2 : ℂ) • (p 0-Complex.I • p 1)
    ![c,p 2-z • c,s]
lemma chartVector_normal (b : Bool) (z : ℂ) (c : Fin 3 → ℂ) :
    ElasticityFrame.normal (chartTheta b z) (chartVector b z c)=0 := by
  change dotProduct (theta _ _) (c 0 • h₁ _ _+c 1 • h₂ _ _)=0
  rw [dotProduct_add,dotProduct_smul,dotProduct_smul,theta_dot_h₁,theta_dot_h₂]
  simp only [smul_zero,add_zero]
lemma chartCoord_vector (b : Bool) (z : ℂ) (c : Fin 3 → ℂ) :
    chartCoord b z (chartVector b z c).1 (chartVector b z c).2=c := by
  ext i
  cases b <;> fin_cases i <;>
    simp [chartCoord,chartVector,chartZ₀,chartZ₁,h₁,h₂,smul_eq_mul]
  · linear_combination -(c 0+z*c 1)*Complex.I_sq/2
  · linear_combination z*(c 0+z*c 1)*Complex.I_sq/2
  · linear_combination z*(z*c 0+c 1)*Complex.I_sq/2
  · linear_combination -(z*c 0+c 1)*Complex.I_sq/2
lemma chartVector_coord (b : Bool) (z : ℂ) (p : Amp)
    (hp : ElasticityFrame.normal (chartTheta b z) p=0) :
    chartVector b z (chartCoord b z p.1 p.2)=p := by
  have hh := hp
  cases b
  · have hc : chartCoord false z p.1 p.2=finiteCoordinates z p := by
      ext i
      fin_cases i <;> simp [chartCoord,finiteCoordinates,smul_eq_mul,div_eq_mul_inv,mul_comm]
    rw [hc]
    exact finiteVector_coordinates z p hp
  · have he : (z^2-1)*p.1 0+Complex.I*(z^2+1)*p.1 1+2*z*p.1 2=0 := by
      simpa [ElasticityFrame.normal,chartTheta,theta,chartZ₀,chartZ₁,Fin.sum_univ_three] using hh
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [chartVector,chartCoord,chartZ₀,chartZ₁,h₁,h₂,smul_eq_mul]
      · linear_combination he/2
      · linear_combination Complex.I*he/2-p.1 1*Complex.I_sq
      · ring
    · rfl

def conicChart (b : Bool) (z : ℂ) : (Fin 3 → ℂ) ≃ₗ[ℂ] Fiber (chartTheta b z) where
  toFun c := ⟨chartVector b z c,chartVector_normal b z c⟩
  invFun p := chartCoord b z p.val.1 p.val.2
  left_inv := chartCoord_vector b z
  right_inv p := Subtype.ext (chartVector_coord b z p.val p.property)
  map_add' c d := by
    apply Subtype.ext
    apply Prod.ext
    · change (c 0+d 0) • h₁ _ _+(c 1+d 1) • h₂ _ _=
        (c 0 • h₁ _ _+c 1 • h₂ _ _)+(d 0 • h₁ _ _+d 1 • h₂ _ _)
      simp only [add_smul]
      abel
    · rfl
  map_smul' a c := by
    apply Subtype.ext
    apply Prod.ext
    · change (a*c 0) • h₁ _ _+(a*c 1) • h₂ _ _=a • (c 0 • h₁ _ _+c 1 • h₂ _ _)
      simp only [smul_add,mul_smul]
    · rfl
end ElasticityConic

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Rigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityConic

def chartDiagonal (z : ℂ) (i : Fin 3) : ℂ := if i=2 then 1 else z
end ElasticityConic

end
end

end OAI
end


