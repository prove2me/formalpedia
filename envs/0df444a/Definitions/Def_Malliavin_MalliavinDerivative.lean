-- Prove2me | Definitions.Def_Malliavin_MalliavinDerivative
-- name    : Malliavin_MalliavinDerivative
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:04:03.435066+00:00
-- url     : https://prove2.me/theorems/5f1089ed-330a-56b2-b8a0-248e85c978e6
-- title:
--   Malliavin Derivative
-- statement:
--   Definitions and structural lemmas for Malliavin Derivative, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean

import Definitions.Def_Malliavin_CameronMartinTheorem
import Theorems.Thm_Malliavin_CameronMartin_centeredDualToLp_ae_eq
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_denseRange_ofDual
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_integrable_exp_mul_coe
import Theorems.Thm_Malliavin_CameronMartin_integral_add_inclusion
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
namespace Malliavin
section Abstract
variable {E F ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
def IsTotal (T : κ → F) : Prop := ∀ η : F, (∀ k, ⟪η, T k⟫_ℝ = 0) → η = 0
theorem eq_zero_of_tendsto_of_adjoint (ι' : ι → E) (D : ι → F) (T : κ → F)
    (hT : IsTotal T) (δ : κ → E)
    (hδ : ∀ a k, ⟪D a, T k⟫_ℝ = ⟪ι' a, δ k⟫_ℝ)
    {a : ℕ → ι} {η : F} (ha : Tendsto (fun k ↦ ι' (a k)) atTop (𝓝 0))
    (hD : Tendsto (fun k ↦ D (a k)) atTop (𝓝 η)) : η = 0 := by
  apply hT
  intro k
  have h1 : Tendsto (fun n ↦ ⟪D (a n), T k⟫_ℝ) atTop (𝓝 ⟪η, T k⟫_ℝ) :=
    hD.inner tendsto_const_nhds
  have h2 : Tendsto (fun n ↦ ⟪D (a n), T k⟫_ℝ) atTop (𝓝 0) := by
    simp_rw [hδ _ k]
    simpa only [inner_zero_left] using ha.inner (tendsto_const_nhds (x := δ k))
  exact tendsto_nhds_unique h1 h2
end Abstract
namespace CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
instance instCompleteSpaceSpace : CompleteSpace (Space μ) :=
  inferInstanceAs (CompleteSpace ((centeredDualToLp μ).range.topologicalClosure))
end CameronMartin
section SmoothBounded
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
structure IsSmoothBounded (F : W → ℝ) : Prop where
  contDiff : ContDiff ℝ 1 F
  bounded : ∃ C, ∀ x, |F x| ≤ C
  bounded_fderiv : ∃ C, ∀ x, ‖fderiv ℝ F x‖ ≤ C
namespace IsSmoothBounded
variable {F G : W → ℝ}
theorem continuous (hF : IsSmoothBounded F) : Continuous F := hF.contDiff.continuous
theorem differentiable (hF : IsSmoothBounded F) : Differentiable ℝ F :=
  hF.contDiff.differentiable one_ne_zero
theorem continuous_fderiv (hF : IsSmoothBounded F) : Continuous (fderiv ℝ F) :=
  hF.contDiff.continuous_fderiv one_ne_zero
theorem const (c : ℝ) : IsSmoothBounded (fun _ : W ↦ c) where
  contDiff := contDiff_const
  bounded := ⟨|c|, fun _ ↦ le_rfl⟩
  bounded_fderiv := ⟨0, fun _ ↦ by
    simp only [fderiv_const_apply, norm_zero, le_refl]⟩
theorem add (hF : IsSmoothBounded F) (hG : IsSmoothBounded G) :
    IsSmoothBounded (fun y ↦ F y + G y) where
  contDiff := hF.contDiff.add hG.contDiff
  bounded := by
    obtain ⟨C, hC⟩ := hF.bounded
    obtain ⟨D, hD⟩ := hG.bounded
    exact ⟨C + D, fun x ↦ (abs_add_le _ _).trans (add_le_add (hC x) (hD x))⟩
  bounded_fderiv := by
    obtain ⟨C, hC⟩ := hF.bounded_fderiv
    obtain ⟨D, hD⟩ := hG.bounded_fderiv
    refine ⟨C + D, fun x ↦ ?_⟩
    rw [fderiv_fun_add (hF.differentiable x) (hG.differentiable x)]
    exact (norm_add_le _ _).trans (add_le_add (hC x) (hD x))
theorem mul (hF : IsSmoothBounded F) (hG : IsSmoothBounded G) :
    IsSmoothBounded (fun y ↦ F y * G y) where
  contDiff := hF.contDiff.mul hG.contDiff
  bounded := by
    obtain ⟨C, hC⟩ := hF.bounded
    obtain ⟨D, hD⟩ := hG.bounded
    refine ⟨C * D, fun x ↦ ?_⟩
    rw [abs_mul]
    exact mul_le_mul (hC x) (hD x) (abs_nonneg _) ((abs_nonneg _).trans (hC x))
  bounded_fderiv := by
    obtain ⟨C, hC⟩ := hF.bounded
    obtain ⟨D, hD⟩ := hG.bounded
    obtain ⟨C', hC'⟩ := hF.bounded_fderiv
    obtain ⟨D', hD'⟩ := hG.bounded_fderiv
    refine ⟨C * D' + D * C', fun x ↦ ?_⟩
    rw [fderiv_fun_mul (hF.differentiable x) (hG.differentiable x)]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hC x) (hD' x) (norm_nonneg _) ((abs_nonneg _).trans (hC x))
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hD x) (hC' x) (norm_nonneg _) ((abs_nonneg _).trans (hD x))
theorem smul (hF : IsSmoothBounded F) (c : ℝ) : IsSmoothBounded (fun y ↦ c * F y) :=
  (const c).mul hF
theorem neg (hF : IsSmoothBounded F) : IsSmoothBounded (fun y ↦ -F y) := by
  simpa [neg_one_mul] using hF.smul (-1)
theorem sub (hF : IsSmoothBounded F) (hG : IsSmoothBounded G) :
    IsSmoothBounded (fun y ↦ F y - G y) := by
  simpa [sub_eq_add_neg] using hF.add hG.neg
theorem comp_dual {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hb : ∃ C, ∀ t, |φ t| ≤ C)
    (hb' : ∃ C, ∀ t, |deriv φ t| ≤ C) (L : StrongDual ℝ W) :
    IsSmoothBounded (fun x ↦ φ (L x)) where
  contDiff := hφ.comp L.contDiff
  bounded := hb.imp fun C hC x ↦ hC _
  bounded_fderiv := by
    obtain ⟨C, hC⟩ := hb'
    refine ⟨C * ‖L‖, fun x ↦ ?_⟩
    have e : (fun x ↦ φ (L x)) = φ ∘ L := rfl
    rw [e, fderiv_comp x (hφ.differentiable one_ne_zero _) L.differentiableAt, L.fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right ?_ (ContinuousLinearMap.opNorm_nonneg _))
    refine ContinuousLinearMap.opNorm_le_bound _ ((abs_nonneg _).trans (hC (L x))) fun s ↦ ?_
    rw [fderiv_eq_smul_deriv, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (abs_nonneg _)
theorem cos_dual (L : StrongDual ℝ W) : IsSmoothBounded (fun x ↦ Real.cos (L x)) :=
  comp_dual Real.contDiff_cos ⟨1, fun t ↦ Real.abs_cos_le_one t⟩
    ⟨1, fun t ↦ by rw [Real.deriv_cos, abs_neg]; exact Real.abs_sin_le_one t⟩ L
theorem sin_dual (L : StrongDual ℝ W) : IsSmoothBounded (fun x ↦ Real.sin (L x)) :=
  comp_dual Real.contDiff_sin ⟨1, fun t ↦ Real.abs_sin_le_one t⟩
    ⟨1, fun t ↦ by rw [Real.deriv_sin]; exact Real.abs_cos_le_one t⟩ L
end IsSmoothBounded
end SmoothBounded
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
noncomputable def mderiv (F : W → ℝ) (x : W) : Space μ :=
  (InnerProductSpace.toDual ℝ (Space μ)).symm ((fderiv ℝ F x).comp (inclusion μ))
theorem inner_mderiv (F : W → ℝ) (x : W) (h : Space μ) :
    ⟪mderiv μ F x, h⟫_ℝ = fderiv ℝ F x (inclusion μ h) := by
  simp only [mderiv, InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.comp_apply, inclusion_apply]
theorem norm_mderiv_le (F : W → ℝ) (x : W) :
    ‖mderiv μ F x‖ ≤ ‖fderiv ℝ F x‖ * ‖inclusion μ‖ := by
  unfold mderiv
  rw [LinearIsometryEquiv.norm_map]
  exact ContinuousLinearMap.opNorm_comp_le _ _
theorem mderiv_add {F G : W → ℝ} {x : W} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) :
    mderiv μ (fun y ↦ F y + G y) x = mderiv μ F x + mderiv μ G x := by
  unfold mderiv
  rw [fderiv_fun_add hF hG, ContinuousLinearMap.add_comp, map_add]
theorem mderiv_smul {F : W → ℝ} {x : W} (hF : DifferentiableAt ℝ F x) (c : ℝ) :
    mderiv μ (fun y ↦ c * F y) x = c • mderiv μ F x := by
  unfold mderiv
  rw [fderiv_const_mul hF c, ContinuousLinearMap.smul_comp, map_smulₛₗ]
  simp only [conj_trivial]
theorem mderiv_sub {F G : W → ℝ} {x : W} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) :
    mderiv μ (fun y ↦ F y - G y) x = mderiv μ F x - mderiv μ G x := by
  unfold mderiv
  rw [fderiv_fun_sub hF hG, ContinuousLinearMap.sub_comp, LinearIsometryEquiv.map_sub]
theorem mderiv_const (c : ℝ) (x : W) : mderiv μ (fun _ ↦ c) x = 0 := by
  unfold mderiv
  have : fderiv ℝ (fun _ : W ↦ c) x = 0 := by
    exact fderiv_const_apply c
  rw [this, ContinuousLinearMap.zero_comp, LinearIsometryEquiv.map_zero]
theorem mderiv_mul {F G : W → ℝ} {x : W} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) :
    mderiv μ (fun y ↦ F y * G y) x = F x • mderiv μ G x + G x • mderiv μ F x := by
  unfold mderiv
  rw [fderiv_fun_mul hF hG, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.smul_comp, map_add, map_smulₛₗ, map_smulₛₗ]
  simp only [conj_trivial]
namespace IsSmoothBounded
variable {μ} {F G : W → ℝ}
theorem continuous_mderiv (hF : IsSmoothBounded F) : Continuous (mderiv μ F) := by
  unfold mderiv
  exact (InnerProductSpace.toDual ℝ (Space μ)).symm.continuous.comp
    (hF.continuous_fderiv.clm_comp continuous_const)
theorem exists_norm_mderiv_le (hF : IsSmoothBounded F) :
    ∃ C, ∀ x, ‖mderiv μ F x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hF.bounded_fderiv
  refine ⟨C * ‖inclusion μ‖, fun x ↦ (norm_mderiv_le μ F x).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (hC x) (ContinuousLinearMap.opNorm_nonneg _)
variable (μ)
omit [CompleteSpace W] [SecondCountableTopology W] in
theorem memLp (hF : IsSmoothBounded F) (p : ℝ≥0∞) : MemLp F p μ := by
  obtain ⟨C, hC⟩ := hF.bounded
  exact MemLp.of_bound hF.continuous.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x ↦ by simpa [Real.norm_eq_abs] using hC x)
omit [CompleteSpace W] [SecondCountableTopology W] in
theorem integrable (hF : IsSmoothBounded F) : Integrable F μ :=
  (hF.memLp μ 1).integrable le_rfl
theorem memLp_mderiv (hF : IsSmoothBounded F) (p : ℝ≥0∞) : MemLp (mderiv μ F) p μ := by
  obtain ⟨C, hC⟩ := hF.exists_norm_mderiv_le (μ := μ)
  exact MemLp.of_bound hF.continuous_mderiv.aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)
theorem memLp_inner_mderiv (hF : IsSmoothBounded F) (h : Space μ) (p : ℝ≥0∞) :
    MemLp (fun x ↦ ⟪mderiv μ F x, h⟫_ℝ) p μ := by
  obtain ⟨C, hC⟩ := hF.exists_norm_mderiv_le (μ := μ)
  refine MemLp.of_bound ((hF.continuous_mderiv.inner continuous_const).aestronglyMeasurable)
    (C * ‖h‖) (Filter.Eventually.of_forall fun x ↦ ?_)
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))
theorem integrable_inner_mderiv (hF : IsSmoothBounded F) (h : Space μ) :
    Integrable (fun x ↦ ⟪mderiv μ F x, h⟫_ℝ) μ :=
  (hF.memLp_inner_mderiv μ h 1).integrable le_rfl
omit [CompleteSpace W] [SecondCountableTopology W] in
/-- A bounded continuous functional times an `L²` function is integrable. -/
theorem integrable_mul_coe (hF : IsSmoothBounded F) (g : Lp ℝ 2 μ) :
    Integrable (fun x ↦ F x * g x) μ := by
  obtain ⟨C, hC⟩ := hF.bounded
  exact ((Lp.memLp g).integrable one_le_two).bdd_mul hF.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ by simpa [Real.norm_eq_abs] using hC x)
omit [CompleteSpace W] in
theorem memLp_smul (hF : IsSmoothBounded F) (h : Space μ) (p : ℝ≥0∞) :
    MemLp (fun x ↦ F x • h) p μ := by
  obtain ⟨C, hC⟩ := hF.bounded
  refine MemLp.of_bound (hF.continuous.smul continuous_const).aestronglyMeasurable (C * ‖h‖)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
omit [CompleteSpace W] [SecondCountableTopology W] [IsGaussian μ] in
/-- A smooth bounded functional times an integrable function is integrable. -/
theorem integrable_mul (hF : IsSmoothBounded F) {g : W → ℝ} (hg : Integrable g μ) :
    Integrable (fun x ↦ F x * g x) μ := by
  obtain ⟨C, hC⟩ := hF.bounded
  exact hg.bdd_mul hF.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ by simpa [Real.norm_eq_abs] using hC x)
omit [CompleteSpace W] [SecondCountableTopology W] in
theorem memLp_mul_coe (hF : IsSmoothBounded F) (g : Lp ℝ 2 μ) :
    MemLp (fun x ↦ F x * g x) 2 μ :=
  (Lp.memLp g).mul' (hF.memLp μ ∞)
noncomputable def toLp (hF : IsSmoothBounded F) : Lp ℝ 2 μ := (hF.memLp μ 2).toLp F
noncomputable def mderivLp (hF : IsSmoothBounded F) : Lp (Space μ) 2 μ :=
  (hF.memLp_mderiv μ 2).toLp (mderiv μ F)
omit [CompleteSpace W] [SecondCountableTopology W] in
theorem toLp_sub (hF : IsSmoothBounded F) (hG : IsSmoothBounded G) :
    (hF.sub hG).toLp μ = hF.toLp μ - hG.toLp μ :=
  MemLp.toLp_sub (hF.memLp μ 2) (hG.memLp μ 2)
theorem mderivLp_sub (hF : IsSmoothBounded F) (hG : IsSmoothBounded G) :
    (hF.sub hG).mderivLp μ = hF.mderivLp μ - hG.mderivLp μ := by
  unfold IsSmoothBounded.mderivLp
  rw [← MemLp.toLp_sub, MemLp.toLp_eq_toLp_iff]
  refine Filter.Eventually.of_forall fun x ↦ ?_
  exact mderiv_sub μ (hF.differentiable x) (hG.differentiable x)
omit [CompleteSpace W] [SecondCountableTopology W] in
theorem toLp_add (hF : IsSmoothBounded F) (hG : IsSmoothBounded G) :
    (hF.add hG).toLp μ = hF.toLp μ + hG.toLp μ :=
  MemLp.toLp_add (hF.memLp μ 2) (hG.memLp μ 2)
theorem mderivLp_add (hF : IsSmoothBounded F) (hG : IsSmoothBounded G) :
    (hF.add hG).mderivLp μ = hF.mderivLp μ + hG.mderivLp μ := by
  unfold IsSmoothBounded.mderivLp
  rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
  refine Filter.Eventually.of_forall fun x ↦ ?_
  exact mderiv_add μ (hF.differentiable x) (hG.differentiable x)
omit [CompleteSpace W] [SecondCountableTopology W] in
theorem toLp_smul (hF : IsSmoothBounded F) (c : ℝ) :
    (hF.smul c).toLp μ = c • hF.toLp μ := by
  unfold IsSmoothBounded.toLp
  rw [← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
  exact Filter.Eventually.of_forall fun x ↦ rfl
theorem mderivLp_smul (hF : IsSmoothBounded F) (c : ℝ) :
    (hF.smul c).mderivLp μ = c • hF.mderivLp μ := by
  unfold IsSmoothBounded.mderivLp
  rw [← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
  refine Filter.Eventually.of_forall fun x ↦ ?_
  exact mderiv_smul μ (hF.differentiable x) c
noncomputable def smulLp (hG : IsSmoothBounded G) (h : Space μ) : Lp (Space μ) 2 μ :=
  (hG.memLp_smul μ h 2).toLp (fun x ↦ G x • h)
theorem memLp_divergence (hG : IsSmoothBounded G) (h : Space μ) :
    MemLp (fun x ↦ G x * (h : Lp ℝ 2 μ) x - ⟪mderiv μ G x, h⟫_ℝ) 2 μ :=
  (hG.memLp_mul_coe μ (h : Lp ℝ 2 μ)).sub (hG.memLp_inner_mderiv μ h 2)
noncomputable def divergenceLp (hG : IsSmoothBounded G) (h : Space μ) : Lp ℝ 2 μ :=
  (hG.memLp_divergence μ h).toLp (fun x ↦ G x * (h : Lp ℝ 2 μ) x - ⟪mderiv μ G x, h⟫_ℝ)
end IsSmoothBounded
theorem integral_inner_mderiv_eq_inner_integral {F : W → ℝ} (hF : IsSmoothBounded F)
    (h : Space μ) :
    ∫ x, ⟪mderiv μ F x, h⟫_ℝ ∂μ = ⟪∫ x, mderiv μ F x ∂μ, h⟫_ℝ := by
  have e : (fun x ↦ ⟪mderiv μ F x, h⟫_ℝ) = fun x ↦ ⟪h, mderiv μ F x⟫_ℝ :=
    funext fun x ↦ real_inner_comm _ _
  rw [e, integral_inner ((hF.memLp_mderiv μ 1).integrable le_rfl) h, real_inner_comm]
omit [CompleteSpace W] [SecondCountableTopology W] in
/-- `∫ F · g dμ = ⟪F, g⟫_{L²}` for a smooth bounded `F` and `g ∈ L²(μ)`.  In particular the
right side of the integration by parts formula is the `L²` pairing of `F` with `h`, hence
continuous in `h`. -/
theorem integral_mul_coe_eq_inner {F : W → ℝ} (hF : IsSmoothBounded F) (g : Lp ℝ 2 μ) :
    ∫ x, F x * g x ∂μ = ⟪hF.toLp μ, g⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (hF.memLp μ 2)] with x hx
  unfold IsSmoothBounded.toLp
  rw [hx]
  simp only [RCLike.inner_apply, conj_trivial, mul_comm]
theorem integral_fderiv_inclusion_ofDual {F : W → ℝ} (hF : IsSmoothBounded F)
    (L : StrongDual ℝ W) :
    ∫ x, fderiv ℝ F x (inclusion μ (ofDual μ L)) ∂μ = ∫ x, F x * (L x - L (mean μ)) ∂μ := by
  set h : Space μ := ofDual μ L with hh
  set k : W := inclusion μ h with hk
  set v : ℝ := ‖h‖ ^ 2 with hv
  have hhm : Measurable ((h : Lp ℝ 2 μ) : W → ℝ) := (Lp.stronglyMeasurable _).measurable
  have hFm : Measurable F := hF.continuous.measurable
  -- the two parametrized integrals agree
  have hΦ : ∀ ε : ℝ, ∫ x, F (x + ε • k) ∂μ =
      ∫ x, F x * Real.exp (ε * (h : Lp ℝ 2 μ) x - ε ^ 2 * (v / 2)) ∂μ := by
    intro ε
    have := integral_add_inclusion μ hF.continuous (ε • h)
    rw [map_smul, ← hk] at this
    rw [this]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul ε (h : Lp ℝ 2 μ)] with x hx
    rw [Submodule.coe_smul, hx, Pi.smul_apply, smul_eq_mul, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, hv]
    ring_nf
  -- derivative of the left side at `0`
  obtain ⟨C, hC⟩ := hF.bounded_fderiv
  have hL : HasDerivAt (fun ε : ℝ ↦ ∫ x, F (x + ε • k) ∂μ) (∫ x, fderiv ℝ F x k ∂μ) 0 := by
    have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
      (s := Metric.ball 0 1) (F := fun ε x ↦ F (x + ε • k))
      (F' := fun ε x ↦ fderiv ℝ F (x + ε • k) k) (bound := fun _ ↦ C * ‖k‖)
      (Metric.ball_mem_nhds 0 one_pos) ?_ ?_ ?_ ?_ ?_ ?_
    · simpa only [zero_smul, add_zero] using this.2
    · exact Filter.Eventually.of_forall fun ε ↦
        (hF.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable
    · simpa only [zero_smul, add_zero] using hF.integrable μ
    · simp only [zero_smul, add_zero]
      exact (hF.continuous_fderiv.clm_apply continuous_const).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x ε _ ↦ ?_
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
    · exact integrable_const _
    · refine Filter.Eventually.of_forall fun x ε _ ↦ ?_
      have hline : HasDerivAt (fun ε : ℝ ↦ x + ε • k) ((1 : ℝ) • k) ε :=
        ((hasDerivAt_id ε).smul_const k).const_add x
      rw [one_smul] at hline
      exact (hF.differentiable _).hasFDerivAt.comp_hasDerivAt ε hline
  -- derivative of the right side at `0`
  obtain ⟨C₀, hC₀⟩ := hF.bounded
  have hv0 : 0 ≤ v := sq_nonneg _
  have hR : HasDerivAt
      (fun ε : ℝ ↦ ∫ x, F x * Real.exp (ε * (h : Lp ℝ 2 μ) x - ε ^ 2 * (v / 2)) ∂μ)
      (∫ x, F x * (((h : Lp ℝ 2 μ) x - 0 * v) *
        Real.exp (0 * (h : Lp ℝ 2 μ) x - 0 ^ 2 * (v / 2))) ∂μ) 0 := by
    have hbound : Integrable (fun x ↦ C₀ * (1 + v) *
        (Real.exp (2 * (h : Lp ℝ 2 μ) x) + Real.exp (-2 * (h : Lp ℝ 2 μ) x))) μ :=
      ((integrable_exp_mul_coe μ h 2).add (integrable_exp_mul_coe μ h (-2))).const_mul _
    have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
      (s := Metric.ball 0 1)
      (F := fun ε x ↦ F x * Real.exp (ε * (h : Lp ℝ 2 μ) x - ε ^ 2 * (v / 2)))
      (F' := fun ε x ↦ F x * (((h : Lp ℝ 2 μ) x - ε * v) *
        Real.exp (ε * (h : Lp ℝ 2 μ) x - ε ^ 2 * (v / 2))))
      (bound := fun x ↦ C₀ * (1 + v) *
        (Real.exp (2 * (h : Lp ℝ 2 μ) x) + Real.exp (-2 * (h : Lp ℝ 2 μ) x)))
      (Metric.ball_mem_nhds 0 one_pos) ?_ ?_ ?_ ?_ hbound ?_
    · exact this.2
    · exact Filter.Eventually.of_forall fun ε ↦ (by fun_prop : Measurable _).aestronglyMeasurable
    · simpa only [zero_mul, pow_two, mul_zero, sub_zero, Real.exp_zero, mul_one] using
        hF.integrable μ
    · exact (by fun_prop : Measurable _).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x ε hε ↦ ?_
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hε
      set a := (h : Lp ℝ 2 μ) x with ha
      have hexp : Real.exp (ε * a - ε ^ 2 * (v / 2)) ≤ Real.exp |a| := by
        apply Real.exp_le_exp.mpr
        have : ε * a ≤ |a| := by
          calc ε * a ≤ |ε * a| := le_abs_self _
            _ = |ε| * |a| := abs_mul _ _
            _ ≤ 1 * |a| := mul_le_mul_of_nonneg_right hε.le (abs_nonneg _)
            _ = |a| := one_mul _
        nlinarith [sq_nonneg ε]
      have hlin : |a - ε * v| ≤ |a| + v := by
        calc |a - ε * v| ≤ |a| + |ε * v| := abs_sub _ _
          _ = |a| + |ε| * v := by rw [abs_mul, abs_of_nonneg hv0]
          _ ≤ |a| + 1 * v := by gcongr
          _ = |a| + v := by ring
      have hexp2 : Real.exp (2 * |a|) ≤ Real.exp (2 * a) + Real.exp (-2 * a) := by
        rcases le_total 0 a with h0 | h0
        · rw [abs_of_nonneg h0]
          exact le_add_of_nonneg_right (Real.exp_pos _).le
        · rw [abs_of_nonpos h0]
          rw [show 2 * -a = -2 * a by ring]
          exact le_add_of_nonneg_left (Real.exp_pos _).le
      have habs : |a| ≤ Real.exp |a| := by
        have := Real.add_one_le_exp |a|
        linarith
      have hone : 1 ≤ Real.exp |a| := Real.one_le_exp (abs_nonneg _)
      have hpos : 0 < Real.exp |a| := Real.exp_pos _
      have hC₀' : 0 ≤ C₀ := (abs_nonneg _).trans (hC₀ x)
      calc ‖F x * ((a - ε * v) * Real.exp (ε * a - ε ^ 2 * (v / 2)))‖
          = |F x| * (|a - ε * v| * Real.exp (ε * a - ε ^ 2 * (v / 2))) := by
            rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
        _ ≤ C₀ * ((|a| + v) * Real.exp |a|) := by
            gcongr
            · exact hC₀ x
        _ ≤ C₀ * ((1 + v) * Real.exp (2 * |a|)) := by
            refine mul_le_mul_of_nonneg_left ?_ hC₀'
            rw [show 2 * |a| = |a| + |a| by ring, Real.exp_add]
            calc (|a| + v) * Real.exp |a| ≤ (Real.exp |a| + v * Real.exp |a|) * Real.exp |a| := by
                  gcongr
                  exact le_mul_of_one_le_right hv0 hone
              _ = (1 + v) * (Real.exp |a| * Real.exp |a|) := by ring
        _ ≤ C₀ * (1 + v) * (Real.exp (2 * a) + Real.exp (-2 * a)) := by
            rw [mul_assoc]
            gcongr
    · refine Filter.Eventually.of_forall fun x ε _ ↦ ?_
      have h1 : HasDerivAt (fun ε : ℝ ↦ ε * (h : Lp ℝ 2 μ) x - ε ^ 2 * (v / 2))
          ((h : Lp ℝ 2 μ) x - ε * v) ε := by
        have h2 : HasDerivAt (fun ε : ℝ ↦ ε * (h : Lp ℝ 2 μ) x) ((h : Lp ℝ 2 μ) x) ε :=
          hasDerivAt_mul_const _
        have h3 : HasDerivAt (fun ε : ℝ ↦ ε ^ 2 * (v / 2))
            (((2 : ℕ) : ℝ) * ε ^ (2 - 1) * (v / 2)) ε :=
          (hasDerivAt_pow 2 ε).mul_const (v / 2)
        refine (h2.fun_sub h3).congr_deriv ?_
        simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
        ring
      exact (h1.exp.const_mul (F x)).congr_deriv (by ring)
  -- conclude
  have hfun : (fun ε : ℝ ↦ ∫ x, F (x + ε • k) ∂μ) =
      fun ε : ℝ ↦ ∫ x, F x * Real.exp (ε * (h : Lp ℝ 2 μ) x - ε ^ 2 * (v / 2)) ∂μ :=
    funext hΦ
  rw [hfun] at hL
  rw [hL.unique hR]
  apply integral_congr_ae
  filter_upwards [centeredDualToLp_ae_eq μ L] with x hx
  rw [hh, coe_ofDual, hx]
  norm_num
theorem integral_inner_mderiv_ofDual {F : W → ℝ} (hF : IsSmoothBounded F)
    (L : StrongDual ℝ W) :
    ∫ x, ⟪mderiv μ F x, ofDual μ L⟫_ℝ ∂μ = ∫ x, F x * (ofDual μ L : Lp ℝ 2 μ) x ∂μ := by
  simp_rw [inner_mderiv]
  rw [integral_fderiv_inclusion_ofDual μ hF L]
  apply integral_congr_ae
  filter_upwards [centeredDualToLp_ae_eq μ L] with x hx
  rw [coe_ofDual, hx]
theorem integral_inner_mderiv {F : W → ℝ} (hF : IsSmoothBounded F) (h : Space μ) :
    ∫ x, ⟪mderiv μ F x, h⟫_ℝ ∂μ = ∫ x, F x * (h : Lp ℝ 2 μ) x ∂μ := by
  have key := (denseRange_ofDual μ).equalizer
    (g := fun h : Space μ ↦ ∫ x, ⟪mderiv μ F x, h⟫_ℝ ∂μ)
    (h := fun h : Space μ ↦ ∫ x, F x * (h : Lp ℝ 2 μ) x ∂μ) ?_ ?_ ?_
  · exact congr_fun key h
  · have e : (fun h : Space μ ↦ ∫ x, ⟪mderiv μ F x, h⟫_ℝ ∂μ) =
        fun h : Space μ ↦ ⟪∫ x, mderiv μ F x ∂μ, h⟫_ℝ :=
      funext (integral_inner_mderiv_eq_inner_integral μ hF)
    rw [e]
    exact continuous_const.inner continuous_id
  · have e : (fun h : Space μ ↦ ∫ x, F x * (h : Lp ℝ 2 μ) x ∂μ) =
        fun h : Space μ ↦ ⟪hF.toLp μ, (h : Lp ℝ 2 μ)⟫_ℝ :=
      funext fun h ↦ integral_mul_coe_eq_inner μ hF h
    rw [e]
    exact continuous_const.inner continuous_subtype_val
  · funext L
    exact integral_inner_mderiv_ofDual μ hF L
theorem integral_inner_mderiv_mul {F G : W → ℝ} (hF : IsSmoothBounded F)
    (hG : IsSmoothBounded G) (h : Space μ) :
    ∫ x, ⟪mderiv μ F x, h⟫_ℝ * G x ∂μ =
      ∫ x, F x * (G x * (h : Lp ℝ 2 μ) x - ⟪mderiv μ G x, h⟫_ℝ) ∂μ := by
  have hFG := integral_inner_mderiv μ (hF.mul hG) h
  have hmul : ∀ x, ⟪mderiv μ (fun y ↦ F y * G y) x, h⟫_ℝ =
      F x * ⟪mderiv μ G x, h⟫_ℝ + ⟪mderiv μ F x, h⟫_ℝ * G x := by
    intro x
    rw [mderiv_mul μ (hF.differentiable x) (hG.differentiable x), Submodule.coe_inner,
      Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, ← Submodule.coe_inner, ← Submodule.coe_inner]
    ring
  have h1 : Integrable (fun x ↦ F x * ⟪mderiv μ G x, h⟫_ℝ) μ :=
    hF.integrable_mul μ (hG.integrable_inner_mderiv μ h)
  have h2 : Integrable (fun x ↦ ⟪mderiv μ F x, h⟫_ℝ * G x) μ := by
    simpa [mul_comm] using hG.integrable_mul μ (hF.integrable_inner_mderiv μ h)
  have h4 : Integrable (fun x ↦ F x * G x * (h : Lp ℝ 2 μ) x) μ :=
    (hF.mul hG).integrable_mul_coe μ (h : Lp ℝ 2 μ)
  simp only [hmul] at hFG
  rw [integral_add h1 h2] at hFG
  have h5 : ∫ x, F x * (G x * (h : Lp ℝ 2 μ) x - ⟪mderiv μ G x, h⟫_ℝ) ∂μ =
      ∫ x, F x * G x * (h : Lp ℝ 2 μ) x ∂μ - ∫ x, F x * ⟪mderiv μ G x, h⟫_ℝ ∂μ := by
    rw [← integral_sub h4 h1]
    congr 1
    funext x
    ring
  rw [h5]
  linarith
theorem inner_mderivLp_smulLp {F G : W → ℝ} (hF : IsSmoothBounded F)
    (hG : IsSmoothBounded G) (h : Space μ) :
    ⟪hF.mderivLp μ, hG.smulLp μ h⟫_ℝ = ⟪hF.toLp μ, hG.divergenceLp μ h⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  calc ∫ x, ⟪(hF.mderivLp μ) x, (hG.smulLp μ h) x⟫_ℝ ∂μ
      = ∫ x, ⟪mderiv μ F x, G x • h⟫_ℝ ∂μ := by
        apply integral_congr_ae
        filter_upwards [MemLp.coeFn_toLp (hF.memLp_mderiv μ 2),
          MemLp.coeFn_toLp (hG.memLp_smul μ h 2)] with x hx hy
        change ⟪((hF.memLp_mderiv μ 2).toLp (mderiv μ F)) x,
          ((hG.memLp_smul μ h 2).toLp (fun x ↦ G x • h)) x⟫_ℝ = _
        rw [hx, hy]
    _ = ∫ x, ⟪mderiv μ F x, h⟫_ℝ * G x ∂μ := by
        congr 1
        funext x
        rw [Submodule.coe_inner, Submodule.coe_smul, real_inner_smul_right,
          ← Submodule.coe_inner, mul_comm]
    _ = ∫ x, F x * (G x * (h : Lp ℝ 2 μ) x - ⟪mderiv μ G x, h⟫_ℝ) ∂μ :=
        integral_inner_mderiv_mul μ hF hG h
    _ = ∫ x, ⟪(hF.toLp μ) x, (hG.divergenceLp μ h) x⟫_ℝ ∂μ := by
        apply integral_congr_ae
        filter_upwards [MemLp.coeFn_toLp (hF.memLp μ 2),
          MemLp.coeFn_toLp (hG.memLp_divergence μ h)] with x hx hy
        change _ = ⟪((hF.memLp μ 2).toLp F) x, ((hG.memLp_divergence μ h).toLp
            (fun x ↦ G x * (h : Lp ℝ 2 μ) x - ⟪mderiv μ G x, h⟫_ℝ)) x⟫_ℝ
        rw [hx, hy]
        simp only [Submodule.coe_inner, RCLike.inner_apply, conj_trivial, mul_comm]
abbrev SimpleIndex : Type _ := {G : W → ℝ // IsSmoothBounded G} × Space μ
noncomputable def simpleVec (p : SimpleIndex μ) : Lp (Space μ) 2 μ := p.1.2.smulLp μ p.2
noncomputable def simpleDiv (p : SimpleIndex μ) : Lp ℝ 2 μ := p.1.2.divergenceLp μ p.2
omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The smooth bounded functionals form a subspace of `L²(μ)`. -/
noncomputable def smoothBoundedLp : Submodule ℝ (Lp ℝ 2 μ) where
  carrier := Set.range (fun G : {G : W → ℝ // IsSmoothBounded G} ↦ G.2.toLp μ)
  add_mem' := by
    rintro _ _ ⟨F, rfl⟩ ⟨G, rfl⟩
    exact ⟨⟨_, F.2.add G.2⟩, IsSmoothBounded.toLp_add μ F.2 G.2⟩
  zero_mem' := ⟨⟨fun _ ↦ 0, IsSmoothBounded.const 0⟩, MemLp.toLp_zero _⟩
  smul_mem' := by
    rintro c _ ⟨G, rfl⟩
    exact ⟨⟨_, G.2.smul c⟩, IsSmoothBounded.toLp_smul μ G.2 c⟩
theorem ae_eq_zero_of_forall_integral_cos_sin {g : W → ℝ} (hg : Integrable g μ)
    (hcos : ∀ L : StrongDual ℝ W, ∫ x, Real.cos (L x) * g x ∂μ = 0)
    (hsin : ∀ L : StrongDual ℝ W, ∫ x, Real.sin (L x) * g x ∂μ = 0) :
    g =ᵐ[μ] 0 := by
  set gp : W → ℝ := fun x ↦ max (g x) 0 with hgp
  set gm : W → ℝ := fun x ↦ max (-g x) 0 with hgm
  have hgp_int : Integrable gp μ := hg.pos_part
  have hgm_int : Integrable gm μ := hg.neg_part
  have hgp_nn : ∀ x, 0 ≤ gp x := fun x ↦ le_max_right _ _
  have hgm_nn : ∀ x, 0 ≤ gm x := fun x ↦ le_max_right _ _
  have hsub : ∀ x, gp x - gm x = g x := fun x ↦ max_zero_sub_eq_self (g x)
  -- the complex integral of `g` against every character vanishes
  have hchar : ∀ L : StrongDual ℝ W, ∫ x, g x • Complex.exp (L x * Complex.I) ∂μ = 0 := by
    intro L
    have hL : Continuous fun x ↦ L x := L.continuous
    have e : ∀ x, g x • Complex.exp (L x * Complex.I) =
        ((Real.cos (L x) * g x : ℝ) : ℂ) + ((Real.sin (L x) * g x : ℝ) : ℂ) * Complex.I := by
      intro x
      rw [Complex.exp_mul_I, Complex.real_smul, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      push_cast
      ring
    have hc : Integrable (fun x ↦ Real.cos (L x) * g x) μ :=
      hg.bdd_mul (Real.continuous_cos.comp hL).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x ↦ by
          simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (L x))
    have hs : Integrable (fun x ↦ Real.sin (L x) * g x) μ :=
      hg.bdd_mul (Real.continuous_sin.comp hL).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x ↦ by
          simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (L x))
    simp_rw [e]
    rw [integral_add hc.ofReal (hs.ofReal.mul_const _), integral_mul_const,
      integral_complex_ofReal, integral_complex_ofReal, hcos, hsin]
    simp only [Complex.ofReal_zero, zero_mul, add_zero]
  -- the finite measures `g⁺ μ` and `g⁻ μ` have the same characteristic function
  have : IsFiniteMeasure (μ.withDensity fun x ↦ ENNReal.ofReal (gp x)) :=
    isFiniteMeasure_withDensity_ofReal hgp_int.hasFiniteIntegral
  have : IsFiniteMeasure (μ.withDensity fun x ↦ ENNReal.ofReal (gm x)) :=
    isFiniteMeasure_withDensity_ofReal hgm_int.hasFiniteIntegral
  have hp_meas : AEMeasurable (fun x ↦ ENNReal.ofReal (gp x)) μ :=
    hgp_int.aemeasurable.ennreal_ofReal
  have hm_meas : AEMeasurable (fun x ↦ ENNReal.ofReal (gm x)) μ :=
    hgm_int.aemeasurable.ennreal_ofReal
  have hmeas : μ.withDensity (fun x ↦ ENNReal.ofReal (gp x)) =
      μ.withDensity (fun x ↦ ENNReal.ofReal (gm x)) := by
    apply Measure.ext_of_charFunDual
    funext L
    rw [charFunDual_apply, charFunDual_apply,
      integral_withDensity_eq_integral_toReal_smul₀ hp_meas
        (Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul₀ hm_meas
        (Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
    simp_rw [ENNReal.toReal_ofReal (hgp_nn _), ENNReal.toReal_ofReal (hgm_nn _)]
    have hexp : MemLp (fun x ↦ Complex.exp (L x * Complex.I)) ∞ μ :=
      memLp_top_of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
        (Filter.Eventually.of_forall fun x ↦ (Complex.norm_exp_ofReal_mul_I (L x)).le)
    have hpi : Integrable (fun x ↦ gp x • Complex.exp (L x * Complex.I)) μ :=
      hgp_int.smul_of_top_left hexp
    have hmi : Integrable (fun x ↦ gm x • Complex.exp (L x * Complex.I)) μ :=
      hgm_int.smul_of_top_left hexp
    rw [← sub_eq_zero, ← integral_sub hpi hmi, ← hchar L]
    congr 1
    funext x
    rw [← sub_smul, hsub]
  rw [withDensity_eq_iff_of_sigmaFinite hp_meas hm_meas] at hmeas
  filter_upwards [hmeas] with x hx
  rw [ENNReal.ofReal_eq_ofReal_iff (hgp_nn x) (hgm_nn x)] at hx
  have := hsub x
  simp only [Pi.zero_apply]
  linarith
theorem denseRange_toLp :
    DenseRange (fun G : {G : W → ℝ // IsSmoothBounded G} ↦ G.2.toLp μ) := by
  change Dense (smoothBoundedLp μ : Set (Lp ℝ 2 μ))
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro g hg
  rw [Submodule.mem_orthogonal] at hg
  have key : ∀ G : {G : W → ℝ // IsSmoothBounded G}, ∫ x, G.1 x * g x ∂μ = 0 := fun G ↦ by
    rw [integral_mul_coe_eq_inner μ G.2 g]
    exact hg _ ⟨G, rfl⟩
  exact Lp.eq_zero_iff_ae_eq_zero.mpr
    (ae_eq_zero_of_forall_integral_cos_sin μ ((Lp.memLp g).integrable one_le_two)
      (fun L ↦ key ⟨_, IsSmoothBounded.cos_dual L⟩) (fun L ↦ key ⟨_, IsSmoothBounded.sin_dual L⟩))
theorem ae_inner_eq_zero_of_forall_inner_simpleVec {η : Lp (Space μ) 2 μ}
    (hη : ∀ k, ⟪η, simpleVec μ k⟫_ℝ = 0) (h : Space μ) :
    ∀ᵐ x ∂μ, ⟪η x, h⟫_ℝ = 0 := by
  have hmem : MemLp (fun x ↦ ⟪η x, h⟫_ℝ) 2 μ := (Lp.memLp η).inner_const h
  have hzero : hmem.toLp (fun x ↦ ⟪η x, h⟫_ℝ) = 0 := by
    apply (denseRange_toLp μ).eq_zero_of_inner_left ℝ
    intro G
    have hk := hη (G, h)
    rw [L2.inner_def] at hk
    rw [L2.inner_def, ← hk]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hmem, MemLp.coeFn_toLp (G.2.memLp μ 2),
      MemLp.coeFn_toLp (G.2.memLp_smul μ h 2)] with x hx hG hs
    change ⟪(hmem.toLp (fun x ↦ ⟪η x, h⟫_ℝ)) x, ((G.2.memLp μ 2).toLp G.1) x⟫_ℝ =
      ⟪η x, ((G.2.memLp_smul μ h 2).toLp (fun x ↦ G.1 x • h)) x⟫_ℝ
    rw [hx, hG, hs]
    conv_rhs => rw [Submodule.coe_inner, Submodule.coe_smul, real_inner_smul_right,
      ← Submodule.coe_inner]
    simp only [Submodule.coe_inner, RCLike.inner_apply, conj_trivial]
  have := (MemLp.coeFn_toLp hmem).symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hzero)
  filter_upwards [this] with x hx
  exact hx
theorem isTotal_simpleVec : IsTotal (simpleVec μ) := by
  intro η hη
  obtain ⟨t, ⟨c, hc_count, hct⟩, hmem_t⟩ := (Lp.aestronglyMeasurable η).isSeparable_ae_range
  have hall : ∀ᵐ x ∂μ, ∀ h ∈ c, ⟪η x, h⟫_ℝ = 0 :=
    (ae_ball_iff hc_count).mpr fun h _ ↦ ae_inner_eq_zero_of_forall_inner_simpleVec μ hη h
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hmem_t, hall] with x hx hx'
  change (η : W → Space μ) x = 0
  have hcl : closure c ⊆ {y : Space μ | ⟪η x, y⟫_ℝ = 0} := by
    apply closure_minimal
    · exact fun y hy ↦ hx' y hy
    · exact isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hself : ⟪η x, η x⟫_ℝ = 0 := hcl (hct hx)
  exact inner_self_eq_zero.mp hself
theorem mderiv_closable (F : ℕ → {F : W → ℝ // IsSmoothBounded F}) {η : Lp (Space μ) 2 μ}
    (hF : Tendsto (fun k ↦ (F k).2.toLp μ) atTop (𝓝 0))
    (hD : Tendsto (fun k ↦ (F k).2.mderivLp μ) atTop (𝓝 η)) : η = 0 := by
  have hδ : ∀ (a : {F : W → ℝ // IsSmoothBounded F}) (k : SimpleIndex μ),
      ⟪a.2.mderivLp μ, simpleVec μ k⟫_ℝ = ⟪a.2.toLp μ, simpleDiv μ k⟫_ℝ :=
    fun a k ↦ inner_mderivLp_smulLp μ a.2 k.1.2 k.2
  exact eq_zero_of_tendsto_of_adjoint (fun F : {F : W → ℝ // IsSmoothBounded F} ↦ F.2.toLp μ)
    (fun F ↦ F.2.mderivLp μ) (simpleVec μ) (isTotal_simpleVec μ) (simpleDiv μ) hδ hF hD
def InGraphClosure (F : Lp ℝ 2 μ) (η : Lp (Space μ) 2 μ) : Prop :=
  ∃ Fk : ℕ → {F : W → ℝ // IsSmoothBounded F},
    Tendsto (fun k ↦ (Fk k).2.toLp μ) atTop (𝓝 F) ∧
      Tendsto (fun k ↦ (Fk k).2.mderivLp μ) atTop (𝓝 η)
def domD12 : Set (Lp ℝ 2 μ) := {F | ∃ η, InGraphClosure μ F η}
theorem IsSmoothBounded.inGraphClosure {F : W → ℝ} (hF : IsSmoothBounded F) :
    InGraphClosure μ (hF.toLp μ) (hF.mderivLp μ) :=
  ⟨fun _ ↦ ⟨F, hF⟩, tendsto_const_nhds, tendsto_const_nhds⟩
theorem IsSmoothBounded.toLp_mem_domD12 {F : W → ℝ} (hF : IsSmoothBounded F) :
    hF.toLp μ ∈ domD12 μ :=
  ⟨_, hF.inGraphClosure μ⟩
theorem InGraphClosure.unique {F : Lp ℝ 2 μ} {η η' : Lp (Space μ) 2 μ}
    (h1 : InGraphClosure μ F η) (h2 : InGraphClosure μ F η') : η = η' := by
  obtain ⟨Fk, hF1, hD1⟩ := h1
  obtain ⟨Gk, hF2, hD2⟩ := h2
  let Hk : ℕ → {F : W → ℝ // IsSmoothBounded F} :=
    fun k ↦ ⟨fun y ↦ (Fk k).1 y - (Gk k).1 y, (Fk k).2.sub (Gk k).2⟩
  have hH : Tendsto (fun k ↦ (Hk k).2.toLp μ) atTop (𝓝 0) := by
    have h := hF1.sub hF2
    rw [sub_self] at h
    exact Filter.Tendsto.congr (fun k ↦ (IsSmoothBounded.toLp_sub μ (Fk k).2 (Gk k).2).symm) h
  have hDH : Tendsto (fun k ↦ (Hk k).2.mderivLp μ) atTop (𝓝 (η - η')) :=
    Filter.Tendsto.congr (fun k ↦ (IsSmoothBounded.mderivLp_sub μ (Fk k).2 (Gk k).2).symm)
      (hD1.sub hD2)
  exact sub_eq_zero.mp (mderiv_closable μ Hk hH hDH)
open Classical in
/-- The closed extension of the Malliavin derivative to `𝔻₁,₂` (and `0` outside it). -/
noncomputable def mderivClosure (F : Lp ℝ 2 μ) : Lp (Space μ) 2 μ :=
  if h : ∃ η, InGraphClosure μ F η then h.choose else 0
theorem inGraphClosure_mderivClosure {F : Lp ℝ 2 μ} (hF : F ∈ domD12 μ) :
    InGraphClosure μ F (mderivClosure μ F) := by
  have h' : ∃ η, InGraphClosure μ F η := hF
  unfold mderivClosure
  rw [dif_pos h']
  exact h'.choose_spec
theorem mderivClosure_eq {F : Lp ℝ 2 μ} {η : Lp (Space μ) 2 μ} (h : InGraphClosure μ F η) :
    mderivClosure μ F = η :=
  (inGraphClosure_mderivClosure μ ⟨η, h⟩).unique μ h
theorem InGraphClosure.add {F G : Lp ℝ 2 μ} {η ζ : Lp (Space μ) 2 μ}
    (hF : InGraphClosure μ F η) (hG : InGraphClosure μ G ζ) :
    InGraphClosure μ (F + G) (η + ζ) := by
  obtain ⟨Fk, hF1, hD1⟩ := hF
  obtain ⟨Gk, hF2, hD2⟩ := hG
  refine ⟨fun k ↦ ⟨fun y ↦ (Fk k).1 y + (Gk k).1 y, (Fk k).2.add (Gk k).2⟩, ?_, ?_⟩
  · exact Filter.Tendsto.congr
      (fun k ↦ (IsSmoothBounded.toLp_add μ (Fk k).2 (Gk k).2).symm) (hF1.add hF2)
  · exact Filter.Tendsto.congr
      (fun k ↦ (IsSmoothBounded.mderivLp_add μ (Fk k).2 (Gk k).2).symm) (hD1.add hD2)
theorem InGraphClosure.smul {F : Lp ℝ 2 μ} {η : Lp (Space μ) 2 μ}
    (hF : InGraphClosure μ F η) (c : ℝ) : InGraphClosure μ (c • F) (c • η) := by
  obtain ⟨Fk, hF1, hD1⟩ := hF
  refine ⟨fun k ↦ ⟨fun y ↦ c * (Fk k).1 y, (Fk k).2.smul c⟩, ?_, ?_⟩
  · exact Filter.Tendsto.congr
      (fun k ↦ (IsSmoothBounded.toLp_smul μ (Fk k).2 c).symm) (hF1.const_smul c)
  · exact Filter.Tendsto.congr
      (fun k ↦ (IsSmoothBounded.mderivLp_smul μ (Fk k).2 c).symm) (hD1.const_smul c)
theorem InGraphClosure.zero : InGraphClosure μ (0 : Lp ℝ 2 μ) 0 := by
  have h := (IsSmoothBounded.const (W := W) 0).inGraphClosure μ
  have e1 : (IsSmoothBounded.const (W := W) 0).toLp μ = 0 := MemLp.toLp_zero _
  have e2 : (IsSmoothBounded.const (W := W) 0).mderivLp μ = 0 := by
    unfold IsSmoothBounded.mderivLp
    rw [← MemLp.toLp_zero (MemLp.zero (μ := μ) (p := 2) (ε := Space μ)),
      MemLp.toLp_eq_toLp_iff]
    exact Filter.Eventually.of_forall (mderiv_const μ 0)
  rwa [e1, e2] at h
noncomputable def D12 : Submodule ℝ (Lp ℝ 2 μ) where
  carrier := domD12 μ
  add_mem' := fun ⟨η, hη⟩ ⟨ζ, hζ⟩ ↦ ⟨η + ζ, hη.add μ hζ⟩
  zero_mem' := ⟨0, InGraphClosure.zero μ⟩
  smul_mem' := fun c _ ⟨η, hη⟩ ↦ ⟨c • η, hη.smul μ c⟩
theorem mderivClosure_add {F G : Lp ℝ 2 μ} (hF : F ∈ domD12 μ) (hG : G ∈ domD12 μ) :
    mderivClosure μ (F + G) = mderivClosure μ F + mderivClosure μ G :=
  mderivClosure_eq μ
    ((inGraphClosure_mderivClosure μ hF).add μ (inGraphClosure_mderivClosure μ hG))
theorem mderivClosure_smul {F : Lp ℝ 2 μ} (hF : F ∈ domD12 μ) (c : ℝ) :
    mderivClosure μ (c • F) = c • mderivClosure μ F :=
  mderivClosure_eq μ ((inGraphClosure_mderivClosure μ hF).smul μ c)
theorem tendsto_of_dist_lt_of_tendsto {X : Type*} [PseudoMetricSpace X] {u v : ℕ → X} {a : X}
    (hv : Tendsto v atTop (𝓝 a)) (huv : ∀ n, dist (u n) (v n) < 1 / ((n : ℝ) + 1)) :
    Tendsto u atTop (𝓝 a) := by
  rw [Metric.tendsto_atTop] at hv ⊢
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := hv (ε / 2) (half_pos hε)
  obtain ⟨N₂, hN₂⟩ := exists_nat_one_div_lt (half_pos hε)
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  have h1 := hN₁ n (le_of_max_le_left hn)
  have hN₂n : (N₂ : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have h2 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N₂ : ℝ) + 1) := by gcongr
  calc dist (u n) a ≤ dist (u n) (v n) + dist (v n) a := dist_triangle _ _ _
    _ < 1 / ((n : ℝ) + 1) + ε / 2 := add_lt_add (huv n) h1
    _ ≤ 1 / ((N₂ : ℝ) + 1) + ε / 2 := by gcongr
    _ < ε / 2 + ε / 2 := by gcongr
    _ = ε := add_halves ε
theorem InGraphClosure.of_tendsto {F : ℕ → Lp ℝ 2 μ} {η : ℕ → Lp (Space μ) 2 μ}
    (h : ∀ n, InGraphClosure μ (F n) (η n)) {F₀ : Lp ℝ 2 μ} {η₀ : Lp (Space μ) 2 μ}
    (hF : Tendsto F atTop (𝓝 F₀)) (hη : Tendsto η atTop (𝓝 η₀)) :
    InGraphClosure μ F₀ η₀ := by
  choose Fk hFk hDk using h
  have key : ∀ n : ℕ, ∃ k : ℕ, dist ((Fk n k).2.toLp μ) (F n) < 1 / ((n : ℝ) + 1) ∧
      dist ((Fk n k).2.mderivLp μ) (η n) < 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp (hFk n)) _ hpos
    obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp (hDk n)) _ hpos
    exact ⟨max N₁ N₂, hN₁ _ (le_max_left _ _), hN₂ _ (le_max_right _ _)⟩
  choose k hk₁ hk₂ using key
  exact ⟨fun n ↦ Fk n (k n), tendsto_of_dist_lt_of_tendsto hF hk₁,
    tendsto_of_dist_lt_of_tendsto hη hk₂⟩
theorem isClosed_graph_mderivClosure :
    IsClosed {z : Lp ℝ 2 μ × Lp (Space μ) 2 μ |
      z.1 ∈ domD12 μ ∧ mderivClosure μ z.1 = z.2} := by
  refine IsSeqClosed.isClosed ?_
  intro f z hf hz
  have hgraph : ∀ n, InGraphClosure μ (f n).1 (f n).2 := by
    intro n
    have h := inGraphClosure_mderivClosure μ (hf n).1
    rw [(hf n).2] at h
    exact h
  have hcl := InGraphClosure.of_tendsto μ hgraph
    ((continuous_fst.tendsto z).comp hz) ((continuous_snd.tendsto z).comp hz)
  exact ⟨⟨z.2, hcl⟩, mderivClosure_eq μ hcl⟩
noncomputable def mderivD12 : D12 μ →ₗ[ℝ] Lp (Space μ) 2 μ where
  toFun F := mderivClosure μ F
  map_add' F G := mderivClosure_add μ F.2 G.2
  map_smul' c F := mderivClosure_smul μ F.2 c
@[simp]
theorem mderivD12_apply (F : D12 μ) : mderivD12 μ F = mderivClosure μ F := rfl
noncomputable def mderivPMap :
    Lp ℝ 2 μ →ₗ.[ℝ] Lp (Space μ) 2 μ where
  domain := D12 μ
  toFun := mderivD12 μ
@[simp]
theorem mderivPMap_domain : (mderivPMap μ).domain = D12 μ := rfl
@[simp]
theorem mderivPMap_apply (F : (mderivPMap μ).domain) :
    mderivPMap μ F = mderivClosure μ F := rfl
theorem mem_mderivPMap_graph_iff {z : Lp ℝ 2 μ × Lp (Space μ) 2 μ} :
    z ∈ (mderivPMap μ).graph ↔
      z.1 ∈ domD12 μ ∧ mderivClosure μ z.1 = z.2 := by
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨F, hfst, hsnd⟩
    constructor
    · rw [← hfst]
      exact F.2
    · rw [← hfst, ← hsnd]
      exact mderivPMap_apply μ F
  · rintro ⟨hF, hD⟩
    refine ⟨⟨z.1, hF⟩, rfl, ?_⟩
    rw [mderivPMap_apply]
    exact hD
theorem isClosed_mderivPMap_graph :
    IsClosed ((mderivPMap μ).graph : Set (Lp ℝ 2 μ × Lp (Space μ) 2 μ)) := by
  have hgraph : ((mderivPMap μ).graph : Set (Lp ℝ 2 μ × Lp (Space μ) 2 μ)) =
      {z | z.1 ∈ domD12 μ ∧ mderivClosure μ z.1 = z.2} := by
    ext z
    exact mem_mderivPMap_graph_iff μ
  rw [hgraph]
  exact isClosed_graph_mderivClosure μ
noncomputable abbrev D12Graph : Submodule ℝ (Lp ℝ 2 μ × Lp (Space μ) 2 μ) :=
  (mderivPMap μ).graph
noncomputable instance instCompleteSpaceD12Graph : CompleteSpace (D12Graph μ) := by
  exact @IsClosed.completeSpace_coe _ _ _ _ (isClosed_mderivPMap_graph μ)
namespace D12Graph
noncomputable def toLp : D12Graph μ →L[ℝ] Lp ℝ 2 μ :=
  (ContinuousLinearMap.fst ℝ _ _).comp (D12Graph μ).subtypeL
noncomputable def mderiv : D12Graph μ →L[ℝ] Lp (Space μ) 2 μ :=
  (ContinuousLinearMap.snd ℝ _ _).comp (D12Graph μ).subtypeL
@[simp]
theorem toLp_apply (F : D12Graph μ) : toLp μ F = F.1.1 := rfl
@[simp]
theorem mderiv_apply (F : D12Graph μ) : mderiv μ F = F.1.2 := rfl
theorem toLp_mem (F : D12Graph μ) : toLp μ F ∈ D12 μ :=
  (mem_mderivPMap_graph_iff μ).mp F.2 |>.1
noncomputable def toD12 : D12Graph μ →L[ℝ] D12 μ :=
  (toLp μ).codRestrict (D12 μ) (toLp_mem μ)
@[simp]
theorem coe_toD12 (F : D12Graph μ) :
    (toD12 μ F : Lp ℝ 2 μ) = toLp μ F := rfl
theorem mderiv_eq (F : D12Graph μ) :
    mderiv μ F = mderivClosure μ (toLp μ F) := by
  exact (mem_mderivPMap_graph_iff μ).mp F.2 |>.2.symm
theorem mderivD12_toD12 (F : D12Graph μ) :
    mderivD12 μ (toD12 μ F) = mderiv μ F := by
  calc
    mderivD12 μ (toD12 μ F) = mderivClosure μ (toD12 μ F) :=
      mderivD12_apply μ (toD12 μ F)
    _ = mderivClosure μ (toLp μ F) := by rw [coe_toD12]
    _ = mderiv μ F := (mderiv_eq μ F).symm
noncomputable def ofD12 : D12 μ →ₗ[ℝ] D12Graph μ where
  toFun F := ⟨((F : Lp ℝ 2 μ), mderivD12 μ F), (mderivPMap μ).mem_graph F⟩
  map_add' F G := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact map_add (mderivD12 μ) F G
  map_smul' c F := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact map_smul (mderivD12 μ) c F
@[simp]
theorem toD12_ofD12 (F : D12 μ) : toD12 μ (ofD12 μ F) = F := by
  apply Subtype.ext
  rfl
@[simp]
theorem ofD12_toD12 (F : D12Graph μ) : ofD12 μ (toD12 μ F) = F := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact mderivD12_toD12 μ F
noncomputable def linearEquivD12 : D12Graph μ ≃ₗ[ℝ] D12 μ where
  toLinearMap := (toD12 μ).toLinearMap
  invFun := ofD12 μ
  left_inv := ofD12_toD12 μ
  right_inv := toD12_ofD12 μ
end D12Graph
end Malliavin


