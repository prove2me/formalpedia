-- Prove2me | Definitions.Def_Malliavin_Solution
-- name    : Malliavin_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:06:20.012051+00:00
-- url     : https://prove2.me/theorems/df92cde4-3d3d-57cd-b4fd-4d3007263c8f
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Solution.lean

import Definitions.Def_Malliavin
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
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
open scoped ENNReal NNReal Real Topology InnerProductSpace
noncomputable def CameronMartin.Space
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (μ : Measure W) [IsGaussian μ] :
    Submodule ℝ (Lp ℝ 2 μ) :=
  (StrongDual.toLp μ 2 -
    (Lp.constL 2 μ ℝ).comp
      (ContinuousLinearMap.apply ℝ ℝ (∫ x, x ∂μ))).range.topologicalClosure
namespace CameronMartin
noncomputable def centeredId
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (μ : Measure W) [IsGaussian μ] : W → W :=
  id - fun _ ↦ ∫ x, x ∂μ
theorem memLp_centeredId
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (μ : Measure W) [IsGaussian μ] : MemLp (centeredId μ) 2 μ := by
  have h_id : MemLp id 2 μ := IsGaussian.memLp_id μ 2 (by norm_num)
  have h_const : MemLp (fun _ : W ↦ ∫ x, x ∂μ) 2 μ :=
    memLp_const (∫ x, x ∂μ)
  exact h_id.sub h_const
noncomputable def centeredIdLp
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (μ : Measure W) [IsGaussian μ] : Lp W 2 μ :=
  (memLp_centeredId μ).toLp (centeredId μ)
noncomputable def covarianceMap
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (μ : Measure W) [IsGaussian μ] : Lp ℝ 2 μ →L[ℝ] W :=
  ((ContinuousLinearMap.lsmul ℝ ℝ (E := W)).lpPairing μ 2 2).flip
    (centeredIdLp μ)
noncomputable def inclusion
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (μ : Measure W) [IsGaussian μ] : Space μ →L[ℝ] W :=
  (covarianceMap μ).domRestrict (Space μ)
instance instCompleteSpaceSpace
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (μ : Measure W) [IsGaussian μ] : CompleteSpace (Space μ) :=
  inferInstanceAs (CompleteSpace
    ((StrongDual.toLp μ 2 -
      (Lp.constL 2 μ ℝ).comp
        (ContinuousLinearMap.apply ℝ ℝ (∫ x, x ∂μ))).range.topologicalClosure))
end CameronMartin
noncomputable def mderiv
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (μ : Measure W) [IsGaussian μ] (F : W → ℝ) (x : W) : CameronMartin.Space μ :=
  (InnerProductSpace.toDual ℝ (CameronMartin.Space μ)).symm
    ((fderiv ℝ F x).comp (CameronMartin.inclusion μ))
structure IsSmoothBounded {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (F : W → ℝ) : Prop where
  contDiff : ContDiff ℝ 1 F
  bounded : ∃ C, ∀ x, |F x| ≤ C
  bounded_fderiv : ∃ C, ∀ x, ‖fderiv ℝ F x‖ ≤ C
namespace IsSmoothBounded
theorem continuous_fderiv
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : W → ℝ} (hF : IsSmoothBounded F) : Continuous (fderiv ℝ F) :=
  hF.contDiff.continuous_fderiv one_ne_zero
theorem memLp
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    {F : W → ℝ} (μ : Measure W) [IsGaussian μ]
    (hF : IsSmoothBounded F) (p : ℝ≥0∞) : MemLp F p μ := by
  obtain ⟨C, hC⟩ := hF.bounded
  exact MemLp.of_bound hF.contDiff.continuous.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x ↦ by
      simpa [Real.norm_eq_abs] using hC x)
theorem continuous_mderiv
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {F : W → ℝ} (μ : Measure W) [IsGaussian μ]
    (hF : IsSmoothBounded F) : Continuous (mderiv μ F) := by
  unfold mderiv
  exact (InnerProductSpace.toDual ℝ (CameronMartin.Space μ)).symm.continuous.comp
    (hF.continuous_fderiv.clm_comp continuous_const)
theorem exists_norm_mderiv_le
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {F : W → ℝ} (μ : Measure W) [IsGaussian μ]
    (hF : IsSmoothBounded F) : ∃ C, ∀ x, ‖mderiv μ F x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hF.bounded_fderiv
  refine ⟨C * ‖CameronMartin.inclusion μ‖, fun x ↦ ?_⟩
  unfold mderiv
  rw [LinearIsometryEquiv.norm_map]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (hC x)
      (ContinuousLinearMap.opNorm_nonneg _))
theorem memLp_mderiv
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {F : W → ℝ} (μ : Measure W) [IsGaussian μ]
    (hF : IsSmoothBounded F) (p : ℝ≥0∞) : MemLp (mderiv μ F) p μ := by
  obtain ⟨C, hC⟩ := hF.exists_norm_mderiv_le μ
  exact MemLp.of_bound (hF.continuous_mderiv μ).aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)
noncomputable def toLp
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {F : W → ℝ} (μ : Measure W) [IsGaussian μ]
    (hF : IsSmoothBounded F) :
    Lp ℝ 2 μ :=
  (hF.memLp μ 2).toLp F
noncomputable def mderivLp
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {F : W → ℝ} (μ : Measure W) [IsGaussian μ]
    (hF : IsSmoothBounded F) :
    Lp (CameronMartin.Space μ) 2 μ :=
  (hF.memLp_mderiv μ 2).toLp (mderiv μ F)
end IsSmoothBounded


