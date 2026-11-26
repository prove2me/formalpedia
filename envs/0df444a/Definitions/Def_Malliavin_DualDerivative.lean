-- Prove2me | Definitions.Def_Malliavin_DualDerivative
-- name    : Malliavin_DualDerivative
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:10:54.196255+00:00
-- url     : https://prove2.me/theorems/80aa12e3-901f-52e3-ab2f-4fff7792430c
-- title:
--   Dual Derivative
-- statement:
--   Definitions and structural lemmas for Dual Derivative, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/DualDerivative.lean

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Recall
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.mem_symmetricSubmodule


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2
namespace Malliavin
noncomputable def cutoff (n : ℕ) (x : ℝ) : ℝ := (n + 1 : ℝ) * Real.arctan (x / (n + 1))
section DCT
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
end DCT
section Dual
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
noncomputable def dualLp (L : StrongDual ℝ W) : Lp ℝ 2 μ :=
  (IsGaussian.memLp_dual μ L 2 (by simp)).toLp L
noncomputable def constOfDual (L : StrongDual ℝ W) : Lp (Space μ) 2 μ :=
  (memLp_const (ofDual μ L)).toLp _
end Dual
section Brownian
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
end Brownian
section Space
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
noncomputable def constLp : Space μ →ₗᵢ[ℝ] Lp (Space μ) 2 μ :=
  ⟨(Lp.constL 2 μ ℝ : Space μ →L[ℝ] Lp (Space μ) 2 μ).toLinearMap, fun h ↦ by
    rw [ContinuousLinearMap.coe_coe, Lp.constL_apply]
    have hsq : ‖(Lp.const 2 μ h : Lp (Space μ) 2 μ)‖ ^ 2 = ‖h‖ ^ 2 := by
      rw [norm_sq_eq_integral_norm_sq, integral_congr_ae ((Lp.coeFn_const 2 μ h).mono
        fun x hx ↦ by rw [hx])]
      simp only [Function.const_apply, integral_const, measureReal_def, measure_univ,
        ENNReal.toReal_one, one_smul]
    exact (sq_eq_sq₀ (norm_nonneg (Lp.const 2 μ h : Lp (Space μ) 2 μ)) (norm_nonneg h)).mp hsq⟩
end Space
section WienerSpace
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
end WienerSpace
end Malliavin


