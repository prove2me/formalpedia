-- Prove2me | Definitions.Def_Malliavin_IteratedKernelPurePower
-- name    : Malliavin_IteratedKernelPurePower
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:05:23.008535+00:00
-- url     : https://prove2.me/theorems/aa44b9c1-5093-403d-b219-944da3bfa4d9
-- title:
--   Iterated Kernel Pure Power
-- statement:
--   Definitions and structural lemmas for Iterated Kernel Pure Power, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedKernelPurePower.lean

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPositiveTowerLI_single
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianSimplexIntegralLI_apply
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_bestNaturalItoIntegrand_centeredNaturalItoIntegral
import Theorems.Thm_Malliavin_centeredNaturalItoEquiv_apply
import Theorems.Thm_Malliavin_centeredNaturalItoIntegralIsometry_apply
import Theorems.Thm_Malliavin_centeredPartL2_coe
import Theorems.Thm_Malliavin_centeredWienerIntegral_coe
import Theorems.Thm_Malliavin_elementaryBrownianCoefficientCLM_apply
import Theorems.Thm_Malliavin_elementaryBrownianValueLinear_apply
import Theorems.Thm_Malliavin_elementaryPredictableCoefficientCLM_apply
import Theorems.Thm_Malliavin_expectationL2_wienerIntegral
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.BrownianIteratedConstruction.brownianPositiveTowerLI_single
attribute [local simp] Malliavin.BrownianIteratedConstruction.brownianSimplexIntegralLI_apply
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.bestNaturalItoIntegrand_centeredNaturalItoIntegral
attribute [local simp] Malliavin.centeredNaturalItoEquiv_apply
attribute [local simp] Malliavin.centeredNaturalItoIntegralIsometry_apply
attribute [local simp] Malliavin.centeredPartL2_coe
attribute [local simp] Malliavin.centeredWienerIntegral_coe
attribute [local simp] Malliavin.elementaryBrownianCoefficientCLM_apply
attribute [local simp] Malliavin.elementaryBrownianValueLinear_apply
attribute [local simp] Malliavin.elementaryPredictableCoefficientCLM_apply
attribute [local simp] Malliavin.expectationL2_wienerIntegral
attribute [local simp] Malliavin.mem_symmetricSubmodule


set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
namespace Malliavin
def iteratedKernelPurePowerFun (n : ℕ) (f : ℝ≥0 → ℝ) : (Fin n → ℝ≥0) → ℝ :=
  fun t ↦ ∏ i, f (t i)
theorem memLp_two_iteratedKernelPurePowerFun (n : ℕ)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    MemLp (iteratedKernelPurePowerFun n f) 2 (iteratedKernelMeasure n) := by
  have hmeas : AEStronglyMeasurable (iteratedKernelPurePowerFun n f)
      (iteratedKernelMeasure n) := by
    unfold iteratedKernelPurePowerFun iteratedKernelMeasure
    apply Finset.aestronglyMeasurable_fun_prod Finset.univ
    intro i _hi
    exact (Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval
        (fun _ : Fin n ↦ nonnegativeLebesgueMeasure) i)
  rw [memLp_two_iff_integrable_sq hmeas]
  have hsq : Integrable (fun t : ℝ≥0 ↦ f t ^ 2) nonnegativeLebesgueMeasure :=
    (Lp.memLp f).integrable_sq
  have hprod : Integrable
      (fun t : Fin n → ℝ≥0 ↦ ∏ i, (f (t i)) ^ 2) (iteratedKernelMeasure n) := by
    exact Integrable.fintype_prod fun _ : Fin n ↦ hsq
  simpa only [iteratedKernelPurePowerFun, Finset.prod_pow] using hprod
noncomputable def iteratedKernelPurePower (n : ℕ)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) : IteratedKernel n :=
  (memLp_two_iteratedKernelPurePowerFun n f).toLp (iteratedKernelPurePowerFun n f)
end Malliavin


