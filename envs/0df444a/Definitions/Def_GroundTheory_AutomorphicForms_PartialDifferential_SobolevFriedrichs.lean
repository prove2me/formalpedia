-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
-- name    : GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:20.866018+00:00
-- url     : https://prove2.me/theorems/0ff9741b-f68b-46a9-ba49-067233dbc4a5
-- title:
--   Sobolev Friedrichs
-- statement:
--   Definitions and structural lemmas for Sobolev Friedrichs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevFriedrichs.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_convolutionCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_sub
attribute [local simp] GroundTheory.Automorphic.Sobolev.dualEquiv_apply


set_option autoImplicit false
namespace GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
section Translation
open Complex in
theorem iteratedDeriv_cexp_I_mul (n : ℕ) :
    iteratedDeriv n (fun t : ℝ ↦ exp (I * t)) = fun t : ℝ ↦ I ^ n * exp (I * t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have h := (((hasDerivAt_id t).ofReal_comp.const_mul I).cexp).const_mul (I ^ n)
    simp only [id] at h
    rw [h.deriv]
    simp only [Complex.ofReal_one, mul_one]
    ring
open Complex in
theorem hasTemperateGrowth_cexp_I_mul : (fun t : ℝ ↦ exp (I * t)).HasTemperateGrowth := by
  refine ⟨Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff),
    fun n ↦ ⟨0, 1, fun t ↦ ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp_I_mul, norm_mul, norm_pow,
    Complex.norm_I, one_pow, one_mul, Complex.norm_exp_I_mul_ofReal]
  simp
def expChar (a : E) (ξ : E) : ℂ := Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ ξ a : ℝ) : ℂ))
theorem expChar_hasTemperateGrowth (a : E) : (expChar a : E → ℂ).HasTemperateGrowth := by
  have hL : (fun ξ : E ↦ 2 * Real.pi * inner ℝ ξ a).HasTemperateGrowth := by
    have : (fun ξ : E ↦ 2 * Real.pi * inner ℝ ξ a) = ⇑((2 * Real.pi) • innerSL ℝ a) := by
      funext ξ; simp [real_inner_comm]
    rw [this]; exact ContinuousLinearMap.hasTemperateGrowth _
  exact hasTemperateGrowth_cexp_I_mul.comp hL
theorem norm_expChar (a ξ : E) : ‖expChar a ξ‖ = 1 := Complex.norm_exp_I_mul_ofReal _
variable (F) in

def translate (h : E) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  PointwiseConvergenceCLM.precomp F (SchwartzMap.compSubConstCLM ℂ (-h))
end Translation
def dqSymbol (v : E) (t : ℝ) (ξ : E) : ℂ := ((t⁻¹ : ℝ) : ℂ) * (expChar (t • v) ξ - 1)
theorem dqSymbol_hasTemperateGrowth (v : E) (t : ℝ) : (dqSymbol v t : E → ℂ).HasTemperateGrowth :=
  (Function.HasTemperateGrowth.const _).mul
    ((expChar_hasTemperateGrowth _).sub (Function.HasTemperateGrowth.const 1))
theorem norm_dqSymbol_le' (v : E) (t : ℝ) (ξ : E) : ‖dqSymbol v t ξ‖ ≤ 2 * |t|⁻¹ := by
  rw [dqSymbol, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, mul_comm]
  gcongr
  calc ‖expChar (t • v) ξ - 1‖ ≤ ‖expChar (t • v) ξ‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_expChar, norm_one]; norm_num
namespace SobolevSpace
variable {s : ℝ}
def diffQuot (v : E) (t : ℝ) : SobolevSpace E F s →L[ℂ] SobolevSpace E F s :=
  multiplier (dqSymbol_hasTemperateGrowth v t) (bound_of_le (norm_dqSymbol_le' v t))
end SobolevSpace
end
end GroundTheory.Automorphic.Sobolev


