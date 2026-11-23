-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
-- name    : GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:54.404573+00:00
-- url     : https://prove2.me/theorems/49f5a95e-754f-4b9b-95d5-03ff9fa13395
-- title:
--   Sobolev Mollifier
-- statement:
--   Definitions and structural lemmas for Sobolev Mollifier, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMollifier.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevDuality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
section MultiplierFourier
variable {m : E → ℂ} {C s t : ℝ}
theorem bound_of_le {m : E → ℂ} {M : ℝ} (hM : ∀ ξ, ‖m ξ‖ ≤ M) (ξ : E) :
    ‖m ξ‖ ≤ M * (1 + ‖ξ‖ ^ 2) ^ ((s - s) / 2) := by
  rw [sub_self, zero_div, Real.rpow_zero, mul_one]; exact hM ξ
end MultiplierFourier
section Convolution
variable (E) in

def reflect : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := E)).toContinuousLinearEquiv
variable (F) in

def convolution (ψ : 𝓢(E, ℂ)) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  PointwiseConvergenceCLM.precomp F
    (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (reflect E ψ))
end Convolution
section Mollifier
theorem norm_fourier_le_integral (ψ : 𝓢(E, ℂ)) (ξ : E) :
    ‖(𝓕 ψ : 𝓢(E, ℂ)) ξ‖ ≤ ∫ x, ‖ψ x‖ := by
  rw [SchwartzMap.fourier_coe]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
namespace SobolevSpace
variable {s : ℝ}
def convolutionCLM (ψ : 𝓢(E, ℂ)) : SobolevSpace E F s →L[ℂ] SobolevSpace E F s :=
  multiplier (𝓕 ψ : 𝓢(E, ℂ)).hasTemperateGrowth (bound_of_le (norm_fourier_le_integral ψ))
end SobolevSpace
def mollifier (ψ : 𝓢(E, ℂ)) (ε : ℝ) : 𝓢(E, ℂ) :=
  if h : ε = 0 then ψ else
    ((|ε| ^ Module.finrank ℝ E)⁻¹ : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (LinearEquiv.smulOfNeZero ℝ E ε⁻¹ (inv_ne_zero h)).toContinuousLinearEquiv ψ
end Mollifier
end
end GroundTheory.Automorphic.Sobolev


