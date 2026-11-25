-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
-- name    : GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:42:05.290178+00:00
-- url     : https://prove2.me/theorems/9415ed02-1c1f-4626-b943-380a3fbfa3a3
-- title:
--   Sobolev Multiplication
-- statement:
--   Definitions and structural lemmas for Sobolev Multiplication, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
def wK (c : ℝ) (ψ : 𝓢(E, ℂ)) (ζ : E) : ℝ≥0∞ := ENNReal.ofReal ((1 + ‖ζ‖ ^ 2) ^ c * ‖ψ ζ‖)
def wInt (c : ℝ) (ψ : 𝓢(E, ℂ)) : ℝ := ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ c * ‖ψ ζ‖
variable (χ : 𝓢(E, ℂ))
def commRem (r : ℝ) (φ : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) φ -
    SchwartzMap.fourierMultiplierCLM ℂ (weight (-r))
      (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ))
def commConst (r a : ℝ) : ℝ := |r| * 2 ^ (|r - 1| / 2) * 2 ^ (|a| / 2)
open Classical in

def sob (s : ℝ) (u : 𝓢'(E, ℂ)) : ℝ≥0∞ :=
  if h : MemSobolev s 2 u then ‖(SobolevSpace.mk u h : SobolevSpace E ℂ s)‖ₑ else ⊤
def mulConst (r : ℝ) (χ : 𝓢(E, ℂ)) : ℝ := 2 ^ (|r| / 2) * wInt (|r| / 2) (𝓕 χ)
def mulPrin (χ : 𝓢(E, ℂ)) (r : ℝ) : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ) :=
  fourierMultiplierCLM ℂ (weight (-r)) ∘L smulLeftCLM ℂ (χ : E → ℂ) ∘L
    fourierMultiplierCLM ℂ (weight r)
def mulRem (χ : 𝓢(E, ℂ)) (r : ℝ) : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ) :=
  smulLeftCLM ℂ (χ : E → ℂ) - mulPrin χ r
end
end GroundTheory.Automorphic.Sobolev


