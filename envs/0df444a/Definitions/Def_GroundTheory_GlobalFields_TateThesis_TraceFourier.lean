-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
-- name    : GroundTheory_GlobalFields_TateThesis_TraceFourier
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:37.796499+00:00
-- url     : https://prove2.me/theorems/ea744bf8-e88c-4499-ae06-928b0a8296ec
-- title:
--   Trace Fourier
-- statement:
--   Definitions and structural lemmas for Trace Fourier, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ComplexConjugate RealInnerProductSpace FourierTransform Real ENNReal SchwartzMap
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
def selfDualMeasure : Measure (mixedSpace K) := (2 ^ nrComplexPlaces K : ℝ≥0∞) • volume
instance : (selfDualMeasure K).IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.smul _ (by simp) (by simp)
def mapComplexCoord (a : ℂ ≃L[ℝ] ℂ) : mixedSpace K ≃L[ℝ] mixedSpace K :=
  (ContinuousLinearEquiv.refl ℝ _).prodCongr (ContinuousLinearEquiv.piCongrRight fun _ => a)
def sqrtTwoSMulComplex : ℂ ≃L[ℝ] ℂ :=
  (LinearEquiv.smulOfNeZero ℝ ℂ (√2) (by positivity)).toContinuousLinearEquiv
def sqrtTwoSMulConj : ℂ ≃L[ℝ] ℂ := Complex.conjCLE.trans sqrtTwoSMulComplex
def mixedToEuclidean : mixedSpace K ≃L[ℝ] euclidean.mixedSpace K :=
  (mapComplexCoord K sqrtTwoSMulComplex).trans (euclidean.toMixed K).symm
def mixedToEuclideanConj : mixedSpace K ≃L[ℝ] euclidean.mixedSpace K :=
  (mapComplexCoord K sqrtTwoSMulConj).trans (euclidean.toMixed K).symm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def mixedFourier (f : mixedSpace K → E) : mixedSpace K → E :=
  VectorFourier.fourierIntegral 𝐞 (selfDualMeasure K) (mixedTraceForm K) f
def mixedFourierInv (f : mixedSpace K → E) : mixedSpace K → E :=
  VectorFourier.fourierIntegral 𝐞 (selfDualMeasure K) (-mixedTraceForm K) f
def mixedFourierSchwartz : 𝓢(mixedSpace K, E) →L[ℂ] 𝓢(mixedSpace K, E) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclideanConj K)).comp
    ((SchwartzMap.fourierTransformCLM ℂ).comp
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclidean K).symm))
variable [CompleteSpace E]
end
end GroundTheory.Global


