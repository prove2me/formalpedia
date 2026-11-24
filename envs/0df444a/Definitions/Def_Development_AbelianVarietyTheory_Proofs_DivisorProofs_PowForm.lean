-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:25.677636+00:00
-- url     : https://prove2.me/theorems/7601c370-f653-4fe1-a6cf-fbeefb32ee74
-- title:
--   Pow Form
-- statement:
--   Definitions and structural lemmas for Pow Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PowForm.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace GlobalTheory.ConvSeries
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def wt (b c : ℝ) (h : E → ℂ) (a : E) : ℂ :=
  Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a * Complex.exp (-((c * ‖a‖ ^ 2 : ℝ) : ℂ))
def innerC (a : E) : E →L[ℝ] ℂ := Complex.ofRealCLM ∘L innerSL ℝ a
def powForm (k : ℕ) (a : E) : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℂ).compContinuousLinearMap fun _ => innerC a
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
def coef (b c : ℝ) (h : E → ℂ) (k : ℕ) : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ :=
  ∫ a, wt b c h a • powForm k a
def term (b c : ℝ) (h : E → ℂ) (k : ℕ) (y : E) : ℂ :=
  Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * (((2 * c) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) *
    coef b c h k (fun _ => y)
end GlobalTheory.ConvSeries


