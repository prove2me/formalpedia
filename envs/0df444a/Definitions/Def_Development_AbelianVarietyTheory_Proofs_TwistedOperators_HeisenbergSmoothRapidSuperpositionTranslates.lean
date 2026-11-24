-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeisenbergSmoothRapidSuperpositionTranslates
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeisenbergSmoothRapidSuperpositionTranslates
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T23:44:25.928267+00:00
-- url     : https://prove2.me/theorems/d84b10b4-a902-4d29-9f86-49f036974946
-- title:
--   Heisenberg Smooth Rapid Superposition Translates
-- statement:
--   Definitions and structural lemmas for Heisenberg Smooth Rapid Superposition Translates, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HeisenbergSmoothRapidSuperpositionTranslates.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
open scoped ContDiff Real
noncomputable section
namespace GlobalTheory.RealWeil
namespace Superpos
variable {V Y B : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
def ph (om : V →L[ℝ] V →L[ℝ] ℝ) (ι : Y →L[ℝ] V) (v : V) (y : Y) : ℂ :=
  cexp (2 * π * I * (om v (ι y) : ℂ))
def Mom (ν : Measure Y) (h : Y → ℂ) : Prop :=
  Continuous h ∧ ∀ n : ℕ, Integrable (fun y => ‖y‖ ^ n * ‖h y‖) ν
def itg (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B) (ι : Y →L[ℝ] V) (h : Y → ℂ) (g : V → B) (v : V) (y : Y) : B :=
  (h y * ph om ι v y) • ρ (ι y) (g v)
variable {om : V →L[ℝ] V →L[ℝ] ℝ} {ρ : V → B →L[ℂ] B} {ι : Y →L[ℝ] V} {ν : Measure Y}
def dh (om : V →L[ℝ] V →L[ℝ] ℝ) (ι : Y →L[ℝ] V) (h : Y → ℂ) (z : V) (y : Y) : ℂ :=
  h y * (2 * π * I * (om z (ι y) : ℂ))
def dI (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B) (ι : Y →L[ℝ] V) (h : Y → ℂ) (g : V → B) (v : V) (y : Y) :
    V →L[ℝ] B :=
  (h y * ph om ι v y) • (((ρ (ι y)).restrictScalars ℝ).comp (fderiv ℝ g v)) +
    (h y • (ph om ι v y • ((2 * π * I : ℂ) • (Complex.ofRealCLM.comp (om.flip (ι y)))))).smulRight (ρ (ι y) (g v))
end Superpos
end GlobalTheory.RealWeil


