-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSchwartzGaussWidth
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSchwartzGaussWidth
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:55.491122+00:00
-- url     : https://prove2.me/theorems/50d40b82-0223-42da-b038-7caa10f2a310
-- title:
--   Exists Schwartz Gauss Width
-- statement:
--   Definitions and structural lemmas for Exists Schwartz Gauss Width, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSchwartzGaussWidth.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.GaussWidths
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
end GlobalTheory.GaussWidths
namespace GlobalTheory.GaussWidths
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
def HasWidth (M : Submodule ℂ (SchwartzMap E ℂ)) (c : ℝ) : Prop :=
  ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M
def ConvStable (M : Submodule ℂ (SchwartzMap E ℂ)) : Prop :=
  ∀ (b c : ℝ), 0 < b → 0 < c →
    (∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M) →
    ∀ (h u : SchwartzMap E ℂ),
      (∀ y, u y = ∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a *
        Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) → u ∈ M
end GlobalTheory.GaussWidths
namespace GlobalTheory.GaussWidths
end GlobalTheory.GaussWidths


