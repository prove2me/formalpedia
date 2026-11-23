-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:57.280141+00:00
-- url     : https://prove2.me/theorems/ffbd6e9b-8dd4-4207-9b9d-9a8856441c18
-- title:
--   Gauss Tube Of Tube Good
-- statement:
--   Definitions and structural lemmas for Gauss Tube Of Tube Good, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussTubeOfTubeGood.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology PositivityTheory.RgEis
namespace GlobalTheory.CompanionTheory.TubeFourier
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
def pt (x y : ℝ × ℝ) : ℂ × ℂ := (⟨x.1, y.1⟩, ⟨x.2, y.2⟩)
def dot (l : ℂ × ℂ) (t : ℝ × ℝ) : ℂ := l.1 * t.1 + l.2 * t.2
def rdot (x t : ℝ × ℝ) : ℝ := x.1 * t.1 + x.2 * t.2
def phi (G : ℂ × ℂ → X) (x t : ℝ × ℝ) : X :=
  ∫ y : ℝ × ℝ, Complex.exp (-dot (pt x y) t) • G (pt x y)
def inv (φ : ℝ × ℝ → X) (l : ℂ × ℂ) : X :=
  (((2 * Real.pi) ^ 2 : ℂ)⁻¹) • ∫ t : ℝ × ℝ, Complex.exp (dot l t) • φ t
def gauss (F : ℂ × ℂ → X) (l : ℂ × ℂ) : X := Complex.exp (l.1 ^ 2 + l.2 ^ 2) • F l
structure GaussTube (G : ℂ × ℂ → X) (Ω : Set (ℝ × ℝ)) : Prop where
  hol : LineHol G (tube Ω)
  cont : ContinuousOn G (tube Ω)
  decay : ∀ C ⊆ Ω, IsCompact C → ∃ M : ℝ, ∀ l ∈ tube C,
    ‖G l‖ ≤ M * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2))
def ExpDecay {T : Type} [TopologicalSpace T] (φ : ℝ × ℝ → T → X) : Prop :=
  ∀ (x₀ : ℝ × ℝ) (g : T), ∃ ε : ℝ, 0 < ε ∧ ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ x : ℝ × ℝ, |x.1 - x₀.1| ≤ ε → |x.2 - x₀.2| ≤ ε →
    ∀ g' ∈ U, ∀ t : ℝ × ℝ, ‖φ t g'‖ ≤ M * Real.exp (-rdot x t) * Real.exp (-ε * (|t.1| + |t.2|))
end GlobalTheory.CompanionTheory.TubeFourier


