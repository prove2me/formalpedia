-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ContinuousOnRationalWeight
-- name    : Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ContinuousOnRationalWeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:07.371619+00:00
-- url     : https://prove2.me/theorems/11338779-6d93-4837-a181-c295b377607d
-- title:
--   Continuous On Rational Weight
-- statement:
--   Definitions and structural lemmas for Continuous On Rational Weight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/ContinuousOnRationalWeight.lean

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped SchwartzMap RealInnerProductSpace
variable {ι : Type} [Fintype ι] {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X] {K : Type} [TopologicalSpace K] [T2Space K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
def Dec (a : K × (ι → ℂ) → ℂ) : Prop := ∀ N : ℕ, ∃ C : ℝ, ∀ k c, ‖a (k, c)‖ * (1 + ‖c‖) ^ N ≤ C
def mj (x : ι → ℂ) : ℝ := ((1 + ‖x‖) ^ (Module.finrank ℝ (ι → ℂ) + 1))⁻¹
structure Prp (π : K × (ι → ℂ) → X) (x₀ : X) : Prop where
  cont : Continuous π
  pt : ∃ p, π p = x₀
  cpt : ∃ (ε : ℝ) (S : Set (K × (ι → ℂ))), 0 < ε ∧ IsCompact S ∧ (∀ p ∈ S, ∀ w, p.2 w ≠ 0) ∧ ∀ p, dist (π p) x₀ ≤ ε → p ∈ S
end PositivityTheory.ThKG.Loc.Bump
end


