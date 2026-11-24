-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_CoefRealA
-- name    : Development_WeilBound_ThetaLifts_FrameEstimates_CoefRealA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:38.978845+00:00
-- url     : https://prove2.me/theorems/f8fb69af-2c78-49dd-97c8-abb7c396842c
-- title:
--   Coef Real A
-- statement:
--   Definitions and structural lemmas for Coef Real A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefRealA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.ThKEst.RealFourierCoefficientBounds
open MeasureTheory SchwartzMap
open scoped FourierTransform ContDiff
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
def q (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (M N : ℕ) : Seminorm ℂ (SchwartzMap V ℂ) :=
  (Finset.Iic (M, N)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2
def H (f₁ f₂ : SchwartzMap V ℂ) (x : V) (u : V) : ℂ := f₁ (u + x) * (starRingEnd ℂ) (f₂ u)
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
end PositivityTheory.ThKEst.RealFourierCoefficientBounds
end


