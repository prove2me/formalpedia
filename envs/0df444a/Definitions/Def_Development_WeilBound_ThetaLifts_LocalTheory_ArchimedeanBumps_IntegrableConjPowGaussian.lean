-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
-- name    : Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:35.35635+00:00
-- url     : https://prove2.me/theorems/11d1bf6d-237b-4119-bc9d-94b6b3630e8e
-- title:
--   Integrable Conj Pow Gaussian
-- statement:
--   Definitions and structural lemmas for Integrable Conj Pow Gaussian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
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
open scoped ComplexConjugate
variable {ι : Type} [Fintype ι]
def nm (y : ι → ℂ) : ℝ := ∏ w, ‖y w‖ ^ 2
def pr (x y : ι → ℂ) : ℝ := ∑ w, 2 * (x w * y w).re
def FT (h : (ι → ℂ) → ℂ) (t : ι → ℂ) : ℂ := ∫ x, ch (-pr x t) * h x
def r0 (κ : ι → ℕ) (e : ℕ) (x : ι → ℂ) : ℂ := ∏ w, (x w / (‖x w‖ : ℂ)) ^ κ w * (‖x w‖ : ℂ) ^ (2 * e)
def gm (κ : ι → ℕ) (x : ι → ℂ) : ℂ := ∏ w, conj (x w) ^ κ w * Complex.exp (-2 * Real.pi * (‖x w‖ : ℂ) ^ 2)
end PositivityTheory.ThKG.Loc.Bump
end


