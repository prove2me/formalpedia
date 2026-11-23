-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_DiagonalTermNorms_ConvergenceOfLandauEuler
-- name    : Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_DiagonalTermNorms_ConvergenceOfLandauEuler
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:25.737919+00:00
-- url     : https://prove2.me/theorems/794197f7-3166-4da3-85cb-3707855b468e
-- title:
--   Convergence Of Landau Euler
-- statement:
--   Definitions and structural lemmas for Convergence Of Landau Euler, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/DiagonalTermNorms/ConvergenceOfLandauEuler.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
namespace PositivityTheory.RgJS
namespace DiagonalEntryNormBounds
variable {W : Type} (q : W → ℕ)
def ll (p : W × ℕ) : ℝ := ((p.2 : ℝ) + 1) * Real.log (q p.1)
def cd {A : Type} [Fintype A] (α : W → A → ℂ) (p : W × ℕ) : ℝ := ‖∑ a, α p.1 a ^ (p.2 + 1)‖ ^ 2 / ((p.2 : ℝ) + 1)
end DiagonalEntryNormBounds
end PositivityTheory.RgJS


