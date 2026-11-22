-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_PsiZeroIntegral
-- name    : Formalism_GL3MeanSquares_HookFormulaTorsion_PsiZeroIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:33:03.690768+00:00
-- url     : https://prove2.me/theorems/7dbfc4be-064a-4c95-9353-e0a015d0a37c
-- title:
--   Psi Zero Integral
-- statement:
--   Definitions and structural lemmas for Psi Zero Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/PsiZeroIntegral.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction MeasureTheory
noncomputable section
namespace Formalism.HermitianLattices.P.PsiZeroIntegral
def dom (t : ℝ) : ℝ := 1 / (t * Real.log t ^ 2)
def rem (a : ℕ → ℂ) (m : ℂ) (t : ℝ) : ℂ := (∑ k ∈ Icc 1 ⌊t⌋₊, a k) - m * t
def RemBound (a : ℕ → ℂ) (m : ℂ) : Prop :=
  ∃ K x₁ : ℝ, 1 < x₁ ∧ ∀ t : ℝ, x₁ ≤ t → ‖rem a m t‖ ≤ K * t / Real.log t ^ 2
end Formalism.HermitianLattices.P.PsiZeroIntegral
namespace Formalism.HermitianLattices.GL2a2
end Formalism.HermitianLattices.GL2a2


