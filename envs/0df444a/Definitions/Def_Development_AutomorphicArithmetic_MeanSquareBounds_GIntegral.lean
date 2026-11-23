-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_GIntegral
-- name    : Development_AutomorphicArithmetic_MeanSquareBounds_GIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:04:40.519296+00:00
-- url     : https://prove2.me/theorems/950cf9c3-c17c-4d89-bb5f-98150922a559
-- title:
--   GIntegral
-- statement:
--   Definitions and structural lemmas for GIntegral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/MeanSquareBounds/GIntegral.lean

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmoothedRemainderRealIntegralFormula
import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpNegLeDivPowFour
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_PrimesInProgressionCountLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_PsiZeroIntegral
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HasDerivAtLogSquareAntiderivative
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ShortIntervalImpliesProgressionsStatement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SizeEstimates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace QH
section
open Filter Topology ArithmeticFunction MeasureTheory
noncomputable def dom (t : ℝ) : ℝ := 1 / (t * Real.log t ^ 2)
noncomputable def remA (a : ℕ → ℂ) (m : ℂ) (t : ℝ) : ℂ := (∑ k ∈ Icc 1 ⌊t⌋₊, a k) - m * t
noncomputable def RemBound (a : ℕ → ℂ) (m : ℂ) : Prop :=
  ∃ K x₁ : ℝ, 1 < x₁ ∧ ∀ t : ℝ, x₁ ≤ t → ‖remA a m t‖ ≤ K * t / Real.log t ^ 2
noncomputable def aChi {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ := ((vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N)
end
end QH


