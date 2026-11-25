-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PhiDerivative_StarinvDeriv
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PhiDerivative_StarinvDeriv
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T08:02:40.543723+00:00
-- url     : https://prove2.me/theorems/393e6c25-bb91-4140-8234-f8fca2406aec
-- title:
--   Starinv Deriv
-- statement:
--   Definitions and structural lemmas for Starinv Deriv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PhiDerivative/StarinvDeriv.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace PI.SwBig.PhiDerivW
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
variable (k r : ℕ)
def dvC : (Fin r → ℂ) →L[ℝ] (Fin (2 * r + k + 1) → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    if h : i.val < r then ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) ⟨i.val, h⟩
    else if h2 : i.val ≤ r + k then 0
    else -((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ)
        ⟨2 * r + k - i.val, by have := i.isLt; omega⟩))
def diagC : (Fin (2 * r + k + 1) → ℂ) →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap (Matrix.diagonalLinearMap (Fin (2 * r + k + 1)) ℝ ℂ)
end PI.SwBig.PhiDerivW


