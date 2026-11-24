-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjPoly
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjPoly
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T14:54:34.617739+00:00
-- url     : https://prove2.me/theorems/f1ba22f1-9b2d-481c-90f6-06e0040f1d57
-- title:
--   Dj Poly
-- statement:
--   Definitions and structural lemmas for Dj Poly, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/DjPoly.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
namespace PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def djVarMat (k j ρ : ℕ) :
    Matrix (Fin j) (Fin j)
      (MvPolynomial ((Fin (2 * (j + ρ) + k + 1) × Fin (2 * (j + ρ) + k + 1)) ⊕
        (Fin (2 * (j + ρ) + k + 1) × Fin (2 * (j + ρ) + k + 1))) ℂ) :=
  fun a b => MvPolynomial.X (Sum.inl (⟨2 * (j + ρ) + k - a.val, by omega⟩, ⟨b.val, by omega⟩))
end PI.UnitaryCorollaryDerivatives


