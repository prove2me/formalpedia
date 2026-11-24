-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_ColsConjTranspose
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_ColsConjTranspose
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:57:17.466689+00:00
-- url     : https://prove2.me/theorems/379ccbc1-77f0-4b1c-900d-f8db4358d7f6
-- title:
--   Cols Conj Transpose
-- statement:
--   Definitions and structural lemmas for Cols Conj Transpose, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/ColsConjTranspose.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NegBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
namespace PI.FrameInd.UPosW
def cols (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    Matrix (Fin (2 * r + k + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  Matrix.of fun p j => gramVec k r z z' γ j p
def emb (m : ℕ) : (Fin m → ℂ) →ₗ[ℂ] (Fin m ⊕ Fin m → ℂ) where
  toFun a := Sum.elim 0 a
  map_add' a b := by funext i; cases i <;> simp
  map_smul' c a := by funext i; cases i <;> simp
end PI.FrameInd.UPosW


