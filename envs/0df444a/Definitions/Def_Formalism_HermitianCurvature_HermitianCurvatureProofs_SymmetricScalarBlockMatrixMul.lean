-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T14:28:28.939941+00:00
-- url     : https://prove2.me/theorems/9afec8d8-da5e-49de-8822-6bf475645dcb
-- title:
--   Symmetric Scalar Block Matrix Mul
-- statement:
--   Definitions and structural lemmas for Symmetric Scalar Block Matrix Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace Formalism.FourierDecayAlt.P.Ux3
variable {k j ρ : ℕ}
def eC (j ρ : ℕ) : Fin j ⊕ Fin (ρ + 1) ≃ Fin (j + ρ + 1) := finSumFinEquiv.trans (finCongr (by omega))
def F0 (Fj : Matrix (Fin (2 * ρ + k + 1)) (Fin (ρ + 1)) ℂ) : Matrix (Ix k j ρ) (Fin j ⊕ Fin (ρ + 1)) ℂ :=
  Matrix.fromRows (Matrix.fromBlocks 1 0 0 Fj) 0
def skewCoords {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) : (G.UT n → ℂ) × (Fin n → ℝ) :=
  (fun p => S p.1.1 p.1.2, fun i => (S i i).im)
end Formalism.FourierDecayAlt.P.Ux3
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


