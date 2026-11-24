-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDiagonalMap
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDiagonalMap
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T16:37:12.146307+00:00
-- url     : https://prove2.me/theorems/68253f3b-01f5-4644-82fa-4f71cbdb765a
-- title:
--   Big Cell Diagonal Map
-- statement:
--   Definitions and structural lemmas for Big Cell Diagonal Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellDiagonalMap.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
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
noncomputable section
namespace Formalism.FourierDecayAlt.P.BigCellDiagonalMap
variable {k j ρ : ℕ}
def eW (k : ℕ) : Fin (2 * 0 + k + 1) ≃ Fin (k + 1) := finCongr (by omega)
def muOf (γ : B.Mat k 0) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := Matrix.reindex (eW k) (eW k) γ
end Formalism.FourierDecayAlt.P.BigCellDiagonalMap
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


