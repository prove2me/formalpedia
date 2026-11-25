-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:19:44.987455+00:00
-- url     : https://prove2.me/theorems/ffa0c0e4-a785-4561-8793-01e4d5e840ac
-- title:
--   Anisotropic Column Sums
-- statement:
--   Definitions and structural lemmas for Anisotropic Column Sums, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AnisotropicColumnSums.lean

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace AnisotropicColumnSums
variable {k r : ℕ}
def bcol (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ)
    (j : Fin (mdim k r (Fin.last r))) : Fin (2 * r + k + 1) → ℂ :=
  if h : j.val < k then Bs ⟨j.val, h⟩ else x
def nrm (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) (j : Fin (mdim k r (Fin.last r))) : ℂ :=
  if j.val < k then 1 else (herm (Hpk k r) x x)⁻¹
end AnisotropicColumnSums
end Formalism.FourierDecayAlt.P


