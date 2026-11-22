-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLGenPtInt
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLGenPtInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:15.894607+00:00
-- url     : https://prove2.me/theorems/cc1ef3bd-82d8-47e8-b906-9975d9904e8d
-- title:
--   Qc Ev GLGen Pt Int
-- statement:
--   Definitions and structural lemmas for Qc Ev GLGen Pt Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLGenPtInt.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
def qc_genPt (F : Type) [CommRing F] (n : ℕ) : GL (Fin n) (GLCoord F n) :=
  Matrix.nonsingInvUnit ((algebraMap _ (GLCoord F n)).mapMatrix (genMat F n))
    (by rw [← RingHom.map_det]; exact IsLocalization.Away.algebraMap_isUnit _)
section SMu
variable {n : ℕ} [NeZero n] {M : GLMod n} {mu : Fin n → ℤ} {β : M.ι → GLCoord ℤ n}
end SMu
end Formalism.InvariantFactorPaths.ColumnFamilies


