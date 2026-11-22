-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhMemDualWeyl
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhMemDualWeyl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:34.199501+00:00
-- url     : https://prove2.me/theorems/8e75ee51-354c-4922-8077-7d45048ba0f0
-- title:
--   Qh Mem Dual Weyl
-- statement:
--   Definitions and structural lemmas for Qh Mem Dual Weyl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhMemDualWeyl.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
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
variable {n : ℕ} {R : Type} [CommRing R]
def qhPhi (R : Type) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin n × Fin n) R →ₐ[R] MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R) :=
  aeval fun v : Fin n × Fin n => X v.2 * C (X v)
end Formalism.InvariantFactorPaths.ColumnFamilies


