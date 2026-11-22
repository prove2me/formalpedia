-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:01.051395+00:00
-- url     : https://prove2.me/theorems/6e65d3bd-c2a4-4a0e-8f39-a8788b9d4c89
-- title:
--   Act Form Contract
-- statement:
--   Definitions and structural lemmas for Act Form Contract, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
variable {R : Type*} [CommRing R] {n : ℕ}
def basisF (I : Finset (Fin n)) : Form R n := fun I' => if I' = I then 1 else 0
end Formalism.InvariantFactorPaths.GelfandTsetlinBases


