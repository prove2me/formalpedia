-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:55.75494+00:00
-- url     : https://prove2.me/theorems/901a77c9-abd8-4b40-8407-1bc1712d102f
-- title:
--   BCore T
-- statement:
--   Definitions and structural lemmas for BCore T, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreT.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
def qb_sU (w : Fin n → ℤ) : (AddMonoidAlgebra ℤ (Fin n → ℤ))ˣ :=
  Units.map (AddMonoidAlgebra.of ℤ (Fin n → ℤ)) (toUnits (Multiplicative.ofAdd w))
variable [NeZero n]
end Formalism.InvariantFactorPaths.ColumnFamilies


