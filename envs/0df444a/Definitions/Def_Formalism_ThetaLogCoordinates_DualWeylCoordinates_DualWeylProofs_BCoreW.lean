-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:25:10.067827+00:00
-- url     : https://prove2.me/theorems/0b63295d-55b3-4631-abec-49696900ca3d
-- title:
--   BCore W
-- statement:
--   Definitions and structural lemmas for BCore W, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreW.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
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
def qb_psi (mu : Fin n → ℤ) : ℤ := ∑ a, ∑ b ∈ univ.filter (· ≤ a), mu b
variable [NeZero n]
def qb_wtT (mu : Fin n → ℤ) (I : TIdx mu) : Fin n → ℤ :=
  fun a => mu (lastIdx n) + ((univ.filter fun c : ↥(TCols mu) => a ∈ (I c).1).card : ℤ)
end Formalism.InvariantFactorPaths.ColumnFamilies


