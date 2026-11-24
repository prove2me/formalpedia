-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagCoeffBlockPermute
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagCoeffBlockPermute
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:37:33.859358+00:00
-- url     : https://prove2.me/theorems/aa438ca1-a713-475f-8ecd-5c146fcba61a
-- title:
--   PFlag Coeff Block Permute
-- statement:
--   Definitions and structural lemmas for PFlag Coeff Block Permute, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagCoeffBlockPermute.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
namespace RestTerms
open MvPolynomial
noncomputable section
def blockPermuteEquiv (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) :
    Fin f × Fin N ≃ Fin f × Fin N where
  toFun p := (p.1, w p.1 p.2)
  invFun p := (p.1, (w p.1).symm p.2)
  left_inv p := by simp
  right_inv p := by simp
end
end RestTerms
end GroundTheory.Heights₂.Heights


