-- Prove2me | Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PermSubSumInv
-- name    : Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PermSubSumInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:07:13.415156+00:00
-- url     : https://prove2.me/theorems/aef11203-3fd9-458c-9275-da1b7280cd90
-- title:
--   Perm Sub Sum Inv
-- statement:
--   Definitions and structural lemmas for Perm Sub Sum Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/PermSubSumInv.lean

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GaloisIrreducibility
namespace SubsetSumInvariance
open Equiv Equiv.Perm Finset
variable {α : Type} [Fintype α] [DecidableEq α]
def orbs (σ : Perm α) : Finset (Finset α) :=
  (σ.cycleFactorsFinset.image support) ∪ ((univ \ σ.support).image fun y => {y})
end SubsetSumInvariance
namespace SubsetSumInvariance
end SubsetSumInvariance
end Formalism.GaloisIrreducibility


