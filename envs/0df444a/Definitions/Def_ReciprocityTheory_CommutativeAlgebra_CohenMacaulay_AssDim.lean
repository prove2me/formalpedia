-- Prove2me | Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_AssDim
-- name    : ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_AssDim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:44:08.654943+00:00
-- url     : https://prove2.me/theorems/97e3c656-4ab1-4baa-95a5-7e65f4bfacb1
-- title:
--   Ass Dim
-- statement:
--   Definitions and structural lemmas for Ass Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/AssDim.lean

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_Lemmata_GeneralBFactRest_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence Pointwise
variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
def killedBy (M : Type*) [AddCommGroup M] [Module R M] (p : Ideal R) : Submodule R M where
  carrier := {z | ∀ a ∈ p, a • z = 0}
  add_mem' := by
    intro z w hz hw a ha
    rw [smul_add, hz a ha, hw a ha, add_zero]
  zero_mem' := by
    intro a _
    exact smul_zero a
  smul_mem' := by
    intro c z hz a ha
    rw [smul_comm, hz a ha, smul_zero]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
end ReciprocityTheory.CA


