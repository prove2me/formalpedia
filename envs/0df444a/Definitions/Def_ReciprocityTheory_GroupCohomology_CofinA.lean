-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_CofinA
-- name    : ReciprocityTheory_GroupCohomology_CofinA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:57.344994+00:00
-- url     : https://prove2.me/theorems/e054f52c-3c94-4217-871a-732f13ea28d6
-- title:
--   Cofin A
-- statement:
--   Definitions and structural lemmas for Cofin A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CofinA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh.PowerKernelFiltration
universe u
section Art
variable {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
def kerPow (t : R) (m : ℕ) : Submodule R N := LinearMap.ker ((t ^ m) • (LinearMap.id : N →ₗ[R] N))
def layer (t : R) (P : Submodule R N) (m : ℕ) : Submodule R N :=
  (P ⊓ kerPow t (m + 1)).map ((t ^ m) • (LinearMap.id : N →ₗ[R] N))
end Art
section Card
end Card
end ReciprocityTheory.Coh.PowerKernelFiltration


