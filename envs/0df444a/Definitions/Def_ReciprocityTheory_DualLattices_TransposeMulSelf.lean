-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_TransposeMulSelf
-- name    : ReciprocityTheory_DualLattices_TransposeMulSelf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:49.682829+00:00
-- url     : https://prove2.me/theorems/d8da0ed5-9723-4e91-8d0c-5499b911365a
-- title:
--   Transpose Mul Self
-- statement:
--   Definitions and structural lemmas for Transpose Mul Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TransposeMulSelf.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_NearIdentityColengthStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.PGsh
open Matrix
section
variable {K : Type} [Field K] {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
noncomputable def invPerm (e : G ≃ AddChar G K) : Equiv.Perm G :=
  Function.Involutive.toPerm (fun h => e.symm (e h)⁻¹) (fun h => by simp)
end
end ReciprocityTheory.PGsh


