-- Prove2me | Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
-- name    : ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:09:59.099561+00:00
-- url     : https://prove2.me/theorems/1c6d910b-ff58-4052-a82d-ad729cf2974b
-- title:
--   Loc Dim
-- statement:
--   Definitions and structural lemmas for Loc Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/LocDim.lean

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularOfLeHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
variable {R : Type*} [CommRing R] [IsLocalRing R]
end ReciprocityTheory.CA


