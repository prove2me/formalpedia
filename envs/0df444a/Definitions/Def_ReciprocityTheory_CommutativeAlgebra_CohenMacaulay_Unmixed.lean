-- Prove2me | Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Unmixed
-- name    : ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Unmixed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:36.861193+00:00
-- url     : https://prove2.me/theorems/82fc526f-1315-49e9-a477-4e29b5bac9d1
-- title:
--   Unmixed
-- statement:
--   Definitions and structural lemmas for Unmixed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Unmixed.lean

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_AssDim
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
variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
end ReciprocityTheory.CA


