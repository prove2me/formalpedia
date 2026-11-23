-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_LowNat
-- name    : ReciprocityTheory_GroupCohomology_LowNat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:28:40.704797+00:00
-- url     : https://prove2.me/theorems/b6c2aecc-c6d7-4a61-b4c7-bf1671268827
-- title:
--   Low Nat
-- statement:
--   Definitions and structural lemmas for Low Nat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/LowNat.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_ContractNthCastAddCastSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx
universe u
end ReciprocityTheory.Coh


