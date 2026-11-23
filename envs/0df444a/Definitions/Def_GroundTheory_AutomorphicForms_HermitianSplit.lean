-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HermitianSplit
-- name    : GroundTheory_AutomorphicForms_HermitianSplit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:55.603719+00:00
-- url     : https://prove2.me/theorems/c8742c48-f80f-40cd-8cbc-ac659f8bebd3
-- title:
--   Hermitian Split
-- statement:
--   Definitions and structural lemmas for Hermitian Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianSplit.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitarySplit
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open Module Matrix
variable {F : Type*} [Field F]
variable {V V' : Type*} [AddCommGroup V] [Module (F × F) V] [AddCommGroup V'] [Module (F × F) V']
end GroundTheory.Automorphic


