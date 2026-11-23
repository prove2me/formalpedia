-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:54:46.558873+00:00
-- url     : https://prove2.me/theorems/7e56b5f6-b880-4654-8d89-e3f83fc15cb2
-- title:
--   Unr Ext E
-- statement:
--   Definitions and structural lemmas for Unr Ext E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtE.lean

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
end ReciprocityTheory.DiscreteGroups.LocalClassField


