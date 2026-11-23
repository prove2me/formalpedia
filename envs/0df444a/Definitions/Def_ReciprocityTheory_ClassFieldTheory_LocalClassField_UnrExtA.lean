-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:31.337241+00:00
-- url     : https://prove2.me/theorems/7adf7fa0-447e-452d-828d-38988e50fc6e
-- title:
--   Unr Ext A
-- statement:
--   Definitions and structural lemmas for Unr Ext A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtA.lean

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
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


