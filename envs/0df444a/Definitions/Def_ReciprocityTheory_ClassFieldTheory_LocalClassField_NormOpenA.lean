-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormOpenA
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_NormOpenA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:54:40.82854+00:00
-- url     : https://prove2.me/theorems/81605c7b-c5d4-40f8-924e-12c0a8bd5dff
-- title:
--   Norm Open A
-- statement:
--   Definitions and structural lemmas for Norm Open A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormOpenA.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}
end ReciprocityTheory.DiscreteGroups.LocalClassField


