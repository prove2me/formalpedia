-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GabLim
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_GabLim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:39.738722+00:00
-- url     : https://prove2.me/theorems/02a8c337-bb83-466d-b05a-b4415bc9551b
-- title:
--   Gab Lim
-- statement:
--   Definitions and structural lemmas for Gab Lim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GabLim.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
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
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
open Topology
open scoped commutatorElement
variable {p K L}
end ReciprocityTheory.DiscreteGroups.LocalClassField


