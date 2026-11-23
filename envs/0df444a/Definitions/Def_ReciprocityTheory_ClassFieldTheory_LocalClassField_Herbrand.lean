-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_Herbrand
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_Herbrand
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:16.558406+00:00
-- url     : https://prove2.me/theorems/1627c839-04dd-4d31-a417-a428c45a7b93
-- title:
--   Herbrand
-- statement:
--   Definitions and structural lemmas for Herbrand, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/Herbrand.lean

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
open Function CategoryTheory
universe u
variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G] {M : Type u} [AddCommGroup M] [Module k M]
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand


