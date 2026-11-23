-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreApply
-- name    : CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:08:33.739328+00:00
-- url     : https://prove2.me/theorems/1cc03136-edc9-4a30-92f5-56e35718ef65
-- title:
--   Cre Apply
-- statement:
--   Definitions and structural lemmas for Cre Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/CreApply.lean

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace CompanionTheory.D.LK.Car
variable {n : ℕ}
def tw (i j : Pos n) : ℂ := if key j < key i then -1 else 1
variable {V : Type} [AddCommGroup V] [Module ℂ V]
end CompanionTheory.D.LK.Car


