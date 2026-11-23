-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandB
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:51.664561+00:00
-- url     : https://prove2.me/theorems/88085137-9bbd-42be-be09-22f7424a6052
-- title:
--   Units Herbrand B
-- statement:
--   Definitions and structural lemmas for Units Herbrand B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandB.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
open Finset
variable {R : Type*} [Field R] {G : Type*} [Group G] [Fintype G] [MulSemiringAction G R]
def act (g : G) : Rˣ →* Rˣ := Units.map (MulSemiringAction.toRingHom G R g : R →* R)
variable (G) in

def normU : Rˣ →* Rˣ := ∏ g : G, act g
namespace Filt
variable {I : ℕ → AddSubgroup R} {e : R →+ R} (h : Filt G I e)
include h
end Filt
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt


