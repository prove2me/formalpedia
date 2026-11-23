-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_SubsingletonHOfSubsingleton
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_SubsingletonHOfSubsingleton
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:25.388365+00:00
-- url     : https://prove2.me/theorems/5e3a36fe-bc4d-4127-b766-729e686df69b
-- title:
--   Subsingleton HOf Subsingleton
-- statement:
--   Definitions and structural lemmas for Subsingleton HOf Subsingleton, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/SubsingletonHOfSubsingleton.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HomFInjective
import Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {G' : Type u} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
def tau (R : Type u) [CommRing R] (n : ℕ) : R := 1 + ∑ j : Fin (n + 1), (-1 : R) ^ ((j : ℕ) + 1)
end
end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2


