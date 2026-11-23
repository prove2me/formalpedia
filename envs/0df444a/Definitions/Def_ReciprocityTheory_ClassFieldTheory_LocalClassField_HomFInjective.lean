-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HomFInjective
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_HomFInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:23.8158+00:00
-- url     : https://prove2.me/theorems/83c8408c-09e0-41e1-be05-90f4e1102965
-- title:
--   Hom FInjective
-- statement:
--   Definitions and structural lemmas for Hom FInjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HomFInjective.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_CurriedCoboundaryEq
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
variable (M : TRep R G) (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M)
end
end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2


