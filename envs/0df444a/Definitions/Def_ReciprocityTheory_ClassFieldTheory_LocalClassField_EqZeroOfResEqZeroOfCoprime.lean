-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_EqZeroOfResEqZeroOfCoprime
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_EqZeroOfResEqZeroOfCoprime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:11.6528+00:00
-- url     : https://prove2.me/theorems/ff818ef2-42fc-4abf-ad6a-dc957c506073
-- title:
--   Eq Zero Of Res Eq Zero Of Coprime
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Res Eq Zero Of Coprime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/EqZeroOfResEqZeroOfCoprime.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_SubsingletonHOfSubsingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
open ReciprocityTheory.Coh Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {G' : Type u} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
abbrev resP (M : TRep R G) (U : Subgroup G) : Pair M (M.resSub U) :=
  Pair.res M U.subtype continuous_subtype_val
end
end ReciprocityTheory.DiscreteGroups.LocalClassField


