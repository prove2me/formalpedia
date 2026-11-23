-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_CurriedCoboundaryEq
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_CurriedCoboundaryEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:07.272303+00:00
-- url     : https://prove2.me/theorems/d898a14e-501b-4a6f-af4b-f4bbadb4622a
-- title:
--   Curried Coboundary Eq
-- statement:
--   Definitions and structural lemmas for Curried Coboundary Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/CurriedCoboundaryEq.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_IsTwoCocycleCoboundary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants ReciprocityTheory.Coh.CohomologyFunctoriality₂ ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
def cur (M : TRep R G) (x : M.coch.X 2) (g h : G) : M.V := x.1 ![g, h]
def mk1 (M : TRep R G) (y : G → M.V) (hy : Continuous y) : M.coch.X 1 :=
  ⟨fun v => y (v 0), hy.comp (continuous_apply 0)⟩
variable (M : TRep R G) (N : Subgroup G)
end
end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2


