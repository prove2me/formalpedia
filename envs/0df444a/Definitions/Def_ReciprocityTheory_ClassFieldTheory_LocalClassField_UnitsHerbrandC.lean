-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandC
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:30.605971+00:00
-- url     : https://prove2.me/theorems/bc755179-3bcf-4c6d-b9a9-3ced91306b58
-- title:
--   Units Herbrand C
-- statement:
--   Definitions and structural lemmas for Units Herbrand C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandC.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandB
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
variable (K L : Type*) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [NormedField L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
noncomputable def Phi : L ≃L[K] ((L ≃ₐ[K] L) → K) :=
  (IsGalois.normalBasis K L).equivFun.toContinuousLinearEquiv
variable {K L}
variable (K L) in

noncomputable def proj1 : L →+ L where
  toFun x := Phi K L x 1 • IsGalois.normalBasis K L 1
  map_zero' := by simp
  map_add' x y := by rw [map_add, Pi.add_apply, add_smul]
variable (K L) in

def ball (t : ℝ) (ht : 0 ≤ t) : AddSubgroup L where
  carrier := {x | ‖Phi K L x‖ ≤ t}
  zero_mem' := by simpa using ht
  add_mem' := fun {x y} hx hy => by
    show ‖Phi K L (x + y)‖ ≤ t
    rw [map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  neg_mem' := fun {x} hx => by
    show ‖Phi K L (-x)‖ ≤ t
    rw [map_neg, norm_neg]; exact hx
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt


