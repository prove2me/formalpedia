-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LocallyCompactField_Countability
-- name    : GroundTheory_HeightsAndTheta_Theta_LocallyCompactField_Countability
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:10.969789+00:00
-- url     : https://prove2.me/theorems/9b6c0b1b-de1d-4759-85fe-27ad453929fd
-- title:
--   Countability
-- statement:
--   Definitions and structural lemmas for Countability, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/LocallyCompactField/Countability.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Heights₂.Theta
open MeasureTheory Measure Filter Topology Set
open scoped NNReal ENNReal Pointwise
section Field
variable {R : Type*} [Field R] [TopologicalSpace R] [IsTopologicalRing R]
def mulLeftAddEquiv (a : R) (ha : a ≠ 0) : R ≃ₜ+ R where
  toFun x := a * x
  invFun x := a⁻¹ * x
  left_inv x := inv_mul_cancel_left₀ ha x
  right_inv x := mul_inv_cancel_left₀ ha x
  map_add' x y := mul_add a x y
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id
variable [LocallyCompactSpace R] [T2Space R]
end Field
section Module
variable {R : Type*} [Field R] [TopologicalSpace R] [IsTopologicalRing R]
  {X : Type*} [AddCommGroup X] [Module R X] [FiniteDimensional R X] [TopologicalSpace X]
  [IsModuleTopology R X]
variable (R X) in

def coordHomeomorph : X ≃ₜ (Fin (Module.finrank R X) → R) :=
  haveI := IsModuleTopology.toContinuousAdd R X
  { toEquiv := (Module.finBasis R X).equivFun.toEquiv
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (Module.finBasis R X).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (Module.finBasis R X).equivFun.symm.toLinearMap }
end Module
section Haar
end Haar
end GroundTheory.Heights₂.Theta


