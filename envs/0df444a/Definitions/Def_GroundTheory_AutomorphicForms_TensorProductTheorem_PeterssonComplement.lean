-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_PeterssonComplement
-- name    : GroundTheory_AutomorphicForms_TensorProductTheorem_PeterssonComplement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:43.712736+00:00
-- url     : https://prove2.me/theorems/5f86818a-a344-4d02-82ed-0e9a093a6520
-- title:
--   Petersson Complement
-- statement:
--   Definitions and structural lemmas for Petersson Complement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/PeterssonComplement.lean

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
namespace GroundTheory.Automorphic
namespace PeterssonComplement
open Polynomial
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H)
def orthIn (U : Submodule ℂ V) : Submodule ℂ V where
  carrier := {v | ∀ u ∈ U, inner ℂ (ι u) (ι v) = 0}
  zero_mem' u _ := by rw [map_zero, inner_zero_right]
  add_mem' {v w} hv hw u hu := by rw [map_add, inner_add_right, hv u hu, hw u hu, add_zero]
  smul_mem' c v hv u hu := by rw [map_smul, inner_smul_right, hv u hu, mul_zero]
variable {ι}
end PeterssonComplement
end GroundTheory.Automorphic


