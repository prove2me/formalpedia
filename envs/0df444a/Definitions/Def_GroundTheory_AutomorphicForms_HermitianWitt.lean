-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt
-- name    : GroundTheory_AutomorphicForms_HermitianWitt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:31.661798+00:00
-- url     : https://prove2.me/theorems/b1513fdd-7bc3-4b0f-be94-0f7b76229d76
-- title:
--   Hermitian Witt
-- statement:
--   Definitions and structural lemmas for Hermitian Witt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_eq_zero_of_forall
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_smul_right

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
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V₁] [Module E V₁]
  [AddCommGroup V₂] [Module E V₂]
namespace HermitianForm
def quasiReflection (h : HermitianForm F E V) (w : V) (c : E) : V →ₗ[E] V :=
  LinearMap.id - (c • h.toSesq w).smulRight w
def equivOfIsometry [FiniteDimensional E V] (h : HermitianForm F E V) (f : V →ₗ[E] V)
    (hf : ∀ x y, h.toSesq (f x) (f y) = h.toSesq x y) : V ≃ₗ[E] V :=
  LinearEquiv.ofInjectiveEndo f (by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply h.eq_zero_of_forall
    intro y
    rw [← hf, hx, map_zero, LinearMap.zero_apply])
def orthogonal (h : HermitianForm F E V) (U : Submodule E V) : Submodule E V where
  carrier := {y | ∀ x ∈ U, h.toSesq x y = 0}
  add_mem' {a b} ha hb x hx := by rw [map_add, ha x hx, hb x hx, add_zero]
  zero_mem' x _ := map_zero _
  smul_mem' c y hy x hx := by rw [h.toSesq_smul_right, hy x hx, mul_zero]
end HermitianForm
end GroundTheory.Automorphic
end


