-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
-- name    : GroundTheory_AutomorphicForms_SphericalLaurent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:42.049809+00:00
-- url     : https://prove2.me/theorems/a2c85129-f47f-4d91-9c30-aa09cb92036d
-- title:
--   Spherical Laurent
-- statement:
--   Definitions and structural lemmas for Spherical Laurent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalLaurent.lean

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
namespace Spherical
open AddMonoidAlgebra
variable {n : ℕ}
variable (n) in

abbrev LaurentRing : Type := AddMonoidAlgebra ℂ (Fin n → ℤ)
abbrev monomial (l : Fin n → ℤ) : LaurentRing n := single l 1
def monomialChar (l : Fin n → ℤ) : (Fin n → ℂˣ) →* ℂ where
  toFun w := ∏ i, ((w i ^ l i : ℂˣ) : ℂ)
  map_one' := by simp
  map_mul' w w' := by
    simp only [Pi.mul_apply, mul_zpow, Units.val_mul, Finset.prod_mul_distrib]
theorem monomialChar_apply (l : Fin n → ℤ) (w : Fin n → ℂˣ) :
    monomialChar l w = ∏ i, ((w i ^ l i : ℂˣ) : ℂ) := rfl
@[simp]
theorem monomialChar_zero (w : Fin n → ℂˣ) : monomialChar 0 w = 1 := by
  simp [monomialChar_apply]
def pointHom (w : Fin n → ℂˣ) : Multiplicative (Fin n → ℤ) →* ℂ where
  toFun l := monomialChar (Multiplicative.toAdd l) w
  map_one' := by simp [monomialChar_apply]
  map_mul' l l' := by
    simp only [toAdd_mul, monomialChar_apply, Pi.add_apply, zpow_add, Units.val_mul,
      Finset.prod_mul_distrib]
def evalAt (w : Fin n → ℂˣ) : LaurentRing n →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (Fin n → ℤ) (pointHom w)
instance : Algebra.FiniteType ℂ (LaurentRing n) := by
  infer_instance
end Spherical
end GroundTheory.Automorphic


