-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_SatakeSymmetric
-- name    : GroundTheory_AutomorphicForms_SatakeSymmetric
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:02.660282+00:00
-- url     : https://prove2.me/theorems/a44e4da3-9dda-48c8-b848-b81f0c6eca9a
-- title:
--   Satake Symmetric
-- statement:
--   Definitions and structural lemmas for Satake Symmetric, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
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
open AddMonoidAlgebra MvPolynomial
namespace Spherical
variable {n : ℕ}
def permCoord (σ : Equiv.Perm (Fin n)) : (Fin n → ℤ) →+ (Fin n → ℤ) where
  toFun l := l ∘ σ.symm
  map_zero' := rfl
  map_add' _ _ := rfl
def permAct (σ : Equiv.Perm (Fin n)) : LaurentRing n →ₐ[ℂ] LaurentRing n :=
  mapDomainAlgHom ℂ ℂ (permCoord σ)
variable (n) in

def symmetricLaurent : Subalgebra ℂ (LaurentRing n) where
  carrier := {p | ∀ σ, permAct σ p = p}
  mul_mem' {a b} ha hb σ := by
    change permAct σ (a * b) = a * b
    rw [map_mul, ha σ, hb σ]
  add_mem' {a b} ha hb σ := by
    change permAct σ (a + b) = a + b
    rw [map_add, ha σ, hb σ]
  algebraMap_mem' c σ := AlgHom.commutes _ c
def natToInt : (Fin n →₀ ℕ) →+ (Fin n → ℤ) where
  toFun s i := s i
  map_zero' := by
    funext i
    simp
  map_add' s t := by
    funext i
    simp
variable (n) in

def polyEmb : MvPolynomial (Fin n) ℂ →ₐ[ℂ] LaurentRing n :=
  mapDomainAlgHom ℂ ℂ natToInt
def orbitSum (ν : Fin n → ℤ) : LaurentRing n :=
  ∑ σ : Equiv.Perm (Fin n), monomial (ν ∘ σ.symm)
end Spherical
end GroundTheory.Automorphic


