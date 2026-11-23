-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KroneckerTransposeMulVec
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KroneckerTransposeMulVec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:25.197781+00:00
-- url     : https://prove2.me/theorems/0d7a477b-ed22-4c15-af8e-14e761de5002
-- title:
--   Kronecker Transpose Mul Vec
-- statement:
--   Definitions and structural lemmas for Kronecker Transpose Mul Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/KroneckerTransposeMulVec.lean

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
open Matrix
namespace GlobalTheory.PMon
variable {R : Type*} [CommRing R] {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
def vecM {S : Type*} (X : Matrix a b S) : a × b → S := fun p => X p.1 p.2
def homUnit (A : GL a R) (B : GL b R) : GL (a × b) R where
  val := Matrix.kroneckerMap (· * ·) (A : Matrix a a R) ((B⁻¹ : GL b R) : Matrix b b R)ᵀ
  inv := Matrix.kroneckerMap (· * ·) ((A⁻¹ : GL a R) : Matrix a a R) (B : Matrix b b R)ᵀ
  val_inv := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul]
    simp [Matrix.one_kronecker_one]
  inv_val := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul]
    simp [Matrix.one_kronecker_one]
theorem homUnit_val (A : GL a R) (B : GL b R) :
    ((homUnit A B : GL (a × b) R) : Matrix (a × b) (a × b) R) =
      Matrix.kroneckerMap (· * ·) (A : Matrix a a R) ((B⁻¹ : GL b R) : Matrix b b R)ᵀ := rfl
def homRep {G : Type*} [Group G] (ρ₁ : G →* GL a R) (ρ₂ : G →* GL b R) : G →* GL (a × b) R where
  toFun g := homUnit (ρ₁ g) (ρ₂ g)
  map_one' := by
    ext1
    simp [homUnit_val, Matrix.one_kronecker_one]
  map_mul' g h := by
    ext1
    show ((homUnit (ρ₁ (g * h)) (ρ₂ (g * h)) : GL (a × b) R) : Matrix _ _ R) = ((homUnit (ρ₁ g) (ρ₂ g) : GL (a × b) R) : Matrix (a × b) (a × b) R) * ((homUnit (ρ₁ h) (ρ₂ h) : GL (a × b) R) : Matrix (a × b) (a × b) R)
    rw [homUnit_val, homUnit_val, homUnit_val, map_mul, map_mul, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, Matrix.transpose_mul, Matrix.mul_kronecker_mul]
def extCoc {G : Type*} [Group G] (ρ₂ : G →* GL b R) (c : G → Matrix a b R) (g : G) : a × b → R :=
  vecM (c g * (((ρ₂ g)⁻¹ : GL b R) : Matrix b b R))
end GlobalTheory.PMon


