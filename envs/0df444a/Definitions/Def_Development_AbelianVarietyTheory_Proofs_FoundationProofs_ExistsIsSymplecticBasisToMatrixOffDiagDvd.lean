-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:27.036436+00:00
-- url     : https://prove2.me/theorems/0c34eee3-b85b-4f49-881a-d3a3e7071352
-- title:
--   Exists Is Symplectic Basis To Matrix Off Diag Dvd
-- statement:
--   Definitions and structural lemmas for Exists Is Symplectic Basis To Matrix Off Diag Dvd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk


set_option autoImplicit false
open Matrix Module Function
open private exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot from
  Mathlib.LinearAlgebra.SymplecticGroup
namespace GlobalTheory
section Semilocal
variable {R : Type*} [CommRing R]
end Semilocal
section SpecialLinear
variable {S R : Type*} [CommRing S] [CommRing R] {f : S →+* R}
  {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
def LiftsToDetOne (f : S →+* R) (A : Matrix n n R) : Prop :=
  ∃ B : Matrix n n S, B.det = 1 ∧ B.map f = A
namespace LiftsToDetOne
end LiftsToDetOne
end SpecialLinear
section Symplectic
variable {S R : Type*} [CommRing S] [CommRing R] {f : S →+* R}
  {l : Type*} [Fintype l] [DecidableEq l]
def symplecticGroupMap (l : Type*) [Fintype l] [DecidableEq l] (f : S →+* R) :
    symplecticGroup l S →* symplecticGroup l R where
  toFun A := ⟨A.1.map f, SymplecticGroup.map_mem A.2 f⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext Matrix.map_mul
def LiftsToSymplectic (f : S →+* R) (A : Matrix (l ⊕ l) (l ⊕ l) R) : Prop :=
  ∃ B ∈ symplecticGroup l S, B.map f = A
namespace LiftsToSymplectic
theorem J : LiftsToSymplectic f (Matrix.J l R) :=
  ⟨Matrix.J l S, SymplecticGroup.J_mem _ _, map_J _ _⟩
end LiftsToSymplectic
end Symplectic
section Gram
variable {R : Type*} [CommRing R] {l n : Type*} [Fintype l] [DecidableEq l] [Fintype n]
  [DecidableEq n]
end Gram
section Bases
variable {R M l : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype l] [DecidableEq l]
  {B : LinearMap.BilinForm R M}
end Bases
section Lifting
variable {S R Λ M l : Type*} [CommRing S] [CommRing R] [Finite (MaximalSpectrum R)]
  [AddCommGroup Λ] [Module S Λ] [AddCommGroup M] [Module R M] [Fintype l]
  {f : S →+* R} {B : LinearMap.BilinForm S Λ} {B' : LinearMap.BilinForm R M}
end Lifting
section Reduction
open TensorProduct
variable {S R Λ l : Type*} [CommRing S] [CommRing R] [AddCommGroup Λ] [Module S Λ] [Fintype l]
  {B : LinearMap.BilinForm S Λ}
end Reduction
section Int
open TensorProduct
variable {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {B : LinearMap.BilinForm ℤ Λ}
end Int
end GlobalTheory


