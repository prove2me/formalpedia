-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicRestrict
-- name    : GroundTheory_AutomorphicForms_AnisotropicRestrict
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:56.140303+00:00
-- url     : https://prove2.me/theorems/979684c2-5431-4c8b-bd10-beb3c38ddbbb
-- title:
--   Anisotropic Restrict
-- statement:
--   Definitions and structural lemmas for Anisotropic Restrict, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicRestrict.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Matrix TensorProduct
set_option linter.unusedSectionVars false
namespace GroundTheory.Automorphic
noncomputable section
namespace Anisotropic
variable {K : Type*} [Field K] {κ : Type*} [Fintype κ] [DecidableEq κ]
section General
variable {A : Type*} [Ring A] [Algebra K A] (b : Module.Basis κ K A)
variable (R : Type*) [CommRing R] [Algebra K R]
abbrev baseBasis : Module.Basis κ R (R ⊗[K] A) := Algebra.TensorProduct.basis R b
def coords : (R ⊗[K] A) ≃ₗ[R] (κ → R) := (baseBasis b R).equivFun
theorem coords_baseBasis (k : κ) : coords b R (baseBasis b R k) = Pi.single k 1 := by
  funext l
  rw [coords, Module.Basis.equivFun_self, Pi.single_apply]
  exact if_congr eq_comm rfl rfl
theorem eq_sum_coords (z : R ⊗[K] A) : z = ∑ k, coords b R z k • baseBasis b R k :=
  ((baseBasis b R).sum_equivFun z).symm
def rmat (x : R ⊗[K] A) : Matrix κ κ R := fun k => coords b R (baseBasis b R k * x)
def lmat (a : R ⊗[K] A) : Matrix κ κ R := fun k => coords b R (a * baseBasis b R k)
theorem coords_mul (z x : R ⊗[K] A) : coords b R (z * x) = coords b R z ᵥ* rmat b R x := by
  conv_lhs => rw [eq_sum_coords b R z]
  rw [Finset.sum_mul, map_sum]
  funext l
  simp only [smul_mul_assoc, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecMul,
    dotProduct, rmat]
theorem rmat_mul (x y : R ⊗[K] A) : rmat b R (x * y) = rmat b R x * rmat b R y := by
  ext k l
  simp only [rmat]
  rw [← mul_assoc, coords_mul]
  simp only [vecMul, dotProduct, Matrix.mul_apply, rmat]
theorem rmat_one : rmat b R 1 = 1 := by
  ext k l
  simp only [rmat, mul_one, coords_baseBasis, Pi.single_apply, Matrix.one_apply, eq_comm]
def rmatHom : R ⊗[K] A →ₐ[R] Matrix κ κ R :=
  AlgHom.ofLinearMap
    { toFun := rmat b R
      map_add' := fun x y => by
        ext k l
        simp [rmat, mul_add]
      map_smul' := fun c x => by
        ext k l
        simp [rmat] }
    (rmat_one b R) (rmat_mul b R)
variable {R} {R' : Type*} [CommRing R'] [Algebra K R']
def baseMap (f : R →ₐ[K] R') : R ⊗[K] A →ₐ[K] R' ⊗[K] A :=
  Algebra.TensorProduct.map f (AlgHom.id K A)
end General
section Block
variable {E : Type*} [CommRing E] [Algebra K E] (b : Module.Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def blockHom : Matrix ι ι (R ⊗[K] E) →ₐ[R] Matrix (ι × κ) (ι × κ) R :=
  (Matrix.compAlgEquiv ι κ R R).toAlgHom.comp (rmatHom b R).mapMatrix
def coordsVec (x : ι → R ⊗[K] E) : ι × κ → R := fun p => coords b R (x p.1) p.2
variable {R}
end Block
end Anisotropic
end
end GroundTheory.Automorphic


