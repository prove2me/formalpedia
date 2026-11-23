-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
-- name    : GroundTheory_AutomorphicForms_HermitianSpaces
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:00.658481+00:00
-- url     : https://prove2.me/theorems/0d1f241a-d9c9-4206-8048-38a231a2565b
-- title:
--   Hermitian Spaces
-- statement:
--   Definitions and structural lemmas for Hermitian Spaces, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianSpaces.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj


set_option autoImplicit false
namespace GroundTheory.Automorphic
open Module Matrix
section MatrixGroup
variable {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] [DecidableEq ι]
def unitaryGroupMatrix (s : A →+* A) (H : Matrix ι ι A) : Subgroup (GL ι A) where
  carrier := {g | ((g : Matrix ι ι A).map s)ᵀ * H * g = H}
  one_mem' := by
    simp [Matrix.map_one _ (map_zero s) (map_one s)]
  mul_mem' {g k} hg hk := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Units.val_mul, Matrix.map_mul, transpose_mul]
    calc _ = ((k : Matrix ι ι A).map s)ᵀ *
          ((((g : Matrix ι ι A).map s)ᵀ * H * g) * k) := by simp only [Matrix.mul_assoc]
      _ = H := by rw [hg, ← Matrix.mul_assoc, hk]
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at *
    have h1 : ((g : Matrix ι ι A).map s) * ((↑g⁻¹ : Matrix ι ι A).map s) = 1 := by
      rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero s) (map_one s)]
    calc ((↑g⁻¹ : Matrix ι ι A).map s)ᵀ * H * ↑g⁻¹
        = ((↑g⁻¹ : Matrix ι ι A).map s)ᵀ * (((g : Matrix ι ι A).map s)ᵀ * H * g) * ↑g⁻¹ := by
          rw [hg]
      _ = (((g : Matrix ι ι A).map s) * ((↑g⁻¹ : Matrix ι ι A).map s))ᵀ * H *
          ((g : Matrix ι ι A) * ↑g⁻¹) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [h1, Units.mul_inv, transpose_one, Matrix.one_mul, Matrix.mul_one]
theorem mem_unitaryGroupMatrix {s : A →+* A} {H : Matrix ι ι A} {g : GL ι A} :
    g ∈ unitaryGroupMatrix s H ↔ ((g : Matrix ι ι A).map s)ᵀ * H * g = H := Iff.rfl
def IsHermitianFor (s : A →+* A) (H : Matrix ι ι A) : Prop := (H.map s)ᵀ = H
end MatrixGroup
variable (F E : Type*) [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
noncomputable abbrev conjHom : E →+* E := (conj F E).toAlgHom.toRingHom
variable (V : Type*) [AddCommGroup V] [Module E V]
structure HermitianForm where

  toSesq : V →ₛₗ[conjHom F E] V →ₗ[E] E

  isSymm : toSesq.IsSymm

  nonsingular : Function.Bijective toSesq
variable {F E V}
namespace HermitianForm
def unitaryGroup (h : HermitianForm F E V) : Subgroup (V ≃ₗ[E] V) where
  carrier := {g | ∀ x y, h.toSesq (g x) (g y) = h.toSesq x y}
  one_mem' := fun _ _ => rfl
  mul_mem' {a b} ha hb x y := by
    change h.toSesq (a (b x)) (a (b y)) = _
    rw [ha, hb]
  inv_mem' {a} ha x y := by
    change h.toSesq (a.symm x) (a.symm y) = _
    conv_rhs => rw [← a.apply_symm_apply x, ← a.apply_symm_apply y]
    rw [ha]
end HermitianForm
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def gram (B : V →ₛₗ[conjHom F E] V →ₗ[E] E) (v : Basis ι E V) : Matrix ι ι E :=
  fun i j => B (v i) (v j)
omit [Fintype ι] [DecidableEq ι] in
theorem gram_apply (B : V →ₛₗ[conjHom F E] V →ₗ[E] E) (v : Basis ι E V) (i j : ι) :
    gram B v i j = B (v i) (v j) := rfl
omit [DecidableEq ι] in

theorem sesq_eq_sum (B : V →ₛₗ[conjHom F E] V →ₗ[E] E) (v : Basis ι E V) (x y : V) :
    B x y = ∑ i, ∑ j, conj F E (v.repr x i) * gram B v i j * v.repr y j := by
  conv_lhs => rw [← v.sum_repr x, ← v.sum_repr y]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul,
    smul_eq_mul, Finset.mul_sum, gram_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_toAlgHom]
  ring
theorem sesq_apply_map_basis (B : V →ₛₗ[conjHom F E] V →ₗ[E] E) (v : Basis ι E V)
    (g : V →ₗ[E] V) (i j : ι) :
    B (g (v i)) (g (v j)) =
      (((LinearMap.toMatrix v v g).map (conjHom F E))ᵀ * gram B v * LinearMap.toMatrix v v g)
        i j := by
  rw [sesq_eq_sum B v]
  simp only [Matrix.mul_apply, transpose_apply, map_apply, LinearMap.toMatrix_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl
theorem mem_unitaryGroup_iff_toMatrix (h : HermitianForm F E V) (v : Basis ι E V)
    (g : V ≃ₗ[E] V) :
    g ∈ h.unitaryGroup ↔
      ((LinearMap.toMatrix v v (g : V →ₗ[E] V)).map (conjHom F E))ᵀ * gram h.toSesq v *
        LinearMap.toMatrix v v (g : V →ₗ[E] V) = gram h.toSesq v := by
  constructor
  · intro hg
    ext i j
    rw [← sesq_apply_map_basis]
    exact hg _ _
  · intro hM x y
    have key : (h.toSesq.comp (g : V →ₗ[E] V)).compl₂ (g : V →ₗ[E] V) = h.toSesq := by
      refine LinearMap.ext_basis v v fun i j => ?_
      have := congrFun (congrFun hM i) j
      rw [← sesq_apply_map_basis] at this
      simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
      simpa [gram_apply] using this
    exact LinearMap.congr_fun₂ key x y
noncomputable def autEquivGL (v : Basis ι E V) : (V ≃ₗ[E] V) ≃* GL ι E :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv E V).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv v).toRingEquiv.toMulEquiv)
theorem autEquivGL_apply (v : Basis ι E V) (g : V ≃ₗ[E] V) :
    (autEquivGL v g : Matrix ι ι E) = LinearMap.toMatrix v v (g : V →ₗ[E] V) := by
  simp [autEquivGL]
  rfl
noncomputable def unitaryGroupEquivMatrix (h : HermitianForm F E V) (v : Basis ι E V) :
    h.unitaryGroup ≃* unitaryGroupMatrix (conjHom F E) (gram h.toSesq v) where
  toFun g := ⟨autEquivGL v g, by
    rw [mem_unitaryGroupMatrix, autEquivGL_apply]
    exact (mem_unitaryGroup_iff_toMatrix h v g).1 g.2⟩
  invFun m := ⟨(autEquivGL v).symm m, by
    rw [mem_unitaryGroup_iff_toMatrix h v, ← autEquivGL_apply, MulEquiv.apply_symm_apply]
    exact m.2⟩
  left_inv g := Subtype.ext (by simp)
  right_inv m := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    change autEquivGL v ((a : V ≃ₗ[E] V) * b) = autEquivGL v a * autEquivGL v b
    exact map_mul _ _ _)
end GroundTheory.Automorphic


