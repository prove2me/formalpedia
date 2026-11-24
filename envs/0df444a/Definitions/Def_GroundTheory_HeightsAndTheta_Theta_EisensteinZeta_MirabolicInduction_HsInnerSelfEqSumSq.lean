-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq
-- name    : GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:38.347439+00:00
-- url     : https://prove2.me/theorems/b7df079c-5a4e-4788-aaaa-2e3db2a51b52
-- title:
--   Hs Inner Self Eq Sum Sq
-- statement:
--   Definitions and structural lemmas for Hs Inner Self Eq Sum Sq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Theorems.Thm_GroundTheory_Automorphic_indefJ_conjTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Theta
open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option linter.unusedSectionVars false
namespace SecondKind
namespace UnitaryRecombination
section HS
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def hsVec (X : Matrix ι ι ℂ) : EuclideanSpace ℂ (ι × ι) := WithLp.toLp 2 (fun ij => X ij.1 ij.2)
def hs (X : Matrix ι ι ℂ) : ℝ := ‖hsVec X‖
def tInner (X Y : Matrix ι ι ℂ) : ℝ := (trace (X * Yᴴ)).re
end HS
section Inner
variable {f : ℕ} {p q : Fin f → ℕ}
def hsInnerR (X : MatProd p q) : MatProd p q →ₗ[ℝ] ℝ where
  toFun Y := hsInner X Y
  map_add' Y Z := by
    simp only [hsInner, Pi.add_apply, conjTranspose_add, Matrix.mul_add, trace_add, Complex.add_re,
      Finset.sum_add_distrib]
  map_smul' c Y := by
    simp only [hsInner, Pi.smul_apply, conjTranspose_smul, star_trivial, Matrix.mul_smul,
      trace_smul, Complex.smul_re, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
end Inner
section Frame
def coords (F : OrthoFrame) (X : MatProd F.p F.q) : Fin F.dim → ℝ := fun k => hsInner (F.E k) X
end Frame
end UnitaryRecombination
namespace UnitaryRecombination
section ExpBound
end ExpBound
section Dim
variable (p q : ℕ)
def dag (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  indefJ p q * Xᴴ * indefJ p q
theorem J_mul_J_mul (Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    indefJ p q * (indefJ p q * Y) = Y := by
  rw [← Matrix.mul_assoc, indefJ_mul_self, Matrix.one_mul]
theorem dag_dag (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) : dag p q (dag p q X) = X := by
  simp only [dag, conjTranspose_mul, conjTranspose_conjTranspose, indefJ_conjTranspose,
    Matrix.mul_assoc, indefJ_mul_self, Matrix.mul_one]
  rw [J_mul_J_mul]
theorem dag_add (X Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    dag p q (X + Y) = dag p q X + dag p q Y := by
  simp only [dag, conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
theorem dag_sub (X Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    dag p q (X - Y) = dag p q X - dag p q Y := by
  simp only [dag, conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
theorem dag_smul (c : ℂ) (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    dag p q (c • X) = (starRingEnd ℂ c) • dag p q X := by
  simp only [dag, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Complex.star_def]
theorem dag_real_smul (c : ℝ) (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    dag p q (c • X) = c • dag p q X := by
  simp only [dag, conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul]
theorem mem_u_iff_dag {X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} :
    X ∈ indefiniteUnitaryLieAlgebra p q ↔ dag p q X = -X := by
  rw [mem_indefiniteUnitaryLieAlgebra_iff]
  constructor
  · intro h
    rw [dag, h]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, indefJ_mul_self, Matrix.mul_one]
    rw [J_mul_J_mul]
  · intro h
    have : Xᴴ = indefJ p q * dag p q X * indefJ p q := by
      rw [dag]
      simp only [Matrix.mul_assoc, indefJ_mul_self, Matrix.mul_one]
      rw [J_mul_J_mul]
    rw [this, h, Matrix.mul_neg, Matrix.neg_mul]
def skewPartU : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ →ₗ[ℝ] indefiniteUnitaryLieAlgebra p q where
  toFun X := ⟨(1 / 2 : ℂ) • (X - dag p q X), by
    rw [mem_u_iff_dag, dag_smul, dag_sub, dag_dag]
    simp only [map_div₀, map_one, map_ofNat]
    rw [← smul_neg, neg_sub]⟩
  map_add' X Y := by
    ext1
    simp only [dag_add, Submodule.coe_add]
    rw [← smul_add]; congr 1; abel
  map_smul' c X := by
    ext1
    simp only [dag_real_smul, RingHom.id_apply, SetLike.val_smul]
    rw [← smul_sub, smul_comm]
def hermPartU : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ →ₗ[ℝ] indefiniteUnitaryLieAlgebra p q where
  toFun X := ⟨(Complex.I / 2 : ℂ) • (X + dag p q X), by
    rw [mem_u_iff_dag, dag_smul, dag_add, dag_dag]
    simp only [map_div₀, Complex.conj_I, map_ofNat]
    rw [add_comm, neg_div, neg_smul]⟩
  map_add' X Y := by
    ext1
    simp only [dag_add, Submodule.coe_add]
    rw [← smul_add]; congr 1; abel
  map_smul' c X := by
    ext1
    simp only [dag_real_smul, RingHom.id_apply, SetLike.val_smul]
    rw [← smul_add, smul_comm]
def recombineU : (indefiniteUnitaryLieAlgebra p q × indefiniteUnitaryLieAlgebra p q) →ₗ[ℝ]
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ where
  toFun AB := (AB.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) - Complex.I • (AB.2 : Matrix _ _ ℂ)
  map_add' AB CD := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]; abel
  map_smul' c AB := by
    simp only [Prod.smul_fst, Prod.smul_snd, SetLike.val_smul, RingHom.id_apply, smul_sub]
    rw [smul_comm]
def matEquivU : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ ≃ₗ[ℝ]
    (indefiniteUnitaryLieAlgebra p q × indefiniteUnitaryLieAlgebra p q) :=
  { (skewPartU p q).prod (hermPartU p q) with
    invFun := recombineU p q
    left_inv := fun X => by
      change (1 / 2 : ℂ) • (X - dag p q X) - Complex.I • ((Complex.I / 2) • (X + dag p q X)) = X
      rw [smul_smul, show Complex.I * (Complex.I / 2) = - (1 / 2) by
          rw [mul_div_assoc', Complex.I_mul_I]; ring]
      module
    right_inv := fun AB => by
      obtain ⟨A, B⟩ := AB
      have hA := (mem_u_iff_dag p q).1 A.2
      have hB := (mem_u_iff_dag p q).1 B.2
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · change (1 / 2 : ℂ) • (((A : Matrix _ _ ℂ) - Complex.I • (B : Matrix _ _ ℂ)) -
          dag p q ((A : Matrix _ _ ℂ) - Complex.I • (B : Matrix _ _ ℂ))) = (A : Matrix _ _ ℂ)
        rw [dag_sub, dag_smul, hA, hB, Complex.conj_I]
        module
      · change (Complex.I / 2) • (((A : Matrix _ _ ℂ) - Complex.I • (B : Matrix _ _ ℂ)) +
          dag p q ((A : Matrix _ _ ℂ) - Complex.I • (B : Matrix _ _ ℂ))) = (B : Matrix _ _ ℂ)
        rw [dag_sub, dag_smul, hA, hB, Complex.conj_I]
        match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring }
end Dim
end UnitaryRecombination
namespace UnitaryRecombination
section Places
variable {ι : Type*} [Fintype ι]
def tInnerR (X : Matrix ι ι ℂ) : Matrix ι ι ℂ →ₗ[ℝ] ℝ where
  toFun Y := tInner X Y
  map_add' Y Z := by simp only [tInner, conjTranspose_add, Matrix.mul_add, trace_add, Complex.add_re]
  map_smul' c Y := by
    simp only [tInner, conjTranspose_smul, star_trivial, Matrix.mul_smul, trace_smul,
      Complex.smul_re, RingHom.id_apply, smul_eq_mul]
variable (F : OrthoFrame)
end Places
end UnitaryRecombination
namespace UnitaryRecombination
section Products
variable (F : OrthoFrame)
abbrev Mat (τ : Fin F.f) : Type :=
  Matrix (Fin (F.p τ) ⊕ Fin (F.q τ)) (Fin (F.p τ) ⊕ Fin (F.q τ)) ℂ
def Evec (τ : Fin F.f) (m : ℕ) : Mat F τ := if h : m < F.dim then F.E ⟨m, h⟩ τ else 0
def yy (y : Fin F.dim → ℝ) (m : ℕ) : ℝ := if h : m < F.dim then y ⟨m, h⟩ else 0
def G (y : Fin F.dim → ℝ) (τ : Fin F.f) : ℕ → Mat F τ
  | 0 => 1
  | m + 1 => NormedSpace.exp (yy F y m • Evec F τ m) * G y τ m
def Gi (y : Fin F.dim → ℝ) (τ : Fin F.f) : ℕ → Mat F τ
  | 0 => 1
  | m + 1 => Gi y τ m * NormedSpace.exp (-(yy F y m • Evec F τ m))
def IsU {p q : ℕ} (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) : Prop :=
  gᴴ * indefJ p q * g = indefJ p q
def cc (y : Fin F.dim → ℝ) (τ : Fin F.f) (m : ℕ) : ℝ :=
  if h : m < F.dim then (if F.place ⟨m, h⟩ = τ then |y ⟨m, h⟩| else 0) else 0
end Products
end UnitaryRecombination
end SecondKind
end
end GroundTheory.Heights₂.Theta


