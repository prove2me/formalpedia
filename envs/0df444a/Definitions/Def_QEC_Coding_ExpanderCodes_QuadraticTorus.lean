-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
-- name    : QEC_Coding_ExpanderCodes_QuadraticTorus
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T11:32:04.216198+00:00
-- url     : https://prove2.me/theorems/c414cdcd-d7cb-4ec7-864e-f4d5425dc8e1
-- title:
--   Quadratic Torus
-- statement:
--   Definitions and structural lemmas for Quadratic Torus, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticTorus.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionCayleySets
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.GroupTheory.Coset.Card
import Lean.Elab.Tactic.Omega
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_mem_center_of_val_scalar
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_alphaUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_baseUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_primeUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_alphaUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_baseUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_primeUnit


set_option autoImplicit false
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]
def coefficientEmbedding (f : F →+* K) (epsilon : F) (y : K) :
    QuadraticAlgebra F epsilon 0 →+* Model (f epsilon) y where
  toFun a := ⟨f a.re, f a.im, 0, 0⟩
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp <;> ring
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
def constantProjectiveMap (f : F →+* K) (epsilon : F) (y : K) :
    (QuadraticAlgebra F epsilon 0)ˣ →* ProjectiveGroup (f epsilon) y :=
  (QuotientGroup.mk' _).comp
    (Units.map (coefficientEmbedding f epsilon y).toMonoidHom)
def constantTorus (f : F →+* K) (epsilon : F) (y : K) :
    Subgroup (ProjectiveGroup (f epsilon) y) :=
  (constantProjectiveMap f epsilon y).range
def skewUnit (epsilon y : K) (hOne : 1 + y ≠ 0) : (Model epsilon y)ˣ where
  val := z epsilon y
  inv := ⟨0, 0, (1 + y)⁻¹, 0⟩
  val_inv := by ext <;> simp [z, hOne]
  inv_val := by ext <;> simp [z, hOne]
theorem constantProjectiveMap_eq_one_iff (f : F →+* K) (epsilon : F) (y : K)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
    (a : (QuadraticAlgebra F epsilon 0)ˣ) :
    constantProjectiveMap f epsilon y a = 1 ↔ (a : QuadraticAlgebra F epsilon 0).im = 0 := by
  let image := Units.map (coefficientEmbedding f epsilon y).toMonoidHom a
  change (image : ProjectiveGroup (f epsilon) y) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro hCenter
    have hCommute := Subgroup.mem_center_iff.mp hCenter (skewUnit (f epsilon) y hOne)
    have hCoordinate := congrArg (fun b : (Model (f epsilon) y)ˣ =>
      (b : Model (f epsilon) y).imK) hCommute
    simp [image, coefficientEmbedding, skewUnit, z] at hCoordinate
    have hDouble : (2 : K) * f (a : QuadraticAlgebra F epsilon 0).im = 0 := by
      linear_combination -hCoordinate
    have hZero := (mul_eq_zero.mp hDouble).resolve_left hTwo
    exact f.injective (by simpa using hZero)
  · intro hImag
    apply mem_center_of_val_scalar image (f (a : QuadraticAlgebra F epsilon 0).re)
    ext <;> simp [image, coefficientEmbedding, hImag]
def scalarUnitOfZeroImag (epsilon : F) (a : (QuadraticAlgebra F epsilon 0)ˣ)
    (hImag : (a : QuadraticAlgebra F epsilon 0).im = 0) : Fˣ where
  val := (a : QuadraticAlgebra F epsilon 0).re
  inv := a.inv.re
  val_inv := by
    have h := congrArg QuadraticAlgebra.re a.val_inv
    simpa only [QuadraticAlgebra.re_mul, hImag, mul_zero, zero_mul, add_zero,
      QuadraticAlgebra.re_one] using h
  inv_val := by
    have h := congrArg QuadraticAlgebra.re a.val_inv
    simpa only [QuadraticAlgebra.re_mul, hImag, mul_zero, zero_mul, add_zero,
      QuadraticAlgebra.re_one, mul_comm] using h
def constantKernelEquiv (f : F →+* K) (epsilon : F) (y : K)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    (constantProjectiveMap f epsilon y).ker ≃ Fˣ where
  toFun a := scalarUnitOfZeroImag epsilon a.val
    ((constantProjectiveMap_eq_one_iff f epsilon y hOne hTwo a.val).mp a.property)
  invFun a := ⟨Units.map (algebraMap F (QuadraticAlgebra F epsilon 0)).toMonoidHom a,
    (constantProjectiveMap_eq_one_iff f epsilon y hOne hTwo _).mpr (by simp)⟩
  left_inv a := by
    apply Subtype.ext
    apply Units.ext
    ext
    · rfl
    · exact ((constantProjectiveMap_eq_one_iff f epsilon y hOne hTwo a.val).mp
        a.property).symm
  right_inv a := by
    apply Units.ext
    rfl
end QEC.Coding.ExpanderCodes.QuaternionGenerators


