-- Prove2me | Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
-- name    : QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:07:57.333084+00:00
-- url     : https://prove2.me/theorems/fef4469f-86f8-4b4e-be9a-37ed6791bf74
-- title:
--   Self Dual Basis
-- statement:
--   Definitions and structural lemmas for Self Dual Basis, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/SelfDualBasis.lean

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Field
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic
set_option autoImplicit false
open Polynomial
open scoped Matrix
namespace QEC.Coding
noncomputable def f256Alpha : F256 := AdjoinRoot.root f256Modulus
noncomputable instance : CharP F256 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
def f256SelfDualP : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 1, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 1, 1, 1;
     0, 0, 1, 0, 1, 1, 0, 1;
     1, 1, 1, 1, 0, 1, 1, 0;
     0, 0, 0, 1, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1, 1, 1]
def f256SelfDualPInv : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 1, 1, 1, 0, 0, 1;
     1, 0, 0, 0, 0, 0, 0, 0;
     1, 1, 1, 0, 0, 1, 0, 1;
     1, 1, 0, 0, 1, 0, 1, 0;
     1, 1, 0, 0, 0, 0, 0, 1;
     1, 1, 0, 0, 0, 0, 1, 0;
     1, 1, 0, 0, 0, 1, 0, 0;
     1, 1, 0, 0, 0, 1, 1, 0]
def f256PolynomialTraceGram : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 0, 0, 1, 0, 1, 1, 1;
     0, 0, 1, 0, 1, 1, 1, 0;
     0, 1, 0, 1, 1, 1, 0, 0;
     1, 0, 1, 1, 1, 0, 0, 1;
     0, 1, 1, 1, 0, 0, 1, 1;
     1, 1, 1, 0, 0, 1, 1, 1;
     1, 1, 0, 0, 1, 1, 1, 0;
     1, 0, 0, 1, 1, 1, 0, 1]
theorem f256SelfDualP_mul_inv : f256SelfDualP * f256SelfDualPInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide
theorem f256SelfDualP_det : f256SelfDualP.det = 1 := by
  have hdet : f256SelfDualP.det * f256SelfDualPInv.det = 1 := by
    rw [← Matrix.det_mul, f256SelfDualP_mul_inv, Matrix.det_one]
  have hne : f256SelfDualP.det ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hdet
    exact zero_ne_one hdet
  exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hne
theorem f256SelfDualP_det_isUnit : IsUnit f256SelfDualP.det := by
  rw [f256SelfDualP_det]
  exact isUnit_one
noncomputable def f256SelfDualChange : F256 ≃ₗ[ZMod 2] F256 :=
  Matrix.toLinearEquiv f256PolynomialBasis f256SelfDualP f256SelfDualP_det_isUnit
noncomputable def f256SelfDualBasis : Module.Basis (Fin 8) (ZMod 2) F256 :=
  f256PolynomialBasis.map f256SelfDualChange
end QEC.Coding


