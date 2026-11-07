-- Prove2me | Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
-- name    : QEC_Coding_QuditQubitConversion_SelfDualBasis
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T11:11:28.236046+00:00
-- url     : https://prove2.me/theorems/59d765bf-788b-46ab-a124-adf9f897ceae
-- title:
--   Self Dual Basis
-- statement:
--   Definitions and structural lemmas for Self Dual Basis, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/SelfDualBasis.lean

import Definitions.Def_QEC_Coding_QuditQubitConversion_FiniteField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic
set_option autoImplicit false
open Polynomial
open scoped Matrix
namespace QEC.Coding
noncomputable instance : CharP F1024 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F1024).injective 2
def f1024SelectedSelfDualP : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  !![1, 0, 0, 1, 1, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1, 0, 0, 0, 0;
     1, 0, 1, 1, 0, 1, 1, 1, 0, 0;
     0, 1, 0, 1, 0, 1, 0, 0, 1, 0;
     1, 0, 0, 1, 1, 0, 0, 0, 0, 1;
     1, 0, 1, 0, 1, 0, 0, 1, 0, 0;
     0, 1, 0, 1, 0, 0, 1, 0, 0, 1;
     1, 1, 1, 1, 1, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 0, 0, 0, 0, 0]
def f1024SelectedSelfDualPInv : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  !![1, 0, 1, 1, 0, 1, 1, 0, 0, 0;
     1, 1, 0, 0, 1, 1, 1, 1, 0, 1;
     1, 0, 1, 0, 0, 0, 0, 1, 1, 0;
     1, 1, 0, 1, 1, 0, 0, 0, 0, 1;
     1, 0, 1, 1, 0, 1, 1, 0, 1, 1;
     1, 0, 0, 0, 1, 1, 1, 1, 0, 0;
     1, 1, 0, 0, 0, 1, 0, 1, 1, 0;
     1, 0, 1, 0, 0, 1, 0, 1, 0, 1;
     1, 0, 0, 0, 1, 0, 0, 0, 0, 0;
     1, 1, 0, 1, 0, 0, 0, 0, 1, 0]
def f1024PolynomialTraceGram : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0, 0, 1;
     0, 1, 0, 0, 0, 0, 0, 0, 1, 0;
     1, 0, 0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0, 0, 1;
     0, 0, 0, 0, 0, 1, 0, 0, 1, 0]
theorem f1024SelectedSelfDualP_mul_inv :
    f1024SelectedSelfDualP * f1024SelectedSelfDualPInv = 1 := by decide
theorem f1024SelectedSelfDualP_det_isUnit : IsUnit f1024SelectedSelfDualP.det :=
  Matrix.isUnit_det_of_right_inverse f1024SelectedSelfDualP_mul_inv
noncomputable def f1024SelectedSelfDualChange : F1024 ≃ₗ[ZMod 2] F1024 :=
  Matrix.toLinearEquiv f1024PolynomialBasis f1024SelectedSelfDualP f1024SelectedSelfDualP_det_isUnit
noncomputable def f1024SelectedSelfDualBasis : Module.Basis (Fin 10) (ZMod 2) F1024 :=
  f1024PolynomialBasis.map f1024SelectedSelfDualChange
noncomputable def f1024SelectedCoordinates : F1024 ≃ₗ[ZMod 2] (Fin 10 → ZMod 2) :=
  f1024SelectedSelfDualBasis.equivFun
end QEC.Coding


