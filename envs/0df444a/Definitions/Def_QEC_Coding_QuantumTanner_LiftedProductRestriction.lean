-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductRestriction
-- name    : QEC_Coding_QuantumTanner_LiftedProductRestriction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T11:05:16.303283+00:00
-- url     : https://prove2.me/theorems/c8949a09-6db1-4404-b998-86dfada90d14
-- title:
--   Lifted Product Restriction
-- statement:
--   Definitions and structural lemmas for Lifted Product Restriction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductRestriction.lean

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.MonoidAlgebra.Basic
set_option autoImplicit false
namespace QEC.Coding.QuantumTanner.LiftedProductRestriction
variable {R A B C D C' D' : Type*} [Ring R]
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [Fintype C'] [Fintype D']
def zRetained (hA HA : Matrix C A R) (U0 U1 : Matrix C B R) : Matrix A B R :=
  hA.transpose * U0 + HA.transpose * U1
def xRetained (hB HB : Matrix D B R) (V0 V1 : Matrix A D R) : Matrix A B R :=
  V0 * hB + V1 * HB
def zAuxiliary (hB HB : Matrix D B R) (U0 U1 : Matrix C B R) :
    Matrix (Bool × C) (Bool × D) R :=
  fun c d =>
    if c.1 then
      if d.1 then (U1 * HB.transpose) c.2 d.2 else (U1 * hB.transpose) c.2 d.2
    else
      if d.1 then (U0 * HB.transpose) c.2 d.2 else (U0 * hB.transpose) c.2 d.2
def xAuxiliary (hA HA : Matrix C A R) (V0 V1 : Matrix A D R) :
    Matrix (Bool × C) (Bool × D) R :=
  fun c d =>
    if c.1 then
      if d.1 then (HA * V1) c.2 d.2 else (HA * V0) c.2 d.2
    else
      if d.1 then (hA * V1) c.2 d.2 else (hA * V0) c.2 d.2
def selectedZRetained (hA HA : Matrix C A R) (gB GB : Matrix D' B R)
    (U0 U1 : Matrix C D' R) : Matrix A B R :=
  zRetained hA HA (U0 * GB) (U1 * gB)
def selectedXRetained (hB HB : Matrix D B R) (gA GA : Matrix C' A R)
    (V0 V1 : Matrix C' D R) : Matrix A B R :=
  xRetained hB HB (gA.transpose * V0) (GA.transpose * V1)
noncomputable section GroupAlgebra
variable {F G I J K : Type*} [CommRing F] [Group G] [Fintype K]
def twistedMatrix (h : Matrix I K F) (s : K → G) : Matrix I K (MonoidAlgebra F G) :=
  fun i k => MonoidAlgebra.single (s k) (h i k)
def scalarMatrix (h : Matrix I K F) : Matrix I K (MonoidAlgebra F G) :=
  twistedMatrix h (fun _ => 1)
end GroupAlgebra
end QEC.Coding.QuantumTanner.LiftedProductRestriction


