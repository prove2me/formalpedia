-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductActionBridge
-- name    : QEC_Coding_QuantumTanner_LiftedProductActionBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T11:08:36.736505+00:00
-- url     : https://prove2.me/theorems/64f016d5-9fe9-49cd-be23-a935ec48aa27
-- title:
--   Lifted Product Action Bridge
-- statement:
--   Definitions and structural lemmas for Lifted Product Action Bridge, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductRestriction
set_option autoImplicit false
namespace QEC.Coding.QuantumTanner.LiftedProductActionBridge
open QEC.Coding.LiftedProduct
open QEC.Coding.QuantumTanner.LiftedProductRestriction
noncomputable section
variable {G A B C D : Type*} [Group G] [Fintype G] [DecidableEq G]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
def canonicalData (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (a : A → G) (b : B → G) : Data (ZMod 2) G (Bool × D) B A (Bool × C) where
  A := fun d k => if d.1 then twistedMatrix hB b d.2 k else scalarMatrix hB d.2 k
  B := fun k c => if c.1 then twistedMatrix hA (fun i => (a i)⁻¹) c.2 k
    else scalarMatrix hA c.2 k
def retainedCoordinate (a : A) (b : B) (g : G) :
    QubitIndex (Bool × D) B A (Bool × C) G := Sum.inl (b, a, g)
def auxiliaryCoordinate (c : Bool × C) (d : Bool × D) (g : G) :
    QubitIndex (Bool × D) B A (Bool × C) G := Sum.inr (d, c, g)
def zWord (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (a : A → G) (b : B → G) (U : C2Index B (Bool × C) G → ZMod 2) :=
  (boundary2Matrix (canonicalData hA hB a b)).mulVec U
def xWord (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (a : A → G) (b : B → G) (V : C0Index (Bool × D) A G → ZMod 2) :=
  (boundary1Matrix (canonicalData hA hB a b)).transpose.mulVec V
def zParameter (U0 U1 : Matrix C B (MonoidAlgebra (ZMod 2) G)) :
    C2Index B (Bool × C) G → ZMod 2 :=
  fun (j, (s, c), u) => (if s then U1 c j else U0 c j).coeff u
def xParameter (V0 V1 : Matrix A D (MonoidAlgebra (ZMod 2) G)) :
    C0Index (Bool × D) A G → ZMod 2 :=
  fun ((t, d), i, u) => (if t then V1 i d else V0 i d).coeff u
variable {C' D' : Type*} [Fintype C'] [Fintype D']
end
end QEC.Coding.QuantumTanner.LiftedProductActionBridge


