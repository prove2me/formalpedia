-- Prove2me | Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
-- name    : LeanPool_QECCertificates_GF2_LiftedProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:43:38.788498+00:00
-- url     : https://prove2.me/theorems/ca13aad3-1883-4c0a-ad8e-8bd5f7ba8a98
-- title:
--   Lifted Product
-- statement:
--   Definitions and structural lemmas for Lifted Product, from Shuoming An; LeanPool contributors's pinned Quantum code certificates and hypergraph-product theory development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]
def leftMulMat (a : G → ZMod 2) : Matrix G G (ZMod 2) := fun σ τ => a (σ * τ⁻¹)
def rightMulMat (b : G → ZMod 2) : Matrix G G (ZMod 2) := fun σ τ => b (τ⁻¹ * σ)
def mulLeftEquiv (g : G) : G ≃ G where
  toFun x := g * x
  invFun x := g⁻¹ * x
  left_inv x := by simp
  right_inv x := by simp
def invMulEquiv (g : G) : G ≃ G where
  toFun x := x⁻¹ * g
  invFun y := g * y⁻¹
  left_inv x := by simp
  right_inv y := by simp
def lpExpandR {mA nA : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2)) :
    Matrix (Fin mA × G) (Fin nA × G) (ZMod 2) :=
  fun x y => A x.1 y.1 (x.2 * y.2⁻¹)
def lpExpandL {mB nB : ℕ} (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2)) :
    Matrix (Fin mB × G) (Fin nB × G) (ZMod 2) :=
  fun x y => B x.1 y.1 (y.2⁻¹ * x.2)
def lpHX {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2)) :
    Matrix ((Fin mA × Fin mB) × G)
      (((Fin nA × Fin mB) × G) ⊕ ((Fin mA × Fin nB) × G)) (ZMod 2) :=
  fun x c => Sum.elim
    (fun y => lpExpandR A (x.1.1, x.2) (y.1.1, y.2) * (if x.1.2 = y.1.2 then 1 else 0))
    (fun y => (if x.1.1 = y.1.1 then 1 else 0) * lpExpandL B (x.1.2, x.2) (y.1.2, y.2)) c
def lpHZ {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2)) :
    Matrix ((Fin nA × Fin nB) × G)
      (((Fin nA × Fin mB) × G) ⊕ ((Fin mA × Fin nB) × G)) (ZMod 2) :=
  fun x c => Sum.elim
    (fun y => (if x.1.1 = y.1.1 then 1 else 0) * lpExpandL B (y.1.2, y.2) (x.1.2, x.2))
    (fun y => lpExpandR A (y.1.1, y.2) (x.1.1, x.2) * (if x.1.2 = y.1.2 then 1 else 0)) c
def lp2HX (a b : G → ZMod 2) : Matrix G (G ⊕ G) (ZMod 2) :=
  fun σ c => Sum.elim (fun τ => leftMulMat a σ τ) (fun τ => rightMulMat b σ τ) c
def lp2HZ (a b : G → ZMod 2) : Matrix G (G ⊕ G) (ZMod 2) :=
  fun σ c => Sum.elim (fun τ => rightMulMat b τ σ) (fun τ => leftMulMat a τ σ) c
def liftConst [DecidableEq G] {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    Matrix (Fin m) (Fin n) (G → ZMod 2) :=
  fun i j g => M i j * (if g = 1 then 1 else 0)
end QECCertificates


