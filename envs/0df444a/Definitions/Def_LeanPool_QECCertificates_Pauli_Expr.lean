-- Prove2me | Definitions.Def_LeanPool_QECCertificates_Pauli_Expr
-- name    : LeanPool_QECCertificates_Pauli_Expr
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:46:30.519436+00:00
-- url     : https://prove2.me/theorems/da307be1-bec4-4f8e-b153-a0b2fd59ecf3
-- title:
--   Expr
-- statement:
--   Definitions and structural lemmas for Expr, from Shuoming An; LeanPool contributors's pinned Quantum code certificates and hypergraph-product theory development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_kerL
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QECCertificates
open scoped BigOperators
variable {n : ℕ}
inductive Pauli where
  | I | X | Y | Z
  deriving DecidableEq, Repr
instance : Fintype Pauli where
  elems := {.I, .X, .Y, .Z}
  complete := by intro p; cases p <;> simp
namespace Pauli
def mul : Pauli → Pauli → Pauli
  | .I, q => q
  | p, .I => p
  | .X, .X => .I
  | .X, .Y => .Z
  | .X, .Z => .Y
  | .Y, .X => .Z
  | .Y, .Y => .I
  | .Y, .Z => .X
  | .Z, .X => .Y
  | .Z, .Y => .X
  | .Z, .Z => .I
def symp : Pauli → ZMod 2 × ZMod 2
  | .I => (0, 0)
  | .X => (0, 1)
  | .Y => (1, 1)
  | .Z => (1, 0)
def anti : Pauli → Pauli → ZMod 2
  | .I, _ => 0
  | _, .I => 0
  | .X, .X => 0
  | .Y, .Y => 0
  | .Z, .Z => 0
  | _, _ => 1
end Pauli
abbrev PauliWord (n : ℕ) := Fin n → Pauli
def sympWord (w : PauliWord n) : Vec n × Vec n :=
  ((fun i => (Pauli.symp (w i)).1), (fun i => (Pauli.symp (w i)).2))
def commutesWord (u v : PauliWord n) : Prop := (∑ i, Pauli.anti (u i) (v i)) = 0
inductive PauliExpr (n : ℕ) where
  /-- Place the single-site Pauli `p` at position `i`. -/
  | atom (i : Fin n) (p : Pauli)
  /-- The identity operator. -/
  | one
  /-- A multiplication node. -/
  | mul (a b : PauliExpr n)
namespace PauliExpr
def eval : PauliExpr n → PauliWord n
  | .atom i p => fun j => if j = i then p else .I
  | .one => fun _ => .I
  | .mul a b => fun i => Pauli.mul (eval a i) (eval b i)
def toSymp (e : PauliExpr n) : Vec n × Vec n := sympWord (eval e)
def commutes (a b : PauliExpr n) : Prop := commutesWord (eval a) (eval b)
end PauliExpr
end QECCertificates


