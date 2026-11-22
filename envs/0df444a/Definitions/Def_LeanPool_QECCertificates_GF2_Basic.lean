-- Prove2me | Definitions.Def_LeanPool_QECCertificates_GF2_Basic
-- name    : LeanPool_QECCertificates_GF2_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:41:32.326797+00:00
-- url     : https://prove2.me/theorems/1505331e-bd94-4110-a702-8815435567b4
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Shuoming An; LeanPool contributors's pinned Quantum code certificates and hypergraph-product theory development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QECCertificates
open scoped BigOperators
abbrev Vec (n : ℕ) := Fin n → ZMod 2
variable {n : ℕ}
def e {n : ℕ} (i : Fin n) : Vec n := fun j => if j = i then 1 else 0
def zeroRows (n : ℕ) : Matrix (Fin 0) (Fin n) (ZMod 2) := fun i => i.elim0
def support (v : Vec n) : Finset (Fin n) := Finset.univ.filter (fun i => v i ≠ 0)
def spanL (L : List (Vec n)) : Submodule (ZMod 2) (Vec n) :=
  Submodule.span (ZMod 2) {x | x ∈ L}
def addSmul (v r : Vec n) (c : ZMod 2) : Vec n := v + c • r
end QECCertificates


