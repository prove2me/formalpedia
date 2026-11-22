-- Prove2me | Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
-- name    : LeanPool_QECCertificates_GF2_KernelBasis
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:44:54.379824+00:00
-- url     : https://prove2.me/theorems/d7d1efcb-401c-4deb-a233-46d4938eee20
-- title:
--   Kernel Basis
-- statement:
--   Definitions and structural lemmas for Kernel Basis, from Shuoming An; LeanPool contributors's pinned Quantum code certificates and hypergraph-product theory development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QECCertificates
open scoped BigOperators
variable {n : ℕ}
def unitVec (i : Fin n) : Vec n := fun j => if j = i then 1 else 0
@[simp] lemma unitVec_apply (i j : Fin n) : unitVec i j = if j = i then 1 else 0 := rfl
def kerL (L : List (Vec n)) : Submodule (ZMod 2) (Vec n) where
  carrier := {x | ∀ r ∈ L, r ⬝ᵥ x = 0}
  zero_mem' := by intro r _; simp
  add_mem' := by
    intro x y hx hy r hr
    rw [dotProduct_add, hx r hr, hy r hr, add_zero]
  smul_mem' := by
    intro c x hx r hr
    rw [dotProduct_smul, hx r hr, smul_zero]
def pivCols (D : List (PivRow n)) : Finset (Fin n) := (D.map (·.2)).toFinset
def IsFreeCol (D : List (PivRow n)) (j : Fin n) : Prop := ∀ ri ∈ D, ri.2 ≠ j
def kerVec (D : List (PivRow n)) (j : Fin n) : Vec n :=
  fun i => (if i = j then 1 else 0) + ∑ ri ∈ D.toFinset, (if ri.2 = i then ri.1 j else 0)
def kerBasis (D : List (PivRow n)) : List (Vec n) :=
  ((List.finRange n).filter (fun j => decide (j ∉ pivCols D))).map (kerVec D)
end QECCertificates


