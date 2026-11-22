-- Prove2me | Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
-- name    : LeanPool_QECCertificates_GF2_RowReduce
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:43:36.203134+00:00
-- url     : https://prove2.me/theorems/16ed0395-f9ab-4521-b4c8-8ba114e63d1b
-- title:
--   Row Reduce
-- statement:
--   Definitions and structural lemmas for Row Reduce, from Shuoming An; LeanPool contributors's pinned Quantum code certificates and hypergraph-product theory development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
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
variable {n : ℕ}
abbrev PivRow (n : ℕ) := Vec n × Fin n
def rowList (D : List (PivRow n)) : List (Vec n) := D.map (·.1)
@[simp] lemma rowList_nil : rowList ([] : List (PivRow n)) = [] := rfl
@[simp] lemma rowList_cons (ri : PivRow n) (D : List (PivRow n)) :
    rowList (ri :: D) = ri.1 :: rowList D := rfl
@[simp] lemma rowList_append (D E : List (PivRow n)) :
    rowList (D ++ E) = rowList D ++ rowList E := List.map_append
def IsReduced (D : List (PivRow n)) : Prop :=
  (∀ ri ∈ D, ri.1 ri.2 = 1) ∧ (∀ ri ∈ D, ∀ rj ∈ D, ri ≠ rj → ri.1 rj.2 = 0)
def reduceAgainst (D : List (PivRow n)) (v : Vec n) : Vec n :=
  D.foldl (fun w ri => w + (w ri.2) • ri.1) v
@[simp] lemma reduceAgainst_nil (v : Vec n) : reduceAgainst ([] : List (PivRow n)) v = v := rfl
lemma support_nonempty {v : Vec n} (h : v ≠ 0) :
    (Finset.univ.filter (fun i => v i ≠ 0)).Nonempty := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (funext hc)
  exact ⟨i, by simp [hi]⟩
def leadIdx (v : Vec n) (h : v ≠ 0) : Fin n :=
  (Finset.univ.filter (fun i => v i ≠ 0)).min' (support_nonempty h)
def insertPivot (D : List (PivRow n)) (w : Vec n) (p : Fin n) : List (PivRow n) :=
  D.map (fun ri => (ri.1 + (ri.1 p) • w, ri.2)) ++ [(w, p)]
def step (D : List (PivRow n)) (v : Vec n) : List (PivRow n) :=
  if hw : reduceAgainst D v = 0 then D
  else insertPivot D (reduceAgainst D v) (leadIdx (reduceAgainst D v) hw)
def rowReduceFrom (D : List (PivRow n)) : List (Vec n) → List (PivRow n)
  | [] => D
  | v :: rest => rowReduceFrom (step D v) rest
def rowReduce (L : List (Vec n)) : List (PivRow n) := rowReduceFrom [] L
end QECCertificates


