-- Prove2me | Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
-- name    : LeanPool_QECCertificates_GF2_RankEchelon
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:46:29.680242+00:00
-- url     : https://prove2.me/theorems/26568150-6093-40ee-912a-d3fc7511fb84
-- title:
--   Rank Echelon
-- statement:
--   Definitions and structural lemmas for Rank Echelon, from Shuoming An; LeanPool contributors's pinned Quantum code certificates and hypergraph-product theory development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
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
def insertPivotA (D : List (PivRow n)) (w : Vec n) (p : Fin n) : List (PivRow n) :=
  D ++ [(w, p)]
def stepA (D : List (PivRow n)) (v : Vec n) : List (PivRow n) :=
  if hw : reduceAgainst D v = 0 then D
  else insertPivotA D (reduceAgainst D v) (leadIdx (reduceAgainst D v) hw)
def echelonFrom (L : List (Vec n)) : List (PivRow n) := L.foldl stepA []
def rankEchelon (L : List (Vec n)) : ℕ := (echelonFrom L).length
def EchSelf (D : List (PivRow n)) : Prop := ∀ i : Fin D.length, (D.get i).1 (D.get i).2 = 1
def EchPair (D : List (PivRow n)) : Prop :=
  ∀ i j : Fin D.length, i < j → (D.get j).1 (D.get i).2 = 0
lemma length_append_singleton (D : List (PivRow n)) (x : PivRow n) :
    (D ++ [x]).length = D.length + 1 := by simp [List.length_append]
def inSpanEch (L : List (Vec n)) (v : Vec n) : Bool :=
  decide (reduceAgainst (echelonFrom L) v = 0)
end QECCertificates


