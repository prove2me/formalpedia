-- Prove2me | Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
-- name    : LeanPool_QECCertificates_GF2_Canonical
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:45:38.562506+00:00
-- url     : https://prove2.me/theorems/e4c7703c-fa05-479b-962f-152e338152f2
-- title:
--   Canonical
-- statement:
--   Definitions and structural lemmas for Canonical, from Shuoming An; LeanPool contributors's pinned Quantum code certificates and hypergraph-product theory development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QECCertificates
open scoped BigOperators
variable {n : ℕ}
def readOff (D : List (PivRow n)) (w : Vec n) : Vec n :=
  ∑ ri ∈ D.toFinset, (w ri.2) • ri.1
def IsEchelon (D : List (PivRow n)) : Prop :=
  IsReduced D ∧ ∀ ri ∈ D, ∀ i : Fin n, i < ri.2 → ri.1 i = 0
end QECCertificates


