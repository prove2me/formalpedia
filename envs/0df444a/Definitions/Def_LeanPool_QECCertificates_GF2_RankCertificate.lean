-- Prove2me | Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
-- name    : LeanPool_QECCertificates_GF2_RankCertificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:45:19.296582+00:00
-- url     : https://prove2.me/theorems/17a1e5e6-ad14-47ce-bff2-a17a0f923edc
-- title:
--   Rank Certificate
-- statement:
--   Definitions and structural lemmas for Rank Certificate, from Shuoming An; LeanPool contributors's pinned Quantum code certificates and hypergraph-product theory development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QECCertificates
open scoped BigOperators
open _root_.Matrix
variable {n : ℕ}
def NodupPiv (D : List (PivRow n)) : Prop := (D.map (·.2)).Nodup
end QECCertificates


