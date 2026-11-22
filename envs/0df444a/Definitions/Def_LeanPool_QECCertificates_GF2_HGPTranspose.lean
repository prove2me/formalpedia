-- Prove2me | Definitions.Def_LeanPool_QECCertificates_GF2_HGPTranspose
-- name    : LeanPool_QECCertificates_GF2_HGPTranspose
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:42:47.52793+00:00
-- url     : https://prove2.me/theorems/04c556f9-79d1-49a6-af25-2604315ccbdb
-- title:
--   HGPTranspose
-- statement:
--   Definitions and structural lemmas for HGPTranspose, from Shuoming An; LeanPool contributors's pinned Quantum code certificates and hypergraph-product theory development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPTranspose.lean

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
def swapBlocks {α β : Type*} : α ⊕ β → β ⊕ α := Sum.swap
end QECCertificates


