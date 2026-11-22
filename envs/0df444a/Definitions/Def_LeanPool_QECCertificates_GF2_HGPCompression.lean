-- Prove2me | Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
-- name    : LeanPool_QECCertificates_GF2_HGPCompression
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:42:15.031035+00:00
-- url     : https://prove2.me/theorems/d10c0e5b-b0d0-4716-aef4-6f69d9f42197
-- title:
--   HGPCompression
-- statement:
--   Definitions and structural lemmas for HGPCompression, from Shuoming An; LeanPool contributors's pinned Quantum code certificates and hypergraph-product theory development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
def blockL (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    Matrix (Fin n₁) (Fin n₂) (ZMod 2) :=
  fun a b => v (Sum.inl (a, b))
def blockR (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    Matrix (Fin r₁) (Fin r₂) (ZMod 2) :=
  fun s t => v (Sum.inr (s, t))
end QECCertificates


