-- Prove2me | Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
-- name    : LeanPool_QECCertificates_GF2_HGPCleaning
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:45:58.167122+00:00
-- url     : https://prove2.me/theorems/c28f6478-cc03-4cc2-9cec-0477bb39133f
-- title:
--   HGPCleaning
-- statement:
--   Definitions and structural lemmas for HGPCleaning, from Shuoming An; LeanPool contributors's pinned Quantum code certificates and hypergraph-product theory development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
def matRowList {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2)) : List (Vec k) :=
  List.ofFn fun i => fun j => M i j
def colList {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2)) : List (Vec m) :=
  matRowList M.transpose
noncomputable def preimage {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2)) (y : Vec m) : Vec k :=
  if h : ∃ x : Vec k, M *ᵥ x = y then Classical.choose h else 0
end QECCertificates


