-- Prove2me | Definitions.Def_LeanPool_QECCertificates_GF2_HGP
-- name    : LeanPool_QECCertificates_GF2_HGP
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:41:57.380641+00:00
-- url     : https://prove2.me/theorems/63096aa2-c1e7-4b1c-aef6-409dc27fb8c8
-- title:
--   HGP
-- statement:
--   Definitions and structural lemmas for HGP, from Shuoming An; LeanPool contributors's pinned Quantum code certificates and hypergraph-product theory development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGP.lean

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QECCertificates
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
def hgpHX (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    Matrix (Fin r₁ × Fin n₂) ((Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂)) (ZMod 2) :=
  fun x c => Sum.elim
    (fun ab => H₁ x.1 ab.1 * (if x.2 = ab.2 then 1 else 0))
    (fun st => (if x.1 = st.1 then 1 else 0) * H₂ st.2 x.2) c
def hgpHZ (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    Matrix (Fin n₁ × Fin r₂) ((Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂)) (ZMod 2) :=
  fun x c => Sum.elim
    (fun ab => (if x.1 = ab.1 then 1 else 0) * H₂ x.2 ab.2)
    (fun st => H₁ st.1 x.1 * (if x.2 = st.2 then 1 else 0)) c
end QECCertificates


