-- Prove2me | Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
-- name    : LeanPool_QECCertificates_Reflect_Distance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:46:20.273801+00:00
-- url     : https://prove2.me/theorems/5fdc849f-da20-4ae2-bf53-ecda7951886d
-- title:
--   Distance
-- statement:
--   Definitions and structural lemmas for Distance, from Shuoming An; LeanPool contributors's pinned Quantum code certificates and hypergraph-product theory development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QECCertificates.LRAT
def vecOf (σ : Assign) (n : ℕ) : Vec n := fun i => if σ i.val then 1 else 0
def rowOf (n : ℕ) (r : List Nat) : Vec n := fun i => if i.val ∈ r then 1 else 0
def certAssign (n : ℕ) (E w : Vec n) : Assign := fun t =>
  if h : t < n then decide (E ⟨t, h⟩ = 1)
  else if h2 : t < 2 * n then decide (w ⟨t - n, by omega⟩ = 1)
  else false
end QECCertificates.LRAT


