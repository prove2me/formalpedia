-- Prove2me | Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
-- name    : LeanPool_QECCertificates_Reflect_Complete
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:41:55.353809+00:00
-- url     : https://prove2.me/theorems/ac918268-6861-473e-aeff-16f7ff12cb30
-- title:
--   Complete
-- statement:
--   Definitions and structural lemmas for Complete, from Shuoming An; LeanPool contributors's pinned Quantum code certificates and hypergraph-product theory development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QECCertificates.LRAT
def chainFill (σ : Assign) : List Nat → Bool → Nat → Nat → Bool
  | [], _, _, _ => false
  | x :: rest, acc, c, t =>
      if t = c then (acc ^^ σ x)
      else chainFill σ rest (acc ^^ σ x) (c + 1) t
def chainAssign (σ : Assign) (rest : List Nat) (acc : Bool) (c : Nat) : Assign :=
  fun t => if t < c then σ t else chainFill σ rest acc c t
def prodFill (σ : Assign) (c n : Nat) : Assign :=
  fun t => if c ≤ t ∧ t < c + n then (σ (t - c) && σ (n + (t - c))) else σ t
def rowFill (τ : Assign) (c k i cnt : Nat) : Assign :=
  fun t => if c + slotBase k i ≤ t ∧ t < c + slotBase k i + min i (k + 1) then
      decide ((t - (c + slotBase k i)) + 1 ≤ cnt)
    else τ t
end QECCertificates.LRAT


