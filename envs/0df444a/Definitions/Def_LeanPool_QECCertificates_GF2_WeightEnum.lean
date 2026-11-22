-- Prove2me | Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
-- name    : LeanPool_QECCertificates_GF2_WeightEnum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:41:59.266812+00:00
-- url     : https://prove2.me/theorems/aa6e279f-18cb-4129-803f-68141d85258a
-- title:
--   Weight Enum
-- statement:
--   Definitions and structural lemmas for Weight Enum, from Shuoming An; LeanPool contributors's pinned Quantum code certificates and hypergraph-product theory development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/WeightEnum.lean

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QECCertificates
open scoped BigOperators
variable {n : ℕ}
def snocV {n : ℕ} (u : Vec n) (b : ZMod 2) : Vec (n + 1) :=
  fun i => if h : (i : ℕ) < n then u ⟨i, h⟩ else b
def wtRec : (n : ℕ) → Vec n → ℕ
  | 0, _ => 0
  | n + 1, v => wtRec n (fun i => v i.castSucc) + (if v (Fin.last n) = 0 then 0 else 1)
def lightVecs : (n w : ℕ) → List (Vec n)
  | 0, _ => [0]
  | _ + 1, 0 => [0]
  | n + 1, w + 1 =>
      (lightVecs n (w + 1)).map (fun u => snocV u 0) ++ (lightVecs n w).map (fun u => snocV u 1)
end QECCertificates


