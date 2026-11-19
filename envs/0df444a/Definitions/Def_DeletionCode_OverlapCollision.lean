-- Prove2me | Definitions.Def_DeletionCode_OverlapCollision
-- name    : DeletionCode_OverlapCollision
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:26:19.421509+00:00
-- url     : https://prove2.me/theorems/32214fad-5363-43f5-99e9-52a57ed8de94
-- title:
--   Overlap Collision
-- statement:
--   Definitions and structural lemmas for Overlap Collision, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OverlapCollision.lean

import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega
set_option autoImplicit true
namespace DeletionCode.OverlapCollision
open Windows HeaderRecovery
abbrev Collision (n k a b : ℕ) :=
  {x : Bits n // Agree (padBits x) a (padBits x) b k}
noncomputable instance collisionFintype (n k a b : ℕ) :
    Fintype (Collision n k a b) := by
  classical
  unfold Collision
  infer_instance
def keptIndex (n k b : ℕ) (hb : b + k ≤ n) (i : Fin (n - k)) : Fin n :=
  if h : i.val < b then ⟨i.val, by omega⟩
  else ⟨i.val + k, by omega⟩
def encode (n k b : ℕ) (hb : b + k ≤ n) (x : Bits n) : Bits (n - k) :=
  fun i => x (keptIndex n k b hb i)
def collisionEncode (n k a b : ℕ) (hb : b + k ≤ n) :
    Collision n k a b → Bits (n - k) :=
  fun x => encode n k b hb x.val
end DeletionCode.OverlapCollision


