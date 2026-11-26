-- Prove2me | Definitions.Def_Scott1976_DataTypesAsLattices_Enumeration
-- name    : Scott1976_DataTypesAsLattices_Enumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:54:51.043567+00:00
-- url     : https://prove2.me/theorems/1342ffd1-3c36-45db-bf42-47dde4454fc2
-- title:
--   Enumeration
-- statement:
--   Definitions and structural lemmas for Enumeration, from Lars Warren Ericson (catskillsresearch/scott1976; original Lean code Apache-2.0; non-Lean reference PDF excluded per NOTICE)'s pinned Dana Scott's Data Types as Lattices (1976): Pomega, continuous functions, fixed points, and lambda models development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Enumeration.lean

import Definitions.Def_Scott1976_DataTypesAsLattices_Computability
set_option autoImplicit true
namespace Scott1976.DataTypesAsLattices
def Gpack : Pomega :=
  seq2 sucC (seq2 predC (seq2 condC (seq2 Kcomb Scomb)))
def Gcomb : Pomega :=
  graph (fun z => condSet z Gpack zeroC)
def applyNat (n m : ℕ) : ℕ := pair n m + 1
def valStep (v : Pomega) : Pomega :=
  graph (fun k =>
    condSet k Gcomb
      {j | ∃ n m, pair n m + 1 ∈ k ∧
        j ∈ funOf (funOf v (ofNat n)) (funOf v (ofNat m))})
def valC : Pomega := fix valStep
def RE : Set Pomega := {u | IsCombinatory u}
def num : ℕ → ℕ
  | 0 => 1
  | n + 1 => applyNat 12 (num n)
def recNat (v : ℕ → ℕ) (n : ℕ) : ℕ :=
  applyNat (v n) (num (v n))
def IsExtensional (val : ℕ → Pomega) (p : ℕ → ℕ) : Prop :=
  ∀ n m, val n = val m → val (p n) = val (p m)
def Deg (a : Pomega) : Set Pomega :=
  {u | ∃ r, IsCombinatory r ∧ u = funOf r a}
def Rcomb : Pomega := graph (fun x => seq2 (ofNat 0) x)
def Lcomb : Pomega :=
  graph (fun x => funOf (funOf x (ofNat 1)) (funOf x (ofNat 2)))
def TOT : Set Pomega :=
  {u | ∀ n, ∃ k, funOf u (ofNat n) = ofNat k}
end Scott1976.DataTypesAsLattices


