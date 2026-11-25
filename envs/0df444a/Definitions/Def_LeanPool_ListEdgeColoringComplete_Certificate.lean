-- Prove2me | Definitions.Def_LeanPool_ListEdgeColoringComplete_Certificate
-- name    : LeanPool_ListEdgeColoringComplete_Certificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T16:00:55.489053+00:00
-- url     : https://prove2.me/theorems/cf567b1b-4db7-4ca5-85e2-53c16263cb3c
-- title:
--   Certificate
-- statement:
--   Definitions and structural lemmas for Certificate, from Juan Pablo Traverso Gianini (jtraverso/haggkvist-janssen; see pinned Apache-2.0 LICENSE and source headers)'s pinned Haggkvist-Janssen bound on the list chromatic index of complete graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Certificate.lean

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Fin
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.ListEdgeColoringComplete
def diagIndex (n u v : ℕ) : ℕ :=
  if n - 1 ≤ u + v then u + v - (n - 1) else u + v
def IsLowEnd (n u v : ℕ) : Prop :=
  (diagIndex n u v % 2 = 0 ↔ v < u)
instance (n u v : ℕ) : Decidable (IsLowEnd n u v) :=
  inferInstanceAs (Decidable (_ ↔ _))
def localRank (n u v : ℕ) : ℕ :=
  if IsLowEnd n u v then diagIndex n u v / 2 else targetDegree n u v - diagIndex n u v / 2
def fullRank (n u v : ℕ) : ℕ :=
  if u = v then blockedRank n u else localRank n u v
def lowEnd (n u v : ℕ) : ℕ :=
  if IsLowEnd n u v then u else v
def Precedes (n u v u' v' : ℕ) : Prop :=
  diagIndex n u v / 2 < diagIndex n u' v' / 2 ∨
    (diagIndex n u v / 2 = diagIndex n u' v' / 2 ∧ lowEnd n u' v' < lowEnd n u v)
def edgeKey (n u v : ℕ) : ℕ :=
  diagIndex n u v / 2 * n + (n - 1 - lowEnd n u v)
section Arithmetic
variable {n u v w : ℕ}
theorem localRank_lt (hu : u < n) (hv : v < n) : localRank n u v < n := by
  unfold localRank IsLowEnd targetDegree diagIndex
  split_ifs <;> omega
theorem fullRank_lt (hu : u < n) (hv : v < n) : fullRank n u v < n := by
  unfold fullRank
  split_ifs with h
  · unfold blockedRank
    split_ifs <;> omega
  · exact localRank_lt hu hv
end Arithmetic
section FinCertificate
variable {n : ℕ}
def canonicalRow (i : Fin n) (j : Fin n) : Fin n :=
  ⟨fullRank n i j, fullRank_lt i.isLt j.isLt⟩
end FinCertificate
end LeanPool.ListEdgeColoringComplete


