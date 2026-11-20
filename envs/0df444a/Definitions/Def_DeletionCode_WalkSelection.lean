-- Prove2me | Definitions.Def_DeletionCode_WalkSelection
-- name    : DeletionCode_WalkSelection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:09:32.519426+00:00
-- url     : https://prove2.me/theorems/2a10868b-8533-4543-817d-d2be372d45bd
-- title:
--   Walk Selection
-- statement:
--   Definitions and structural lemmas for Walk Selection, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WalkSelection.lean

import Definitions.Def_DeletionCode_ClosedWalk
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
set_option autoImplicit true
namespace DeletionCode.WalkSelection
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℚ V] {m : ℕ}
def walkStep (p : Fin (m + 1) → V) (i : Fin m) : V := p i.succ - p i.castSucc
def selectedSpan (step : Fin m → V) (S : Finset (Fin m)) : Submodule ℚ V :=
  Submodule.span ℚ (step '' (S : Set (Fin m)))
def SignedMember (step : Fin m → V) (S : Finset (Fin m)) (v : V) : Prop :=
  ∃ r ∈ S, v = step r ∨ v = -step r
structure ScanState (step : Fin m → V) (Good : Finset (Fin m) → Prop)
    (n : ℕ) (S : Finset (Fin m)) : Prop where
  before : ∀ r ∈ S, r.val < n
  good : Good S
  independent : LinearIndepOn ℚ step (S : Set (Fin m))
  covered : ∀ j : Fin m, j.val < n →
    ∃ r ∈ S, r.val ≤ j.val ∧ (step j = step r ∨ step j = -step r)
def Stopped (step : Fin m → V) (Good : Finset (Fin m) → Prop) : Prop :=
  ∃ (i : Fin m) (S : Finset (Fin m)),
    ScanState step Good i.val S ∧ ¬ SignedMember step S (step i) ∧
      (step i ∈ selectedSpan step S ∨
        (step i ∉ selectedSpan step S ∧
          LinearIndepOn ℚ step ((insert i S : Finset (Fin m)) : Set (Fin m)) ∧
          ¬ Good (insert i S)))
def GeneratingSelected {H : Type*} (p : Fin (m + 1) → H → ℚ)
    (S : Finset (Fin m)) : Prop :=
  ∀ i ∈ S, ∀ h, walkStep p i h = -1 →
    p 0 h ≠ 0 ∨ ∃ r ∈ S, r.val < i.val ∧ walkStep p r h ≠ 0
end DeletionCode.WalkSelection


