-- Prove2me | solution 1 for Apportionmentlib.Rule.seats_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:41:26.102773+00:00
-- url     : https://prove2.me/submissions/f1e14386-237b-4fea-a7ef-a251038b2dd0

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Rat.Floor
public import Definitions.Def_Apportionmentlib_Utils
public import Definitions.Def_Apportionmentlib_Basic

set_option autoImplicit false
@[expose] public section
public section
open BigOperators
open Apportionmentlib
namespace Apportionmentlib
namespace Rule
theorem _root_.solution (rule : Rule) [h_quota : IsQuotaRule rule] {n : ℕ} (election : Election n)
    (i : Fin n) (m : ℕ) (h : election.quota i ≤ m) :
    ∀ App ∈ rule.res election, App[i] ≤ m := by
  intro App h_App
  have h_quota := h_quota.quota_rule election i App h_App
  have h_ceil : ⌈election.quota i⌉ ≤ m := Int.ceil_le.mpr h
  have h_floor := Int.floor_le_ceil (election.quota i)
  rcases h_quota <;> omega
end Rule
end Apportionmentlib
