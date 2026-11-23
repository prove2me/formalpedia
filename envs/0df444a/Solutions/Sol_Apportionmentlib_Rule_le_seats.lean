-- Prove2me | solution 1 for Apportionmentlib.Rule.le_seats
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:41:36.422499+00:00
-- url     : https://prove2.me/submissions/3786c1cd-48ca-4532-9d1d-d38f586eb7b7

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
    (i : Fin n) (m : ℕ) (h : (m : ℚ) ≤ election.quota i) :
    ∀ App ∈ rule.res election, m ≤ App[i] := by
  intro App h_App
  have h_quota := h_quota.quota_rule election i App h_App
  have h_floor : m ≤ ⌊election.quota i⌋ := Int.le_floor.mpr h
  have h_ceil := Int.floor_le_ceil (election.quota i)
  rcases h_quota <;> omega
end Rule
end Apportionmentlib
