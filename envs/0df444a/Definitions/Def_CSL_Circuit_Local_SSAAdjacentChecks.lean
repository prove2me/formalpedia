-- Prove2me | Definitions.Def_CSL_Circuit_Local_SSAAdjacentChecks
-- name    : CSL_Circuit_Local_SSAAdjacentChecks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:10:06.719686+00:00
-- url     : https://prove2.me/theorems/5793926a-bc3f-4cbc-abf1-7db6c827a169
-- title:
--   Coded sorting library: Circuit / Local / SSAAdjacentChecks
-- statement:
--   Module `CodedSorting.Circuit.Local.SSAAdjacentChecks` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Linear-size structural certificates for sorted source lists.
--
--   The generated Construction source lists are in increasing order. Checking adjacent pairs
--   avoids the quadratic computation used by `decide sources.Nodup`. The theorem
--   below converts the actual checked Boolean into the required `List.Nodup` fact.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Local.SSAAdjacentChecks

import Definitions.Def_CSL_Compat
import Std

/-! Linear-size structural certificates for sorted source lists.

The generated Construction source lists are in increasing order. Checking adjacent pairs
avoids the quadratic computation used by `decide sources.Nodup`. The theorem
below converts the actual checked Boolean into the required `List.Nodup` fact.
-/
set_option autoImplicit false

namespace CSL.Construction.SSAAdjacentChecks

def increasing : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: xs => decide (a < b) && increasing (b :: xs)

theorem increasing_tail (a : Nat) (xs : List Nat)
    (h : increasing (a :: xs) = true) : increasing xs = true := by
  cases xs with
  | nil => rfl
  | cons b bs =>
      have hpair : decide (a < b) = true ∧ increasing (b :: bs) = true := by
        simpa only [increasing, Bool.and_eq_true] using h
      exact hpair.2

theorem increasing_head (a : Nat) (xs : List Nat)
    (h : increasing (a :: xs) = true) : ∀ b ∈ xs, a < b := by
  induction xs generalizing a with
  | nil => simp
  | cons c cs ih =>
      have hpair : a < c ∧ increasing (c :: cs) = true := by
        simpa only [increasing, Bool.and_eq_true, decide_eq_true_eq] using h
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hpair.1
      · exact Nat.lt_trans hpair.1 (ih c hpair.2 b hb)

theorem nodup_of_increasing (xs : List Nat) (h : increasing xs = true) :
    xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons a xs ih =>
      apply List.nodup_cons.mpr
      constructor
      · intro ha
        exact Nat.lt_irrefl a (increasing_head a xs h a ha)
      · exact ih (increasing_tail a xs h)

/-- The 112 unordered source lists in the actual word have at most three
entries; their direct check is bounded. Longer lists use the linear check. -/
def nodupCheck (xs : List Nat) : Bool :=
  if xs.length ≤ 3 then decide xs.Nodup else increasing xs

theorem nodup_of_check (xs : List Nat) (h : nodupCheck xs = true) : xs.Nodup := by
  unfold nodupCheck at h
  split at h
  · exact of_decide_eq_true h
  · exact nodup_of_increasing xs h

end CSL.Construction.SSAAdjacentChecks

#print axioms CSL.Construction.SSAAdjacentChecks.nodup_of_increasing
#print axioms CSL.Construction.SSAAdjacentChecks.nodup_of_check


