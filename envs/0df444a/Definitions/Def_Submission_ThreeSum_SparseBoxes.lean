-- Prove2me | Definitions.Def_Submission_ThreeSum_SparseBoxes
-- name    : Submission_ThreeSum_SparseBoxes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:50:45.141428+00:00
-- url     : https://prove2.me/theorems/2129da36-6c91-4cbf-99ab-8c046cefe6e8
-- title:
--   Sparse Boxes
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
def largest : ℕ → Finset α → Finset α
  | 0, _ => ∅
  | t + 1, m =>
      if hm : m.Nonempty then
        insert (m.max' hm) (largest t (m.erase (m.max' hm)))
      else ∅
def IsLargest (t : ℕ) (m u : Finset α) : Prop :=
  u ⊆ m ∧ u.card = t ∧ ∀ a ∈ u, ∀ b ∈ m, b ∉ u → b < a
def BoxMember (flags free leaf : Finset α) : Prop :=
  leaf ⊆ flags ∧ flags \ free ⊆ leaf
def queryFree (q u : Finset α) : Finset α :=
  (q \ u).filter (fun x => ∀ y ∈ u, x < y)
def QueryBox (q u leaf : Finset α) : Prop :=
  BoxMember (q \ u) (queryFree q u) leaf
def IsInitial (flags free : Finset α) : Prop :=
  free ⊆ flags ∧ ∀ a ∈ free, ∀ b ∈ flags, b < a → b ∈ free
def smallest (t : ℕ) (flags : Finset α) : Finset α :=
  @largest (OrderDual α) _ t flags
def boundedSubsets (ambient : Finset α) (cut : ℕ) : Finset (Finset α) :=
  (Finset.range (cut + 1)).biUnion (fun j => ambient.powersetCard j)
def records (ambient : Finset α) (cut : ℕ) :
    Finset (Sigma (fun _ : Finset α => ℕ)) :=
  (boundedSubsets ambient cut).sigma
    (fun flags => Finset.range (flags.card + 1))
instance (flags free leaf : Finset α) : Decidable (BoxMember flags free leaf) := by
  unfold BoxMember
  infer_instance
instance (q u leaf : Finset α) : Decidable (QueryBox q u leaf) := by
  unfold QueryBox
  infer_instance
def boxSum (flags free : Finset α) (weight : Finset α → ℤ) : ℤ :=
  ∑ leaf ∈ flags.powerset, if flags \ free ⊆ leaf then weight leaf else 0
def explicitLeaves (q : Finset α) (t : ℕ) : Finset (Finset α) :=
  ((Finset.range t).biUnion (fun j => q.powersetCard j)).image (fun missing => q \ missing)
end ThreeSum.SparseBoxes


