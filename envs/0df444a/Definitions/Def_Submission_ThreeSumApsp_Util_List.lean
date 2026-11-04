-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Util_List
-- name    : Submission_ThreeSumApsp_Util_List
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:23:56.825287+00:00
-- url     : https://prove2.me/theorems/a0049087-ee26-4c4f-8f1c-8227c34139fd
-- title:
--   List
-- statement:
--   Definitions and structural lemmas for List, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean

module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Count
set_option autoImplicit false
@[expose] public section
namespace List
variable {α β : Type*}
section
variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]
end
section Sorted
variable [LinearOrder α]
end Sorted
end List
namespace ThreeSumApsp
variable {α β : Type*}
def AbsLe (l : List ℤ) (U : ℤ) : Prop := ∀ x ∈ l, |x| ≤ U
def sumLists (len : ℕ) (ls : List (List ℤ)) : List ℤ :=
  ls.foldl (fun acc l => List.zipWith (· + ·) acc l) (List.replicate len 0)
end ThreeSumApsp


