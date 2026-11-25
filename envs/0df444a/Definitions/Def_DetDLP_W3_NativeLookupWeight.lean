-- Prove2me | Definitions.Def_DetDLP_W3_NativeLookupWeight
-- name    : DetDLP_W3_NativeLookupWeight
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T01:12:53.713936+00:00
-- url     : https://prove2.me/theorems/288bc37f-1d2c-49e4-9f47-004cb51c8c75
-- title:
--   Native address lookup and exact label weights
-- statement:
--   Each native address selects a block index by a finite scan. Injectivity identifies a successful lookup with its unique preimage. The product of the negative and positive label factors selected in this way equals the prescribed weight of the ordered tuple pair.

import Definitions.Def_DetDLP_W3_Separator

set_option autoImplicit false
namespace DetDLP

/-- The port evaluator can scan the encoded block; it need not invert the seed. -/
def w3_lookupIndex (q : w3_Query) (i : Fin q.m) (a : ℕ) : Option (Fin (q.FB.blocks i).length) :=
  (List.finRange (q.FB.blocks i).length).find? (fun r => decide (q.addr i r = a))

theorem w3_lookupIndex_eq_some_iff (q : w3_Query) (i : Fin q.m)
    (inj : Function.Injective (q.addr i)) (a : ℕ) (r : Fin (q.FB.blocks i).length) :
    w3_lookupIndex q i a = some r ↔ q.addr i r = a := by
  unfold w3_lookupIndex
  constructor
  · intro h
    have hh := List.find?_some h
    exact of_decide_eq_true hh
  · intro h
    cases he : (List.finRange (q.FB.blocks i).length).find? (fun s => decide (q.addr i s = a)) with
    | none =>
      have hf := List.find?_eq_none.mp he r (List.mem_finRange r)
      simp [h] at hf
    | some s =>
      have hh := List.find?_some he
      have hs : q.addr i s = a := of_decide_eq_true hh
      rw [inj (hs.trans h.symm)]

noncomputable def w3_addressWeight (q : w3_Query) (i : Fin q.m) (positive : Bool) (a : ℕ) :
    TruncPoly (w3_precision q) (w3_len q) :=
  match w3_lookupIndex q i a with
  | none => 0
  | some r => let z : ℤ := (q.y (q.FB.coordOf i r)).val
              w3_binWord q (if positive then z else -z)

theorem w3_addressWeight_product (q : w3_Query) (inj : ∀ i, Function.Injective (q.addr i))
    (X Y : q.FB.BlockTuple) :
    (∏ i : Fin q.m, ∏ s : Fin 2,
      w3_addressWeight q i false (q.addr i (X i s)) * w3_addressWeight q i true (q.addr i (Y i s))) =
      w3_pairWeight q (X,Y) := by
  have hit (i : Fin q.m) (r : Fin (q.FB.blocks i).length) : w3_lookupIndex q i (q.addr i r) = some r :=
    (w3_lookupIndex_eq_some_iff q i (inj i) _ r).mpr rfl
  simp only [w3_addressWeight, hit, Bool.false_eq_true, if_false, if_true, w3_pairWeight]

end DetDLP


