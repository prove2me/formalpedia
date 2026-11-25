-- Prove2me | Definitions.Def_StableMarriageF6_F6SmallBlockTokenCapacity
-- name    : StableMarriageF6_F6SmallBlockTokenCapacity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T09:30:21.603751+00:00
-- url     : https://prove2.me/theorems/0a7b176c-0958-432a-93b2-016ca7b02e53
-- title:
--   F6 Small Block Token Capacity
-- statement:
--   Definitions and structural lemmas for F6 Small Block Token Capacity, from insammael (insammael/stable-marriage-f6; see pinned Apache-2.0 LICENSE and lean/third_party provenance)'s pinned Small rotation blocks and antichain bound for width-3 CI2 posets (Stable Marriage F6) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/lean/StableMarriageF6/F6SmallBlockTokenCapacity.lean

import Mathlib
set_option autoImplicit true
open scoped BigOperators
open Classical
noncomputable section
namespace F6SmallBlockTokenCapacity
variable {B W : Type*} [Fintype B] [Fintype W] {q : ℕ}
structure TokenRun (B W : Type*) [Fintype B] [Fintype W] (q : ℕ) where
  support : Fin q → Finset B
  state : Fin (q + 1) → (B ≃ W)
  rank : B → W → ℕ
  HMIN : ∀ i, 2 ≤ (support i).card
  HOUT : ∀ i b, b ∉ support i → state i.castSucc b = state i.succ b
  HWORSE : ∀ i b, b ∈ support i →
    rank b (state i.castSucc b) < rank b (state i.succ b)
namespace TokenRun
variable (R : TokenRun B W q)
noncomputable def participationSteps (b : B) : Finset (Fin q) := by
  classical
  exact Finset.univ.filter (fun i => b ∈ R.support i)
def firstSteps (n : ℕ) (h : n ≤ q) : TokenRun B W n where
  support i := R.support (i.castLE h)
  state t := R.state (t.castLE (Nat.add_le_add_right h 1))
  rank := R.rank
  HMIN i := R.HMIN (i.castLE h)
  HOUT i b hb := R.HOUT (i.castLE h) b hb
  HWORSE i b hb := R.HWORSE (i.castLE h) b hb
end TokenRun
end F6SmallBlockTokenCapacity


