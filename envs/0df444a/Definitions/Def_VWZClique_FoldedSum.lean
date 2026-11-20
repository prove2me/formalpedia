-- Prove2me | Definitions.Def_VWZClique_FoldedSum
-- name    : VWZClique_FoldedSum
-- status  : Definition
-- author  : @orz
-- created : 2026-11-20T01:00:38.411118+00:00
-- url     : https://prove2.me/theorems/04f5387c-ed58-4203-bd6f-f9f5d3fab053
-- title:
--   Weighted sums with wedge factors assigned to channels
-- statement:
--   Three factorized channels with specified active binary factors are contracted using identities or partial swaps on two pivot pairs.
-- source:
--   V. Vassilevska Williams and O. Zamir, The k-Clique hypothesis is dead, for good (2026), Section 3.2, Lemma 3.2. https://zamir.prof/kclq.pdf

import Definitions.Def_VWZClique_Contraction

namespace VWZClique
abbrev EdgeSlot := Fin 3 × Slot × Slot

def placedChannel {F : Type*} [Field F] {L : ℕ} (E : Finset EdgeSlot)
    (w : ChannelKey L → F) (h : Fin 3) (a b : Block L) : F :=
  let x : Slot → Bits L := Sum.elim a b
  (∏ i : Slot, w (h, .inl (i, x i))) *
    ∏ v ∈ E, if v.1 = h then w (h, .inr (v.2.1, v.2.2, x v.2.1, x v.2.2)) else 1

open Classical in
noncomputable def maskKernel {F : Type*} [Field F] {L : ℕ}
    (m : Option (Mask L)) (x y : PairBits L) : F :=
  match m with
  | none => if x = y then 1 else 0
  | some s => if swapOK s x y then 1 else 0

noncomputable def placedFold {F : Type*} [Field F] {L : ℕ} (E : Finset EdgeSlot)
    (a b : Option (Mask L)) (w : ChannelKey L → F) : F :=
  ∑ z₁ : Bits L, ∑ z₂ : Bits L, ∑ c : Block L,
    ∑ x : PairBits L, ∑ x' : PairBits L, ∑ y : PairBits L, ∑ y' : PairBits L,
      maskKernel a x x' * maskKernel (F := F) b y y' *
      placedChannel E w 0 (block x z₁) (block y z₂) *
      placedChannel E w 1 (block y' z₂) c * placedChannel E w 2 c (block x' z₁)

def wedgePlaced (E : Finset EdgeSlot) (left right : Fin 3) : Prop :=
  (left, Sum.inl 0, Sum.inl 2) ∈ E ∧ (right, Sum.inr 1, Sum.inr 2) ∈ E
end VWZClique


