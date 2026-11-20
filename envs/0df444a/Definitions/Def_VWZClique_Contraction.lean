-- Prove2me | Definitions.Def_VWZClique_Contraction
-- name    : VWZClique_Contraction
-- status  : Definition
-- author  : @orz
-- created : 2026-11-20T00:59:44.411973+00:00
-- url     : https://prove2.me/theorems/d859fbfc-1aea-43f9-b278-88caf4883f97
-- title:
--   The two-projection contribution
-- statement:
--   Three channels consist of products of unary and binary factors on two incident triples. Two rational product-basis projections are interpreted in the coefficient field.
-- source:
--   V. Vassilevska Williams and O. Zamir, The k-Clique hypothesis is dead, for good (2026), Section 3.3, equations (6)–(9). https://zamir.prof/kclq.pdf

import Definitions.Def_VWZClique_Operators
import Definitions.Def_VWZClique_Weighted

namespace VWZClique
abbrev Slot := Fin 3 ⊕ Fin 3
abbrev Block (L : ℕ) := Fin 3 → Bits L
abbrev ChannelKey (L : ℕ) :=
  Fin 3 × ((Slot × Bits L) ⊕ (Slot × Slot × Bits L × Bits L))

def channel {F : Type*} [Field F] {L : ℕ} (w : ChannelKey L → F)
    (h : Fin 3) (a b : Block L) : F :=
  let x : Slot → Bits L := Sum.elim a b
  (∏ i : Slot, w (h, .inl (i, x i))) *
    ∏ i : Slot, ∏ j : Slot, w (h, .inr (i, j, x i, x j))

def block {L : ℕ} (x : PairBits L) (z : Bits L) : Block L :=
  fun i => if i = 0 then x.1 else if i = 1 then x.2 else z

def projected {F : Type*} [Field F] [CharZero F] {L : ℕ}
    (Λ : Finset (BasisLabel L)) (d : BasisLabel L → F) (x y : PairBits L) : F :=
  ∑ j ∈ Λ, d j * (basisEntry j x : F) * (basisEntry j y : F)

noncomputable def doubleProjection {F : Type*} [Field F] [CharZero F] {L : ℕ}
    (Λ Γ : Finset (BasisLabel L)) (d e : BasisLabel L → F)
    (w : ChannelKey L → F) : F :=
  ∑ z₁ : Bits L, ∑ z₂ : Bits L, ∑ c : Block L,
    ∑ x : PairBits L, ∑ x' : PairBits L, ∑ y : PairBits L, ∑ y' : PairBits L,
      projected Λ d x x' * projected Γ e y y' *
      channel w 0 (block x z₁) (block y z₂) *
      channel w 1 (block y' z₂) c * channel w 2 c (block x' z₁)
end VWZClique


