-- Prove2me | Definitions.Def_PricingWithTips3DM_e80588e5c6eb8509e1ccd808
-- name    : PricingWithTips3DM_e80588e5c6eb8509e1ccd808
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:18:05.692086+00:00
-- url     : https://prove2.me/theorems/a48ffd12-7920-4614-ba81-282fb11d09d2
-- title:
--   PricingWithTips 3DM dependency: HardnessReductions.Cert.Numbering
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/DominikPeters/HardnessReductionsLean

import Mathlib.Data.Fintype.Card
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Positional numberings, by blocks

A certificate whose gadget builds a *structured* vertex or element type — a
sum of rectangles of `Fin`s and `Bool`s — must realize those tagged names as
positions of the list it emits. Six annexes hand-rolled the same apparatus:
an offset-arithmetic map into `ℕ`, a bound, an injectivity case split
(block-range disjointness off the diagonal, a mixed-radix argument on it), a
cardinality count, and `Equiv.ofBijective` to upgrade to the bijection that
the entry's renaming-invariance lemma transports along.

`Numbering α` packages the map with the three facts that make it a bijection
onto an initial segment — bound, injectivity, completeness — and the
combinators compose them:

* `Numbering.fin`, `Numbering.bool`, `Numbering.boolRev` — the digits;
* `A.prod B` — a rectangle, numbered row-major (`A` the high digit);
* `A.sum B` — two blocks laid end to end, the `A` block first;
* `Numbering.ofEquiv` — a block that already has a bijection onto `Fin n`
  (mathlib's `finSigmaFinEquiv`, for occurrence-indexed tags whose clauses
  differ in width and so admit no radix).

A client instantiates the combinators to match the offsets its program emits,
states one arithmetic *face* lemma per tag constructor (a `simp` unfold plus
`omega`), and reads `num_lt`, `num_inj`, `card_eq` and `equivFin` off the
structure. The faces are where the layout is checked against the program;
nothing else is.
-/

namespace Hardness
namespace Cert

/-- A positional numbering of a type of tagged names: an injection *onto* the
initial segment `[0, size)` of `ℕ`. Completeness (`num_surj`) is what a block
layout has and a mere labelling does not, and it is what makes the bijection
`equivFin` free — so it is a field, not an afterthought. -/
structure Numbering (α : Type*) where
  /-- The position of a tag. -/
  num : α → ℕ
  /-- The number of positions. -/
  size : ℕ
  num_lt : ∀ a, num a < size
  num_inj : Function.Injective num
  num_surj : ∀ i < size, ∃ a, num a = i

namespace Numbering

variable {α β : Type*}

/-! ## The digits -/

/-- `Fin n`, numbered by value. -/
def fin (n : ℕ) : Numbering (Fin n) where
  num := Fin.val
  size := n
  num_lt := Fin.isLt
  num_inj := Fin.val_injective
  num_surj i hi := ⟨⟨i, hi⟩, rfl⟩

@[simp] theorem fin_num {n : ℕ} (i : Fin n) : (fin n).num i = i.val := rfl

@[simp] theorem fin_size {n : ℕ} : (fin n).size = n := rfl

/-- `Bool`, numbered `false` first. -/
def bool : Numbering Bool where
  num := Bool.toNat
  size := 2
  num_lt b := by cases b <;> decide
  num_inj a b h := by revert h; cases a <;> cases b <;> decide
  num_surj i hi := match i, hi with
    | 0, _ => ⟨false, rfl⟩
    | 1, _ => ⟨true, rfl⟩

@[simp] theorem bool_num (b : Bool) : bool.num b = b.toNat := rfl

@[simp] theorem bool_size : bool.size = 2 := rfl

/-- `Bool`, numbered `true` first — for layouts that list the positive block
before the negative one. -/
def boolRev : Numbering Bool where
  num b := (!b).toNat
  size := 2
  num_lt b := by cases b <;> decide
  num_inj a b h := by revert h; cases a <;> cases b <;> decide
  num_surj i hi := match i, hi with
    | 0, _ => ⟨true, rfl⟩
    | 1, _ => ⟨false, rfl⟩

@[simp] theorem boolRev_num (b : Bool) : boolRev.num b = (!b).toNat := rfl

@[simp] theorem boolRev_size : boolRev.size = 2 := rfl

/-- A block that already has a bijection onto `Fin n`. -/
def ofEquiv {n : ℕ} (e : α ≃ Fin n) : Numbering α where
  num a := (e a).val
  size := n
  num_lt a := (e a).isLt
  num_inj _ _ h := e.injective (Fin.ext h)
  num_surj i hi := ⟨e.symm ⟨i, hi⟩, by rw [Equiv.apply_symm_apply]⟩

@[simp] theorem ofEquiv_num {n : ℕ} (e : α ≃ Fin n) (a : α) :
    (ofEquiv e).num a = (e a).val := rfl

@[simp] theorem ofEquiv_size {n : ℕ} (e : α ≃ Fin n) : (ofEquiv e).size = n := rfl

/-! ## The block combinators -/

/-- One distinguished name in front of a block: `none` takes position `0` and
the `α` block is shifted by one. The layout of a gadget with a *root* vertex,
whose tag type is `Option _`. -/
def option (A : Numbering α) : Numbering (Option α) where
  num := fun o ↦ o.elim 0 fun a ↦ A.num a + 1
  size := A.size + 1
  num_lt := by
    rintro (_ | a)
    · exact Nat.succ_pos _
    · exact Nat.succ_lt_succ (A.num_lt a)
  num_inj := by
    rintro (_ | a) (_ | a') h <;> simp only [Option.elim] at h
    · rfl
    · exact absurd h (by omega)
    · exact absurd h (by omega)
    · exact congrArg some (A.num_inj (by omega))
  num_surj i hi := by
    match i with
    | 0 => exact ⟨none, rfl⟩
    | j + 1 =>
      obtain ⟨a, ha⟩ := A.num_surj j (by omega)
      exact ⟨some a, by simp only [Option.elim, ha]⟩

@[simp] theorem option_num_none (A : Numbering α) : A.option.num none = 0 := rfl

@[simp] theorem option_num_some (A : Numbering α) (a : α) :
    A.option.num (some a) = A.num a + 1 := rfl

@[simp] theorem option_size (A : Numbering α) : A.option.size = A.size + 1 := rfl


/-- Two blocks laid end to end: the `α` block first, then the `β` block at
offset `A.size`. -/
def sum (A : Numbering α) (B : Numbering β) : Numbering (α ⊕ β) where
  num := Sum.elim A.num fun b ↦ A.size + B.num b
  size := A.size + B.size
  num_lt := by
    rintro (a | b)
    · exact Nat.lt_of_lt_of_le (A.num_lt a) (Nat.le_add_right _ _)
    · exact Nat.add_lt_add_left (B.num_lt b) _
  num_inj := by
    rintro (a | b) (a' | b') h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg Sum.inl (A.num_inj h)
    · exact absurd h (by have := A.num_lt a; omega)
    · exact absurd h (by have := A.num_lt a'; omega)
    · exact congrArg Sum.inr (B.num_inj (by omega))
  num_surj i hi := by
    rcases Nat.lt_or_ge i A.size with h | h
    · obtain ⟨a, ha⟩ := A.num_surj i h
      exact ⟨.inl a, by simpa using ha⟩
    · obtain ⟨b, hb⟩ := B.num_surj (i - A.size) (by omega)
      exact ⟨.inr b, by simp only [Sum.elim_inr, hb]; omega⟩

@[simp] theorem sum_num_inl (A : Numbering α) (B : Numbering β) (a : α) :
    (A.sum B).num (.inl a) = A.num a := rfl

@[simp] theorem sum_num_inr (A : Numbering α) (B : Numbering β) (b : β) :
    (A.sum B).num (.inr b) = A.size + B.num b := rfl

@[simp] theorem sum_size (A : Numbering α) (B : Numbering β) :
    (A.sum B).size = A.size + B.size := rfl

/-- Mixed-radix uniqueness: within a rectangle, the high and the low digit are
both recovered from the number. -/
private theorem mul_add_inj {S a b a' b' : ℕ} (hb : b < S) (hb' : b' < S)
    (h : a * S + b = a' * S + b') : a = a' ∧ b = b' := by
  rcases Nat.lt_trichotomy a a' with hlt | rfl | hgt
  · have hle : (a + 1) * S ≤ a' * S := Nat.mul_le_mul_right S hlt
    rw [Nat.succ_mul] at hle
    omega
  · omega
  · have hle : (a' + 1) * S ≤ a * S := Nat.mul_le_mul_right S hgt
    rw [Nat.succ_mul] at hle
    omega

/-- A rectangle, numbered row-major: `A` is the high digit. -/
def prod (A : Numbering α) (B : Numbering β) : Numbering (α × β) where
  num p := A.num p.1 * B.size + B.num p.2
  size := A.size * B.size
  num_lt p := by
    have h1 : (A.num p.1 + 1) * B.size ≤ A.size * B.size :=
      Nat.mul_le_mul_right _ (A.num_lt p.1)
    have h2 := B.num_lt p.2
    rw [Nat.succ_mul] at h1
    omega
  num_inj := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨h1, h2⟩ := mul_add_inj (B.num_lt b) (B.num_lt b') h
    exact Prod.ext (A.num_inj h1) (B.num_inj h2)
  num_surj i hi := by
    have hS : 0 < B.size := by
      rcases Nat.eq_zero_or_pos B.size with h0 | h
      · rw [h0, Nat.mul_zero] at hi; omega
      · exact h
    obtain ⟨a, ha⟩ := A.num_surj (i / B.size)
      (Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi))
    obtain ⟨b, hb⟩ := B.num_surj (i % B.size) (Nat.mod_lt _ hS)
    exact ⟨(a, b), by rw [ha, hb, Nat.div_add_mod']⟩

@[simp] theorem prod_num (A : Numbering α) (B : Numbering β) (a : α) (b : β) :
    (A.prod B).num (a, b) = A.num a * B.size + B.num b := rfl

@[simp] theorem prod_size (A : Numbering α) (B : Numbering β) :
    (A.prod B).size = A.size * B.size := rfl

/-! ## What every client reads off -/

/-- The numbering, as a bijection onto the positions. Noncomputable proof-layer
apparatus (`Equiv.ofBijective`), no part of any certified program. -/
noncomputable def equivFin (N : Numbering α) : α ≃ Fin N.size :=
  Equiv.ofBijective (fun a ↦ ⟨N.num a, N.num_lt a⟩)
    ⟨fun _ _ h ↦ N.num_inj (congrArg Fin.val h),
      fun i ↦ (N.num_surj i.val i.isLt).imp fun _ ha ↦ Fin.ext ha⟩

@[simp] theorem equivFin_val (N : Numbering α) (a : α) :
    ((N.equivFin a : Fin N.size) : ℕ) = N.num a := rfl

/-- The tag count is the position count — no client states it separately. -/
theorem card_eq (N : Numbering α) [Fintype α] : Fintype.card α = N.size := by
  simpa using Fintype.card_congr N.equivFin

/-- The numbering applied to both ends of an edge is still injective. -/
theorem num_pair_inj (N : Numbering α) :
    Function.Injective fun p : α × α ↦ (N.num p.1, N.num p.2) := fun _ _ h ↦
  Prod.ext (N.num_inj (congrArg Prod.fst h)) (N.num_inj (congrArg Prod.snd h))

/-- Membership of a numbered pair in a numbered family list — the step that
carries "the program's list is the abstract family, mapped through the
numbering" back to abstract membership. -/
theorem mem_map_num_pair (N : Numbering α) {L : List (α × α)} {u w : α} :
    (N.num u, N.num w) ∈ L.map (fun p ↦ (N.num p.1, N.num p.2)) ↔ (u, w) ∈ L :=
  List.mem_map_of_injective N.num_pair_inj (a := (u, w)) (l := L)

end Numbering

end Cert
end Hardness


