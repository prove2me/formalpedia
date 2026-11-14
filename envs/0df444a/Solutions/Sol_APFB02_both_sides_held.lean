-- Prove2me | solution 1 for APFB02.both_sides_held
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:54:53.1892+00:00
-- url     : https://prove2.me/submissions/56ab0b5e-ee2e-4785-8f7a-e3079aa6d0b7

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K1_alignment_count
title: Every distinction is held on each side by some raw state (from B02); for two alignments of one family the overlap is agreements less oppositions, and half of the family's size plus the overlap is the number of agreements
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's ruling of 2026-11-13 17:53 HST ("Yes, record is an alignment of distinctions").
 FOUNDATION_INPUTS B02 in declared form. Def_APFPaper5_K1_AlignmentCount. The NUMBERS clause adopted
 2026-11-12 ("Numbers are a count of distinctions"). Thm_APFPaper5_K3_marks_of_the_carrier (the number
 between two marks of the two-component model is one half of one plus the cosine between their directions).
consumes_inputs: B02 (APFB02.B02SourceMeaning) as a hypothesis in the first theorem. None in the others.
statement: (APFB02.both_sides_held) under B02 every distinction is true at some raw state and false at
 another. A record of one distinction therefore has two sides, and both occur.
 (side_mul_side) the product of two sides is 1 when they are the same and -1 when they are opposite.
 (overlap_eq_agree_sub_oppose) the overlap of two alignments of a family is the number of agreements less
 the number of oppositions.
 (agree_add_oppose) agreements and oppositions together number the family.
 (number_is_count_of_agreements) half of the family's size plus the overlap is the number of agreements.
 (overlap_of_same_alignment) an alignment's overlap with itself is the size of the family.
reading: with a record read as an alignment of distinctions, the number between two records of one family
 is a count of distinctions: those on which they agree. As a fraction of the family it runs from 0 to 1;
 the overlap runs from minus the family's size to plus it. The form "one half of one plus the overlap over
 the size" is the form the number between two marks takes in the two-component model.
not_claimed: that every pattern of sides over a family is held by some raw state (B02 gives both sides of
 each distinction separately, not every combination); anything continuous; the rate; that an interface is
 the two-component model.
-/
import Definitions.Def_APFPaper5_K1_AlignmentCount
import Definitions.Def_APF_B02_DeclaredInput
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem APFB02.both_sides_held {Context : Type*} {X Q P Record : Context → Type*}
    (Cont : (g : Context) → X g → Q g → Prop)
    (Delta : (g : Context) → (X g → Bool) → Prop)
    (maintained : (g : Context) → P g → Record g → Prop)
    (sufficient : (g : Context) → P g → (Record g → Prop) →
      {d : X g → Bool // Delta g d} → Prop)
    (usesToRealize : (g : Context) → P g →
      {d : X g → Bool // Delta g d} → (Record g → Prop) → Prop)
    (hB02 : APFB02.B02SourceMeaning Cont Delta maintained sufficient usesToRealize)
    (g : Context) (d : {f : X g → Bool // Delta g f}) :
    (∃ x : X g, d.val x = true) ∧ ∃ y : X g, d.val y = false := by
  obtain ⟨_, ⟨x, y, hxy⟩, _⟩ := hB02 g d
  cases hx : d.val x <;> cases hy : d.val y
  · exact absurd (hx.trans hy.symm) hxy
  · exact ⟨⟨y, hy⟩, ⟨x, hx⟩⟩
  · exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  · exact absurd (hx.trans hy.symm) hxy

namespace APFPaper5.K1

theorem side_mul_side (x y : Bool) : side x * side y = if x = y then 1 else -1 := by
  cases x <;> cases y <;> simp [side]

theorem overlap_eq_agree_sub_oppose {D : Type*} (S : Finset D) (v w : D → Bool) :
    overlapOn S v w = agreeOn S v w - opposeOn S v w := by
  unfold overlapOn agreeOn opposeOn
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [side_mul_side]
  by_cases h : v d = w d
  · rw [if_pos h, if_pos h, if_pos h]
    norm_num
  · rw [if_neg h, if_neg h, if_neg h]
    norm_num

theorem agree_add_oppose {D : Type*} (S : Finset D) (v w : D → Bool) :
    agreeOn S v w + opposeOn S v w = (S.card : ℝ) := by
  unfold agreeOn opposeOn
  rw [← Finset.sum_add_distrib]
  have h : ∀ d : D, ((if v d = w d then (1 : ℝ) else 0) + if v d = w d then 0 else 1) = 1 := by
    intro d
    by_cases hd : v d = w d
    · rw [if_pos hd, if_pos hd]
      norm_num
    · rw [if_neg hd, if_neg hd]
      norm_num
  rw [Finset.sum_congr rfl (fun d _ => h d), Finset.sum_const, nsmul_eq_mul, mul_one]

theorem number_is_count_of_agreements {D : Type*} (S : Finset D) (v w : D → Bool) :
    ((S.card : ℝ) + overlapOn S v w) / 2 = agreeOn S v w := by
  have h1 := overlap_eq_agree_sub_oppose S v w
  have h2 := agree_add_oppose S v w
  rw [h1]
  linarith

theorem overlap_of_same_alignment {D : Type*} (S : Finset D) (v : D → Bool) :
    overlapOn S v v = (S.card : ℝ) := by
  unfold overlapOn
  have h : ∀ d : D, side (v d) * side (v d) = 1 := fun d => by
    rw [side_mul_side, if_pos rfl]
  rw [Finset.sum_congr rfl (fun d _ => h d), Finset.sum_const, nsmul_eq_mul, mul_one]

end APFPaper5.K1


universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4 apfNative_u_5
theorem solution :
∀ {Context : Type apfNative_u_1} {X : Context → Type apfNative_u_2} {Q : Context → Type apfNative_u_3}
  {P : Context → Type apfNative_u_4} {Record : Context → Type apfNative_u_5} (Cont : (g : Context) → X g → Q g → Prop)
  (Delta : (g : Context) → (X g → Bool) → Prop) (maintained : (g : Context) → P g → Record g → Prop)
  (sufficient :
    (g : Context) →
      P g → (Record g → Prop) → (@Subtype.{apfNative_u_2 + 1} (X g → Bool) fun (d : X g → Bool) => Delta g d) → Prop)
  (usesToRealize :
    (g : Context) →
      P g → (@Subtype.{apfNative_u_2 + 1} (X g → Bool) fun (d : X g → Bool) => Delta g d) → (Record g → Prop) → Prop)
  (hB02 :
    @APFB02.B02SourceMeaning.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} Context X Q P
      Record Cont Delta maintained sufficient usesToRealize)
  (g : Context) (d : @Subtype.{apfNative_u_2 + 1} (X g → Bool) fun (f : X g → Bool) => Delta g f),
  And
    (@Exists.{apfNative_u_2 + 1} (X g) fun (x : X g) =>
      @Eq.{1} Bool (@Subtype.val.{apfNative_u_2 + 1} (X g → Bool) (fun (f : X g → Bool) => Delta g f) d x) Bool.true)
    (@Exists.{apfNative_u_2 + 1} (X g) fun (y : X g) =>
      @Eq.{1} Bool (@Subtype.val.{apfNative_u_2 + 1} (X g → Bool) (fun (f : X g → Bool) => Delta g f) d y) Bool.false) := by
  exact @APFB02.both_sides_held
