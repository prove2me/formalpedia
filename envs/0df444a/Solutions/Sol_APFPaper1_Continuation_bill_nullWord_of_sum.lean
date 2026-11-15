-- Prove2me | solution 1 for APFPaper1.Continuation.bill_nullWord_of_sum
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T02:36:45.363258+00:00
-- url     : https://prove2.me/submissions/2d55f5f9-a641-4740-a99c-8a787c4ab31e

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper1_Cont_identity_from_sum
title: If the bill of a word is the sum of the costs of the records it keeps, and the empty word keeps no record, the empty word bills zero and is a continuation from every raw possibility
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:1227 (C1, identity) and 2889-2891 (the empty word bills zero), as cited in
 Thm_APFPaper1_Cont_identity (seat 01WrrBvu), which carries that as the named hypothesis hnull.
 Thm_APFPaper1_Cont_prefix_from_sum_and_keep (this seat, pass 12) for SUM. The author, 2026-11-14 13:00 HST,
 "Proceed as proposed", read in RULING_calls_2026-11-14 as adopting SUM as a reading.
consumes_inputs: none. Ordinary mathematics on the definitions.
hypotheses:
  SUM (hsum): the calibrated bill of a word is the sum, over the records the word keeps, of their costs.
  EMPTY (hempty): the empty word keeps no record. This was not put to the author as a call of its own.
statement: (bill_nullWord_of_sum) under SUM and EMPTY the empty word bills zero, which is the hypothesis
 hnull of cont_identity; (cont_identity_of_sum) so the empty word belongs to Cont g x for every x, and it
 reaches x and nothing else.
reading: under SUM, A7 is no longer its own hypothesis. It is the statement that the empty word keeps
 nothing.
not_claimed: SUM or EMPTY themselves. SUM is an adopted reading, not a declared input and not derived from
 the declared forms. EMPTY is supplied.
-/
import Theorems.Thm_APFPaper1_Continuation_cont_identity
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
namespace APFPaper1.Continuation

universe uC uF uX uR uK
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}

/-- Under SUM, a word that keeps no record bills zero. Said of the empty word. -/
theorem bill_nullWord_of_sum {Rec : Context → Type uK}
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (kept : (g : Context) → WordFrom Frag g → Finset (Rec g))
    (cost : (g : Context) → Rec g → NNReal)
    (hsum : ∀ (g : Context) (w : WordFrom Frag g),
      calibration g (resource g w) = ∑ r ∈ kept g w, cost g r)
    (g : Context) (hempty : kept g (nullWord g) = ∅) :
    calibration g (resource g (nullWord g)) = 0 := by
  rw [hsum g (nullWord g), hempty, Finset.sum_empty]

/-- C1 from SUM and EMPTY: the empty word is a continuation from every raw possibility, and reaches that
possibility and nothing else. -/
theorem cont_identity_of_sum {Rec : Context → Type uK}
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (kept : (g : Context) → WordFrom Frag g → Finset (Rec g))
    (cost : (g : Context) → Rec g → NNReal)
    (hsum : ∀ (g : Context) (w : WordFrom Frag g),
      calibration g (resource g w) = ∑ r ∈ kept g w, cost g r)
    (g : Context) (x : Raw g) (hempty : kept g (nullWord g) = ∅) :
    Cont step resource calibration C g x (nullWord g) ∧
      ∀ z : Raw g, Executes step (Word.nil g) x z ↔ x = z :=
  cont_identity step resource calibration C g x
    (bill_nullWord_of_sum resource calibration kept cost hsum g hempty)

end APFPaper1.Continuation

#print axioms APFPaper1.Continuation.bill_nullWord_of_sum
#print axioms APFPaper1.Continuation.cont_identity_of_sum


universe apfNative_uC apfNative_uF apfNative_uR apfNative_uK
theorem solution :
∀ {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF} {R : Context → Type apfNative_uR}
  {Rec : Context → Type apfNative_uK}
  (resource : (g : Context) → @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g → R g)
  (calibration : (g : Context) → R g → NNReal)
  (kept :
    (g : Context) →
      @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g → Finset.{apfNative_uK} (Rec g))
  (cost : (g : Context) → Rec g → NNReal)
  (hsum :
    ∀ (g : Context) (w : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g),
      @Eq.{1} NNReal (calibration g (resource g w))
        (@Finset.sum.{apfNative_uK, 0} (Rec g) NNReal (@Semiring.toAddCommMonoid.{0} NNReal NNReal.instSemiring)
          (kept g w) fun (r : Rec g) => cost g r))
  (g : Context)
  (hempty :
    @Eq.{apfNative_uK + 1} (Finset.{apfNative_uK} (Rec g))
      (kept g (@APFPaper1.Continuation.nullWord.{apfNative_uC, apfNative_uF} Context Frag g))
      (@EmptyCollection.emptyCollection.{apfNative_uK} (Finset.{apfNative_uK} (Rec g))
        (@Finset.instEmptyCollection.{apfNative_uK} (Rec g)))),
  @Eq.{1} NNReal
    (calibration g (resource g (@APFPaper1.Continuation.nullWord.{apfNative_uC, apfNative_uF} Context Frag g)))
    (@OfNat.ofNat.{0} NNReal (nat_lit 0) (@Zero.toOfNat0.{0} NNReal NNReal.instZero)) := by
  exact @APFPaper1.Continuation.bill_nullWord_of_sum
