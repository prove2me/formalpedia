-- Prove2me | solution 1 for APFPaper1.Continuation.cont_prefix_of_sum_and_keep
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T02:40:26.949059+00:00
-- url     : https://prove2.me/submissions/6d47ae3e-fd7a-4a9c-8246-1ba3c5c8bb55

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper1_Cont_prefix_from_sum_and_keep
title: If the bill of a word is the sum of the costs of the records it keeps and a step erases nothing, then an initial segment never bills more than the whole, prefix restriction holds for the whole-word class, and that class is the hereditary class; with one more clause, contiguous-subword heredity holds too
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: FOUNDATION_INPUTS B07a, whose definition node binds A2's price to "the ORIGINAL total admissibility
 cost (sum of distinction costs in the adopted Paper0 statement)". RECORDS, named on 2026-11-12 as the
 hypothesis of the record-book side: "each distinction has its own set of records, each record has its own
 cost, and a protocol's bill is the sum of the costs of the records it maintains" (a named hypothesis, not
 a declared input; RULING_records_clause_2026-11-12, RULING_bill_is_a_sum_2026-11-13,
 Thm_APFPaper5_K1_bill_is_a_sum of seat 01WrrBvu). The author, 2026-11-13:
 15:39 HST "Distinctions aren't drawn or erased, just rearranged" (adopted scoped to a hold); 17:30 HST "The
 step acts on the full family and changes the alignment of the occupant" (typed by seat 01WrrBvu as: after
 the step every distinction of the family is still held). Paper 1 Supplement v9.28:1231 (C3), 2209-2213
 (calibration), 3301 (W-her; "fragment-monotone budgets (running less of an admissible protocol never costs
 more)"). Def_APFPaper1_ContinuationWords, Thm_APFPaper1_Cont_prefix_restriction,
 Def_APFPaper1_ContextualEquivalence (seat 01WrrBvu). Codebank: nothing on this.
consumes_inputs: none as a declared predicate. The two clauses below are typed here on words, with "what a
 word keeps" a supplied function. Whether that typing is what the author's sentences mean is for the author.
the clauses:
 SUM (hsum): the calibrated resource of a word is the sum, over the records the word keeps, of their costs.
  Costs are nonnegative reals.
 KEEP (hkeep): a step erases nothing: every record a word keeps is kept by that word followed by one more
  fragment.
 AFTER (hafter): what a word keeps on its own it still keeps when it is run after one more fragment.
 CAPACITY (hcap): capacity does not shrink along a word: the context a word ends in has at least the
  capacity of the context it starts in.
statement: (kept_subset_of_isPrefix) KEEP, stated for one step, gives it for every initial segment.
 (prefixMonotone_of_sum_and_keep) SUM and KEEP give PrefixMonotone. (cont_prefix_of_sum_and_keep) so C3
 holds for the whole-word class, and (cont_iff_contHereditary_of_sum_and_keep) the whole-word class is the
 hereditary class: budget tested on the whole word and budget tested at every stage agree.
 (kept_subset_sandwich) KEEP and AFTER give: a contiguous subword keeps nothing the whole word does not.
 (subwordHeredity_of_subword_bill) for the whole-word class, W-her follows from "a contiguous subword bills
 no more in its own context than the whole word" and CAPACITY. (subwordHeredity_of_sum_and_keeps) so SUM,
 KEEP, AFTER and CAPACITY give W-her, when one record type and one cost function serve every context.
reading: A6 is not a separate hypothesis. It follows from RECORDS, which is already a named hypothesis, and
 from KEEP, which is the author's hold sentence said of every step. Under those two the whole-word budget of
 the ruling of 2026-11-12 and the Supplement's C3 agree. A8 needs AFTER and CAPACITY besides.
not_claimed: SUM, KEEP, AFTER or CAPACITY themselves. They are not consequences of the eight declared
 forms: SUM and KEEP fail together in one supplied world of the eight, and SUM, KEEP and AFTER fail together
 in another (Thm_APFPaper1_Cont_load_worlds; Thm_APFPaper1_Cont_sum_keep_worlds). SUM alone says nothing: any
 bill is the cost of one record named after the word. The content is in SUM with KEEP. CAPACITY is not
 tested by any world of this seat, since each has one context. That the calibrated whole-resource
 bill of the ledger is such a sum is RECORDS, a named hypothesis and not derived; whether A2's price is that
 sum was put to the author by seat 01WrrBvu and is not settled. KEEP is said by the author of a hold and of
 a step on the occupant's family; it is typed here for every fragment of every word, on a supplied "what
 the word keeps". SUM here asks less than RECORDS: nothing about which records a distinction needs.
-/
import Definitions.Def_APFPaper1_ContextualEquivalence
import Theorems.Thm_APFPaper1_Continuation_cont_prefix
import Theorems.Thm_APFPaper1_Continuation_contHereditary_iff_cont
import Theorems.Thm_APFPaper1_Continuation_prefix_closed_iff_hereditary
import Theorems.Thm_APFPaper1_Continuation_prefixMonotone_of_resource_mono
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
namespace APFPaper1.Continuation

universe uC uF uX uR uK
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}

/-- KEEP along any continuation of a word: what `v` keeps, `v` followed by `u` keeps. By induction on `u`,
from the one-fragment statement. -/
theorem kept_subset_append {Rec : Context → Type uK}
    (kept : (g : Context) → WordFrom Frag g → Finset (Rec g))
    (hkeep : ∀ (g h k : Context) (w : Word Frag g h) (f : Frag h k),
      kept g ⟨h, w⟩ ⊆ kept g ⟨k, w.append (Word.single f)⟩) (g : Context) :
    ∀ {a c : Context} (u : Word Frag a c) (v : Word Frag g a),
      kept g ⟨a, v⟩ ⊆ kept g ⟨c, v.append u⟩
  | _, _, Word.nil _, v => by
      intro r hr
      rw [Word.append_nil]
      exact hr
  | _, _, Word.cons f u', v => by
      have h1 := hkeep g _ _ v f
      have h2 := kept_subset_append kept hkeep g u' (v.append (Word.single f))
      have e : (v.append (Word.single f)).append u' = v.append (Word.cons f u') :=
        (Word.append_assoc v (Word.single f) u').trans rfl
      rw [e] at h2
      exact fun r hr => h2 (h1 hr)

/-- An initial segment keeps nothing the whole word does not keep. -/
theorem kept_subset_of_isPrefix {Rec : Context → Type uK}
    (kept : (g : Context) → WordFrom Frag g → Finset (Rec g))
    (hkeep : ∀ (g h k : Context) (w : Word Frag g h) (f : Frag h k),
      kept g ⟨h, w⟩ ⊆ kept g ⟨k, w.append (Word.single f)⟩)
    (g : Context) (v w : WordFrom Frag g) (hpre : IsPrefix v w) : kept g v ⊆ kept g w := by
  obtain ⟨u, hu⟩ := hpre
  have h := kept_subset_append kept hkeep g u v.2
  rw [← hu] at h
  exact h

/-- SUM and KEEP give prefix-monotone bills. -/
theorem prefixMonotone_of_sum_and_keep {Rec : Context → Type uK}
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (kept : (g : Context) → WordFrom Frag g → Finset (Rec g))
    (cost : (g : Context) → Rec g → NNReal)
    (hsum : ∀ (g : Context) (w : WordFrom Frag g),
      calibration g (resource g w) = ∑ r ∈ kept g w, cost g r)
    (hkeep : ∀ (g h k : Context) (w : Word Frag g h) (f : Frag h k),
      kept g ⟨h, w⟩ ⊆ kept g ⟨k, w.append (Word.single f)⟩) :
    PrefixMonotone resource calibration := by
  intro g v w hpre
  rw [hsum g v, hsum g w]
  exact Finset.sum_le_sum_of_subset (kept_subset_of_isPrefix kept hkeep g v w hpre)

/-- C3 for the whole-word class, from SUM and KEEP. -/
theorem cont_prefix_of_sum_and_keep {Rec : Context → Type uK}
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (kept : (g : Context) → WordFrom Frag g → Finset (Rec g))
    (cost : (g : Context) → Rec g → NNReal)
    (hsum : ∀ (g : Context) (w : WordFrom Frag g),
      calibration g (resource g w) = ∑ r ∈ kept g w, cost g r)
    (hkeep : ∀ (g h k : Context) (w : Word Frag g h) (f : Frag h k),
      kept g ⟨h, w⟩ ⊆ kept g ⟨k, w.append (Word.single f)⟩)
    (g : Context) (x : Raw g) (v w : WordFrom Frag g) (hpre : IsPrefix v w)
    (hw : Cont step resource calibration C g x w) : Cont step resource calibration C g x v :=
  cont_prefix step resource calibration C
    (prefixMonotone_of_sum_and_keep resource calibration kept cost hsum hkeep) g x v w hpre hw

/-- Under SUM and KEEP the whole-word class is the hereditary class. -/
theorem cont_iff_contHereditary_of_sum_and_keep {Rec : Context → Type uK}
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (kept : (g : Context) → WordFrom Frag g → Finset (Rec g))
    (cost : (g : Context) → Rec g → NNReal)
    (hsum : ∀ (g : Context) (w : WordFrom Frag g),
      calibration g (resource g w) = ∑ r ∈ kept g w, cost g r)
    (hkeep : ∀ (g h k : Context) (w : Word Frag g h) (f : Frag h k),
      kept g ⟨h, w⟩ ⊆ kept g ⟨k, w.append (Word.single f)⟩)
    (g : Context) (x : Raw g) (w : WordFrom Frag g) :
    Cont step resource calibration C g x w ↔ ContHereditary step resource calibration C g x w :=
  (contHereditary_iff_cont step resource calibration C
    (prefixMonotone_of_sum_and_keep resource calibration kept cost hsum hkeep) g x w).symm

/-! ### Contiguous subwords -/

/-- KEEP and AFTER give: a contiguous subword keeps nothing the whole word does not keep. One record type
serves every context. -/
theorem kept_subset_sandwich {Rec : Type uK}
    (kept : (g : Context) → WordFrom Frag g → Finset Rec)
    (hkeep : ∀ (g h k : Context) (w : Word Frag g h) (f : Frag h k),
      kept g ⟨h, w⟩ ⊆ kept g ⟨k, w.append (Word.single f)⟩)
    (hafter : ∀ (g h k : Context) (f : Frag g h) (w : Word Frag h k),
      kept h ⟨k, w⟩ ⊆ kept g ⟨k, Word.cons f w⟩) :
    ∀ {g a : Context} (A : Word Frag g a) {b c : Context} (M : Word Frag a b) (B : Word Frag b c),
      kept a ⟨b, M⟩ ⊆ kept g (sandwich A M B)
  | _, _, Word.nil _, _, _, M, B =>
      kept_subset_append (Rec := fun _ => Rec) kept hkeep _ B M
  | _, _, Word.cons f A', _, _, M, B => fun _ hr =>
      hafter _ _ _ f (A'.append (M.append B)) (kept_subset_sandwich kept hkeep hafter A' M B hr)

/-- W-her for the whole-word class, from a clause on bills and a clause on capacities. A word is admissible
when it is in Cont from some raw possibility. -/
theorem subwordHeredity_of_subword_bill
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (hsub : ∀ (g a b c : Context) (A : Word Frag g a) (M : Word Frag a b) (B : Word Frag b c),
      calibration a (resource a ⟨b, M⟩) ≤ calibration g (resource g (sandwich A M B)))
    (hcap : ∀ (g a : Context), Word Frag g a → C g ≤ C a) :
    SubwordHeredity (Cont step resource calibration C)
      (fun g h M => ∃ x : Raw g, Cont step resource calibration C g x ⟨h, M⟩) := by
  intro g a b c A M B x hdef
  obtain ⟨⟨z, hz⟩, hbill⟩ := hdef
  have hz' : Executes step (A.append (M.append B)) x z := hz
  obtain ⟨y, _, hy⟩ := (executes_append step A (M.append B) x z).mp hz'
  obtain ⟨y', hM, _⟩ := (executes_append step M B y z).mp hy
  show ∃ x' : Raw a, Cont step resource calibration C a x' ⟨b, M⟩
  exact ⟨y, ⟨y', hM⟩, le_trans (hsub g a b c A M B) (le_trans hbill (hcap g a A))⟩

/-- SUM, KEEP, AFTER and CAPACITY give W-her for the whole-word class. -/
theorem subwordHeredity_of_sum_and_keeps {Rec : Type uK}
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (kept : (g : Context) → WordFrom Frag g → Finset Rec) (cost : Rec → NNReal)
    (hsum : ∀ (g : Context) (w : WordFrom Frag g),
      calibration g (resource g w) = ∑ r ∈ kept g w, cost r)
    (hkeep : ∀ (g h k : Context) (w : Word Frag g h) (f : Frag h k),
      kept g ⟨h, w⟩ ⊆ kept g ⟨k, w.append (Word.single f)⟩)
    (hafter : ∀ (g h k : Context) (f : Frag g h) (w : Word Frag h k),
      kept h ⟨k, w⟩ ⊆ kept g ⟨k, Word.cons f w⟩)
    (hcap : ∀ (g a : Context), Word Frag g a → C g ≤ C a) :
    SubwordHeredity (Cont step resource calibration C)
      (fun g h M => ∃ x : Raw g, Cont step resource calibration C g x ⟨h, M⟩) :=
  subwordHeredity_of_subword_bill step resource calibration C
    (fun g a b c A M B => by
      rw [hsum a, hsum g]
      exact Finset.sum_le_sum_of_subset (kept_subset_sandwich kept hkeep hafter A M B))
    hcap

end APFPaper1.Continuation

#print axioms APFPaper1.Continuation.kept_subset_of_isPrefix
#print axioms APFPaper1.Continuation.prefixMonotone_of_sum_and_keep
#print axioms APFPaper1.Continuation.cont_prefix_of_sum_and_keep
#print axioms APFPaper1.Continuation.cont_iff_contHereditary_of_sum_and_keep
#print axioms APFPaper1.Continuation.kept_subset_sandwich
#print axioms APFPaper1.Continuation.subwordHeredity_of_subword_bill
#print axioms APFPaper1.Continuation.subwordHeredity_of_sum_and_keeps


universe apfNative_uC apfNative_uF apfNative_uX apfNative_uR apfNative_uK
theorem solution :
∀ {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF} {Raw : Context → Type apfNative_uX}
  {R : Context → Type apfNative_uR} {Rec : Context → Type apfNative_uK}
  (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
  (kept :
    (g : Context) →
      @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g → Finset.{apfNative_uK} (Rec g))
  (cost : (g : Context) → Rec g → NNReal)
  (hsum :
    ∀ (g : Context) (w : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g),
      @Eq.{1} NNReal (calibration g (resource g w))
        (@Finset.sum.{apfNative_uK, 0} (Rec g) NNReal (@Semiring.toAddCommMonoid.{0} NNReal NNReal.instSemiring)
          (kept g w) fun (r : Rec g) => cost g r))
  (hkeep :
    ∀ (g h k : Context) (w : @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h) (f : Frag h k),
      @LE.le.{apfNative_uK} (Finset.{apfNative_uK} (Rec g))
        (@Preorder.toLE.{apfNative_uK} (Finset.{apfNative_uK} (Rec g))
          (@PartialOrder.toPreorder.{apfNative_uK} (Finset.{apfNative_uK} (Rec g))
            (@Finset.instPartialOrder.{apfNative_uK} (Rec g))))
        (kept g
          (@Sigma.mk.{apfNative_uC, max apfNative_uC apfNative_uF} Context
            (fun (h : Context) => @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h) h w))
        (kept g
          (@Sigma.mk.{apfNative_uC, max apfNative_uC apfNative_uF} Context
            (fun (h : Context) => @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag g h) k
            (@APFPaper1.Continuation.Word.append.{apfNative_uC, apfNative_uF} Context Frag g h k w
              (@APFPaper1.Continuation.Word.single.{apfNative_uC, apfNative_uF} Context Frag h k f)))))
  (g : Context) (x : Raw g) (v w : @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g)
  (hpre : @APFPaper1.Continuation.IsPrefix.{apfNative_uC, apfNative_uF} Context Frag g v w)
  (hw :
    @APFPaper1.Continuation.Cont.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR} Context Frag Raw R step
      resource calibration C g x w),
  @APFPaper1.Continuation.Cont.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR} Context Frag Raw R step resource
    calibration C g x v := by
  exact @APFPaper1.Continuation.cont_prefix_of_sum_and_keep
