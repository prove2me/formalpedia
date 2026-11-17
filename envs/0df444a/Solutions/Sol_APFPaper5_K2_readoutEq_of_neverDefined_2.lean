-- Prove2me | solution 2 for APFPaper5.K2.readoutEq_of_neverDefined
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:44:00.686978+00:00
-- url     : https://prove2.me/submissions/e23afdbb-28a2-4360-8d93-3a8910b0a15d

import Definitions.Def_APFPaper5_K2_closed_boundary_on_words_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K2_closed_boundary_on_words
title: On the foundation's words the closed-boundary classes multiply, words that differ are told apart by an admitted completed word, and the combinations no score can see are closed under every prefix and suffix
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 5 Supplement v7.33:746-789 (readout equivalence is a strong congruence; the null ideal),
 790-843 (score-null space; context saturation; contextual null lies inside score null), 921-930 ("APF must
 still establish that every difference consequential to a committed record is separated by an admitted
 completed context, while every universally record-null direction is quotient-null"), 2999-3013, 3042-3048
 (K2). The builder seat's Thm_APFPaper1_ContextualEquivalence_congruence (strong congruence over all ambient
 words, published on the spine) and Def_APFPaper1_ContinuationWords (Cont).
standing: every statement is about the supplied word data and holds for ANY choice of "defined", value and
 score, except where Cont or the admission score is named. None is a statement that a physical score exists.
consumes_inputs: none. No declared input is used as a hypothesis and none is proved.
theorems:
 - (readoutEq_append_right, readoutEq_append_left, readoutEq_append) readout equivalence is kept by
   following and by preceding with any word, so the product of two classes does not depend on the words
   chosen.
 - (mulClass, oneClass, mulClass_assoc, oneClass_mul, mul_oneClass) the classes of closed words at a
   boundary form a monoid; its unit is the class of the empty word.
 - (neverDefined_sandwich, readoutEq_of_neverDefined, never_class_mul, mul_never_class) a word admitted
   nowhere stays so inside any prefix and suffix; all such words are one class; that class absorbs every
   product. It is the zero of the linearization.
 - (toldApart_of_not_readoutEq, not_readoutEq_of_toldApart, not_readoutEq_iff_toldApart) two words are not
   readout-equivalent exactly when a completed word tells them apart.
 - (toldApart_one_is_defined, told_apart_by_admitted_word) and then at least one of the two completed words
   is defined; with Cont as "defined", it runs from the raw input and its whole bill is within the capacity
   of the context it starts in.
 - (scoreNull_sandwich) a combination no score can see is still unseen after any prefix and suffix are put
   round every word in it. No hypothesis on the score.
 - (score_eq_of_readoutEq, scoreNull_pair_of_readoutEq) under the zero convention, with the score as the
   value read, two readout-equivalent words have the same score everywhere, so their difference is a
   combination no score can see.
 - (admissionScore_zeroConvention, admissionScore_eq_one_iff, readoutEq_iff_admissionScore_eq) for the
   admission score: two words have the same admission in every prefix and suffix at every raw input exactly
   when their admission scores agree everywhere.
not claimed:
 - That the classes are finitely many. Nothing here bounds them; Paper 5 asks for a finite-dimensional
   algebra.
 - An adjoint on the classes, or any use of K1's form. K1's score is a table on distinctions; a rule taking a
   closed word to the distinctions it holds and reads is not typed.
 - That the differences these words can show are the differences that matter to a record. The relation is
   defined by completed words, so it sees exactly what they see.
 - Certain-effect typing, physical realization of readouts, order soundness, the positive-state premise.
 - No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born is
   derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K2_ClosedBoundary
import Theorems.Thm_APFPaper1_Continuation_contextEq_sandwich
import Theorems.Thm_APFPaper1_Continuation_contextEq_sandwich_all
import Theorems.Thm_APFPaper1_Continuation_contextEq_all_of_ambientHeredity
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

set_option autoImplicit false
open APFPaper1.Continuation

namespace APFPaper5.K2

universe uC uF uX uV uR uI
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {Val : Type uV}

/-! ### The classes multiply -/





/-- Products of readout-equivalent words are readout-equivalent. -/
theorem readoutEq_append (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    {a b c : Context} (W W' : Word Frag a b) (U U' : Word Frag b c)
    (hW : ReadoutEq Defd value W W') (hU : ReadoutEq Defd value U U') :
    ReadoutEq Defd value (W.append U) (W'.append U') :=
  contextEq_trans Defd value (fun _ _ _ => True) _ _ _
    (readoutEq_append_right Defd value W W' U hW) (readoutEq_append_left Defd value W' U U' hU)





theorem mulClass_mk (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val) {a : Context} (W U : Word Frag a a) :
    mulClass Defd value (Quot.mk _ W) (Quot.mk _ U) = Quot.mk _ (W.append U) := rfl

theorem mulClass_assoc (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val) {a : Context}
    (p q r : ClosedClass Defd value a) :
    mulClass Defd value (mulClass Defd value p q) r =
      mulClass Defd value p (mulClass Defd value q r) := by
  induction p using Quot.ind with
  | mk W =>
    induction q using Quot.ind with
    | mk U =>
      induction r using Quot.ind with
      | mk T =>
        show mulClass Defd value (Quot.mk _ (W.append U)) (Quot.mk _ T) =
          mulClass Defd value (Quot.mk _ W) (Quot.mk _ (U.append T))
        rw [mulClass_mk, mulClass_mk, Word.append_assoc]

theorem oneClass_mul (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val) {a : Context}
    (p : ClosedClass Defd value a) : mulClass Defd value (oneClass Defd value a) p = p := by
  induction p using Quot.ind with
  | mk W => rfl

theorem mul_oneClass (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val) {a : Context}
    (p : ClosedClass Defd value a) : mulClass Defd value p (oneClass Defd value a) = p := by
  induction p using Quot.ind with
  | mk W =>
    show mulClass Defd value (Quot.mk _ W) (Quot.mk _ (Word.nil a)) = Quot.mk _ W
    rw [mulClass_mk, Word.append_nil]

/-! ### The word admitted nowhere is the zero -/

/-- A word admitted nowhere stays so inside any prefix and suffix. -/
theorem neverDefined_sandwich (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    {a' a b b' : Context} (L : Word Frag a' a) (R : Word Frag b b') (W : Word Frag a b)
    (h : NeverDefined Defd W) : NeverDefined Defd (L.append (W.append R)) := by
  intro g c P S x
  rw [sandwich_reassoc]
  exact h g c (P.append L) (R.append S) x

theorem neverDefined_append_right (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    {a b c : Context} (W : Word Frag a b) (R : Word Frag b c)
    (h : NeverDefined Defd W) : NeverDefined Defd (W.append R) :=
  neverDefined_sandwich Defd (Word.nil a) R W h

theorem neverDefined_append_left (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    {a b c : Context} (L : Word Frag a b) (W : Word Frag b c)
    (h : NeverDefined Defd W) : NeverDefined Defd (L.append W) := by
  have h' := neverDefined_sandwich Defd L (Word.nil c) W h
  simpa only [Word.append_nil] using h'

/-- Any two words admitted nowhere are readout-equivalent, whatever the value. -/
theorem readoutEq_of_neverDefined (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    {a b : Context} (W W' : Word Frag a b)
    (h : NeverDefined Defd W) (h' : NeverDefined Defd W') : ReadoutEq Defd value W W' :=
  fun g c P S x _ _ =>
    ⟨⟨fun hd => absurd hd (h g c P S x), fun hd => absurd hd (h' g c P S x)⟩,
      fun hd _ => absurd hd (h g c P S x)⟩

/-- The class of a closed word admitted nowhere absorbs a product on the right. -/
theorem never_class_mul (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val) {a : Context} (Z : Word Frag a a)
    (hZ : NeverDefined Defd Z) (p : ClosedClass Defd value a) :
    mulClass Defd value (Quot.mk _ Z) p = Quot.mk _ Z := by
  induction p using Quot.ind with
  | mk W =>
    rw [mulClass_mk]
    exact Quot.sound
      (readoutEq_of_neverDefined Defd value _ _ (neverDefined_append_right Defd Z W hZ) hZ)

/-- The class of a closed word admitted nowhere absorbs a product on the left. -/
theorem mul_never_class (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val) {a : Context} (Z : Word Frag a a)
    (hZ : NeverDefined Defd Z) (p : ClosedClass Defd value a) :
    mulClass Defd value p (Quot.mk _ Z) = Quot.mk _ Z := by
  induction p using Quot.ind with
  | mk W =>
    rw [mulClass_mk]
    exact Quot.sound
      (readoutEq_of_neverDefined Defd value _ _ (neverDefined_append_left Defd W Z hZ) hZ)

/-! ### Words that differ are told apart by a completed word -/

theorem toldApart_of_not_readoutEq (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    {a b : Context} (W W' : Word Frag a b) (h : ¬ ReadoutEq Defd value W W') :
    ToldApart Defd value W W' := by
  classical
  by_contra hn
  apply h
  intro g c P S x _ _
  have hn' : ¬ ((Defd g x (sandwich P W S) ∧ ¬ Defd g x (sandwich P W' S)) ∨
      (¬ Defd g x (sandwich P W S) ∧ Defd g x (sandwich P W' S)) ∨
      (Defd g x (sandwich P W S) ∧ Defd g x (sandwich P W' S) ∧
        value g (sandwich P W S) x ≠ value g (sandwich P W' S) x)) :=
    fun hh => hn ⟨g, c, P, S, x, hh⟩
  refine ⟨⟨fun h1 => ?_, fun h2 => ?_⟩, fun h1 h2 => ?_⟩
  · by_contra h2
    exact hn' (Or.inl ⟨h1, h2⟩)
  · by_contra h1
    exact hn' (Or.inr (Or.inl ⟨h1, h2⟩))
  · by_contra hne
    exact hn' (Or.inr (Or.inr ⟨h1, h2, hne⟩))

theorem not_readoutEq_of_toldApart (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    {a b : Context} (W W' : Word Frag a b) (h : ToldApart Defd value W W') :
    ¬ ReadoutEq Defd value W W' := by
  intro hE
  obtain ⟨g, c, P, S, x, h1 | h1 | h1⟩ := h
  · exact h1.2 ((hE g c P S x trivial trivial).1.mp h1.1)
  · exact h1.1 ((hE g c P S x trivial trivial).1.mpr h1.2)
  · exact h1.2.2 ((hE g c P S x trivial trivial).2 h1.1 h1.2.1)

/-- Two words are not readout-equivalent exactly when a completed word tells them apart. -/
theorem not_readoutEq_iff_toldApart (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    {a b : Context} (W W' : Word Frag a b) :
    ¬ ReadoutEq Defd value W W' ↔ ToldApart Defd value W W' :=
  ⟨toldApart_of_not_readoutEq Defd value W W', not_readoutEq_of_toldApart Defd value W W'⟩

/-- Where two words are told apart, at least one of the two completed words is defined. -/
theorem toldApart_one_is_defined (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    {a b : Context} (W W' : Word Frag a b) (h : ToldApart Defd value W W') :
    ∃ (g c : Context) (P : Word Frag g a) (S : Word Frag b c) (x : Raw g),
      Defd g x (sandwich P W S) ∨ Defd g x (sandwich P W' S) := by
  obtain ⟨g, c, P, S, x, h1 | h1 | h1⟩ := h
  · exact ⟨g, c, P, S, x, Or.inl h1.1⟩
  · exact ⟨g, c, P, S, x, Or.inr h1.2⟩
  · exact ⟨g, c, P, S, x, Or.inl h1.1⟩

/-- On the foundation's continuation class: two words that are not readout-equivalent are told apart by a
completed word that runs from a raw input and whose whole bill is within the capacity of the context it
starts in. -/
theorem told_apart_by_admitted_word {R : Context → Type uR}
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    {a b : Context} (W W' : Word Frag a b)
    (h : ¬ ReadoutEq (Cont step resource calibration C) value W W') :
    ∃ (g c : Context) (P : Word Frag g a) (S : Word Frag b c) (x : Raw g),
      ((∃ y : Raw c, Executes step (P.append (W.append S)) x y) ∧
          calibration g (resource g (sandwich P W S)) ≤ C g) ∨
      ((∃ y : Raw c, Executes step (P.append (W'.append S)) x y) ∧
          calibration g (resource g (sandwich P W' S)) ≤ C g) :=
  toldApart_one_is_defined (Cont step resource calibration C) value W W'
    (toldApart_of_not_readoutEq (Cont step resource calibration C) value W W' h)

/-! ### The combinations no score can see -/

/-- A combination no score can see is still unseen after a prefix and a suffix are put round every word in
it. The scores of completed words are closed under further prefixes and suffixes by reassociation, so no
hypothesis on the score is needed. -/
theorem scoreNull_sandwich {ι : Type uI} [Fintype ι]
    (score : (g : Context) → WordFrom Frag g → Raw g → ℝ)
    {a' a b b' : Context} (coef : ι → ℝ) (w : ι → Word Frag a b)
    (L : Word Frag a' a) (R : Word Frag b b') (h : ScoreNull score coef w) :
    ScoreNull score coef (fun i => L.append ((w i).append R)) := by
  intro g c P S x
  have h' := h g c (P.append L) (R.append S) x
  simpa only [sandwich_reassoc] using h'

/-- Under the zero convention, with the score as the value read, readout-equivalent words have the same
score inside every prefix and suffix at every raw input. -/
theorem score_eq_of_readoutEq (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (score : (g : Context) → WordFrom Frag g → Raw g → ℝ) (hz : ZeroConvention Defd score)
    {a b : Context} (W W' : Word Frag a b) (h : ReadoutEq Defd score W W')
    (g c : Context) (P : Word Frag g a) (S : Word Frag b c) (x : Raw g) :
    score g (sandwich P W S) x = score g (sandwich P W' S) x := by
  classical
  obtain ⟨hiff, hval⟩ := h g c P S x trivial trivial
  by_cases hd : Defd g x (sandwich P W S)
  · exact hval hd (hiff.mp hd)
  · rw [hz g x _ hd, hz g x _ (fun hd' => hd (hiff.mpr hd'))]

/-- So the difference of two readout-equivalent words is a combination no score can see. -/
theorem scoreNull_pair_of_readoutEq (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (score : (g : Context) → WordFrom Frag g → Raw g → ℝ) (hz : ZeroConvention Defd score)
    {a b : Context} (W W' : Word Frag a b) (h : ReadoutEq Defd score W W') :
    ScoreNull score (fun i : Bool => if i then (1 : ℝ) else -1) (fun i : Bool => if i then W else W') := by
  intro g c P S x
  rw [Fintype.sum_bool]
  have e := score_eq_of_readoutEq Defd score hz W W' h g c P S x
  simp only [if_true, Bool.false_eq_true, if_false]
  rw [e]
  ring

/-! ### The admission score -/

theorem admissionScore_of_defd (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (g : Context) (w : WordFrom Frag g) (x : Raw g) (h : Defd g x w) :
    admissionScore Defd g w x = 1 := by
  unfold admissionScore
  rw [if_pos h]

theorem admissionScore_of_not_defd (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (g : Context) (w : WordFrom Frag g) (x : Raw g) (h : ¬ Defd g x w) :
    admissionScore Defd g w x = 0 := by
  unfold admissionScore
  rw [if_neg h]

theorem admissionScore_zeroConvention (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop) :
    ZeroConvention Defd (admissionScore Defd) :=
  fun g x w h => admissionScore_of_not_defd Defd g w x h

theorem admissionScore_eq_one_iff (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (g : Context) (w : WordFrom Frag g) (x : Raw g) :
    admissionScore Defd g w x = 1 ↔ Defd g x w := by
  classical
  constructor
  · intro h
    by_contra hn
    rw [admissionScore_of_not_defd Defd g w x hn] at h
    exact zero_ne_one h
  · exact admissionScore_of_defd Defd g w x

/-- With nothing read but admission: two words are admitted in the same prefixes and suffixes at the same
raw inputs exactly when their admission scores agree everywhere. -/
theorem readoutEq_iff_admissionScore_eq (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    {a b : Context} (W W' : Word Frag a b) :
    ReadoutEq Defd (fun (_ : Context) (_ : WordFrom Frag _) (_ : Raw _) => ()) W W' ↔
      ∀ (g c : Context) (P : Word Frag g a) (S : Word Frag b c) (x : Raw g),
        admissionScore Defd g (sandwich P W S) x = admissionScore Defd g (sandwich P W' S) x := by
  classical
  constructor
  · intro h g c P S x
    have hiff := (h g c P S x trivial trivial).1
    by_cases hd : Defd g x (sandwich P W S)
    · rw [admissionScore_of_defd Defd g _ x hd, admissionScore_of_defd Defd g _ x (hiff.mp hd)]
    · rw [admissionScore_of_not_defd Defd g _ x hd,
        admissionScore_of_not_defd Defd g _ x (fun hd' => hd (hiff.mpr hd'))]
  · intro h g c P S x _ _
    refine ⟨⟨fun hd => ?_, fun hd => ?_⟩, fun _ _ => rfl⟩
    · have e := h g c P S x
      rw [admissionScore_of_defd Defd g _ x hd] at e
      exact (admissionScore_eq_one_iff Defd g _ x).mp e.symm
    · have e := h g c P S x
      rw [admissionScore_of_defd Defd g _ x hd] at e
      exact (admissionScore_eq_one_iff Defd g _ x).mp e

end APFPaper5.K2


universe apfNative_uC apfNative_uF apfNative_uX apfNative_uV
theorem solution :
∀ {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF} {Raw : Context → Type apfNative_uX}
  {Val : Type apfNative_uV}
  (Defd : (g : Context) → Raw g → @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g → Prop)
  (value : (g : Context) → @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g → Raw g → Val)
  {a b : Context} (W W' : @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag a b)
  (h : @APFPaper5.K2.NeverDefined.{apfNative_uC, apfNative_uF, apfNative_uX} Context Frag Raw Defd a b W)
  (h' : @APFPaper5.K2.NeverDefined.{apfNative_uC, apfNative_uF, apfNative_uX} Context Frag Raw Defd a b W'),
  @APFPaper5.K2.ReadoutEq.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uV} Context Frag Raw Val Defd value a b W
    W' := by
  exact @APFPaper5.K2.readoutEq_of_neverDefined
