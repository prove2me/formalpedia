-- Prove2me | solution 1 for APFPaper5.K2.SplitWorld.defd_iff
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:57:02.538376+00:00
-- url     : https://prove2.me/submissions/336d9121-b468-4d3b-9f44-cd0c43db9560

import Definitions.Def_APFPaper5_K2_split_world_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K2_split_world
title: A yes/no test on words: the three closed words are told apart, yet "yes" plus "no" minus "the sure test" is a combination no admission score can see
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 5 Supplement v7.33:829-843 (contextual null lies inside score null; "equality holds exactly
 when the induced completed-score family separates the linearized contextual quotient"), 3009-3011 ("even
 point separation of original words would not establish linear separation of their formal real
 combinations"), 3042-3048 (K2: "linear score separation"). Def_APFPaper5_K2_ClosedBoundary.
model: one context. Two raw possibilities, false and true. Three fragments, each leaving the raw possibility
 as it is: A runs only from false, B runs only from true, Cc runs from both. Every word is free (bill 0,
 capacity 0). "Defined" is Cont: the word runs and its bill is within capacity.
shown:
 - (executes_iff, runsAt_append, defd_iff, defd_sandwich_iff) a word runs from a raw possibility exactly
   when each of its fragments does, and then it ends where it began.
 - (A_B_apart, A_C_apart, B_C_apart) the one-fragment words A, B and Cc are pairwise told apart, whatever
   value is read.
 - (sum_split, split_is_score_null) inside every prefix and suffix, at every raw input, the admission score
   of A plus that of B is that of Cc. So the combination A + B - Cc is one no admission score can see, and
   its three coefficients are not zero (coef_ne_zero).
 - (points_apart_and_a_combination_no_score_sees) the two together: the words are separated one by one and
   their real combinations are not.
 - (sure_test_is_empty_word) with nothing read but admission, Cc is readout-equivalent to the empty word.
 - (A_then_B_never) A followed by B is admitted nowhere: it is the zero class.
 - (A_twice_is_A) with nothing read but admission, A followed by A is readout-equivalent to A.
reading: the classes here are the empty word, A, B and the zero: one yes/no test. "The sure test is yes
 plus no" is the relation the real combinations must satisfy and the classes one by one do not. So the two
 null spaces of Paper 5 differ in this world, and they differ wherever a sure test splits in two.
not shown: that this model meets any declared input (not checked against the eight). That the admission
 score is the physical score. Anything about worlds with other scores.
not claimed: No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or
 that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K2_ClosedBoundary
import Definitions.Def_APFPaper5_K2_closed_boundary_on_words_Vocabulary
import Theorems.Thm_APFPaper5_K2_readoutEq_append
import Theorems.Thm_APFPaper5_K2_mulClass_assoc
import Theorems.Thm_APFPaper5_K2_oneClass_mul
import Theorems.Thm_APFPaper5_K2_mul_oneClass
import Theorems.Thm_APFPaper5_K2_neverDefined_sandwich
import Theorems.Thm_APFPaper5_K2_readoutEq_of_neverDefined
import Theorems.Thm_APFPaper5_K2_never_class_mul
import Theorems.Thm_APFPaper5_K2_mul_never_class
import Theorems.Thm_APFPaper5_K2_toldApart_of_not_readoutEq
import Theorems.Thm_APFPaper5_K2_not_readoutEq_of_toldApart
import Theorems.Thm_APFPaper5_K2_not_readoutEq_iff_toldApart
import Theorems.Thm_APFPaper5_K2_toldApart_one_is_defined
import Theorems.Thm_APFPaper5_K2_told_apart_by_admitted_word
import Theorems.Thm_APFPaper5_K2_scoreNull_sandwich
import Theorems.Thm_APFPaper5_K2_score_eq_of_readoutEq
import Theorems.Thm_APFPaper5_K2_scoreNull_pair_of_readoutEq
import Theorems.Thm_APFPaper5_K2_admissionScore_of_defd
import Theorems.Thm_APFPaper5_K2_admissionScore_of_not_defd
import Theorems.Thm_APFPaper5_K2_admissionScore_zeroConvention
import Theorems.Thm_APFPaper5_K2_admissionScore_eq_one_iff
import Theorems.Thm_APFPaper5_K2_readoutEq_iff_admissionScore_eq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open APFPaper1.Continuation

namespace APFPaper5.K2.SplitWorld

universe uV


















theorem runsAt_nil (g : Unit) (x : Bool) : runsAt (Word.nil (Frag := Frag) g) x := by
  show True
  trivial

theorem executes_iff : ∀ {g h : Unit} (w : Word Frag g h) (x : Raw g) (z : Raw h),
    Executes step w x z ↔ runsAt w x ∧ z = x := by
  intro g h w
  induction w with
  | nil g =>
    intro x z
    constructor
    · intro hx
      exact ⟨runsAt_nil g x, (show x = z from hx).symm⟩
    · intro hx
      exact (show x = z from hx.2.symm)
  | cons f w ih =>
    intro x z
    rw [executes_cons]
    constructor
    · rintro ⟨y, ⟨hf, hy⟩, hw⟩
      obtain ⟨hr, hz⟩ := (ih y z).mp hw
      have hy' : y = x := hy
      rw [hy'] at hr hz
      exact And.intro (show letterRuns f x ∧ runsAt w x from ⟨hf, hr⟩) hz
    · intro hx
      have hx1 : letterRuns f x ∧ runsAt w x := hx.1
      exact ⟨x, ⟨hx1.1, rfl⟩, (ih x z).mpr ⟨hx1.2, hx.2⟩⟩

theorem runsAt_append : ∀ {g h k : Unit} (w : Word Frag g h) (u : Word Frag h k) (x : Bool),
    runsAt (w.append u) x ↔ runsAt w x ∧ runsAt u x := by
  intro g h k w
  induction w with
  | nil g =>
    intro u x
    exact ⟨fun hu => ⟨runsAt_nil g x, hu⟩, fun hu => hu.2⟩
  | cons f w ih =>
    intro u x
    show letterRuns f x ∧ runsAt (w.append u) x ↔ (letterRuns f x ∧ runsAt w x) ∧ runsAt u x
    rw [ih u x, and_assoc]

/-- A word is in the continuation class of a raw possibility exactly when each of its fragments runs there. -/
theorem defd_iff (g : Unit) (x : Raw g) (w : WordFrom Frag g) : Defd g x w ↔ runsAt w.2 x := by
  constructor
  · rintro ⟨⟨y, hy⟩, _⟩
    exact ((executes_iff w.2 x y).mp hy).1
  · intro h
    exact ⟨⟨x, (executes_iff w.2 x x).mpr ⟨h, rfl⟩⟩, le_refl _⟩

theorem defd_sandwich_iff {g a b c : Unit} (P : Word Frag g a) (W : Word Frag a b)
    (S : Word Frag b c) (x : Raw g) :
    Defd g x (sandwich P W S) ↔ runsAt P x ∧ runsAt W x ∧ runsAt S x := by
  rw [defd_iff]
  show runsAt (P.append (W.append S)) x ↔ _
  rw [runsAt_append, runsAt_append]



theorem runsAt_word (l : Letter) (x : Bool) : runsAt (word l) x ↔ letterRuns l x := by
  show letterRuns l x ∧ True ↔ letterRuns l x
  exact ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

theorem runs_A (x : Bool) : letterRuns Letter.A x ↔ x = false := Iff.rfl
theorem runs_B (x : Bool) : letterRuns Letter.B x ↔ x = true := Iff.rfl
theorem runs_C (x : Bool) : letterRuns Letter.Cc x := by
  show True
  trivial

/-! ### The three words are told apart -/

theorem A_B_apart {Val : Type uV} (value : (g : Unit) → WordFrom Frag g → Raw g → Val) :
    ¬ ReadoutEq Defd value (word Letter.A) (word Letter.B) := by
  intro h
  have h1 := (h () () (Word.nil ()) (Word.nil ()) false trivial trivial).1
  rw [defd_sandwich_iff, defd_sandwich_iff] at h1
  have hB := (h1.mp ⟨runsAt_nil () false, (runsAt_word _ _).mpr ((runs_A false).mpr rfl),
    runsAt_nil () false⟩).2.1
  exact Bool.false_ne_true ((runs_B false).mp ((runsAt_word _ _).mp hB))

theorem A_C_apart {Val : Type uV} (value : (g : Unit) → WordFrom Frag g → Raw g → Val) :
    ¬ ReadoutEq Defd value (word Letter.A) (word Letter.Cc) := by
  intro h
  have h1 := (h () () (Word.nil ()) (Word.nil ()) true trivial trivial).1
  rw [defd_sandwich_iff, defd_sandwich_iff] at h1
  have hA := (h1.mpr ⟨runsAt_nil () true, (runsAt_word _ _).mpr (runs_C true),
    runsAt_nil () true⟩).2.1
  exact Bool.false_ne_true ((runs_A true).mp ((runsAt_word _ _).mp hA)).symm

theorem B_C_apart {Val : Type uV} (value : (g : Unit) → WordFrom Frag g → Raw g → Val) :
    ¬ ReadoutEq Defd value (word Letter.B) (word Letter.Cc) := by
  intro h
  have h1 := (h () () (Word.nil ()) (Word.nil ()) false trivial trivial).1
  rw [defd_sandwich_iff, defd_sandwich_iff] at h1
  have hB := (h1.mpr ⟨runsAt_nil () false, (runsAt_word _ _).mpr (runs_C false),
    runsAt_nil () false⟩).2.1
  exact Bool.false_ne_true ((runs_B false).mp ((runsAt_word _ _).mp hB))

/-! ### Yes plus no is the sure test, for every admission score -/

theorem sum_split {g c : Unit} (P : Word Frag g ()) (S : Word Frag () c) (x : Raw g) :
    admissionScore Defd g (sandwich P (word Letter.A) S) x +
        admissionScore Defd g (sandwich P (word Letter.B) S) x =
      admissionScore Defd g (sandwich P (word Letter.Cc) S) x := by
  classical
  by_cases hPS : runsAt P x ∧ runsAt S x
  · have hC : Defd g x (sandwich P (word Letter.Cc) S) :=
      (defd_sandwich_iff P _ S x).mpr ⟨hPS.1, (runsAt_word _ _).mpr (runs_C x), hPS.2⟩
    by_cases hx : x = false
    · have hA : Defd g x (sandwich P (word Letter.A) S) :=
        (defd_sandwich_iff P _ S x).mpr ⟨hPS.1, (runsAt_word _ _).mpr ((runs_A x).mpr hx), hPS.2⟩
      have hB : ¬ Defd g x (sandwich P (word Letter.B) S) := fun hd => by
        have hb := (runs_B x).mp ((runsAt_word _ _).mp ((defd_sandwich_iff P _ S x).mp hd).2.1)
        rw [hx] at hb
        exact Bool.false_ne_true hb
      rw [admissionScore_of_defd Defd g _ x hA, admissionScore_of_not_defd Defd g _ x hB,
        admissionScore_of_defd Defd g _ x hC]
      norm_num
    · have hx' : x = true := by
        cases x with
        | false => exact absurd rfl hx
        | true => rfl
      have hA : ¬ Defd g x (sandwich P (word Letter.A) S) := fun hd =>
        hx ((runs_A x).mp ((runsAt_word _ _).mp ((defd_sandwich_iff P _ S x).mp hd).2.1))
      have hB : Defd g x (sandwich P (word Letter.B) S) :=
        (defd_sandwich_iff P _ S x).mpr ⟨hPS.1, (runsAt_word _ _).mpr ((runs_B x).mpr hx'), hPS.2⟩
      rw [admissionScore_of_not_defd Defd g _ x hA, admissionScore_of_defd Defd g _ x hB,
        admissionScore_of_defd Defd g _ x hC]
      norm_num
  · have hn : ∀ l : Letter, ¬ Defd g x (sandwich P (word l) S) := fun l hd =>
      hPS ⟨((defd_sandwich_iff P _ S x).mp hd).1, ((defd_sandwich_iff P _ S x).mp hd).2.2⟩
    rw [admissionScore_of_not_defd Defd g _ x (hn Letter.A),
      admissionScore_of_not_defd Defd g _ x (hn Letter.B),
      admissionScore_of_not_defd Defd g _ x (hn Letter.Cc)]
    norm_num





theorem letter_zero : letter 0 = Letter.A := by
  unfold letter
  rw [if_pos rfl]

theorem letter_one : letter 1 = Letter.B := by
  unfold letter
  rw [if_neg (by decide), if_pos rfl]

theorem letter_two : letter 2 = Letter.Cc := by
  unfold letter
  rw [if_neg (by decide), if_neg (by decide)]

theorem coef_zero : coef 0 = 1 := by
  unfold coef
  rw [if_neg (by decide)]

theorem coef_one : coef 1 = 1 := by
  unfold coef
  rw [if_neg (by decide)]

theorem coef_two : coef 2 = -1 := by
  unfold coef
  rw [if_pos rfl]

theorem coef_ne_zero (i : Fin 3) : coef i ≠ 0 := by
  unfold coef
  by_cases h : i = 2
  · rw [if_pos h]
    norm_num
  · rw [if_neg h]
    norm_num

/-- "Yes plus no minus the sure test" is a combination no admission score can see. -/
theorem split_is_score_null :
    ScoreNull (admissionScore Defd) coef (fun i => word (letter i)) := by
  intro g c P S x
  show ∑ i : Fin 3, coef i * admissionScore Defd g (sandwich P (word (letter i)) S) x = 0
  rw [Fin.sum_univ_three, coef_zero, coef_one, coef_two, letter_zero, letter_one, letter_two]
  have e := sum_split P S x
  linarith

/-- The words are separated one by one, and their real combinations are not. -/
theorem points_apart_and_a_combination_no_score_sees {Val : Type uV}
    (value : (g : Unit) → WordFrom Frag g → Raw g → Val) :
    (¬ ReadoutEq Defd value (word Letter.A) (word Letter.B) ∧
      ¬ ReadoutEq Defd value (word Letter.A) (word Letter.Cc) ∧
      ¬ ReadoutEq Defd value (word Letter.B) (word Letter.Cc)) ∧
    ScoreNull (admissionScore Defd) coef (fun i => word (letter i)) ∧ ∀ i, coef i ≠ 0 :=
  ⟨⟨A_B_apart value, A_C_apart value, B_C_apart value⟩, split_is_score_null, coef_ne_zero⟩

/-! ### The classes: the empty word, A, B and the zero -/

/-- With nothing read but admission, the sure test is the empty word. -/
theorem sure_test_is_empty_word :
    ReadoutEq Defd (fun (_ : Unit) (_ : WordFrom Frag _) (_ : Raw _) => ()) (word Letter.Cc)
      (Word.nil ()) := by
  intro g c P S x _ _
  refine ⟨?_, fun _ _ => rfl⟩
  rw [defd_sandwich_iff, defd_sandwich_iff]
  exact ⟨fun h => ⟨h.1, runsAt_nil () x, h.2.2⟩,
    fun h => ⟨h.1, (runsAt_word _ _).mpr (runs_C x), h.2.2⟩⟩

/-- A followed by B is admitted nowhere. -/
theorem A_then_B_never : NeverDefined Defd ((word Letter.A).append (word Letter.B)) := by
  intro g c P S x hd
  have h := ((defd_sandwich_iff P _ S x).mp hd).2.1
  rw [runsAt_append] at h
  have hA := (runs_A x).mp ((runsAt_word _ _).mp h.1)
  have hB := (runs_B x).mp ((runsAt_word _ _).mp h.2)
  rw [hA] at hB
  exact Bool.false_ne_true hB

/-- With nothing read but admission, A followed by A is A. -/
theorem A_twice_is_A :
    ReadoutEq Defd (fun (_ : Unit) (_ : WordFrom Frag _) (_ : Raw _) => ())
      ((word Letter.A).append (word Letter.A)) (word Letter.A) := by
  intro g c P S x _ _
  refine ⟨?_, fun _ _ => rfl⟩
  rw [defd_sandwich_iff, defd_sandwich_iff, runsAt_append]
  exact ⟨fun h => ⟨h.1, h.2.1.1, h.2.2⟩, fun h => ⟨h.1, ⟨h.2.1, h.2.1⟩, h.2.2⟩⟩

end APFPaper5.K2.SplitWorld


theorem solution :
∀ (g : Unit) (x : APFPaper5.K2.SplitWorld.Raw g)
  (w : @APFPaper1.Continuation.WordFrom.{0, 0} Unit APFPaper5.K2.SplitWorld.Frag g),
  Iff (APFPaper5.K2.SplitWorld.Defd g x w)
    (@APFPaper5.K2.SplitWorld.runsAt g
      (@Sigma.fst.{0, 0} Unit
        (fun (h : Unit) => @APFPaper1.Continuation.Word.{0, 0} Unit APFPaper5.K2.SplitWorld.Frag g h) w)
      (@Sigma.snd.{0, 0} Unit
        (fun (h : Unit) => @APFPaper1.Continuation.Word.{0, 0} Unit APFPaper5.K2.SplitWorld.Frag g h) w)
      x) := by
  exact @APFPaper5.K2.SplitWorld.defd_iff
