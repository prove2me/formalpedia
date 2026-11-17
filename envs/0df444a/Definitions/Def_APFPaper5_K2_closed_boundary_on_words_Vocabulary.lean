-- Prove2me | Definitions.Def_APFPaper5_K2_closed_boundary_on_words_Vocabulary
-- name    : APFPaper5_K2_closed_boundary_on_words_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:23:07.108235+00:00
-- url     : https://prove2.me/theorems/4cf2c2b9-1f93-4649-a186-91a9381821b7
-- title:
--   Model vocabulary — Congruence and score-null results for supplied words
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   Theorems concern supplied admission, value and score data; ZeroConvention is retained where used. Point separation is built into ReadoutEq and does not prove separation of linear combinations, physical readout coverage, a finite-dimensional algebra or an adjoint.
--
--   **Supplied data and hypotheses**
--
--   - Every parameter and hypothesis in the exact source declaration remains exposed; no author input is adopted.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Theorems.Thm_APFPaper5_K2_closed_boundary_on_words; Pullbacks v39, SHA-256 53befb18d62f4f7ca23091d8275015586b7d38d3cc263a68544f0abab264b9e5. Theorems.Thm_APFPaper5_K2_closed_boundary_on_words; pullbacks v39; SHA-256 53befb18d62f4f7ca23091d8275015586b7d38d3cc263a68544f0abab264b9e5

import Definitions.Def_APFPaper1_ContextualEquivalence
import Definitions.Def_APFPaper5_K2_ClosedBoundary
import Theorems.Thm_APFPaper1_Continuation_contextEq_sandwich
import Theorems.Thm_APFPaper1_Continuation_contextEq_sandwich_all
import Theorems.Thm_APFPaper1_Continuation_contextEq_all_of_ambientHeredity
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
/-
APF Foundation Ledger — theorem node. DRAFT for author and cold review. Not gated, not released, not uploaded.
name: APFPaper1.Continuation.contextEq_sandwich
title: Contextual equivalence is a strong congruence, under ambient heredity; unconditionally when every word is an ambient
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:3284-3298 (lemma and proof), 3301 (W-her).
consumes: no declared input. Named hypothesis in the general form: AmbientHeredity. That hypothesis is NOT an
  adopted input; the Supplement obtains it from W-her, which it calls hypothesized and not derived.
statement:
  (1) ContextEq is reflexive, symmetric and transitive.
  (2) Strong congruence. Under AmbientHeredity, if W and W' are contextually equivalent then so are
      "Lw, then W, then Rw" and "Lw, then W', then Rw", for all words Lw and Rw of matching type.
  (3) With every word an ambient, AmbientHeredity holds trivially, so (2) is unconditional for that relation.
  (4) Contiguous-subword heredity implies AmbientHeredity for the admissible-word ambient class.
  (5) The all-word relation implies the relation restricted to any ambient class. No hypothesis.
  (6) Under AmbientHeredity the restricted relation implies the all-word relation. With (5): under AmbientHeredity
      the two relations are the same.
label: (2) is CONDITIONAL in its general form. (3) is unconditional and is about the all-ambient relation. By (5)
  and (6) that relation coincides with the Supplement's relation whenever AmbientHeredity holds for the
  Supplement's admissible words, which (4) obtains from W-her. Coincidence without heredity is not claimed.
-/


set_option autoImplicit false
namespace APFPaper1.Continuation

universe uC uF uX uV
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {Val : Type uV}

/-- Re-bracketing: `P`, then (`Lw`, `M`, `Rw`), then `S` is (`P`,`Lw`), then `M`, then (`Rw`,`S`). -/
theorem sandwich_reassoc {g a' a b b' c : Context} (P : Word Frag g a') (Lw : Word Frag a' a)
    (M : Word Frag a b) (Rw : Word Frag b b') (S : Word Frag b' c) :
    sandwich P (Lw.append (M.append Rw)) S = sandwich (P.append Lw) M (Rw.append S) := by
  simp only [sandwich, Word.append_assoc]





theorem contextEq_trans (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    (Amb : (g h : Context) → Word Frag g h → Prop) {a b : Context} (W W' W'' : Word Frag a b)
    (h : ContextEq Defd value Amb W W') (h' : ContextEq Defd value Amb W' W'') :
    ContextEq Defd value Amb W W'' :=
  fun g c P S x hP hS =>
    ⟨(h g c P S x hP hS).1.trans (h' g c P S x hP hS).1,
     fun h1 h3 =>
       have h2 := (h g c P S x hP hS).1.mp h1
       ((h g c P S x hP hS).2 h1 h2).trans ((h' g c P S x hP hS).2 h2 h3)⟩











end APFPaper1.Continuation

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







set_option autoImplicit false
open APFPaper1.Continuation

namespace APFPaper5.K2

universe uC uF uX uV uR uI
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {Val : Type uV}

/-! ### The classes multiply -/

/-- Following two readout-equivalent words with one word keeps them readout-equivalent. -/
theorem readoutEq_append_right (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    {a b c : Context} (W W' : Word Frag a b) (R : Word Frag b c)
    (h : ReadoutEq Defd value W W') : ReadoutEq Defd value (W.append R) (W'.append R) :=
  contextEq_sandwich_all Defd value (Word.nil a) R W W' h

/-- Preceding two readout-equivalent words with one word keeps them readout-equivalent. -/
theorem readoutEq_append_left (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    {a b c : Context} (L : Word Frag a b) (W W' : Word Frag b c)
    (h : ReadoutEq Defd value W W') : ReadoutEq Defd value (L.append W) (L.append W') := by
  have h' := contextEq_sandwich_all Defd value L (Word.nil c) W W' h
  simpa only [Word.append_nil] using h'



/-- The product of two classes of closed words: the class of one word followed by the other. -/
def mulClass (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val) {a : Context} :
    ClosedClass Defd value a → ClosedClass Defd value a → ClosedClass Defd value a :=
  Quot.lift
    (fun W : Word Frag a a =>
      Quot.lift (fun U : Word Frag a a => (Quot.mk _ (W.append U) : ClosedClass Defd value a))
        (fun U U' hU => Quot.sound (readoutEq_append_left Defd value W U U' hU)))
    (fun W W' hW => by
      funext q
      induction q using Quot.ind with
      | mk U => exact Quot.sound (readoutEq_append_right Defd value W W' U hW))

/-- The class of the empty word. -/
def oneClass (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val) (a : Context) :
    ClosedClass Defd value a :=
  Quot.mk _ (Word.nil a)









/-! ### The word admitted nowhere is the zero -/













/-! ### Words that differ are told apart by a completed word -/











/-! ### The combinations no score can see -/







/-! ### The admission score -/











end APFPaper5.K2


