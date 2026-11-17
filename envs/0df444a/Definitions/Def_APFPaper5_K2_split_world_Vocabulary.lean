-- Prove2me | Definitions.Def_APFPaper5_K2_split_world_Vocabulary
-- name    : APFPaper5_K2_split_world_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:51:12.452668+00:00
-- url     : https://prove2.me/theorems/eb958651-9eee-4af0-8e64-fcf6c09c66be
-- title:
--   Model vocabulary — Point separation need not separate linear combinations
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   The supplied one-context model has admission-only score and three pairwise distinct word classes with invisible combination A+B-C. No declared form is verified for this example, and its score is not asserted physical. The sure test is equivalent to the empty word only for trivial values.
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
--   Theorems.Thm_APFPaper5_K2_split_world; Pullbacks v39, SHA-256 ab8c5d883c4869eacb9234c07f3222c655df1746ff6238076e60f1ea564a8e57. Theorems.Thm_APFPaper5_K2_split_world; pullbacks v39; SHA-256 ab8c5d883c4869eacb9234c07f3222c655df1746ff6238076e60f1ea564a8e57

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

inductive Letter
  | A
  | B
  | Cc
  deriving DecidableEq

abbrev Frag : Unit → Unit → Type := fun _ _ => Letter
abbrev Raw : Unit → Type := fun _ => Bool
abbrev Res : Unit → Type := fun _ => Unit

/-- Where a fragment runs. -/
def letterRuns : Letter → Bool → Prop
  | Letter.A, x => x = false
  | Letter.B, x => x = true
  | Letter.Cc, _ => True

/-- A fragment runs where `letterRuns` says and leaves the raw possibility as it is. -/
def step : (g h : Unit) → Frag g h → Raw g → Raw h → Prop := fun _ _ f x y => letterRuns f x ∧ y = x
def resource : (g : Unit) → WordFrom Frag g → Res g := fun _ _ => ()
def calibration : (g : Unit) → Res g → NNReal := fun _ _ => 0
def C : Unit → NNReal := fun _ => 0

abbrev Defd : (g : Unit) → Raw g → WordFrom Frag g → Prop := Cont step resource calibration C

/-- Every fragment of the word runs at `x`. -/
def runsAt : {g h : Unit} → Word Frag g h → Bool → Prop
  | _, _, Word.nil _, _ => True
  | _, _, Word.cons f w, x => letterRuns f x ∧ runsAt w x











/-- The one-fragment closed word of a letter. -/
def word (l : Letter) : Word Frag () () := Word.cons (g := ()) (h := ()) (k := ()) l (Word.nil ())







/-! ### The three words are told apart -/







/-! ### Yes plus no is the sure test, for every admission score -/



/-- The three letters, listed. -/
def letter (i : Fin 3) : Letter := if i = 0 then Letter.A else if i = 1 then Letter.B else Letter.Cc

/-- The coefficients of "yes plus no minus the sure test". -/
def coef (i : Fin 3) : ℝ := if i = 2 then -1 else 1



















/-! ### The classes: the empty word, A, B and the zero -/







end APFPaper5.K2.SplitWorld


