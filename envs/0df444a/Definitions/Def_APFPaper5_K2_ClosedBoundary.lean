-- Prove2me | Definitions.Def_APFPaper5_K2_ClosedBoundary
-- name    : APFPaper5_K2_ClosedBoundary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:21:22.24021+00:00
-- url     : https://prove2.me/theorems/e194b16c-4c80-4ea3-a0a4-c4314488e3c7
-- title:
--   Closed-word equivalence and score-null combinations
-- statement:
--   Readout equivalence compares admission and values in every ambient prefix and suffix. ClosedClass, NeverDefined, ToldApart, ZeroConvention and ScoreNull use supplied word/readout data. They do not supply physical readouts or finite-dimensionality.
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
--   Definitions.Def_APFPaper5_K2_ClosedBoundary; Pullbacks v39, SHA-256 89b97b3d2fdd75d080ea324a55309888be02e1275cb8b95076ae99cfe48fc247. Definitions.Def_APFPaper5_K2_ClosedBoundary; pullbacks v39; SHA-256 89b97b3d2fdd75d080ea324a55309888be02e1275cb8b95076ae99cfe48fc247

/-
APF Foundation Ledger — definition node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K2_ClosedBoundary
title: K2's objects on the foundation's words: readout equivalence, the classes of closed words at a boundary, a word admitted nowhere, told apart by a completed word, and a combination no score can see
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 5 Supplement v7.33:746-760 (strong closed-boundary readout equivalence: domain agreement and
 the same readout under every preparation prefix and terminal-test suffix), 761-768 (quotient first, then the
 real linearization; "the algebraic zero is bookkeeping"), 790-811 (the family of scores, the score-null
 space, context saturation), 3042-3048 (K2). Paper 1 Supplement v9.28:3239-3250. The builder seat's
 Def_APFPaper1_ContinuationWords (words, Cont) and Def_APFPaper1_ContextualEquivalence (ContextEq), and the
 author's ruling of 2026-11-12 that the relation is taken over all ambient words.
standing: DEFINITIONS on the foundation's own data. A process is a word of fragments, as in the encoding of
 B06 (a protocol is a full process). Nothing is assumed about the data. Three things are SUPPLIED and not
 fixed here: when a word is defined at a raw input (the canonical choice is Cont: it runs and its whole bill
 is within the capacity of the context it starts in); the value read off a completed word; and a real score
 of a completed word. Which value and which score are the physical ones is NOT RULED.
definitions:
 - ReadoutEq: two words of the same type are readout-equivalent when, inside every prefix and suffix and at
   every raw input, one is defined exactly when the other is, and their values agree where defined.
 - ClosedClass: the closed words at a boundary (words from a context back to it), up to that relation.
 - NeverDefined: a word that is defined inside no prefix and suffix at no raw input.
 - ToldApart: some prefix, suffix and raw input at which one of two words is defined and the other is not,
   or both are defined with different values.
 - ZeroConvention: the score of a word at an input where it is not defined is 0.
 - admissionScore: 1 where a word is defined, 0 where it is not.
 - ScoreNull: a finite real combination of words whose score adds to 0 inside every prefix and suffix at
   every raw input.
not claimed: that the classes are finitely many; any adjoint; that any score is the physical score.
no structure, no class, no Prop-valued field.
-/
import Definitions.Def_APFPaper1_ContextualEquivalence
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

set_option autoImplicit false
open APFPaper1.Continuation

namespace APFPaper5.K2

universe uC uF uX uV uI
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {Val : Type uV}

/-- Readout equivalence: contextual equivalence with every word allowed as prefix and as suffix. -/
abbrev ReadoutEq (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    {a b : Context} (W W' : Word Frag a b) : Prop :=
  ContextEq Defd value (fun _ _ _ => True) W W'

/-- The closed words at the boundary `a`, up to readout equivalence. -/
def ClosedClass (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val) (a : Context) : Type (max uC uF) :=
  Quot (fun W W' : Word Frag a a => ReadoutEq Defd value W W')

/-- A word that is defined inside no prefix and suffix, at no raw input. -/
def NeverDefined (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    {a b : Context} (W : Word Frag a b) : Prop :=
  ∀ (g c : Context) (P : Word Frag g a) (S : Word Frag b c) (x : Raw g),
    ¬ Defd g x (sandwich P W S)

/-- Two words are told apart by a completed word: a prefix, a suffix and a raw input at which one is defined
and the other is not, or both are defined and their values differ. -/
def ToldApart (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    {a b : Context} (W W' : Word Frag a b) : Prop :=
  ∃ (g c : Context) (P : Word Frag g a) (S : Word Frag b c) (x : Raw g),
    (Defd g x (sandwich P W S) ∧ ¬ Defd g x (sandwich P W' S)) ∨
    (¬ Defd g x (sandwich P W S) ∧ Defd g x (sandwich P W' S)) ∨
    (Defd g x (sandwich P W S) ∧ Defd g x (sandwich P W' S) ∧
      value g (sandwich P W S) x ≠ value g (sandwich P W' S) x)

/-- The zero convention: where a word is not defined its score is 0. -/
def ZeroConvention (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (score : (g : Context) → WordFrom Frag g → Raw g → ℝ) : Prop :=
  ∀ (g : Context) (x : Raw g) (w : WordFrom Frag g), ¬ Defd g x w → score g w x = 0

/-- The admission score: 1 where the word is defined, 0 where it is not. -/
noncomputable def admissionScore (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (g : Context) (w : WordFrom Frag g) (x : Raw g) : ℝ :=
  @ite ℝ (Defd g x w) (Classical.propDecidable _) 1 0

/-- A finite real combination of words that no score can see: inside every prefix and suffix, at every raw
input, the scores add to 0. -/
def ScoreNull {ι : Type uI} [Fintype ι]
    (score : (g : Context) → WordFrom Frag g → Raw g → ℝ)
    {a b : Context} (coef : ι → ℝ) (w : ι → Word Frag a b) : Prop :=
  ∀ (g c : Context) (P : Word Frag g a) (S : Word Frag b c) (x : Raw g),
    ∑ i, coef i * score g (sandwich P (w i) S) x = 0

end APFPaper5.K2


