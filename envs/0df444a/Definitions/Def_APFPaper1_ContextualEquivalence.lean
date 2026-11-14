-- Prove2me | Definitions.Def_APFPaper1_ContextualEquivalence
-- name    : APFPaper1_ContextualEquivalence
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:44:49.553594+00:00
-- url     : https://prove2.me/theorems/76aaaed6-c712-4e79-b3fb-395e0aedf1bc
-- title:
--   Generic typed ContextEq with exact domain/value agreement
-- statement:
--   Generic typed ContextEq with exact domain/value agreement; all-word ambient specialization is the ledger relation chosen by author. Premises: Supplied Defd, value and Amb; AmbientHeredity and SubwordHeredity are defined predicates, not axioms. Scope: Generic relation accurately represents the admissible-ambient source shape. Raw inputs and arbitrary values do not by themselves bind to quotient profiles. Author-selected all-word relation is obtained by Amb := True.
--
--   **Representation and scope.** Generic relation accurately represents the admissible-ambient source shape. Raw inputs and arbitrary values do not by themselves bind to quotient profiles. Author-selected all-word relation is obtained by Amb := True.
--
--   **Supplied data or hypotheses.** Supplied Defd, value and Amb; AmbientHeredity and SubwordHeredity are defined predicates, not axioms.
-- source:
--   Definitions/Def_APFPaper1_ContextualEquivalence.lean; Sib v15, SHA-256 e62bd518a673c4e8d6d0d2f7d3c24b06a09987fae7fa4cc0668d404e1f573dd7. ['34-36: sandwich', '41-48: ContextEq', '52-62: heredity predicates', 'Paper1 v9.28:3239-3250', 'RULING_ContextEq_all_ambients']

/-
APF Foundation Ledger — definition node. DRAFT for author and cold review. Not gated, not released, not uploaded.
name: APFPaper1_ContextualEquivalence
title: Contextual continuation equivalence of words
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:3239-3250 (contextual continuation equivalence: domain agreement and profile
  agreement under every admissible prefix and suffix), 3221-3230 (partial word product), 3284-3298 (strong
  congruence lemma), 3301 (hypothesis W-her). Word order: the Supplement writes products right to left; here words
  are in execution order, so the Supplement's S W P is `P` then `W` then `S`.
statement: Fix a definedness predicate on (context, raw input, word), a value assigned to a word run from a raw
  input, and a class of ambient words. Two words W, W' of the same type are contextually equivalent when, for every
  ambient prefix P, ambient suffix S and raw input x: (i) P then W then S is defined at x exactly when P then W'
  then S is; (ii) when both are defined their values at x are equal.
canonical instantiation (not fixed by this module): definedness := membership in Cont of
  APFPaper1_ContinuationWords; ambient words := the Supplement's admissible words.
supplied data, nothing assumed about it: the value function (the Supplement's "physical continuation profile,
  the same tested operational values, exactly"); the ambient class.
fidelity exposure: (a) the Supplement quantifies over compatible input possibilities, i.e. classes; this module
  quantifies over raw inputs. (b) The value of a run is supplied data, not constructed from readouts. (c) Which
  words count as admissible ambients under the corrected Cont is not settled here; it is the parameter Amb.
no structure, no class, no Prop-valued field.
-/
import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
namespace APFPaper1.Continuation

universe uC uF uX uV
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {Val : Type uV}

/-- The composite word "`P`, then `W`, then `S`", as a process of the context `P` starts in. -/
def sandwich {g a b c : Context} (P : Word Frag g a) (W : Word Frag a b) (S : Word Frag b c) :
    WordFrom Frag g :=
  ⟨c, P.append (W.append S)⟩

/-- Contextual continuation equivalence of two words of the same type, relative to a definedness predicate, a
value function and a class of ambient words. Clause (i) is domain agreement; clause (ii) is exact profile
agreement where defined. -/
def ContextEq (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    (Amb : (g h : Context) → Word Frag g h → Prop)
    {a b : Context} (W W' : Word Frag a b) : Prop :=
  ∀ (g c : Context) (P : Word Frag g a) (S : Word Frag b c) (x : Raw g), Amb g a P → Amb b c S →
    (Defd g x (sandwich P W S) ↔ Defd g x (sandwich P W' S)) ∧
    (Defd g x (sandwich P W S) → Defd g x (sandwich P W' S) →
      value g (sandwich P W S) x = value g (sandwich P W' S) x)

/-- Ambient heredity: whenever a composite is defined at some input, its outer parts are ambient words.
A property the data may or may not have. -/
def AmbientHeredity (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (Amb : (g h : Context) → Word Frag g h → Prop) : Prop :=
  ∀ (g a b c : Context) (A : Word Frag g a) (M : Word Frag a b) (B : Word Frag b c) (x : Raw g),
    Defd g x (sandwich A M B) → Amb g a A ∧ Amb b c B

/-- Contiguous-subword heredity (the Supplement's W-her, 3301), in this vocabulary: every contiguous subword of a
word that is defined at some input is admissible. Hypothesized in the Supplement, not derived. -/
def SubwordHeredity (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (Adm : (g h : Context) → Word Frag g h → Prop) : Prop :=
  ∀ (g a b c : Context) (A : Word Frag g a) (M : Word Frag a b) (B : Word Frag b c) (x : Raw g),
    Defd g x (sandwich A M B) → Adm a b M

end APFPaper1.Continuation


