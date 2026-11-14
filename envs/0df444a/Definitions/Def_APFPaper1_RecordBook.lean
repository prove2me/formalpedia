-- Prove2me | Definitions.Def_APFPaper1_RecordBook
-- name    : APFPaper1_RecordBook
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:07:22.851481+00:00
-- url     : https://prove2.me/theorems/b4f547f5-68c8-4e07-97b2-bcca1c2e7279
-- title:
--   Generic multiplicative word-value map, sharpness and equality-faithfulness predicates
-- statement:
--   Generic multiplicative word-value map, sharpness and equality-faithfulness predicates. Premises: Supplied multiplication, rho and relation E; no existence asserted. Scope: Deliberately stronger total-word multiplicativity and fewer defender components than Paper1 finite tested defender; not a faithful encoding of the whole defender.
--
--   **Representation and scope.** Deliberately stronger total-word multiplicativity and fewer defender components than Paper1 finite tested defender; not a faithful encoding of the whole defender.
--
--   **Supplied data or hypotheses.** Supplied multiplication, rho and relation E; no existence asserted.
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper1_RecordBook.lean; Sib v15, SHA-256 c9a4a02893646d80aff1dcb98a2b0b581278ba65ac4ff0332d9b8636d7e8f880. ['28-42: four definitions', '7-11: exposed reduction', 'Paper1 v9.28:3721-3746,6276-6280']

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper1_RecordBook
title: A commuting record book on the words at one context
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:3721-3749 (commuting-extension defender), 3778 (sharp tested event),
 6276-6280 (the two-query collapse). This module keeps only what that collapse argument uses: a value for
 every word at one context, concatenation sent to product, and sharp letters sent to idempotents. The
 Supplement's defender carries more (a Boolean record space, state weights, recovery maps, a tested word
 set); none of that is encoded here, so a statement proved for these predicates is about them alone.
statement: For words from a context to itself, Multiplicative rho says rho sends concatenation to the
 product of the target; Sharp rho f says the single-letter word f has an idempotent value; Faithful rho E
 says rho identifies exactly the pairs related by a supplied relation E.
-/
import Definitions.Def_APFPaper1_ContinuationWords
import Mathlib.Algebra.Group.Basic

set_option autoImplicit false
namespace APFPaper1.RecordBook

open APFPaper1.Continuation

universe uC uF uM
variable {Context : Type uC} {Frag : Context → Context → Type uF}

/-- The three-letter word `f g h` at one context. -/
def word3 {a : Context} (f g h : Frag a a) : Word Frag a a :=
  Word.cons f (Word.cons g (Word.single h))

/-- Concatenation of words is sent to the product of the target. -/
def Multiplicative {M : Type uM} [Mul M] {a : Context} (rho : Word Frag a a → M) : Prop :=
  ∀ v w : Word Frag a a, rho (v.append w) = rho v * rho w

/-- The single-letter word `f` has an idempotent value: repeating it changes nothing. -/
def Sharp {M : Type uM} [Mul M] {a : Context} (rho : Word Frag a a → M) (f : Frag a a) : Prop :=
  rho (Word.single f) * rho (Word.single f) = rho (Word.single f)

/-- `rho` identifies exactly the pairs of words related by `E`. -/
def Faithful {M : Type uM} {a : Context} (rho : Word Frag a a → M)
    (E : Word Frag a a → Word Frag a a → Prop) : Prop :=
  ∀ v w : Word Frag a a, rho v = rho w ↔ E v w

end APFPaper1.RecordBook


