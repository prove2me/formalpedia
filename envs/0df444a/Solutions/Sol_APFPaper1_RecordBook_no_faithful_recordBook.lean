-- Prove2me | solution 1 for APFPaper1.RecordBook.no_faithful_recordBook
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:18:24.988266+00:00
-- url     : https://prove2.me/submissions/5a6f89c4-8ca4-4396-a8b9-cd8aa8e89128

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper1_RecordBook_collapse
title: A commuting record book with sharp letters cannot tell XZX from ZXZ
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:6276-6280 (Example two-query-table, record level).
consumes_inputs: none. No declared input is used; the statement is algebra on the word vocabulary.
statement: (idem_comm_collapse) in a commutative semigroup, idempotent p and q satisfy p*q*p = q*p*q.
 (recordBook_collapse) a multiplicative map from the words at one context into a commutative semigroup that
 is sharp at x and at z gives the words xzx and zxz the same value. (no_faithful_recordBook) so if a
 relation E separates xzx from zxz, no such map is faithful for E. (no_faithful_recordBook_contextEq) the
 same with E the ledger's contextual equivalence.
not_claimed: nothing about any particular interface separating xzx from zxz; nothing about process models.
 The Supplement's own verdict on its example is classical invasive disturbance (6354).
-/
import Definitions.Def_APFPaper1_RecordBook
import Definitions.Def_APFPaper1_ContextualEquivalence
import Mathlib.Algebra.Group.Basic

set_option autoImplicit false
namespace APFPaper1.RecordBook

open APFPaper1.Continuation

universe uC uF uM uX uV
variable {Context : Type uC} {Frag : Context → Context → Type uF}

/-- Two commuting idempotents: `p q p` and `q p q` are both `p q`. -/
theorem idem_comm_collapse {M : Type uM} [CommSemigroup M] (p q : M)
    (hp : p * p = p) (hq : q * q = q) : p * q * p = q * p * q := by
  have h1 : p * q * p = p * q := by rw [mul_right_comm, hp]
  have h2 : q * p * q = p * q := by rw [mul_right_comm, hq, mul_comm]
  rw [h1, h2]

theorem word3_eq_append {a : Context} (f g h : Frag a a) :
    word3 f g h = (Word.single f).append ((Word.single g).append (Word.single h)) := rfl

/-- A multiplicative map sends a three-letter word to the product of its letters' values. -/
theorem rho_word3 {M : Type uM} [Mul M] {a : Context} {rho : Word Frag a a → M}
    (hmul : Multiplicative rho) (f g h : Frag a a) :
    rho (word3 f g h) =
      rho (Word.single f) * (rho (Word.single g) * rho (Word.single h)) := by
  rw [word3_eq_append, hmul, hmul]

/-- The collapse: sharp letters in a commuting book make `xzx` and `zxz` indistinguishable. -/
theorem recordBook_collapse {M : Type uM} [CommSemigroup M] {a : Context}
    {rho : Word Frag a a → M} (hmul : Multiplicative rho) {x z : Frag a a}
    (hx : Sharp rho x) (hz : Sharp rho z) :
    rho (word3 x z x) = rho (word3 z x z) := by
  rw [rho_word3 hmul, rho_word3 hmul, ← mul_assoc, ← mul_assoc]
  exact idem_comm_collapse _ _ hx hz

/-- If `E` separates `xzx` from `zxz`, no commuting sharp record book is faithful for `E`. -/
theorem no_faithful_recordBook {M : Type uM} [CommSemigroup M] {a : Context}
    (E : Word Frag a a → Word Frag a a → Prop) {x z : Frag a a}
    (hsep : ¬ E (word3 x z x) (word3 z x z)) :
    ¬ ∃ rho : Word Frag a a → M,
        Multiplicative rho ∧ Sharp rho x ∧ Sharp rho z ∧ Faithful rho E := by
  rintro ⟨rho, hmul, hx, hz, hfaith⟩
  exact hsep ((hfaith _ _).mp (recordBook_collapse hmul hx hz))

/-- The same statement with `E` the ledger's contextual equivalence of words. -/
theorem no_faithful_recordBook_contextEq {M : Type uM} [CommSemigroup M]
    {Raw : Context → Type uX} {Val : Type uV}
    (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    (Amb : (g h : Context) → Word Frag g h → Prop)
    {a : Context} {x z : Frag a a}
    (hsep : ¬ ContextEq Defd value Amb (word3 x z x) (word3 z x z)) :
    ¬ ∃ rho : Word Frag a a → M,
        Multiplicative rho ∧ Sharp rho x ∧ Sharp rho z ∧
          Faithful rho (fun v w => ContextEq Defd value Amb v w) :=
  no_faithful_recordBook (fun v w => ContextEq Defd value Amb v w) hsep

end APFPaper1.RecordBook


universe apfNative_uC apfNative_uF apfNative_uM
theorem solution :
∀ {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF} {M : Type apfNative_uM}
  [inst : CommSemigroup.{apfNative_uM} M] {a : Context}
  (E :
    @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag a a →
      @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag a a → Prop)
  {x z : Frag a a}
  (hsep :
    Not
      (E (@APFPaper1.RecordBook.word3.{apfNative_uC, apfNative_uF} Context Frag a x z x)
        (@APFPaper1.RecordBook.word3.{apfNative_uC, apfNative_uF} Context Frag a z x z))),
  Not
    (@Exists.{max (max (apfNative_uC + 1) (apfNative_uF + 1)) (apfNative_uM + 1)}
      (@APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag a a → M)
      fun (rho : @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag a a → M) =>
      And
        (@APFPaper1.RecordBook.Multiplicative.{apfNative_uC, apfNative_uF, apfNative_uM} Context Frag M
          (@CommMagma.toMul.{apfNative_uM} M (@CommSemigroup.toCommMagma.{apfNative_uM} M inst)) a rho)
        (And
          (@APFPaper1.RecordBook.Sharp.{apfNative_uC, apfNative_uF, apfNative_uM} Context Frag M
            (@CommMagma.toMul.{apfNative_uM} M (@CommSemigroup.toCommMagma.{apfNative_uM} M inst)) a rho x)
          (And
            (@APFPaper1.RecordBook.Sharp.{apfNative_uC, apfNative_uF, apfNative_uM} Context Frag M
              (@CommMagma.toMul.{apfNative_uM} M (@CommSemigroup.toCommMagma.{apfNative_uM} M inst)) a rho z)
            (@APFPaper1.RecordBook.Faithful.{apfNative_uC, apfNative_uF, apfNative_uM} Context Frag M a rho E)))) := by
  exact @APFPaper1.RecordBook.no_faithful_recordBook
