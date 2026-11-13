-- Prove2me | solution 1 for APFB02.per_distinction_nonvacuity
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-12T15:27:39.324917+00:00
-- url     : https://prove2.me/submissions/ecdf0aab-1e0b-4ec7-aaf4-39ec4470634a

/-
APF Foundation Ledger — theorem node (Batch 3). First theorem consuming the declared input B02.
name: APFB02.per_distinction_nonvacuity
title: Under B02 every distinction separates two inputs with different continuation profiles and has a realizing protocol
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:1059 (a physical distinction is a finite enforceable separator of continuation
  profiles), 2158-2161 (a distinction separating two classes forces their continuation profiles to differ), and
  FOUNDATION_INPUTS.json revision 2026-10-04.1, B02. Restates the archive theorem
  APFOriginalProcess.per_distinction_nonvacuity over the live B02 node.
statement: Let B02 hold (B02SourceMeaning). Then at every context g and for every distinction d of that context
  there are raw inputs x and y on which d takes different values and whose continuation profiles differ, and there
  is a protocol with a maintained record set sufficient for d that it uses to realize d.
  The second conjunct is the contrapositive of the descent clause of B02; the first and third are clauses of B02
  restated. The continuation profile Cont is an arbitrary parameter. Inputs consumed: B02 only. Nothing is asserted
  about cost, capacity, or which inputs are physically prepared.
-/
import Definitions.Def_APF_B02_DeclaredInput

set_option autoImplicit false

universe uG uX uQ uP uR

namespace APFB02


end APFB02

open APFB02 in
theorem solution
    {Context : Type uG} {X : Context → Type uX} {Q : Context → Type uQ}
    {P : Context → Type uP} {Record : Context → Type uR}
    (Cont : (g : Context) → X g → Q g → Prop)
    (Delta : (g : Context) → (X g → Bool) → Prop)
    (maintained : (g : Context) → P g → Record g → Prop)
    (sufficient : (g : Context) → P g → (Record g → Prop) →
      {d : X g → Bool // Delta g d} → Prop)
    (usesToRealize : (g : Context) → P g →
      {d : X g → Bool // Delta g d} → (Record g → Prop) → Prop)
    (hB02 : B02SourceMeaning Cont Delta maintained sufficient usesToRealize)
    (g : Context) (d : {f : X g → Bool // Delta g f}) :
    ∃ x y : X g, d.val x ≠ d.val y ∧ Cont g x ≠ Cont g y ∧
      ∃ (p : P g) (sigma : Record g → Prop),
        (∀ r, sigma r → maintained g p r) ∧
        sufficient g p sigma d ∧ usesToRealize g p d sigma := by
  obtain ⟨hdesc, ⟨x, y, hxy⟩, hreal⟩ := hB02 g d
  exact ⟨x, y, hxy, fun hC => hxy (hdesc x y hC), hreal⟩
