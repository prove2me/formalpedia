-- Prove2me | solution 1 for APFB02.per_distinction_nonvacuity_r2
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T18:35:40.467234+00:00
-- url     : https://prove2.me/submissions/be4be843-c45e-4ad1-9926-24e8e647bd78

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-14; not gated, not reviewed)
name: APFB02_per_distinction_nonvacuity_r2
title: Under B02 as revised every distinction separates two inputs with different continuation profiles and has a realizing protocol
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:1059, 2158-2161, and FOUNDATION_INPUTS.json revision 2026-11-14.1, B02. The
 statement is that of the live theorem APFB02.per_distinction_nonvacuity (node
 d2a73d60-6aa6-40c9-bc2d-bc36c5ba0f6e) with its hypothesis replaced by the whole-module form of B02 as revised
 (Def_APF_B02_DeclaredInput_r2_whole_proposed). It imports that module only, not the live B02 module.
standing: a PROPOSAL, wanted only if B02 is re-registered as one module that replaces the live B02 node (the
 pattern of B03 and B05). In that case the live consumer of B02 must import the new module, and this is it.
 If the live B02 node is kept and extended instead, this file is not needed:
 APFB02.per_distinction_nonvacuity_at_r2 (Thm_APFB02_r2_carries_first_sentence) says the same.
consumes_inputs: B02 in its proposed revised form, as a hypothesis. No other input.
statement: (APFB02.per_distinction_nonvacuity_r2) let B02 hold as revised. Then at every context and for every
 distinction of that context there are raw inputs on which it takes different values and whose continuation
 profiles differ, and there is a protocol with a maintained record set sufficient for it that it uses to
 realize it.
not_claimed: anything from B02's second sentence, which this proof does not use; anything about cost, capacity,
 or which inputs are physically prepared.
-/
import Definitions.Def_APF_B02_DeclaredInput_r2_whole_proposed

set_option autoImplicit false

universe uG uX uQ uP uR

namespace APFB02

theorem per_distinction_nonvacuity_r2
    {Context : Type uG} {X : Context → Type uX} {Q : Context → Type uQ}
    {P : Context → Type uP} {Record : Context → Type uR}
    (Cont : (g : Context) → X g → Q g → Prop)
    (Delta : (g : Context) → (X g → Bool) → Prop)
    (maintained : (g : Context) → P g → Record g → Prop)
    (sufficient : (g : Context) → P g → (Record g → Prop) →
      {d : X g → Bool // Delta g d} → Prop)
    (usesToRealize : (g : Context) → P g →
      {d : X g → Bool // Delta g d} → (Record g → Prop) → Prop)
    (hB02 : B02SourceMeaning_r2_whole Cont Delta maintained sufficient usesToRealize)
    (g : Context) (d : {f : X g → Bool // Delta g f}) :
    ∃ x y : X g, d.val x ≠ d.val y ∧ Cont g x ≠ Cont g y ∧
      ∃ (p : P g) (sigma : Record g → Prop),
        (∀ r, sigma r → maintained g p r) ∧
        sufficient g p sigma d ∧ usesToRealize g p d sigma := by
  obtain ⟨hdesc, ⟨x, y, hxy⟩, hreal⟩ := hB02.1 g d
  exact ⟨x, y, hxy, fun hC => hxy (hdesc x y hC), hreal⟩

end APFB02


universe apfNative_uG apfNative_uX apfNative_uQ apfNative_uP apfNative_uR
theorem solution :
∀ {Context : Type apfNative_uG} {X : Context → Type apfNative_uX} {Q : Context → Type apfNative_uQ}
  {P : Context → Type apfNative_uP} {Record : Context → Type apfNative_uR} (Cont : (g : Context) → X g → Q g → Prop)
  (Delta : (g : Context) → (X g → Bool) → Prop) (maintained : (g : Context) → P g → Record g → Prop)
  (sufficient :
    (g : Context) →
      P g → (Record g → Prop) → (@Subtype.{apfNative_uX + 1} (X g → Bool) fun (d : X g → Bool) => Delta g d) → Prop)
  (usesToRealize :
    (g : Context) →
      P g → (@Subtype.{apfNative_uX + 1} (X g → Bool) fun (d : X g → Bool) => Delta g d) → (Record g → Prop) → Prop)
  (hB02 :
    @APFB02.B02SourceMeaning_r2_whole.{apfNative_uG, apfNative_uX, apfNative_uQ, apfNative_uP, apfNative_uR} Context X Q
      P Record Cont Delta maintained sufficient usesToRealize)
  (g : Context) (d : @Subtype.{apfNative_uX + 1} (X g → Bool) fun (f : X g → Bool) => Delta g f),
  @Exists.{apfNative_uX + 1} (X g) fun (x : X g) =>
    @Exists.{apfNative_uX + 1} (X g) fun (y : X g) =>
      And
        (@Ne.{1} Bool (@Subtype.val.{apfNative_uX + 1} (X g → Bool) (fun (f : X g → Bool) => Delta g f) d x)
          (@Subtype.val.{apfNative_uX + 1} (X g → Bool) (fun (f : X g → Bool) => Delta g f) d y))
        (And (@Ne.{apfNative_uQ + 1} (Q g → Prop) (Cont g x) (Cont g y))
          (@Exists.{apfNative_uP + 1} (P g) fun (p : P g) =>
            @Exists.{apfNative_uR + 1} (Record g → Prop) fun (sigma : Record g → Prop) =>
              And (∀ (r : Record g), sigma r → maintained g p r)
                (And (sufficient g p sigma d) (usesToRealize g p d sigma)))) := by
  exact @APFB02.per_distinction_nonvacuity_r2
