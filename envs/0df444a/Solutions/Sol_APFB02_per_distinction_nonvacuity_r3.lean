-- Prove2me | solution 1 for APFB02.per_distinction_nonvacuity_r3
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T19:52:36.591719+00:00
-- url     : https://prove2.me/submissions/e8a42b98-cc44-4c86-bb5f-6b0bd17e4f2e

/-
APF Foundation Ledger — theorem node DRAFT, PROPOSED (session EthanBrooke-01WrrBvu, 2026-11-14; not gated, not
 reviewed, not released)
name: APFB02_per_distinction_nonvacuity_r3
title: B02 with its list complete still gives each distinction two states it separates, with different continuation profiles and a serving protocol
inputs_revision: 2026-11-14.1
proposed_for_inputs_revision: 2026-11-14.2 (NOT INSTALLED)
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: FOUNDATION_INPUTS.json revision 2026-11-14.1, B02 (wording unchanged by the proposal). Proposed form
 Def_APF_B02_DeclaredInput_r3_whole_proposed. This is the statement of the live node
 a4658ec7-96fa-4d27-b14b-3334e81dc1c3 (APFB02.per_distinction_nonvacuity_r2), restated on the proposed form so
 that the one Foundation consumer of B02 has a successor if the proposal is taken.
consumes_inputs: B02, in the proposed form, as the hypothesis hB02.
statement: under the proposed form of B02, every distinction of every context has two raw states it reads
 differently; those two states have different continuation profiles; and the distinction has a protocol
 with maintained records that suffice for it and that it uses.
not_claimed: anything the live node does not claim. The third part of the proposed form is not used.
-/
import Definitions.Def_APF_B02_DeclaredInput_r3_whole_proposed

set_option autoImplicit false

universe uG uX uQ uP uR

namespace APFB02

theorem per_distinction_nonvacuity_r3
    {Context : Type uG} {X : Context → Type uX} {Q : Context → Type uQ}
    {P : Context → Type uP} {Record : Context → Type uR}
    (Cont : (g : Context) → X g → Q g → Prop)
    (Delta : (g : Context) → (X g → Bool) → Prop)
    (maintained : (g : Context) → P g → Record g → Prop)
    (sufficient : (g : Context) → P g → (Record g → Prop) →
      {d : X g → Bool // Delta g d} → Prop)
    (usesToRealize : (g : Context) → P g →
      {d : X g → Bool // Delta g d} → (Record g → Prop) → Prop)
    (hB02 : B02SourceMeaning_r3_whole Cont Delta maintained sufficient usesToRealize)
    (g : Context) (d : {f : X g → Bool // Delta g f}) :
    ∃ x y : X g, d.val x ≠ d.val y ∧ Cont g x ≠ Cont g y ∧
      ∃ (p : P g) (sigma : Record g → Prop),
        (∀ r, sigma r → maintained g p r) ∧
        sufficient g p sigma d ∧ usesToRealize g p d sigma := by
  obtain ⟨hdesc, ⟨x, y, hxy⟩, hreal⟩ := hB02.1.1 g d
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
    @APFB02.B02SourceMeaning_r3_whole.{apfNative_uG, apfNative_uX, apfNative_uQ, apfNative_uP, apfNative_uR} Context X Q
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
  exact @APFB02.per_distinction_nonvacuity_r3
