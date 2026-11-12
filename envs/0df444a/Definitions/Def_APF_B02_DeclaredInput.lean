-- Prove2me | Definitions.Def_APF_B02_DeclaredInput
-- name    : APF_B02_DeclaredInput
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-10-06T20:54:02.146705+00:00
-- url     : https://prove2.me/theorems/2d6854de-b2dd-4db3-8be5-57bbbb64efb6
-- title:
--   Declared input — B02 — Physical distinction
-- statement:
--   A distinction is a finite, enforceable separator of continuation profiles.
-- source:
--   APF Reconstruction Spine/FOUNDATION_INPUTS.json; revision 2026-10-04.1; SHA-256 bb3b59f6011dd70c5d34c9c830ab65aad0a224b11e26d4d438c4e1ab2ad445c4; declared input B02.

import Init

/-! B02 declared-input predicate, revision 2026-10-04.1.
For EVERY original source context: X is its entire raw substrate, Q its full
finite process universe, P its ORIGINAL finite admissible enforcement protocols,
and Delta its entire physical distinction domain (not all arbitrary predicates,
not an occupied or tested subfamily). The complete resolution/perturbation/
lifetime/confidence contract remains part of this fixed source context.
maintained, sufficient and usesToRealize denote the SAME original physical
records and actual use relation from Supplement v9.27:1744-1757,2615-2617.
This factors the historical B02SourceMeaning by removing resource/calibration
fields which its body never reads. No calibration law is renamed or asserted.
The physical interpretation is mandatory source vocabulary, not a theorem
certifying arbitrary instances of these parameters. B01 is not redefined.
-/
set_option autoImplicit false
universe uG uX uQ uP uR
namespace APFB02

def B02SourceMeaning
    {Context : Type uG} {X : Context → Type uX} {Q : Context → Type uQ}
    {P : Context → Type uP} {Record : Context → Type uR}
    (Cont : (g : Context) → X g → Q g → Prop)
    (Delta : (g : Context) → (X g → Bool) → Prop)
    (maintained : (g : Context) → P g → Record g → Prop)
    (sufficient : (g : Context) → P g → (Record g → Prop) →
      {d : X g → Bool // Delta g d} → Prop)
    (usesToRealize : (g : Context) → P g →
      {d : X g → Bool // Delta g d} → (Record g → Prop) → Prop) : Prop :=
  ∀ g (d : {f : X g → Bool // Delta g f}),
    (∀ x y, Cont g x = Cont g y → d.val x = d.val y) ∧
    (∃ x y, d.val x ≠ d.val y) ∧
    ∃ (p : P g) (sigma : Record g → Prop),
      (∀ r, sigma r → maintained g p r) ∧
      sufficient g p sigma d ∧ usesToRealize g p d sigma

end APFB02


