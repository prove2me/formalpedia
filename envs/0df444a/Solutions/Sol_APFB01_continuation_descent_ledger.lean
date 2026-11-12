-- Prove2me | solution 1 for APFB01.continuation_descent_ledger
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-10-07T22:18:41.665383+00:00
-- url     : https://prove2.me/submissions/0c405a5b-5584-46d5-bc5e-0d5b09c9527e

import Definitions.Def_APF_B01_DeclaredInput
import Mathlib.Logic.ExistsUnique
set_option autoImplicit false
universe uX uP uY

/-- Ordinary quotient unique-factorization equivalence for the existing B01
quotient and canonical class. This theorem neither assumes nor establishes
the physical input predicate APF_B01_DeclaredInput or any physical fact descent.
The supplied profile and codomain remain arbitrary mathematical parameters. -/
theorem solution
    {X : Type uX} {Q : Type uP} {Y : Type uY}
    (profile : X → Q → Prop) (f : X → Y) :
    (∃! g : APFB01.PhysicalState profile → Y,
      ∀ x, g (APFB01.physicalClass profile x) = f x) ↔
    (∀ x y, profile x = profile y → f x = f y) := by
  constructor
  · rintro ⟨g, hg, _⟩ x y hxy
    have hq : APFB01.physicalClass profile x = APFB01.physicalClass profile y :=
      Quot.sound hxy
    rw [← hg x, ← hg y, hq]
  · intro hf
    refine ⟨Quot.lift f (fun x y h => hf x y h), ?_, ?_⟩
    · intro x; rfl
    · intro g hg
      funext q
      exact Quot.inductionOn q hg

#print axioms solution
