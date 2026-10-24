-- Prove2me | Definitions.Def_PricingWithTips3DM_307b3e3bb027799e65a0a713
-- name    : PricingWithTips3DM_307b3e3bb027799e65a0a713
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T05:01:39.349117+00:00
-- url     : https://prove2.me/theorems/2ab80452-307d-4ea5-8d42-4f347a9a0bad
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorBodyTransitionPrefixCompiler
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2
import Definitions.Def_PricingWithTips3DM_5ef5be0c9754064ac0f08ba4
import Definitions.Def_PricingWithTips3DM_693ce23dec6dc45ed34c4fb1
import Definitions.Def_PricingWithTips3DM_30bb247006e7aff5fdce0462
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Concrete verifier-body input through the transition phase

The independently verified validity and transition input compilers are joined
on their common raw verifier word.  This closes the complete runtime operand
prefix consumed before the post-transition verifier tail.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Exact unary verifier-body operands through all local transitions. -/
def verifierBodyTransitionPrefixUnaryTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierValidityRowFamilyInputTarget W input ++
    verifierTransitionFamilyUnaryInputTarget W input

/-- The joined source is the literal prefix of the canonical body script. -/
theorem verifierBodyTransitionPrefixUnaryTarget_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierBodyTransitionPrefixUnaryTarget W input =
      encodeAffineValidityRowFamilyInput
          (verifierValidityRowFramesByLength W input.length) ++
        encodeAffineTransitionFamilyUnary
          (verifierTransitionFamilyScripts W input) := by
  unfold verifierBodyTransitionPrefixUnaryTarget
  rw [verifierValidityRowFamilyInputTarget_eq_canonical]
  rfl

/-- A single fixed polynomial-time TM2 emits the validity-plus-transition
operand prefix directly from the raw verifier input. -/
noncomputable def
    verifierBodyTransitionPrefixUnaryTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierBodyTransitionPrefixUnaryTarget W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact unaryFrameSameInputConcat_computableInPolyTime
    (verifierValidityRowFamilyInputTarget_computableInPolyTime W)
    (verifierTransitionFamilyUnaryInputTarget_computableInPolyTime W)

end CLRS.Chapter34.Turing.CookLevin


