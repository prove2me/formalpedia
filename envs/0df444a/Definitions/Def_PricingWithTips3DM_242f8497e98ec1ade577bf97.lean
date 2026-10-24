-- Prove2me | Definitions.Def_PricingWithTips3DM_242f8497e98ec1ade577bf97
-- name    : PricingWithTips3DM_242f8497e98ec1ade577bf97
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:56:06.111891+00:00
-- url     : https://prove2.me/theorems/440af8dc-b187-4439-a894-7ed7fa835028
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionWidenedFallbackMarkedDescriptors
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_a39abcc00b238b2d99ed7809
import Definitions.Def_PricingWithTips3DM_7019935caab4d9733d34fc99
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Marked widened-fallback descriptors from the raw verifier word

This is the concrete source boundary needed by descriptor-local stack-route
passes: the already verified raw-input affine source is followed by the fixed
seven-field row marker.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Every runtime widened-fallback progression descriptor, now with an outer
row marker suitable for descriptor-local streaming rewrites. -/
noncomputable def verifierTransitionWidenedFallbackMarkedDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  markAffineUnaryTripleProgressionRows
    (verifierTransitionWidenedFallbackDescriptorFrames W input)

/-- Exact marked descriptor semantics over every transition-row seed. -/
theorem verifierTransitionWidenedFallbackMarkedDescriptorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionWidenedFallbackMarkedDescriptorFrames W input =
      encodeAffineUnaryTripleProgressionMarkedFamily
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionWidenedFallbackProgressions W.machine.tm)) := by
  unfold verifierTransitionWidenedFallbackMarkedDescriptorFrames
  rw [verifierTransitionWidenedFallbackDescriptorFrames_eq]
  exact markAffineUnaryTripleProgressionRows_encode _

/-- One fixed polynomial-time TM2 emits the marked descriptor family directly
from the original verifier input. -/
noncomputable def
    verifierTransitionWidenedFallbackMarkedDescriptorFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionWidenedFallbackMarkedDescriptorFrames W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionWidenedFallbackDescriptorFrames_computableInPolyTime W)
      markAffineUnaryTripleProgressionRows_computableInPolyTime
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionWidenedFallbackMarkedDescriptorFrames] using run }

end CLRS.Chapter34.Turing.CookLevin


