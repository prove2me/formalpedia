-- Prove2me | Definitions.Def_PricingWithTips3DM_ca80a4821d90bc35010bdc9e
-- name    : PricingWithTips3DM_ca80a4821d90bc35010bdc9e
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:11:05.273662+00:00
-- url     : https://prove2.me/theorems/36bc8e2d-a443-4dce-9853-f9798ba41256
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxTrueArmTerminalPrefixFrames
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_2b2043d97c6219d5e9e3ac58
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Concrete raw-input source for terminal true-arm prefixes

The existing generic affine-map source evaluates the verifier-fixed terminal
prefix table over every runtime transition-row seed.  The resulting fixed TM2
emits exactly the halted, label, and state operands of all terminal true arms.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Raw-input unary values for every terminal true-arm prefix. -/
noncomputable def verifierTransitionDispatchTerminalPrefixValueFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineMapFrames W
    (transitionDispatchTerminalPrefixForms W.machine.tm) input

/-- Exact semantic contract of the generated terminal-prefix values. -/
theorem verifierTransitionDispatchTerminalPrefixValueFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchTerminalPrefixValueFrames W input =
      encodeUnaryFrame
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchTerminalPrefixValues W.machine.tm)) := by
  unfold verifierTransitionDispatchTerminalPrefixValueFrames
    verifierTransitionAffineMapFrames verifierTransitionTailAffineSeeds
    affineUnaryTripleMapFamily encodeUnaryFrame
  congr 1
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  exact transitionDispatchTerminalPrefixForms_value W.machine.tm seed

/-- One fixed polynomial-time TM2 emits every terminal-prefix operand directly
from the raw verifier word. -/
noncomputable def
    verifierTransitionDispatchTerminalPrefixValueFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchTerminalPrefixValueFrames W) := by
  exact verifierTransitionAffineMapFrames_computableInPolyTime W
    (transitionDispatchTerminalPrefixForms W.machine.tm)

end CLRS.Chapter34.Turing.CookLevin


