-- Prove2me | Definitions.Def_PricingWithTips3DM_0ff3662639483ad7a2afd58b
-- name    : PricingWithTips3DM_0ff3662639483ad7a2afd58b
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T21:06:42.648442+00:00
-- url     : https://prove2.me/theorems/8ede58cc-2d98-40f3-8392-b3750bacb6bc
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Emitter.GateFamily
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_41498b17e792ce83b61d55c2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! # General-circuit formula emitter: chronological gate families -/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

open StateTransition

private abbrev transition := flip Option.bind step

def gateRowsStepsFrom (inputCount : Nat) : Nat → List CircuitGate → Nat
  | _, [] => 0
  | gateIndex, gate :: gates =>
      gateRowSteps inputCount gateIndex gate +
        gateRowsStepsFrom inputCount (gateIndex + 1) gates

/-- Emit all canonical gate rows, stopping before the terminal true constant. -/
theorem gateRows_phase (state : State) (inputCount gateIndex : Nat)
    (gates : List CircuitGate) (input : List NormalizedCircuitSym)
    (output : List FormulaSym) :
    ∃ finalState,
      transition^[gateRowsStepsFrom inputCount gateIndex gates]
        (some (cfg (some .rows) state
          (encodeNormalizedGateRowsFrom gateIndex gates ++ input)
          output inputCount 0)) =
      some (cfg (some .rows) finalState input
        ((generalCircuitGateRowsListFrom inputCount gateIndex gates).reverse ++
          output) inputCount 0) := by
  induction gates generalizing state gateIndex output with
  | nil =>
      exact ⟨state, by simp [gateRowsStepsFrom, encodeNormalizedGateRowsFrom,
        generalCircuitGateRowsListFrom]⟩
  | cons gate gates ih =>
      rcases gateRow_phase state inputCount gateIndex gate
          (encodeNormalizedGateRowsFrom (gateIndex + 1) gates ++ input)
          output with ⟨afterGate, hgate⟩
      rcases ih afterGate (gateIndex + 1)
          ((.andMark :: generalCircuitGateFormulaList inputCount gateIndex gate).reverse ++
            output) with ⟨finalState, htail⟩
      refine ⟨finalState, ?_⟩
      have hfull := step_comp _ _ (by
        simpa [List.append_assoc] using hgate) htail
      simpa [gateRowsStepsFrom, encodeNormalizedGateRowsFrom,
        generalCircuitGateRowsListFrom, List.reverse_append,
        List.append_assoc] using hfull

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter


