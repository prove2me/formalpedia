-- Prove2me | Definitions.Def_PricingWithTips3DM_4fdae9e266d58da6e127ceff
-- name    : PricingWithTips3DM_4fdae9e266d58da6e127ceff
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:56:21.874991+00:00
-- url     : https://prove2.me/theorems/51aee412-258b-4c9d-9605-0d303d084232
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Emitter.Config
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_a1e492e117ae1c512cdc4f29
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! # General-circuit formula emitter: named configurations -/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

abbrev stackContents (input : List NormalizedCircuitSym)
    (output : List FormulaSym) (inputCount saved : Nat) :
    ∀ stack : Stack, List (Alphabet stack)
  | .input => input
  | .output => output
  | .inputCount => List.replicate inputCount ()
  | .saved => List.replicate saved ()

def cfg (label : Option Label) (state : State)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount saved : Nat) : reverseMachine.Cfg :=
  ⟨label, state, stackContents input output inputCount saved⟩

def step : reverseMachine.Cfg → Option reverseMachine.Cfg := reverseMachine.step

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter


