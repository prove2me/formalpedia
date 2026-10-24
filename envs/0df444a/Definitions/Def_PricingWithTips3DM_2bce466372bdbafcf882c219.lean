-- Prove2me | Definitions.Def_PricingWithTips3DM_2bce466372bdbafcf882c219
-- name    : PricingWithTips3DM_2bce466372bdbafcf882c219
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:52:17.171337+00:00
-- url     : https://prove2.me/theorems/7490db60-9894-4c61-9b2f-a1e825f557c1
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Normalizer.Config
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_6dba0df426c2c529c032ecee
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Guarded circuit normalizer: named configurations
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

/-- Concrete stack family used by all phase specifications. -/
abbrev stackContents (input : List CircuitSym)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    ∀ stack : Stack, List (Alphabet stack)
  | .input => input
  | .output => output
  | .rows => rows
  | .inputCount => List.replicate inputCount ()
  | .gateCount => List.replicate gateCount ()
  | .operand => List.replicate operand ()
  | .saved => List.replicate saved ()
  | .outputIndex => List.replicate outputIndex ()

/-- Named constructor for configurations in exact run lemmas. -/
def cfg (label : Option Label) (state : State)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) : machine.Cfg :=
  ⟨label, state, stackContents input output rows inputCount gateCount operand saved outputIndex⟩

/-- Short name for the normalizer transition function. -/
def step : machine.Cfg → Option machine.Cfg := machine.step

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer


