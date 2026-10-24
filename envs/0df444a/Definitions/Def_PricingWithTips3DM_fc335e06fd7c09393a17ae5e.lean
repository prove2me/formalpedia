-- Prove2me | Definitions.Def_PricingWithTips3DM_fc335e06fd7c09393a17ae5e
-- name    : PricingWithTips3DM_fc335e06fd7c09393a17ae5e
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:51:32.30238+00:00
-- url     : https://prove2.me/theorems/9d08ec7d-024c-49f7-887e-545e58ab2872
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Emitter.Encoding
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_3d6db667d76a0b7270310da7
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# General-circuit formula emitter: exact list encoding

These definitions expose the prefix-polish output stream directly, one gate
row at a time.  The later TM2 proof targets these lists rather than unfolding
the recursive `Formula` encoder inside machine configurations.
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

/-- Prefix stream for the expression on the right-hand side of one circuit
gate equation. -/
def generalCircuitGateExprList (inputCount : Nat) : CircuitGate →
    List FormulaSym
  | .input inputIndex => varEnc inputIndex
  | .const value => [.lit value]
  | .not source => .notMark :: varEnc (inputCount + source)
  | .and left right =>
      .andMark :: (varEnc (inputCount + left) ++
        varEnc (inputCount + right))
  | .or left right =>
      .orMark :: (varEnc (inputCount + left) ++
        varEnc (inputCount + right))

/-- Prefix stream for one indexed gate-consistency equation. -/
def generalCircuitGateFormulaList (inputCount gateIndex : Nat)
    (gate : CircuitGate) : List FormulaSym :=
  .iffMark :: (varEnc (inputCount + gateIndex) ++
    generalCircuitGateExprList inputCount gate)

/-- Gate-row prefix stream before the terminal true constant. -/
def generalCircuitGateRowsListFrom (inputCount : Nat) :
    Nat → List CircuitGate → List FormulaSym
  | _, [] => []
  | gateIndex, gate :: gates =>
      .andMark :: (generalCircuitGateFormulaList inputCount gateIndex gate ++
        generalCircuitGateRowsListFrom inputCount (gateIndex + 1) gates)

/-- Right-associated conjunction stream for a chronological gate suffix. -/
def generalCircuitGateFamilyListFrom (inputCount : Nat) :
    Nat → List CircuitGate → List FormulaSym
  | _, [] => [.lit true]
  | gateIndex, gate :: gates =>
      .andMark :: (generalCircuitGateFormulaList inputCount gateIndex gate ++
        generalCircuitGateFamilyListFrom inputCount (gateIndex + 1) gates)

/-- Exact prefix stream of the textbook general-circuit consistency formula. -/
def generalCircuitFormulaList (c : Circuit) : List FormulaSym :=
  .andMark :: (varEnc (c.inputCount + c.output) ++
    generalCircuitGateFamilyListFrom c.inputCount 0 c.gates)

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter


