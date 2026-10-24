-- Prove2me | Definitions.Def_PricingWithTips3DM_f820102d1b4254c4f74e0384
-- name    : PricingWithTips3DM_f820102d1b4254c4f74e0384
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T21:09:21.961989+00:00
-- url     : https://prove2.me/theorems/9e53c88c-1b00-4e1f-a44b-918e1d05e243
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Emitter.Guarded
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_9309684e16b91559eab59525
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! # General-circuit formula emitter: guarded semantic interface -/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

/-- Semantic encoder for the only two record shapes produced by the verified
normalizer. -/
def encodeGuardedCircuit : Option Circuit → List NormalizedCircuitSym
  | none => [.invalidMark]
  | some c => encodeNormalizedCircuit c

/-- Invalid records become false; valid records become the exact consistency
formula stream for their circuit. -/
def guardedCircuitFormulaList : Option Circuit → List FormulaSym
  | none => enc (.const false)
  | some c => generalCircuitFormulaList c

def guardedReverseSteps : Option Circuit → Nat
  | none => invalidReverseSteps
  | some c => reverseSuccessfulSteps c

/-- One total exact-run theorem for the guarded semantic input type. -/
theorem guarded_reverse_run (guarded : Option Circuit) :
    (flip Option.bind step)^[guardedReverseSteps guarded]
      (some (_root_.Turing.initList reverseMachine
        (encodeGuardedCircuit guarded))) =
    some (_root_.Turing.haltList reverseMachine
      (guardedCircuitFormulaList guarded).reverse) := by
  cases guarded with
  | none => simpa [guardedReverseSteps, encodeGuardedCircuit,
      guardedCircuitFormulaList] using invalid_reverse_run
  | some c => simpa [guardedReverseSteps, encodeGuardedCircuit,
      guardedCircuitFormulaList] using canonical_reverse_run c

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter


