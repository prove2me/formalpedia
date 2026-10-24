-- Prove2me | Definitions.Def_PricingWithTips3DM_c5fd22a06718898ef0cc9e70
-- name    : PricingWithTips3DM_c5fd22a06718898ef0cc9e70
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T21:37:40.310546+00:00
-- url     : https://prove2.me/theorems/98dab29d-2545-47a1-a5c6-7fe7592d333f
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.GuardedBridge
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_73463e9c86d4d084282cdafd
import Definitions.Def_PricingWithTips3DM_c2e7a0423b643592427a9c54
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! # General CIRCUIT-SAT to SAT: guarded machine bridge -/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT

open _root_.Turing

/-- Semantic result computed by the guarded normalizer. -/
def guardGeneralCircuit (input : List CircuitSym) : Option Circuit :=
  match decodeCircuit input with
  | some c => if c.WellFormed then some c else none
  | none => none

/-- The semantic guarded encoder is exactly the normalizer's public symbol
stream on every raw input. -/
theorem encodeGuardedCircuit_guardGeneralCircuit (input : List CircuitSym) :
    Emitter.encodeGuardedCircuit (guardGeneralCircuit input) =
      normalizeGeneralCircuit input := by
  cases hdecode : decodeCircuit input with
  | none =>
      simp [guardGeneralCircuit, hdecode, Emitter.encodeGuardedCircuit,
        normalizeGeneralCircuit]
  | some c =>
      by_cases hwellFormed : c.WellFormed <;>
        simp [guardGeneralCircuit, hdecode, hwellFormed,
          Emitter.encodeGuardedCircuit, normalizeGeneralCircuit]

/-- Reinterpret the already verified normalizer as computing the guarded
semantic value, rather than an opaque internal symbol list. -/
noncomputable def normalizerGuardedComputableInPolyTime :
    TM2ComputableInPolyTime id Emitter.encodeGuardedCircuit
      guardGeneralCircuit := by
  let old := Normalizer.computableInPolyTime
  exact {
    tm := old.tm
    inputAlphabet := old.inputAlphabet
    outputAlphabet := old.outputAlphabet
    time := old.time
    outputsFun := fun input => by
      simpa [encodeGuardedCircuit_guardGeneralCircuit] using
        old.outputsFun input }

/-- The guarded formula semantics agrees exactly with the existing total
raw-string reduction, including malformed and ill-formed inputs. -/
theorem guardedCircuitFormula_guardGeneralCircuit (input : List CircuitSym) :
    Emitter.guardedCircuitFormulaList (guardGeneralCircuit input) =
      generalCircuitToSATMap input := by
  cases hdecode : decodeCircuit input with
  | none =>
      simp [guardGeneralCircuit, hdecode, Emitter.guardedCircuitFormulaList,
        generalCircuitToSATMap]
  | some c =>
      by_cases hwellFormed : c.WellFormed
      · simp [guardGeneralCircuit, hdecode, hwellFormed,
          Emitter.guardedCircuitFormulaList, generalCircuitToSATMap,
          Emitter.generalCircuitFormulaList_eq_enc]
      · simp [guardGeneralCircuit, hdecode, hwellFormed,
          Emitter.guardedCircuitFormulaList, generalCircuitToSATMap]

/-- Concrete fixed-TM2 polynomial-time computation of the total textbook
general-circuit-to-SAT map. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id generalCircuitToSATMap := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    normalizerGuardedComputableInPolyTime Emitter.computableInPolyTime
  simpa [Function.comp_def, guardedCircuitFormula_guardGeneralCircuit] using
    Classical.choice composed

end CLRS.Chapter34.Turing.GeneralCircuitToSAT


