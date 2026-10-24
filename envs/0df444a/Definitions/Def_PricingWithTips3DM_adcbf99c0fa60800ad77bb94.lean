-- Prove2me | Definitions.Def_PricingWithTips3DM_adcbf99c0fa60800ad77bb94
-- name    : PricingWithTips3DM_adcbf99c0fa60800ad77bb94
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T21:08:55.390572+00:00
-- url     : https://prove2.me/theorems/36f359e1-92a3-4841-878a-e5f82398daef
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.OccurrenceRowsRuntime
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_19cad84cc22c0a34729aa2d8
import Definitions.Def_PricingWithTips3DM_b8c03f33e84411dcd1343113
import Definitions.Def_PricingWithTips3DM_4901b5edb9039a7b71dab674
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Indexed occurrence rows: compiled runtime

The local reverse-output controller is compiled, composed with the generic
list reversal machine, and finally connected to the canonical raw-CNF
normalizer.  Thus the public theorem is about one fixed TM2 on arbitrary raw
CNF words, not merely about a semantic helper function.
-/

noncomputable section

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Concrete compiled row builder before restoring forward output order. -/
noncomputable def occurrenceRowsRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      (fun formula : CNF => relabel (encCNF formula)) id
      (fun formula => (encodeIndexedOccurrenceRows formula).reverse) where
  tm := compile occurrenceRowsRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 24 * (Polynomial.X + 1) ^ 2
  outputsFun := fun formula => by
    have builderRun := occurrenceRowsRev_run formula
    have compiledRun := compile_evalsToInTime occurrenceRowsRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile occurrenceRowsRevProgram).step
        (_root_.Turing.initList (compile occurrenceRowsRevProgram)
          (relabel (encCNF formula)))
        (some (_root_.Turing.haltList (compile occurrenceRowsRevProgram)
          (encodeIndexedOccurrenceRows formula).reverse))
        (occurrenceRowsRevSteps formula) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : occurrenceRowsRevSteps formula ≤
        (24 * (Polynomial.X + 1) ^ 2).eval
          (relabel (encCNF formula)).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
        Polynomial.eval_ofNat] using occurrenceRowsRevSteps_le_input formula
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile occurrenceRowsRevProgram).step
        (_root_.Turing.initList (compile occurrenceRowsRevProgram)
          (relabel (encCNF formula)))
        (some (_root_.Turing.haltList (compile occurrenceRowsRevProgram)
          (encodeIndexedOccurrenceRows formula).reverse))
        ((24 * (Polynomial.X + 1) ^ 2).eval
          (relabel (encCNF formula)).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward-order indexed rows for every semantic CNF descriptor stream. -/
noncomputable def occurrenceRows_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      (fun formula : CNF => relabel (encCNF formula)) id
      encodeIndexedOccurrenceRows := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      occurrenceRowsRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

/-- Reinterpret the canonical occurrence-stream machine as producing the
decoded semantic formula expected by the row builder. -/
noncomputable def canonicalOccurrenceStream_asFormula_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id
      (fun formula : CNF => relabel (encCNF formula))
      (fun input : List CNFSym => decodeCNF input) := by
  let stream := canonicalOccurrenceStream_computableInPolyTime
  exact
    { tm := stream.tm
      inputAlphabet := stream.inputAlphabet
      outputAlphabet := stream.outputAlphabet
      time := stream.time
      outputsFun := fun input => by
        simpa [canonicalOccurrenceStream_eq] using stream.outputsFun input }

/-- A fixed polynomial-time TM2 maps every raw CNF word to its canonical
stream of indexed occurrence rows. -/
noncomputable def canonicalIndexedOccurrenceRows_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      canonicalIndexedOccurrenceRows := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      canonicalOccurrenceStream_asFormula_computableInPolyTime
      occurrenceRows_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List CNFSym =>
      encodeIndexedOccurrenceRows (decodeCNF input))
  simpa [Function.comp_def] using Classical.choice composed

/-- The fixed compiled-and-composed indexed-row machine. -/
noncomputable def canonicalIndexedOccurrenceRowsMachine :
    _root_.Turing.FinTM2 :=
  canonicalIndexedOccurrenceRows_computableInPolyTime.tm

/-- Direct output contract for the fixed raw-input indexed-row machine. -/
theorem canonicalIndexedOccurrenceRowsMachine_outputs (input : List CNFSym) :
    Nonempty (_root_.Turing.TM2OutputsInTime
      canonicalIndexedOccurrenceRows_computableInPolyTime.tm
      (List.map
        canonicalIndexedOccurrenceRows_computableInPolyTime.inputAlphabet.invFun
        input)
      (some (List.map
        canonicalIndexedOccurrenceRows_computableInPolyTime.outputAlphabet.invFun
        (canonicalIndexedOccurrenceRows input)))
      (canonicalIndexedOccurrenceRows_computableInPolyTime.time.eval
        input.length)) :=
  ⟨canonicalIndexedOccurrenceRows_computableInPolyTime.outputsFun input⟩

end TMClique
end Turing
end Chapter34
end CLRS


