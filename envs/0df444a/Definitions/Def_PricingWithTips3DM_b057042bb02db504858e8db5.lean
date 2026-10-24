-- Prove2me | Definitions.Def_PricingWithTips3DM_b057042bb02db504858e8db5
-- name    : PricingWithTips3DM_b057042bb02db504858e8db5
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T05:50:22.919967+00:00
-- url     : https://prove2.me/theorems/5817bd49-b02b-47de-86dd-63c1f5f00ec8
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesGenericRuntime
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_38e334b9b610c42fe7b114ed
import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Generic polynomial runtime of the occurrence-row pair controller
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.TMClique

open PolyBuilder

/-- Named semantic output used by the generic polynomial-time witness. -/
def encodeCompatibleOccurrenceIterationsReverse
    (entries : List (IndexedOccurrence × Nat)) : List CliqueSym :=
  encodeCompatibleOccurrenceIterations entries.reverse

/-- The generic terminating controller has the same cubic bound as its
formula-specific specialization. -/
theorem compatibilityEdgesEntriesSteps_le_input
    (entries : List (IndexedOccurrence × Nat)) :
    compatibilityEdgesEntriesSteps entries ≤
      80 * ((encodeIndexedOccurrenceEntries entries).length + 1) ^ 3 := by
  let inputLength := (encodeIndexedOccurrenceEntries entries).length
  have hreverse :
      (encodeIndexedOccurrenceEntries entries.reverse).length =
        inputLength := by
    simpa [inputLength] using
      encodeIndexedOccurrenceEntries_reverse_length entries
  have hload := compatibilityEdgesLoadRowsSteps_le_input entries
  have houter :=
    compatibilityEdgesOuterIterationsSteps_le_input entries.reverse
  rw [hreverse] at houter
  have hlinear : inputLength + 1 ≤ (inputLength + 1) ^ 3 :=
    Nat.le_pow (by omega)
  simp only [compatibilityEdgesEntriesSteps]
  change compatibilityEdgesLoadRowsSteps entries +
      compatibilityEdgesOuterIterationsSteps entries.reverse + 3 ≤
    80 * (inputLength + 1) ^ 3
  nlinarith

/-- Polynomial-time computability of the reusable arbitrary-row controller. -/
noncomputable def compatibilityEdgesEntries_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeIndexedOccurrenceEntries id
      encodeCompatibleOccurrenceIterationsReverse where
  tm := compile compatibilityEdgesProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 80 * (Polynomial.X + 1) ^ 3
  outputsFun := fun entries => by
    have builderRun := compatibilityEdges_entriesRun entries
    have compiledRun := compile_evalsToInTime compatibilityEdgesProgram
      builderRun
    have machineRun : EvalsToInTime
        (compile compatibilityEdgesProgram).step
        (_root_.Turing.initList (compile compatibilityEdgesProgram)
          (encodeIndexedOccurrenceEntries entries))
        (some (_root_.Turing.haltList (compile compatibilityEdgesProgram)
          (encodeCompatibleOccurrenceIterations entries.reverse)))
        (compatibilityEdgesEntriesSteps entries) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime := compatibilityEdgesEntriesSteps_le_input entries
    have polynomialBound : compatibilityEdgesEntriesSteps entries ≤
        (80 * (Polynomial.X + 1) ^ 3).eval
          (encodeIndexedOccurrenceEntries entries).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
        Polynomial.eval_ofNat] using htime
    have boundedRun : EvalsToInTime
        (compile compatibilityEdgesProgram).step
        (_root_.Turing.initList (compile compatibilityEdgesProgram)
          (encodeIndexedOccurrenceEntries entries))
        (some (_root_.Turing.haltList (compile compatibilityEdgesProgram)
          (encodeCompatibleOccurrenceIterations entries.reverse)))
        ((80 * (Polynomial.X + 1) ^ 3).eval
          (encodeIndexedOccurrenceEntries entries).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans polynomialBound⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile,
      encodeCompatibleOccurrenceIterationsReverse] using boundedRun

end CLRS.Chapter34.Turing.TMClique


