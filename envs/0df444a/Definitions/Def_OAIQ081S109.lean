-- Prove2me | Definitions.Def_OAIQ081S109
-- name    : OAIQ081S109
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:27:46.613371+00:00
-- url     : https://prove2.me/theorems/ea4ba77c-f407-4094-a95d-bb179612b30e
-- title:
--   Definitions bundle OAIQ081S109 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 77 declarations of OpenAI's Lean: 52 definitions and 25 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Cache.unaryWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.cached`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.clearCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.cleared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.exportCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.fieldCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.restoredWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout.EncodesParameters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization.unaryCopy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Clause.caller`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Clause.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Clause.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Expansion.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Expansion.finished`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Expansion.forwardCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.accumulate`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.cleared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.lowReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.moved`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.multiply`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.nativeHigh`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch.finished`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch.staged`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters.project`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceControls.cutoffState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.unary`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.increment`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.machine`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.readyRecords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.entries`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.record`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgram.Coefficient`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgram.dictionaryBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRank.factor`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRank.words`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.seq`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram.SearchReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram.state` and 12 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLogSpace_HeadEvaluationProgram`, `SubexponentialSAT_SqrtLog_LeafParametersProgramCache`, `SubexponentialSAT_SqrtLog_LeafParametersProgramExports`, `SubexponentialSAT_SqrtLog_LeafParametersProgramExportsOps`, `SubexponentialSAT_SqrtLog_LeafParametersProgramExportsTable`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_LeafParametersProgramSerializationUnary`, `SubexponentialSAT_SqrtLog_LeafProgramClause`, `SubexponentialSAT_SqrtLog_LeafProgramExpansion`, `SubexponentialSAT_SqrtLog_LeafProgramExpansionForward`, `SubexponentialSAT_SqrtLog_LeafProgramFactorArithmetic`, `SubexponentialSAT_SqrtLog_LeafProgramFactorBase`, `SubexponentialSAT_SqrtLog_LeafProgramFactorDispatch`, `SubexponentialSAT_SqrtLog_LeafProgramFactorFinish`, `SubexponentialSAT_SqrtLog_LeafProgramLayoutMasters`, `SubexponentialSAT_SqrtLog_LeafProgramNodeFrames`, `SubexponentialSAT_SqrtLog_LeafProgramSourceControls`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramWords`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramArity`, `SubexponentialSAT_SqrtLog_MomentsProjectionProgramBase`, `SubexponentialSAT_SqrtLog_MomentsProjectionProgramNative`, `SubexponentialSAT_SqrtLog_PerturbationEmitProgram`, `SubexponentialSAT_SqrtLog_PerturbationProgramABI`, `SubexponentialSAT_SqrtLog_ProducedQueryRankProvenance`, `SubexponentialSAT_SqrtLog_ReconstructionProgramSetup`, `SubexponentialSAT_SqrtLog_RingCoefficientLiftProgram`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramBlock`, `SubexponentialSAT_SqrtLog_SetupPrimitives`, `SubexponentialSAT_SubexpBasePUnranking`, `SubexponentialSAT_SubexpCRTOuterControl`, `SubexponentialSAT_SubexpClauseMastersProgram`, `SubexponentialSAT_SubexpFactorCountSetup`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S082`, `OAIQ081S083`, `OAIQ081S084`, `OAIQ081S085`, `OAIQ081S088`, `OAIQ081S089`, `OAIQ081S091`, `OAIQ081S092`, `OAIQ081S093`, `OAIQ081S094` and `OAIQ081S099` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S125`, `OAIQ081S126`, `OAIQ081S127`, `OAIQ081S128`, `OAIQ081S129`, `OAIQ081S130`, `OAIQ081S131`, `OAIQ081S135` and `OAIQ081S136`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization.raw_dictionary_runsIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.forward_original_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.accumulate_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.hit_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRank.packing_coverage`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.hit_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRank.packing_coverage`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S082
import Definitions.Def_OAIQ081S083
import Definitions.Def_OAIQ081S084
import Definitions.Def_OAIQ081S085
import Definitions.Def_OAIQ081S088
import Definitions.Def_OAIQ081S089
import Definitions.Def_OAIQ081S091
import Definitions.Def_OAIQ081S092
import Definitions.Def_OAIQ081S093
import Definitions.Def_OAIQ081S094
import Definitions.Def_OAIQ081S099

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native full-key computation for the resumable attained-signature scan

One invocation preserves the assignment and all raw integer constraint rows.
Its local polynomial-time bound controls every scratch stack at every source
prefix. The generator retains candidate and predecessor cursors separately.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

namespace Rescan

abbrev Code := Cmd 16 24

end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete components of the sharp clause/core search from Appendix A.
The guard counts actual framed literals and executes the preserving subset tester.
The complete search and its polynomial resource bound are developed separately below. -/


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace Selector

def retainCandidate : Code :=
  .seq (atom (.copy 23 4)) (.ite 23 (.base .skip) (.seq (clear 9) (clear 12)))

end Selector

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProjectionProgramBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def machine (r : Fin 5 → Bool) (a : Tape) : State 5 10 := ⟨r,tapes a⟩

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProjectionProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms



namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def readyRecords (regs : Fin 5 → Bool) (source query output : List Bool) : State 5 10 :=
  machine (readRegs regs 0 3 source.head?) (clean source query output)

@[simp] theorem readyRecords_guard (regs : Fin 5 → Bool) (source query output : List Bool) :
    (readyRecords regs source query output).regs 3 = !source.isEmpty := by
  cases source <;> simp [readyRecords,machine,readRegs]

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram


/-! A fixed finite program for exact-support projection of a raw sparse dictionary.
Coefficients are opaque framed payloads. No normalization or arithmetic is used. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadEvaluationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete correction-mask checking for a head rescan. This local routine
preserves its input masters and charges every stack at every source prefix. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
open OAI BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

abbrev Code := Cmd 40 896

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpClauseMastersProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical preparation of the shared clause-factor masters

Four preserved binary input words supply the declared variable count, chunk
width, field modulus, and chunk count. Copies of the three counts are converted
by the checked binary-to-unary program. The checked full-shape capture then
builds the padded-array shape. No desired shape is an input assumption.

The modulus-width shape is a physical copy of the modulus word: its consumers
use its length, not its bits. The other two copies supply the binary chunk
width and field modulus at the clause-family's own persistent ports.
-/

namespace SubexponentialSAT.SubexpClauseMastersProgram

open BitProgram StructuredCalls

theorem copy_eval (src dst : Fin 14) (d : Data)
    (hsd : src ≠ dst) (hs : src ≠ 13) (hd : (13 : Fin 14) ≠ dst)
    (hempty : d.stacks dst = []) (htmp : d.stacks 13 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (copied d src dst) := by
  have h := ListRegisterProgram.copy_run src dst 13 (0 : Fin 3) 1
    hsd hs hd (by decide) d.regs d.stacks htmp
  apply Eval.call
  simpa only [copied, ListRegisterProgram.Run, StructuredProgram.State.withPC,
    StackRoutines.copyStacks, hempty, List.append_nil] using h

theorem embed_unary_output (src dst : Fin 14) (d : Data)
    (hd11 : dst ≠ 11) (hd12 : dst ≠ 12)
    (h11 : d.stacks 11 = []) (h12 : d.stacks 12 = []) :
    embedState id (unaryPorts dst) (copied d src 11)
      (CounterConversions.state CounterConversions.zeroRegs [] (unary (d.stacks src))) =
      write d dst (unary (d.stacks src)) := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id
    (unaryPorts_injective dst hd11 hd12)
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;>
      simp [unaryPorts, write, CounterConversions.state,
        Ne.symm hd11, Ne.symm hd12, h11, h12]
  · intro i hi
    have hi11 : i ≠ 11 := fun h => hi ⟨0, h.symm⟩
    have hid : i ≠ dst := fun h => hi ⟨1, h.symm⟩
    simp [write, copied, hi11, hid]

/-- A preserving binary-to-unary call using fixed work ports 11--13. -/
theorem unaryCopy_eval (src dst : Fin 14) (d : Data)
    (hs11 : src ≠ 11) (hs13 : src ≠ 13)
    (hd11 : dst ≠ 11) (hd12 : dst ≠ 12)
    (hd : d.stacks dst = []) (h11 : d.stacks 11 = [])
    (h12 : d.stacks 12 = []) (h13 : d.stacks 13 = []) :
    ∃ t ≤ unaryCopyBound (d.stacks src),
      Eval (unaryCopy src dst) t d (write d dst (unary (d.stacks src))) := by
  have hc := copy_eval src 11 d hs11 hs13 (by decide) h11 h13
  obtain ⟨t, ht, htrace⟩ := CounterConversions.unary_runs
    (readRegs d.regs 0 1 none) (d.stacks src) []
  simp only [List.append_nil] at htrace
  have hu := eval_call_lifted CounterConversions.unaryProgram id (unaryPorts dst)
    (copied d src 11) Function.injective_id (unaryPorts_injective dst hd11 hd12) htrace
  rw [embed_unary_input src dst d hd11 hd12 hd h12] at hu
  have hout := embed_unary_output src dst d hd11 hd12 h11 h12
  unfold unary at hout
  rw [hout] at hu
  refine ⟨7 * (d.stacks src).length + 5 + t, ?_, hc.seq hu⟩
  exact Nat.add_le_add_left ht _

end SubexponentialSAT.SubexpClauseMastersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramSerializationUnary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid, preserving serialization of parameter words as unary loop counters.
This is the checked bit conversion already used for clause-factor masters. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization

open BitProgram StructuredCalls BinaryArithmetic

abbrev unaryCopy := SubexpClauseMastersProgram.unaryCopy

/-- Ports 11--13 are temporary. The binary parameter remains at `src`, and
`dst` receives one true bit per unit of the parameter. -/
theorem unaryCopy_eval (src dst : Fin 14) (d : Data)
    (hs11 : src ≠ 11) (hs13 : src ≠ 13)
    (hd11 : dst ≠ 11) (hd12 : dst ≠ 12)
    (hd : d.stacks dst = []) (h11 : d.stacks 11 = [])
    (h12 : d.stacks 12 = []) (h13 : d.stacks 13 = []) :
    ∃ t ≤ unaryCopyBound (d.stacks src),
      Eval (unaryCopy src dst) t d
        (SubexpClauseMastersProgram.write d dst (List.replicate (BinaryArithmetic.toNat (d.stacks src)) true)) := by
  simpa only [SubexpClauseMastersProgram.unary,CounterPrograms.value_eq_toNat] using
    SubexpClauseMastersProgram.unaryCopy_eval src dst d hs11 hs13 hd11 hd12 hd h11 h12 h13

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SetupPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual fixed bit programs for the two logarithmic setup quantities.
Input and output numbers are arbitrary padded little-endian words. -/
namespace SubexponentialSAT.SqrtLog.Setup

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

theorem addConst_eval (k : ℕ) (xs : List Bool) :
    ∃ output t, value output = value xs + k ∧ output.length ≤ xs.length + k ∧
      t ≤ 8 * k * (xs.length + k + 1) ∧ Eval (addConst k) t (io xs) (io output) := by
  induction k with
  | zero => exact ⟨xs, 0, by simp, by simp, by simp, .base (.skip _)⟩
  | succ k ih =>
    obtain ⟨ys, t, hv, hl, ht, he⟩ := ih
    refine ⟨ripple true ys, t + (CounterPrograms.rippleCost true ys + 1), ?_, ?_, ?_,
      he.seq (increment_eval ys)⟩
    · rw [CounterPrograms.value_increment, hv]
      omega
    · exact (CounterPrograms.ripple_length_le true ys).trans (by omega)
    · have hc := CounterPrograms.rippleCost_le true ys
      nlinarith

end SubexponentialSAT.SqrtLog.Setup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native runtime leaf parameter production, integer guards, and paid setup.
The former composition modules are import-only compatibility shims. -/


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramBankRoots -/

/-! A fixed ten-comparison bit guard. All operands are runtime binary words.
This module states their data relation separately from parameter production. -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

/-- Public output ABI for a successful fast-path parameter setup. Other
entries are paid working values and need not be interpreted by callers. -/
def EncodesParameters (p : Parameters) (w : Words) : Prop :=
  BinaryArithmetic.toNat (w 13)=p.L ∧ BinaryArithmetic.toNat (w 14)=p.w ∧ BinaryArithmetic.toNat (w 17)=p.s ∧
  BinaryArithmetic.toNat (w 18)=p.r ∧ BinaryArithmetic.toNat (w 21)=p.Q ∧ BinaryArithmetic.toNat (w 25)=p.epsilonDen ∧
  BinaryArithmetic.toNat (w 29)=p.R ∧ BinaryArithmetic.toNat (w 31)=p.N ∧ BinaryArithmetic.toNat (w 33)=p.t ∧
  BinaryArithmetic.toNat (w 34)=p.d ∧ BinaryArithmetic.toNat (w 35)=3^p.d ∧ BinaryArithmetic.toNat (w 42)=p.J

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramExecutePublic -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramCache
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Cache


open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

attribute [local simp] Fin.coe_ofNat_eq_mod

def unaryWords (w : Words) : Words :=
  Function.update (Function.update (Function.update w 51
    (List.replicate (BinaryArithmetic.toNat (w 29)) true)) 52
      (List.replicate (BinaryArithmetic.toNat (w 46)) true)) 53
        (List.replicate (BinaryArithmetic.toNat (w 50)) true)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Cache

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramExportsOps
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid metadata exports. These commands touch only their destination and
three working registers; binary sources and all scratch words are restored. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports
open BitProgram StructuredCalls BinaryArithmetic
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

def fieldCommand (f : Field) : Code :=
  if f.unary then liftCommand (Serialization.unaryCopy 0 1) 0 1 regs (ports f)
  else .call (StackRoutines.copyProgram f.src f.dst 679 0 1)

def command : List Field → Code
  | [] => .base .skip
  | f::fs => .seq (fieldCommand f) (command fs)

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramExportsTable
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports
open BitProgram StructuredCalls BinaryArithmetic
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

def exportCommand : Code := command fields

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramExports
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native cache preparation, persistent metadata export, and bank restoration.
The guard register is framed. Unary cache tapes are cleared after copying so
ring setup again receives the ordinary binary parameter model. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports
open BitProgram StructuredCalls BinaryArithmetic Bank Circuit
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

def cached (a : Data) (r : Regs) (w : Words) : Data :=
  embedState bankRegs bank a (Bank.state r (Cache.unaryWords w))

def cleared (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,BankRoutines.clearBankStacks clearPorts a.stacks⟩
def clearCost (a : Data) : ℕ := 2*(clearPorts.map (fun j => (a.stacks j).length)).sum+57

def restoredWords (w : Words) : Words := fun j => if 46 ≤ j.val then [] else w j

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramClause
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Evaluate the optional marked clause without applying a hash idempotent.
The constant seed is copied by the machine, and every original literal is
processed by the same concrete decoder and sparse arithmetic as hash rows. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Clause

open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open MomentsProgram

abbrev command : Cmd 8 96 := .seq (copy 69 67 70) (clauseLoop arithmetic)
def program := compiled command 63 67

abbrev caller : Cmd 40 768 :=
  .call (ProgramLinking.liftProgram program callerRegisters callerStacks)

end SubexponentialSAT.SqrtLog.LeafProgram.Clause

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramExpansion
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native expansion of one selected raw hash row.  The row is read from the
dispatcher result; every original clause lookup and coefficient lift is paid
by the fixed assembler.  The original formula and dynamic width words are
read in place, so they remain available for the next factor. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Expansion

open SubexponentialSAT BitProgram StructuredCalls

abbrev command : Cmd 40 768 :=
  .call (ProgramLinking.liftProgram HashInputProgram.Loop.assembleProgram register stackMap)

noncomputable def finished (a : Data) (rf : Fin 8 → Bool) (word : List Bool) : Data :=
  embedState register stackMap a
    (HashInputProgram.Loop.data rf [] (a.stacks 708) (a.stacks 707)
      (a.stacks 700) (a.stacks 280) word [] [] [] [])

end SubexponentialSAT.SqrtLog.LeafProgram.Expansion

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramExpansionForward
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The preserved source lookup returns forward frame contents. Reverse this
actual tape before invoking the raw-tuple assembler. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Expansion
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

abbrev forwardCommand : Cmd 40 768 := .seq reverseInput command

end SubexponentialSAT.SqrtLog.LeafProgram.Expansion

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Wide native factor arithmetic and paid tape movement. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls

abbrev Data := State 40 768

def multiply : Code := .call (ProgramLinking.liftProgram
  (compiled (HashCircuitProgram.Native.productAdapter HashCircuitProgram.Native.product) 61 67)
    nativeRegisters nativeStacks)

/-- The running head-local product is parked on151 while the next factor is
computed on67. Native multiplication consumes61 and returns67. -/
def accumulate : Code := .seq (move 67 61)
  (.seq (move 151 67) (.seq multiply (move 67 151)))


/-- Movement itself is paid; output-state notation is used only in proofs. -/
def moved (a : Data) (src dst : Fin 768) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks dst (a.stacks src ++ a.stacks dst)) src []⟩


end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual native multiplication call in the wide factor loop. This
adapter derives its execution from the concrete sparse product program and
retains an exact frame, including every outer factor/source tape. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native

def lowReady (a : Data) (e : MomentsProgram.Product.Store) : Prop :=
  ∀ i : Fin 56, a.stacks (nativeStacks (Memory.lowPort i)) =
    MomentsProgram.Product.tapes e i

def nativeHigh (a : Data) (i : Fin 40) : List Bool :=
  a.stacks (nativeStacks (Memory.highPort i))

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorDispatch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The factor dispatcher in the native leaf's actual bank.  The parsed ID
is retained for incidence preparation.  The mark flag is read from a tape,
not inserted as a program parameter. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def staged (a : Data) : Data :=
  ⟨readRegs (copied a).regs 7 0 (a.stacks 706).head?,(copied a).stacks⟩

noncomputable def finished (a : Data) (rf : Fin 8 → Bool)
    (rows clauses : List (List Bool)) (marked : Bool) (mark factor : ℕ) : Data :=
  embedState register stackMap (staged a)
    ⟨rf,LeafFactorDispatchProgram.outputStacks rows clauses marked mark factor⟩

end SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpBasePUnranking
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual base-p digit extraction

A digit is obtained by the checked binary long-division program. Its remainder
is copied to the fixed width of the modulus, while the padded high bits are
removed. Repeated extraction uses the quotient as the next rank. The modulus,
arity, and all widths are data; the instruction table is fixed.
-/

namespace SubexponentialSAT.SubexpBasePUnranking

open BitProgram StructuredCalls StackRoutines
open BinaryArithmetic ModularQuotientArithmetic

/-- A real execution materializes all fixed-width digit records. The result is
least-significant base-p digit first, with little-endian bits inside each record. -/
theorem command_eval (regs : Fin 8 → Bool) (modulus rank arity output : List Bool) :
    ∃ n, n + 1 ≤ budget modulus rank arity ∧ ∃ finalRegs : Fin 8 → Bool,
      Eval command n (state regs modulus rank arity [] output)
        (state finalRegs modulus (remainingRank modulus arity.length rank) [] []
          ((digitWords modulus arity.length rank).flatten ++ output)) := by
  have hp := popArity_eval regs modulus rank arity [] output
  obtain ⟨nl, hnl, rf, hl⟩ := loop_eval regs modulus rank arity [] output
  simp only [List.append_nil] at hl
  have ht := transfer_eval 11 12 (by decide) rf
    (tapes [] modulus (remainingRank modulus arity.length rank) [] [] [] []
      (digitWords modulus arity.length rank).flatten.reverse output)
  simp only [transferStacks, tapes_11, tapes_12, tapes_update_11, tapes_update_12,
    List.reverse_reverse, List.length_reverse, digitWords_flatten_length] at ht
  have h := hp.seq (hl.seq ht)
  refine ⟨_, ?_, readRegs rf 1 3 none, h⟩
  dsimp [budget, stepBudget] at *
  nlinarith

end SubexponentialSAT.SubexpBasePUnranking

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceControls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid source-control copies into the isolated 340-stack worker. All inputs
come from runtime layout/ring masters; no source polynomial is supplied. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceControls
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
def cutoffState (a : Data) : Data :=
  ⟨Function.update (readRegs a.regs 0 1 none) 0 true,
    Function.update a.stacks 550 (true :: (a.stacks 138 ++ a.stacks 550))⟩

end SubexponentialSAT.SqrtLog.LeafProgram.SourceControls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationProgramABI
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical interchange format for prepared incidence rows. Coefficients are
fixed-width extension-ring words; keys contain unary exponents and n support
bits. The outer variable key is Encoding.encodeNat v, matching the hash lookup.
This file also discharges primitive emission of each output record. -/
namespace SubexponentialSAT.SqrtLog.PerturbationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

abbrev Coefficient (d B : ℕ) := RingProgram.Code (Word B) d

/-- No outer list markers: one framed key and one framed coefficient per item. -/
def dictionaryBits {n d B : ℕ} (p : List (Index (Fin n) × Coefficient d B)) : List Bool :=
  p.flatMap fun a => Encoding.frame (encodeIndex a.1) ++ Encoding.frame (RingProgram.flat a.2)

@[simp] theorem dictionaryBits_cons {n d B : ℕ}
    (a : Index (Fin n) × Coefficient d B) (p : List (Index (Fin n) × Coefficient d B)) :
    dictionaryBits (a::p) = Encoding.frame (encodeIndex a.1) ++
      Encoding.frame (RingProgram.flat a.2) ++ dictionaryBits p := by
  simp [dictionaryBits, List.append_assoc]

end SubexponentialSAT.SqrtLog.PerturbationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationEmitProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native emission of the positive part of a shifted coefficient array.
The dimensions and the singleton support mask are runtime data. The constant
cell is consumed without emission; all later cells are framed, including zero
coefficients. No normalization or arithmetic oracle is used. -/
namespace SubexponentialSAT.SqrtLog.PerturbationEmitProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl

def record (mask : List Bool) (j : ℕ) (coeff : List Bool) : List Bool :=
  Encoding.frame (keyBits mask j) ++ Encoding.frame coeff

end SubexponentialSAT.SqrtLog.PerturbationEmitProgram


namespace SubexponentialSAT.SqrtLog.PerturbationEmitProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open PerturbationProgram _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

/-- Exact mathematical record list, before the native prepend reversal. -/
def entries {n d B : ℕ} (v : Fin n) :
    ℕ → List (Coefficient d B) → List (Index (Fin n) × Coefficient d B)
  | _, [] => []
  | j, c::cs => (⟨0,j,{v}⟩,c)::entries v (j+1) cs

@[simp] theorem entries_length {n d B : ℕ} (v : Fin n) (j : ℕ)
    (cs : List (Coefficient d B)) : (entries v j cs).length=cs.length := by
  induction cs generalizing j with
  | nil => rfl
  | cons c cs ih => simp [entries,ih]

@[simp] theorem record_typed {n d B : ℕ} (v : Fin n) (j : ℕ) (c : Coefficient d B) :
    record (encodeMask {v}) j (RingProgram.flat c) =
      Encoding.frame (encodeIndex (⟨0,j,{v}⟩ : Index (Fin n))) ++
        Encoding.frame (RingProgram.flat c) := by
  simp [record,keyBits,PerturbationProgram.Key.bits,encodeIndex,Encoding.encodeNat,
    List.append_assoc]

@[simp] theorem dictionaryBits_append {n d B : ℕ}
    (p q : List (Index (Fin n) × Coefficient d B)) :
    dictionaryBits (p++q)=dictionaryBits p++dictionaryBits q := by
  simp [dictionaryBits,List.flatMap_append]

end SubexponentialSAT.SqrtLog.PerturbationEmitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid cleanup and multiplication after a real factor service. The running
product remains on151 and all source/cache tapes are framed. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native

abbrev cleared := LeafAssignmentSetupProgram.cleared

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramLayoutMasters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Layout/source metadata are parked outside the native arithmetic bank.
CRT and scalar arithmetic use several ports128..141 as scratch; these values
are therefore physically reloaded for each node and cleared before CRT. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem park_local_eval (a : LocalData) (ht : a.stacks 684 = []) :
    Eval parkLocal (parkCost a) a (parked a) :=
  (copyMany_eval 684 parkPairs a park_valid ht).seq
    (clearMany_eval lowPorts (copyManyState parkPairs a))

theorem loaded_low (a : LocalData) (hz : ∀ i, a.stacks (low i) = []) (i : Fin 14) :
    (loaded a).stacks (low i) = a.stacks (high i) := by
  exact copyMany_value loadPairs a load_nodup
    (by intro p hp; simp only [loadPairs,List.mem_map,List.mem_finRange,true_and] at hp
        obtain ⟨j,rfl⟩ := hp; exact hz j)
    load_sep (high i,low i) (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)

theorem loaded_frame (a : LocalData) (j : Fin 768) (hj : j ∉ lowPorts) :
    (loaded a).stacks j = a.stacks j := by
  apply copyMany_frame
  intro p hp he
  simp only [loadPairs,List.mem_map,List.mem_finRange,true_and] at hp
  obtain ⟨i,rfl⟩ := hp
  apply hj
  exact List.mem_map.mpr ⟨i,List.mem_finRange i,he.symm⟩

def project (a : Data) : LocalData := ⟨a.regs ∘ registers,a.stacks⟩

end SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid conversion of flat fixed-width node words to framed node records.
Both the width and the number of nodes are read from runtime unary tapes. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeFrames

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpTaylorFrames
open SubexponentialSAT.SubexpExponentProgram

theorem ringWords_trace {d B : ℕ} (width : List Bool)
    (hw : width.length = d * B)
    (words : List (RingProgram.Code (SubexponentialSAT.SubexpQuarticRing.Word B) d))
    (regs : Fin 5 → Bool) :
    ∃ finalRegs, Trace program (words.length * (28 * width.length + 33) + 11)
      ((state regs (data width words.length (words.map RingProgram.flat).flatten [])).withPC
        (some program.entry))
      ((state finalRegs {data width 0 [] [] with
        output := Encoding.encodeList id (words.map RingProgram.flat)}).withPC none) := by
  have hwords : ∀ word ∈ words.map RingProgram.flat, word.length = width.length := by
    intro word hm
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hm
    simpa only [RingProgram.flat_length] using hw.symm
  simpa only [List.length_map] using trace width (words.map RingProgram.flat) hwords regs

end SubexponentialSAT.SqrtLog.LeafProgram.NodeFrames

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramWords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid word movement and binary-to-unary conversion used by ring setup.
The helpers update actual tapes; a state equality is never used as a free
copy, clear, or counter conversion. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

open BitProgram StructuredCalls StackRoutines

abbrev unary (src dst : Fin 640) : Cmd 32 640 :=
  liftCommand (LeafParametersProgram.Serialization.unaryCopy 0 1) 0 1
    unaryRegisters (unaryPorts src dst)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFactorCountSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving setup of a factor-local assignment count

The fixed program copies a unary arity, counts the copy into a binary exponent,
and invokes the actual preserving power routine.  The base and unary arity are
retained verbatim.  The number of bits in either input is runtime data.
-/

namespace SubexponentialSAT.SubexpFactorCountSetup

open BitProgram StructuredCalls StackRoutines

def countProgram := compiled countCommand (1 : Fin 13) 2

end SubexponentialSAT.SubexpFactorCountSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramArity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime outer record fold computing the maximum masked scope length and
factor count, including empty scope records. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
def increment : Code := .seq (.base (.atom (.set 0 true))) (.base (.atom (.push 11 0)))

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryRankProvenance
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The rank certificate refers to the packing and word table actually
produced by the native packing caller, with its original incidence order. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open PackingCallerProgram

abbrev factor (p : Problem) :=
  PackingIncidenceInput.Semantics.factor p.scopes p.n p.mask p.mask_le

def words (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (Fin p.n ⊕ Fin p.factors) → Word p.r p.Q
  | .inl v => (p.words a tail).get ⟨v.val,by rw [p.words_length]; omega⟩
  | .inr f => (p.words a tail).get ⟨p.n+f.val,by rw [p.words_length]; omega⟩

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete tape operations and traversal assertions for the outer CRT.
All operations in this module are fixed finite programs. Arithmetic is supplied
by the separately defined concrete CRT service commands. -/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open BitProgram StructuredCalls SubexpScanPrimitives

def transfer (src dst : Fin 320) : Code :=
  .call (StackRoutines.transferProgram src dst (0 : Fin 16) 1)

def clear (src : Fin 320) : Code :=
  .call (StackRoutines.clearProgram src (0 : Fin 16) 1)

def testNodes : Code := .base (.atom (.peek 257 0 15))

def incrementIndex : Code :=
  .base (.seq (.atom (.set 0 false)) (.atom (.push 260 0)))

def resetThreeRegisters : Code :=
  .base (.seq (.atom (.set 0 false))
    (.seq (.atom (.set 1 false)) (.atom (.set 2 false))))

def countDimension : Code :=
  .call (ProgramLinking.liftProgram SubexpFactorCountSetup.countProgram registers countPorts)

def takeNode : Code := takeWord 104 278 279 257 259 0 1
def takeJet : Code := takeWord 277 278 279 266 225 0 1

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Arbitrary-width physical CRT initialization. The computed ring-zero word
is passed on stack 280; all copying, width construction and unary-to-binary
conversion are charged by actual primitive traces. -/

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram

def seq (a b : Code) : Code := .seq a b

end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingCoefficientLiftProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! A fixed scanner widens consecutive two-bit coefficients using a runtime
width tape. The original width is preserved, and all bit movement is paid. -/
namespace SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ModularPrograms
open SubexponentialSAT.Subexp.MatrixProgramSupport

def state (regs : Fin 8 → Bool) (input width shape word output temp final : List Bool) : Data :=
  ⟨regs,tapes input width shape word output temp final⟩

theorem pad_eval (regs : Fin 8 → Bool) (input width shape word output temp final : List Bool) :
    ∃ rf, Eval pad (4*shape.length+3)
      (state regs input width shape word output temp final)
      (state rf input width [] (word.drop shape.length)
        ((ModularArithmetic.padTo shape word).reverse ++ output) temp final) := by
  obtain ⟨rf,ht⟩ := ModularRingPrograms.paddingPrefix_correct regs shape word output
  let d := state regs input width shape word output temp final
  let a : State 8 3 := ⟨regs,operandStacks shape word output⟩
  let b : State 8 3 := ⟨rf,operandStacks [] (word.drop shape.length)
    ((ModularArithmetic.padTo shape word).reverse ++ output)⟩
  have ha : embedState id paddingPorts d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id paddingPorts_injective
    · intro i; rfl
    · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hb : embedState id paddingPorts d b = state rf input width [] (word.drop shape.length)
      ((ModularArithmetic.padTo shape word).reverse ++ output) temp final := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id paddingPorts_injective
    · intro i; rfl
    · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro j hj
      fin_cases j <;> try rfl
      · exact False.elim (hj ⟨0,rfl⟩)
      · exact False.elim (hj ⟨1,rfl⟩)
      · exact False.elim (hj ⟨2,rfl⟩)
  have ht' : Trace paddingProgram (4*shape.length+3)
      (a.withPC (some paddingProgram.entry)) (b.withPC none) := ht
  have h := eval_call_lifted paddingProgram id paddingPorts d
    Function.injective_id paddingPorts_injective ht'
  exact ⟨rf,by simpa only [ha,hb,pad] using h⟩

theorem popInput_eval (regs : Fin 8 → Bool) (r : Fin 8) (bit : Bool)
    (input width shape word output temp final : List Bool) :
    Eval (.base (.atom (.pop 0 r 6))) 1
      (state regs (bit::input) width shape word output temp final)
      (state (readRegs regs r 6 (some bit)) input width shape word output temp final) := by
  apply Eval.base
  convert StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (r := 8) (s := 7) 0 r 6)
    (state regs (bit::input) width shape word output temp final) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;>
        simp [state,tapes,StructuredProgram.Atom.instr,execInstr]

theorem pushWord_eval (regs : Fin 8 → Bool) (r : Fin 8)
    (input width shape word output temp final : List Bool) :
    Eval (.base (.atom (.push 3 r))) 1
      (state regs input width shape word output temp final)
      (state regs input width shape (regs r::word) output temp final) := by
  apply Eval.base
  convert StructuredProgram.Eval.atom (StructuredProgram.Atom.push (r := 8) (s := 7) 3 r)
    (state regs input width shape word output temp final) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;>
        simp [state,tapes,StructuredProgram.Atom.instr,execInstr]

theorem takeTwo_eval (regs : Fin 8 → Bool) (a b : Bool)
    (input width shape output temp final : List Bool) :
    ∃ rf, Eval takeTwo 4 (state regs (a::b::input) width shape [] output temp final)
      (state rf input width shape [a,b] output temp final) := by
  let r1 := readRegs regs 0 6 (some a)
  let r2 := readRegs r1 1 6 (some b)
  have h1 := popInput_eval regs 0 a (b::input) width shape [] output temp final
  have h2 := popInput_eval r1 1 b input width shape [] output temp final
  have h3 := pushWord_eval r2 1 input width shape [] output temp final
  have h4 := pushWord_eval r2 0 input width shape [b] output temp final
  have hb : r2 1=b := by simp [r2,readRegs]
  have ha : r2 0=a := by simp [r2,r1,readRegs]
  rw [hb] at h3
  rw [ha] at h4
  exact ⟨r2,h1.seq (h2.seq (h3.seq h4))⟩

theorem step_eval (regs : Fin 8 → Bool) (word input width output final : List Bool)
    (hword : word.length=2) (hwidth : 2 ≤ width.length) :
    ∃ rf, Eval step (11*width.length+12)
      (state regs (word++input) width [] [] output [] final)
      (state rf input width [] [] ((ModularArithmetic.padTo width word).reverse++output) [] final) := by
  obtain ⟨a,b,rfl⟩ : ∃ a b, word=[a,b] := by
    cases word with
    | nil => simp at hword
    | cons a word =>
      cases word with
      | nil => simp at hword
      | cons b word =>
        have hw : word=[] := List.length_eq_zero_iff.mp (by simpa using hword)
        exact ⟨a,b,by simp [hw]⟩
  obtain ⟨r1,h1⟩ := takeTwo_eval regs a b input width [] output [] final
  obtain ⟨s2,h2,hs2⟩ := copy_eval (1 : Fin 7) 2 5 (by decide) (by decide) (by decide)
    (state r1 input width [] [a,b] output [] final) rfl
  have hstate : s2=state s2.regs input width width [a,b] output [] final := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · rw [hs2]; funext i; fin_cases i <;> simp [state,tapes,StackRoutines.copyStacks]
  rw [hstate] at h2
  obtain ⟨rf,h3⟩ := pad_eval s2.regs input width width [a,b] output [] final
  have hd : [a,b].drop width.length=[] := List.drop_eq_nil_of_le (by simpa using hwidth)
  rw [hd] at h3
  have he := h1.seq (h2.seq h3)
  have hc : 4+((7*width.length+5)+(4*width.length+3))=11*width.length+12 := by omega
  refine ⟨rf,?_⟩
  simpa only [step, state, tapes, Matrix.cons_val_one, Matrix.cons_val_zero,
    List.cons_append, List.nil_append, hc] using he

end SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram


namespace SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

theorem peek_eval (regs : Fin 8 → Bool) (input width output final : List Bool) :
    Eval peek 1 (state regs input width [] [] output [] final)
      (state (readRegs regs 0 7 input.head?) input width [] [] output [] final) := by
  apply Eval.base
  convert StructuredProgram.Eval.atom (StructuredProgram.Atom.peek (r := 8) (s := 7) 0 0 7)
    (state regs input width [] [] output [] final) using 1 ;
    simp [state,tapes,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,execInstr]

theorem loop_eval (words : List (List Bool)) (width : List Bool)
    (hwords : ∀ w ∈ words, w.length=2) (hwidth : 2 ≤ width.length)
    (regs : Fin 8 → Bool) (output final : List Bool) :
    ∃ rf, Eval loop (words.length*(11*width.length+14)+1)
      (state (readRegs regs 0 7 words.flatten.head?) words.flatten width [] [] output [] final)
      (state rf [] width [] [] ((padded width words).reverse++output) [] final) := by
  induction words generalizing regs output with
  | nil =>
    refine ⟨readRegs regs 0 7 none,?_⟩
    simp only [List.length_nil,Nat.zero_mul,Nat.zero_add,List.flatten_nil,
      List.head?_nil,padded_nil,List.reverse_nil,List.nil_append]
    apply Eval.while_false
    simp [state,readRegs_present]
  | cons word words ih =>
    have hw := hwords word (by simp)
    obtain ⟨a,b,rfl⟩ : ∃ a b, word=[a,b] := by
      cases word with
      | nil => simp at hw
      | cons a word =>
        cases word with
        | nil => simp at hw
        | cons b word =>
          have hz : word=[] := List.length_eq_zero_iff.mp (by simpa using hw)
          exact ⟨a,b,by simp [hz]⟩
    obtain ⟨r1,h1⟩ := step_eval (readRegs regs 0 7 (some a)) [a,b] words.flatten width output final
      rfl hwidth
    have h2 := peek_eval r1 words.flatten width
      ((ModularArithmetic.padTo width [a,b]).reverse++output) final
    obtain ⟨rf,h3⟩ := ih (fun w hw => hwords w (by simp [hw])) r1
      ((ModularArithmetic.padTo width [a,b]).reverse++output)
    have h := Eval.while_true
      (show (state (readRegs regs 0 7 (some a)) ([a,b]++words.flatten)
        width [] [] output [] final).regs 7=true by simp [state,readRegs_present])
      (h1.seq h2) h3
    have hc : (11*width.length+12)+1+(words.length*(11*width.length+14)+1)+1=
        (words.length+1)*(11*width.length+14)+1 := by ring
    rw [hc] at h
    refine ⟨rf,?_⟩
    simpa only [loop,List.length_cons,List.flatten_cons,List.head?_cons,List.cons_append,
      List.nil_append,padded_cons,List.reverse_append,List.append_assoc] using h

theorem scan_eval (words : List (List Bool)) (width : List Bool)
    (hwords : ∀ w ∈ words, w.length=2) (hwidth : 2 ≤ width.length)
    (regs : Fin 8 → Bool) (output final : List Bool) :
    ∃ rf, Eval scan (words.length*(11*width.length+14)+2)
      (state regs words.flatten width [] [] output [] final)
      (state rf [] width [] [] ((padded width words).reverse++output) [] final) := by
  have h1 := peek_eval regs words.flatten width output final
  obtain ⟨rf,h2⟩ := loop_eval words width hwords hwidth regs output final
  have h := h1.seq h2
  have hc : 1+(words.length*(11*width.length+14)+1)=words.length*(11*width.length+14)+2 := by omega
  rw [hc] at h
  exact ⟨rf,h⟩

theorem command_eval (words : List (List Bool)) (width : List Bool)
    (hwords : ∀ w ∈ words, w.length=2) (hwidth : 2 ≤ width.length)
    (regs : Fin 8 → Bool) :
    ∃ rf, Eval command (words.length*(14*width.length+14)+5)
      (state regs words.flatten width [] [] [] [] [])
      (state rf [] width [] [] [] [] (padded width words)) := by
  obtain ⟨r1,h1⟩ := scan_eval words width hwords hwidth regs [] []
  simp only [List.append_nil] at h1
  obtain ⟨e,h2,hs⟩ := transfer_eval (4 : Fin 7) 6 (by decide)
    (state r1 [] width [] [] (padded width words).reverse [] [])
  have he : e=state e.regs [] width [] [] [] [] (padded width words) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · rw [hs]; funext i; fin_cases i <;>
        simp [state,tapes,StackRoutines.transferStacks]
  rw [he] at h2
  have hlen : ((state r1 [] width [] [] (padded width words).reverse [] []).stacks 4).length =
      words.length*width.length := by
    change (padded width words).reverse.length=_
    rw [List.length_reverse,padded_length]
  rw [hlen] at h2
  have h := h1.seq h2
  have hc : (words.length*(11*width.length+14)+2)+(3*(words.length*width.length)+3)=
      words.length*(14*width.length+14)+5 := by ring
  rw [hc] at h
  exact ⟨e.regs,h⟩

end SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram


/-! Exact byte bridge from canonical F3 coefficients to the supplied-polynomial
ring model. The program itself has no degree or width parameter. -/


/-! Search-to-table ABI. The search has 22 registers and 28 stacks. In particular,
stack24 may contain unread candidates and is outside this adapter's ports. -/
namespace SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def SearchReady (s : SearchData) : Prop :=
  s.stacks 23=[] ∧ s.stacks 15=[] ∧ s.stacks 25=[] ∧ s.stacks 26=[] ∧ s.stacks 21=[]

end SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramBlock
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem blockStep_eval (rows : List (List Bool)) (s : Store) (regs : Fin 2 → Bool) (C : ℕ)
    (hp : s.powers = rows.flatten)
    (hw : ∀ row ∈ rows, row.length = s.width.length)
    (hword : s.word = []) (hindex : s.index = [])
    (hj : s.ji = []) (hcj : s.jc = []) (hi : s.ii = []) (hci : s.ic = [])
    (hcap : s.ki.length + 2*s.degree.length*s.degree.length ≤ C)
    (hv : ∀ i < s.degree.length, ∀ j < s.degree.length,
      s.ki.length+i*s.degree.length+j*s.degree.length < rows.length) :
    ∃ n ≤ blockBudget s.width.length s.degree.length C, ∃ rf,
      Eval blockStep n (state regs s)
        (state rf {s with
          ki := false :: s.ki
          rev := (matrixBits rows s.degree.length s.ki.length s.degree.length).reverse ++ s.rev}) := by
  obtain ⟨r1, h1⟩ := startBlock_eval s regs hi hci
  let a : Store := {s with ii := s.ki, ic := s.degree}
  have hcap' : a.ii.length + a.ic.length*a.degree.length + a.degree.length*a.degree.length ≤ C := by
    dsimp [a]
    nlinarith
  obtain ⟨n, hn, r2, idx, hidx, h2⟩ := iScan_eval rows a r1 C hp hw hword hindex hj hcj hcap' hv
  let b : Store := {s with
    ic := []
    ii := idx
    rev := (matrixBits rows s.degree.length s.ki.length s.degree.length).reverse ++ s.rev}
  have h2' : Eval iScan n (state r1 a) (state r2 b) := h2
  have h3 := finishBlock_eval b r2
  refine ⟨(7*s.ki.length+7*s.degree.length+10)+(n+(2*idx.length+4)),
    ?_, readRegs r2 0 1 none, ?_⟩
  · dsimp [a] at hn hidx
    dsimp [blockBudget]
    nlinarith
  · simpa only [blockStep, a, b, hi, hci] using h1.seq (h2'.seq h3)

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end


