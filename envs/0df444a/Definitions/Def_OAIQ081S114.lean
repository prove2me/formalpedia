-- Prove2me | Definitions.Def_OAIQ081S114
-- name    : OAIQ081S114
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:30:02.570446+00:00
-- url     : https://prove2.me/theorems/9711b1d0-6bfe-4b2f-87a0-9b3c03235001
-- title:
--   Definitions bundle OAIQ081S114 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 76 declarations of OpenAI's Lean: 53 definitions, 6 inductive types or structures and 17 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.rawInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.rawLocal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Local.prepared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.initializedStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.wordBlockCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.clearedAt`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.clipState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.eraseData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.eraseReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.storageCleared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.storageCopied`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage.cleaned`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage.cleanupCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage.stageCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage.staged`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage.temporaryCleared`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.KeyEquality.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.KeyEquality.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.Boundary`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.ScanInvariant`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.countdownPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.loopSpace`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.naturalKey`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.predecessorPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.workState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures.assignmentEquiv`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures.integerKey`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram.finishScan`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram.firstSuccess`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram.firstSuccessStep`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram.prepareScan`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram.prepareSearch`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram.scanPreparedStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram.scanWrapper`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidates.tupleBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.GraphMatrixReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.LocalMatrixReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.RejectionBody`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.RejectionFrame` and 19 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_AcceptedQueryStage`, `SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram`, `SubexponentialSAT_SqrtLogSpace_AttainedSignatureRescan`, `SubexponentialSAT_SqrtLogSpace_AttainedSignatures`, `SubexponentialSAT_SqrtLogSpace_CodeCandidateProgram`, `SubexponentialSAT_SqrtLogSpace_CodeCandidates`, `SubexponentialSAT_SqrtLogSpace_CodeChecks`, `SubexponentialSAT_SqrtLogSpace_Counters`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLogSpace_HashGreedyProgram`, `SubexponentialSAT_SqrtLogSpace_HashMassStaged`, `SubexponentialSAT_SqrtLogSpace_HashTrialStage`, `SubexponentialSAT_SqrtLogSpace_SparseCodeProgram`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramCapture`, `SubexponentialSAT_SqrtLog_PackingProgramCombine`, `SubexponentialSAT_SqrtLog_PackingProgramScale`, `SubexponentialSAT_SqrtLog_PackingProgramZipSemantics`, `SubexponentialSAT_SqrtLog_PackingWeightProgramNative`, `SubexponentialSAT_SqrtLog_ReconstructionProgramLocal`, `SubexponentialSAT_SqrtLog_ReconstructionProgramSetup`, `SubexponentialSAT_SqrtLog_RingProgramSerialization`, `SubexponentialSAT_SqrtLog_SquarefreeProgramClip`, `SubexponentialSAT_SqrtLog_SquarefreeProgramErase`, `SubexponentialSAT_SqrtLog_SquarefreeProgramLess`, `SubexponentialSAT_SqrtLog_SquarefreeProgramScan`, `SubexponentialSAT_SqrtLog_SquarefreeProgramStorage`, `SubexponentialSAT_SubexpSetupStorage`, `SubexponentialSAT_Subexp_AssignmentInputCall`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S082`, `OAIQ081S083`, `OAIQ081S084`, `OAIQ081S085`, `OAIQ081S089`, `OAIQ081S091`, `OAIQ081S092`, `OAIQ081S093`, `OAIQ081S096` and `OAIQ081S098` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S119`, `OAIQ081S135`, `OAIQ081S136` and `OAIQ081S137`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.naturalKey_eq_iff`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures.card_integer_representative_le_rank`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_stream_runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.local_checker_runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.rejection_scan_runs_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryCostBudgets.actual_key_inventory_le_maxRank`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.controller_run_framed`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.initialize_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.eraseOne_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.naturalKey_eq_iff`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures.card_integer_representative_le_rank`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_stream_runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.local_checker_runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.rejection_scan_runs_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate.attempt_entry_of_query`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryCostBudgets.actual_key_inventory_le_maxRank`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashParameters.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.controller_run_framed`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.initialize_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.eraseOne_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S082
import Definitions.Def_OAIQ081S083
import Definitions.Def_OAIQ081S084
import Definitions.Def_OAIQ081S085
import Definitions.Def_OAIQ081S089
import Definitions.Def_OAIQ081S091
import Definitions.Def_OAIQ081S092
import Definitions.Def_OAIQ081S093
import Definitions.Def_OAIQ081S096
import Definitions.Def_OAIQ081S098

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_Counters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters

open BitProgram CounterPrograms CounterForPrograms

/-- Fixed-width words and their in-range numeric indices are equivalent.
This specification is not a retained list of the enumerated words. -/
def wordEquiv (width : ℕ) : Fin (2 ^ width) ≃ {xs : List Bool // xs.length = width} where
  toFun i := ⟨ExecCNFTupleEnumeration.fixedBits width i, by simp⟩
  invFun xs := ⟨value xs.val, by
    simpa only [xs.property] using ExecCNFTupleOdometer.value_lt_power_length xs.val⟩
  left_inv i := Fin.ext (ExecCNFTupleEnumeration.fixedBits_value width i i.isLt)
  right_inv xs := Subtype.ext (ExecCNFTupleEnumeration.word_eq_of_length_value
    (by simp only [ExecCNFTupleEnumeration.fixedBits_length, xs.property])
    (ExecCNFTupleEnumeration.fixedBits_value width (value xs.val)
      (by simpa only [xs.property] using ExecCNFTupleOdometer.value_lt_power_length xs.val)))

/-- Generic actual increment call on the same finite ports as countdown. -/
def incrementCmd {R S : ℕ} (p : Ports R S) : StructuredCalls.Cmd R S :=
  .call (ProgramLinking.liftProgram (rippleProgram true) p.register (stackPorts p))

noncomputable def incrementResult {R S : ℕ} (p : Ports R S) (d : Data R S) : Data R S :=
  install p d false false (d.regs (p.register 2)) (ripple true (d.stacks p.counter)) []

@[simp] theorem incrementResult_counter {R S : ℕ} (p : Ports R S) (d : Data R S) :
    (incrementResult p d).stacks p.counter = ripple true (d.stacks p.counter) :=
  install_counter p d _ _ _ _ _

@[simp] theorem incrementResult_scratch {R S : ℕ} (p : Ports R S) (d : Data R S) :
    (incrementResult p d).stacks p.scratch = [] := install_scratch p d _ _ _ _ _

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual fixed binary comparison/update used by the streaming selector.
Its queue port is a bounded iterator frame, not a list of candidate records. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open scoped BigOperators

def appended (a : State 8 10) : State 8 10 :=
  let b := Subexp.TupleProgram.pushedState 9 0 false a
  let c := Subexp.TupleProgram.escapedState appendPorts b
  let d := Subexp.TupleProgram.pushedState 9 0 true c
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks 3 d.stacks⟩

@[simp] theorem appended_payload (a : State 8 10) : (appended a).stacks 2 = [] := by
  simp [appended, StackRoutines.clearStacks, appendPorts]

@[simp] theorem appended_score (a : State 8 10) : (appended a).stacks 3 = [] := by
  simp [appended, StackRoutines.clearStacks]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashTrialStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact finite staging extracted from `SqrtLog.LeafOuterNativeStage` for the
space-aware hash pipeline. Semantic query provenance remains in the original
module, while these declarations live in the stronger development's namespace. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
open OAI BitProgram StructuredCalls SqrtLog.LeafOuterProgram
open Subexp

def finalStaged (a : Data) : Data := routesState masterRoutes a
def stageFinalCost (a : Data) : ℕ := routesCost masterRoutes a

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassStaged
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid physical source assembly precedes all marked queries. The candidate
is prepended to a copied history stream; neither retained word is changed.
The temporary source masters are cleared after the complete natural mass. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram LeafOuterProgram
open HashMassAdapter

def cleanup : Cmd 40 896 := BankRoutines.clearCmd 767 0 1 stagedPorts
def cleaned (a : State 40 896) : State 40 896 :=
  ⟨readRegs a.regs 0 1 none, BankRoutines.clearBankStacks stagedPorts a.stacks⟩
def cleanupCost (a : State 40 896) : ℕ :=
  2 * (stagedPorts.map fun i => (a.stacks i).length).sum + 21

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AcceptedQueryStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The accepted query physically receives the saved history, without a trial
candidate prefix. All routing, scratch reset and source reclamation are paid
commands. The query is composed through its actual evaluation and prefix proof. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage

open BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.SqrtLog LeafOuterProgram

def temporaryCleared (a : State 40 896) : State 40 896 :=
  ⟨readRegs a.regs 0 1 none, clearStacks 767 a.stacks⟩

def staged (a : State 40 896) : State 40 896 :=
  LeafOuterNative.finalStaged (temporaryCleared a)

def stageCost (a : State 40 896) : ℕ :=
  2 * (a.stacks 767).length + 3 + LeafOuterNative.stageFinalCost (temporaryCleared a)

def cleaned (a : State 40 896) : State 40 896 :=
  HashMassStaged.cleaned (temporaryCleared a)

def cleanupCost (a : State 40 896) : ℕ :=
  2 * (a.stacks 767).length + 3 + HashMassStaged.cleanupCost (temporaryCleared a)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatures
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# First occurrences of attained keys

The subtype below is a specification of emissions, not a stored family.
The executable scan checks a candidate against its predecessors one at a time.
The key may be an entire integer row-signature; no coordinate projection occurs.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures

variable {N : ℕ} {κ : Type*} (key : Fin N → κ)

/-- Increasing numeric order of little-endian words, equivalently lexicographic
order after reversing the words. The empty head has its unique empty word. -/
def assignmentEquiv (h : ℕ) : Fin (2 ^ h) ≃ (Fin h → Bool) :=
  (Counters.wordEquiv h).trans (Equiv.vectorEquivFin Bool h)

/-- All stored constraint rows occur in this key, with integer arithmetic. -/
def integerKey {d h : ℕ} (A : Fin d → Fin h → ℤ) (i : Fin (2 ^ h)) : Fin d → ℤ :=
  OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSignatureBound.boolSignature A (assignmentEquiv h i)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

def state (regs : Fin 8 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (key : List Bool) : Data :=
  ⟨regs, ![W, [], [], [], [], [], [], [], [], [], [], [], bits, [], key,
    words (rows.map words)]⟩

namespace KeyEquality

open OAI.Algorithms.SubexponentialSAT.SubexpRecordScan

/-- The two compared words and the surrounding frame survive comparison. -/
def command : Cmd 5 6 :=
  .seq (.call (StackRoutines.copyProgram 0 1 4 (0 : Fin 5) 1))
    (.seq (.call (StackRoutines.copyProgram 2 3 4 (0 : Fin 5) 1))
      (.seq (.call compareKeys)
        (.seq (.call (StackRoutines.clearProgram 1 (0 : Fin 5) 1))
          (.call (StackRoutines.clearProgram 3 (0 : Fin 5) 1)))))

def program := compiled command 0 0

end KeyEquality

namespace Rescan

def workState (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor fuel : List Bool)
    (fresh : Bool) (bits key : List Bool) : Data :=
  ⟨regs, ![W, [], [], [], [], [], [], [], [], [], [], [], bits, [], key,
    words (rows.map words), candidate, saved, predecessor, fuel, [], [], [fresh], []]⟩

def countdownPorts : CounterForPrograms.Ports 16 24 where
  register := ⟨![13, 14, 15], by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
  counter := 19
  scratch := 20
  counter_ne_scratch := by decide

def predecessorPorts : CounterForPrograms.Ports 16 24 where
  register := countdownPorts.register
  counter := 18
  scratch := 20
  counter_ne_scratch := by decide

def naturalKey (W : List Bool) (rows : List (List (List Bool))) (h i : ℕ) : List Bool :=
  signatureValue W (ExecCNFTupleEnumeration.fixedBits h i) rows

end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatureRescan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual bounded-word predecessor rescan and its uniform source-prefix storage. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

namespace Rescan

inductive ScanInvariant (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (i : ℕ) (a : Data) : Prop where
  | intro (fuel : List Bool) (hlen : fuel.length = h)
      (hvalue : i + CounterPrograms.value fuel = candidate.val)
      (he : a = workState a.regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
        (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h i) fuel
        (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate i)) [] []) :
      ScanInvariant W rows h candidate i a

inductive Boundary (W : List Bool) (rows : List (List (List Bool))) (h c phase : ℕ)
    (a : Data) : Prop where
  | intro (i : ℕ) (fuel : List Bool) (fresh : Bool) (hi : i ≤ c)
      (hv : i + CounterPrograms.value fuel = c + phase) (hl : fuel.length = h)
      (he : a = workState a.regs W rows (ExecCNFTupleEnumeration.fixedBits h c)
        (naturalKey W rows h c) (ExecCNFTupleEnumeration.fixedBits h i) fuel fresh [] []) :
      Boundary W rows h c phase a

def loopSpace (W : List Bool) (rows : List (List (List Bool))) (h B c : ℕ) : ℕ :=
  max (boundaryBound W (naturalKey W rows h c) rows h +
      bodyBound W (naturalKey W rows h c) rows h B)
    (40 * boundaryBound W (naturalKey W rows h c) rows h + 16)


end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeCandidates
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The retained domain of the code search is one word of two-bit scalars.
The tuple counter visits all four digits; the physical converter rejects the
unused digits and produces the original scalar-frame arithmetic format. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidates

open SubexpEnumerationPayload

def tupleBits (xs : List (Bool × Bool)) : List Bool :=
  Encoding.encodeList digitBits xs

@[simp] theorem tupleBits_length (xs : List (Bool × Bool)) :
    (tupleBits xs).length = 6 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [tupleBits, Encoding.encodeList, digitBits] at *; omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidates
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeCandidateProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed-table conversion of one odometer tuple to one arithmetic candidate.
The input contains only the current candidate. The output is reversed scalar
frames, directly suitable for the existing word and matrix callbacks. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram

open BitProgram CodeCandidates

/-- Retain the first successful current candidate. The callback is actual
fixed native code; it includes all range and mathematical candidate checks. -/
def firstSuccessStep {R S : ℕ} (check : StructuredCalls.Cmd R S)
    (found accepted value present : Fin R) (current selected scratch : Fin S) :
    StructuredCalls.Cmd R S :=
  .ite found (.base .skip)
    (.seq check (.ite accepted
      (.seq (.call (StackRoutines.copyProgram current selected scratch value present))
        (.base (.atom (.set found true)))) (.base .skip)))

/-- Recover the witness flag from its physical stack on every invocation.
The saved tuple is nonempty even for the unique zero-dimensional candidate. -/
def firstSuccess {R S : ℕ} (check : StructuredCalls.Cmd R S)
    (found accepted value present : Fin R) (current selected scratch : Fin S) :
    StructuredCalls.Cmd R S :=
  .seq (.base (.atom (.peek selected value found)))
    (firstSuccessStep check found accepted value present current selected scratch)

def prepareScan {S : ℕ} (p : ScanPorts S) : StructuredCalls.Cmd 16 S :=
  .seq (.call (StackRoutines.copyProgram (p.stack 0) (p.stack 1) (p.stack 3) 0 1)) <|
  .seq (.call (ProgramLinking.liftProgram zeroTupleProgram scanRegisters (scanInitializePorts p))) <|
  .seq (.base (.atom (.set 13 false))) (.base (.atom (.push (p.stack 4) 13)))

/-- Read the actual rejection bit, negate it into the acceptance register,
and clear the current counter with all cleanup charged. -/
def finishScan {S : ℕ} (counter latch : Fin S) : StructuredCalls.Cmd 16 S :=
  .seq (.base (.atom (.pop latch 13 14))) <|
  .seq (.base (.atom (.bnot 15 13)))
    (.call (StackRoutines.clearProgram counter 0 1))

def scanWrapper {S l : ℕ} (p : ScanPorts S) (core : Program 16 S l) : StructuredCalls.Cmd 16 S :=
  .seq (prepareScan p) (.seq (.call core) (finishScan (p.stack 2) (p.stack 4)))


/-- State assertion for preparation, not a free input-construction operation. -/
def scanPreparedStacks {S : ℕ} (p : ScanPorts S) (a : StructuredCalls.State 16 S) :
    Fin S → List Bool :=
  Function.update (Function.update a.stacks (p.stack 2)
    (Encoding.encodeList id (List.replicate (a.stacks (p.stack 0)).length [false, false])))
    (p.stack 4) [false]

def prepareSearch {S : ℕ} (ports : Fin 4 ↪ Fin S) : StructuredCalls.Cmd 16 S :=
  .seq (.call (StackRoutines.copyProgram (ports 0) (ports 1) (ports 3) 0 1))
    (.call (ProgramLinking.liftProgram zeroTupleProgram scanRegisters
      (searchInitializePorts ports)))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical storage operations for the closed parameter setup

All copies, clears, and register resets are fixed instruction sequences or
calls to proved bit programs. Their state transformations below are assertion
notation only. The setup program uses them to isolate dirty arithmetic
subroutines from the persistent parameter words.
-/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem prepare_eval {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S)
    (hp : ∀ p ∈ inputs, p.1 ≠ p.2 ∧ p.1 ≠ tmp ∧ tmp ≠ p.2) :
    Eval (prepare tmp ports inputs) (prepareCost tmp ports inputs a) a
      (prepareState tmp ports inputs a) := by
  exact .seq (clearMany_eval [tmp] a)
    (.seq (clearMany_eval ports (clearManyState [tmp] a))
      (.seq (resetWork_eval (clearManyState ports (clearManyState [tmp] a)))
        (copyMany_eval tmp inputs (beforeCopies tmp ports a) hp
          (beforeCopies_temporary tmp ports a))))

theorem finish_eval {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S)
    (hp : ∀ p ∈ outputs, p.1 ≠ p.2 ∧ p.1 ≠ tmp ∧ tmp ≠ p.2)
    (ht : a.stacks tmp = []) :
    Eval (finish tmp ports outputs) (finishCost ports outputs a) a
      (finishState ports outputs a) := by
  have ht' : (clearManyState (outputs.map Prod.snd) a).stacks tmp = [] := by
    rw [clearMany_stacks, ht]
    split <;> rfl
  exact .seq (clearMany_eval (outputs.map Prod.snd) a)
    (.seq (copyMany_eval tmp outputs (clearManyState (outputs.map Prod.snd) a) hp ht')
      (.seq (clearMany_eval ports (copyManyState outputs (clearManyState (outputs.map Prod.snd) a)))
        (resetWork_eval _)))

/-- Copy/clear overhead is derived from actual instructions around an actual
callee trace. No unproved semantic or timing callback is introduced. -/
theorem isolated_eval {r s l S : ℕ} (p : Program r s l)
    (register : Fin r → Fin 16) (stack : Fin s → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (tmp : Fin S) (ports : List (Fin S))
    (inputs outputs : List (Fin S × Fin S)) (a : Data S) (out : State r s) {t : ℕ}
    (hi : ∀ p ∈ inputs, p.1 ≠ p.2 ∧ p.1 ≠ tmp ∧ tmp ≠ p.2)
    (ho : ∀ p ∈ outputs, p.1 ≠ p.2 ∧ p.1 ≠ tmp ∧ tmp ≠ p.2)
    (hframe : ¬ ∃ j, stack j = tmp)
    (ht : Trace p t
      ((project register stack (prepareState tmp ports inputs a)).withPC (some p.entry))
      (out.withPC none)) :
    let middle := embedState register stack (prepareState tmp ports inputs a) out
    Eval (isolated p register stack tmp ports inputs outputs)
      (prepareCost tmp ports inputs a + (t + finishCost ports outputs middle)) a
      (finishState ports outputs middle) := by
  dsimp only
  have htmp :
      (embedState register stack (prepareState tmp ports inputs a) out).stacks tmp = [] :=
    (embedState_stack_frame register stack _ out tmp hframe).trans
      (prepare_temporary tmp ports inputs a hi)
  exact .seq (prepare_eval tmp ports inputs a hi)
    (.seq (invoke_eval p register stack hr hs _ out ht)
      (finish_eval tmp ports outputs _ ho htmp))

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeChecks
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Space of the concrete sparse-code predicates

The local-code and Walsh predicates are polynomial-time bit programs. These bounds apply
to every candidate, including losing candidates, and every stack in each actual source
prefix. They are intended as the body estimates of bounded-memory enumeration; the
materialized candidate-family programs are not used here.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

def graphCounterPorts : CounterForPrograms.Ports 16 40 where
  register := ⟨Fin.castAdd 13, Fin.castAdd_injective _ _⟩
  counter := 36
  scratch := 38
  counter_ne_scratch := by decide

def localCounterPorts : CounterForPrograms.Ports 16 40 where
  register := ⟨Fin.castAdd 13, Fin.castAdd_injective _ _⟩
  counter := 24
  scratch := 26
  counter_ne_scratch := by decide

def copyConvertCommand {S : ℕ} (ternary : Bool)
    (current input payload scratch : Fin S) : Cmd 16 S :=
  .seq (SubexpSetupStorage.copyCmd current input scratch)
    (.call (ProgramLinking.liftProgram (CodeCandidateProgram.convert ternary)
      (Fin.castAdd 11) ![input, payload]))

/-- The result is a one-bit OR latch, not a retained list of check results. -/
def latchReject (port : Fin 40) : Cmd 16 40 :=
  .seq (.base (.atom (.pop port 13 14))) <|
  .seq (.base (.atom (.bor 13 13 15))) (.base (.atom (.push port 13)))

def graphStreamBody : Cmd 16 40 :=
  .seq (copyConvertCommand false 36 39 34 35) <|
  .ite 4 (SubexpSetupStorage.clearCmd 34)
    (.seq (.call (ProgramLinking.liftProgram graphCallbackProgram id graphStreamStacks))
      (latchReject 37))

def localStreamBody : Cmd 16 40 :=
  .seq (copyConvertCommand true 24 27 22 23) <|
  .ite 4 (SubexpSetupStorage.clearCmd 22)
    (.seq (.call (ProgramLinking.liftProgram callbackProgram id localStreamStacks))
      (latchReject 25))

/-- Staging a current matrix only clears the old matrix and reverses the
converted payload. No list of all test words is copied. -/
def installMatrix {S : ℕ} (payload matrix : Fin S) : Cmd 16 S :=
  .seq (SubexpSetupStorage.clearCmd matrix)
    (.call (StackRoutines.transferProgram payload matrix 0 1))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
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

namespace Guard

def subset : Cmd 13 11 :=
  liftCommand (ExecClauseRelationsProgram.compare 0 1) 8 9 subsetReg subsetStack

end Guard

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SparseCodeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Sparse rows from the candidates actually selected by the search

The construction below consumes the selected shifts and local matrix explicitly. Its
proofs need their checked Walsh and distance properties, not identity with the old
materialized search's selected candidates. The finite list of final rows is polynomial
size and can be retained; lists of all candidates and all test words cannot.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

/-- The iterator may alter its counter and scratch; one Boolean is the only
additional retained result. All other caller stacks have an exact frame. -/
structure RejectionFrame {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (latch : Fin S) (base a : State R S) : Prop where
  frame : ∀ i, i ≠ p.counter → i ≠ p.scratch → i ≠ latch → a.stacks i = base.stacks i
  latch_word : ∃ b : Bool, a.stacks latch = [b]

/-- Intermediate contract for an actual, fixed rejection body. The concrete
local and graph bodies below instantiate this by their native arithmetic traces. -/
structure RejectionBody {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (latch : Fin S) (body : Cmd R S) (dimension budget : ℕ)
    (base : State R S) (reject : ℕ → Bool) : Prop where
  run : ∀ words a, words.map List.length = List.replicate dimension 2 →
    RejectionFrame p latch base a → a.stacks p.counter = Encoding.encodeList id words →
    a.stacks p.scratch = [] →
    ∃ n out, n ≤ budget ∧ Eval body n a out ∧
      out.stacks = Function.update a.stacks latch
        [(a.stacks latch).headD false || reject (CounterPrograms.value words.flatten)]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks



namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

def localChecker : Cmd 16 40 := CodeCandidateProgram.scanWrapper localScanPorts
  (ExecCNFTupleEnumeration.program localCounterPorts localStreamBody)

def graphChecker : Cmd 16 40 := CodeCandidateProgram.scanWrapper graphScanPorts
  (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

structure LocalMatrixReady (t D d : ℕ) (a : MatrixState) : Prop where
  work : ∀ i : Fin 18, a.stacks (Fin.castAdd 30 i) = []
  rows : a.stacks 19 = List.replicate t true
  distance : a.stacks 20 = List.replicate d true
  dimension : a.stacks 21 = List.replicate D true
  payload : a.stacks 22 = []
  scratch : a.stacks 23 = []
  counter : a.stacks 24 = []
  latch : a.stacks 25 = []
  counterScratch : a.stacks 26 = []
  copy : a.stacks 27 = []
  outerInput : a.stacks 43 = []
  outerPayload : a.stacks 44 = []
  outerScratch : a.stacks 45 = []

structure GraphMatrixReady (D r : ℕ) (qbits Dbits : List Bool) (a : MatrixState) : Prop where
  work : ∀ i : Fin 29, a.stacks (Fin.castAdd 19 i) = []
  degree : a.stacks 30 = List.replicate D true
  quotient : a.stacks 31 = qbits
  degreeBits : a.stacks 32 = Dbits
  dimension : a.stacks 33 = List.replicate r true
  payload : a.stacks 34 = []
  scratch : a.stacks 35 = []
  counter : a.stacks 36 = []
  latch : a.stacks 37 = []
  counterScratch : a.stacks 38 = []
  copy : a.stacks 39 = []
  outerInput : a.stacks 43 = []
  outerPayload : a.stacks 44 = []
  outerScratch : a.stacks 45 = []

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramCapture
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Consume the incidence installer's transient metadata while preserving an
explicit raw-scope master outside the selector's48-stack bank. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

def rawLocal (regs : Fin 16 → Bool) (scopes : List Bool) (n k f : ℕ)
    (pairs : List Bool) : State 16 48 :=
  ⟨regs,fun i => if i=32 then scopes else if i=33 then List.replicate n true
    else if i=34 then List.replicate k true else if i=35 then List.replicate f true
    else if i=45 then pairs else []⟩
noncomputable def rawInput (outside : Store) (regs : Fin 16 → Bool)
    (scopes : List Bool) (n k f : ℕ) (pairs : List Bool) : Data :=
  framed outside (rawLocal regs scopes n k f pairs)

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramScale
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed binary-counted copier scales a unary score, preserving both inputs.
The loop count is read from the multiplier stack and every copied bit is paid. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

 theorem scaleInvariant_stable (base : ScaleData) (count : ℕ) :
    SubexponentialSAT.CounterForPrograms.FrameStable scalePorts (scaleInvariant base count) := by
  intro i a b hab ha
  refine ⟨(hab 1 (by decide) (by decide)).symm.trans ha.1,
    (hab 2 (by decide) (by decide)).symm.trans ha.2.1,
    (hab 5 (by decide) (by decide)).symm.trans ha.2.2.1, ?_⟩
  intro j hj2 hj3 hj4
  exact (hab j hj3 hj4).symm.trans (ha.2.2.2 j hj2 hj3 hj4)

 theorem scale_body_spec (base : ScaleData) (count : ℕ) :
    SubexponentialSAT.CounterForPrograms.BodySpec scalePorts (scaleCopy 1 2)
      (scaleInvariant base count) (fun _ => 7*count+5) := by
  intro i d hi hs hv
  let e := SubexponentialSAT.SubexpScanPrimitives.afterCopy d 1 2 0 1
  have he := SubexponentialSAT.SubexpScanPrimitives.copy_eval d 1 2 5 0 1
    (by decide) (by decide) (by decide) (by decide) hi.2.2.1
  refine ⟨7*count+5, e, le_rfl, ?_, ?_, ?_, ?_⟩
  · simpa [scaleCopy, hi.1] using he
  · simp [e, SubexponentialSAT.SubexpScanPrimitives.afterCopy, SubexponentialSAT.StackRoutines.copyStacks, scalePorts]
  · simpa [e, SubexponentialSAT.SubexpScanPrimitives.afterCopy, SubexponentialSAT.StackRoutines.copyStacks, scalePorts] using hs
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [e, SubexponentialSAT.SubexpScanPrimitives.afterCopy, SubexponentialSAT.StackRoutines.copyStacks] using hi.1
    · simp only [e, SubexponentialSAT.SubexpScanPrimitives.afterCopy, SubexponentialSAT.StackRoutines.copyStacks,
        Function.update_self]
      rw [hi.1, hi.2.1, ← List.append_assoc, ← List.replicate_add]
      congr 2
      ring
    · simpa [e, SubexponentialSAT.SubexpScanPrimitives.afterCopy, SubexponentialSAT.StackRoutines.copyStacks] using hi.2.2.1
    · intro j hj2 hj3 hj4
      simpa [e, SubexponentialSAT.SubexpScanPrimitives.afterCopy, SubexponentialSAT.StackRoutines.copyStacks, hj2] using
        hi.2.2.2 j hj2 hj3 hj4

 theorem scaleCommand_eval (d : ScaleData) (count : ℕ)
    (hcount : d.stacks 1 = List.replicate count false)
    (h3 : d.stacks 3 = []) (h4 : d.stacks 4 = []) (h5 : d.stacks 5 = []) :
    ∃ t ≤ scaleBudget (d.stacks 0) count, ∃ e : ScaleData,
      Eval scaleCommand t d e ∧
      e.stacks 2 = List.replicate (SubexponentialSAT.CounterPrograms.value (d.stacks 0)*count) false ++ d.stacks 2 ∧
      (∀ j : Fin 6, j ≠ 2 → e.stacks j = d.stacks j) := by
  let a := SubexponentialSAT.SubexpScanPrimitives.afterCopy d 0 3 0 1
  have hcopy := SubexponentialSAT.SubexpScanPrimitives.copy_eval d 0 3 5 0 1
    (by decide) (by decide) (by decide) (by decide) h5
  have ha3 : a.stacks 3 = d.stacks 0 := by
    simp [a, SubexponentialSAT.SubexpScanPrimitives.afterCopy, SubexponentialSAT.StackRoutines.copyStacks, h3]
  have ha4 : a.stacks scalePorts.scratch = [] := by
    simpa [a, SubexponentialSAT.SubexpScanPrimitives.afterCopy, SubexponentialSAT.StackRoutines.copyStacks, scalePorts] using h4
  have hi : scaleInvariant d count 0 a := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [a, SubexponentialSAT.SubexpScanPrimitives.afterCopy, SubexponentialSAT.StackRoutines.copyStacks] using hcount
    · simp [a, SubexponentialSAT.SubexpScanPrimitives.afterCopy, SubexponentialSAT.StackRoutines.copyStacks]
    · simpa [a, SubexponentialSAT.SubexpScanPrimitives.afterCopy, SubexponentialSAT.StackRoutines.copyStacks] using h5
    · intro j hj2 hj3 hj4
      simp [a, SubexponentialSAT.SubexpScanPrimitives.afterCopy, SubexponentialSAT.StackRoutines.copyStacks, hj3]
  obtain ⟨n, b, hb, hbi, hbv, hbl, hbs, hbn⟩ :=
    SubexponentialSAT.CounterForPrograms.for_correct scalePorts (scaleCopy 1 2)
      (scaleInvariant d count) (fun _ => 7*count+5)
      (scaleInvariant_stable d count) (scale_body_spec d count) a ha4 hi
  let e : ScaleData := ⟨readRegs b.regs 0 1 none, Function.update b.stacks 3 []⟩
  have he : Eval scaleClear (2*(b.stacks 3).length+3) b e :=
    .call _ (SubexponentialSAT.ListRegisterProgram.clear_run 3 0 1 b.regs b.stacks)
  refine ⟨(7*(d.stacks 0).length+5)+(n+(2*(b.stacks 3).length+3)), ?_, e,
    hcopy.seq (hb.seq he), ?_, ?_⟩
  · have hbl' : (b.stacks 3).length = (d.stacks 0).length := by
      simpa only [scalePorts, ha3] using hbl
    have hbn' : n ≤ SubexponentialSAT.CounterPrograms.value (d.stacks 0)*(7*count+5) +
        (SubexponentialSAT.CounterPrograms.value (d.stacks 0)+1)*(16*(d.stacks 0).length+16) := by
      simpa only [scalePorts, ha3, SubexponentialSAT.CounterForPrograms.budgetSum_const] using hbn
    unfold scaleBudget
    omega
  · simpa only [e, Function.update_of_ne (by decide : (2:Fin 6) ≠ 3), scalePorts, ha3] using hbi.2.1
  · intro j hj2
    by_cases hj3 : j = 3
    · subst j; simpa [e] using h3.symm
    by_cases hj4 : j = 4
    · subst j; simpa [e, scalePorts, h4] using hbs
    · simpa [e, hj3] using hbi.2.2.2 j hj2 hj3 hj4

end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramCombine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed two-call score combiner. Inputs are binary weights and canonical
false-unary collision counts. The only modified port is the score accumulator. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

 theorem scale_lifted {R S : ℕ} (register : Fin 3 → Fin R) (stack : Fin 6 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (d : State R S) (count : ℕ)
    (hc : d.stacks (stack 1) = List.replicate count false)
    (h3 : d.stacks (stack 3) = []) (h4 : d.stacks (stack 4) = [])
    (h5 : d.stacks (stack 5) = []) :
    ∃ t ≤ scaleBudget (d.stacks (stack 0)) count+1, ∃ e : State R S,
      Eval (liftCommand scaleCommand 0 2 register stack) t d e ∧
      e.stacks (stack 2) =
        List.replicate (SubexponentialSAT.CounterPrograms.value (d.stacks (stack 0))*count) false ++
          d.stacks (stack 2) ∧
      (∀ j, j ≠ stack 2 → e.stacks j = d.stacks j) := by
  let a := projectState register stack d
  obtain ⟨t, ht, b, hb, ho, hf⟩ := scaleCommand_eval a count hc h3 h4 h5
  refine ⟨t+1, by simpa [a, projectState] using Nat.add_le_add_right ht 1,
    embedState register stack d b,
    eval_liftCommand_from_state _ 0 2 register stack d hr hs hb, ?_, ?_⟩
  · simpa [a, projectState, embedState_stack register stack d b hs 2] using ho
  · intro j hj
    by_cases hm : ∃ i, stack i = j
    · obtain ⟨i, rfl⟩ := hm
      rw [embedState_stack register stack d b hs i]
      exact hf i (fun h => hj (congrArg stack h))
    · exact embedState_stack_frame register stack d b j hm

end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramZipSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact output semantics of the native weighted-stream merger. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Zip
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

 theorem scores_map {A : Type*} (xs : List A) (f g : A → ℕ) (wi wh : List Bool) :
    Streams.scores wi wh (xs.map (fun x => (f x,g x))) =
      xs.map (fun x => SubexponentialSAT.Subexp.UnaryCompare.encode
        (SubexponentialSAT.CounterPrograms.value wi*f x+SubexponentialSAT.CounterPrograms.value wh*g x)) := by
  simp [Streams.scores,Streams.value,SubexponentialSAT.Subexp.UnaryCompare.encode,List.map_map,Function.comp_def]

 theorem scores_reduced {A : Type*} (xs : List A) (f g : A → ℕ)
    (wi wh : List Bool) (n s M r : ℕ)
    (hi : SubexponentialSAT.BinaryArithmetic.toNat wi = n^2*s^2)
    (hh : SubexponentialSAT.BinaryArithmetic.toNat wh = 8*M^2*r^2) :
    Streams.scores wi wh (xs.map (fun x => (f x,g x))) =
      xs.map (fun x => SubexponentialSAT.Subexp.UnaryCompare.encode (reducedScore n s M r (f x) (g x))) := by
  rw [scores_map]
  apply List.map_congr_left
  intro x hx
  rw [SubexponentialSAT.CounterPrograms.value_eq_toNat, SubexponentialSAT.CounterPrograms.value_eq_toNat, hi, hh,
    reducedScore_weights]

end SubexponentialSAT.SqrtLog.PackingProgram.Zip

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingWeightProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingWeightProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- Relocation preserves every unassigned register and every non-output stack,
including arbitrary caller data outside the local port block. -/
theorem command_lifted {R S : ℕ} (register : Fin 8 → Fin R) (stack : Fin 13 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (d : State R S) (hd : ∀ j : Fin 13, 4 ≤ j.val → d.stacks (stack j) = []) :
    ∃ t ≤ 500 * (2 * inputLength (projectState register stack d) + 4)^2 + 1,
    ∃ e : State R S,
      Eval (liftCommand command 0 4 register stack) t d e ∧
      SubexponentialSAT.BinaryArithmetic.toNat (e.stacks (stack 4)) =
        incidence (projectState register stack d) ∧
      SubexponentialSAT.BinaryArithmetic.toNat (e.stacks (stack 5)) =
        head (projectState register stack d) ∧
      (e.stacks (stack 4)).length ≤
        2 * (d.stacks (stack 0)).length + 2 * (d.stacks (stack 1)).length + 3 ∧
      (e.stacks (stack 5)).length ≤
        2 * (d.stacks (stack 2)).length + 2 * (d.stacks (stack 3)).length + 6 ∧
      (∀ j, j ≠ stack 4 → j ≠ stack 5 → e.stacks j = d.stacks j) ∧
      (∀ j, (¬ ∃ i, register i = j) → e.regs j = d.regs j) := by
  let a := projectState register stack d
  obtain ⟨t, ht, b, he, hi, hh, hli, hlh, hf⟩ := command_eval a hd
  refine ⟨t+1, Nat.add_le_add_right ht 1, embedState register stack d b,
    eval_liftCommand_from_state command 0 4 register stack d hr hs he,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [embedState_stack register stack d b hs 4] using hi
  · simpa only [embedState_stack register stack d b hs 5] using hh
  · simpa [a, projectState, embedState_stack register stack d b hs 4] using hli
  · simpa [a, projectState, embedState_stack register stack d b hs 5] using hlh
  · intro j hj4 hj5
    by_cases hm : ∃ i, stack i = j
    · obtain ⟨i, rfl⟩ := hm
      rw [embedState_stack register stack d b hs i]
      exact hf i (fun h => hj4 (congrArg stack h)) (fun h => hj5 (congrArg stack h))
    · exact embedState_stack_frame register stack d b j hm
  · exact fun j hj => embedState_register_frame register stack d b j hj

end SubexponentialSAT.SqrtLog.PackingWeightProgram

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

def initializedStacks (d : Data) (D : ℕ) (exponent : List Bool) : Fin 320 → List Bool :=
  let zero := d.stacks 280
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update d.stacks
      104 zero) 261 zero) 268 exponent)
      277 (Subexp.BlockCopyProgram.copies D zero))
      214 (d.stacks 256)) 257 (d.stacks 256)) 266 (d.stacks 265)

end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramLocal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid cache setup and framing for the lower local Hermite-CRT routine. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Local

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram

def prepared (d : Data) : Data := afterCopy (afterCopy d 277 192 0 1) 243 193 0 1

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Local

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramSerialization
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgram

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.BinaryArithmetic

/-- A scalar word is already its own fixed-width serialization. -/
def wordBlockCode (B : ℕ) (hB : 0 < B) : SubexponentialSAT.StackEncoding.BlockCode (Word B) where
  width := B
  width_pos := hB
  block := Subtype.val
  length_block x := x.property
  injective_block := Subtype.val_injective

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramLess
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed unary comparison with explicit residual-length bounds and paid
cleanup. Register 4 is a caller-owned Boolean saved across this operation. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.CodeSearchProgram

def clearedAt {s : ℕ} (d : State 5 s) (src : Fin s) : State 5 s :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramClip
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed primitive clipping for sparse keys. The key and both unary limits
are disposable inputs; all four local stacks are empty on return. Callers may
keep master copies outside these ports. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev clipState (regs : Fin 5 → Bool) (source t J buffer : List Bool) : State 5 4 :=
  ⟨regs,![source,t,J,buffer]⟩

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Port relocation and paid bit-copy primitives for the dictionary builder. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpRecordScan

def storageCopied (d : StorageData) (src dst : Fin 7) : StorageData :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

def storageCleared (d : StorageData) (src : Fin 7) : StorageData :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks src d.stacks⟩

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramErase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete one-record deletion for sparse coefficient dictionaries. The
selected key is saved before comparison; retained records are emitted intact. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

abbrev eraseData (regs : Fin 5 → Bool) (source query output saved : List Bool) : StorageData :=
  extendStorage (recordState regs source [] query.reverse [] [] output) saved

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-sized dictionary deletion. One fixed loop visits every encoded
record and retains every nonmatching record, reversing record order. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

def eraseReady (regs : Fin 5 → Bool) (entries : List ByteRecord) (query output : List Bool) : StorageData :=
  eraseData (readRegs regs 0 1 (rawEntries entries).head?) (rawEntries entries) query output []

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInputCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One-output physical calls in the assignment-input workspace. -/

namespace SubexponentialSAT.Subexp.AssignmentInputCall

open BitProgram StructuredCalls SubexpSetupStorage

theorem prepare_bound (inputs : List (Fin 48 × Fin 48)) (a : Data) (B : ℕ)
    (hn : inputs.length ≤ 2) (h : Within a B) :
    Within (prepareState 31 work inputs a) (4 * B) ∧
      prepareCost 31 work inputs a ≤ 100 * (B + 1) := by
  obtain ⟨hc, hct⟩ := clearMany_bound [31] a B h
  obtain ⟨hw, hwt⟩ := clearMany_bound work (clearManyState [31] a) B hc
  have hb : Within (beforeCopies 31 work a) B := within_reset _ _ _ hw
  obtain ⟨hi, hit⟩ := copyMany_bound inputs (beforeCopies 31 work a) B hb
  have hpow : 2 ^ inputs.length ≤ 4 := by
    have : inputs.length = 0 ∨ inputs.length = 1 ∨ inputs.length = 2 := by omega
    rcases this with he | he | he <;> simp [he]
  constructor
  · exact within_mono hi (Nat.mul_le_mul_right B hpow)
  · have hlen : work.length = 10 := by simp [work]
    have hit' : copyManyCost inputs (beforeCopies 31 work a) ≤ 2 * (7 * 4 * B + 5) := by
      apply hit.trans
      exact Nat.mul_le_mul hn (by gcongr)
    simp only [List.length_singleton] at hct
    rw [hlen] at hwt
    unfold prepareCost
    nlinarith

theorem finish_bound (q dst : Fin 48) (a : Data) (B : ℕ) (h : Within a B) :
    finishCost work [(q, dst)] a ≤ 60 * (B + 1) := by
  obtain ⟨hc, hct⟩ := clearMany_bound [dst] a B h
  obtain ⟨hp, hpt⟩ := copyMany_bound [(q, dst)] (clearManyState [dst] a) B hc
  have hp' : Within (copyManyState [(q, dst)] (clearManyState [dst] a)) (2 * B) := by
    simpa using hp
  have hwt := (clearMany_bound work _ (2 * B) hp').2
  have hlen : work.length = 10 := by simp [work]
  rw [hlen] at hwt
  simp only [List.length_singleton, pow_one, Nat.one_mul] at hct hpt
  unfold finishCost
  simp only [List.map_cons, List.map_nil]
  nlinarith

end SubexponentialSAT.Subexp.AssignmentInputCall

end OAI.Algorithms
end


