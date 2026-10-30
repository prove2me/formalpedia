-- Prove2me | Definitions.Def_OAIQ081S179
-- name    : OAIQ081S179
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:30:50.44849+00:00
-- url     : https://prove2.me/theorems/9784fb65-ede5-4258-b251-54ad8a8c808f
-- title:
--   Definitions bundle OAIQ081S179 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 9 definitions. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad.result`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds.keyEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds.matrixEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.localWork`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.workSize`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepare.resetCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepare.resetState`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLogSpace_QueryVisitorCorrect`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorCorrect.lean), [`SubexponentialSAT_SqrtLogSpace_QueryVisitorLoad`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorLoad.lean), [`SubexponentialSAT_SqrtLogSpace_QueryVisitorLoadBounds`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorLoadBounds.lean), [`SubexponentialSAT_SqrtLogSpace_ReconstructionNative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/ReconstructionNative.lean), [`SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureHeadLoader.lean), [`SubexponentialSAT_SqrtLogSpace_SignatureHeadPrepare`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureHeadPrepare.lean).
--
--   **Imports.** It imports the bundles `OAIQ081S165`, `OAIQ081S168`, `OAIQ081S169` and `OAIQ081S171` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ081S185`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadLoaderBudgets.leafWork_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.loader_caps`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds.generated_bounds`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad.result_mask_count`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad.result_mask_length`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad.result_mask_word` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.run_space`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadLoaderBudgets.leafWork_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.loader_caps`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstructionReplay.prepare_avoids`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.run_space_with_full_frame`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds.generated_bounds`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad.result_mask_count`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad.result_mask_length`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad.result_mask_word` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.run_space`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ081S165
import Definitions.Def_OAIQ081S168
import Definitions.Def_OAIQ081S169
import Definitions.Def_OAIQ081S171

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid setup for one visited signature head. The physical key workspace,
old master words and selector outputs are cleared by the command itself. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepare

open BitProgram StructuredCalls StackRoutines
open HighQueryAdapter QueryTupleVisitor
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

def resetState (a : State 40 896) : State 40 896 :=
  ⟨readRegs a.regs 0 1 none, BankRoutines.clearBankStacks cleared a.stacks⟩

def resetCost (a : State 40 896) : ℕ :=
  2 * (a.stacks 841).length + 3 +
    (2 * (cleared.map (fun i => ((clearStacks 841 a.stacks) i).length)).sum + 45)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepare
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Correctness of the fixed concrete two-pass visitor. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram
open OAI BitProgram StructuredCalls
abbrev Data := State 40 896

open OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram
open QueryTupleState QueryTupleVisitor SignatureTupleProgram SubexpSetupStorage

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The concrete head-loader is specialized to actual node bootstrap data.
All physical entry contracts are discharged by the native cache producer. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

/-- The coarse resource polynomial keeps the complete raw row count and the
actual per-column budget; its degree is independent of the input. -/
def localWork (s : Native.Inputs) (z A : ℕ) : ℕ :=
  let size := Bounds.preparationSize s.n s.N s.rows s.low (s.Q*s.r) z
  let matrix := LayoutMatrixProgram.commandCost s.columnTime s.columnLength s.D s.n
    (selectedHeads s.n s.rows s.low z)+1
  let live := A+5*size^2+matrix
  let shift := 10000*(s.D+1)*(s.n+1)*(live+s.columnLength+1)^2
  100000*(A+size^3+1)+(matrix+1878*(live+1))+
    (shift+147*(live+shift+1))+(2*(live+shift)+3)

/-- Scalar sum used only for a fixed-degree resource envelope. -/
def workSize (s : Native.Inputs) (z A : ℕ) : ℕ :=
  A+Bounds.preparationSize s.n s.N s.rows s.low (s.Q*s.r) z+
    s.columnTime+s.columnLength+s.D+s.n+2

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorLoad
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid reverse-head reload for the two-pass query visitor. The same native
run returns every integer row, preserves the suspended query data, and restores
a fixed retained word cap before the next head. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
/-- The physical result of that one concrete head loader. -/
def result (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    State 40 896 :=
  SignatureHeadLoader.leafOutputFrom 843 frame
    (SignatureHeadLoader.localResult (SignatureHeadLoader.leafInputFrom 843 frame)
      rp rm rs s.n s.N (s.Q*s.r) z s.rows s.low raw shifted)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorLoadBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Source-parameter bounds for the full key produced from an actual shifted
incidence matrix. Every incidence row and every retained coefficient is charged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

/-- The same physical matrix envelope specialized to the actual native input. -/
def matrixEnvelope (s : LeafHeadSetupProgram.Native.Inputs) (L : ℕ) : ℕ :=
  matrixBound s.n s.D s.columnLength L

def keyEnvelope (s : LeafHeadSetupProgram.Native.Inputs) (L : ℕ) : ℕ :=
  let R := matrixEnvelope s L
  16*(L+s.n+R)+7*R+
    s.D*(BucketProgram.signatureRowBound (List.replicate L false) s.n R+2)+9


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_ReconstructionNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! One concrete lower-workspace recovery tail: native Hermite reconstruction,
canonical complete binary readback, and paid cache reclamation. All retained
caller stacks enter its local prefix bound; the endpoint changes only count323.
The physical jet and semantic target hypotheses must be produced by the query. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog
open DensePolynomialProgram
open LeafProgram.Count

def program := compiled command 256 323

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative
end


