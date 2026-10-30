-- Prove2me | Definitions.Def_OAIQ081S151
-- name    : OAIQ081S151
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:55:15.286708+00:00
-- url     : https://prove2.me/theorems/294913b3-ac92-4af2-b56a-11159507fd77
-- title:
--   Definitions bundle OAIQ081S151 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 100 declarations of OpenAI's Lean: 79 definitions, 5 inductive types or structures and 16 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.LowInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.nativeStored`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.outputStored`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.outputWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.scanRecords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.sourceWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.finish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.nextValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.popChoice`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.prepareInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.runValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.selected`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.stepValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.executionCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.literalBytes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.loadBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.totalBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram.decoded`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop.Raw`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.oneEntries`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.specializedRowPayload`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.liftInner`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.tableRecord`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.tableResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution.attemptBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution.stagedAttemptBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyStagedSpace.attemptSpace`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn.cost`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn.result`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn.upperCleared`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn.upperCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.ReferencesReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.finishedStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.massBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.read`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.workspace` and 44 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_FactorAssignmentLoop`, `SubexponentialSAT_SqrtLogSpace_FactorCacheProgram`, `SubexponentialSAT_SqrtLogSpace_FactorTablePayloadMeaning`, `SubexponentialSAT_SqrtLogSpace_FactorTableProgram`, `SubexponentialSAT_SqrtLogSpace_HashGreedyExecution`, `SubexponentialSAT_SqrtLogSpace_HashGreedyStagedSpace`, `SubexponentialSAT_SqrtLogSpace_HashMarkedReturn`, `SubexponentialSAT_SqrtLogSpace_HashMassAdapter`, `SubexponentialSAT_SqrtLogSpace_HashMassStaged`, `SubexponentialSAT_SqrtLogSpace_HashMassStagedSpace`, `SubexponentialSAT_SqrtLogSpace_HeadSumAssembly`, `SubexponentialSAT_SqrtLogSpace_HeadSumProgram`, `SubexponentialSAT_SqrtLogSpace_HighCountInit`, `SubexponentialSAT_SqrtLogSpace_HighCountSeed`, `SubexponentialSAT_SqrtLogSpace_HighMarkedCleanup`, `SubexponentialSAT_SqrtLogSpace_HighQueryAdapter`, `SubexponentialSAT_SqrtLogSpace_QueryIncidenceSpace`, `SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyInput`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyNativeLiteral`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyStored`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyStoredBytes`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyStoredNative`, `SubexponentialSAT_SqrtLog_PerturbationBetaProgram`, `SubexponentialSAT_SqrtLog_PerturbationBetaProgramRun`, `SubexponentialSAT_SqrtLog_PerturbationBetaProgramSelected`, `SubexponentialSAT_SqrtLog_PerturbationBetaProgramStep`, `SubexponentialSAT_SqrtLog_PolynomialExecutorProgramBounds`, `SubexponentialSAT_SqrtLog_PolynomialExecutorProgramContext`, `SubexponentialSAT_SqrtLog_PolynomialExecutorProgramCost`, `SubexponentialSAT_SqrtLog_SquarefreeKeyMapProgram`, `SubexponentialSAT_SqrtLog_SquarefreeScaleProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S116`, `OAIQ081S118`, `OAIQ081S119`, `OAIQ081S120`, `OAIQ081S125`, `OAIQ081S126`, `OAIQ081S128`, `OAIQ081S132`, `OAIQ081S135` and `OAIQ081S136` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S162`, `OAIQ081S163` and `OAIQ081S165`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace.accumulate_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRun.staged_boundary_attempt`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyStagedSpace.attempt_halt_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn.cost_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn.trace_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.finish_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.mass_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.references_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace.collector_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace.mass_halt_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStagedSpace.command_halt_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged.eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryShadow.marked_shadow_bound_of_references`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace.accumulate_return_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.accumulate_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.finalize_prefix`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace.seed_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.product_dense`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.product_work_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness.model_ready_of_low_agreement`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.evaluateModel_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRowWith_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_relSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.nativeStored_fixed_rows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.add_implements`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.load_implements`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.model_flat_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.mul_implements` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.program_run`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.hashWork_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.indicatorBudget_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.markedWork_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.result_good`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace.accumulate_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRun.staged_boundary_attempt`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyStagedSpace.attempt_halt_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.finish_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.mass_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.references_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace.collector_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace.mass_halt_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStagedSpace.command_halt_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged.eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryShadow.marked_shadow_bound_of_references`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySpace.clear_bank_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleReadoutSemantics.grouped_dense_query_emitted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.product_dense`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.product_work_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.prepared_denote`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.shiftU_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness.model_ready_of_low_agreement`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.evaluateModel_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRowWith_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_relSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.clause_denote_scoped`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.row_fold_denote_scoped`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.keyPhase_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.nativeStored_fixed_rows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.add_implements`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.load_implements`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.model_flat_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.mul_implements` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.program_run`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S116
import Definitions.Def_OAIQ081S118
import Definitions.Def_OAIQ081S119
import Definitions.Def_OAIQ081S120
import Definitions.Def_OAIQ081S125
import Definitions.Def_OAIQ081S126
import Definitions.Def_OAIQ081S128
import Definitions.Def_OAIQ081S132
import Definitions.Def_OAIQ081S135
import Definitions.Def_OAIQ081S136

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeKeyMapProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def ready {n : ℕ} (regs : Fin 8 → Bool) (a : Index (Fin n)) (t J : ℕ)
    (entries : List (Entry n)) (output : List Bool) : Data :=
  state (readRegs regs 0 1 (Program.rawEntries (encoded entries)).head?)
    (idle (environment a t J) (Program.rawEntries (encoded entries)) output)

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

/-! Public native sparse-key mapper. The instruction table is independent of
the keys, clipping limits, coefficient width, and dictionary length. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeScaleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Base stage. -/
/-! Fixed physical ABI for scaling all coefficients in a sparse dictionary.
The low 32 stacks are the common coefficient-ring service. The eight high
stacks hold source, reversed output, scalar, key, coefficient staging, frame
staging, final output, and a preserved copy of the unary degree. -/

/-! Moves stage. -/

/-! Emit stage. -/

/-! Native stage. -/

/-! Loop stage. -/

/-! Cost stage. -/

/-! Semantics stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open scoped BigOperators

variable {K V R : Type*} [DecidableEq V] [CommRing R]

def decoded (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (entries : List (K × RingProgram.Code (Word (baseWidth p t)) d)) : List (K × R) :=
  entries.map (fun a => (a.1, RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis a.2))

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source-sensitive costs and validity of the generic coefficient-array
interpreter, independently of its native arithmetic implementation. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT

def loadBound (B d J : ℕ) (P : List (Coeff B d)) : ℕ :=
  12*(DensePolynomialProgram.encode P).length + 16*(J*(d*B)) + 46

def executionCost {B d : ℕ} (Ka Km W : ℕ) : Algorithm.Expr (List (Coeff B d)) → ℕ
  | .lit P => 23*(DensePolynomialProgram.encode P).length + 16*W + 63
  | .add e f => executionCost Ka Km W e + executionCost Ka Km W f + 14 + Ka
  | .mul e f => executionCost Ka Km W e + executionCost Ka Km W f + 14 + Km

def literalBytes {B d : ℕ} : Algorithm.Expr (List (Coeff B d)) → ℕ
  | .lit P => (DensePolynomialProgram.encode P).length
  | .add e f => literalBytes e + literalBytes f
  | .mul e f => literalBytes e + literalBytes f

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial bit bounds for the fixed source interpreter. Source size and
raw literal bytes are charged separately from the retained coefficient count. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram


def totalBudget {B d : ℕ} (J : ℕ) (e : SubexponentialSAT.Algorithm.Expr (List (Coeff B d))) : ℕ :=
  300000*(e.size + literalBytes e + 1)*(J+1)^3*(d+1)^3*(B+1)^2


end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramContext
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Persistent native arithmetic context for the source-row postfix machine.
The dispatcher owns26/27/28; neither coefficient-array service touches them. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (contextStore physicalCfg)
open SubexponentialSAT.SubexpRowPostfixContext (operandStore preparedStore )

structure Ready (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (ops : SubexpSymbolicCost.RingProgram (DensePolynomialProgram.Coeff (baseWidth p t) d))
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (J : ℕ)
    (width : List Bool) (frame : Fin 6 → List Bool) (context : Fin 252 → List Bool) : Prop where
  arithmetic : DensePolynomialProgram.PairSpec.BaseReady p t M cache table (contextStore context) width frame
  empty21 : contextStore context 21 = []
  empty99 : contextStore context 99 = []
  empty121 : contextStore context 121 = []
  empty122 : contextStore context 122 = []
  empty240 : contextStore context 240 = []
  empty241 : contextStore context 241 = []
  empty244 : contextStore context 244 = []
  empty245 : contextStore context 245 = []
  buffers : ∀ i, contextStore context (bufferPorts i) = []
  zeroArray : contextStore context 192 = DensePolynomialProgram.encode (List.replicate J ops.zeroRun.1)
  dimension : (contextStore context 193).length = J
  loaderShape : contextStore context 242 = DensePolynomialProgram.encode (List.replicate J ops.zeroRun.1)

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native beta evaluation.  The caller supplies actual coefficient arrays,
not evaluated row values.  Masters205..212 are preserved;220 is the result.
Work230/231/232 holds the framed row scan, choice scan and reverse buffer. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives

def popChoice : Code := .base (.atom (.pop 231 0 1))

/-- Evaluate the current actual row, then add it to the existing beta. -/
def selected : Code :=
  .seq (copy 207 240) (.seq (copy 210 248)
    (.seq HornerProgram.modelCommand (.seq (copy 220 241)
      (.seq (CRTLocalProgram.binaryStep HornerProgram.Services.add)
        (.seq (clear 241) (.seq (clear 220)
          (SubexpPolynomialConstructor.move 240 220)))))))

def prepareInput : Code := .seq (copy 205 230) (.seq (copy 206 231)
  (.seq (copy 207 220) (.seq (copy 209 247) (copy 211 250))))
def finish : Code := .seq (clear 230) (.seq (clear 231)
  (.seq (clear 247) (clear 250)))

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgramSelected
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One selected coefficient row is evaluated by the actual Horner command
and accumulated by the actual extension-ring addition service. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives SubexpLiftRing SubexpQuarticRing
open CRTLocalProgram (LowFrame lowFrame_update lowFrame_refl)

def nextValue (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (P : List (RingProgram.Code (RingProgram.ScalarCode 3 t) d))
    (theta acc : RingProgram.Code (RingProgram.ScalarCode 3 t) d) :=
  ((RingProgram.modelProgram t a M cache).addRun
    (HornerProgram.modelValue t a M cache P theta) acc).1

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgramStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives SubexpLiftRing SubexpQuarticRing
open CRTLocalProgram (LowFrame lowFrame_update lowFrame_refl)

def stepValue (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (theta acc : Coeff t d) (row : List (Coeff t d) × Bool) : Coeff t d :=
  if row.2 then nextValue t a M cache row.1 theta acc else acc

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed native beta scan from preserved row/choice masters. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives SubexpLiftRing SubexpQuarticRing
open CRTLocalProgram (LowFrame lowFrame_update lowFrame_refl)

def runValue (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (theta : Coeff t d) (rows : List (List (Coeff t d) × Bool)) : Coeff t d :=
  rows.foldl (stepValue t a M cache theta) (RingProgram.modelProgram t a M cache).zeroRun.1

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Input-only contract for the closed native low-variable worker. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- This record describes only the actual incoming words, arithmetic caches,
and empty work tapes. It contains no evaluation or execution oracle. -/
structure LowInput (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) (s : Store) : Prop where
  widthPositive : 0 < baseWidth 3 t
  zeroCanonical : BinaryArithmetic.toNat cache.zero.val < 3^t
  pairReady : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache) s (s 10) (fun _=>[])
  scalarReady : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache) s
  buffersEmpty : ∀ i,s (bufferPorts i)=[]
  empty121 : s 121=[]
  empty122 : s 122=[]
  zeroBits : RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1=
    List.replicate (d*baseWidth 3 t) false
  sourceRows : s 205=Encoding.encodeList Fixed.encode (rows.map Prod.fst)
  choices : s 206=rows.map Prod.snd
  zeroWord : s 207=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1
  oneWord : s 208=RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1
  thetaWord : s 209=RingProgram.flat theta
  sourceCount : (s 210).length=N
  wordWidth : (s 211).length=d*baseWidth 3 t
  ambientCount : (s 212).length=rows.length
  targetCount : s 213=List.replicate J true
  widthZeros : s 104=List.replicate (d*baseWidth 3 t) false
  workEmpty : ∀ i∈lowScratch,s i=[]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyNativeLiteral
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native source-to-literal composition. The source premise is the execution
of one fixed finite source command; all beta, shift, and emission services are
fully discharged by LowInput.run. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def sourceWords {B d N : ℕ} (rows : List (Fixed.Array B d N × Bool)) : List Bool :=
  Encoding.encodeList Fixed.encode (rows.map Prod.fst)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorCacheProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical reconstruction of the exact node caches, including the sparse
ring identity and ambient shape, before accepted assignment evaluation. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram

open OAI BitProgram StructuredCalls SubexpSetupStorage
open SqrtLog SqrtLog.LeafProgram

def oneEntries {n B d : ℕ} (one : RingProgram.Code (SubexpQuarticRing.Word B) d) :
    List (MomentsProgram.Product.Entry n B d) := [(Squarefree.Index.origin, one)]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native arithmetic after immediate Boolean specialization

The existing finite sparse-product program is used with empty formal support.
Its keys still carry the ambient input coordinate type; this does not compress
the declared variables. There are at most `u * J` retained entries, including
zero cutoffs. Polynomial local time therefore bounds all its source prefixes,
including the table, inputs, output, normalization copies and arithmetic scratch.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram

open scoped BigOperators
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram BitProgram

/- The two fields coincide with LeafProgram.NativeSemantics.Good. The
arithmetic layer states them transparently to avoid importing the factor
interpreter. Conversion in either direction supplies `valid` and `nodup`.
The proof bodies below are the original finite-program validity arguments. -/
section NativeValidity
structure Good {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (a : List (Product.Entry n B d)) : Prop where
  valid : ∀ x ∈ a, Product.ValidKey vars u J x.1
  nodup : (Squarefree.Sparse.keys a).Nodup


end NativeValidity

variable {V R : Type*} [DecidableEq V] [CommRing R]

noncomputable section

noncomputable def rawDenote {R : Type*} [CommRing R] {n B d : ℕ}
    (f : RingProgram.Code (Word B) d → R) (a : List (Product.Entry n B d)) :
    Squarefree.Jet (Fin n) R := Squarefree.Sparse.denote (Dictionary.denoteTable f a)


/-- Decode an actual finite native dictionary into the dense ring. -/
def rawValue {n B d : ℕ} (u J : ℕ)
    (f : RingProgram.Code (Word B) d → R) (a : List (Product.Entry n B d)) : Dense R u J :=
  jetProjection u J (rawDenote f a)

@[simp] theorem rawValue_nil {n B d : ℕ} (u J : ℕ)
    (f : RingProgram.Code (Word B) d → R) : rawValue (n := n) u J f [] = 0 := by
  simp [rawValue, rawDenote, Dictionary.denoteTable, Squarefree.Sparse.denote,
    Squarefree.Sparse.decode]

end

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual selected-factor table runs over ambient variable IDs. Each low
payload is specialized immediately before its framed table entry is retained.
The source scratch embedding excludes persistent layout masters. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives
open SubexpPolynomialConstructor PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

def liftInner (code : Cmd 16 256) : OuterCode :=
  liftCommand code 0 0 id innerPort

def tableRecord (payload : ℕ → List Bool) (j : ℕ) : List Bool :=
  Encoding.frame (Encoding.encodeNat j) ++ Encoding.frame (payload j)

def tableResult (payload : ℕ → List Bool) : ℕ → List Bool → List Bool
  | 0,acc => acc
  | n+1,acc => tableResult payload n (tableRecord payload n ++ acc)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Relational execution of the fixed specialized factor-record loop. This
adapts the original FactorLoop reader/while proof to the shared 896-stack ABI
and empty-support dictionaries. The explicit callback premise must be proved
for the actual callback before this component can close an algorithm endpoint. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop
attribute [local simp] Fin.coe_ofNat_eq_mod
open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram MomentsProgram

abbrev Raw (n B d : ℕ) := List (Product.Entry n B d)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyStored
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual fixed-array Horner output is already valid Stored data.
The native order is reversed and zero coefficients are deliberately kept. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT.SubexpSymbolicCost
open DensePolynomialProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree PerturbationProgram

variable {B d n : ℕ} {R : Type*} [CommRing R]

def outputWords (ops : RingProgram (Coeff B d)) (J : ℕ)
    (theta beta : Coeff B d) (rows : Fin n → List (Coeff B d)) :
    List (Index (Fin n) × Coeff B d) :=
  rawWords beta (fun v => (shiftedValue ops J theta (rows v)).val.tail)

theorem outputWords_nodup (ops : RingProgram (Coeff B d)) (J : ℕ)
    (theta beta : Coeff B d) (rows : Fin n → List (Coeff B d)) :
    ((outputWords ops J theta beta rows).map Prod.fst).Nodup :=
  rawWords_nodup _ _

theorem shifted_tail_length (ops : RingProgram (Coeff B d))
    (J : ℕ) (hJ : 0 < J) (theta : Coeff B d) (p : List (Coeff B d)) :
    (shiftedValue ops J theta p).val.tail.length < J := by
  rw [List.length_tail,(shiftedValue ops J theta p).property]
  omega

theorem outputWords_valid (ops : RepresentedRing (Coeff B d) R)
    (t J : ℕ) (ht : 0 < t) (hJ : 0 < J)
    (theta beta : Coeff B d) (rows : Fin n → List (Coeff B d)) :
    Sparse.ValidData Finset.univ t J
      (decodeRecords ops (outputWords ops.program J theta beta rows)) :=
  rawWords_valid ops t J ht hJ beta _
    (fun v => shifted_tail_length ops.program J hJ theta (rows v))

def outputStored (ops : RepresentedRing (Coeff B d) R)
    (t J : ℕ) (ht : 0 < t) (hJ : 0 < J)
    (theta beta : Coeff B d) (rows : Fin n → List (Coeff B d)) :
    Moments.Stored (R:=R) (Finset.univ : Finset (Fin n)) t J where
  data := decodeRecords ops (outputWords ops.program J theta beta rows)
  valid := outputWords_valid ops t J ht hJ theta beta rows
  nodup := by
    simpa [Sparse.keys,decodeRecords,List.map_map,Function.comp_def] using
      outputWords_nodup ops.program J theta beta rows

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyStoredBytes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact byte order of the physical row scan. No sparse normalization or
deletion of zero coefficient records is used by this bridge. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT
open SubexponentialSAT.SubexpSymbolicCost
open DensePolynomialProgram _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree PerturbationProgram

def scanRecords {B d : ℕ} (ops : RingProgram (Coeff B d)) (J n N : ℕ)
    (theta : Coeff B d) (j : ℕ) (rows : List (Fixed.Array B d N)) :
    List (Index (Fin n) × Coeff B d) :=
  (rows.zipIdx j).flatMap fun p =>
    if hi : p.2 < n then coefficientRecords ⟨p.2,hi⟩ 1
      (shiftedValue ops J theta p.1.val).val.tail else []

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryIncidenceSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram
open scoped BigOperators

def emittedSource (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : DensePolynomialProgram.Coeff (baseWidth 3 t) d)
    (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 t) d N × Bool)) :
    List (Product.Entry rows.length (baseWidth 3 t) d) :=
  PerturbationAssembly.outputWords (RingProgram.modelProgram t model M cache) J theta
    (PerturbationBetaProgram.runValue t model M cache theta (PerturbationAssembly.pairedRows rows))
    (fun v : Fin rows.length => rows[v].1.val)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTablePayloadMeaning
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The unchanged actual specialized payload and its source witness predicate.
Execution and resource theorems remain in FactorTableNative. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram
open PerturbationAssembly LayoutProgram DensePolynomialProgram
open OAI.Algorithms.SubexponentialSAT.Subexp OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes

def specializedRowPayload (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d)
    (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 t) d N × Bool))
    (mask : List Bool) : List Bool :=
  MomentsProgram.Product.bytes (MomentsProgram.Normalize.run 3 t M cache
    (HeadEvaluation.specializeEntries (Squarefree.decodeMask rows.length mask)
      (QueryProducerSpace.emittedSource t model M cache J N theta rows)) [])

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual marked-clause collector generalized to the frozen 40/896 leaf
bank. Its parser and adder are the original measured finite programs. All
marked queries are executed; their integer results are added before argmin.
The temporary query execution premise must be discharged by the concrete
optional-mark evaluator, including its high-assignment loop and cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram

def workspace (a : Data) : Fin 891 → List Bool := fun i => a.stacks (workPort i)
def read (a : Data) : List Bool := a.stacks 322

structure Ready (ready : (Fin 891 → List Bool) → Prop) (a : Data) : Prop where
  workspace_ready : ready (workspace a)
  result_empty : a.stacks 323 = []
  scratch_empty : a.stacks 324 = []

variable {X Row : Type*} [Fintype X] {m : ℕ}

def finishedStacks (a : Data) : Fin 896 → List Bool :=
  Function.update (Function.update a.stacks 322 []) 769
    (DisjointReuse.binaryNat (BinaryArithmetic.toNat (a.stacks 322)))


open LeafOuterProgram

structure ReferencesReady (a : Data) : Prop where
  scratch : a.stacks 767 = []
  empty : ∀ i : Fin 896, i.val < 9 ∨ i = 320 → a.stacks i = []

open scoped BigOperators

def massBudget (a : Data) (queryCost width : List Bool → ℕ) (m : ℕ) : ℕ :=
  routeCost (782,0) a + LeafOuterNative.References.budget (a.stacks 782) + 1 +
    (valueBudget queryCost width (RowSelectionProgram.Index.alphabet m) [] +
      50 * (outputGrowth width (RowSelectionProgram.Index.alphabet m) + (a.stacks 769).length + 1))


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter
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

def budget (a : State 40 896) (queryCost width : List Bool → ℕ) (m : ℕ) : ℕ :=
  stagingBudget a + massBudget a queryCost width m

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual candidate attempt is the fixed normalizer, all-clause mass
collector, and paid fixed-width padding. The only remaining query execution
premise is the concrete per-mark evaluator, including its exact caller frame. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashMassAdapter

def attemptBudget (a : State 40 896) (n m depth : ℕ) (queryCost : List Bool → ℕ) : ℕ :=
  HashCandidateProgram.Leaf.budget m depth +
    (massBudget a queryCost (fun _ => n + 1) m + (23 * HashSelect.loopCap n m + 20))

def stagedAttemptBudget (a : State 40 896) (n m depth : ℕ)
    (queryCost : List Bool → ℕ) (L : ℕ) : ℕ :=
  attemptBudget a n m depth queryCost + 95 * L + 103

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete per-high-assignment setup and compressed head overlays.
The routines read physical counter/mask words and preserve ambient coordinates. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

noncomputable def highResult (a : Data) (regs : Fin 4 → Bool) (high : List Bool) : Data :=
  embedState highRegs highStacks a (LeafHighContextProgram.Local.state regs
    (a.stacks 330) (a.stacks 338) (a.stacks 338).reverse
    (Restriction.zeroMerge (a.stacks 338) high).reverse [] [] [] [] [] [])

@[simp] theorem highResult_mask (a : Data) (regs : Fin 4 → Bool) (high : List Bool) :
    (highResult a regs high).stacks 702 = (a.stacks 338).reverse :=
  embedState_stack highRegs highStacks a _ (by decide) 2

@[simp] theorem highResult_bits (a : Data) (regs : Fin 4 → Bool) (high : List Bool) :
    (highResult a regs high).stacks 703 =
      (Restriction.zeroMerge (a.stacks 338) high).reverse :=
  embedState_stack highRegs highStacks a _ (by decide) 3

namespace HeadSelect
open OAI.Algorithms.SubexponentialSAT.StackRoutines

def state (regs : Fin 4 → Bool) (mask bits rev out ones : List Bool) : Data :=
  ⟨regs,![mask,bits,rev,out,ones]⟩

end HeadSelect

namespace NativeHeadSelect
open OAI.Algorithms.SubexponentialSAT.StackRoutines

def copied (a : Data) : Data :=
  ⟨readRegs (readRegs a.regs 0 1 none) 0 1 none,
    copyStacks 670 879 (copyStacks 858 878 a.stacks)⟩

noncomputable def result (a : Data) (rf : Fin 4 → Bool) : Data :=
  embedState regs stackMap (copied a) (HeadSelect.state rf [] [] []
    (Restriction.selected true (a.stacks 670) (a.stacks 858))
    (List.replicate (Restriction.highCount (a.stacks 670)) true))

@[simp] theorem result_E (a : Data) (rf : Fin 4 → Bool) :
    (result a rf).stacks 867 = Restriction.selected true (a.stacks 670) (a.stacks 858) :=
  embedState_stack regs stackMap (copied a) _ (by decide) 3

@[simp] theorem result_H (a : Data) (rf : Fin 4 → Bool) :
    (result a rf).stacks 868 = List.replicate (Restriction.highCount (a.stacks 670)) true :=
  embedState_stack regs stackMap (copied a) _ (by decide) 4

end NativeHeadSelect

/-- A callback is entered only under a true iterator guard; restoring that
known control bit is an actual source instruction after conditioned readback. -/
def restoreHighGuard : Code := .base (.atom (.set 21 true))

open OAI.Algorithms.SubexponentialSAT.StackRoutines

def copiedHighCounter (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,Function.update (Function.update a.stacks 330 (a.stacks 789)) 792 []⟩

@[simp] theorem copiedHighCounter_word (a : Data) :
    (copiedHighCounter a).stacks 330=a.stacks 789 := by simp [copiedHighCounter]

namespace CanonicalHigh
open DisjointReuse

noncomputable def result (a : Data) : Data := embedState regMap stackMap a
  (CanonicalWordProgram.state CanonicalWordProgram.zeroRegs
    (binaryNat (CounterPrograms.value (a.stacks 788))) [])

@[simp] theorem result_count (a : Data) : (result a).stacks 788=
    countWord (BinaryArithmetic.toNat (a.stacks 788)) := by
  change (result a).stacks (stackMap 0) =
    countWord (BinaryArithmetic.toNat (a.stacks 788))
  have h := embedState_stack regMap stackMap a
    (CanonicalWordProgram.state CanonicalWordProgram.zeroRegs
      (binaryNat (CounterPrograms.value (a.stacks 788))) []) (by decide) 0
  simpa [result, CanonicalWordProgram.state,
    CounterPrograms.value_eq_toNat, binaryNat, countWord] using h

open OAI.Algorithms.SubexponentialSAT.StackRoutines

def resetState (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,clearStacks 794 (clearStacks 793 a.stacks)⟩

@[simp] theorem final_count (a : Data) : (result (resetState a)).stacks 788=
    countWord (BinaryArithmetic.toNat (a.stacks 788)) := by
  rw [result_count]
  simp [resetState,clearStacks]

end CanonicalHigh

namespace Overlay
open OAI.Algorithms.SubexponentialSAT.StackRoutines

def state (regs : Fin 8 → Bool) (bits mask baseline u v x y z tmp full out low : List Bool) : Data :=
  ⟨regs,![bits,mask,baseline,u,v,x,y,z,tmp,full,out,low]⟩

def copy (src dst : Fin 12) : Code := .call (copyProgram src dst 8 0 1)
def expand : Code := .call (ProgramLinking.liftProgram Restriction.program smallRegs expandStacks)
def merge : Code := .call (ProgramLinking.liftProgram LeafAssignmentMergeProgram.Native.program id mergeStacks)

end Overlay

namespace NativeOverlay
open OAI.Algorithms.SubexponentialSAT.StackRoutines

noncomputable def result (a : Data) (rf : Fin 8 → Bool) : Data :=
  embedState regMap stackMap a (Overlay.state rf (a.stacks 859) (a.stacks 670)
    (a.stacks 869) (a.stacks 870) (a.stacks 871) [] [] [] [] []
    (LeafAssignmentMergeProgram.merge (Restriction.zeroMerge (a.stacks 670) (a.stacks 859))
      (a.stacks 670) (a.stacks 869)) [])

@[simp] theorem result_assignment (a : Data) (rf : Fin 8 → Bool) :
    (result a rf).stacks 145=LeafAssignmentMergeProgram.merge
      (Restriction.zeroMerge (a.stacks 670) (a.stacks 859)) (a.stacks 670) (a.stacks 869) :=
  embedState_stack regMap stackMap a _ (by decide) 10

/-- Cleanup is an actual finite program and accepts arbitrary old buffers. -/
def reset : Code := .seq (.call (StackRoutines.clearProgram 875 0 1))
  (BankRoutines.clearCmd 875 0 1 changed)

end NativeOverlay


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassStagedSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical staging, all marked counts, and actual source cleanup share one
prefix bound. Cleanup only removes bits, so it does not amplify the query's
transient cap into the next boundary allowance. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStagedSpace

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashMassAdapter HashMassStaged

/-- The caller cap L is distinct from the staged boundary cap 3*L+2. -/
def spaceBudget (a : State 40 896) (L K : ℕ) : ℕ :=
  max K (896 * (3 * L + 2) +
    (LeafOuterProgram.routeCost (782,0) a + LeafOuterNative.References.budget (a.stacks 782) + 1) +
      50 * (3 * L + 3) + 59 * L + 100)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStagedSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyStagedSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Prefix storage for the physically staged candidate attempt. The full marked-query
runtime never appears in this bound: the marked queries supply an independent
prefix cap, while preparation, reference setup and padding are polynomial. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyStagedSpace

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashMassAdapter HashGreedyExecution

/-- One fixed allowance for all source prefixes of a concrete candidate attempt. -/
def attemptSpace (a : State 40 896) (n m depth L K : ℕ) : ℕ :=
  max K (896 * (3 * L + 2) + HashCandidateProgram.Leaf.budget m depth +
    (LeafOuterProgram.routeCost (782,0) a + LeafOuterNative.References.budget (a.stacks 782) + 1) +
      50 * (3 * L + 3) + 59 * L + 23 * HashSelect.loopCap n m + 150)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyStagedSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighMarkedCleanup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
/-! Actual lower-workspace reclamation in the shared leaf ABI. Source masters,
collector, count and upper caller words are preserved by the paid cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog

@[simp] theorem result_stack (a : Data) (b : LeafProgram.Query.Data) (i : Fin 768) :
    (result a b).stacks (stackMap i)=b.stacks i :=
  embedState_stack id stackMap a b (Fin.castAdd_injective _ _) i

@[simp] theorem result_register (a : Data) (b : LeafProgram.Query.Data) (i : Fin 40) :
    (result a b).regs i=b.regs i := embedState_register id stackMap a b Function.injective_id i

@[simp] theorem project_result (a : Data) (b : LeafProgram.Query.Data) :
    project (result a b)=b := by
  apply congrArg₂ StructuredProgram.State.mk
  · exact funext (result_register a b)
  · exact funext (result_stack a b)

def cleanupCommand : Code := .call (ProgramLinking.liftProgram cleanupLocalProgram id stackMap)
noncomputable def cleaned (a : Data) : Data := result a (LeafProgram.Query.cleaned (project a))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMarkedReturn
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete return from a completed marked high-assignment count. All fresh
query workspace is reclaimed, the complete count is moved to323, and the
collector parser registers are reset after cleanup. The compact boundary cap
is distinct from the transient query cap. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn

open BitProgram StructuredCalls RecordPrograms SqrtLog
open HashMarkedQueryAdapter
open HashGreedyProgram.NativeRound

def upperCleared (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,BankRoutines.clearBankStacks upperPorts a.stacks⟩
def upperCost (a : Data) : ℕ :=
  2*(upperPorts.map (fun i => (a.stacks i).length)).sum+3*upperPorts.length+3

def command : Code := .seq finish
  (.seq HighMarkedFrontend.cleanupCommand (.seq upperClear resetParser))
noncomputable def result (a : Data) : Data :=
  parserReset (upperCleared (HighMarkedFrontend.cleaned (finishState a)))
noncomputable def cost (a : Data) : ℕ := finishSteps a+
  (LeafProgram.Query.cleanupCost (HighMarkedFrontend.project (finishState a))+1+
    (upperCost (HighMarkedFrontend.cleaned (finishState a))+3))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The head rescan retains one raw Boolean assignment and a binary countdown.
The full-key/correction gate is executed for every candidate. Accepted values
are accumulated before the cursor advances, including the empty-head case. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram

open OAI BitProgram StructuredCalls CounterPrograms

def body (accepted : Code) : Code :=
  .seq HeadEvaluationProgram.StagedGate.command
    (.seq (.ite 15 accepted (.base .skip)) (Counters.incrementCmd cursorPorts))

def command (accepted : Code) : Code := CounterForPrograms.forCmd fuelPorts (body accepted)

def power : Code := .call (ProgramLinking.liftProgram
  Counters.powerTwoProgram powerRegisters powerStacks)

open HeadEvaluationProgram.StagedGate (copy copyState clear clearState )

/-- The existing head preparation stores its actual zero word on651. Two
copies initialize_ cursor and binary-fuel construction; the head sum is reset. -/
def seed : Code := .seq (copy 651 859) (.seq (copy 651 861) (.seq power (clear 853)))


open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing TruncatedRingProgram

def add : Code := .call (ProgramLinking.liftProgram Normalize.program
  additionRegisters additionStacks)


/-- Accepted factors are added and their reusable arithmetic workspace is
reclaimed before the controller increments its candidate word. -/
def accumulate : Code := .seq add FactorEnvironment.reset


open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

open scoped BigOperators


/-- Both binary controller words are physically reclaimed after the exhausted
loop, including the possible terminal overflow bit of the assignment cursor. -/
def finalize : Code := liftCommand (SubexpSetupStorage.clearMany [859, 860]) 859 853
  FactorEnvironment.registerMap id

/-- The complete head-rescan control, including paid initialization and cleanup. -/
def scan (accepted : Code) : Code := .seq seed (.seq (command accepted) finalize)

def scanProgram (accepted : Code) := compiled (scan accepted) 651 853

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumAssembly
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete head-sum assembly. The first head gate receives a physically
cleared arithmetic bank; persistent source parameters remain outside that bank.
Accepted assignments continue through dense addition and workspace reclamation,
including empty factor products and zero-valued products. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly

open OAI BitProgram StructuredCalls StackRoutines
open HeadEvaluationProgram.StagedGate

/-- The initial workspace cleanup is paid before the complete native scan.
The concrete assembly supplies its fixed accepted-assignment command. -/
def head (accepted : Code) : Code :=
  .seq clearWork (.call (HeadSumProgram.scanProgram accepted))

def headProgram (accepted : Code) := compiled (head accepted) 651 853

open CommandRegisterFrames

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighCountInit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid entry to one disjoint high-assignment count. Internal empty binary
words represent zero; the final CanonicalHigh routine emits canonical [false].
The high odometer is copied from the actual encoded seed, never reconstructed
from an assumed family of successful branch states. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountInit

open BitProgram StructuredCalls StackRoutines HighQueryAdapter

def resetState (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,BankRoutines.clearBankStacks changed a.stacks⟩
def resetCost (a : Data) := 2*(a.stacks 792).length+3+
  (2*(changed.map (fun i => ((clearStacks 792 a.stacks) i).length)).sum+21)

def copied (a : Data) : Data :=
  ⟨readRegs (resetState a).regs 0 1 none,copyStacks 330 789 (resetState a).stacks⟩
def result (a : Data) : Data := ⟨Function.update (copied a).regs 21 true,(copied a).stacks⟩
def command : Code := .seq reset (.seq copy restoreHighGuard)
def program := compiled command 330 788
def cost (a : Data) := resetCost a+7*(a.stacks 330).length+6

@[simp] theorem guard (a : Data) : (result a).regs 21=true := by simp [result]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountInit
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighCountSeed
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Each marked count regenerates its own zero high-assignment odometer from
its current physical mask. No common high set or retained previous seed is
assumed. The original two-stack branch initializer is executed concretely. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed

open OAI BitProgram StructuredCalls StackRoutines HighQueryAdapter
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

def resetState (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,BankRoutines.clearBankStacks changed a.stacks⟩
def resetCost (a : Data) := 2*(a.stacks 791).length+3+
  (2*(changed.map (fun i => ((clearStacks 791 a.stacks) i).length)).sum+12)

def copied (a : Data) : Data :=
  ⟨readRegs (resetState a).regs 0 1 none,copyStacks 338 792 (resetState a).stacks⟩
def cost (a : Data) := resetCost a+10*(a.stacks 338).length+
  8*Branches.trueCount (a.stacks 338)+10

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyStoredNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete low-variable output with its executed beta fold, rather than
a supplied beta premise. The full source-row interpretation remains explicit. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT
open DensePolynomialProgram _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree PerturbationProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open scoped BigOperators

noncomputable def nativeStored (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u J N : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) :
    Moments.Stored (R:=a.O t) (Finset.univ : Finset (Fin rows.length)) u J :=
  outputStored (RingProgram.modelRing t ht hd a M cache) u J hu hJ theta
    (PerturbationBetaProgram.runValue t a M cache theta (pairedRows rows))
    (fun v => rows[v].1.val)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end


