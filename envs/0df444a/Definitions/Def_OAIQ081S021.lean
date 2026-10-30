-- Prove2me | Definitions.Def_OAIQ081S021
-- name    : OAIQ081S021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:25:47.660578+00:00
-- url     : https://prove2.me/theorems/b49c75f9-e7d3-40f6-8227-c752bedae462
-- title:
--   Definitions bundle OAIQ081S021 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 416 declarations of OpenAI's Lean: 340 definitions, 10 inductive types or structures, 1 instance and 65 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.ParametersProgram.logRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.ParametersProgram.port`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget.inverseIndex`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget.occurrenceCap`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget.parameterTest`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudgetProgram.Arithmetic`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudgetProgram.Arithmetic.value`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudgetProgram.candidateWidth`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCharging.depthConstant`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCharging.rightConstant`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives.Filter.emitIfSelectedSteps`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives.FrameWriter.escapeBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary.retainedPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary.scalarPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary.sourcePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop.byteBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop.uniformProductBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.localRegister`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.lowStack`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment.environmentPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment.lowPort`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment.pairs`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment.registerMap`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.inputScale`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.serviceBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace.byteBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableBudgets.payloadEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableBudgets.specializationEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.specializedPayloadBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.specializedRawBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.OuterStore`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.basePort`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.callerRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.innerPort`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.joinedPort`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.literalReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.literalRecordBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.protectedPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace.middleBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace.tableBudget` and 310 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_Asymptotics`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_ParameterBank`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseBudget`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseBudgetProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseCharging`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityPrimitives`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLogSpace_FactorAssignmentBoundary`, `SubexponentialSAT_SqrtLogSpace_FactorAssignmentLoop`, `SubexponentialSAT_SqrtLogSpace_FactorCacheProgram`, `SubexponentialSAT_SqrtLogSpace_FactorEnvironment`, `SubexponentialSAT_SqrtLogSpace_FactorEvaluationSpace`, `SubexponentialSAT_SqrtLogSpace_FactorProductSpace`, `SubexponentialSAT_SqrtLogSpace_FactorTableBudgets`, `SubexponentialSAT_SqrtLogSpace_FactorTableNative`, `SubexponentialSAT_SqrtLogSpace_FactorTableProgram`, `SubexponentialSAT_SqrtLogSpace_FactorTableSpace`, `SubexponentialSAT_SqrtLogSpace_FiniteFallback`, `SubexponentialSAT_SqrtLogSpace_GuardedCompiler`, `SubexponentialSAT_SqrtLogSpace_HashCandidateProgram`, `SubexponentialSAT_SqrtLogSpace_HashGreedy`, `SubexponentialSAT_SqrtLogSpace_HashGreedyProgram`, `SubexponentialSAT_SqrtLogSpace_HashMarkedQueryAdapter`, `SubexponentialSAT_SqrtLogSpace_HashMarkedReturn`, `SubexponentialSAT_SqrtLogSpace_HashMassAdapter`, `SubexponentialSAT_SqrtLogSpace_HeadAcceptedCorrect`, `SubexponentialSAT_SqrtLogSpace_HeadEvaluationProgram`, `SubexponentialSAT_SqrtLogSpace_HeadLoaderBudgets`, `SubexponentialSAT_SqrtLogSpace_HeadSpecializationProgram`, `SubexponentialSAT_SqrtLogSpace_HeadSumAssembly`, `SubexponentialSAT_SqrtLogSpace_HeadSumBudgets`, `SubexponentialSAT_SqrtLogSpace_HeadSumNative`, `SubexponentialSAT_SqrtLogSpace_HeadSumProgram`, `SubexponentialSAT_SqrtLogSpace_HighCountInit`, `SubexponentialSAT_SqrtLogSpace_HighCountSeed`, `SubexponentialSAT_SqrtLogSpace_HighIncidenceProgram`, `SubexponentialSAT_SqrtLogSpace_HighMarkedCleanup`, `SubexponentialSAT_SqrtLogSpace_HighQueryAdapter`, `SubexponentialSAT_SqrtLogSpace_HighQueryCorrect`, `SubexponentialSAT_SqrtLogSpace_HighQueryCount`, `SubexponentialSAT_SqrtLogSpace_HighQueryLocalBounds`, `SubexponentialSAT_SqrtLogSpace_HighQueryProgram`, `SubexponentialSAT_SqrtLogSpace_HighQuerySetup`, `SubexponentialSAT_SqrtLogSpace_HighQueryStart`, `SubexponentialSAT_SqrtLogSpace_NativeCode`, `SubexponentialSAT_SqrtLogSpace_NativeFrontend`, `SubexponentialSAT_SqrtLogSpace_NativeLayoutLoad`, `SubexponentialSAT_SqrtLogSpace_NativeLeafPreparation`, `SubexponentialSAT_SqrtLogSpace_NativeOuter`, `SubexponentialSAT_SqrtLogSpace_NativeOuterBudgets`, `SubexponentialSAT_SqrtLogSpace_NativeProgram`, `SubexponentialSAT_SqrtLogSpace_NativeQueryInputBounds`, `SubexponentialSAT_SqrtLogSpace_NativeQueryPreparation`, `SubexponentialSAT_SqrtLogSpace_NativeQuerySpaceBounds`, `SubexponentialSAT_SqrtLogSpace_NativeQueryTimeBounds`, `SubexponentialSAT_SqrtLogSpace_NativeSetupSpace`, `SubexponentialSAT_SqrtLogSpace_NativeTerminal`, `SubexponentialSAT_SqrtLogSpace_NodeReadoutSpace`, `SubexponentialSAT_SqrtLogSpace_PairNativeSetup`, `SubexponentialSAT_SqrtLogSpace_QueryAssembler`, `SubexponentialSAT_SqrtLogSpace_QueryHeadBudgets`, `SubexponentialSAT_SqrtLogSpace_QueryIncidenceCommand`, `SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation`, `SubexponentialSAT_SqrtLogSpace_QueryNodeFinish`, `SubexponentialSAT_SqrtLogSpace_QueryPairEvaluation`, `SubexponentialSAT_SqrtLogSpace_QueryProducerSpace`, `SubexponentialSAT_SqrtLogSpace_QueryProgram`, `SubexponentialSAT_SqrtLogSpace_QueryReadyConstruction`, `SubexponentialSAT_SqrtLogSpace_QueryReconstruction`, `SubexponentialSAT_SqrtLogSpace_QuerySourceSnapshot`, `SubexponentialSAT_SqrtLogSpace_QueryStreamCorrect`, `SubexponentialSAT_SqrtLogSpace_QueryStreamSpaceBudgets`, `SubexponentialSAT_SqrtLogSpace_QueryTupleInit`, `SubexponentialSAT_SqrtLogSpace_QueryTupleState`, `SubexponentialSAT_SqrtLogSpace_QueryTupleSum`, `SubexponentialSAT_SqrtLogSpace_QueryVisitorBudgets`, `SubexponentialSAT_SqrtLogSpace_QueryVisitorHead`, `SubexponentialSAT_SqrtLogSpace_QueryVisitorLoad`, `SubexponentialSAT_SqrtLogSpace_QueryVisitorLoadBounds`, `SubexponentialSAT_SqrtLogSpace_QueryVisitorSemantics`, `SubexponentialSAT_SqrtLogSpace_ReconstructionSpace`, `SubexponentialSAT_SqrtLogSpace_ScheduleProgram`, `SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore`, `SubexponentialSAT_SqrtLogSpace_SignatureHeadPrepare`, `SubexponentialSAT_SqrtLogSpace_SignatureKeyNative`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleDFS`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleLoadCommand`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleNative`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleTraversal`, `SubexponentialSAT_SqrtLogSpace_SparseCodeSearch`, `SubexponentialSAT_SqrtLogSpace_StreamResources`, `SubexponentialSAT_SqrtLogSpace_StreamedQueryMeasuredCost`, `SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram`, `SubexponentialSAT_SqrtLogSpace_TupleRunBudgets`, `SubexponentialSAT_SqrtLogSpace_VisitedTape`, `SubexponentialSAT_StackCompiler`, `SubexponentialSAT_StackMachine`, `SubexponentialSAT_SubexpCRTOuterControl`, `SubexponentialSAT_SubexpFrontend`, `SubexponentialSAT_SubexpNormalizationProgram`, `SubexponentialSAT_SubexpSwapMultiplicity`, `SubexponentialSAT_SubexpTautologyFilterProgram`, `SubexponentialSAT_Subexp_ConstructivePacking`, `SubexponentialSAT_Subexp_GlobalBasisMetadata`, `SubexponentialSAT_Subexp_MatrixAnchorTypes`, `SubexponentialSAT_Subexp_MatrixColorReadProgram`, `SubexponentialSAT_Subexp_MatrixInputProgram`, `SubexponentialSAT_Subexp_MatrixParityProgram`, `SubexponentialSAT_Subexp_MismatchPlanProgram`, `SubexponentialSAT_Subexp_SpectralRank`, `SubexponentialSAT_Subexp_TensorSpectrum`, `SubexponentialSAT_Subexp_TypeBitProgram`, `SubexponentialSAT_Subexp_UniversalRowGuard`, `SubexponentialSAT_Subexp_UniversalRowMismatchBound`, `SubexponentialSAT_Subexp_UniversalRowMismatchProgram`, `SubexponentialSAT_Subexp_UniversalRowMismatchTypes`, `SubexponentialSAT_Subexp_UniversalRowSourceBound`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S042`, `OAIQ081S043` and `OAIQ081S074`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds.physicalCap_polynomial` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Spectral.centered_normalizedTail_le_of_sq`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryCountReconstruction_run_space_of_outputs_with_full_frame` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Spectral.centered_normalizedTail_le_of_sq`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_Asymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Numerical parameters for the disjoint counting reduction. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- The literal base-two exponent in the counting manuscript. -/
noncomputable def rho (n : ℕ) : ℝ :=
  (n : ℝ) * (Real.logb 2 (Real.logb 2 n)) ^ 2 / Real.sqrt (Real.logb 2 n)

/-- Exact ceiling logarithms, computed with natural-number arithmetic. -/
def sparsifyLambda (n : ℕ) : ℕ := Nat.clog 2 n

def sparsifyNu (n : ℕ) : ℕ := Nat.clog 2 (sparsifyLambda n)

def sparsifySchedule (n : ℕ) : ℕ :=
  Nat.sqrt (sparsifyLambda n) / sparsifyNu n ^ 2

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
Actual primitive tape programs for encoded stacks. Every instruction below is
one move or one write of `Computation.PrimitiveMachine`; the measured traces
are derived from that transition function.
-/

namespace SubexponentialSAT.StackMachine

open Turing SubexponentialSAT.Computation

abbrev BitTape := Turing.Tape (Option Bool)
abbrev Action := Turing.TM0.Stmt (Option Bool)

def applyAction (action : Action) (tape : BitTape) : BitTape :=
  match action with
  | .move d => tape.move d
  | .write b => tape.write b

def execute : List Action → BitTape → BitTape
  | [], tape => tape
  | action :: rest, tape => execute rest (applyAction action tape)

@[simp] theorem execute_nil (tape : BitTape) : execute [] tape = tape := rfl

@[simp] theorem execute_cons (action : Action) (rest : List Action) (tape : BitTape) :
    execute (action :: rest) tape = execute rest (applyAction action tape) := rfl

/-- All cells left of this representation are blank. There is no extra binary
sentinel, so a width-one Boolean code agrees with the actual raw input tape. -/
def dataTape (bits : List Bool) : BitTape := Tape.mk₁ (bits.map some)

def pushBits : List Bool → List Action
  | [] => []
  | bit :: bits => pushBits bits ++ [.move .left, .write (some bit)]

@[simp] theorem length_pushBits (bits : List Bool) :
    (pushBits bits).length = 2 * bits.length := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [pushBits, ih]; omega

def popBits : ℕ → List Action
  | 0 => []
  | n + 1 => [.write none, .move .right] ++ popBits n

@[simp] theorem length_popBits (n : ℕ) : (popBits n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [popBits, ih]; omega

/-! Reindexing a genuinely finite controller changes no primitive actions. -/

universe u

structure Controller (Q : Type u) (tapeCount : ℕ) where
  inputTape : Fin tapeCount
  start : Q
  scan : Q → Fin tapeCount
  transition : Q → Option Bool → Bool ⊕ (Q × Action)

structure ControlCfg (Q : Type u) (tapeCount : ℕ) where
  state : Bool ⊕ Q
  tapes : Fin tapeCount → BitTape

def controlStep {Q : Type u} {t : ℕ} (p : Controller Q t)
    (c : ControlCfg Q t) : Option (ControlCfg Q t) :=
  match c.state with
  | .inl _ => none
  | .inr q =>
    let k := p.scan q
    match p.transition q (c.tapes k).head with
    | .inl answer => some ⟨.inl answer, c.tapes⟩
    | .inr (q', action) =>
      some ⟨.inr q', Function.update c.tapes k (applyAction action (c.tapes k))⟩

def reindex {Q : Type u} {t n : ℕ} (e : Q ≃ Fin n) (p : Controller Q t) :
    PrimitiveMachine where
  tapeCount := t
  stateCount := n
  inputTape := p.inputTape
  start := e p.start
  scan q := p.scan (e.symm q)
  transition q b :=
    match p.transition (e.symm q) b with
    | .inl answer => .inl answer
    | .inr (q', action) => .inr (e q', action)

def reindexCfg {Q : Type u} {t n : ℕ} (e : Q ≃ Fin n) (p : Controller Q t)
    (c : ControlCfg Q t) : (reindex e p).Cfg :=
  ⟨match c.state with | .inl b => .inl b | .inr q => .inr (e q), c.tapes⟩

/-! A block reader uses one right move per bit, stores the observed bit in its
finite control, then performs the same number of left moves. -/

abbrev Registers (width : ℕ) := Fin width → Option Bool
abbrev ReaderState (width : ℕ) := Fin (2 * width + 1) × Registers width

/-! Connecting the physical routines to the fixed alphabet encodings. -/

@[simp] theorem dataTape_nil_nth (n : ℕ) : (dataTape []).nth n = none := by
  simp [dataTape, Tape.mk₁, Tape.mk₂, ListBlank.nth_mk]
  rfl

/-- A function on a fixed finite register space; not an unbounded list read. -/
def registerBits {width : ℕ} (registers : Registers width) : List Bool :=
  (List.ofFn registers).filterMap id

@[simp] theorem registerBits_blank (width : ℕ) :
    registerBits (fun i : Fin width => (dataTape []).nth i.val) = [] := by
  simp [registerBits, List.ofFn_const]

/-! Inlining into a larger finite controller. The hypotheses below are
single-instruction transition-table equations, not assumed execution bounds.
They allow the final local control index to denote any caller continuation. -/

end SubexponentialSAT.StackMachine

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
A global finite controller for one-head finite stack programs. A source step
first inspects one finite-alphabet stack top, then changes finite control and
keeps, pops, or pushes that stack. The compiled controller performs only the
primitive bit reads, moves, and writes of StackMachine.controlStep.
-/

namespace SubexponentialSAT.StackCompiler

open Turing SubexponentialSAT.Computation SubexponentialSAT.StackMachine

inductive Mutation (α : Type) where
  | keep
  | pop
  | push (value : α)
  deriving Fintype

def Mutation.apply {α : Type} : Mutation α → List α → List α
  | .keep, s => s
  | .pop, s => s.tail
  | .push a, s => a :: s

structure StackProgram (Q : Type) {t : ℕ} (Γ : Fin t → Type) where
  inputTape : Fin t
  start : Q
  select : Q → Fin t
  transition : (q : Q) → Option (Γ (select q)) →
    Bool ⊕ (Q × Mutation (Γ (select q)))

structure StackCfg (Q : Type) {t : ℕ} (Γ : Fin t → Type) where
  state : Bool ⊕ Q
  stk : ∀ k, List (Γ k)

def stackStep {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (p : StackProgram Q Γ) (c : StackCfg Q Γ) : Option (StackCfg Q Γ) :=
  match c.state with
  | .inl _ => none
  | .inr q =>
    match p.transition q (c.stk (p.select q)).head? with
    | .inl answer => some ⟨.inl answer, c.stk⟩
    | .inr (q', op) => some ⟨.inr q',
        Function.update c.stk (p.select q) (op.apply (c.stk (p.select q)))⟩

/-- The source input stack uses its given Boolean interface; all other stacks are empty. -/
def initialCfg {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (p : StackProgram Q Γ) (inputAlphabet : Γ p.inputTape ≃ Bool)
    (input : List Bool) : StackCfg Q Γ :=
  ⟨.inr p.start, Function.update (fun _ => []) p.inputTape
    (input.map inputAlphabet.symm)⟩

end SubexponentialSAT.StackCompiler

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_ParameterBank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed Boolean-stack arithmetic in a 19-word data bank and 13 scratch stacks. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.ParametersProgram

open BinaryArithmetic

def port (i : Fin 19) : Fin 32 := i.castAdd 13

def logRegisters : Fin 3 → Fin 8 := Fin.castAdd 5


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.ParametersProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseCharging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Appendix A, insertion recurrence and the resulting path budgets. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCharging

open scoped BigOperators

def depthConstant (k M : ℕ) : ℕ :=
  4 * ∑ j ∈ Finset.range (k - 1), (3 * M) ^ j

def rightConstant (k : ℕ) : ℕ :=
  4 * ∑ j ∈ Finset.range (k - 1), 3 ^ j

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCharging
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Sharp numerical budgets for disjoint counting sparsification

The frozen counting manuscript, Appendix A, lines 1991–2054. These numerical lemmas do not assert the
existence of a sparsification tree or a primitive implementation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget

open Finset
open scoped BigOperators

/-- The literal-degree sum in the source's leaf occurrence estimate. -/
def occurrenceCap (k M : ℕ) : ℕ := 2 * ∑ j ∈ range k, M ^ j

/-- An explicit constant exponent absorbs the affine term in the dyadic test. -/
theorem control_exponent (a q γ : ℕ) :
    let T := 2 * (γ * (a + 4 * q + 1) + 1)
    1 ≤ T ∧ γ ≤ 2 ^ T ∧ γ * (a + q * (T + 2)) ≤ 2 ^ T := by
  let u := γ * (a + 4 * q + 1) + 1
  have hu : 1 ≤ u := by dsimp [u]; omega
  have hγ : γ ≤ u := by dsimp [u]; nlinarith
  have hconstant : γ * a + 2 * γ * q ≤ u := by dsimp [u]; nlinarith
  have hslope : 2 * γ * q + 1 ≤ u := by dsimp [u]; nlinarith
  have hp : u ≤ 2 ^ u := (Nat.lt_pow_self (by decide : 1 < 2)).le
  have hsquare : u ^ 2 ≤ 2 ^ (2 * u) := by
    calc
      u ^ 2 ≤ (2 ^ u) ^ 2 := Nat.pow_le_pow_left hp 2
      _ = 2 ^ (2 * u) := by rw [← pow_mul, Nat.mul_comm]
  have hscaled := Nat.mul_le_mul_right u hslope
  have hlinear : γ * (a + q * (2 * u + 2)) ≤ u ^ 2 := by
    nlinarith
  refine ⟨by dsimp [u] at *; omega, ?_, hlinear.trans hsquare⟩
  exact hγ.trans ((by nlinarith : u ≤ u ^ 2).trans hsquare)

open SparseCharging

theorem depthConstant_le (k M : ℕ) (hM : 2 ≤ M) :
    depthConstant k M ≤ (4 * (k - 1) * 3 ^ (k - 2)) * M ^ (k - 2) := by
  have hsum : (∑ j ∈ range (k - 1), (3 * M) ^ j) ≤
      (k - 1) * (3 * M) ^ (k - 2) := by
    calc
      _ ≤ ∑ _j ∈ range (k - 1), (3 * M) ^ (k - 2) := by
        apply sum_le_sum
        intro j hj
        exact Nat.pow_le_pow_right (by omega) (by have := mem_range.mp hj; omega)
      _ = _ := by simp
  calc
    depthConstant k M ≤ 4 * ((k - 1) * (3 * M) ^ (k - 2)) := Nat.mul_le_mul_left _ hsum
    _ = _ := by rw [mul_pow]; ring

/-- Exact source test at the candidate `M = 2^e`, for the rational numerator `a`
and denominator `b`. Only integer arithmetic and a ceiling logarithm occur. -/
def parameterTest (k a b e : ℕ) : Bool :=
  decide (2 ≤ 2 ^ e ∧ rightConstant k ≤ 2 ^ e ∧
    rightConstant k * Nat.clog 2 (4 * depthConstant k (2 ^ e) * 2 ^ e) * b ≤
      a * 2 ^ e)

/-- Conservative inverse of a positive rational budget. -/
def inverseIndex (a b : ℕ) : ℕ := (b - 1) / a + 1

theorem inverseIndex_mul (a b : ℕ) (ha : 0 < a) : b ≤ a * inverseIndex a b := by
  have := Nat.lt_mul_div_succ (b - 1) ha
  dsimp [inverseIndex]
  omega

theorem rational_data (σ : ℚ) (hσ : 0 < σ) :
    0 < σ.num.natAbs ∧ (σ.num.natAbs : ℝ) / σ.den = (σ : ℝ) := by
  have hnum : 0 < σ.num := Rat.num_pos.mpr hσ
  have habs : (σ.num.natAbs : ℤ) = σ.num := Int.natAbs_of_nonneg hnum.le
  refine ⟨Int.natAbs_pos.mpr (ne_of_gt hnum), ?_⟩
  rw [Rat.cast_def]
  congr 1
  simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) habs


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseBudgetProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
Concrete finite-control construction of the Appendix A dyadic search.
The input budget is `1 / s`; the search uses only exact binary arithmetic.
This file separates command construction from theorems about its execution.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudgetProgram

open BinaryArithmetic
open ParametersProgram
open scoped BigOperators

@[simp] theorem bits_three_length : (3 : ℕ).bits.length = 2 := by
  rw [Nat.bit1_bits 1, Nat.one_bits]
  rfl

@[simp] theorem bits_four_length : (4 : ℕ).bits.length = 3 := by
  rw [Nat.bit0_bits 2 (by decide), Nat.bit0_bits 1 (by decide), Nat.one_bits]
  rfl

@[simp] theorem bits_sixteen_length : (16 : ℕ).bits.length = 5 := by
  rw [Nat.bit0_bits 8 (by decide), Nat.bit0_bits 4 (by decide),
    Nat.bit0_bits 2 (by decide), Nat.bit0_bits 1 (by decide), Nat.one_bits]
  rfl

inductive Arithmetic where
  | add
  | multiply

def Arithmetic.value : Arithmetic → ℕ → ℕ → ℕ
  | .add => (· + ·)
  | .multiply => (· * ·)

def candidateWidth (k : ℕ) (s M : List Bool) : ℕ :=
  (k - 1) * (M.length + 6) + M.length + s.length +
    (SparseCharging.rightConstant k).bits.length + 20

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudgetProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete record-count and emission primitives extracted from supplied sources.
No sparsification schedule or formula evaluator is imported. Provenance is recorded
in verification/counting-draft/worker04/extraction.json. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives

open BinaryArithmetic

namespace FrameWriter

/-- Escaped data without the final false delimiter. -/
def escapeBits : List Bool → List Bool
  | [] => []
  | b :: bs => true :: b :: escapeBits bs


end FrameWriter

namespace Filter

def emitIfSelectedSteps (selected : Bool) (bits : List Bool) : ℕ :=
  if selected then 5 * bits.length + 11 else 2 * bits.length + 7


end Filter

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_VisitedTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Passive absolute-coordinate instrumentation for the primitive machine.
The interval on every tape includes its initial input cells and every visited
head coordinate. The instrumentation never changes a primitive transition. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open OAI.Algorithms.SubexponentialSAT.Computation
open scoped BigOperators

@[simp] theorem LocatedCfg.monitor_config {machine : PrimitiveMachine}
    (c : LocatedCfg machine) (config : machine.Cfg) :
    (c.monitor config).config = config := by
  cases hs : c.config.state with
  | inl answer => simp [LocatedCfg.monitor, hs]
  | inr q =>
      cases ht : machine.transition q (c.config.tapes (machine.scan q)).head with
      | inl answer => simp [LocatedCfg.monitor, hs, ht]
      | inr result =>
          obtain ⟨next, action⟩ := result
          simp [LocatedCfg.monitor, hs, ht]


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete components of the sharp clause/core search from Appendix A.
The guard counts actual framed literals and executes the preserving subset tester.
The complete search and its polynomial resource bound are developed separately below. -/


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

namespace Selector

@[simp] theorem update_high_apply_low (store : Fin 24 → List Bool) (port : Fin 24)
    (word : List Bool) (i : Fin 9) (hport : 9 ≤ port.val) :
    Function.update store port word (Fin.castAdd 15 i) = store (Fin.castAdd 15 i) := by
  have hne : Fin.castAdd 15 i ≠ port := by
    intro h
    have hh := congrArg Fin.val h
    change i.val = port.val at hh
    have := i.isLt
    omega
  simp [hne]

end Selector

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFrontend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Syntactic frontend for the variable-parameter SAT algorithm

The external input declares `n` Boolean coordinates. We first normalize the
finite CNF, then enumerate only its syntactically appearing coordinates in
increasing order. The resulting coordinate set is retained through all later
branching; this frontend is not reapplied at sparsification leaves.

All constructions inspect finite syntax. No satisfiability test, choice of a
satisfying assignment, or noncomputable enumeration is used by `prepare`.
-/

namespace SubexponentialSAT.SubexpFrontend

open SAT

/-- Flip the polarity bit, retaining the variable index. -/
def negateCode (c : ℕ) : ℕ :=
  2 * (c / 2) + if c % 2 = 1 then 0 else 1

end SubexponentialSAT.SubexpFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GlobalBasisMetadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical packing metadata lookup

The raw packing table and query remain on stacks 0 and 1. A successful lookup
returns either a block/type pair on 2/3, or a leftover rank on 4. Register 4
distinguishes those cases; all other registers and stacks 5 through 11 are
cleared. Keys, indices, and type encodings are runtime words.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisMetadata

abbrev Regs := Fin 5 → Bool

end SubexponentialSAT.Subexp.GlobalBasisMetadata

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ConstructivePacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable complete-block packing

All execution definitions use supplied finite lists, filtering, minimum scans,
indexed list access, and index lookup. No execution definition uses classical
choice or an abstract inverse. Mathematical cardinalities occur only in proofs.
-/

namespace SubexponentialSAT.Subexp.ConstructivePacking

open scoped BigOperators

/-- A concrete list enumerating a predicate gives a computable subtype equivalence.
The predicate itself need not have a decision procedure: the list is supplied. -/
def listSubtypeEquiv {α : Type*} [DecidableEq α] (xs : List α) (hn : xs.Nodup)
    (p : α → Prop) (hm : ∀ x, x ∈ xs ↔ p x) : Fin xs.length ≃ {x // p x} where
  toFun i := ⟨xs.get i, (hm _).mp (List.get_mem xs i)⟩
  invFun x := ⟨xs.idxOf x.val, List.idxOf_lt_length_iff.mpr ((hm x.val).mpr x.property)⟩
  left_inv i := Fin.ext (List.get_idxOf hn i)
  right_inv _x := Subtype.ext (List.idxOf_get _)

end SubexponentialSAT.Subexp.ConstructivePacking

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSwapMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Multiplicities of register-swap eigenvalue labels

The negative local labels are strictly below the diagonal and the positive
labels are on or above it. Counting these labels and their tensor words is
independent of the characteristic of the coefficient field.
-/

namespace SubexponentialSAT.SubexpSwapMultiplicity

open scoped BigOperators

def positiveMultiplicity (r : ℕ) : ℕ := r * (r + 1) / 2
def negativeMultiplicity (r : ℕ) : ℕ := r * (r - 1) / 2

def swapMultiplicity (r q w : ℕ) : ℕ :=
  q.choose w * positiveMultiplicity r ^ (q - w) * negativeMultiplicity r ^ w

/-- The uniform word measure, expressed with exact rational arithmetic. -/
def swapProbability (r q w : ℕ) : ℚ :=
  (swapMultiplicity r q w : ℚ) / ((r : ℚ) ^ 2) ^ q

/-! ## General binomial second moment and the interval tail -/

end SubexponentialSAT.SubexpSwapMultiplicity

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TensorSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Tensor eigenbases for the multicolor register swap

The finite change of basis is constructed from invertible local kernels. This
module then specializes it to the actual register swap and transports it to the
joint fiber of universal types; multiplicities count those actual basis labels.
-/

namespace SubexponentialSAT.Subexp.TensorSpectrum

open scoped BigOperators

section Multiplicities

open SubexponentialSAT.SubexpSwapMultiplicity

variable {r Q Δ : ℕ}

/-- The integer tail, with both local eigenspace multiplicities retained. -/
def weightedTail (q a b A R : ℕ) : ℕ :=
  ∑ w ∈ Finset.range (q + 1),
    if w ∈ Finset.Ico A (A + R) then 0 else q.choose w * a ^ (q - w) * b ^ w

end Multiplicities

end SubexponentialSAT.Subexp.TensorSpectrum

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SpectralRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual rank bounds for the multi-color swap construction

The linear-algebra input is the dimension of the actual range of `id - M`.
The local swap multiplicities and the finite tail are kept as ordinary natural
counts, and converted to real inequalities only at the final scaling step.
-/

namespace SubexponentialSAT.Subexp.SpectralRank

open Module
open scoped BigOperators

section Scalar

variable {K α : Type*} [Field K] [DecidableEq α]

/-- The weight-dependent scalar in equation (3.5). -/
def coefficientEigenvalue (R : ℕ) (c : ℕ → K) (w : ℕ) : K :=
  (-1 : K) ^ w * ∑ j ∈ Finset.range R, c j * (w.choose j : K)

end Scalar

section ProbabilityTail

open SubexponentialSAT.Subexp.TensorSpectrum SubexponentialSAT.SubexpSwapMultiplicity

/-- The probability of an integer weight outside the interpolation interval,
using the actual normalized tensor multiplicities. -/
def normalizedTail (r q A R : ℕ) : ℚ :=
  ∑ w ∈ Finset.range (q + 1),
    if w ∈ Finset.Ico A (A + R) then 0 else swapProbability r q w

end ProbabilityTail

end SubexponentialSAT.Subexp.SpectralRank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowGuard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Count the actual mismatch-index records and compare their count with R. -/

namespace SubexponentialSAT.Subexp.UniversalRowGuard

abbrev Word := List Bool

end SubexponentialSAT.Subexp.UniversalRowGuard

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixColorReadProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed program that consumes one color word from each of the four
matrix-input streams. The word width is supplied as a unary stack. -/

namespace SubexponentialSAT.Subexp.MatrixColorReadProgram

def source (i : Fin 4) : Fin 23 := ⟨17 + i.val, by omega⟩
def target (i : Fin 4) : Fin 23 := ⟨13 + i.val, by omega⟩

end SubexponentialSAT.Subexp.MatrixColorReadProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixParityProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A four-label program computes the sign parity of a unary index. The
bits of the counter are irrelevant; only its length is used. -/

namespace SubexponentialSAT.Subexp.MatrixParityProgram

def toggle : ℕ → Bool → Bool
  | 0, b => b
  | n + 1, b => toggle n (!b)

def sign {K : Type*} [Ring K] (b : Bool) : K := if b then -1 else 1

end SubexponentialSAT.Subexp.MatrixParityProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixInputProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Extract head/slot rows and compare the untouched spectator rows. All row
widths and selected-row indices are data; the instruction table is fixed. -/

namespace SubexponentialSAT.Subexp.MatrixInputProgram

def normalizedBits (common : List Bool) (before after : List (List Bool)) : List Bool :=
  common ++ before.flatten ++ (common ++ after.flatten)

def array (head slot : List Bool) (before after : List (List Bool)) : List Bool :=
  head ++ before.flatten ++ (slot ++ after.flatten)

def cost (left right index width : List Bool) : ℕ :=
  18 * (left.length + right.length) +
    4 * index.length * (14 * width.length + 17) + 203 * width.length + 265

end SubexponentialSAT.Subexp.MatrixInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixAnchorTypes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Canonical one-hot color reads for the explicit joint-membership guard. -/

namespace SubexponentialSAT.Subexp.MatrixAnchorReadProgram

variable {r Q Δ : ℕ}

def colorWord (c : Fin r) : List Bool := List.ofFn fun d : Fin r => decide (c = d)

@[simp] theorem colorWord_length (c : Fin r) : (colorWord c).length = r := by simp [colorWord]

end SubexponentialSAT.Subexp.MatrixAnchorReadProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MismatchPlanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical mismatch-position selection

The input consists of two packed arrays, a runtime row width, and a framed
list of numeric positions. Each callback reads the two rows with the actual
persistent array reader, compares their bytes, and emits exactly the unequal
positions. The arrays and their order are preserved.
-/

namespace SubexponentialSAT.Subexp.MismatchPlanProgram

abbrev Regs := Fin 8 → Bool

abbrev flags (regs : Regs) (v p f : Bool) : Regs :=
  Function.update (Function.update (Function.update regs 0 v) 1 p) 7 f

@[simp] theorem flags_self (regs : Regs) : flags regs (regs 0) (regs 1) (regs 7) = regs := by
  funext j; fin_cases j <;> simp [flags]

abbrev markedRegs (regs : Regs) (answer : Bool) : Regs :=
  Function.update (Function.update regs 1 true) 7 (!answer)

abbrev outerFlags (regs : Regs) (v p f : Bool) : Regs :=
  Function.update (Function.update (Function.update regs 5 v) 6 p) 7 f

@[simp] theorem outerFlags_self (regs : Regs) :
    outerFlags regs (regs 5) (regs 6) (regs 7) = regs := by
  funext j; fin_cases j <;> simp [outerFlags]

end SubexponentialSAT.Subexp.MismatchPlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowMismatchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Generate all positions on tape, then retain the mismatches.  The output
is in descending position order, as required by the prepend-based row loops. -/

namespace SubexponentialSAT.Subexp.UniversalRowMismatchProgram

abbrev Word := List Bool
abbrev Regs := Fin 10 → Bool

def installedRegs (regs : Regs) (rf : Fin 8 → Bool) : Regs :=
  fun j => if h : j.val < 8 then rf ⟨j.val, h⟩ else regs j

end SubexponentialSAT.Subexp.UniversalRowMismatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowMismatchTypes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Read the two relevant words from the complete types, generate their
mismatch positions, and restore the temporary extracted words. -/

namespace SubexponentialSAT.Subexp.UniversalRowMismatchTypes

abbrev Word := List Bool

end SubexponentialSAT.Subexp.UniversalRowMismatchTypes

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowSourceBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial bounds for the actual nested row-data and source emitters. -/

namespace SubexponentialSAT.Subexp.UniversalRowSourceBound

abbrev Word := List Bool

end SubexponentialSAT.Subexp.UniversalRowSourceBound

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TypeBitProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed seven-label routine reads a runtime-indexed bit and clears its
two inputs. An out-of-range read returns false, as `List.getD` does. -/

namespace SubexponentialSAT.Subexp.TypeBitProgram

def resultRegs (b : Bool) : Fin 3 → Bool := ![false,false,b]

end SubexponentialSAT.Subexp.TypeBitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorCacheProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical reconstruction of the exact node caches, including the sparse
ring identity and ambient shape, before accepted assignment evaluation. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram

open OAI
open SqrtLog

def lowStack : Fin 768 → Fin 896 := Fin.castAdd 128

def localRegister : Fin 16 → Fin 40 := Fin.castAdd 24

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSpecializationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Immediate Boolean specialization using the actual dictionary scanner. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Subset
open OAI

def below : List Bool → List Bool → Bool
  | [], _ => true
  | b::bs, qs => (!b || qs.headD false) && below bs qs.tail

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Subset

/-! The dictionary framing, key rewrite and record traversal follow the actual
MomentsProjectionProgramNative implementation. The replacement comparator tests
support inclusion, so this scan implements evaluation at a Boolean correction
assignment. Numeric-key collisions are intentionally left for normalization. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization
open OAI
open OAI.Algorithms.SubexponentialSAT.SqrtLog

def subsetPorts : Fin 3 → Fin 10 := ![2,1,6]


open Squarefree

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram
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
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog

variable {V R : Type*} [DecidableEq V] [CommRing R]

def scalingBudget (n B d u J : ℕ) : ℕ :=
  (u * J) * (40000 * (d + 1) ^ 3 * (B + 1) ^ 2 + 35 * (d * B) +
    7 * d + 22 * (n + u + J) + 57) + 6

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryProducerSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Immediate Boolean specialization followed by the actual additive dictionary
normalizer. The input is a polynomial-size origin/singleton incidence stream;
no multivariate product is materialized before specialization. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace

open OAI
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open TruncatedRingProgram
open scoped BigOperators

/-- The source arithmetic uses its original twenty-eight ports. -/
def normalizePorts : Fin 28 → Fin 38 := Fin.castAdd 10

def scanPorts : Fin 10 → Fin 38 := Fin.natAdd 28

def scanRegisters : Fin 5 → Fin 8 := Fin.castAdd 3

noncomputable def scanOverlay (regs : Fin 8 → Bool) (rr : Fin 5 → Bool) : Fin 8 → Bool :=
  Function.extend scanRegisters rr regs

/-- Escape bits without the final delimiter, used only in the framing proof. -/
def escaped : List Bool → List Bool
  | [] => []
  | bit :: bits => true :: bit :: escaped bits

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryIncidenceCommand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed native incidence command and its physical port ABI. The definitions
are extracted unchanged from the same emitter-specializer composition. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
open OAI
open OAI.Algorithms.SubexponentialSAT.SqrtLog

namespace Native

def lowPorts : Fin 256 → Fin 294 := Fin.castAdd 38

def producerPorts : Fin 38 → Fin 294 := Fin.natAdd 256

def producerRegisters : Fin 8 → Fin 16 := Fin.castAdd 8

def loadPairs : List (Fin 294 × Fin 294) := [(194,261),(202,268),(204,280)]

end Native
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StreamResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform storage rules for concrete streaming loops. A local runtime bound
is used only for one invocation whose entire initial storage is uniformly
bounded; neither bound depends on the number of loop iterations. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

/-- Deterministic successful traces to halted states have the same length. -/
theorem halted_trace_steps_eq {α : Type*} {step : α → Option α}
    {n m : ℕ} {a b c : α} (hb : Computation.Trace step n a b)
    (hc : Computation.Trace step m a c) (hstopb : step b = none)
    (hstopc : step c = none) : n = m := by
  induction hb generalizing m c with
  | refl a =>
      cases hc with
      | refl => rfl
      | cons hs _ => simp [hstopb] at hs
  | @cons n a next b hs ht ih =>
      cases hc with
      | refl => simp [hstopc] at hs
      | @cons m _ next' _ hs' ht' =>
          have heq : next = next' := Option.some.inj (hs.symm.trans hs')
          subst next'
          exact congrArg Nat.succ (ih ht' hstopb hstopc)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual selected-factor table runs over ambient variable IDs. Each low
payload is specialized immediately before its framed table entry is retained.
The source scratch embedding excludes persistent layout masters. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev OuterStore := Fin 896 → List Bool

def innerPort (i : Fin 256) : Fin 896 := ⟨340+i.val, by omega⟩

def basePort (i : Fin 768) : Fin 896 :=
  if i = 640 then 885 else if i = 641 then 886 else
  if i = 642 then 887 else if i = 647 then 888 else
  if i = 650 then 889 else if i = 651 then 890 else
  if i = 670 then 891 else if i = 671 then 892 else i.castAdd 128

/-- These are live caller words, never source scratch after relocation. -/
def protectedPorts : List (Fin 896) := [640,641,642,647,650,651,670,671]

def joinedPort (i : Fin 294) : Fin 896 := ⟨340+i.val, by omega⟩

def literalReady (s : OuterStore) (count acc : List Bool) : OuterStore :=
  Function.update (Function.update s 573 count) 569 acc

/-- Space for one framed original-variable ID and one bounded payload. -/
def literalRecordBound (n L : ℕ) : ℕ := 2*n+2*L+4

def callerRegisters (i : Fin 16) : Fin 40 := i.castAdd 24

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorEnvironment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The seven fixed persistent cache words are physically copied into the
native arithmetic environment. Cleanup clears those seven copies; both
commands frame all other stacks, including the query buffers. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment

open OAI

def registerMap : Fin 16 → Fin 40 := Fin.castAdd 24

def lowPort : Fin 56 → Fin 896 := Fin.castAdd 840

def pairs : List (Fin 896 × Fin 896) :=
  [(194, 5), (202, 12), (203, 17), (201, 22), (204, 39), (212, 45), (243, 46)]

def environmentPorts : List (Fin 896) := [5, 12, 17, 22, 39, 45, 46]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The original concrete factor accumulator, with empty correction support.
All three tape moves and the original sparse product call are charged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace

open OAI
open SqrtLog

def byteBound (n B d u J : ℕ) : ℕ :=
  u * J * (2 * (u + J + n) + 2 * (d * B) + 2)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorEvaluationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Immediate correction specialization keeps every factor dictionary over the
empty formal-variable support. The retained key capacity is polynomial u*J.
The bounds below apply to the actual native indicator, clause and product
programs, including their input parsers and paid tape cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace

open OAI
open SqrtLog

variable {p t n d : ℕ} [Fact p.Prime]


/-- All numerical arguments are encoded dimensions or polynomial retained
capacity. The exponent is fixed independently of every input. -/
def inputScale (B d n u J k m L : ℕ) : ℕ :=
  B + d + n + u + J + u * J + k + m + L + 1

def serviceBudget (B d n u J k m L : ℕ) : ℕ :=
  14000000 * (inputScale B d n u J k m L) ^ 9

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Space for one actual ambient-coordinate table construction. Its unary
traversal has only n iterations, so its polynomial local time bounds every
source prefix. No outer signature or finite-difference iteration count occurs
in this estimate. The concrete literal and staging traces are instantiated by
the factor-table producer, rather than supplied to a final counting endpoint. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace

open SqrtLog

open FactorTableProgram

/-- Includes the master's copy, all literal visits, output move and final halt. -/
def tableBudget (n K L : ℕ) : ℕ :=
  7 * n + n * (K + 2) + 6 * (n * (2 * n + 2 * L + 4)) + 16

/-- The middle store retains the old caller data and one polynomial table. -/
def middleBound (B n L : ℕ) : ℕ :=
  1029 * B + 99 + n * literalRecordBound n L

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical source preparation for the specialized factor table. The old
master-word argument is generalized to the actually selected unary factor,
then transported through the fixed protected-port embedding. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
open OAI
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.Subexp OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q d n J S f : ℕ}
  {ps : List (ℕ × ℕ)}

def specializedPayloadBound (n u J B d : ℕ) : ℕ :=
  u*J*(2*(u+J+n)+2*(d*B)+2)

def specializedRawBound (n u J B d : ℕ) : ℕ :=
  (1+n*(J-1)) * (2*(u+J+n)+2*(d*B)+2)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentLoop
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
open OAI SqrtLog

def byteBound (n B d u J : ℕ) : ℕ :=
  u * J * (2 * (u + J + n) + 2 * (d * B) + 2)

def uniformProductBudget (n B d u J T C : ℕ) : ℕ :=
  7 * T + 16 * byteBound n B d u J + (C + 17) * (T + 1) + 18

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighIncidenceProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The supplied high-coordinate odometer with a fixed-width exact accumulator.
The residual callback is an actual command; its interface is discharged by the
assembled query program. No branch family is stored on any source stack. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram

open OAI.Algorithms.SubexponentialSAT.BinaryArithmetic
open scoped BigOperators

variable {R S : ℕ}


/-- Residual indices increase with the original ambient identifier. The list
is obtained by filtering the actual finite coordinate list. -/
def freeCoordinates {n : ℕ} (H : Finset (Fin n)) : List (Fin n) :=
  (List.finRange n).filter (fun v => decide (v ∉ H))

theorem freeCoordinates_nodup {n : ℕ} (H : Finset (Fin n)) :
    (freeCoordinates H).Nodup := (List.nodup_finRange n).filter _

@[simp] theorem mem_freeCoordinates {n : ℕ} (H : Finset (Fin n)) (v : Fin n) :
    v ∈ freeCoordinates H ↔ v ∉ H := by simp [freeCoordinates]

def freeRawOrder {n : ℕ} (H : Finset (Fin n)) :
    Fin (freeCoordinates H).length ≃ {v : Fin n // v ∉ H} :=
  (List.Nodup.getEquiv (freeCoordinates H) (freeCoordinates_nodup H)).trans
    (Equiv.subtypeEquivRight (mem_freeCoordinates H))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_PairNativeSetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical pair traversal initialization and ambient-mask expansion. The
five low scratch ports325..329 are reclaimed before the caller returns; the
pair controller and persistent node/layout words are not scratch. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup
open OAI

def scratch : List (Fin 896) := [325,326,327,328,329]

def countRegister (i : Fin 3) : Fin 16 := i.castLE (by decide)
def countStack (i : Fin 2) : Fin 896 := if i = 0 then 325 else 326



def fillRegister (i : Fin 4) : Fin 16 := i.castLE (by decide)
def fillStack (i : Fin 4) : Fin 896 := ⟨325+i.val, by omega⟩
def fillInput (isE : Bool) : Fin 896 := if isE then 834 else 835
def fillOutput (isE : Bool) : Fin 896 := if isE then 858 else 857

def callerRegister (i : Fin 16) : Fin 40 := i.castLE (by decide)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NodeReadoutSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual node-array readout after all finite-difference pairs. The fixed
cleanup pays for transient lower words and clears the old output. Preserved
masters supply the coefficient zero vector and both truncation bounds. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace

open OAI SqrtLog
open TruncatedRingProgram

def registers : Fin 8 → Fin 40 := Fin.castAdd 32

/-- Shared inputs are restored by the original native readout. -/
def ports (i : Fin 40) : Fin 896 :=
  if i = 0 then 862 else if i = 5 then 5 else if i = 12 then 12
  else if i = 15 then 850 else if i = 24 then 39 else if i = 27 then 280
  else if i = 28 then 212 else if i = 29 then 243 else if i = 36 then 128
  else ⟨88 + i.val, by omega⟩

def scratchIndices : List (Fin 40) :=
  (List.ofFn (fun i : Fin 40 => i)).filter (fun i => decide
    (i ≠ 0 ∧ i ≠ 5 ∧ i ≠ 12 ∧ i ≠ 15 ∧ i ≠ 24 ∧ i ≠ 27 ∧
      i ≠ 28 ∧ i ≠ 29 ∧ i ≠ 36))

def scratchPorts : List (Fin 896) := scratchIndices.map ports

def clearPorts : List (Fin 896) := 862 :: scratchPorts

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryAdapter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete per-high-assignment setup and compressed head overlays.
The routines read physical counter/mask words and preserve ambient coordinates. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter

open OAI
open OAI.Algorithms.SubexponentialSAT.SqrtLog

def highRegs : Fin 4 → Fin 40 := Fin.castAdd 36
def highStacks : Fin 10 → Fin 896 := ![330,338,702,703,680,681,682,683,684,685]
def highChanged : List (Fin 896) := [702,703,680,681,682,683,684,685]

namespace NativeHeadSelect

def regs : Fin 4 → Fin 40 := Fin.castAdd 36
def stackMap : Fin 5 → Fin 896 := ![879,878,877,867,868]
def changed : List (Fin 896) := [867,868,877,878,879,880]

end NativeHeadSelect

namespace CanonicalHigh
open DisjointReuse

def regMap : Fin 3 → Fin 40 := Fin.castAdd 37
def stackMap : Fin 3 → Fin 896 := ![788,793,794]

end CanonicalHigh

namespace Overlay
def smallRegs : Fin 4 → Fin 8 := Fin.castAdd 4
def expandStacks : Fin 4 → Fin 12 := ![6,5,11,7]
def mergeStacks : Fin 10 → Fin 12 := ![9,1,2,3,4,5,6,7,8,10]

end Overlay

namespace NativeOverlay

def regMap : Fin 8 → Fin 40 := Fin.castAdd 32
def stackMap : Fin 12 → Fin 896 := ![859,670,869,870,871,872,873,874,875,876,145,877]
def changed : List (Fin 896) := [145,872,873,874,875,876,877]

end NativeOverlay


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete bit primitives for streamed finite-difference queries. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram

open OAI
open scoped BigOperators

def parity : List Bool → Bool → Bool
  | [], b => b
  | bit :: bits, b => parity bits (Bool.xor b bit)

/-- Shared leaf ABI for pair signs: preserve both masks and every suspended
signature frame, with output848 and a single scratch word849. -/
def pairRegisters : Fin 3 → Fin 40 := Fin.castAdd 37

def pairStacks : Fin 4 → Fin 896 := ![834, 835, 848, 849]

section SignedArray

attribute [local simp] Fin.coe_ofNat_eq_mod

open OAI.Algorithms.SubexponentialSAT.SqrtLog
open TruncatedRingProgram

/-- The forty arithmetic ports are disjoint from the preserved sign bit. -/
def scalePorts : Fin 40 → Fin 41 := Fin.castAdd 1

def signedScalingBudget (n B d u J : ℕ) : ℕ :=
  TruncatedRingProgram.scalingBudget n B d u J +
    6 * (u * J * (2 * (u + J + n) + 2 * (d * B) + 2)) + 9

/-- Physical arithmetic registers lie below the four suspended DFS flags. -/
def leafArithmeticRegs : Fin 8 → Fin 40 := Fin.castAdd 32

/-- Consume the current pair array on 851; the sign remains on 848. -/
def leafScalePorts (i : Fin 41) : Fin 896 :=
  if i = 32 then 851 else if i = 40 then 848 else ⟨i.val, by omega⟩

/-- Share the existing scalar parameters, consume scaled output 38, and
normalize into node accumulator 850. All other arithmetic scratch is below128. -/
def leafNormalizePorts (i : Fin 28) : Fin 896 :=
  if i = 5 then 5 else if i = 12 then 12 else if i = 24 then 39
  else if i = 15 then 850 else if i = 27 then 38 else ⟨100 + i.val, by omega⟩

end SignedArray

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleDFS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Attained-signature DFS cardinalities and work

A level is indexed by its attained signatures, not its Boolean assignments or
an ambient rectangular range of raw row values. These finite types describe
visits mathematically; no family or product is materialized by these definitions.
The native encoded-frame traversal is a separate refinement obligation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleDFS

open scoped BigOperators

/-- Partial tuples indexing invocations of the generator at the next level. -/
abbrev Prefix (A : ℕ → Type*) (depth : ℕ) := (i : Fin depth) → A i.val

/-- Number of partial tuples at a specified depth. -/
def prefixCount (K : ℕ → ℕ) (depth : ℕ) : ℕ :=
  ∏ i ∈ Finset.range depth, K i

@[simp] theorem prefixCount_zero (K : ℕ → ℕ) : prefixCount K 0 = 1 := by
  simp [prefixCount]

@[simp] theorem prefixCount_succ (K : ℕ → ℕ) (depth : ℕ) :
    prefixCount K (depth + 1) = prefixCount K depth * K depth := by
  exact Finset.prod_range_succ K depth

/-- One full invocation cost for each earlier emitted partial tuple. The
cost includes reset, unsuccessful predecessor scans, and generator cleanup. -/
def generatorWork (K cost : ℕ → ℕ) (levels : ℕ) : ℕ :=
  ∑ i ∈ Finset.range levels, prefixCount K i * cost i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleDFS
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Fixed-control interpreter for streaming signature tuples

The input-dependent depth is represented by an encoded stack of suspended
frames. `probe` tests one candidate against earlier assignments. A rejected
candidate advances at its current depth; only a fresh signature descends.
Thus this control table never traverses raw assignment tuples.

The subroutines are concrete finite commands, and all execution theorems use
their actual measured evaluations. Instantiating their frame, signature, and
counter invariants remains a separate native-program obligation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram

/-- Fixed Boolean control ports; all unbounded data live on bit stacks. -/
structure Ports (r : ℕ) where
  active : Fin r
  leaf : Fin r
  available : Fin r
  fresh : Fin r

/-- The shared leaf ABI reserves twelve fixed physical ports. Their order is
frames, representatives, candidate, key, payload, scratch, depth, limit,
predecessor, predecessor key, and two scratch buffers. -/
def tupleStacks : Fin 12 ↪ Fin 896 where
  toFun i := ⟨836 + i.val, by have := i.isLt; omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega

def frameRegisters : Fin 2 ↪ Fin 40 := Fin.castLEEmb (by decide)

/-- The four controller flags are preserved by the smaller native routines.
Callbacks using the full register bank must use the shared caller-save wrapper. -/
def controllerPorts : Ports 40 := ⟨36, 37, 38, 39⟩

/-- Two physical stack ports for a frame operation. -/
def wordPorts (src dst : Fin 896) (h : src ≠ dst) : Fin 2 ↪ Fin 896 where
  toFun i := if i = 0 then src else dst
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- These are the current generator's words. Suspended ancestors, emitted
representatives, remaining depth, and the physical head address are retained. -/
def currentHeadPorts : List (Fin 896) :=
  [tupleStacks 2, tupleStacks 3, tupleStacks 4, tupleStacks 5,
    tupleStacks 7, tupleStacks 8, tupleStacks 10, tupleStacks 11]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryAssembler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical assembly of the streamed query. Arithmetic caches are installed
from retained produced words by paid finite commands. These local theorems do
not assert completion of the node, pair, or tuple evaluator. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler

open OAI
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

def pairScratch : List (Fin 896) :=
  (List.finRange 56).map (Fin.castAdd 840) ++
    (List.finRange 28).map (fun i => (⟨100+i.val,by omega⟩ : Fin 896)) ++ [159,841,848,849]

open TruncatedRingProgram


/-! The interpolation-node cursor is the actual framed table emitted by the
ring producer. Its low-bank loader is embedded into the common leaf bank;
all high pair/tuple state is preserved by the injective port map. -/
namespace Nodes

def lowPort : Fin 768 → Fin 896 := Fin.castAdd 128

/-- Actual reset before each node. The old tuple markers and retained integer
cache destinations are cleared so repeated bootstrap copies cannot accumulate. -/
def nodeResetPorts : List (Fin 896) := [78,302,660,665,710,711,712,850,851]


end Nodes


/-! Native multiplication of one completed head sum into the tuple product.
The original accumulator is relocated only at its two persistent operands. -/
namespace TupleMultiply

def ports (i : Fin 768) : Fin 896 :=
  if i=67 then 853 else if i=151 then 852 else i.castAdd 128

end TupleMultiply

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleInit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete initialization of one attained-signature tuple product. The
multiplicative identity is built by the native cache routine, and every stale
output and borrowed word is cleared by an actual command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleInit

open OAI
open SqrtLog

def lowPorts : List (Fin 896) := List.ofFn (fun i : Fin 56 => i.castAdd 840)
def entryPorts : List (Fin 896) := lowPorts ++ [841]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleInit
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete unsigned tuple accumulation. The complete head product on852
is normalized into the pair accumulator851. Physical caches are copied from
retained masters and every native peripheral scratch word is paid for. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum

open OAI SqrtLog
open TruncatedRingProgram

def registers : Fin 8 → Fin 40 := Fin.castAdd 32

def ports (i : Fin 28) : Fin 896 :=
  if i = 5 then 5 else if i = 12 then 12 else if i = 24 then 39
  else if i = 15 then 851 else if i = 27 then 852 else ⟨100+i.val, by omega⟩

def scratchIndices : List (Fin 28) :=
  (List.ofFn (fun i : Fin 28 => i)).filter (fun i => decide
    (i ≠ 5 ∧ i ≠ 12 ∧ i ≠ 24 ∧ i ≠ 15 ∧ i ≠ 27))

def scratchPorts : List (Fin 896) := scratchIndices.map ports

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The attained-tuple traversal retains the actual query inputs and the
meaning of its current pair accumulator. These predicates contain word
identities and algebraic facts, with no execution or algorithm-service fields. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState

open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog
open Subexp.ConstructivePacking
open TruncatedRingProgram

/-- Immutable inputs throughout one tuple traversal. Derived per-head words,
the ambient representative baseline869, and the changing accumulator851 are
not members of this list. -/
def masterPorts : List (Fin 896) :=
  [78,128,129,130,131,132,133,134,135,136,138,139,140,141,
   194,201,202,203,204,207,209,211,212,243,256,280,281,
   300,301,302,305,307,320,322,338,640,641,642,647,
   700,701,702,703,704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,728,
   730,731,732,733,734,735,736,737,738,739,740,741,742,743,
   832,833,834,835,850,857,858,863]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The real initializer and paid cache setup establish the physical boundary
for the actual stored-ID fold. Bounds are fixed before that fold; the current
Good-empty-support seed is serialized on151, the unread suffix on150 and the
reversed original ID on149. No execution service is a field below. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary
open OAI
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open FactorAssignmentProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The fixed source masters read by the actual scalar table producer. -/
def scalarPorts : List (Fin 768) :=
  [194,202,203,201,204,145,280,207,78,128,243,138,703]

/-- The fixed layout/source masters read by the actual source-row producer. -/
def sourcePorts : List (Fin 768) :=
  [130,131,132,710,711,140,712,138,139,135,136,713,714,715,717,716,280,207,211,728]

/-- All retained words used at a factor boundary, including the original175
ID stream and actual857 correction word. -/
def retainedPorts : List (Fin 896) :=
  (scalarPorts ++ sourcePorts).map FactorTableProgram.basePort ++
    [175,212,281,700,701,702,704,705,706,707,708,857]

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowMismatchBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Bounds for the actual unary-range, mismatch-filter and type-extractor
programs used by the universal-row constructor. -/

namespace SubexponentialSAT.Subexp.UniversalRowMismatchBound

def mismatchBound (S : ℕ) : ℕ := 400 * S ^ 3

end SubexponentialSAT.Subexp.UniversalRowMismatchBound

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed polynomial bounds for the actual factor-table service. The scalar
allowance includes physical signed-word lengths; it never bounds the integer
value of an exponential modulus or numerator in unary. All ambient source
rows and every specialized incidence record are included. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.Subexp
open FactorTableNative

/-- Full normalized payload width, before inserting its framed table record. -/
def payloadEnvelope (S : ℕ) : ℕ := S*S*(2*(S+S+S)+2*S*(2*S)+2)

def specializationEnvelope (S : ℕ) : ℕ :=
  (3200000*(1000000000*3^10+64)^10)*(10*(S+1))^100

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_GuardedCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! A width-one compilation of Boolean programs, with empty pop guarded before
the primitive stack compiler. The output contract reads the entire tape. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler

open OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.StackCompiler OAI.Algorithms.SubexponentialSAT.StackMachine
open scoped BigOperators

abbrev State (r l : ℕ) := Fin l × (Fin r → Bool)

def guardedPop : Option Bool → Mutation Bool
  | none => .keep
  | some _ => .pop

def decoder (s : ℕ) : (i : Fin s) → List Bool → Option Bool := fun _ => List.head?

@[simp] theorem reindex_tapeCount {Q : Type} {t states : ℕ}
    (e : Q ≃ Fin states) (p : Controller Q t) : (reindex e p).tapeCount = t := rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual finite count-word positivity suffix. The counting body is integrated
separately; this suffix never interprets the least significant bit as SAT. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

def headerStacks : Fin 4 ↪ Fin 1220 where
  toFun := ![1218, 268, 267, 269]
  inj' := by decide

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FiniteFallback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Generic finite scanner selectively adapted from the reviewed canceled source
`CountingDraft/FiniteWordScanner.lean`; no obsolete endpoint or rate is imported.

Fixed finite control for bounded input prefixes and complete binary output words.
The transition table is chosen before any runtime input. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.Scanner


def BoundedWord (M : ℕ) := {word : List Bool // word.length ≤ M}

noncomputable instance boundedWordFintype (M : ℕ) : Fintype (BoundedWord M) :=
  Fintype.ofInjective
    (fun w => (⟨⟨w.val.length, by have := w.property; omega⟩, ⟨w.val, rfl⟩⟩ :
      (i : Fin (M + 1)) × List.Vector Bool i.val))
    (by
      intro a b h
      exact Subtype.ext (congrArg (fun v : (i : Fin (M + 1)) × List.Vector Bool i.val => v.2.val) h))

/-- `none` is a single overflow state. Bounded prefes occupy fixed finite control. -/
def boundedNext (M : ℕ) : Option (BoundedWord M) → Bool → Option (BoundedWord M)
  | none, _ => none
  | some pref, bit =>
      if h : pref.val.length < M then
        some ⟨pref.val ++ [bit], by simp; omega⟩
      else none

noncomputable def finiteOutputBound {Q : Type*} [Fintype Q] (out : Q → List Bool) : ℕ :=
  Finset.univ.sup fun q => (out q).length

theorem length_le_finiteOutputBound {Q : Type*} [Fintype Q]
    (out : Q → List Bool) (q : Q) :
    (out q).length ≤ finiteOutputBound out :=
  Finset.le_sup (f := fun q => (out q).length) (Finset.mem_univ q)



variable {qCount : ℕ}

/-- One fixed table contains the complete output word for each finite scanner state. -/
def labelCount (L : ℕ) : ℕ := qCount * (2 * L + 5)

def addr (L : ℕ) (q : Fin qCount) (i : ℕ) (hi : i < 2 * L + 5) :
    Fin (labelCount (qCount := qCount) L) := finProdFinEquiv (q, ⟨i, hi⟩)

def decode (L : ℕ) (label : Fin (labelCount (qCount := qCount) L)) :
    Fin qCount × Fin (2 * L + 5) := finProdFinEquiv.symm label

@[simp] theorem decode_addr (L : ℕ) (q : Fin qCount) (i : ℕ)
    (hi : i < 2 * L + 5) : decode L (addr L q i hi) = (q, ⟨i, hi⟩) :=
  Equiv.symm_apply_apply finProdFinEquiv _

def regs (value present : Bool) : Fin 2 → Bool :=
  fun i => if i = 0 then value else present

@[simp]theorem update_value (value present next : Bool) :
    Function.update (regs value present) 0 next = regs next present := by
  funext i
  fin_cases i <;> simp [regs]

@[simp]theorem update_present (value present next : Bool) :
    Function.update (regs value present) 1 next = regs value next := by
  funext i
  fin_cases i <;> simp [regs]

@[simp]theorem regs_false : regs false false = fun _ => false := by
  funext i
  simp [regs]

@[simp]theorem update_stack (before after : List Bool) :
    Function.update (fun _ : Fin 1 => before) 0 after = fun _ => after := by
  funext i
  fin_cases i
  simp

@[simp] theorem only_stack (word : List Bool) (i : Fin 1) :
    (if i = 0 then word else []) = word := by
  fin_cases i
  simp


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.Scanner

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback

open Scanner
open scoped BigOperators

/-- Only the scanner's two registers are reset; all dispatcher tapes survive. -/
def resetScannerRegs (regs : Fin 80 → Bool) : Fin 80 → Bool :=
  Function.update (Function.update regs 0 false) 1 false

/-- Finite saturated control for the fixed exceptional cutoff; no numeric
cutoff is stored in an input-dependent runtime array. -/
def cutoffNext (B : ℕ) (q : Fin (B + 2)) (bit : Bool) : Fin (B + 2) :=
  ⟨min (B + 1) (q.val + if bit then 1 else 0), by omega⟩

def cutoffOut (B : ℕ) (q : Fin (B + 2)) : List Bool := [decide (q.val ≤ B)]

def cutoffRegs : Fin 2 ↪ Fin 80 where
  toFun := ![75, 76]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashCandidateProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram

open OAI.Algorithms.SubexponentialSAT.SqrtLog

namespace Normalize

def arithmeticPorts : Fin 8 → Fin 12 := Fin.castAdd 4


end Normalize

namespace Leaf

open scoped BigOperators

def registers : Fin 8 → Fin 40 := Fin.castAdd 32

def loaderStacks : Fin 11 → Fin 896 :=
  ![768,769,770,771,772,773,774,775,776,778,779]

def normalizerStacks : Fin 12 → Fin 896 := Fin.castAdd 884

def lowPorts : List (Fin 896) := [0,1,2,3,4,5,6,7,8,9,10,11]

end Leaf

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The streamed strict argmin and its greedy invariant. Candidate indices describe
an iterator's successive callbacks; no list of candidates is constructed here.
The finite-program implementation must refine these recurrences. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedy

open scoped BigOperators

variable {R X : Type*}

/-- One cached-score update. Equal scores retain the earlier candidate. -/
def update (best : R × ℕ) (candidate : R) (score : ℕ) : R × ℕ :=
  if score < best.2 then (candidate, score) else best

/-- Result after the seed and the next `t` candidates have been evaluated. -/
def scan (evaluate : R → ℕ) (candidate : ℕ → R) : ℕ → R × ℕ
  | 0 => (candidate 0, evaluate (candidate 0))
  | t + 1 => update (scan evaluate candidate t)
      (candidate (t + 1)) (evaluate (candidate (t + 1)))

@[simp] theorem update_score (best : R × ℕ) (candidate : R) (score : ℕ) :
    (update best candidate score).2 = min best.2 score := by
  unfold update
  split_ifs with h
  · exact (Nat.min_eq_right (Nat.le_of_lt h)).symm
  · exact (Nat.min_eq_left (Nat.le_of_not_gt h)).symm

@[simp] theorem scan_score (evaluate : R → ℕ) (candidate : ℕ → R) (t : ℕ) :
    (scan evaluate candidate t).2 = evaluate (scan evaluate candidate t).1 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [scan, update]
    split_ifs <;> simp_all

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedy
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual fixed binary comparison/update used by the streaming selector.
Its queue port is a bounded iterator frame, not a list of candidate records. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram

open OAI.Algorithms.SubexponentialSAT.SqrtLog
open scoped BigOperators


namespace PadScore

def pads : Fin 3 → Fin 5 := ![2,0,3]

/-- The query owns the low scratch bank; the retained selector score and
fixed unary shape are outside it. All other selector stacks are framed. -/
def leafRegisters : Fin 8 → Fin 40 := Fin.castAdd 32

def leafStacks : Fin 5 → Fin 896 := ![769,818,0,1,2]

end PadScore

namespace Initialize

def registers : Fin 3 → Fin 40 := Fin.castAdd 37

def normalizeStacks : Fin 3 → Fin 896 := ![780,0,1]
def unaryStacks : Fin 3 → Fin 896 := ![781,0,1]


/-- Only the fixed nine-port argmin core is reset after its three prepared
parameters have been saved. History, formula, and count output are framed. -/
def corePorts : List (Fin 896) := [768,769,770,771,772,773,774,775,776]


/-- Physical construction of the one retained zero candidate. The depth
counter is copied from817; the canonical modulus780 determines chunk width. -/
def zeroStacks : Fin 6 → Fin 896 := ![1,778,0,780,2,3]

end Initialize

namespace NativeRound

/-- These are the fixed leaf ports, not an input-dependent bank allocation. -/
def registers : Fin 8 → Fin 40 := Fin.castAdd 32

def coreStacks : Fin 9 → Fin 896 := ![768,769,770,771,772,773,774,775,776]

def historyStacks : Fin 10 → Fin 896 := ![768,769,770,771,772,773,774,775,776,777]

/-- A fixed explicit budget pays the seed, every visit and advance, the
retained winner append, and the outer flag reset. -/
def roundBudget (attemptCost scoreWidth payloadWidth : ℕ) : ℕ :=
  attemptCost + (100 * (scoreWidth + payloadWidth + 1) + 1) +
    (2 ^ payloadWidth * (attemptCost + 100 * (scoreWidth + payloadWidth + 1) + 1 +
      7 * (2 * payloadWidth + 3) + 5) + 2) +
    (5 * payloadWidth + 2 * scoreWidth + 11) + 1

end NativeRound

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassAdapter
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

open SqrtLog

/-- The workspace omits exactly the five collector stacks 320,...,324. -/
def workPort (i : Fin 891) : Fin 896 :=
  if h : i.val < 320 then ⟨i.val, by omega⟩ else ⟨i.val + 5, by omega⟩

def valueInputSize (width : List Bool → ℕ) (records : List (List Bool)) : ℕ :=
  (records.map fun bits => bits.length + width bits + 1).sum

def valueBudget (queryCost width : List Bool → ℕ) (records : List (List Bool))
    (acc : List Bool) : ℕ :=
  4+(records.map queryCost).sum + records.length*(22*(acc.length+valueInputSize width records)+26)

def outputGrowth (width : List Bool → ℕ) (records : List (List Bool)) : ℕ :=
  (records.map fun bits => width bits+1).sum

variable {X Row : Type*} [Fintype X] {m : ℕ}

/-- The all-mark sum is canonicalized before it is padded for comparison. -/
def normalizeRegisters : Fin 3 ↪ Fin 40 := ⟨Fin.castAdd 37, Fin.castAdd_injective 3 37⟩
def normalizeStacks : Fin 3 ↪ Fin 896 := ⟨![322,323,324], by decide⟩

def referenceRegisters : Fin 10 → Fin 40 := Fin.castAdd 30
def referenceStacks : Fin 10 → Fin 896 := ![0,1,2,3,4,5,6,320,7,8]

open scoped BigOperators


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMarkedQueryAdapter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual per-mark staging and return adapters. Each reference is copied and
reversed into the frontend marker words. Each completed high-assignment count
is moved to the marked collector, with its temporary words reclaimed and parser
registers reset by real instructions. Fresh high-query setup remains mandatory. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedQueryAdapter

open SqrtLog

/-- These words are freshly created by the marker/high-query invocation and
must have been empty at its external entry. No shared-H assumption is used. -/
def cleanupPorts : List (Fin 896) :=
  [321,330,698,699,705,706,788,789,790,791,792,793,794]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighMarkedCleanup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
/-! Actual lower-workspace reclamation in the shared leaf ABI. Source masters,
collector, count and upper caller words are preserved by the paid cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
open OAI
open OAI.Algorithms.SubexponentialSAT.SqrtLog
def stackMap : Fin 768 → Fin 896 := Fin.castAdd 128

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMarkedReturn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete return from a completed marked high-assignment count. All fresh
query workspace is reclaimed, the complete count is moved to323, and the
collector parser registers are reset after cleanup. The compact boundary cap
is distinct from the transient query cap. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn

open SqrtLog
open HashMarkedQueryAdapter
open HashGreedyProgram.NativeRound

opaque upperPortsWrapped :
    {ports : List (Fin 896) //
      ports = (List.finRange 896).filter (fun i => decide (832 ≤ i.val ∧ i.val < 895))} :=
  ⟨(List.finRange 896).filter (fun i => decide (832 ≤ i.val ∧ i.val < 895)), rfl⟩

/-- This fixed range is the query-owned upper bank in the shared ABI. It is
opaque so unrelated proofs do not reduce the full finite instruction table. -/
def upperPorts : List (Fin 896) := upperPortsWrapped.1

/-- Kept words are exactly the collector sources, immutable lower sources,
and selector/caller words outside the high-counter and query banks. -/
def kept (i : Fin 896) : Bool := decide
  (i=320 ∨ i=322 ∨ i=700 ∨ i=701 ∨ i=707 ∨ i=708 ∨ i=709 ∨
    (744 ≤ i.val ∧ i.val < 788) ∨ (795 ≤ i.val ∧ i.val < 832) ∨ i=895)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadEvaluationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete correction-mask checking for a head rescan. This local routine
preserves its input masters and charges every stack at every source prefix. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate
open OAI

def keyRegisters : Fin 8 → Fin 16 := Fin.castAdd 8
def keyStacks : Fin 16 → Fin 32 := Fin.castAdd 16

def equalityRegisters : Fin 5 → Fin 16 := Fin.castAdd 11
def equalityStacks : Fin 6 → Fin 32 := ![14,1,16,3,4,5]

def correctionStacks : Fin 10 → Fin 32 := ![12,17,18,19,20,5,6,7,8,21]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
open OAI

def registers : Fin 16 → Fin 40 := Fin.castAdd 24
def stackMap : Fin 32 → Fin 896 := Fin.castAdd 864

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate

def widthPolynomial (B : ℕ) : ℕ := 1+B*(B+1+B)
def rowPolynomial (B : ℕ) : ℕ :=
  9*(B*(2*B+1))+7+(7*B+5)+2+
    ((B+1)*(200*(widthPolynomial B+2)^2+34)+9*widthPolynomial B+22+1)+
      8*(widthPolynomial B+1)+8
/-- A fixed degree-six polynomial charges the full raw matrix and key words. -/
def gatePolynomial (B : ℕ) : ℕ :=
  7*B+B*(rowPolynomial B+2)+20*(B*(2*(widthPolynomial B+1)+1))+38*B+60

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate

def bodyPolynomial (B : ℕ) : ℕ := HeadGate.gatePolynomial B+62*B+58

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The head rescan retains one raw Boolean assignment and a binary countdown.
The full-key/correction gate is executed for every candidate. Accepted values
are accumulated before the cursor advances, including the empty-head case. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram

open OAI


def powerRegisters : Fin 3 → Fin 40 := Fin.castAdd 37

def powerStacks : Fin 2 → Fin 896 := ![861, 860]


open OAI.Algorithms.SubexponentialSAT.SqrtLog
open TruncatedRingProgram

/-- Addition consumes the assignment product directly at854. The two
coefficient scratch ports avoid the retained product zero/table caches. -/
def additionRegisters : Fin 8 → Fin 40 := Fin.castAdd 32

def additionStacks (i : Fin 28) : Fin 896 :=
  if i = 15 then 853 else if i = 27 then 854 else if i = 24 then 39
  else if i = 17 then 883 else if i = 22 then 884 else Fin.castAdd 868 i

open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete head-sum assembly. The first head gate receives a physically
cleared arithmetic bank; persistent source parameters remain outside that bank.
Accepted assignments continue through dense addition and workspace reclamation,
including empty factor products and zero-valued products. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly

open OAI
open HeadEvaluationProgram.StagedGate

/-- These words are dead on head entry and owned by this rescan. -/
def controllerPorts : List (Fin 896) := [859, 860, 861, 883, 884]

/-- The fixed bank is kept opaque so elaboration never expands all of its
ports while checking generic trace lemmas. -/
opaque workPortsData :
    {ports : List (Fin 896) //
      ports = List.ofFn (fun i : Fin 56 => i.castAdd 840) ++ controllerPorts} :=
  ⟨List.ofFn (fun i : Fin 56 => i.castAdd 840) ++ controllerPorts, rfl⟩

/-- A fixed finite bank in the program syntax, independent of input size. -/
def workPorts : List (Fin 896) := workPortsData.1

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadAcceptedCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed accepted branch physically overlays the current assignment,
computes its whole specialized factor product, and adds that same dictionary
to the head sum. Its compact return cap is independent of its transient cost. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect

open OAI
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open FactorAssignmentProgram FactorAssignmentBoundary QueryTupleState
open HighQueryAdapter TruncatedRingProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- These actual caller words remain live throughout repeated candidates. -/
def framePorts : List (Fin 896) := masterPorts ++
  [175,650,651,670,671,836,837,838,839,840,841,842,843,844,845,846,847,
    851,852,859,860,861,864,865,866,867,868,869,883,884]

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed head-loader table uses the actual integer entry program. Its
physical matrix view follows LeafHeadSetupProgramHead/MatrixRun exactly, while
its controller emits one matrix and never constructs assignment tables. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog

def matrixInputs : List (Fin 768 × Fin 288) :=
  [(141,0),(650,17),(128,18),(651,23),
   (135,225),(136,226),(640,227),(641,228),(140,229),(642,230),
   (138,231),(139,232),(130,233),(131,234),(307,235),(132,236),(647,281)]

/-- Exactly the physical source words read by head selection and native
integer entries. Unrelated arithmetic scratch is deliberately excluded. -/
def masters : List (Fin 768) :=
  [128,129,130,131,132,133,134,135,136,138,139,140,141,307,640,641,642,647]

/-- Raw matrix output; the old bucket output21 is never selected. -/
def rawOutputs : List (Fin 288 × Fin 768) := [(24,669)]

def shiftRegs : Fin 8 → Fin 16 := Fin.castAdd 8
def shiftInputs : List (Fin 768 × Fin 17) := [(141,0),(669,14)]
def shiftOutputs : List (Fin 17 × Fin 768) := [(15,668)]

def retainedOutputBound (n N D B L : ℕ) : ℕ :=
  n * (2*n+2) + 2 + (2*N+2)*N + D*(12*n*(B+L)+6*n+1)

/-- The final leaf ABI reserves the high query controls; only16 registers are
used by the loader and its paid copies. -/
def leafRegs : Fin 16 ↪ Fin 40 := Fin.castAddEmb 24
def lowStacks : Fin 768 ↪ Fin 896 := Fin.castAddEmb 128

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadLoaderBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed polynomial bounds for the actual head loader from its retained
source words. Column time is derived from the native integer-entry program;
the outer loop's address is charged by its actual unary word length. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadLoaderBudgets

open OAI SqrtLog

/-- This constant is independent of the input and all runtime parameters. -/
def sizeCoefficient : ℕ := 10000000000000200


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadLoaderBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete tape operations and traversal assertions for the outer CRT.
All operations in this module are fixed finite programs. Arithmetic is supplied
by the separately defined concrete CRT service commands. -/

namespace SubexponentialSAT.SubexpCRTOuterProgram

/-- Horner's ten higher ports avoid the constants at 206, 207, and 211. -/
def hornerPort (i : Fin 87) : Fin 320 :=
  if i.val < 77 then ⟨128 + i.val, by omega⟩ else ⟨169 + i.val, by omega⟩

def hornerPorts : Fin 87 ↪ Fin 320 :=
  ⟨hornerPort, by
    intro i j h
    apply Fin.ext
    have hv := congrArg (fun x : Fin 320 => x.val) h
    by_cases hi : i.val < 77 <;> by_cases hj : j.val < 77 <;>
      simp only [hornerPort, hi, hj, ite_true, if_true, ite_false] at hv <;> omega⟩

@[simp] theorem hornerPorts_output : hornerPorts 72 = (200 : Fin 320) := rfl
@[simp] theorem hornerPorts_stream : hornerPorts 77 = (246 : Fin 320) := rfl
@[simp] theorem hornerPorts_point : hornerPorts 78 = (247 : Fin 320) := rfl
@[simp] theorem hornerPorts_count : hornerPorts 79 = (248 : Fin 320) := rfl
@[simp] theorem hornerPorts_blockWidth : hornerPorts 81 = (250 : Fin 320) := rfl

/-- These fields describe physical traversal stacks. Other stacks, including
the scalar bank and retained inputs, are framed by the execution theorems. -/
structure SweepWords where
  remaining : List Bool
  processed : List Bool
  index : List Bool
  accumulator : List Bool
  jets : List Bool
  current : List Bool := []
  nodeCopy : List Bool := []
  indexCopy : List Bool := []
  jet : List Bool := []

def sweepStore (frame : Fin 320 → List Bool) (w : SweepWords) (j : Fin 320) : List Bool :=
  if j = 213 then w.nodeCopy else
  if j = 216 then w.indexCopy else
  if j = 225 then w.jet else
  if j = 257 then w.remaining else
  if j = 258 then w.processed else
  if j = 259 then w.current else
  if j = 260 then w.index else
  if j = 261 then w.accumulator else
  if j = 266 then w.jets else frame j

@[simp] theorem sweepStore_nodeCopy (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 213 = w.nodeCopy := rfl

@[simp] theorem update_sweepStore_nodeCopy (f : Fin 320 → List Bool) (w : SweepWords)
    (bits : List Bool) :
    Function.update (sweepStore f w) 213 bits = sweepStore f {w with nodeCopy := bits} := by
  funext j
  by_cases h : j = (213 : Fin 320)
  · subst j; simp [sweepStore]
  · simp [sweepStore, h]

@[simp] theorem sweepStore_indexCopy (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 216 = w.indexCopy := rfl

@[simp] theorem update_sweepStore_indexCopy (f : Fin 320 → List Bool) (w : SweepWords)
    (bits : List Bool) :
    Function.update (sweepStore f w) 216 bits = sweepStore f {w with indexCopy := bits} := by
  funext j
  by_cases h : j = (216 : Fin 320)
  · subst j; simp [sweepStore]
  · simp [sweepStore, h]

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Explicit compact boundary, source and arithmetic caps for the actual head
sum. Their fixed polynomial certificates depend on source dimensions and
physical word lengths, independently of the number of head assignments. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open FactorTableBudgets

/-- The boundary accommodates existing words, a regenerated ring cache and
any specialized dictionary returned by a factor. -/
def compactCap (A : ℕ) : ℕ := A+4*A+6+payloadEnvelope A

def sourceCap (A : ℕ) : ℕ :=
  1029*compactCap A+99+A+A*FactorTableProgram.literalRecordBound A (payloadEnvelope A)+1

def arithmeticCap (A : ℕ) : ℕ :=
  1+compactCap A+A+2*A*A+FactorEvaluationSpace.inputScale (2*A) A A A A A A A

/-- Includes the physical staging cap as well as every ordinary source scalar. -/
def tableScalarCap (A : ℕ) : ℕ := A+sourceCap A+1029*compactCap A+99

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Correctness of the fixed head rescan. The invariant retains the current
normalized dictionary and the actual immutable source words. Its compact
boundary is reused after every candidate; no execution service is assumed. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative
open OAI SqrtLog
open TruncatedRingProgram HeadSumProgram
open QueryTupleState (masterPorts )
open scoped BigOperators

noncomputable section

/-- All words retained by one head, excluding its changing cursor and sum. -/
def retainedPorts : List (Fin 896) := masterPorts ++
  [175,650,651,670,671,836,837,838,839,840,841,842,843,844,845,846,847,
    851,852,864,865,866,867,868,869]

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighCountInit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid entry to one disjoint high-assignment count. Internal empty binary
words represent zero; the final CanonicalHigh routine emits canonical [false].
The high odometer is copied from the actual encoded seed, never reconstructed
from an assumed family of successful branch states. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountInit

open HighQueryAdapter

def changed : List (Fin 896) := [788,789,790,323,791,792]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountInit
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighCountSeed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Each marked count regenerates its own zero high-assignment odometer from
its current physical mask. No common high set or retained previous seed is
assumed. The original two-stack branch initializer is executed concretely. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed

open OAI HighQueryAdapter

def changed : List (Fin 896) := [330,791,792]
def regMap : Fin 2 → Fin 40 := Fin.castAdd 38
def stackMap : Fin 2 → Fin 896 := ![792,330]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTautologyFilterProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual tautological-clause filtering

The outer record loop runs the checked clause-tautology machine on each clause,
emits exactly the clauses that it rejects as tautologies, and restores their
original list order. The Boolean predicates below specify this concrete code;
they are not instructions available to the machine.
-/

namespace SubexponentialSAT.SubexpTautologyFilterProgram

def coreRegister (i : Fin 10) : Fin 13 := Fin.castAdd 3 i
def coreStack (i : Fin 8) : Fin 11 := ⟨i.val + 3, by omega⟩

def emitRegister (i : Fin 3) : Fin 13 := ⟨i.val + 10, by omega⟩

def emitStack (i : Fin 4) : Fin 11 :=
  match i.val with
  | 0 => 0
  | 1 => 3
  | 2 => 2
  | _ => 1

def reverseStack (i : Fin 4) : Fin 11 :=
  if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 0 else 1

end SubexponentialSAT.SubexpTautologyFilterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!+# Fixed-control encoded CNF normalization

The common boundary uses stack 13 for the formula and empty work stacks.
Literal cleanup and tautology removal are lifted into that boundary here;
clause deduplication and strict-subset deletion use the same boundary.
-/

namespace SubexponentialSAT.SubexpNormalizationProgram

def prefixRegister (i : Fin 13) : Fin 15 := Fin.castAdd 2 i
def prefixStack (i : Fin 11) : Fin 16 := ⟨13 - i.val, by omega⟩

@[simp] theorem prefixStack_zero : prefixStack 0 = 13 := rfl

end SubexponentialSAT.SubexpNormalizationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeTerminal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual outer-CNF terminal handling. The ambient unary header is retained;
an empty formula emits its full count 2^n, and an empty clause emits zero. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal

open scoped BigOperators

def classifierStacks : Fin 10 ↪ Fin 1220 :=
  (Fin.castAddEmb 1210).trans ((Equiv.swap (9 : Fin 1220) 265).toEmbedding)

@[simp] theorem classifierStacks_body : classifierStacks 9 = 265 := by decide

def powerRegs : Fin 2 ↪ Fin 80 where
  toFun := ![72, 73]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def powerStacks : Fin 2 ↪ Fin 1220 where
  toFun := ![268, 263]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

@[simp] theorem powerRegs_zero : powerRegs 0 = 72 := by decide

@[simp] theorem powerRegs_one : powerRegs 1 = 73 := by decide

@[simp] theorem powerStacks_zero : powerStacks 0 = 268 := by decide

@[simp] theorem powerStacks_one : powerStacks 1 = 263 := by decide

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryLocalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Source-only local costs for the physical high-count controller. Retained
caller words, including the outer marked accumulator322, do not enter them. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLocalBounds
open OAI HighQueryAdapter

def seedSources : List (Fin 896) := [323,330,338,788,789,790,791,792]

open HashGreedyProgram.NativeRound

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLocalBounds
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQueryPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete query packing and arithmetic preparation. Numeric and physical
input caps are kept separate from the subsequent exponential node traversal.
Every arithmetic object is returned by its actual native producer. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation

open OAI SqrtLog

/-- This fixed ordinary envelope pays for the complete packing and the
subsequent polynomial arithmetic phase. -/
def setupEnvelope (Cp dp Ca da S : ℕ) : ℕ :=
  let P := Cp * (790 * (S + 1)) ^ dp
  S + P + Ca * (S + P + 1) ^ da + 1

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLayoutLoad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid node-start loading of the parked source bank. Only the original
layout copy program is called; no head enumeration is imported or executed. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad

open OAI SqrtLog

def registers : Fin 16 → Fin 40 := Fin.castAdd 24
def stackMap : Fin 768 → Fin 896 := Fin.castAdd 128

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual node readout and loop continuation. The emitted coefficient stream
retains its order. Node temporaries are physically reclaimed before refreshing
the outer guard, and every completed node restores one fixed boundary bound. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish

open OAI SqrtLog
open TruncatedRingProgram

def touchedPorts : List (Fin 896) :=
  [5, 12, 39, 78, 307, 850, 862, 863] ++ NodeReadoutSpace.scratchPorts

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_ReconstructionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete CRT reconstruction and full-word modular readback. The same actual
native traces satisfy correctness, polynomial local time, and every-prefix
bounds on all source stacks, including the persistent caller frame. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace

open OAI SubexpCRTOuterProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog

/-- The normalizer uses the count port and two empty low scratch ports.
Modulus and width remain in their existing high ports. -/
def normalizationPorts : Fin 3 ↪ Fin 8 :=
  ⟨Fin.castAdd 5, Fin.castAdd_injective _ _⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual streamed-jet handoff, scratch preparation, and canonical count
reconstruction. Readiness is derived from the produced ring masters. The target
and jets are mathematical properties of the actual query output; no evaluator
or readiness service is accepted by the produced-input theorem. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction

open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog
attribute [local simp] Fin.coe_ofNat_eq_mod

def ringPorts : List (Fin 320) := [194,201,202,203,204,207,209,211,212,243,280]

/-- Full concrete recovery from the actual ring producer and node/jet words.
The same run pays both transfers, real scratch clearing, Hermite arithmetic,
canonical whole-word readback, and the relocated callee halt. -/
-- Actual ring and node masters needed by the next high-assignment query.
def retainedPorts : List (Fin 896) :=
  [194,201,202,203,204,207,209,211,212,243,256,280,281,300]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureKeyNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# One full integer signature on the leaf ABI

All port numbers here are leaf-local. The actual key-only machine preserves
the assignment, shifted matrix and every unrelated caller word; it has no
predecessor, countdown, or signature-table input.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative

def registers : Fin 8 ↪ Fin 40 := Fin.castLEEmb (by decide)

def stackPorts : Fin 16 ↪ Fin 896 where
  toFun i := ⟨if i.val = 0 then 141 else if i.val = 12 then 838 else
    if i.val = 14 then 866 else if i.val = 15 then 847 else 340 + i.val, by
      split_ifs <;> have hi := i.isLt <;> omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    have hv := congrArg Fin.val hij
    dsimp at hv
    split_ifs at hv <;> omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadPrepare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid setup for one visited signature head. The physical key workspace,
old master words and selector outputs are cleared by the command itself. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepare

open HighQueryAdapter

def cleared : List (Fin 896) :=
  [341,342,343,344,345,346,347,348,349,350,351,353,866,841]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepare
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleLoadCommand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed loader call shared by the tuple syntax and its proof. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader

/-- The stack address holding the DFS's current physical head. -/
def headAddress : Fin 896 := 845

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleTraversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Cursor semantics for the attained-signature tuple controller

The cursor stores an attained prefix and one numeric candidate. Suspended
ancestors are first occurrences, so the tree branches over attained keys only.
The traces and finite sums below are mathematical specifications; the actual
controller retains neither a trace nor a family of assignments or tuples.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal

open scoped BigOperators
open SignatureTupleDFS

open Classical

variable {N : ℕ → ℕ} {κ : ℕ → Type*}

section AttainedLabels

variable {G : Type*} {A L : G → Type*} [∀ g, Fintype (A g)] [∀ g, DecidableEq (L g)]

def rangeEnumerateEquiv {count : G → ℕ}
    (enumerate : ∀ g, Fin (count g) ≃ A g) (label : ∀ g, A g → L g) (g : G) :
    Set.range (fun i ↦ label g (enumerate g i)) ≃ Set.range (label g) where
  toFun y := ⟨y.val, by
    obtain ⟨i, hi⟩ := y.property
    exact ⟨enumerate g i, hi⟩⟩
  invFun y := ⟨y.val, by
    obtain ⟨a, ha⟩ := y.property
    exact ⟨(enumerate g).symm a, by simpa using ha⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

end AttainedLabels

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Concrete adapters for the attained-signature tuple controller

The cursor primitives are fixed in `SignatureTupleProgram`. This module
installs the actual head loader and predecessor predicate on the shared leaf
ABI, and relates their physical state to the attained-prefix traversal.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative

open SignatureTupleProgram

/-- The scratch bank is disjoint from the retained ring tables and metadata.
Only the five named persistent source fields are mapped outside340..363. -/
def rescanStacks : Fin 24 ↪ Fin 896 where
  toFun i :=
    ⟨if i.val = 0 then 141 else if i.val = 15 then 847 else
      if i.val = 16 then 838 else if i.val = 17 then 839 else
      if i.val = 18 then 844 else 340 + i.val, by
        split_ifs <;> have hi := i.isLt <;> omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    have he := congrArg Fin.val hij
    dsimp at he
    split_ifs at he <;> omega

def rescanRegisters : Fin 16 ↪ Fin 40 := Fin.castLEEmb (by decide)

@[simp] theorem rescanStacks_offset : rescanStacks 0 = 141 := rfl
@[simp] theorem rescanStacks_matrix : rescanStacks 15 = tupleStacks 11 := rfl
@[simp] theorem rescanStacks_candidate : rescanStacks 16 = tupleStacks 2 := rfl
@[simp] theorem rescanStacks_key : rescanStacks 17 = tupleStacks 3 := rfl
@[simp] theorem rescanStacks_predecessor : rescanStacks 18 = tupleStacks 8 := rfl
@[simp] theorem rescanStacks_fresh : rescanStacks 22 = 362 := rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed finite syntax for both marked and final accepted queries. The only
program parameter is the fixed clause width. Every mark regenerates its own
physical high mask and zero counter. The semantic proof must establish that
the actual frontend guard holds on every reachable input. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram

open OAI HighQueryAdapter
noncomputable section

open HashGreedyProgram.NativeRound

namespace Carried

/-- Exactly the five words left unrestricted by the greedy query-time
quantifiers. Their bytes cannot affect this fixed query's control flow. -/
def words : Finset (Fin 896) := {320,322,770,771,781}

end Carried

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual entry to each high-assignment count. The current frontend mask
survives concrete packing/arithmetic and drives the fixed zero-seed program.
The compact returned boundary is separate from the transient prefix bound. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart

open OAI SqrtLog
open HashGreedyProgram.NativeRound

def changed : List (Fin 896) := [330,788,789,790,323,791,792]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQuerySetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete preparation and fresh high-counter initialization for the fixed
marked and accepted queries. The witness below is produced by the actual
programs; no implementation or evaluator is supplied as a hypothesis. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup

open OAI SqrtLog
open HashGreedyProgram.NativeRound
open HighMarkedFrontend

def localBound (S cost : ℕ) : ℕ := S + cost + 1

structure SeedData where
  seedSteps : ℕ
  seedRegs : Fin 2 → Bool

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete head reloads for the attained-signature DFS.  The matrix comes
from the fixed native integer-entry machine, and each reload restores one
fixed retained-word bound before the next candidate scan. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog
open SignatureTupleProgram SignatureTupleNative

/-- Both the time and every-prefix loader storage are bounded by one fixed
input polynomial. This envelope is transient and is never the next F. -/
def runEnvelope (B F : ℕ) : ℕ :=
  1000*(10000000000000000*HeadLoaderBudgets.sizeCoefficient^8+3)*(F+B+2)^64

section Storage
open SignatureTupleDFS SignatureTupleTraversal


/-- One fixed input polynomial bounds both the candidate scanner's retained
key and its transient space. The numerical candidate value is absent. -/
def scannerEnvelope (B : ℕ) : ℕ := 100000*(20000*(B+2)^6)^6

end Storage

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryReadyConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete query-entry facts from the actual arithmetic and native cache
producers. Pair masks are installed by the paid pair-start command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction

open OAI SqrtLog
open QueryTupleState
attribute [local simp] Fin.coe_ofNat_eq_mod

def commonPorts : List (Fin 896) :=
  [78,128,130,131,132,135,136,138,139,140,194,201,202,203,204,207,211,212,243,280,281,700,701,702,703,704,705,706,707,708,710,711,712,713,714,715,716,717,728]

/-- Only these actual arithmetic producer outputs are needed at node entry. -/
def arithmeticPorts : List (Fin 768) :=
  [194,201,202,203,204,207,211,212,243,280,281,713,714,715,716,717,728]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorLoad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid reverse-head reload for the two-pass query visitor. The same native
run returns every integer row, preserves the suspended query data, and restores
a fixed retained word cap before the next head. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog

/-- Both the time and every-prefix loader storage are bounded by one fixed
input polynomial. This envelope is transient and is never the next F. -/
def runEnvelope (B F : ℕ) : ℕ :=
  1000*(10000000000000000*HeadLoaderBudgets.sizeCoefficient^8+3)*(F+B+2)^64

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorLoadBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Source-parameter bounds for the full key produced from an actual shifted
incidence matrix. Every incidence row and every retained coefficient is charged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds

open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog

/-- Serialized full matrix, with the actual incidence count `D`. -/
def matrixBound (n D B L : ℕ) : ℕ := D*(12*n*(B+L)+6*n+1)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorHead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The concrete one-head visitor composes its actual loader, paid key setup,
restricted head rescan and tuple multiplication. Exponential work is kept
separate from the reusable boundary and all-prefix storage bounds. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead
open OAI SqrtLog
open TruncatedRingProgram
open QueryTupleState
open scoped BigOperators
noncomputable section

/-- Controller words and the full representative baseline survive one head. -/
def retainedPorts : List (Fin 896) :=
  [836,837,838,839,840,842,843,844,845,846,847,851,864,865,866,867,868,869]

/-- These replay words are immutable while the current head product changes. -/
def controlPorts : List (Fin 896) :=
  [836,837,838,839,840,842,843,844,845,846,847,851,869]

def visitorPorts : List (Fin 896) := [836,837,838,839,840,842,843,844,845,851,869]

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryHeadBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! A concrete numerical HeadBounds certificate for the actual visitor.
Source columns are bounded from its stored native input, all incidence rows
remain present, and the compact endpoint cap is separate from transient space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets
open OAI
open SqrtLog
open HeadSumBudgets FactorTableBudgets

/-- Includes the actual column-length bound obtained from the stored source. -/
def sourceSize (A : ℕ) : ℕ := (A+1)*(100*(A+2)^2+2)+A+1

def scalarCap (A : ℕ) : ℕ := 1000100*(sourceSize A+1)^10

def compact (A : ℕ) : ℕ := compactCap (scalarCap A)
def source (A : ℕ) : ℕ := sourceCap (scalarCap A)
def arithmetic (A : ℕ) : ℕ := arithmeticCap (scalarCap A)

/-- Actual post-head multiplication, including all dictionary arithmetic. -/
def multiplyEnvelope (A : ℕ) : ℕ :=
  51000*(compact A+1)+4000000*(6*A+1)^10

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete execution of the two representative passes. The saved frame
stack is traversed in place, and every semantic dictionary is the one written
by the actual arithmetic command. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog
open TruncatedRingProgram
open QueryTupleState SignatureTupleProgram


section Product
open scoped BigOperators
variable {R : Type*} [CommMonoid R] {r : ℕ}

/-- Proof-level product of the heads that the decreasing replay has not yet
visited. This indexes only the already emitted tuple. -/
def headPrefix (value : Fin r → R) (remaining : ℕ) : R :=
  ∏ g ∈ Finset.univ.filter (fun g : Fin r => g.val < remaining),value g

@[simp] theorem headPrefix_zero (value : Fin r → R) : headPrefix value 0=1 := by
  simp [headPrefix]

@[simp] theorem headPrefix_full (value : Fin r → R) : headPrefix value r=∏ g,value g := by
  simp [headPrefix]

end Product


open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete cursor invariants for the fixed attained-signature controller.
The integer head matrices come from native source words.  Each boundary uses
one retained cap; reload and predecessor-scan prefix bounds remain transient.
-/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete

open Classical
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram
open SignatureTupleNative SignatureTupleLoader


/-- Persistent query words are disjoint from the loader scratch, current
head descriptors and tuple controller. This includes all ring caches, masks,
formula words and the pair accumulator; low649 is tracked separately. -/
structure PersistentPort (i : Fin 896) : Prop where
  outsideWork : (i.val < 340) ∨ (628 ≤ i.val)
  head : i∉([649,650,651,652,659,668,669,670,671] : List (Fin 896))
  tuple : ∀ j : Fin 12,i≠tupleStacks j

/-- A single cap chosen before traversal pays both persistent frame banks,
all native head arrays and every scanner key. -/
def retainedEnvelope (B A : ℕ) : ℕ :=
  A+scannerEnvelope B+10000*(B+2)^6+6*B*(B+1)+(B*B+B)+(B+1)+1

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryPairEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual finite-difference callback uses the physical pair masks and
one semantic node accumulator. The reference support decoding below is used
only in the proof; the executed controller retains its four finite words. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation

open OAI SqrtLog
open QueryTupleState QueryReadyConstruction
open scoped BigOperators

/-- The outer support represented by a finite ternary word. -/
def outer (N : ℕ) (word : List (Option Bool)) : Finset (Fin N) :=
  Finset.univ.filter (fun i => (word.getD i.val none).isSome)

/-- The inner support consists precisely of the `some true` positions. -/
def inner (N : ℕ) (word : List (Option Bool)) : Finset (Fin N) :=
  Finset.univ.filter (fun i => (word.getD i.val none).getD false)

/-- This is the additive semantic update performed after the complete tuple
product has been read out. The sign is computed from the actual two supports. -/
def visit {R : Type*} [CommRing R] (N : ℕ)
    (value : Finset (Fin N) → Finset (Fin N) → R)
    (word : List (Option Bool)) (total : R) : R :=
  total+(-1)^((outer N word).card-(inner N word).card)*
    value (outer N word) (inner N word)

/-- Physical words retained across each complete pair, in addition to the
source and ring masters. These include the current node cursor and address. -/
def framePorts : List (Fin 896) :=
  [194,201,202,203,204,207,209,211,212,243,256,280,281,300,301,307,320,322,338,649,
    700,701,702,703,704,705,706,707,708,709,713,714,715,716,717,718,719,728,
    730,731,732,733,734,735,736,737,738,739,740,741,742,743,863]

def startBudget (n F : ℕ) : ℕ := 300*(F+n+1)+2*F+5

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QuerySourceSnapshot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! A proof-only native source snapshot retains the actual readiness words.
It does not clear the running machine. The loader starts from the same native
input and generated cache, so all of its eighteen masters remain identical.
Unrelated scratch from earlier nodes is excluded from the source-local cap. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySourceSnapshot
open OAI SqrtLog

/-- These are exactly the source fields inspected by `Native.Ready`.
The four high loader masters are generated by `Native.start`. -/
def retainedPorts : List (Fin 768) :=
  [128,129,130,131,132,133,134,135,136,138,139,140,141,307,660,665]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySourceSnapshot
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete initialization of a node evaluation. The paid node read, layout
load, native cache bootstrap and pair setup are the fixed commands used by the
streaming query; no evaluator is supplied to these constructions. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation

open OAI SqrtLog
open QueryTupleState

/-- All interpolation arithmetic and frontend words in this list are kept
through the concrete node prefix. The three cache outputs are accounted for
separately because they are regenerated for this node. -/
def framePorts : List (Fin 896) :=
  [194,201,202,203,204,207,209,211,212,243,256,280,281,300,307,320,322,338,
    700,701,702,703,704,705,706,707,708,709,713,714,715,716,717,718,719,728,
    730,731,732,733,734,735,736,737,738,739,740,741,742,743,863]

def cacheInputPorts : List (Fin 896) :=
  [194,201,202,203,204,207,211,212,243,280,281,730]

open scoped BigOperators


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Polynomial overhead and prefix space for the complete actual tuple
visitor. The number of heads and the proved maximum head-size exponent stay
explicit; the empty-head/empty-tuple term is retained. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorBudgets
open OAI SqrtLog

/-- Actual final readout and tuple-accumulator addition. -/
def tailEnvelope (A : ℕ) : ℕ :=
  75*QueryHeadBudgets.compact A+97+3000000*(6*A+1)^10

def baselineEnvelope (A : ℕ) : ℕ :=
  QueryVisitorLoad.runEnvelope A (QueryHeadBudgets.compact A)+90*QueryHeadBudgets.compact A+89

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TupleRunBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The same compact endpoint cap supports the actual tuple controller and
its visitor. Transient scanner/reload work is bounded separately; none of it
is fed back into the retained frame cap between pairs. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets
open SignatureTupleComplete SignatureTupleLoader

/-- Source event overhead and all-prefix space, separately from the number
of candidates, attained tuples and callback visits. -/
def eventEnvelope (A : ℕ) : ℕ :=
  scannerEnvelope A+SignatureTupleLoader.runEnvelope A (QueryHeadBudgets.compact A)+
    4000*(QueryHeadBudgets.compact A+1)+200*QueryHeadBudgets.compact A+200

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StreamedQueryMeasuredCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The measured callback pays native mask setup, the complete attained-tuple
run (including ascent), and the signed commit. Its finite-difference iterator
is compared to the original explicit resource record with one fixed power. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost

open OAI SqrtLog
open SignatureTupleTraversal SignatureTupleDFS
open scoped BigOperators

/-- A polynomial envelope for the actual signed scaler, dense addition,
two mask scans, environment setup and cleanup. -/
def commitEnvelope (A : ℕ) : ℕ :=
  51000*(QueryHeadBudgets.compact A+1)+20*A+6000000*(6*A+1)^10+
    6*(A*A*(2*(A+A+A)+2*(A*(2*A))+2))+30

def localEnvelope (A : ℕ) : ℕ :=
  QueryPairEvaluation.startBudget A (QueryHeadBudgets.compact A)+commitEnvelope A

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryStreamCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical boundaries of the fixed conditioned query. The node invariant
retains the actual prepared words and the exact length of the emitted stream;
it contains no execution or evaluator fields. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect

open OAI SqrtLog

/-- The measured polynomial prefix precedes every actual pair traversal. -/
def prepareBudget (A : ℕ) : ℕ :=
  20000*(QueryHeadBudgets.compact A+1)^4+300*(QueryHeadBudgets.compact A+1)

def retainedPorts : List (Fin 896) :=
  QueryNodeEvaluation.framePorts.filter (fun i => i≠307 ∧ i≠863)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The persistent physical boundary for the actual high-assignment loop.
The ring, source and parked layout words are produced once for this query and
retained across each rank. No execution or evaluator is part of this invariant. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount

open OAI SqrtLog
open HighQueryAdapter

/-- The node index, coefficient stream and decoded current-high assignment
are regenerated at each rank; the remaining prepared words are unchanged. -/
def preparedPorts : List (Fin 896) :=
  QueryNodeEvaluation.framePorts.filter
    (fun i => i≠307 ∧ i≠863 ∧ i≠702 ∧ i≠703)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual whole-query composition after the high iterator. The two joins
below consume the fixed iterator's measured execution, preserve the same
prepared witnesses, and execute the existing complete return and cleanup.
The public marked and accepted theorems instantiate HighQueryCount directly. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect

open HighMarkedFrontend HighQuerySetup
open HashGreedyProgram.NativeRound

def markedBudget (frontCost S cost loopCost D : ℕ) : ℕ :=
  frontCost + cost + 110 * localBound S cost + loopCost + 3421 * D + 5218

def acceptedBudget (frontCost S cost loopCost D : ℕ) : ℕ :=
  frontCost + cost + 110 * localBound S cost + loopCost + 3430 * D + 5229

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SparseCodeSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch

def setupPorts : Fin 4 ↪ Fin 48 := ⟨![46, 43, 40, 45], by decide⟩

def timeBudget (d B T C : ℕ) : ℕ :=
  4 ^ d * (T + 7 * (B + C) + 10 + 42 * d + 12) + 3 + 15 * d + 4 * B + 17

def spaceBudget (d B C : ℕ) : ℕ :=
  48 * B + 15 * d + max (56 * (B + C) + 10) (48 * B + 7 * (6 * d + 1) + 4) + 4 * B + 17


open OAI.Algorithms.SubexponentialSAT.SqrtLog

def boundary (A dimension : ℕ) : ℕ := A + 6 * dimension + 1


/-- Fixed injection into the original leaf bank; high metadata, selected rows,
and the leaf controller's upper Boolean registers remain caller-owned. -/
def leafRegisters : Fin 16 → Fin 40 := Fin.castAdd 24

def leafStacks : Fin 48 → Fin 896 := Fin.castAdd 848

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed physical stages for the streamed local-code and graph-code searches.
The retained search state is confined to the lower48 leaf stacks; selected
matrices are saved outside that bank before its paid cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode

open SqrtLog

opaque lowerPortsWrapped :
    {ports : List (Fin 896) // ports = (List.finRange 48).map (Fin.castAdd 848)} :=
  ⟨(List.finRange 48).map (Fin.castAdd 848), rfl⟩

/-- The fixed lower-bank ports, kept opaque to prevent routine theorem
checking from reducing the complete cleanup program. -/
def lowerPorts : List (Fin 896) := lowerPortsWrapped.1

def registers : Fin 16 ↪ Fin 40 := Fin.castAddEmb 24

def stackMap : Fin 48 ↪ Fin 896 := Fin.castAddEmb 848

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeFrontend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

def normalizationRegisters : Fin 15 ↪ Fin 80 := Fin.castAddEmb 65

def normalizationStacks : Fin 16 ↪ Fin 1220 where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 1218, 14, 15]
  inj' := by decide

def unaryStacks : Fin 2 ↪ Fin 1220 where
  toFun := ![1218, 258]
  inj' := by decide


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual physical preparation of the streamed greedy selector. The final
suffix clears the argmin bank, preserves the serialized code history, and
constructs the single retained zero candidate using the runtime depth word. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation

open SqrtLog
open HashGreedyProgram

def finishTime (depth L : ℕ) : ℕ :=
  29 * L + 41 + 100 * (depth + 1) * (3 * L + 1)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_ScheduleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual binary construction of the disjoint-sparsification parameter.
All arithmetic uses fixed finite programs; the input numeral is runtime stack data. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ScheduleProgram

open BinaryArithmetic (toNat)

def resetRegs (r : Fin 8 → Bool) : Fin 8 → Bool :=
  Function.update (Function.update (Function.update r 0 false) 1 false) 2 false

def clogStacks (port : Fin 32) : Fin 3 → Fin 32 := ![port, 6, 7]

def work5 : Fin 5 ↪ Fin 32 := (Fin.natAddEmb 6).trans (Fin.castAddEmb 21)
def work6 : Fin 6 ↪ Fin 32 := (Fin.natAddEmb 6).trans (Fin.castAddEmb 20)
def work13 : Fin 13 ↪ Fin 32 := (Fin.natAddEmb 6).trans (Fin.castAddEmb 13)

/-- Six persistent local words; every local work stack is empty at boundaries. -/
def slots (words : Fin 6 → List Bool) : Fin 32 → List Bool :=
  fun i => if h : i.val < 6 then words ⟨i.val, h⟩ else []

@[simp] theorem slots_low (words : Fin 6 → List Bool) (i : Fin 6) :
    slots words (Fin.castAdd 26 i) = words i := by
  simp [slots, i.isLt]

@[simp] theorem slots_work5 (words : Fin 6 → List Bool) (i : Fin 5) :
    slots words (work5 i) = [] := by
  unfold slots
  split_ifs with h
  · have hv : (work5 i).val = 6 + i.val := rfl
    omega
  · rfl

@[simp] theorem slots_work6 (words : Fin 6 → List Bool) (i : Fin 6) :
    slots words (work6 i) = [] := by
  unfold slots
  split_ifs with h
  · have hv : (work6 i).val = 6 + i.val := rfl
    omega
  · rfl

@[simp] theorem slots_work13 (words : Fin 6 → List Bool) (i : Fin 13) :
    slots words (work13 i) = [] := by
  unfold slots
  split_ifs with h
  · have hv : (work13 i).val = 6 + i.val := rfl
    omega
  · rfl

def initialWords (input : List Bool) : Fin 6 → List Bool := ![input, [], [], [], [], []]

/-- Fixed pre-DFS bank: input n267, retained schedule s266; remaining local ports
use their unchanged low indices. All off-bank caller data are framed. -/
def sharedStacks : Fin 32 ↪ Fin 1220 :=
  (Fin.castAddEmb 1188).trans
    ((Equiv.swap (0 : Fin 1220) 267).toEmbedding.trans
      (Equiv.swap (5 : Fin 1220) 266).toEmbedding)

@[simp] theorem sharedStacks_input : sharedStacks 0 = 267 := by
  decide

@[simp] theorem sharedStacks_output : sharedStacks 5 = 266 := by
  decide

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ScheduleProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeSetupSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete canonical startup through the disjoint sparsification parameters.
The only large-instance premises concern the numeric schedule. All parsing,
normalization, arithmetic, clearing, and caller storage belong to one run. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BinaryArithmetic

def budgetStacks : Fin 32 ↪ Fin 1220 :=
  (Fin.castAddEmb 1188).trans
    ((Equiv.swap (0 : Fin 1220) 266).toEmbedding.trans
      ((Equiv.swap (1 : Fin 1220) 259).toEmbedding.trans
        (Equiv.swap (2 : Fin 1220) 264).toEmbedding))

@[simp] theorem budgetStacks_zero : budgetStacks 0 = 266 := by decide
@[simp] theorem budgetStacks_one : budgetStacks 1 = 259 := by decide
@[simp] theorem budgetStacks_two : budgetStacks 2 = 264 := by decide

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeOuter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed outer instruction sequence composes actual parameter setup,
disjoint counting DFS, and full-word positivity. The existing concrete-leaf
contract remains an explicit development obligation, not a final endpoint. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open DisjointReuse

def outerBoundary (inputBound bound n : ℕ) : ℕ :=
  max inputBound (1224 * bound + 7 * n + 19)

def outerSpace (inputBound bound n : ℕ) : ℕ :=
  1232 * outerBoundary inputBound bound n + 15

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeOuterBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The exact large-entry arithmetic join: paid canonical frontend, fixed
cutoff test, actual setup, disjoint DFS, full-word positivity and factor-seven
primitive compilation. These numerical bounds introduce no run contract. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets
open OAI SqrtLog.Statement DisjointReuse

/-- Each actual source phase is lifted to one bound, once. -/
def entrySpace (n L inputBound bound : ℕ) : ℕ :=
  max (L+4000*(L+1)^2)
    (max (1224*(L+1)+10*n+28) (Native.outerSpace inputBound bound n))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQueryInputBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed input-length bounds for the literal trial and accepted query
preparations. The common bound is produced before the greedy loop; none of
these caps contains a suspended caller word or a repeated-node scratch cap. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds

open SqrtLog DisjointReuse
open NativeQueryPreparation

/-- One source allowance covers the actual marked entry and both canonical
numeric and physical parameter words. All coefficients are fixed first. -/
def sourceCap (Cn dn Cl dl N L k : ℕ) : ℕ :=
  3 * L + 2 + Cn * (N + 1) ^ dn + Cl * (L + k + 1) ^ dl

/-- Both literal frontends fit this source-only cost. -/
def frontendCap (Cf df L k : ℕ) : ℕ :=
  10 * (L + 1) + Cf * (L + k + 1) ^ df + 12

/-- This is the actual Setup.localBound after the frontend and preparation,
with its fixed preparation coefficient and degree. -/
def preparedCap (Cp dp Cn dn Cl dl Cf df N L k : ℕ) : ℕ :=
  let A := sourceCap Cn dn Cl dl N L k + frontendCap Cf df L k
  HighQuerySetup.localBound A (Cp * (A + 1) ^ dp)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryStreamSpaceBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed polynomial space for the actual complete conditioned query.
Retained words and local arithmetic work are counted independently of the
number of support pairs, attained signatures, head assignments or nodes. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamSpaceBudgets
open OAI SqrtLog

/-- The actual node readout, ordered append, cleanup and next-index work. -/
def finishEnvelope (F X : ℕ) : ℕ :=
  29*F+27+(41*(2*F+3)+30000*(6*X+1)^6+1)+
    6*(F+X*(X*(2*X)))+9+4*F+10

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamSpaceBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQuerySpaceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Polynomial space for the actual complete marked and accepted queries.
The input cap is the same immutable leaf bound used by preparation. The
conditioned stream, high loop and whole-word return use their own proved
prefix bounds; no query runtime or number of attained tuples enters space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQuerySpaceBounds

open SqrtLog NativeQueryInputBounds

/-- A fixed polynomial sum dominates the nested physical prefix maxima. -/
def envelope (C e W : ℕ) : ℕ :=
  1000*(W+1)+1000*C*(30*(W+1))^e

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQuerySpaceBounds
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQueryTimeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Time bounds for the same actual source/prepared caps used by the literal
query provider. The resource record supplies the combinatorial exponent;
its ordinary fields are not asserted to measure the actual physical phases.
Frontend, preparation, seed and return work are paid separately below. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds

open SqrtLog SqrtLog.Statement NativeQueryInputBounds

/-- One physical allowance for every scalar in the actual high-loop budget. -/
def physicalCap (Cp dp Cn dn Cl dl Cf df N L k : ℕ) : ℕ :=
  let S := sourceCap Cn dn Cl dl N L k
  let F := frontendCap Cf df L k
  let P := preparedCap Cp dp Cn dn Cl dl Cf df N L k
  30*(S+F+P+4*N+6+1)+QueryHeadBudgets.compact (12*P+4*N+6)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds
end


