-- Prove2me | Definitions.Def_OAIQ081S043
-- name    : OAIQ081S043
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:34:55.393991+00:00
-- url     : https://prove2.me/theorems/5e029f87-fbea-48c7-ba9c-1faac610b773
-- title:
--   Definitions bundle OAIQ081S043 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 212 declarations of OpenAI's Lean: 169 definitions, 5 inductive types or structures, 2 instances and 36 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamily.coeffMap`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram.roundRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CopySpace.copyWeight`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget.chooseExponent`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget.chooseForSigma`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget.chooseM`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.cachePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableBudgets.workspaceEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.projectBase`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.replaceBase`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler.codes`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler.primitive`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler.primitiveCfg`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler.primitiveControlCfg`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler.selected`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler.stackCfg`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler.stackProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler.transition`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram.Normalize.canonicalDigit`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates.chunks`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates.digitWidth`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates.normalize`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates.payloadWidth`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.Initialize.savedRoutes`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.outer`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.massPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Subset.body`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Subset.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Subset.loop`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality.stateFor`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendSources.castRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram.descendingHighMask`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram.freeFill`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram.freeOrder`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.leafPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.leafPortsWrapped`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.leafRegisterPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.unaryRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.graphBoundary` and 134 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_CodeCandidateProgram`, `SubexponentialSAT_SqrtLogSpace_CopySpace`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseBudget`, `SubexponentialSAT_SqrtLogSpace_FactorCacheProgram`, `SubexponentialSAT_SqrtLogSpace_FactorEvaluationSpace`, `SubexponentialSAT_SqrtLogSpace_FactorProductSpace`, `SubexponentialSAT_SqrtLogSpace_FactorTableBudgets`, `SubexponentialSAT_SqrtLogSpace_FactorTableProgram`, `SubexponentialSAT_SqrtLogSpace_GuardedCompiler`, `SubexponentialSAT_SqrtLogSpace_HashCandidateProgram`, `SubexponentialSAT_SqrtLogSpace_HashCandidates`, `SubexponentialSAT_SqrtLogSpace_HashGreedyProgram`, `SubexponentialSAT_SqrtLogSpace_HashMassAdapter`, `SubexponentialSAT_SqrtLogSpace_HeadSourceLocality`, `SubexponentialSAT_SqrtLogSpace_HeadSpecializationProgram`, `SubexponentialSAT_SqrtLogSpace_HighFrontendSources`, `SubexponentialSAT_SqrtLogSpace_HighIncidenceProgram`, `SubexponentialSAT_SqrtLogSpace_NativeCode`, `SubexponentialSAT_SqrtLogSpace_NativeCodeAssembly`, `SubexponentialSAT_SqrtLogSpace_NativeFrontend`, `SubexponentialSAT_SqrtLogSpace_NativeLeafContract`, `SubexponentialSAT_SqrtLogSpace_NativeLeafStartup`, `SubexponentialSAT_SqrtLogSpace_NativeProgram`, `SubexponentialSAT_SqrtLogSpace_QueryIncidenceSpace`, `SubexponentialSAT_SqrtLogSpace_QueryProducerSpace`, `SubexponentialSAT_SqrtLogSpace_QueryProgram`, `SubexponentialSAT_SqrtLogSpace_QueryTupleInit`, `SubexponentialSAT_SqrtLogSpace_QueryTupleReadoutSemantics`, `SubexponentialSAT_SqrtLogSpace_QueryTupleSum`, `SubexponentialSAT_SqrtLogSpace_QueryVisitorLoadBounds`, `SubexponentialSAT_SqrtLogSpace_ReconstructionNative`, `SubexponentialSAT_SqrtLogSpace_RingNodeSetup`, `SubexponentialSAT_SqrtLogSpace_ScheduleProgram`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleRun`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleTraversal`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleWords`, `SubexponentialSAT_SqrtLogSpace_SparseCodeSearch`, `SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram`, `SubexponentialSAT_SqrtLog_HashFamily`, `SubexponentialSAT_StackCompiler`, `SubexponentialSAT_StructuredProgram`, `SubexponentialSAT_SubexpCRTOuterControl`, `SubexponentialSAT_SubexpCRTOuterSweep`, `SubexponentialSAT_SubexpEvaluationProgram`, `SubexponentialSAT_SubexpFactorCountSetup`, `SubexponentialSAT_SubexpFlatCount`, `SubexponentialSAT_SubexpGuardProgram`, `SubexponentialSAT_SubexpHornerProgram`, `SubexponentialSAT_SubexpIncidenceSlotProgram`, `SubexponentialSAT_SubexpJetCellProgram`, `SubexponentialSAT_SubexpJetInitProgram`, `SubexponentialSAT_SubexpKernelControl`, `SubexponentialSAT_SubexpNegatedQueryProgram`, `SubexponentialSAT_SubexpProjectedExecution`, `SubexponentialSAT_SubexpQuarticRing`, `SubexponentialSAT_SubexpRowInterpolation`, `SubexponentialSAT_SubexpSwapMultiplicity`, `SubexponentialSAT_SubexpTautologyProgram`, `SubexponentialSAT_SubexpTaylorExecution`, `SubexponentialSAT_SubexpUnaryRangeProgram`, `SubexponentialSAT_Subexp_ConstructivePacking`, `SubexponentialSAT_Subexp_GlobalBasisMetadata`, `SubexponentialSAT_Subexp_LocalSpectrum`, `SubexponentialSAT_Subexp_MatrixParityProgram`, `SubexponentialSAT_Subexp_MatrixProgram`, `SubexponentialSAT_Subexp_MatrixVectorProgram`, `SubexponentialSAT_Subexp_MismatchPlanProgram`, `SubexponentialSAT_Subexp_SupportSelectionData`, `SubexponentialSAT_Subexp_TypeBitProgram`, `SubexponentialSAT_Subexp_UniversalRowEmitCall`, `SubexponentialSAT_Subexp_UniversalRowLoop`, `SubexponentialSAT_Subexp_UniversalRowSource`, `SubexponentialSAT_Subexp_UniversalRowTableSource`, `SubexponentialSAT_SunflowerBranch`, `SubexponentialSAT_TypeDistribution`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S000`, `OAIQ081S001`, `OAIQ081S002`, `OAIQ081S003`, `OAIQ081S005`, `OAIQ081S006`, `OAIQ081S007`, `OAIQ081S008`, `OAIQ081S009`, `OAIQ081S012`, `OAIQ081S013`, `OAIQ081S014`, `OAIQ081S015`, `OAIQ081S016`, `OAIQ081S017`, `OAIQ081S018`, `OAIQ081S020`, `OAIQ081S021` and `OAIQ081S022` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S064` and `OAIQ081S065`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace.compile_word_answer_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets.runtime_of_tree_and_leaf`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.readback_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell.updateCell_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.sourceCode_decode` and `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixVectorProgram.matrix_trace`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace.compile_word_answer_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets.runtime_of_tree_and_leaf`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.readback_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWord_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrix_apply_trace`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.initial_coverage_of_code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_computed_energies` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.prepareProgram_factored_runsIn`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001
import Definitions.Def_OAIQ081S002
import Definitions.Def_OAIQ081S003
import Definitions.Def_OAIQ081S005
import Definitions.Def_OAIQ081S006
import Definitions.Def_OAIQ081S007
import Definitions.Def_OAIQ081S008
import Definitions.Def_OAIQ081S009
import Definitions.Def_OAIQ081S012
import Definitions.Def_OAIQ081S013
import Definitions.Def_OAIQ081S014
import Definitions.Def_OAIQ081S015
import Definitions.Def_OAIQ081S016
import Definitions.Def_OAIQ081S017
import Definitions.Def_OAIQ081S018
import Definitions.Def_OAIQ081S020
import Definitions.Def_OAIQ081S021
import Definitions.Def_OAIQ081S022

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackCompiler
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

open Turing SubexponentialSAT.Computation SubexponentialSAT.StackMachine SubexponentialSAT.StackEncoding

def mutationActions {α : Type} (code : BlockCode α) : Mutation α → List Action
  | .keep => []
  | .pop => popBits code.width
  | .push a => pushBits (code.block a)

theorem mutationActions_length {α : Type} (code : BlockCode α) (op : Mutation α) :
    (mutationActions code op).length ≤ 2 * code.width := by
  cases op <;> simp [mutationActions, code.length_block]

abbrev CodeFamily {t : ℕ} (Γ : Fin t → Type) := ∀ k, BlockCode (Γ k)

abbrev State {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (p : StackProgram Q Γ) (codes : CodeFamily Γ) :=
  Q ⊕ (((q : Q) × ReaderState (codes (p.select q)).width) ⊕
    ((k : Fin t) × (Q × Mutation (Γ k) × Fin (2 * (codes k).width + 1))))

def ready {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    {p : StackProgram Q Γ} {codes : CodeFamily Γ} (q : Q) : State p codes := .inl q

def reading {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    {p : StackProgram Q Γ} {codes : CodeFamily Γ}
    (q : Q) (r : ReaderState (codes (p.select q)).width) : State p codes :=
  .inr (.inl ⟨q, r⟩)

def acting {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    {p : StackProgram Q Γ} {codes : CodeFamily Γ}
    (k : Fin t) (q : Q) (op : Mutation (Γ k))
    (i : Fin (2 * (codes k).width + 1)) : State p codes :=
  .inr (.inr ⟨k, q, op, i⟩)

def controller {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (p : StackProgram Q Γ) (codes : CodeFamily Γ)
    (decode : ∀ k, List Bool → Option (Γ k)) : Controller (State p codes) t where
  inputTape := p.inputTape
  start := ready p.start
  scan
    | .inl q => p.select q
    | .inr (.inl ⟨q, _⟩) => p.select q
    | .inr (.inr ⟨k, _⟩) => k
  transition
    | .inl q, bit => .inr (reading q (0, fun _ => none), .write bit)
    | .inr (.inl ⟨q, r⟩), bit =>
      let width := (codes (p.select q)).width
      if h : r.1.val < width then
        .inr (reading q (⟨r.1.val + 1, by omega⟩,
          Function.update r.2 ⟨r.1.val, h⟩ bit), .move .right)
      else if h' : r.1.val < 2 * width then
        .inr (reading q (⟨r.1.val + 1, by omega⟩, r.2), .move .left)
      else
        match p.transition q (decode (p.select q) (registerBits r.2)) with
        | .inl answer => .inl answer
        | .inr (q', op) => .inr (acting (p.select q) q' op 0, .write bit)
    | .inr (.inr ⟨k, q, op, i⟩), bit =>
      let actions := mutationActions (codes k) op
      if h : i.val < actions.length then
        .inr (acting k q op ⟨i.val + 1,
          Nat.lt_succ_of_le (Nat.le_trans (Nat.succ_le_of_lt h)
            (mutationActions_length (codes k) op))⟩, actions[i.val])
      else .inr (ready q, .write bit)

def tapeEncoding {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (codes : CodeFamily Γ) (c : StackCfg Q Γ) : Fin t → BitTape :=
  fun k => dataTape (encodeDataStack (codes k) (c.stk k))

def encodeCfg {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (p : StackProgram Q Γ) (codes : CodeFamily Γ) (c : StackCfg Q Γ) :
    ControlCfg (State p codes) t :=
  ⟨c.state.map id ready, tapeEncoding codes c⟩

def readCfg {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (p : StackProgram Q Γ) (codes : CodeFamily Γ)
    (q : Q) (base : Fin t → BitTape)
    (r : ReaderState (codes (p.select q)).width) (tape : BitTape) :
    ControlCfg (State p codes) t :=
  ⟨.inr (reading q r), Function.update base (p.select q) tape⟩

def actionCfg {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (p : StackProgram Q Γ) (codes : CodeFamily Γ)
    (k : Fin t) (q : Q) (op : Mutation (Γ k)) (base : Fin t → BitTape)
    (i : Fin ((mutationActions (codes k) op).length + 1)) (tape : BitTape) :
    ControlCfg (State p codes) t :=
  ⟨.inr (acting k q op ⟨i.val,
      lt_of_lt_of_le i.isLt (Nat.succ_le_succ (mutationActions_length (codes k) op))⟩),
    Function.update base k tape⟩

section FiniteController

variable {Q : Type} [Fintype Q] {t : ℕ} {Γ : Fin t → Type}
  [∀ k, Fintype (Γ k)]
  (p : StackProgram Q Γ) (codes : CodeFamily Γ)
  (decode : ∀ k, List Bool → Option (Γ k))

instance stateFintype : Fintype (State p codes) := inferInstance

/-- The assembled finite control is a genuine primitive bit machine. -/
noncomputable def compiledMachine : PrimitiveMachine :=
  reindex (Fintype.equivFin (State p codes)) (controller p codes decode)

noncomputable def compiledCfg (a : StackCfg Q Γ) : (compiledMachine p codes decode).Cfg :=
  reindexCfg (Fintype.equivFin (State p codes)) (controller p codes decode)
    (encodeCfg p codes a)

end FiniteController

end SubexponentialSAT.StackCompiler

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StructuredProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Structured programs compiled to finite bit instruction tables

The syntax has no unbounded natural-number registers or semantic-function
instructions. All data operations are the concrete Boolean-register and stack
instructions of BitProgram. Loops inspect a Boolean register, and changing data
never changes the finite generated instruction table.
-/

namespace SubexponentialSAT.StructuredProgram

open SubexponentialSAT.BitProgram

instance siteFintype {r s : ℕ} : (c : Cmd r s) → Fintype (Site c)
  | .skip => inferInstanceAs (Fintype Empty)
  | .atom _ => inferInstanceAs (Fintype Unit)
  | .seq first second => by
      letI := siteFintype first
      letI := siteFintype second
      exact inferInstanceAs (Fintype (Site first ⊕ Site second))
  | .ite _ yes no => by
      letI := siteFintype yes
      letI := siteFintype no
      exact inferInstanceAs (Fintype (Option (Site yes ⊕ Site no)))
  | .while _ body => by
      letI := siteFintype body
      exact inferInstanceAs (Fintype (Option (Site body)))

end SubexponentialSAT.StructuredProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpQuarticRing
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed-size, executable quartic ring implementation

The data are four coefficients.  Multiplication is Horner evaluation with
the explicit reduction `T^4 = t0 + t1*T + t2*T^2 + t3*T^3`.
The coefficient operations are parameters of the implementation; the binary
instance below discharges their correctness and uniform finite-event bound.
-/

namespace SubexponentialSAT.SubexpQuarticRing

section RingFormulas

variable {R : Type*} [CommRing R]

def add (a b : Quad R) : Quad R :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3⟩

end RingFormulas

/-! These loops execute exactly the displayed scalar calls. -/

end SubexponentialSAT.SubexpQuarticRing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeCandidateProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed-table conversion of one odometer tuple to one arithmetic candidate.
The input contains only the current candidate. The output is reversed scalar
frames, directly suitable for the existing word and matrix callbacks. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram

open BitProgram CodeCandidates

def roundRegs (ternary : Bool) (regs : Fin 5 → Bool) (a b : Bool) : Fin 5 → Bool :=
  ![false, true, invalidDigit ternary (a,b), b, regs 4 || invalidDigit ternary (a,b)]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CopySpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Every-prefix storage of the actual preserving copy table. Empty destination
and temporary stacks permit the original per-stack envelope to be reused. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CopySpace

open BitProgram

def copyWeight {r s : ℕ} (src dst tmp : Fin s) (present : Fin r)
    (a : Cfg r s 8) : ℕ :=
  let x := (a.stacks src).length
  let y := (a.stacks dst).length
  let z := (a.stacks tmp).length
  match a.pc with
  | none => max x y + z
  | some pc =>
      if pc = 0 then x + y + z
      else if pc = 1 then x + y + z + (if a.regs present then 1 else 0)
      else if pc = 2 then x + y + z + 1
      else if pc = 4 then max x y + z + (if a.regs present then 1 else 0)
      else if pc = 5 then max x y + z + 1
      else if pc = 6 then max x (y + 1) + z
      else max x y + z

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CopySpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SunflowerBranch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Literal-set sunflower branching

Concrete CNF children and their semantic union, together with the absorption
invariants used by the cumulative-insertion argument. Opposite polarities are
distinct literals; no variable-disjointness premise is used.
-/

namespace SubexponentialSAT.SunflowerBranch

open SubexponentialSAT.SAT

universe u
variable {V : Type u} [DecidableEq V]

/-- Add a common literal-set core to each petal. -/
def clauses (H : Clause V) (P : CNF V) : CNF V := P.image fun p => H ∪ p

end SubexponentialSAT.SunflowerBranch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseBudget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

/-- A dyadic witness of order `s log s`, rather than the old quadratic witness.
The source's test uses `clog 2 (4 C M)`, so every comparison is integral. -/
theorem dyadic_witness (C : ℕ → ℕ) (a q γ s : ℕ) (hs : 0 < s)
    (hC : ∀ M, 2 ≤ M → C M ≤ a * M ^ q) :
    ∃ T e : ℕ, 1 ≤ T ∧ γ ≤ 2 ^ e ∧ 2 ≤ 2 ^ e ∧
      γ * Nat.clog 2 (4 * C (2 ^ e) * 2 ^ e) * s ≤ 2 ^ e ∧
      2 ^ e ≤ (4 * 2 ^ T) * s * (Nat.log 2 s + 1) ∧
      e ≤ T + 2 * (Nat.log 2 s + 1) ∧
      T = 2 * (γ * (a + 2 + 4 * (q + 1) + 1) + 1) := by
  let T := 2 * (γ * (a + 2 + 4 * (q + 1) + 1) + 1)
  let l := Nat.log 2 s + 1
  let t := Nat.log 2 l + 1
  let e := T + l + t
  obtain ⟨hT, hγT, hcontrol⟩ := control_exponent (a + 2) (q + 1) γ
  have hl : 0 < l := by dsimp [l]; omega
  have ht : t ≤ l := Nat.succ_le_of_lt (Nat.log_lt_self 2 (by omega))
  have hslow : s ≤ 2 ^ l := (Nat.lt_pow_succ_log_self (by decide) s).le
  have hllow : l ≤ 2 ^ t := (Nat.lt_pow_succ_log_self (by decide) l).le
  have hsup : 2 ^ l ≤ 2 * s := by
    calc
      2 ^ l = 2 ^ Nat.log 2 s * 2 := by rw [show l = Nat.log 2 s + 1 from rfl, pow_succ]
      _ ≤ s * 2 := Nat.mul_le_mul_right 2 (Nat.pow_log_le_self 2 (by omega))
      _ = 2 * s := Nat.mul_comm _ _
  have htup : 2 ^ t ≤ 2 * l := by
    calc
      2 ^ t = 2 ^ Nat.log 2 l * 2 := by rw [show t = Nat.log 2 l + 1 from rfl, pow_succ]
      _ ≤ l * 2 := Nat.mul_le_mul_right 2 (Nat.pow_log_le_self 2 (by omega))
      _ = 2 * l := Nat.mul_comm _ _
  have he : 1 ≤ e := by dsimp [e, T] at *; omega
  have hM : 2 ≤ 2 ^ e := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) he
  have hcoeff : 4 * a ≤ 2 ^ (a + 2) := by
    calc
      4 * a ≤ 4 * 2 ^ a := Nat.mul_le_mul_left 4 (Nat.lt_pow_self (by decide)).le
      _ = 2 ^ (a + 2) := by rw [pow_add]; norm_num; ring
  have hbase : 4 * C (2 ^ e) * 2 ^ e ≤ 2 ^ (a + 2 + (q + 1) * e) := by
    calc
      4 * C (2 ^ e) * 2 ^ e ≤ 4 * (a * (2 ^ e) ^ q) * 2 ^ e :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hC _ hM))
      _ = (4 * a) * (2 ^ e) ^ (q + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (a + 2) * (2 ^ e) ^ (q + 1) := Nat.mul_le_mul_right _ hcoeff
      _ = 2 ^ (a + 2 + (q + 1) * e) := by
        rw [← pow_mul, ← pow_add, Nat.mul_comm e (q + 1)]
  have hlog : Nat.clog 2 (4 * C (2 ^ e) * 2 ^ e) ≤ a + 2 + (q + 1) * e :=
    (Nat.le_pow_iff_clog_le (by decide)).mp hbase
  have htl : T ≤ T * l := Nat.le_mul_of_pos_right T hl
  have hal : a + 2 ≤ (a + 2) * l := Nat.le_mul_of_pos_right (a + 2) hl
  have het : e ≤ (T + 2) * l := by dsimp [e]; nlinarith
  have hbound : a + 2 + (q + 1) * e ≤ (a + 2 + (q + 1) * (T + 2)) * l := by
    have := Nat.mul_le_mul_left (q + 1) het
    nlinarith
  have hbudget : γ * Nat.clog 2 (4 * C (2 ^ e) * 2 ^ e) * s ≤ 2 ^ e := by
    calc
      γ * Nat.clog 2 (4 * C (2 ^ e) * 2 ^ e) * s ≤
          γ * ((a + 2 + (q + 1) * (T + 2)) * l) * s := by
        exact Nat.mul_le_mul_right s (Nat.mul_le_mul_left γ (hlog.trans hbound))
      _ = (γ * (a + 2 + (q + 1) * (T + 2))) * s * l := by ring
      _ ≤ 2 ^ T * s * l := by exact Nat.mul_le_mul_right l (Nat.mul_le_mul_right s hcontrol)
      _ ≤ 2 ^ T * 2 ^ l * 2 ^ t := Nat.mul_le_mul (Nat.mul_le_mul_left _ hslow) hllow
      _ = 2 ^ e := by
        calc
          2 ^ T * 2 ^ l * 2 ^ t = 2 ^ (T + l) * 2 ^ t :=
            congrArg (fun x : ℕ => x * 2 ^ t) (pow_add 2 T l).symm
          _ = 2 ^ e := (pow_add 2 (T + l) t).symm
  refine ⟨T, e, hT, ?_, hM, hbudget, ?_, ?_, rfl⟩
  · exact hγT.trans (Nat.pow_le_pow_right (by decide) (by dsimp [e]; omega))
  · calc
      2 ^ e = 2 ^ T * 2 ^ l * 2 ^ t := by dsimp [e]; rw [pow_add, pow_add]
      _ ≤ 2 ^ T * (2 * s) * (2 * l) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hsup) htup
      _ = (4 * 2 ^ T) * s * (Nat.log 2 s + 1) := by dsimp [l]; ring
  · dsimp [e]; omega

open SparseCharging

/-- The search terminates, with a fully explicit coefficient depending only on
`k`. This theorem counts candidates; primitive bit costs are proved separately. -/
theorem exists_parameter (k a b : ℕ) (ha : 0 < a) :
    ∃ e, parameterTest k a b e = true := by
  let s := inverseIndex a b
  obtain ⟨T, e, _, hγ, hM, hbudget, _, _, _⟩ :=
    dyadic_witness (depthConstant k) (4 * (k - 1) * 3 ^ (k - 2)) (k - 2)
      (rightConstant k) s (by exact Nat.zero_lt_succ _)
      (fun M hM => depthConstant_le k M hM)
  refine ⟨e, ?_⟩
  simp only [parameterTest, decide_eq_true_eq]
  refine ⟨hM, hγ, ?_⟩
  calc
    rightConstant k * Nat.clog 2 (4 * depthConstant k (2 ^ e) * 2 ^ e) * b ≤
        rightConstant k * Nat.clog 2 (4 * depthConstant k (2 ^ e) * 2 ^ e) * (a * s) :=
      Nat.mul_le_mul_left _ (inverseIndex_mul a b ha)
    _ = a * (rightConstant k * Nat.clog 2 (4 * depthConstant k (2 ^ e) * 2 ^ e) * s) := by ring
    _ ≤ a * 2 ^ e := Nat.mul_le_mul_left a hbudget

/-- First passing power of two in the source's deterministic search. -/
def chooseExponent (k a b : ℕ) (ha : 0 < a) : ℕ := Nat.find (exists_parameter k a b ha)

def chooseM (k a b : ℕ) (ha : 0 < a) : ℕ := 2 ^ chooseExponent k a b ha

/-- The source selector on a positive rational budget, preserving its exact
numerator and denominator in every comparison. -/
def chooseForSigma (k : ℕ) (σ : ℚ) (hσ : 0 < σ) : ℕ :=
  chooseM k σ.num.natAbs σ.den (rational_data σ hσ).1


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEvaluationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete evaluation-result extraction

The extractor removes the singleton operand-list framing, parses the result
payload into a reversed scratch stack, and transfers it to physical stack 15.
It clears the operand/depth/scratch stacks and preserves every other stack.
-/

namespace SubexponentialSAT.SubexpEvaluationProgram

open BitProgram
open SubexpPostfixControl

open SubexpPostfixGlobal

/-! ## Entry from arbitrary caller registers -/

def resetData (is : List (Fin 16)) (d : StructuredProgram.State 16 128) :
    StructuredProgram.State 16 128 :=
  ⟨fun i => if i ∈ is then false else d.regs i, d.stacks⟩

end SubexponentialSAT.SubexpEvaluationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSwapMultiplicity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

section PredicateWords

variable {ι β υ : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
variable (Neg : β → Prop) [DecidablePred Neg]

/-- Prescribing the negative positions leaves independent negative and
positive label choices on the two parts. -/
noncomputable def supportFiberEquiv (s : Finset ι) :
    {word : ι → β // negativeSupport Neg word = s} ≃
      (s → {b : β // Neg b}) × ({l : ι // l ∉ s} → {b : β // ¬ Neg b}) := by
  classical
  refine
    { toFun := fun word =>
        (fun l => ⟨word.1 l.1, ?_⟩, fun l => ⟨word.1 l.1, ?_⟩)
      invFun := fun labels =>
        ⟨fun l => if h : l ∈ s then labels.1 ⟨l, h⟩ else labels.2 ⟨l, h⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply (mem_negativeSupport Neg word.1 l.1).mp
    simpa only [word.2] using l.2
  · intro h
    apply l.2
    simpa only [word.2] using (mem_negativeSupport Neg word.1 l.1).mpr h
  · apply Finset.ext
    intro l
    by_cases hl : l ∈ s
    · simp [negativeSupport, hl, (labels.1 ⟨l, hl⟩).2]
    · simp [negativeSupport, hl, (labels.2 ⟨l, hl⟩).2]
  · intro word
    apply Subtype.ext
    funext l
    by_cases hl : l ∈ s <;> simp [hl]
  · intro labels
    apply Prod.ext
    · funext l
      apply Subtype.ext
      simp [l.2]
    · funext l
      apply Subtype.ext
      simp [l.2]

noncomputable def weightedProductLeftEquiv (w : ℕ) :
    {x : υ × (ι → β) // weight Neg x.2 = w} ≃
      υ × {word : ι → β // weight Neg word = w} where
  toFun x := (x.1.1, ⟨x.1.2, x.2⟩)
  invFun x := ⟨(x.1, x.2.1), x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end PredicateWords

/-! ## General binomial second moment and the interval tail -/

end SubexponentialSAT.SubexpSwapMultiplicity

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_LocalSpectrum
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Spectrum of a swap of two finite ordered registers

The alphabet size is unrestricted relative to the characteristic.  The only
field assumption beyond `Field K` is `2 ≠ 0`.  Basis labels on or above the
diagonal are positive; labels strictly below the diagonal are negative.
-/

namespace SubexponentialSAT.Subexp.LocalSpectrum

open scoped BigOperators

variable (K : Type*) [Field K]
variable {α : Type*}

variable [LinearOrder α]

variable [Fintype α]

/-- The sum/difference construction is a genuine basis over every field with `2 ≠ 0`. -/
noncomputable def swapEigenbasis (h2 : (2 : K) ≠ 0) :
    Module.Basis (Pair α) K (Pair α → K) :=
  Module.Basis.ofEquivFun (eigenCoordinateEquiv K h2)

end SubexponentialSAT.Subexp.LocalSpectrum

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpGuardProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete binary guard control for the subexponential schedule

The comparator below has a fixed instruction table, reads arbitrary-width
little-endian binary words, and uses only Boolean operations and stack pops.
Schedule arithmetic is not an instruction of this program.
-/

namespace SubexponentialSAT.SubexpGuardProgram

open BitProgram BinaryArithmetic

open StructuredProgram

def pairCost (j : Fin 3) (a : State 9 6) : ℕ :=
  10 * max (a.stacks (pairStack j 0)).length (a.stacks (pairStack j 1)).length + 8

def pairPass (j : Fin 3) (a : State 9 6) : Bool :=
  decide (BinaryArithmetic.toNat (a.stacks (pairStack j 1)) ≤ BinaryArithmetic.toNat (a.stacks (pairStack j 0)))


end SubexponentialSAT.SubexpGuardProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_TypeDistribution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Uniform words induce uniform local types

The outcome space consists of all assignments of words to distinct factor,
head, and padding indices. Local read maps are injective. Read maps at
distinct coordinates sharing no factor have disjoint ranges. Finite product
counting then supplies the actual marginals and pair moments needed by
SubexponentialSAT.Variance; these probabilistic properties are conclusions, not hypotheses.
-/

namespace SubexponentialSAT.TypeDistribution

open scoped BigOperators
open SubexponentialSAT.Variance

section EnumeratedExpectations

variable {I W A B : Type*}

/-- Swap an assignment coordinate with one fresh word. This is a permutation
of the full product outcome space, including the old coordinate value. -/
def resampleEquiv [DecidableEq I] (i : I) : ((I → W) × W) ≃ ((I → W) × W) where
  toFun p := (Function.update p.1 i p.2, p.1 i)
  invFun p := (Function.update p.1 i p.2, p.1 i)
  left_inv p := by
    apply Prod.ext
    · funext j
      by_cases h : j = i
      · subst j; simp
      · simp [Function.update_of_ne h]
    · simp
  right_inv p := by
    apply Prod.ext
    · funext j
      by_cases h : j = i
      · subst j; simp
      · simp [Function.update_of_ne h]
    · simp

end EnumeratedExpectations

end SubexponentialSAT.TypeDistribution

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

def cachePorts : List (Fin 768) :=
  LeafNodeCacheProgram.cachePorts ++ LeafNodeCacheProgram.pocket

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashFamily
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashFamily

open scoped BigOperators
open Finset

def coeffMap {m d : ℕ} (e : IndexTuple m d) (v : Fin m → ZMod 3) :
    CoeffTuple d →+ ZMod 3 where
  toFun c := ∑ j, c j * v (e j)
  map_zero' := by simp
  map_add' c c' := by simp [add_mul, Finset.sum_add_distrib]

end SubexponentialSAT.SqrtLog.HashFamily

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GlobalBasisMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

open BitProgram StructuredCalls


def reset (regs : Regs) : Regs := readRegs regs 0 1 none

end SubexponentialSAT.Subexp.GlobalBasisMetadata

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ConstructivePacking
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

namespace FiniteEnumeration

variable {α : Type*} [DecidableEq α]

/-- Executable enumeration and inverse, implemented by `get` and `idxOf`. -/
def equivFin (E : FiniteEnumeration α) : Fin E.values.length ≃ α where
  toFun := E.values.get
  invFun x := ⟨E.values.idxOf x, List.idxOf_lt_length_iff.mpr (E.complete x)⟩
  left_inv i := Fin.ext (List.get_idxOf E.nodup i)
  right_inv _x := List.idxOf_get _

end FiniteEnumeration

namespace PackingData

variable {V U : Type*} [DecidableEq U]

/-- Explicit fiber enumeration, without `Fintype.equivFin`. -/
def bucketEquiv [DecidableEq V] (P : PackingData V U) (u : U) :
    Fin (P.bucket u).length ≃ {v // P.label v = u} :=
  listSubtypeEquiv (P.bucket u) (P.bucket_nodup u) (fun v => P.label v = u)
    (P.mem_bucket u)

end PackingData

end SubexponentialSAT.Subexp.ConstructivePacking

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpUnaryRangeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed unary range enumerator which physically emits every framed index. -/
namespace SubexponentialSAT.SubexpUnaryRangeProgram

open BitProgram StructuredCalls SubexpIncidencePlanPrimitives

def indexPrefix (js : List ℕ) : List Bool := js.flatMap fun j => true :: Encoding.frame (unary j)

abbrev testedRegs (regs : Fin 10 → Bool) (n : ℕ) : Fin 10 → Bool :=
  readRegs regs 7 9 (unary n).head?

end SubexponentialSAT.SubexpUnaryRangeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpJetInitProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Initializing the packed output jet

The input dimension is a unary word on stack 109 and the scalar word width is
the length of stack 10.  The fixed program constructs one four-word zero
coefficient on stack 104 and copies it D times to stack 102.  It preserves both
input words.  No zero array is supplied as an input certificate.
-/

namespace SubexponentialSAT.SubexpJetInitProgram

open BitProgram StructuredCalls

abbrev Data := State 16 128

end SubexponentialSAT.SubexpJetInitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpJetCellProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete addition into one packed jet cell

The persistent jet, unary index, and cell width are on stacks 102, 103, and
104. The array subprogram uses 112--117, and order-preserving moves use 118.
All instruction tables are fixed independently of widths and indices. The
full service reads the old cell, invokes the actual flattened quartic adder,
and writes the sum back. Its endpoint changes only the contribution and jet
stacks; all other caller stacks and registers 8--15 are preserved.
-/

namespace SubexponentialSAT.SubexpJetCellProgram

open BitProgram StructuredCalls

abbrev Data := State 16 128

def readOut (d : Data) (record : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks 113 []) 112 (record ++ d.stacks 112)⟩

def replaceOut (d : Data) (earlier : List (List Bool)) (replacement rest : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks 113 []) 102
      (earlier.flatten ++ (replacement ++ rest))⟩

def moveOut (d : Data) (src dst : Fin 128) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks src []) dst (d.stacks src ++ d.stacks dst)⟩

def clearOut (d : Data) (src : Fin 128) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩

end SubexponentialSAT.SubexpJetCellProgram
namespace SubexponentialSAT.SubexpJetCellProgram

open BitProgram StructuredCalls
open SubexpLiftRing SubexpQuarticRing

def addOut (d : Data) (regs : Fin 8 → Bool) (result : List Bool) : Data :=
  ⟨fun i => Fin.addCases (m := 8) (n := 8) (motive := fun _ => Bool) regs
      (fun j => d.regs (Fin.natAdd 8 j)) i,
    Function.update (Function.update d.stacks 8 result) 9 []⟩

end SubexponentialSAT.SubexpJetCellProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpProjectedExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Projected postfix execution

The compiled source contains the original raw literals. Each complete push
calls the finite projection table; the resulting value is therefore
`(e.map project).eval`. The induction tracks the entire remaining source and
operand list, and charges actual service trace bounds at every node.
-/

namespace SubexponentialSAT.SubexpProjectedInterpreter

open BitProgram
open SubexpPostfixControl (operandDepth)

variable {r s a b c : ℕ}

variable (add : Program (3 + r) (4 + s) a) (mul : Program (3 + r) (4 + s) b)
  (loader : Program (3 + r) (4 + s) c)

section Execution

variable {R : Type*} [Add R] [Mul R] (encode : R → List Bool)
variable (addBound mulBound : R → R → ℕ) (context : Fin s → List Bool) (valid : R → Prop)

/-- Interpreter cost includes original literal byte length, its projection,
and the dispatcher overhead on both binary operations. -/
def exprCost (project : R → R) (loadBound : R → ℕ) : Algorithm.Expr R → ℕ
  | .lit x => 11 * (encode x).length + 17 + loadBound x
  | .add e f => exprCost project loadBound e + exprCost project loadBound f +
      (14 + addBound (e.map project).eval (f.map project).eval)
  | .mul e f => exprCost project loadBound e + exprCost project loadBound f +
      (14 + mulBound (e.map project).eval (f.map project).eval)

end Execution

end SubexponentialSAT.SubexpProjectedInterpreter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpHornerProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control source generation for factored Horner expressions

Input payloads are coefficient representations, never precomputed instruction
streams. The emitter writes the actual serialized postfix tags and frames.
-/

namespace SubexponentialSAT.SubexpHornerProgram

open BitProgram

namespace Literal

def cfg (pc : Option (Fin 13)) (v p c : Bool)
    (payload out scratch : List Bool) : Cfg 3 3 13 :=
  ⟨pc, triple v p c, triple payload out scratch⟩

end Literal

end SubexponentialSAT.SubexpHornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpKernelControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed controller constructing the separated postfix source

The input contains literal payloads and the three nested lists of blocks,
color groups, and terms.  The controller only parses frames, copies bits,
and emits postfix tags.  It has no arithmetic callback and never builds a
Cartesian product of the inner lists.  Three unary stacks hold the pending
right-fold operators, so the emitted source has exactly the association of
`SubexpAlgorithm.momentExpression`.
-/

namespace SubexponentialSAT.SubexpKernelControl

open BitProgram StructuredCalls

/-! ## Fixed source-constructor control -/

/-! ## Concrete machine states and elementary traces -/

def counterPort (i : Fin 3) : Fin 8 := if i = 0 then 5 else if i = 1 then 6 else 7

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

/-! ## Forward-output service boundary -/

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowInterpolation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit mismatch interpolation for the multi-color layout

Section 3.3 of `subexponential-sat.txt`. All inverse data are supplied as
units. The polynomials are finite sums and products, not chosen witnesses.
Their scalar evaluation functions are executable from the supplied ring
operations and units; the semantic polynomial definitions use mathlib's
noncomputable polynomial representation.
-/

namespace SubexponentialSAT.SubexpRowInterpolation

open scoped BigOperators

variable {E I V C : Type*} [CommRing E] [DecidableEq I]

variable {node : I → E}

variable [DecidableEq V]

/-! ## Executable finite expression codes

The following constructors produce polynomial expression data using only
finite `List.ofFn` traversals. Their denotations are the proved polynomials
above. This supplies a concrete path representation in addition to the
executable scalar evaluator.
-/

namespace PolynomialCode

/-- Mathematical meaning of the finite expression. -/
noncomputable def denote : PolynomialCode E → Polynomial E
  | constant a => Polynomial.C a
  | indeterminate => Polynomial.X
  | add p q => p.denote + q.denote
  | mul p q => p.denote * q.denote

def sum (ps : List (PolynomialCode E)) : PolynomialCode E :=
  ps.foldr add (constant 0)

def product (ps : List (PolynomialCode E)) : PolynomialCode E :=
  ps.foldr mul (constant 1)

end PolynomialCode

end SubexponentialSAT.SubexpRowInterpolation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTaylorExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable Taylor and factor preprocessing for coefficient code words

Only RingProgram callbacks occur in runtime definitions. Code words need no
ring laws. Decoding the computed arrays yields the true shifted-polynomial
coefficients. Arithmetic callback costs and list visits are kept separate.
-/

namespace SubexponentialSAT.SubexpTaylorExecution

open scoped BigOperators
open SubexpRowInterpolation (PolynomialCode)

variable {C R : Type*}

def mapCode (decode : C → R) : PolynomialCode C → PolynomialCode R
  | .constant c => .constant (decode c)
  | .indeterminate => .indeterminate
  | .add p q => .add (mapCode decode p) (mapCode decode q)
  | .mul p q => .mul (mapCode decode p) (mapCode decode q)

end SubexponentialSAT.SubexpTaylorExecution

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual outer loop assembling correction terms in selected-index order. -/

namespace SubexponentialSAT.Subexp.UniversalRowLoop

open BitProgram StructuredCalls
open UniversalRowGather (Word)
open UniversalRowFactorLoop (indexWord)

def Tables.rows (t : Tables) : List Word := t.differences.map List.flatten

structure Valid (t : Tables) (width rowWidth : Word) (positions : List ℕ) : Prop where
  values : ∀ row ∈ t.values, row.length = width.length
  inverses : ∀ row ∈ t.inverses, row.length = width.length
  negatives : ∀ row ∈ t.negatives, row.length = width.length
  rows : ∀ row ∈ t.rows, row.length = rowWidth.length
  bounds : ∀ i ∈ positions,
    i < t.values.length ∧ i < t.inverses.length ∧ i < t.differences.length
  differences : ∀ i ∈ positions, ∀ row ∈ t.differences.getD i [], row.length = width.length
  innerBounds : ∀ i ∈ positions, ∀ j ∈ positions,
    j < (t.differences.getD i []).length ∧ j < t.negatives.length

end SubexponentialSAT.Subexp.UniversalRowLoop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowEmitCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A framed call to the actual row source emitter inside the row workspace. -/

namespace SubexponentialSAT.Subexp.UniversalRowEmitCall

open BitProgram StructuredCalls
open SubexpKernelControl (Word)

abbrev Data := State 8 32

def resetState (a : Data) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 0 false) 1 false) 2 false, a.stacks⟩

end SubexponentialSAT.Subexp.UniversalRowEmitCall

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Filtered row records for the physical interpolation-code emitter

Inactive zero terms and unit factors are omitted from the emitted records.
This is proved as a polynomial identity, without identifying the two different
expression trees or assuming a desired evaluator result.
-/

namespace SubexponentialSAT.Subexp.UniversalRowSource

open scoped BigOperators
open SubexpSymbolicCost SubexpRowInterpolation SubexpRepresentedRows
open UniversalRowProgram

variable {C E : Type*} {Q : ℕ}

def factorData (ops : RingProgram C) (cache : NodeCache C Q) (i j : Fin Q) : Factor C :=
  ⟨cache.difference i j, (ops.negRun (cache.node j)).1⟩

def termData (ops : RingProgram C) (cache : NodeCache C Q)
    (s : Finset (Fin Q)) (d : Fin Q → C) (i : Fin Q) : Term C :=
  ⟨d i, cache.inverse i, (selected (s.erase i)).map (factorData ops cache i)⟩

def mapFactor {A : Type*} (f : C → A) (x : Factor C) : Factor A :=
  ⟨f x.inverseDifference, f x.negativeNode⟩

def mapTerm {A : Type*} (f : C → A) (x : Term C) : Term A :=
  ⟨f x.value, f x.inverseNode, x.factors.map (mapFactor f)⟩

end SubexponentialSAT.Subexp.UniversalRowSource

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowTableSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Indexed cache tables and the represented interpolation row

The physical producer reads natural-number indexed lists. This adapter
identifies those reads with the finite-indexed row specification, including
the mismatch filter and the cardinality guard. Its premises concern only
individual input cache entries, the delta word, and the limit's length.
-/

namespace SubexponentialSAT.Subexp.UniversalRowTableSource

open SubexpSymbolicCost SubexpRepresentedRows SubexpRowInterpolation
open UniversalRowSource

variable {C E A B : Type*} {Q : ℕ}

def positions (s : Finset (Fin Q)) : List ℕ :=
  (UniversalRowSource.selected s).map Fin.val

end SubexponentialSAT.Subexp.UniversalRowTableSource

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixParityProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A four-label program computes the sign parity of a unary index. The
bits of the counter are irrelevant; only its length is used. -/

namespace SubexponentialSAT.Subexp.MatrixParityProgram

open BitProgram

def start (regs : Fin 3 → Bool) (bits : List Bool) : Cfg 3 1 4 :=
  ⟨some 0, regs, fun _ => bits⟩

def finish (b : Bool) : Cfg 3 1 4 :=
  ⟨none, ![false, false, b], fun _ => []⟩

end SubexponentialSAT.Subexp.MatrixParityProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MismatchPlanProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

open BitProgram StructuredCalls StackRoutines

def keep (left right : List Word) (bits : Word) : Bool :=
  decide (left.getD bits.length [] ≠ right.getD bits.length [])

def mismatch (left right : List Word) (positions : List ℕ) : List ℕ :=
  positions.filter (fun i => decide (left.getD i [] ≠ right.getD i []))

end SubexponentialSAT.Subexp.MismatchPlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TypeBitProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed seven-label routine reads a runtime-indexed bit and clears its
two inputs. An out-of-range read returns false, as `List.getD` does. -/

namespace SubexponentialSAT.Subexp.TypeBitProgram

open BitProgram

abbrev cfg (pc : Option (Fin 7)) (regs : Fin 3 → Bool) (index bits : List Bool) : Cfg 3 2 7 :=
  ⟨pc, regs, ParserProgram.pair index bits⟩

end SubexponentialSAT.Subexp.TypeBitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

variable {V R : Type*} [DecidableEq V] [CommRing R]

def additionBudget (n B d u J : ℕ) : ℕ :=
  (u * J) * (220 * (2 * (u * J) + 1) * (n + u + J + d * B + 1) +
    Dictionary.codeBranchBudget B d + 2) + 3

def normalizationBudget (n B d u J N : ℕ) : ℕ :=
  N * (220 * (N + u * J + 1) * (n + u + J + d * B + 1) +
    Dictionary.codeBranchBudget B d + 2) + 3

/-- Polynomial in dimensions, coefficient width and ambient input length. -/
def productBudget (n B d u J : ℕ) : ℕ :=
  (u * J) * (Product.stepEnvelope B d n u J ((u * J) ^ 2) (u * J) + 2) + 3

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorProductSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The original concrete factor accumulator, with empty correction support.
All three tape moves and the original sparse product call are charged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram MomentsProgram

def budget (n B d u J : ℕ) : ℕ :=
  56 * byteBound n B d u J + TruncatedRingProgram.productBudget n B d u J + 54

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorEvaluationSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Immediate correction specialization keeps every factor dictionary over the
empty formal-variable support. The retained key capacity is polynomial u*J.
The bounds below apply to the actual native indicator, clause and product
programs, including their input parsers and paid tape cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram
open HashCircuitProgram HashCircuitProgram.Native MomentsProgram
open IdempotentApplyProgram.Steps

variable {p t n d : ℕ} [Fact p.Prime]

@[simp] theorem empty_capacity (u J : ℕ) (hJ : 0 < J) :
    IdempotentApplyProgram.Bounds.capacity (∅ : Finset (Fin n)) u J = u * J := by
  simp [IdempotentApplyProgram.Bounds.capacity, Squarefree.Sparse.supportUniverse,
    Finset.filter_singleton, hJ]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSpecializationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Immediate Boolean specialization using the actual dictionary scanner. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Subset
open OAI BitProgram StructuredProgram

def body : Cmd 5 3 :=
  .seq (.atom (.pop 0 0 1)) <|
  .seq (.atom (.pop 1 2 3)) <|
  .seq (.atom (.push 2 2)) <|
  .seq (.atom (.bnot 0 0)) <|
  .seq (.atom (.bor 0 0 2)) <|
  .seq (.atom (.band 4 4 0)) (.atom (.peek 0 0 1))

def loop : Cmd 5 3 := .while 1 body

def command : Cmd 5 3 := .seq (.atom (.set 4 true))
  (.seq (.atom (.peek 0 0 1)) loop)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Subset

/-! The dictionary framing, key rewrite and record traversal follow the actual
MomentsProjectionProgramNative implementation. The replacement comparator tests
support inclusion, so this scan implements evaluation at a Boolean correction
assignment. Numeric-key collisions are intentionally left for normalization. -/
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryProducerSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Immediate Boolean specialization followed by the actual additive dictionary
normalizer. The input is a polynomial-size origin/singleton incidence stream;
no multivariate product is materialized before specialization. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram
open scoped BigOperators

def frameBody : StructuredProgram.Cmd 8 38 :=
  .seq (.atom (.pop 35 0 1)) (.seq (.atom (.push 28 0))
    (.seq (.atom (.set 0 true)) (.seq (.atom (.push 28 0)) (.atom (.peek 35 0 1)))))

def frameLoop : StructuredProgram.Cmd 8 38 := .while 1 frameBody

def framer : StructuredProgram.Cmd 8 38 :=
  .seq (.atom (.set 0 false)) (.seq (.atom (.push 28 0))
    (.seq (.atom (.peek 35 0 1)) frameLoop))

def budget (n B d u J N L : ℕ) : ℕ :=
  200 * (L + 1) * (n + 2) + 1 + 6 * L + 6 +
    TruncatedRingProgram.normalizationBudget n B d u J N + 1

def preparedBudget (n B d u J N L : ℕ) : ℕ := 9 * n + 8 + budget n B d u J N L

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
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
open OAI BitProgram StructuredCalls SubexpConvolutionControl
open PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

def projectBase (s : OuterStore) : PerturbationAssembly.OuterStore := s ∘ basePort

noncomputable def replaceBase (s : OuterStore) (u : PerturbationAssembly.OuterStore) : OuterStore :=
  Function.extend basePort u s

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
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

namespace Native

open SubexpSetupStorage

def combinedBudget (lowWork cacheLength rawLength n B d u J count : ℕ) : ℕ :=
  let outputLength := u * J * (2 * (u + J + n) + 2 * (d * B) + 2)
  lowWork + 1 + (7 * cacheLength + 6 * rawLength + 21) +
    (preparedBudget n B d u J count rawLength +
      (6 * outputLength + 6 + 38 * (2 * (cacheLength + n + outputLength) + 3))) + 1



end Native

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed polynomial bounds for the actual factor-table service. The scalar
allowance includes physical signed-word lengths; it never bounds the integer
value of an exponential modulus or numerator in unary. All ambient source
rows and every specialized incidence record are included. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial
open OAI.Algorithms.SubexponentialSAT.Subexp
open FactorTableNative

def workspaceEnvelope (S : ℕ) : ℕ :=
  S+S*(S*(2*S))+UniversalRowSourceBound.indicesBound S

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_GuardedCompiler
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! A width-one compilation of Boolean programs, with empty pop guarded before
the primitive stack compiler. The output contract reads the entire tape. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler

open OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.StackCompiler OAI.Algorithms.SubexponentialSAT.StackEncoding OAI.Algorithms.SubexponentialSAT.StackMachine
open scoped BigOperators

def selected {r s l : ℕ} (p : BitProgram.Program r s l) (q : State r l) : Fin s :=
  match p.code q.1 with
  | .halt => p.outputStack
  | .push stack _ _ | .peek stack _ _ _ | .pop stack _ _ _ => stack
  | _ => p.inputStack

def transition {r s l : ℕ} (p : BitProgram.Program r s l) (q : State r l)
    (top : Option Bool) : Bool ⊕ (State r l × Mutation Bool) :=
  match p.code q.1 with
  | .halt => .inl (top.getD false)
  | .goto next => .inr ((next, q.2), .keep)
  | .set dst value next => .inr ((next, Function.update q.2 dst value), .keep)
  | .copy dst src next => .inr ((next, Function.update q.2 dst (q.2 src)), .keep)
  | .bnot dst src next => .inr ((next, Function.update q.2 dst (!(q.2 src))), .keep)
  | .band dst a b next => .inr ((next, Function.update q.2 dst (q.2 a && q.2 b)), .keep)
  | .bor dst a b next => .inr ((next, Function.update q.2 dst (q.2 a || q.2 b)), .keep)
  | .bxor dst a b next => .inr ((next, Function.update q.2 dst (q.2 a ^^ q.2 b)), .keep)
  | .branch test yes no => .inr (((if q.2 test then yes else no), q.2), .keep)
  | .push _ src next => .inr ((next, q.2), .push (q.2 src))
  | .peek _ value present next =>
      .inr ((next, BitProgram.readRegs q.2 value present top), .keep)
  | .pop _ value present next =>
      .inr ((next, BitProgram.readRegs q.2 value present top), guardedPop top)

def stackProgram {r s l : ℕ} (p : BitProgram.Program r s l) :
    StackProgram (State r l) (fun _ : Fin s => Bool) where
  inputTape := p.inputStack
  start := (p.entry, fun _ => false)
  select := selected p
  transition := transition p

def stackCfg {r s l : ℕ} (p : BitProgram.Program r s l) (c : BitProgram.Cfg r s l) :
    StackCfg (State r l) (fun _ : Fin s => Bool) :=
  ⟨match c.pc with
    | none => .inl ((c.stacks p.outputStack).head?.getD false)
    | some label => .inr (label, c.regs), c.stacks⟩

def codes (s : ℕ) : CodeFamily (fun _ : Fin s => Bool) := fun _ => boolCode

noncomputable abbrev primitive {r s l : ℕ} (p : BitProgram.Program r s l) : PrimitiveMachine :=
  reindex (Fintype.equivFin (StackCompiler.State (stackProgram p) (codes s)))
    (controller (stackProgram p) (codes s) (decoder s))

noncomputable abbrev primitiveCfg {r s l : ℕ} (p : BitProgram.Program r s l)
    (c : BitProgram.Cfg r s l) : (primitive p).Cfg :=
  reindexCfg (Fintype.equivFin (StackCompiler.State (stackProgram p) (codes s)))
    (controller (stackProgram p) (codes s) (decoder s))
    (encodeCfg (stackProgram p) (codes s) (stackCfg p c))

noncomputable abbrev primitiveControlCfg {r s l : ℕ} (p : BitProgram.Program r s l)
    (c : ControlCfg (StackCompiler.State (stackProgram p) (codes s)) s) :
    (primitive p).Cfg :=
  reindexCfg (Fintype.equivFin _) (controller (stackProgram p) (codes s) (decoder s)) c

@[simp] theorem primitive_tapeCount {r s l : ℕ} (p : BitProgram.Program r s l) :
    (primitive p).tapeCount = s := rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashCandidates
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
The hash stream visits binary payloads in increasing unsigned order and reduces
each indexed ternary digit modulo3*m before the existing row assembler. Every
original candidate is attained and unchanged by normalization. Extra normalized
duplicates preserve the minimum. Visits are bounded by the square of the old family.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamily

/-- Positive chunk width, computed from the ternary coordinate alphabet. -/
def digitWidth (m : ℕ) : ℕ := DyadicWidth.width (3 * m)

/-- Number of retained payload bits, rather than the number of candidates. -/
def payloadWidth (m depth : ℕ) : ℕ := depth * digitWidth m


/-- A proof-level partition of the one retained raw payload. Its length is
only the number of hash slots, never the number of candidates. -/
def chunks (m depth : ℕ) (raw : List Bool) : List (List Bool) :=
  (List.replicate depth (digitWidth m)).splitLengths raw.reverse

@[simp] theorem chunks_length (m depth : ℕ) (raw : List Bool) :
    (chunks m depth raw).length = depth := by simp [chunks]

/-- Canonicalization modulo the indexed ternary alphabet is performed before
lifting coefficients into the existing characteristic-3-power ring. -/
def normalize (m depth : ℕ) (raw : List Bool) : List Bool :=
  ((chunks m depth raw).map fun word =>
    SubexpLiftRing.fixedBits (digitWidth m) (BinaryArithmetic.toNat word % (3 * m))).flatten.reverse


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashCandidateProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog

namespace Normalize

def canonicalDigit (modulus chunk : List Bool) : List Bool :=
  SubexpLiftRing.fixedBits chunk.length
    (BinaryArithmetic.toNat chunk % BinaryArithmetic.toNat modulus)


end Normalize

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

namespace Initialize

open LeafOuterProgram

def savedRoutes : List Route := [(773,817),(768,780),(774,781)]

end Initialize

namespace NativeRound

def outer : HashSelectProgram.LoopPorts 40 896 where
  value := 8
  present := 9
  counter := 781
  value_ne_present := by decide

end NativeRound

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

def massPorts : Mass.Ports 40 896 where
  register i := i.castAdd 32
  stack := ![322,323,324]
  register_injective := Fin.castAdd_injective 8 32
  stack_injective := by decide


open LeafOuterProgram

open scoped BigOperators


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFactorCountSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

abbrev Data := State 8 13

end SubexponentialSAT.SubexpFactorCountSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SupportSelectionData
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Ordered support records selected from the actual packing inverse. -/

namespace SubexponentialSAT.Subexp.SupportSelectionProgram

open ConstructivePacking

variable {D r Q Δ : ℕ}

def indexWords (p : ℕ → Bool) (n : ℕ) : List (List Bool) :=
  ((List.range n).filter p).map unary

end SubexponentialSAT.Subexp.SupportSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSourceLocality
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete source locality for the streamed head evaluation.
The source correspondence is `NodeConcrete.fixedSourceRow_baseline_eq` in
LeafProgramNodeConcretePlan, the actual residualJet in
LeafProgramNodeConcreteResidual, and residualProduct in
LeafProgramNodeConcreteResidualProduct. Fixed-high bits cancel in the full
integer signatures; every correction specialization uses one common U. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog



open OAI SubexpLiftRing SubexpQuarticRing
open MulticolorTypes Subexp.ConstructivePacking
open LeafProgram LeafProgram.NodeConcrete
open LayoutProgram PerturbationAssembly Polynomial

noncomputable section

variable {r Q d n : ℕ}

/-- Canonical semantic state for the complete ambient assignment. Native
state comparisons need only identify its actual assignment word at145. -/
def stateFor (H : Finset (Fin n)) (high : H → Bool)
    (x : ResidualEmbedding.Free H → Bool) : Fin 768 → List Bool :=
  fun i => if i=145 then List.ofFn (HighIncidence.glue H high x) else []

@[simp] theorem stateFor_get (H : Finset (Fin n)) (high : H → Bool)
    (x : ResidualEmbedding.Free H → Bool) (v : Fin n) :
    (stateFor H high x 145).getD v.val false=HighIncidence.glue H high x v := by
  simp [stateFor, List.getD_eq_getElem?_getD, v.isLt]

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidenceSlotProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical local-slot query

The three preserved inputs are the encoded scope family and unary factor and
vertex indices. A real mask pass selects the preceding factors, and the checked
incidence scan counts them. No slot map or selected prefix is supplied as input.
-/

namespace SubexponentialSAT.SubexpIncidenceSlotProgram

open BitProgram StructuredCalls

def degree (scopes : List (List ℕ)) (e v : ℕ) : ℕ :=
  (Subexp.IncidencePlanSpec.incidenceFrom v 0 (scopes.take e)).length

noncomputable def maskResultRegs (regs : Fin 10 → Bool) : Fin 10 → Bool :=
  Function.extend maskReg (fun _ => false) regs

end SubexponentialSAT.SubexpIncidenceSlotProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighIncidenceProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The supplied high-coordinate odometer with a fixed-width exact accumulator.
The residual callback is an actual command; its interface is discharged by the
assembled query program. No branch family is stored on any source stack. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgram
open OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration OAI.Algorithms.SubexponentialSAT.ExecCNFTupleOdometer
open OAI.Algorithms.SubexponentialSAT.BinaryArithmetic
open scoped BigOperators

variable {R S : ℕ}

@[simp] theorem freeCoordinates_length {n : ℕ} (H : Finset (Fin n)) :
    (freeCoordinates H).length = n - H.card := by
  have h := Fintype.card_congr (freeRawOrder H)
  simpa only [Fintype.card_fin, OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence.remaining_variable_count] using h

def freeOrder {n : ℕ} (H : Finset (Fin n)) :
    Fin (n - H.card) ≃ {v : Fin n // v ∉ H} :=
  (finCongr (freeCoordinates_length H).symm).trans (freeRawOrder H)

/-- Inserting zeroes on H preserves the exact free-coordinate assignment. -/
def freeFill {n : ℕ} (H : Finset (Fin n)) (bits : Fin (n - H.card) → Bool) : Fin n → Bool :=
  OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence.glue H (fun _ => false) (fun v => bits ((freeOrder H).symm v))

@[simp] theorem freeFill_high {n : ℕ} (H : Finset (Fin n))
    (bits : Fin (n - H.card) → Bool) (v : H) : freeFill H bits v = false := by
  simp [freeFill, OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence.glue, v.property]

@[simp] theorem freeFill_order {n : ℕ} (H : Finset (Fin n))
    (bits : Fin (n - H.card) → Bool) (i : Fin (n - H.card)) :
    freeFill H bits (freeOrder H i) = bits i := by
  simp [freeFill, OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence.glue, (freeOrder H i).property]

def descendingHighMask {n : ℕ} (H : Finset (Fin n)) : List Bool :=
  (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.coordinates n).map (fun v => decide (v ∈ H))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNegatedQueryProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving complemented-literal queries

The clause iterator supplies a literal's unary word in reverse order. This
fixed program preserves that query on stack 0 and writes the reversed unary
word for the opposite literal on stack 1. Stacks 2 and 3 are empty workspaces
on entry and return. All costs below count actual finite-program transitions.
-/

namespace SubexponentialSAT.SubexpNegatedQueryProgram

open BitProgram StructuredCalls
open ParserProgram (pair)

/-- Exact complete execution count, including the final halt. -/
def steps (c : ℕ) : ℕ :=
  16 * (Encoding.encodeNat c).length +
    9 * (Encoding.encodeNat (SubexpFrontend.negateCode c)).length +
    SubexpNormalizeProgram.negateSteps c + 20

end SubexponentialSAT.SubexpNegatedQueryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTautologyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual encoded-clause tautology testing

The outer iterator reads unary literal records. For each literal, a concrete
program builds its opposite's query, copies the preserved clause, and runs the
proved encoded membership program. All data-dependent repetition is in those
finite programs and the record iterator.
-/

namespace SubexponentialSAT.SubexpTautologyProgram

open BitProgram StructuredCalls

def literalRecords (C : List ℕ) : List (List Bool) := C.map Encoding.encodeNat

end SubexponentialSAT.SubexpTautologyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual finite count-word positivity suffix. The counting body is integrated
separately; this suffix never interprets the least significant bit as SAT. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

opaque leafPortsWrapped :
    {ports : List (Fin 1220) // ports = (List.finRange 896).map ABI.leafStacks} :=
  ⟨(List.finRange 896).map ABI.leafStacks, rfl⟩

/-- The fixed leaf-bank ports, kept opaque so unrelated command proofs do not
reduce the complete 896-element cleanup table. -/
def leafPorts : List (Fin 1220) := leafPortsWrapped.1

def leafRegisterPorts : List (Fin 80) := (List.finRange 40).map ABI.leafRegisters

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighFrontendSources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Typed source and empty-workspace relations follow from the actual trial
and accepted source stages. Changing the marked clause does not change the
immutable source words; its scope and high mask are recomputed by the frontend. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendSources

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open HighMarkedFrontend

/-- The semantic dependent cast retains every physically encoded row word.
It changes no clause index value and introduces no runtime row traversal. -/
def castRows {m m' : ℕ} (h : m=m') (rows : HashScopeProgram.RawTable.Rows m) :
    HashScopeProgram.RawTable.Rows m' :=
  rows.map (List.map (fun term => (Fin.cast h term.1,term.2)))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendSources
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed encoded modular dot products

Vectors are streams of framed, fixed-width little-endian scalar words. The
loop reads the two streams itself and calls the measured multiply-add routine.
Its finite control is independent of the modulus, width, and vector length.
-/

namespace SubexponentialSAT.Subexp.MatrixProgram

open BitProgram StructuredCalls BinaryArithmetic
open MatrixScalarProgram

def dotValue (p : ℕ) : List (List Bool) → List (List Bool) → ZMod p
  | x :: xs, y :: ys => (BinaryArithmetic.toNat x : ZMod p) * (BinaryArithmetic.toNat y : ZMod p) + dotValue p xs ys
  | _, _ => 0

end SubexponentialSAT.Subexp.MatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixVectorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed row controller for encoded matrix-vector multiplication. -/

namespace SubexponentialSAT.Subexp.MatrixVectorProgram

open BitProgram StructuredCalls BinaryArithmetic
open MatrixScalarProgram MatrixProgram

def RowResult (p B : ℕ) (xs ys : List (List Bool)) (z : List Bool) : Prop :=
  z.length = B ∧ BinaryArithmetic.toNat z < p ∧ (BinaryArithmetic.toNat z : ZMod p) = dotValue p xs ys

end SubexponentialSAT.Subexp.MatrixVectorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SparseCodeSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch

open BitProgram StructuredCalls CodeCandidateProgram


open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram CodeChecks

def localSpace (A t D d : ℕ) : ℕ :=
  spaceBudget (t * D) (boundary A (t * D))
    (candidateSpace (boundary A (t * D)) (t * D) D (callbackBudget t D d))

def graphSpace (A D r qlen Dlen : ℕ) : ℕ :=
  spaceBudget (D * r) (boundary A (D * r))
    (candidateSpace (boundary A (D * r)) (D * r) r (graphCallbackBudget D r qlen Dlen))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed physical stages for the streamed local-code and graph-code searches.
The retained search state is confined to the lower48 leaf stacks; selected
matrices are saved outside that bank before its paid cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode

open BitProgram StructuredCalls
open SqrtLog SqrtLog.LeafOuterProgram SqrtLog.CodeSearchProgram

def graphInputs : List Route := [(808,30),(800,31),(801,32),(812,33),(813,46)]

def localInputs : List Route := [(809,19),(811,20),(808,21),(810,46)]

def graphStageSpace (A m occurrence qlen Dlen : ℕ) : ℕ :=
  max A (max (max (SparseCodeSearch.graphSpace A (SparseCode.degree m occurrence)
    (SparseCode.dimension m occurrence) qlen Dlen) A)
    (SparseCodeSearch.boundary A (SparseCode.degree m occurrence * SparseCode.dimension m occurrence)))

def localStageSpace (A m occurrence : ℕ) : ℕ :=
  max A (max (max (SparseCodeSearch.localSpace A (SparseCode.localRows m occurrence)
    (SparseCode.degree m occurrence)
    (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1)) A)
    (SparseCodeSearch.boundary A (SparseCode.localRows m occurrence * SparseCode.degree m occurrence)))


def graphBoundary (A m occurrence : ℕ) : ℕ := SparseCodeSearch.boundary A
  (SparseCode.degree m occurrence * SparseCode.dimension m occurrence)

def searchBoundary (A m occurrence : ℕ) : ℕ := SparseCodeSearch.boundary
  (graphBoundary A m occurrence) (SparseCode.localRows m occurrence * SparseCode.degree m occurrence)

def searchesSpace (A m occurrence qlen Dlen : ℕ) : ℕ :=
  max (graphStageSpace A m occurrence qlen Dlen)
    (localStageSpace (graphBoundary A m occurrence) m occurrence)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeCodeAssembly
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram SubexpSetupStorage

/-- The original physical row stage, independent of either old code-search
controller: inputs are the actually retained new search results. -/
def rowInputs : List Route :=
  [(801,3),(782,4),(768,5),(808,6),(809,7),(814,8),(816,9),(815,10),(812,11)]
def rowOutputs : List Route := [(12,777)]


def serializerTime (r D t W : ℕ) (dword mword width : List Bool) : ℕ :=
  10000 * (W + CodeRowsProgram.explicitCost r D t width.length dword.length mword.length + 1)

def afterBoundary (A m occurrence : ℕ) (dword mword width : List Bool) : ℕ :=
  NativeCode.searchBoundary A m occurrence +
    serializerTime (SparseCode.dimension m occurrence) (SparseCode.degree m occurrence)
      (SparseCode.localRows m occurrence) (NativeCode.searchBoundary A m occurrence)
      dword mword width

def afterSpace (A m occurrence qlen : ℕ) (dword mword width : List Bool) : ℕ :=
  max (NativeCode.searchesSpace A m occurrence qlen dword.length)
    (afterBoundary A m occurrence dword mword width)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

def unaryRegisters : Fin 2 ↪ Fin 80 := (Fin.castAddEmb 1).trans ABI.positivityRegisters


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafStartup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual loaded-leaf startup and canonical saved selector parameters. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram

def saveCanonicalTime (n m L : ℕ) : ℕ :=
  let I := 100 * (HashSelect.loopCap n m + 1) * (L + 1)
  I + 18 * (L + I) + 16

def canonicalStartTime (n m W : ℕ) : ℕ :=
  let S := CodeSetupOuterCost.startupConstant * (W + 1) ^ 4
  S + saveCanonicalTime n m (W + S)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete tape operations and traversal assertions for the outer CRT.
All operations in this module are fixed finite programs. Arithmetic is supplied
by the separately defined concrete CRT service commands. -/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open BitProgram StructuredCalls

@[simp] theorem sweepStore_jet (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 225 = w.jet := rfl

@[simp] theorem update_sweepStore_jet (f : Fin 320 → List Bool) (w : SweepWords)
    (bits : List Bool) :
    Function.update (sweepStore f w) 225 bits = sweepStore f {w with jet := bits} := by
  funext j
  by_cases h : j = (225 : Fin 320)
  · subst j; simp [sweepStore]
  · simp [sweepStore, h]

@[simp] theorem sweepStore_remaining (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 257 = w.remaining := rfl

@[simp] theorem update_sweepStore_remaining (f : Fin 320 → List Bool) (w : SweepWords)
    (bits : List Bool) :
    Function.update (sweepStore f w) 257 bits = sweepStore f {w with remaining := bits} := by
  funext j
  by_cases h : j = (257 : Fin 320)
  · subst j; simp [sweepStore]
  · simp [sweepStore, h]

@[simp] theorem sweepStore_processed (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 258 = w.processed := rfl

@[simp] theorem update_sweepStore_processed (f : Fin 320 → List Bool) (w : SweepWords)
    (bits : List Bool) :
    Function.update (sweepStore f w) 258 bits = sweepStore f {w with processed := bits} := by
  funext j
  by_cases h : j = (258 : Fin 320)
  · subst j; simp [sweepStore]
  · simp [sweepStore, h]

@[simp] theorem sweepStore_current (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 259 = w.current := rfl

@[simp] theorem update_sweepStore_current (f : Fin 320 → List Bool) (w : SweepWords)
    (bits : List Bool) :
    Function.update (sweepStore f w) 259 bits = sweepStore f {w with current := bits} := by
  funext j
  by_cases h : j = (259 : Fin 320)
  · subst j; simp [sweepStore]
  · simp [sweepStore, h]

@[simp] theorem sweepStore_index (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 260 = w.index := rfl

@[simp] theorem update_sweepStore_index (f : Fin 320 → List Bool) (w : SweepWords)
    (bits : List Bool) :
    Function.update (sweepStore f w) 260 bits = sweepStore f {w with index := bits} := by
  funext j
  by_cases h : j = (260 : Fin 320)
  · subst j; simp [sweepStore]
  · simp [sweepStore, h]

@[simp] theorem sweepStore_accumulator (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 261 = w.accumulator := rfl

@[simp] theorem update_sweepStore_accumulator (f : Fin 320 → List Bool) (w : SweepWords)
    (bits : List Bool) :
    Function.update (sweepStore f w) 261 bits = sweepStore f {w with accumulator := bits} := by
  funext j
  by_cases h : j = (261 : Fin 320)
  · subst j; simp [sweepStore]
  · simp [sweepStore, h]

@[simp] theorem sweepStore_jets (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 266 = w.jets := rfl

@[simp] theorem update_sweepStore_jets (f : Fin 320 → List Bool) (w : SweepWords)
    (bits : List Bool) :
    Function.update (sweepStore f w) 266 bits = sweepStore f {w with jets := bits} := by
  funext j
  by_cases h : j = (266 : Fin 320)
  · subst j; simp [sweepStore]
  · simp [sweepStore, h]

@[simp] theorem sweepStore_width (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 104 = f 104 := rfl

@[simp] theorem sweepStore_jetWidth (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 277 = f 277 := rfl

@[simp] theorem sweepStore_counter (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 278 = f 278 := rfl

@[simp] theorem sweepStore_takeTmp (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 279 = f 279 := rfl

@[simp] theorem sweepStore_copyTmp (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 318 = f 318 := rfl

def loadedWords (w : SweepWords) (node nodes jet jets : List Bool) : SweepWords :=
  {w with
    remaining := nodes
    current := node
    nodeCopy := node
    indexCopy := w.index
    jet := jet
    jets := jets}

def cleanedWords (w : SweepWords) : SweepWords :=
  {w with nodeCopy := [], indexCopy := [], jet := [], current := []}

def advancedWords (w : SweepWords) : SweepWords :=
  {cleanedWords w with processed := w.current ++ w.processed, index := false :: w.index}

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterSweep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Ordered execution of the concrete outer CRT tape loop. The only remaining
premise is an actual execution of its arithmetic middle command on the exact
loaded state; all loading, index updates, traversal guards, and transport costs
are discharged here. This premise is instantiated by the concrete CRT services.
-/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open BitProgram StructuredCalls

def readyWords {I A : Type*} (encode : I → List Bool) (jet : I → List Bool)
    (encodeAcc : A → List Bool) (processed remaining : List I) (acc : A) : SweepWords :=
  { remaining := remaining.flatMap encode
    processed := processed.flatMap encode
    index := List.replicate processed.length false
    accumulator := encodeAcc acc
    jets := remaining.flatMap jet }

def loadedReady {I A : Type*} (encode : I → List Bool) (jet : I → List Bool)
    (encodeAcc : A → List Bool) (processed remaining : List I) (item : I) (acc : A) :
    SweepWords :=
  loadedWords (readyWords encode jet encodeAcc processed (item :: remaining) acc)
    (encode item) (remaining.flatMap encode) (jet item) (remaining.flatMap jet)

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete bit primitives for streamed finite-difference queries. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram

open OAI BitProgram
open scoped BigOperators

open StructuredCalls

section SignedArray

attribute [local simp] Fin.coe_ofNat_eq_mod

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

def signedAccumulateBudget (n B d u J : ℕ) : ℕ :=
  signedScalingBudget n B d u J + TruncatedRingProgram.additionBudget n B d u J + 1

def pairUpdateBudget (n B d u J E U : ℕ) : ℕ :=
  10 * (E + U) + signedAccumulateBudget n B d u J + 20

end SignedArray

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

open BitProgram StructuredCalls

/-- Suspended generator records only; no completed tuples or key family. -/
def suspendedFrames (frames : List (List Bool)) : List Bool :=
  frames.flatMap fun word => Encoding.frame word.reverse

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_RingNodeSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid traversal of the actual framed node table. The remaining cursor and
unary index are physical stacks, and the decoded node is transferred to the
original factor port. No list of semantic nodes is manufactured by the machine. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeSetup

open OAI BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram

def initialized (s : Store) : Store :=
  {s with source := s.frame 300, payload := [], temporary := [], index := [], node := []}

def initializeCost (s : Store) : ℕ :=
  2*(s.source.length+s.payload.length+s.temporary.length+s.index.length+s.node.length)+
    7*(s.frame 300).length+20

def nodeRead (s : Store) (bits : List Bool) (tail : List (List Bool)) : Store :=
  {s with source := Encoding.encodeList id tail, payload := [], node := bits}

def nodeRegs (regs : Fin 40 → Bool) : Fin 40 → Bool :=
  readRegs (parserRegs regs false true (regs 39)) 0 1 none

/-- The node reader has no hidden persistent writes. -/
theorem nodeRead_frame (s : Store) (bits : List Bool) (tail : List (List Bool))
    (i : Fin 768) (h301 : i ≠ 301) (h302 : i ≠ 302) (h78 : i ≠ 78) :
    tapes (nodeRead s bits tail) i = tapes s i := by
  simp [nodeRead, tapes, h301, h302, h78]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeSetup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFlatCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Count decisions from the actual flat coefficient representation

Coefficients are stored constant-first, with four consecutive little-endian
words per coefficient. Width and modulus are runtime data. This adapter reads
the first word, discards the unused polynomial suffix, and executes the checked
remainder-and-positivity program. It does not serialize the array into records.
-/

namespace SubexponentialSAT.SubexpFlatCount

open BitProgram StructuredCalls ProgramLinking

abbrev Data := State 8 8

def start (regs : Fin 8 → Bool) (modulus width input : List Bool) : Data :=
  ⟨regs, store input modulus [] width⟩

def finish (regs : Fin 8 → Bool) (modulus width word : List Bool) : Data :=
  ⟨regs, store [] modulus word width⟩

def reset (regs : Fin 8 → Bool) : Fin 8 → Bool := readRegs regs 0 1 none

def peekState (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 (d.stacks 0).head?, d.stacks⟩

end SubexponentialSAT.SubexpFlatCount

end OAI.Algorithms
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

def budget (S : ℕ) : ℕ :=
  2400*(ReconstructionProgram.Native.costConstant+1)^4*(S+1)^96+1 +
    4400*(2*(S+1)^2+1)^2 + 4*S+7

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleInit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete initialization of one attained-signature tuple product. The
multiplicative identity is built by the native cache routine, and every stale
output and borrowed word is cleared by an actual command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleInit

open OAI BitProgram StructuredCalls SubexpSetupStorage
open SqrtLog SqrtLog.LeafProgram

/-- Exact changed ports; every other caller word, including tuple and node
controllers, is retained byte for byte. -/
def changed : List (Fin 896) := entryPorts ++
  FactorAssignmentProgram.cachePorts.map FactorAssignmentProgram.lowStack ++ [852, 869]


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleInit
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleSum
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete unsigned tuple accumulation. The complete head product on852
is normalized into the pair accumulator851. Physical caches are copied from
retained masters and every native peripheral scratch word is paid for. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

def budget (n B d u J incoming : ℕ) : ℕ :=
  75*incoming+97+additionBudget n B d u J

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleTraversal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

abbrev Representatives (key : (d : ℕ) → Fin (N d) → κ d) (d : ℕ) :=
  AttainedSignatures.Representative (key d)

/-- The finite prefix specifies the suspended candidate frames,
in root-to-current order. Exhaustion is represented by `candidate = N depth`. -/
inductive Cursor (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
  | scan (depth : Fin levels) (ancestors : Prefix (Representatives key) depth.val)
      (candidate : ℕ)
  | leaf (ancestors : Prefix (Representatives key) levels)
  | halt

/-- Every probe, including a losing one, every exhausted generator, and every
leaf callback has its own event. None of these domains is stored at runtime. -/
inductive Event (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
  | candidate (depth : Fin levels) (ancestors : Prefix (Representatives key) depth.val)
      (candidate : Fin (N depth.val))
  | exhausted (depth : Fin levels) (ancestors : Prefix (Representatives key) depth.val)
  | leaf (ancestors : Prefix (Representatives key) levels)

def enter (key : (d : ℕ) → Fin (N d) → κ d) (levels depth : ℕ)
    (hd : depth ≤ levels) (ancestors : Prefix (Representatives key) depth) : Cursor key levels :=
  if h : depth = levels then .leaf (h ▸ ancestors)
  else .scan ⟨depth, lt_of_le_of_ne hd h⟩ ancestors 0

def leave (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ) :
    (depth : ℕ) → depth ≤ levels → Prefix (Representatives key) depth → Cursor key levels
  | 0, _, _ => .halt
  | depth + 1, hd, ancestors => .scan ⟨depth, by omega⟩ (Fin.init ancestors)
      ((ancestors (Fin.last depth)).val.val + 1)

@[simp] theorem enter_internal (key : (d : ℕ) → Fin (N d) → κ d)
    (levels depth : ℕ) (hd : depth < levels) (ancestors : Prefix (Representatives key) depth) :
    enter key levels depth hd.le ancestors = .scan ⟨depth, hd⟩ ancestors 0 := by
  simp [enter, Nat.ne_of_lt hd]

@[simp] theorem enter_leaf (key : (d : ℕ) → Fin (N d) → κ d)
    (levels : ℕ) (ancestors : Prefix (Representatives key) levels) :
    enter key levels levels le_rfl ancestors = .leaf ancestors := by simp [enter]

@[simp] theorem leave_snoc (key : (d : ℕ) → Fin (N d) → κ d)
    (levels depth : ℕ) (hd : depth < levels) (ancestors : Prefix (Representatives key) depth)
    (rep : Representatives key depth) :
    leave key levels (depth + 1) hd (Fin.snoc ancestors rep) =
      .scan ⟨depth, hd⟩ ancestors (rep.val.val + 1) := by
  simp [leave]

/-- These are exactly the four controller branches, including advancement
only after a child has returned. Root exhaustion alone halts the cursor. -/
inductive Step (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ) :
    Event key levels → Cursor key levels → Cursor key levels → Prop
  | fresh (depth : Fin levels) (ancestors : Prefix (Representatives key) depth.val)
      (rep : Representatives key depth.val) :
      Step key levels (.candidate depth ancestors rep.val)
        (.scan depth ancestors rep.val.val)
        (enter key levels (depth.val + 1) depth.isLt (Fin.snoc ancestors rep))
  | duplicate (depth : Fin levels) (ancestors : Prefix (Representatives key) depth.val)
      (candidate : Fin (N depth.val))
      (hd : ¬ ∀ j, j < candidate → key depth.val j ≠ key depth.val candidate) :
      Step key levels (.candidate depth ancestors candidate)
        (.scan depth ancestors candidate.val) (.scan depth ancestors (candidate.val + 1))
  | exhausted (depth : Fin levels) (ancestors : Prefix (Representatives key) depth.val) :
      Step key levels (.exhausted depth ancestors) (.scan depth ancestors (N depth.val))
        (leave key levels depth.val depth.isLt.le ancestors)
  | leaf (ancestors : Prefix (Representatives key) levels) :
      Step key levels (.leaf ancestors) (.leaf ancestors) (leave key levels levels le_rfl ancestors)

/-- A proof-level weighted trace. Taking indicator weights states exact
visit counts; taking natural costs charges actual source evaluations. -/
inductive Trace {key : (d : ℕ) → Fin (N d) → κ d} {levels : ℕ}
    {M : Type*} [AddMonoid M] (weight : Event key levels → M) :
    M → Cursor key levels → Cursor key levels → Prop
  | refl (a) : Trace weight 0 a a
  | step {event a b c total} : Step key levels event a b → Trace weight total b c →
      Trace weight (weight event + total) a c

/-- Weighted subtree size. The recursive sum is over first occurrences only;
the separate candidate sum charges every successful and losing probe. -/
noncomputable def subtreeTotal (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M] (weight : Event key levels → M) :
    (remaining depth : ℕ) → depth + remaining = levels →
      Prefix (Representatives key) depth → M := by
  classical
  intro remaining
  induction remaining with
  | zero =>
      intro depth h ancestors
      have he : depth = levels := by omega
      exact weight (.leaf (he ▸ ancestors))
  | succ remaining ih =>
      intro depth h ancestors
      let d : Fin levels := ⟨depth, by omega⟩
      exact (∑ i : Fin (N depth), weight (.candidate d ancestors i)) +
        weight (.exhausted d ancestors) +
        ∑ rep : Representatives key depth, ih (depth + 1) (by omega) (Fin.snoc ancestors rep)

/-- The exact charge of the invocation domain at one depth. -/
noncomputable def levelTotal (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M] (weight : Event key levels → M) (depth : ℕ) : M :=
  if hd : depth < levels then
    ∑ ancestors : Prefix (Representatives key) depth,
      ((∑ i : Fin (N depth), weight (.candidate ⟨depth, hd⟩ ancestors i)) +
        weight (.exhausted ⟨depth, hd⟩ ancestors))
  else 0

/-- Sum over every internal attained prefix and every complete attained tuple.
Each candidate and exhaustion appears once per internal invocation. -/
noncomputable def eventTotal (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M] (weight : Event key levels → M) : M :=
  (∑ depth ∈ Finset.range levels, levelTotal key levels weight depth) +
    ∑ ancestors : Prefix (Representatives key) levels, weight (.leaf ancestors)

/-- Per-candidate comparison charge; the index is a binary counter value,
not a retained word length. The rescan uses precisely its predecessors. -/
def costWeight (key : (d : ℕ) → Fin (N d) → κ d) (levels poly leafCost : ℕ) :
    Event key levels → ℕ
  | .candidate _ _ candidate => poly * (candidate.val + 1)
  | .exhausted _ _ => poly
  | .leaf _ => leafCost

/-- Only leaves alter the mathematical callback accumulator. -/
def callbackWeight (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [Zero M] (value : Prefix (Representatives key) levels → M) :
    Event key levels → M
  | .candidate _ _ _ => 0
  | .exhausted _ _ => 0
  | .leaf ancestors => value ancestors

section KeyEncoding

/-- Reloading or changing the faithful physical encoding of a full key does
not change its first-occurrence candidate. The equivalence fixes every index. -/
def representativeKernelEquiv {n : ℕ} {A B : Type*}
    (actual : Fin n → A) (model : Fin n → B)
    (hkernel : ∀ i j, actual i = actual j ↔ model i = model j) :
    AttainedSignatures.Representative actual ≃ AttainedSignatures.Representative model where
  toFun i := ⟨i.val, fun j hj he => i.property j hj ((hkernel j i.val).mpr he)⟩
  invFun i := ⟨i.val, fun j hj he => i.property j hj ((hkernel j i.val).mp he)⟩
  left_inv _ := rfl
  right_inv _ := rfl

end KeyEncoding

section AttainedLabels

open OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments

variable {G : Type*} {A L : G → Type*} [∀ g, Fintype (A g)] [∀ g, DecidableEq (L g)]

/-- The finset subtype used by head grouping and the set-range subtype used
by first occurrences have the same actual label, with no added restriction. -/
def rangeLabelEquiv (label : ∀ g, A g → L g) (g : G) :
    Set.range (label g) ≃ LabelValue label g where
  toFun y := ⟨y.val, by
    obtain ⟨a, ha⟩ := y.property
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩⟩
  invFun y := ⟨y.val, by
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp y.property
    exact ⟨a, ha⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A bounded assignment enumerator reindexes attained labels without
requiring its chosen representative to satisfy a correction restriction. -/
noncomputable def representativeLabelEquiv {count : G → ℕ}
    (enumerate : ∀ g, Fin (count g) ≃ A g) (label : ∀ g, A g → L g) (g : G) :
    AttainedSignatures.Representative (fun i => label g (enumerate g i)) ≃ LabelValue label g :=
  (AttainedSignatures.representativeEquiv (fun i => label g (enumerate g i))).trans
    ((rangeEnumerateEquiv enumerate label g).trans
      (rangeLabelEquiv label g))

@[simp] theorem representativeLabelEquiv_value {count : G → ℕ}
    (enumerate : ∀ g, Fin (count g) ≃ A g) (label : ∀ g, A g → L g) (g : G)
    (rep : AttainedSignatures.Representative (fun i => label g (enumerate g i))) :
    (representativeLabelEquiv enumerate label g rep).val = label g (enumerate g rep.val) := by
  change ((AttainedSignatures.representativeEquiv
    (fun i ↦ label g (enumerate g i))) rep).val = label g (enumerate g rep.val)
  exact AttainedSignatures.representativeEquiv_value _ rep

noncomputable def representativeLabelTupleEquiv {count : G → ℕ}
    (enumerate : ∀ g, Fin (count g) ≃ A g) (label : ∀ g, A g → L g) :
    (∀ g, AttainedSignatures.Representative (fun i => label g (enumerate g i))) ≃
      (∀ g, LabelValue label g) :=
  Equiv.piCongrRight (representativeLabelEquiv enumerate label)

end AttainedLabels

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal
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

def keyCostBound (n D B L : ℕ) : ℕ :=
  let R := matrixBound n D B L
  7*R+D*(BucketProgram.signatureRowBound (List.replicate L false) n R+2)+8

def keySpaceBound (n D B L : ℕ) : ℕ :=
  16*(L+n+matrixBound n D B L)+keyCostBound n D B L+1


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleReadoutSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact readout of the emitted first-occurrence tuples. The equivalences
below preserve the numeric representative at every head. They are proof-level
reindexings of the native traversal, not stored families or evaluator services. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleReadoutSemantics

open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog Moments SignatureTupleDFS SignatureTupleTraversal
open Classical

section Representatives

variable {r : ℕ} {count : ℕ → ℕ} {K : ℕ → Type*}
    {X L : Fin r → Type*} [∀ g, Fintype (X g)] [∀ g, DecidableEq (L g)]

/-- Actual full-key equality and source-label equality identify the same
first occurrence. The underlying bounded candidate is unchanged. -/
def tupleLabelEquiv (key : (i : ℕ) → Fin (count i) → K i)
    (enumerate : ∀ g : Fin r, Fin (count g.val) ≃ X g)
    (label : ∀ g, X g → L g)
    (hkernel : ∀ g i j, key g.val i = key g.val j ↔
      label g (enumerate g i) = label g (enumerate g j)) :
    Prefix (Representatives key) r ≃ (∀ g, LabelValue label g) :=
  (Equiv.piCongrRight (fun g : Fin r =>
    representativeKernelEquiv (key g.val) (fun i => label g (enumerate g i))
      (hkernel g))).trans (representativeLabelTupleEquiv enumerate label)

@[simp] theorem tupleLabelEquiv_value (key : (i : ℕ) → Fin (count i) → K i)
    (enumerate : ∀ g : Fin r, Fin (count g.val) ≃ X g)
    (label : ∀ g, X g → L g)
    (hkernel : ∀ g i j, key g.val i = key g.val j ↔
      label g (enumerate g i) = label g (enumerate g j))
    (reps : Prefix (Representatives key) r) (g : Fin r) :
    (tupleLabelEquiv key enumerate label hkernel reps g).val =
      label g (enumerate g (reps g).val) := rfl

/-- The attained-label grouping chooses the same assignments that the actual
first-occurrence traversal emitted; no correction restriction is added. -/
def labelRepresentatives (key : (i : ℕ) → Fin (count i) → K i)
    (enumerate : ∀ g : Fin r, Fin (count g.val) ≃ X g)
    (label : ∀ g, X g → L g)
    (hkernel : ∀ g i j, key g.val i = key g.val j ↔
      label g (enumerate g i) = label g (enumerate g j))
    (y : ∀ g, LabelValue label g) (g : Fin r) : LabelBucket label g (y g) :=
  ⟨enumerate g (((tupleLabelEquiv key enumerate label hkernel).symm y) g).val,
    congrArg (fun z => (z g).val)
      ((tupleLabelEquiv key enumerate label hkernel).apply_symm_apply y)⟩

@[simp] theorem labelRepresentatives_emitted
    (key : (i : ℕ) → Fin (count i) → K i)
    (enumerate : ∀ g : Fin r, Fin (count g.val) ≃ X g)
    (label : ∀ g, X g → L g)
    (hkernel : ∀ g i j, key g.val i = key g.val j ↔
      label g (enumerate g i) = label g (enumerate g j))
    (reps : Prefix (Representatives key) r) (g : Fin r) :
    (labelRepresentatives key enumerate label hkernel
      (tupleLabelEquiv key enumerate label hkernel reps) g).val =
      enumerate g (reps g).val := by
  simp only [labelRepresentatives, Equiv.symm_apply_apply]

end Representatives

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleReadoutSemantics
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleWords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact physical words for the emitted numeric head representatives. These
are proof-level coordinate maps; the executable cursor retains only its bounded
binary word and uses the existing native selected-coordinate scan. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleWords
open Classical
open OAI.Algorithms.SubexponentialSAT.SqrtLog

open BucketTupleProgram.Concrete HeadIdentifierProgram

/-- An ambient extension used only to identify the physical selected bits. -/
def ambientAssignment {n r : ℕ} (H : Finset (Fin n)) (head : Fin n → Fin r)
    (g : Fin r) (x : Moments.Head (fun v : {v : Fin n // v∉H} => head v.val) g → Bool) :
    Fin n → Bool := fun v =>
  if hv : v∉H then if hg : head v=g then x ⟨⟨v,hv⟩,hg⟩ else false else false

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleWords
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Complete runs of the fixed attained-signature controller. The retained
boundary cap is separate from transient prefix storage and measured time. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun

open Classical
open OAI SubexpLiftRing BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram
open SignatureTupleNative SignatureTupleLoader
open SignatureTupleComplete

/-- The mathematical sum over attained tuples, with its finite instance fixed
before specialization to a concrete integer signature. This is proof-side data;
the controller stores only one attained path. -/
noncomputable def tupleTotal {N : ℕ → ℕ} {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M] (value : Prefix (Representatives key) levels → M) : M :=
  ∑ ancestors, value ancestors

/-- The mathematical attained-prefix count, independent of runtime storage. -/
noncomputable def tupleCount {N : ℕ → ℕ} {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ) : ℕ :=
  prefixCount (fun depth => Fintype.card (Representatives key depth)) levels

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafContract
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform correctness and resources for the fixed native leaf. The final
contract instantiates the actual preparation, marked rounds and accepted
query; only numerical bounds produced by the outer program remain. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
open BitProgram StructuredCalls DisjointReuse SparseDFSRefinement

def time (n k localTime bound : ℕ) : ℕ :=
  3624 * bound + 100 * (SparseCountProgram.formulaBound n k + 1) +
    11 * n + localTime + 5479

open SqrtLog Filter
open scoped Topology

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_ScheduleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual binary construction of the disjoint-sparsification parameter.
All arithmetic uses fixed finite programs; the input numeral is runtime stack data. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ScheduleProgram

open BitProgram StructuredCalls
open BinaryArithmetic (toNat)

def squarePorts : ArithmeticCalls.Ports 32 where
  left := 2
  right := 2
  out := 3
  work := work5
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left i := by
    intro h
    have hv := congrArg Fin.val h
    change 6 + i.val = _ at hv
    omega
  work_ne_right i := by
    intro h
    have hv := congrArg Fin.val h
    change 6 + i.val = _ at hv
    omega
  work_ne_out i := by
    intro h
    have hv := congrArg Fin.val h
    change 6 + i.val = _ at hv
    omega

def sqrtPorts : SqrtLog.LeafParameterArithmetic.SqrtPorts 32 where
  input := 1
  out := 4
  work := work13
  out_ne_input := by decide
  work_ne_input i := by
    intro h
    have hv := congrArg Fin.val h
    change 6 + i.val = _ at hv
    omega
  work_ne_out i := by
    intro h
    have hv := congrArg Fin.val h
    change 6 + i.val = _ at hv
    omega

def quotientPorts : SqrtLog.LeafParameterArithmetic.QuotientPorts 32 where
  left := 4
  right := 3
  out := 5
  work := work6
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left i := by
    intro h
    have hv := congrArg Fin.val h
    change 6 + i.val = _ at hv
    omega
  work_ne_right i := by
    intro h
    have hv := congrArg Fin.val h
    change 6 + i.val = _ at hv
    omega
  work_ne_out i := by
    intro h
    have hv := congrArg Fin.val h
    change 6 + i.val = _ at hv
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ScheduleProgram
end


