-- Prove2me | Definitions.Def_OAIQ081S184
-- name    : OAIQ081S184
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:32:48.550744+00:00
-- url     : https://prove2.me/theorems/c6cf8e6f-4aa3-42e0-a082-03134b7144ab
-- title:
--   Definitions bundle OAIQ081S184 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 5 definitions and 5 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.betaCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.tableTime`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.markedBranchBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.specializedLiteralWork`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.entry`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLogSpace_FactorAssignmentBranches`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorAssignmentBranches.lean), [`SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallbackNative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorAssignmentCallbackNative.lean), [`SubexponentialSAT_SqrtLogSpace_FactorTableNative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableNative.lean), [`SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureHeadLoaderCore.lean), [`SubexponentialSAT_SqrtLog_PackingCallerProgramState`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingCallerProgramState.lean), [`SubexponentialSAT_SqrtLog_PackingProgramAssemblyIncidence`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingProgramAssemblyIncidence.lean), [`SubexponentialSAT_SqrtLog_PackingProgramAssemblyRefinement`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingProgramAssemblyRefinement.lean), [`SubexponentialSAT_SqrtLog_PackingProgramAssemblyRun`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingProgramAssemblyRun.lean), [`SubexponentialSAT_SqrtLog_PackingProgramAssemblyScope`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingProgramAssemblyScope.lean), [`SubexponentialSAT_SqrtLog_PerturbationBetaProgramRun`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationBetaProgramRun.lean).
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S174`, `OAIQ081S176` and `OAIQ081S177` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S187` and `OAIQ081S188`; the statement `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.betaCommand_run`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.NodeBoundary.sourceBank` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.betaCommand_run`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S174
import Definitions.Def_OAIQ081S176
import Definitions.Def_OAIQ081S177

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

def betaCommand : Code := .seq prepareInput (.seq (.seq peekRow loop) finish)

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical source preparation for the specialized factor table. The old
master-word argument is generalized to the actually selected unary factor,
then transported through the fixed protected-port embedding. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram
open PerturbationAssembly LayoutProgram SubexpSetupStorage DensePolynomialProgram
open OAI.Algorithms.SubexponentialSAT.Subexp OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q d n J S f : ℕ} {p : SourceBank.Parameters r Q d}
    {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {a : SourceReady.Data} {theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d}


def specializedLiteralWork {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (u J n S H : ℕ) : ℕ :=
  7*n + (10*n+9*H+18+(10*n+42*n+29*(d*baseWidth 3 p.t)+109)+
    (Source.nativeSourceWorkPolynomial p S+1+
      (7*n+5+specializedWorkPolynomial p.t d u J (p.R+1) n S))) +
    22*(n+1)+19*specializedPayloadBound n u J (baseWidth 3 p.t) d+
    2*(n*(2*((p.R+1)*(d*baseWidth 3 p.t))+2)+1)+54

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentBranches
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual ordinary and marked factor branches. The physical factor ID is
converted to the unary source counter, then the specialized table is produced
before the original finite-ring arithmetic is run. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open FactorAssignmentProgram
open Subexp.ConstructivePacking MulticolorTypes LayoutProgram DensePolynomialProgram

noncomputable def tableTime {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (u J n B S : ℕ) (a : FactorAssignmentProgram.Data) (factor : ℕ) : ℕ :=
  FactorTableSpace.commandBudget B n
    (FactorTableNative.specializedLiteralWork p u J n S
      ((FactorTableProgram.staged (tableInput a factor)).stacks 574).length)
    (FactorTableNative.specializedPayloadBound n u J (baseWidth 3 p.t) d)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallbackNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete physical inputs for the streamed factor callback. The source
context is the actual q.ctx, and the dispatcher determines every selected row
and clause. These predicates contain stored words and finite size bounds only.
Their construction from the actual loader/cache run remains an integration step. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open FactorAssignmentProgram
open Subexp.ConstructivePacking MulticolorTypes LayoutProgram DensePolynomialProgram

noncomputable section

variable {r Q n d A S : ℕ} {q : Factor.Spec r Q n d}
  {one seed : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d}
  {a : FactorAssignmentProgram.Data} {f : ℕ}

/-- Explicit paid cost of the actual marked-clause branch. -/
def markedBranchBudget (q : Factor.Spec r Q n d) (A S : ℕ)
    (a : FactorAssignmentProgram.Data) (f : ℕ) (rf : Fin 8 → Bool) : ℕ :=
  7 * (f + 1) + 7 +
    FactorAssignmentBranches.tableTime q.p q.u q.J n A S (fetched q a f rf) f +
    (9 * ((fetched q a f rf).stacks 154).length + 9 +
      FactorEvaluationSpace.serviceBudget (baseWidth 3 q.p.t) d n q.u q.J
        q.markedClause.length 0 0)

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed head-loader table uses the actual integer entry program. Its
physical matrix view follows LeafHeadSetupProgramHead/MatrixRun exactly, while
its controller emits one matrix and never constructs assignment tables. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

def entry : Cmd 16 256 :=
  LayoutFiberSumProgram.command LayoutProgram.EntryBank.command

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyIncidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The real incidence scorer with paid parameter parking and restoration. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

section Run
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidence_eval (a : Word r Q) (tail fixed : List (Word r Q))
    (pairs : List (I × I)) (indices : List (V ⊕ E)) (hi : ∀ x,x∈indices)
    (remaining : ℕ) (raw : List PairScoreProgram.PlanPair) (d : Data)
    (nb sb mb rb : List Bool)
    (hraw : raw.Perm (pairs.map (PackingIncidenceProgram.incidencePair ivar factor indices)))
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (remaining+1) fixed d.stacks)
    (hh : SequentialProgram.HighState
      (environment (ScoreBuilderRawInput.environment 1 (a::tail) indices.length raw) nb sb mb rb) d.stacks)
    (hsize : remaining+1+fixed.length=indices.length) :
    ∃ t ≤ PackingIncidenceProgram.runtimeBound indices.length raw.length (a::tail).length
        (ReadPlan.wordWidth r Q)+12*parameterLength d+48,
      ∃ e : Data, Eval incidence t d e ∧
        e.stacks 0=ProgramEncoding.encodeRecords ((a::tail).map (fun candidate =>
          UnaryCompare.encode (PackingIncidenceProgram.incidenceNumerator ivar factor
            (a::tail) pairs indices a remaining (candidate::fixed)))) ∧
        (∀ j,j≠0→e.stacks j=d.stacks j) := by
  have hready : parkReady d := by
    intro j hjlo hjhi
    exact hm.scratch j ((show ∀ j : Fin 48,12 ≤ j.val→j.val ≤ 16→j∈SequentialProgram.scratchPorts by decide) j hjlo hjhi)
  have hloose : PackingIncidenceInput.LooseMemory a fixed remaining (parked d) := by
    constructor
    · simpa [parked_stack] using hm.assignment
    · simpa [parked_stack,ReadPlan.encodeWord_length] using hm.width
    · simpa [parked_stack] using hm.processed
    · intro j hj
      have hj12 : j≠12 := by intro he; subst j; omega
      have hj13 : j≠13 := by intro he; subst j; omega
      have hj14 : j≠14 := by intro he; subst j; omega
      have hj15 : j≠15 := by intro he; subst j; omega
      have hj20 : j≠20 := by intro he; subst j; omega
      have hj21 : j≠21 := by intro he; subst j; omega
      have hj22 : j≠22 := by intro he; subst j; omega
      have hj23 : j≠23 := by intro he; subst j; omega
      rw [parked_stack]
      simp only [hj12,hj13,hj14,hj15,hj20,hj21,hj22,hj23,or_self,ite_false]
      exact hm.scratch j ((show ∀ j : Fin 48,j.val < 8→j∈SequentialProgram.scratchPorts by decide) j hj)
  have hhigh : SequentialProgram.HighState
      (ScoreBuilderRawInput.environment 1 (a::tail) indices.length raw) (parked d).stacks := by
    intro j hj
    by_cases hp : j=20 ∨ j=21 ∨ j=22 ∨ j=23
    · rcases hp with rfl|rfl|rfl|rfl <;>
        simp [parked_stack,ScoreBuilderRawInput.environment,ScoreBuilderProgram.environment]
    · have h12 : j ≠ 12 := by intro h; subst j; norm_num at hj
      have h13 : j ≠ 13 := by intro h; subst j; norm_num at hj
      have h14 : j ≠ 14 := by intro h; subst j; norm_num at hj
      have h15 : j ≠ 15 := by intro h; subst j; norm_num at hj
      have h20 : j ≠ 20 := by intro h; subst j; exact hp (Or.inl rfl)
      have h21 : j ≠ 21 := by intro h; subst j; exact hp (Or.inr (Or.inl rfl))
      have h22 : j ≠ 22 := by intro h; subst j; exact hp (Or.inr (Or.inr (Or.inl rfl)))
      have h23 : j ≠ 23 := by intro h; subst j; exact hp (Or.inr (Or.inr (Or.inr rfl)))
      rw [parked_stack]
      simp only [h12,h13,h14,h15,hp,ite_false]
      simpa [environment,h20,h21,h22,h23] using hh j hj
  obtain ⟨ts,hts,b,hb,ho,hf⟩ := PackingIncidenceInput.run_from_memory_loose
    ivar factor a tail fixed pairs indices hi remaining raw (parked d) hraw hloose hhigh hsize
  have hbready : unparkReady b := by
    constructor
    · rw [hf _ (by decide),parked_stack]
      simpa using hready 16 (by decide) (by decide)
    · intro j hjlo hjhi
      rw [hf j (by intro he; subst j; omega),parked_stack]
      have hj : j=20 ∨ j=21 ∨ j=22 ∨ j=23 := by
        exact (show ∀ j : Fin 48,20 ≤ j.val→j.val ≤ 23→j=20∨j=21∨j=22∨j=23 by decide) j hjlo hjhi
      rcases hj with rfl|rfl|rfl|rfl <;> simp
  have hu := unpark_eval b hbready
  have hcost : (b.stacks 12).length+(b.stacks 13).length+
      (b.stacks 14).length+(b.stacks 15).length=parameterLength d := by
    simp [hf,parked_stack,parameterLength]
  have htrace := (park_eval d hready).seq (hb.seq hu)
  refine ⟨_,?_,unparked b,htrace,?_,?_⟩
  · rw [hcost]
    omega
  · simpa [unparked_stack] using ho
  · intro j hj
    have he := congrFun (unpark_after_output d b hready hf) j
    simpa [hj] using he

end Run
end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete execution of the complete weighted-score producer from memory. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

section Run
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem run_from_memory (a : Word r Q) (tail fixed : List (Word r Q))
    (pairs : List (I × I)) (indices : List (V ⊕ E)) (hi : ∀ x,x∈indices)
    (remaining heads s M : ℕ) (raw : List PairScoreProgram.PlanPair) (d : Data)
    (nb sb mb rb : List Bool)
    (hn : SubexponentialSAT.BinaryArithmetic.toNat nb=heads) (hs : SubexponentialSAT.BinaryArithmetic.toNat sb=s)
    (hmass : SubexponentialSAT.BinaryArithmetic.toNat mb=M) (hr : SubexponentialSAT.BinaryArithmetic.toNat rb=r)
    (hraw : raw.Perm (pairs.map (PackingIncidenceProgram.incidencePair ivar factor indices)))
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (remaining+1) fixed d.stacks)
    (hh : SequentialProgram.HighState
      (environment (ScoreBuilderRawInput.environment 1 (a::tail) indices.length raw) nb sb mb rb) d.stacks)
    (hsize : remaining+1+fixed.length=indices.length) :
    ∃ wi wh : List Bool, SubexponentialSAT.BinaryArithmetic.toNat wi=heads^2*s^2 ∧
      SubexponentialSAT.BinaryArithmetic.toNat wh=8*M^2*r^2 ∧
      wi.length ≤ 2*nb.length+2*sb.length+3 ∧ wh.length ≤ 2*mb.length+2*rb.length+6 ∧
      ∃ t ≤ runBudget ivar factor a tail fixed pairs indices raw heads remaining d wi wh,
      ∃ e : Data, Eval command t d e ∧
        e.stacks 0=ProgramEncoding.encodeRecords ((a::tail).map (fun candidate =>
          UnaryCompare.encode (candidateScore ivar factor (a::tail) pairs indices a heads s M remaining fixed candidate))) ∧
        (∀ j,j≠0→e.stacks j=d.stacks j) := by
  obtain ⟨ti,hti,b,hiRun,hbi,hbf⟩ := incidence_eval ivar factor a tail fixed pairs indices hi remaining raw d
    nb sb mb rb hraw hm hh hsize
  have hd20 : d.stacks 20=nb := by simpa [environment] using hh 20 (by decide)
  have hd21 : d.stacks 21=sb := by simpa [environment] using hh 21 (by decide)
  have hd22 : d.stacks 22=mb := by simpa [environment] using hh 22 (by decide)
  have hd23 : d.stacks 23=rb := by simpa [environment] using hh 23 (by decide)
  have hd30 : d.stacks 30=ProgramEncoding.encodeRecords ((a::tail).map ReadPlan.encodeWord) := by
    simpa [environment,ScoreBuilderRawInput.environment,ScoreBuilderProgram.environment] using hh 30 (by decide)
  have hbready : HeadReady b := by
    intro j hj
    have hs : j∈SequentialProgram.scratchPorts :=
      (show ({1,2,3,4,5,6,7,12,13,14,15,16,17,18} : Finset (Fin 48)) ⊆ SequentialProgram.scratchPorts by decide) hj
    have hj0 : j≠0 := by intro he; subst j; simp at hj
    exact (hbf j hj0).trans (hm.scratch j hs)
  have hbhead : SubexponentialSAT.CounterPrograms.value (b.stacks 20)=heads := by
    rw [hbf _ (by decide),hd20,SubexponentialSAT.CounterPrograms.value_eq_toNat,hn]
  have hbp : (b.stacks 19).length=fixed.length := by rw [hbf _ (by decide)]; exact hm.processed
  have hbw : (b.stacks 10).length=ReadPlan.wordWidth r Q := by
    rw [hbf _ (by decide)]; simpa only [ReadPlan.encodeWord_length] using hm.width
  have hba : b.stacks 8=(fixed.reverse.map ReadPlan.encodeWord).flatten++
      (List.replicate (remaining+1) (ReadPlan.encodeWord a)).flatten := by
    rw [hbf _ (by decide),hm.assignment,List.flatten_append]
  obtain ⟨th,hth,c,hheadRun,hch,hcf⟩ := heads_eval b heads fixed (a::tail) _ hbready hbhead hbp hbw hba
    ((hbf _ (by decide)).trans hd30)
  let ps := scorePairs ivar factor (a::tail) pairs indices a heads remaining fixed
  have hcin : inputPairScores c ps := by
    refine ⟨?_,?_,?_⟩
    · rw [hcf _ (by decide),hbi]
      simp [ps,scorePairs,Zip.firstScores,List.map_map,Function.comp_def,UnaryCompare.encode]
    · rw [hch]
      simp [ps,scorePairs,Zip.secondScores,List.map_map,Function.comp_def,UnaryCompare.encode]
    · intro j hj
      have hj0 : j≠0 := by intro he; subst j; simp at hj
      have hj12 : j≠12 := by intro he; subst j; simp at hj
      rw [hcf j hj12,hbf j hj0]
      exact hm.scratch j ((show ({1,2,3,4,5,6,7,13,14,15,16,17} : Finset (Fin 48)) ⊆ SequentialProgram.scratchPorts by decide) hj)
  obtain ⟨wi,wh,hwi,hwh,hwli,hwlh,tw,htw,e,he,heo,he12,hef⟩ := weightAndMerge_eval c ps hcin
  have hwi' : SubexponentialSAT.BinaryArithmetic.toNat wi=heads^2*s^2 := by
    simpa [hcf,hbf,hd20,hd21,hn,hs] using hwi
  have hwh' : SubexponentialSAT.BinaryArithmetic.toNat wh=8*M^2*r^2 := by
    simpa [hcf,hbf,hd22,hd23,hmass,hr] using hwh
  have hwli' : wi.length ≤ 2*nb.length+2*sb.length+3 := by
    simpa [hcf,hbf,hd20,hd21] using hwli
  have hwlh' : wh.length ≤ 2*mb.length+2*rb.length+6 := by
    simpa [hcf,hbf,hd22,hd23] using hwlh
  have hlen : dataLength c=dataLength d := by
    simp [dataLength,PackingWeightProgram.inputLength,projectState,weightPorts,hcf,hbf]
  have hhb : headsBudget b heads fixed (a::tail)=headsBudget d heads fixed (a::tail) := by
    simp [headsBudget,PackingWeightProgram.Gate.budget,projectState,gatePorts,hbf]
  rw [hlen] at htw
  rw [hhb] at hth
  have hscores : Streams.scores wi wh ps=(a::tail).map (fun candidate =>
      UnaryCompare.encode (candidateScore ivar factor (a::tail) pairs indices a heads s M remaining fixed candidate)) := by
    exact Zip.scores_reduced (a::tail)
      (fun candidate => PackingIncidenceProgram.incidenceNumerator ivar factor (a::tail) pairs indices a remaining (candidate::fixed))
      (overlap heads fixed) wi wh heads s M r hwi' hwh'
  refine ⟨wi,wh,hwi',hwh',hwli',hwlh',ti+(th+tw),?_,e,
    hiRun.seq (hheadRun.seq he),?_,?_⟩
  · have hsum := Nat.add_le_add hti (Nat.add_le_add hth htw)
    simpa [runBudget,ps,Nat.add_assoc] using hsum
  · exact heo.trans (congrArg ProgramEncoding.encodeRecords hscores)
  · intro j hj0
    by_cases hj12 : j=12
    · subst j
      exact he12.trans (hm.scratch 12 (by decide)).symm
    · exact (hef j hj0 hj12).trans ((hcf j hj12).trans (hbf j hj0))

end Run
end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyRefinement
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The complete fixed producer discharges the sequential controller ABI. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

section Refinement
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem refines (a : Word r Q) (tail : List (Word r Q))
    (pairs : List (I × I)) (indices : List (V ⊕ E)) (hi : ∀ x,x∈indices)
    (heads s M : ℕ) (raw : List PairScoreProgram.PlanPair)
    (nb sb mb rb : List Bool)
    (hn : SubexponentialSAT.BinaryArithmetic.toNat nb=heads) (hs : SubexponentialSAT.BinaryArithmetic.toNat sb=s)
    (hmass : SubexponentialSAT.BinaryArithmetic.toNat mb=M) (hr : SubexponentialSAT.BinaryArithmetic.toNat rb=r)
    (hraw : raw.Perm (pairs.map (PackingIncidenceProgram.incidencePair ivar factor indices))) :
    SequentialProgram.ScoreBuilderRefines ReadPlan.encodeWord a tail
      (evaluate ivar factor (a::tail) pairs indices a heads s M) command
      (uniformBudget indices.length pairs.length raw.length (a::tail).length
        (ReadPlan.wordWidth r Q) heads (magnitude heads s M r) (parameterBits nb sb mb rb))
      indices.length
      (environment (ScoreBuilderRawInput.environment 1 (a::tail) indices.length raw) nb sb mb rb) := by
  intro remaining fixed d hsize hm _ hh
  obtain ⟨wi,wh,hwi,hwh,hwli,hwlh,t,ht,e,he,ho,hf⟩ := run_from_memory ivar factor
    a tail fixed pairs indices hi remaining heads s M raw d nb sb mb rb hn hs hmass hr hraw hm hh hsize
  have hd20 : d.stacks 20=nb := by simpa [environment] using hh 20 (by decide)
  have hd21 : d.stacks 21=sb := by simpa [environment] using hh 21 (by decide)
  have hd22 : d.stacks 22=mb := by simpa [environment] using hh 22 (by decide)
  have hd23 : d.stacks 23=rb := by simpa [environment] using hh 23 (by decide)
  have hL : parameterLength d=parameterBits nb sb mb rb := by
    simp [parameterLength,parameterBits,hd20,hd21,hd22,hd23]
  have hB := runBudget_le ivar factor a tail fixed pairs indices raw heads remaining
    (magnitude heads s M r) d wi wh (by rw [hd20,SubexponentialSAT.CounterPrograms.value_eq_toNat,hn])
    (by rw [hm.processed]; omega) (by omega)
    (by simpa [environment,ScoreBuilderRawInput.environment,ScoreBuilderProgram.environment] using hh 30 (by decide))
    (by rw [hL]; unfold parameterBits; omega)
    (by rw [hL]; unfold parameterBits; omega)
    (by rw [SubexponentialSAT.CounterPrograms.value_eq_toNat,hwi]; exact Nat.le_add_right _ _)
    (by rw [SubexponentialSAT.CounterPrograms.value_eq_toNat,hwh]; exact Nat.le_add_left _ _)
  rw [hL] at hB
  refine ⟨t,ht.trans hB,e,he,?_,?_,?_⟩
  · simpa only [evaluate] using ho
  · intro j _ hj; exact hf j hj
  · intro j hj
    rw [hf j (by intro h; subst j; omega)]
    exact hh j hj

end Refinement
end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyScope
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native-scope specialization of the fixed weighted packing selector. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.SqrtLog.Packing

theorem run (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) (hmask : mask.length ≤ n)
    {r Q : ℕ} [NeZero r] (a : Word r Q) (tail : List (Word r Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) (s : ℕ) (hs : 0 < s)
    (nb sb mb rb : List Bool) (hn : SubexponentialSAT.BinaryArithmetic.toNat nb=n)
    (hsb : SubexponentialSAT.BinaryArithmetic.toNat sb=s)
    (hmb : SubexponentialSAT.BinaryArithmetic.toNat mb=(PackingIncidenceInput.Semantics.nativeEntries scopes mask).length)
    (hrb : SubexponentialSAT.BinaryArithmetic.toNat rb=r)
    (d : Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail
      (n+PackingIncidenceInput.Semantics.factorCount scopes mask) [] d.stacks)
    (hc : (d.stacks 11).length=n+PackingIncidenceInput.Semantics.factorCount scopes mask)
    (he : SequentialProgram.HighState (env scopes n mask a tail nb sb mb rb) d.stacks) :
    ∃ e : Data, RunsIn (SequentialProgram.program Assembly.command)
      (cost scopes n mask a tail s nb sb mb rb)
      (d.withPC (some (SequentialProgram.program Assembly.command).entry)) (e.withPC none) ∧
      SequentialProgram.Memory ReadPlan.encodeWord a tail 0
        (values scopes n mask hmask a tail s hs (NeZero.pos r)) e.stacks ∧
      e.stacks 11=[] ∧ SequentialProgram.HighState
        (env scopes n mask a tail nb sb mb rb) e.stacks := by
  let owner := PackingIncidenceInput.Semantics.owner scopes n mask hmask
  let factor := PackingIncidenceInput.Semantics.factor scopes n mask hmask
  let indices := PackingIncidenceInput.Semantics.seedIndices n (PackingIncidenceInput.Semantics.factorCount scopes mask)
  let M := (PackingIncidenceInput.Semantics.nativeEntries scopes mask).length
  let evaluator := Assembly.evaluate owner factor (a::tail) (pairs scopes mask) indices a n s M
  let bound := Assembly.scoreBound (a::tail) (pairs scopes mask) indices n s M
  let budget := uniformBudget indices.length (pairs scopes mask).length (raw scopes n mask).length
    (a::tail).length (ReadPlan.wordWidth r Q) n (magnitude n s M r) (parameterBits nb sb mb rb)
  have hil : indices.length=n+PackingIncidenceInput.Semantics.factorCount scopes mask := by
    simp [indices,PackingIncidenceInput.Semantics.seedIndices,headsFirst_length]
  have hb := Assembly.refines owner factor a tail (pairs scopes mask) indices
    (PackingIncidenceInput.Semantics.seedIndices_complete _ _) n s M (raw scopes n mask) nb sb mb rb hn hsb hmb hrb
    (generated_pairs scopes n mask hmask)
  have hbound : ∀ remaining fixed x, remaining+1+fixed.length ≤ indices.length → x∈a::tail →
      evaluator remaining (x::fixed) ≤ bound := by
    intro remaining fixed x hsize _
    exact Assembly.evaluate_bound owner factor (a::tail) (pairs scopes mask) indices a n s M
      remaining fixed x hsize
  obtain ⟨e,htrace,hmem,hcounter,hcontext⟩ := program_memory ReadPlan.encodeWord a tail
    evaluator Assembly.command budget bound indices.length
    (Assembly.environment (ScoreBuilderRawInput.environment 1 (a::tail) indices.length (raw scopes n mask))
      nb sb mb rb) (fun x => by simp) hbound hb d (by simpa only [hil] using hm)
    (by simpa only [hil] using hc) (by simpa [env,hil] using he)
  have horder : ∀ remaining fixed, remaining+1+fixed.length=indices.length → ∀ x y,
      evaluator remaining (x::fixed) ≤ evaluator remaining (y::fixed) ↔
      sequentialNumerator owner factor (a::tail) (terms scopes n mask Q) indices
        (weights n s M r (a::tail).length hs (NeZero.pos r) (by simp)) a remaining (x::fixed) ≤
      sequentialNumerator owner factor (a::tail) (terms scopes n mask Q) indices
        (weights n s M r (a::tail).length hs (NeZero.pos r) (by simp)) a remaining (y::fixed) := by
    intro remaining fixed hsize x y
    simpa [evaluator,Assembly.evaluate,terms,indices,PackingIncidenceInput.Semantics.seedIndices,
      List.length_finRange] using Assembly.candidateScore_order owner factor (a::tail) haN haC (by simp)
      (pairs scopes mask) (List.finRange n) (List.finRange (PackingIncidenceInput.Semantics.factorCount scopes mask))
      (List.nodup_finRange n) (List.mem_finRange)
      (weights n s M r (a::tail).length hs (NeZero.pos r) (by simp)) s M
      (by simp [weights,Weights.ofFractions]) (by rfl) a remaining fixed hsize x y
  have hvalues := assignNat_eq_of_order a tail evaluator
    (sequentialNumerator owner factor (a::tail) (terms scopes n mask Q) indices
      (weights n s M r (a::tail).length hs (NeZero.pos r) (by simp)) a)
    indices.length horder indices.length [] (by simp)
  rw [hvalues] at hmem
  refine ⟨e,?_,hmem,hcounter,?_⟩
  · simpa [cost,controllerCost,budget,bound,indices,M,PackingIncidenceInput.Semantics.seedIndices,List.length_finRange,
      ReadPlan.encodeWord_length] using htrace
  · simpa [env,hil] using hcontext

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem middle_bank (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) (i : Fin 64) :
    (middle a p w tail).stacks (Wide.ports i)=(bankOutput a p w tail).stacks i := by
  have hi := i.isLt
  have hport : 417 ≤ (Wide.ports i).val ∧ (Wide.ports i).val < 481 := by
    simp only [Wide.ports_val]
    omega
  simp only [middle]
  rw [dite_eq_left hport]
  apply congrArg (bankOutput a p w tail).stacks
  apply Fin.ext
  simp only [Wide.ports_val]
  omega

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end


