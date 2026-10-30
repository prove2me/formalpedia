-- Prove2me | Definitions.Def_OAIQ081S182
-- name    : OAIQ081S182
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:31:24.597506+00:00
-- url     : https://prove2.me/theorems/577f2cdb-46a8-4b5c-a204-28b5ded16f40
-- title:
--   Definitions bundle OAIQ081S182 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 1 definition, 1 inductive type or structure and 10 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.NativeInput`, `OAI.Algorithms.SubexponentialSAT.SubexpKernelControl.scanCost`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLog_LeafProgramQueryPackingInput`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramQueryPackingInput.lean), [`SubexponentialSAT_SqrtLog_LeafProgramQueryRingModel`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramQueryRingModel.lean), [`SubexponentialSAT_SqrtLog_LeafProgramSourceNative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramSourceNative.lean), [`SubexponentialSAT_SqrtLog_LeafQueryFrontendOutput`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendOutput.lean), [`SubexponentialSAT_SqrtLog_LeafRingSetupProgramCoreDegree`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafRingSetupProgramCoreDegree.lean), [`SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafRingSetupProgramNative.lean), [`SubexponentialSAT_SqrtLog_LeafRingSetupProgramReplay`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafRingSetupProgramReplay.lean), [`SubexponentialSAT_SubexpKernelControl`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SubexpKernelControl.lean).
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S173`, `OAIQ081S174`, `OAIQ081S175` and `OAIQ081S176` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S186`, `OAIQ081S187` and `OAIQ081S188`; the statement `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input.native`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input.native`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S173
import Definitions.Def_OAIQ081S174
import Definitions.Def_OAIQ081S175
import Definitions.Def_OAIQ081S176

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
open LeafParametersProgram

/-- The packing dimensions exported from the completed native parameter bank. -/
theorem exported_parameter_values (x : Input) (l : Fin 8 → ℕ) (a : Data)
    (h : Exported (Execute.guardedModel x l) a) :
    BinaryArithmetic.toNat (a.stacks 720)=(produce x).Q ∧
    BinaryArithmetic.toNat (a.stacks 721)=(produce x).r ∧
    BinaryArithmetic.toNat (a.stacks 722)=(produce x).epsilonDen ∧
    BinaryArithmetic.toNat (a.stacks 727)=(produce x).R := by
  have h18 : (Execute.guardedModel x l).val 18=(produce x).r := Execute.guardedModel_radius x l
  have h21 : (Execute.guardedModel x l).val 21=(produce x).Q :=
    (Execute.guardedModel_public x l 4).trans (Layout.model_core_values x l).2.2.2.2.1
  have h25 : (Execute.guardedModel x l).val 25=(produce x).epsilonDen :=
    (Execute.guardedModel_public x l 5).trans (Layout.model_core_values x l).2.2.2.2.2.1
  have h29 : (Execute.guardedModel x l).val 29=(produce x).R :=
    (Execute.guardedModel_public x l 6).trans (Layout.model_core_values x l).2.2.2.2.2.2.1
  exact ⟨by simpa [Exports.destination,Exports.binarySources,h21] using h.2 0,
    by simpa [Exports.destination,Exports.binarySources,h18] using h.2 1,
    by simpa [Exports.destination,Exports.binarySources,h25] using h.2 2,
    by simpa [Exports.destination,Exports.binarySources,h29] using h.2 7⟩

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryPackingInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The packing problem is determined by the physically measured query.
In particular its incidence count is the same native mask scan exported by
the frontend, including neutral factors for uncovered low variables. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram

theorem packing_sources (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (hg : Guard (q.input k)) (l : Fin 8 → ℕ)
    (hex : LeafQueryFrontend.Exported (Execute.guardedModel (q.input k) l) a)
    (hscopes : a.stacks 718=LeafStatisticsProgram.scopeBits q.scopeRows)
    (hmask : a.stacks 719=q.forward) (hambient : a.stacks 709=q.ambient) :
    PackingCallerProgram.Sources a (packingProblem q k hg) := by
  have hi := LeafQueryFrontend.exported_input_values (q.input k) l a hex
  have hp := LeafQueryFrontend.exported_parameter_values (q.input k) l a hex
  constructor
  · exact hscopes
  · exact hi.1
  · exact hmask
  · exact congrArg BinaryArithmetic.toNat hambient
  · exact hp.1
  · exact hp.2.1
  · exact hp.2.2.1
  · rw [packingProblem_incidences]
    exact hi.2.2.1

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryRingModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open LeafParametersProgram

theorem ring_precision_pos (x : Input) (l : Fin 8 → ℕ) (hg : Guard x) :
    0 < (Execute.guardedModel x l).val 33 := by
  rw [Execute.guardedModel_precision x l (Nat.ne_of_gt hg.2.2.1)]
  exact produce_t_pos x

theorem ring_degree_pos (x : Input) (l : Fin 8 → ℕ) (hg : Guard x) :
    0 < (Execute.guardedModel x l).val 34 := by
  have hq : (produce x).Q≠0 := by have := hg.2.2.2.2.2.2.1; omega
  rw [Execute.guardedModel_degree x l hq]
  exact produce_d_pos x

theorem ring_exponent (x : Input) (l : Fin 8 → ℕ) (hg : Guard x) :
    (Circuit.result Serialization.code (Execute.guardedModel x l)).val 44=
      3^((Execute.guardedModel x l).val 34)-2 := by
  have hq : (produce x).Q≠0 := by have := hg.2.2.2.2.2.2.1; omega
  have hf : (Execute.guardedModel x l).val 35=fieldCard x :=
    (Execute.guardedModel_public x l 10).trans (Layout.model_fieldCard x l hq)
  rw [(Serialization.values _).1,hf,Execute.guardedModel_degree x l hq]
  rfl

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpKernelControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

def scanCost {α : Type*} (encode : α → Word) (cost : α → ℕ) (xs : List α) : ℕ :=
  (xs.map (fun x => 9 * (encode x).length + cost x + 9)).sum

/-! ## Forward-output service boundary -/

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed source generation in the incidence worker. The result arrays are
witnesses of the actual run; no equality of separately generated byte arrays
is inferred from equality of their polynomial meanings. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Source
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexponentialSAT.Subexp
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram

/-- These are physical byte, arithmetic-cache, and scratch conditions on the
state reached by the paid source-control copies. They contain no execution
or computed-source-polynomial premise. -/
structure NativeInput {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (a : Source.Data) (v N f S : ℕ) (width : List Bool) (frame : Fin 6 → List Bool) : Prop where
  tmp : a.stacks 684 = []
  low : ∀ i ∈ SourceStaging.lowClearPorts,a.stacks i = []
  extra : ∀ i ∈ SourceControls.extraPorts,a.stacks i = []
  backups : ∀ i ∈ SourceStaging.backupPorts,a.stacks i = []
  init : LayoutSourceRowsProgramInitialize.Ready (nativeStore a ∘ initializationPorts)
    (p.R+1) (d*baseWidth 3 p.t)
  literal : nativeStore a 233 = LayoutSourcePlanLookup.unary v
  ambient : nativeStore a 212 = LayoutSourcePlanLookup.unary N
  factor : nativeStore a 216 = LayoutSourcePlanLookup.unary f
  plans : nativeStore a 337 = LayoutOwnerFiberProgram.stream ps
  lookup : LayoutSourcePlanLookup.Native.Clean
    (⟨fun _ => false,initializeFinish (nativeStore a) (p.R+1) (d*baseWidth 3 p.t)⟩ : LayoutSourceRowsProgram.Data)
  rowsClean : RowsClean (preparedSourceStore (nativeStore a) (p.R+1) (d*baseWidth 3 p.t) ps v N f)
  workClean : RowWorkClean (preparedSourceStore (nativeStore a) (p.R+1) (d*baseWidth 3 p.t) ps v N f)
  owner : ∀ i : Fin 11,2 ≤ i.val →
    (preparedSourceStore (nativeStore a) (p.R+1) (d*baseWidth 3 p.t) ps v N f) (ownerStacks i) = []
  arithmetic : DensePolynomialProgram.PairSpec.BaseReady 3 p.t p.modulus p.cache
    (HornerProgram.modelTable p.t p.model p.modulus p.cache) (nativeStore a ∘ executorPorts) width frame
  empty : LayoutSourceRowsProgramReadiness.Empty (nativeStore a)
  source : SourceBank.Ready p (⟨fun _ => false,
    clearedSourceStore (preparedSourceStore (nativeStore a) (p.R+1) (d*baseWidth 3 p.t) ps v N f) ∘ sourcePorts⟩ : SourceBank.Data)
  sourceClean : ∀ j ∈ SourceBank.cleanupPorts,
    (preparedSourceStore (nativeStore a) (p.R+1) (d*baseWidth 3 p.t) ps v N f) (sourcePorts j) = []
  metadata : nativeStore a 306 = SelectorProgram.rawRecords (SourceBank.metadataRecords P)
  size : ∀ j : Fin 320,
    ((preparedSourceStore (nativeStore a) (p.R+1) (d*baseWidth 3 p.t) ps v N f) (sourcePorts j)).length ≤ S
  metadataSize : ∀ x,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType x) S
  incidenceBound : ps.length ≤ S
  nodesBound : Q ≤ S
  radiusBound : p.R ≤ S
  ringWidthBound : p.ringWidth.length ≤ S
  rowWidthBound : p.rowWidth.length ≤ S

end SubexponentialSAT.SqrtLog.LeafProgram.Source

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The fixed executable preparation pipeline.  Its input is the actual
numerical bank emitted by `LeafParametersProgram`; no field polynomial,
modulus, multiplication table, nodes, or idempotent coefficients are inputs.
The stage-by-stage execution theorem is separate from this code definition.
-/


/-! Arithmetic consumers use the same bytes generated by the preceding
stages.  These are structural handoff lemmas; the complete production
trace must establish `NativeBytes` before invoking them. -/



namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing StackRoutines

theorem coreCommand_eval (a : Data) (bits depth : List Bool) (t : ℕ)
    (ht : 0 < t) (hd : 0 < depth.length)
    (hv : CounterPrograms.value bits=t) (h : CoreInput bits depth a) :
    ∃ n ≤ coreBudget t depth.length bits.length, ∃ e : Data,
      ∃ (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
        (u : RingProgram.ScalarCode 3 t),
      Eval coreCommand n a e ∧
      CoreOutput t depth.length (IrreducibleSearch.data hd) M cache u e ∧
      (∀ i, i∉coreWritePorts → e.stacks i=a.stacks i) := by
  obtain ⟨ns,raw,M,cache,u,lg,hs,ho,hns⟩ := scalarCall_eval a bits t hv ht h.scalarInput
  let a1 := embedState (registers 8 (by decide)) scalar a raw
  have hp (j : Fin 41) : a1.stacks (scalar j)=raw.stacks j :=
    embedState_stack _ _ _ _ scalar_injective j
  have hf (i : Fin 640) (hi : ¬∃ j,scalar j=i) : a1.stacks i=a.stacks i :=
    embedState_stack_frame _ _ _ _ _ hi
  have hm : a1.stacks 194=M.bits := by
    simpa [scalar,IdempotentPreparationProgram.Scalar.low] using
      (hp 5).trans (ho.prepared.rest.1 5)
  have hw : (a1.stacks 202).length=baseWidth 3 t := by
    have hb := ho.unchanged 12 (by decide)
    simpa [scalar,IdempotentPreparationProgram.bootStacks,RingProgram.ternary_baseWidth]
      using congrArg List.length ((hp 12).trans hb)
  have hz : a1.stacks 203=cache.zero.val := (hp 17).trans ho.prepared.zero
  have h1 : a1.stacks 498=cache.one.val := (hp 18).trans ho.prepared.one
  have hm1 : a1.stacks 508=cache.minusOne.val := (hp 28).trans ho.prepared.minusOne
  have hu : a1.stacks 507=u.val := (hp 27).trans ho.prepared.half
  have hprec : a1.stacks 212=List.replicate t true := by
    have hh := (hp 29).trans (ho.unchanged 29 (by decide))
    simpa [scalar,IdempotentPreparationProgram.bootStacks] using hh
  have he253 : a1.stacks 253=[] := (hf 253 (by decide)).trans h.halfEmpty
  have he639 : a1.stacks 639=[] := (hf 639 (by decide)).trans h.copyEmpty
  let a2 : Data := ⟨readRegs a1.regs 30 31 none,Function.update a1.stacks 253 (a1.stacks 507)⟩
  have hcopy : Eval (overwrite 507 253) (7*baseWidth 3 t+8) a1 a2 := by
    simpa [a2,he253,hu,u.property] using overwrite_eval 507 253 a1
      (by decide) (by decide) (by decide) he639
  let a3 := RegisterResetProgram.zeroed a2
  have hreset : Eval RegisterResetProgram.all 32 a2 a3 := RegisterResetProgram.all_eval a2
  have hsearch : projectState (registers 22 (by decide)) search a3 =
      IrreducibleSearchBootstrap.input depth := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      have hdis : ¬∃ i,scalar i=search j := by
        fin_cases j <;> decide
      have hn : search j≠253 := by fin_cases j <;> decide
      simp only [a3,a2,Function.comp_apply,Function.update_of_ne hn]
      rw [hf _ hdis]
      by_cases hj : j=14
      · subst j
        simpa [IrreducibleSearchBootstrap.input,StructuredProgram.ioState,search] using h.degree
      · simpa [IrreducibleSearchBootstrap.input,StructuredProgram.ioState,hj]
          using h.searchClean j hj
  obtain ⟨np,hnp,a4,hpad,hcoeff,hraw,hdepth,hpf⟩ := searchAndPad_eval a3 depth hd t ht
    hsearch (by simpa [a3,a2,RegisterResetProgram.zeroed] using hw)
    (by simpa [a3,a2,RegisterResetProgram.zeroed] using he639)
  have hcarry (i : Fin 640) (hs' : ¬∃ j,search j=i) (hi : i≠253) :
      a4.stacks i=a1.stacks i := by
    rw [hpf i hs']
    simp [a3,a2,hi]
  have hhalf : a4.stacks 253=u.val := by
    rw [hpf 253 (by decide)]
    simp [a3,a2,hu]
  have hseed0 : a4.stacks 538=[] := by
    rw [hcarry 538 (by decide) (by decide),hf 538 (by decide)]
    exact h.tableClean 0 (by decide)
  have hseed1 : a4.stacks 498=cache.one.val :=
    (hcarry 498 (by decide) (by decide)).trans h1
  have hcopy0 : a4.stacks 639=[] :=
    (hcarry 639 (by decide) (by decide)).trans he639
  let a5 : Data := ⟨readRegs a4.regs 30 31 none,Function.update a4.stacks 538 (a4.stacks 498)⟩
  have hload : Eval (overwrite 498 538) (7*baseWidth 3 t+8) a4 a5 := by
    simpa [a5,hseed0,hseed1,cache.one.property] using overwrite_eval 498 538 a4
      (by decide) (by decide) (by decide) hcopy0
  have ti : TableInput t depth.length (IrreducibleSearch.data hd) M cache a5 := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [a5] using (hcarry 194 (by decide) (by decide)).trans hm
    · simpa [a5] using (congrArg List.length (hcarry 202 (by decide) (by decide))).trans hw
    · simp [a5,hdepth]
    · simp [a5,hseed1]
    · simpa [a5] using (hcarry 203 (by decide) (by decide)).trans hz
    · simpa [a5] using (hcarry 508 (by decide) (by decide)).trans hm1
    · change a5.stacks 441 = RingProgramTable.wordBits
        (List.Vector.ofFn (RingProgram.liftCoefficientsRun t
          (IrreducibleSearch.data hd).coefficients).1).val
      rw [RingCoefficientLiftProgram.modelCoefficientBits]
      exact hcoeff
    · intro j hj
      have hj538 : LeafRingSetupProgram.table j≠538 := by
        fin_cases j <;> first | exact (hj (by decide)).elim | decide
      have hj253 : LeafRingSetupProgram.table j≠253 := by fin_cases j <;> decide
      have hd1 : ¬∃ i,search i=LeafRingSetupProgram.table j := by
        fin_cases j <;> first | exact (hj (by decide)).elim | decide
      have hd2 : ¬∃ i,scalar i=LeafRingSetupProgram.table j := by
        fin_cases j <;> first | exact (hj (by decide)).elim | decide
      simp only [a5,Function.update_of_ne hj538]
      rw [hcarry _ hd1 hj253,hf _ hd2]
      exact h.tableClean j (fun hj' => hj (List.mem_cons_of_mem 0 hj'))
  obtain ⟨nt,hnt,e,htable,het,hem,hew,hez,hed,heminus,hef⟩ := tableCall_produces t hd
    (IrreducibleSearch.data hd) M cache ho.prepared.zeroCanonical ho.prepared.oneCanonical a5 ti
  refine ⟨ns+(7*baseWidth 3 t+8)+(32+(np+((7*baseWidth 3 t+8)+nt))),?_,e,M,cache,u,?_,?_,?_⟩
  · unfold coreBudget
    omega
  · simpa only [coreCommand,Nat.add_assoc] using hs.seq (hcopy.seq (hreset.seq (hpad.seq (hload.seq htable))))
  · refine ⟨hem.trans ti.modulus,?_,?_,hez,?_,?_,?_,?_,ho.prepared.inverse,
      ho.prepared.zeroCanonical,ho.prepared.oneCanonical,het⟩
    · exact (congrArg List.length hew).trans ti.width
    · exact (congrArg List.length hed).trans ti.degree
    · rw [hef 498 (by decide)]
      simpa [a5] using hseed1
    · exact heminus
    · rw [hef 253 (by decide)]
      simpa [a5] using hhalf
    · rw [hef 212 (by decide)]
      simpa [a5] using (hcarry 212 (by decide) (by decide)).trans hprec
  · intro i hi
    have hn253 : i≠253 := by
      intro he; subst i; exact hi (by simp [coreWritePorts])
    have hn538 : i≠538 := by
      intro he; subst i; exact hi (by simp [coreWritePorts])
    have hns : ¬∃ j,scalar j=i := by
      rintro ⟨j,rfl⟩; exact hi (by simp [coreWritePorts])
    have hnp : ¬∃ j,search j=i := by
      rintro ⟨j,rfl⟩; exact hi (by simp [coreWritePorts])
    have hnt : ¬∃ j,LeafRingSetupProgram.table j=i := by
      rintro ⟨j,rfl⟩; exact hi (by simp [coreWritePorts])
    rw [hef i hnt]
    change Function.update a4.stacks 538 (a4.stacks 498) i=a.stacks i
    rw [Function.update_of_ne hn538,hcarry i hnp hn253,hf i hns]

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls
open LeafParametersProgram

/-- The serializing arithmetic runs on the actual parameter-bank tapes;
it computes qE-2 and 2t rather than receiving those unary counters. -/
theorem serializationCall_eval (a : Data) (m : Circuit.Model)
    (w : Bank.Words) (r : Bank.Regs) (hs : Circuit.Shape m w)
    (ha : projectState (registers 8 (by decide)) parameters a=Bank.state r w) :
    ∃ n ≤ Circuit.budget Serialization.code m+1, ∃ rf w',
      Eval serializationCall n a
        (embedState (registers 8 (by decide)) parameters a (Bank.state rf w')) ∧
      Circuit.Shape (Circuit.result Serialization.code m) w' := by
  obtain ⟨n,rf,w',he,hshape,hn⟩ := Serialization.command_eval m w r hs
  exact ⟨n+1,Nat.add_le_add_right hn 1,rf,w',
    eval_liftCommand_from_state Serialization.command 33 44
      (registers 8 (by decide)) parameters a (registers_injective 8 (by decide))
      parameters_injective (ha.symm ▸ he),hshape⟩

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls StackRoutines LeafParametersProgram

/-- Actual generated counters and a one-word scalar-service input.  The
bounds concern finite bank values and tape lengths; no arithmetic context
is assumed. -/
theorem numberPhase_eval (a : Data) (m : Circuit.Model)
    (w : Bank.Words) (r : Bank.Regs) (hs : Circuit.Shape m w)
    (ha : projectState (registers 8 (by decide)) parameters a=Bank.state r w)
    (initialWidth V W : ℕ)
    (hinit : ∀ i∈workPorts++outputPorts, (a.stacks i).length ≤ initialWidth)
    (hv : ∀ i, (Circuit.result Serialization.code m).val i ≤ V)
    (hw : ∀ i, (Circuit.result Serialization.code m).len i ≤ W) :
    ∃ n ≤ numberBudget m initialWidth V W, ∃ e : Data, ∃ w' : Bank.Words,
      Eval numberPhase n a e ∧ Circuit.Shape (Circuit.result Serialization.code m) w' ∧
      CoreInput (w' 33) (List.replicate (BinaryArithmetic.toNat (w' 34)) true) e ∧
      e.stacks 191=List.replicate (BinaryArithmetic.toNat (w' 0)) true ∧
      e.stacks 209=List.replicate (BinaryArithmetic.toNat (w' 44)) true ∧
      e.stacks 243=List.replicate (BinaryArithmetic.toNat (w' 42)) true ∧
      e.stacks 296=List.replicate (BinaryArithmetic.toNat (w' 21)) true ∧
      (∀ i, e.stacks (parameters (Bank.port i))=w' i) ∧
      (∀ i, 320 ≤ i.val → i.val < 340 → e.stacks i=a.stacks i) := by
  let a0 := clearedPorts (workPorts++outputPorts) a
  have hclear := clearPorts_eval (workPorts++outputPorts) a
  have hproj : projectState (registers 8 (by decide)) parameters a0=Bank.state r w :=
    (initial_clear_parameter_projection a).trans ha
  obtain ⟨ns,hns,rf,w',hser,hshape⟩ := serializationCall_eval a0 m w r hs hproj
  let a1 := embedState (registers 8 (by decide)) parameters a0 (Bank.state rf w')
  have hp (i : Fin 64) : a1.stacks (parameters (Bank.port i))=w' i :=
    (embedState_stack _ _ _ _ parameters_injective (Bank.port i)).trans (Bank.state_port rf w' i)
  have hz (i : Fin 640) (hi : i∈workPorts++outputPorts)
      (hnot : ¬∃ j,parameters j=i) : a1.stacks i=[] := by
    rw [show a1.stacks i=a0.stacks i from embedState_stack_frame _ _ _ _ _ hnot]
    exact (clearedPorts_stacks _ _ _).trans (ite_eq_left hi)
  have hzOutput (i : Fin 640) (hi : i ∈ outputPorts) : a1.stacks i=[] := by
    apply hz i (List.mem_append.mpr (Or.inr hi))
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    simp only [parameters] at hv
    have hilow : i.val < 340 := by
      simp [outputPorts] at hi
      omega
    omega
  have hzWork (i : Fin 640) (hi : 417 ≤ i.val) : a1.stacks i=[] := by
    apply hz i (List.mem_append.mpr (Or.inl ((mem_workPorts i).mpr hi)))
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    simp only [parameters] at hv
    omega
  have hzAvailable (i : Fin 640) (hi : i ∈ outputPorts ∨ 417 ≤ i.val) :
      a1.stacks i=[] := by
    rcases hi with hi | hi
    · exact hzOutput i hi
    · exact hzWork i hi
  have hempty : ∀ p∈numericPlan, a1.stacks p.2=[] := by
    intro p hmem
    simp only [numericPlan,List.mem_cons,List.not_mem_nil,or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl <;>
      exact hzOutput _ (by simp [outputPorts])
  obtain ⟨nu,hnu,a2,hunary,h2⟩ := numericPlan_eval a1 hempty
    (hzWork _ (by norm_num)) (hzWork _ (by norm_num))
    (hzWork _ (by norm_num))
  have hsource (i : Fin 64) : a2.stacks (parameters (Bank.port i))=w' i := by
    rw [h2]
    have hd1 : parameters (Bank.port i)≠204 := by
      intro he
      have hh := congrArg Fin.val he
      dsimp [parameters,Bank.port] at hh
      omega
    have hd2 : parameters (Bank.port i)≠209 := by
      intro he
      have hh := congrArg Fin.val he
      dsimp [parameters,Bank.port] at hh
      omega
    have hd3 : parameters (Bank.port i)≠243 := by
      intro he
      have hh := congrArg Fin.val he
      dsimp [parameters,Bank.port] at hh
      omega
    have hd4 : parameters (Bank.port i)≠191 := by
      intro he
      have hh := congrArg Fin.val he
      dsimp [parameters,Bank.port] at hh
      omega
    have hd5 : parameters (Bank.port i)≠296 := by
      intro he
      have hh := congrArg Fin.val he
      dsimp [parameters,Bank.port] at hh
      omega
    simpa only [numericPlan,counterStacks,counterStack,Function.update_of_ne hd1,
      Function.update_of_ne hd2,Function.update_of_ne hd3,Function.update_of_ne hd4,
      Function.update_of_ne hd5] using hp i
  have h511 : a2.stacks 511=[] := by
    rw [h2]
    simpa [numericPlan,counterStacks,counterStack] using hzWork 511 (by norm_num)
  have h639 : a2.stacks 639=[] := by
    rw [h2]
    simpa [numericPlan,counterStacks,counterStack] using hzWork 639 (by norm_num)
  have h373 : a2.stacks 373=w' 33 := hsource 33
  let a3 : Data := ⟨readRegs a2.regs 30 31 none,Function.update a2.stacks 511 (a2.stacks 373)⟩
  have hcopy : Eval (overwrite 373 511) (7*(w' 33).length+8) a2 a3 := by
    simpa [a3,h511,h373] using overwrite_eval 373 511 a2 (by decide) (by decide) (by decide) h639
  let e := RegisterResetProgram.zeroed a3
  have hreset : Eval RegisterResetProgram.all 32 a3 e := RegisterResetProgram.all_eval a3
  have hc : CoreInput (w' 33) (List.replicate (BinaryArithmetic.toNat (w' 34)) true) e := by
    constructor
    · apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext j
        change (Function.update a2.stacks 511 (a2.stacks 373)) (scalar j)=_
        rw [h373,h2]
        fin_cases j <;>
          norm_num [scalar,numericPlan,counterStacks,counterStack,
            IdempotentPreparationProgram.inputData,StructuredProgram.ioState]
        all_goals first
          | rfl
          | exact hzAvailable _ (by norm_num [outputPorts] <;> decide)
    · simp [e,a3,h2,numericPlan,counterStacks,counterStack,
        show a1.stacks 374=w' 34 from hp 34]
    · intro j hj
      change (Function.update a2.stacks 511 (a2.stacks 373)) (search j)=[]
      rw [h2]
      fin_cases j <;> first | exact (hj rfl).elim |
        norm_num [search,numericPlan,counterStacks,counterStack]
      all_goals exact hzAvailable _ (by norm_num [outputPorts] <;> decide)
    · intro j hj
      change (Function.update a2.stacks 511 (a2.stacks 373)) (LeafRingSetupProgram.table j)=[]
      rw [h2]
      fin_cases j <;> first | exact (hj (by decide)).elim |
        norm_num [LeafRingSetupProgram.table,numericPlan,counterStacks,counterStack]
      all_goals exact hzAvailable _ (by norm_num [outputPorts] <;> decide)
    · change Function.update a2.stacks 511 (a2.stacks 373) 253=[]
      rw [h2]
      simpa [numericPlan,counterStacks,counterStack] using
        hzOutput 253 (by simp [outputPorts])
    · simpa [e,a3,RegisterResetProgram.zeroed] using h639
  have hnu' : nu ≤ 5*(7*W+6+32*(V+1)*(W+1)) := by
    apply hnu.trans
    apply numericPlan_cost_le
    · intro p hmem
      simp only [numericPlan,List.mem_cons,List.not_mem_nil,or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact (congrArg BinaryArithmetic.toNat (hp 34)).le.trans ((hshape.1 34).le.trans (hv 34))
        | exact (congrArg BinaryArithmetic.toNat (hp 44)).le.trans ((hshape.1 44).le.trans (hv 44))
        | exact (congrArg BinaryArithmetic.toNat (hp 42)).le.trans ((hshape.1 42).le.trans (hv 42))
        | exact (congrArg BinaryArithmetic.toNat (hp 0)).le.trans ((hshape.1 0).le.trans (hv 0))
        | exact (congrArg BinaryArithmetic.toNat (hp 21)).le.trans ((hshape.1 21).le.trans (hv 21))
    · intro p hmem
      simp only [numericPlan,List.mem_cons,List.not_mem_nil,or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact (congrArg List.length (hp 34)).le.trans ((hshape.2 34).trans (hw 34))
        | exact (congrArg List.length (hp 44)).le.trans ((hshape.2 44).trans (hw 44))
        | exact (congrArg List.length (hp 42)).le.trans ((hshape.2 42).trans (hw 42))
        | exact (congrArg List.length (hp 0)).le.trans ((hshape.2 0).trans (hw 0))
        | exact (congrArg List.length (hp 21)).le.trans ((hshape.2 21).trans (hw 21))
  refine ⟨clearPortsCost (workPorts++outputPorts) a+(ns+(nu+(7*(w' 33).length+8+32))),
    ?_,e,w',?_,hshape,hc,?_,?_,?_,?_,?_,?_⟩
  · have hb := clearPortsCost_bound (workPorts++outputPorts) a initialWidth hinit
    have hlen := (hshape.2 33).trans (hw 33)
    unfold numberBudget
    omega
  · exact hclear.seq (hser.seq (hunary.seq (hcopy.seq hreset)))
  · simp [e,a3,h2,numericPlan,counterStacks,counterStack,
      show a1.stacks 340=w' 0 from hp 0]
  · simp [e,a3,h2,numericPlan,counterStacks,counterStack,
      show a1.stacks 384=w' 44 from hp 44]
  · simp [e,a3,h2,numericPlan,counterStacks,counterStack,
      show a1.stacks 382=w' 42 from hp 42]
  · simp [e,a3,h2,numericPlan,counterStacks,counterStack,
      show a1.stacks 361=w' 21 from hp 21]
  · intro i
    have hi : parameters (Bank.port i)≠511 := by
      intro he
      have hh := congrArg Fin.val he
      dsimp [parameters,Bank.port] at hh
      omega
    simpa [e,a3,RegisterResetProgram.zeroed,hi] using hsource i
  · intro i hlo hhi
    have hn : i∉workPorts++outputPorts := by
      simp only [List.mem_append,not_or]
      constructor
      · rw [mem_workPorts]
        omega
      · simp only [outputPorts,List.mem_cons,List.not_mem_nil,or_false]
        intro hh
        rcases hh with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
    have hp' : ¬∃ j,parameters j=i := by
      rintro ⟨j,hj⟩
      have hh := congrArg Fin.val hj
      dsimp [parameters] at hh
      omega
    have hi511 : i≠511 := by intro hh; subst i; omega
    have hi204 : i≠204 := by intro hh; subst i; omega
    have hi209 : i≠209 := by intro hh; subst i; omega
    have hi243 : i≠243 := by intro hh; subst i; omega
    have hi191 : i≠191 := by intro hh; subst i; omega
    have hi296 : i≠296 := by intro hh; subst i; omega
    simp only [e,a3,Function.update_of_ne hi511,h2,
      numericPlan,counterStacks,counterStack,Function.update_of_ne hi204,
      Function.update_of_ne hi209,Function.update_of_ne hi243,
      Function.update_of_ne hi191,Function.update_of_ne hi296]
    rw [show a1.stacks i=a0.stacks i from embedState_stack_frame _ _ _ _ _ hp']
    simp [a0,clearedPorts_stacks,hn]

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramCoreDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Exact unary degree bytes retained from the actual core trace. The
existing native code and all arithmetic services are unchanged. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing StackRoutines

theorem coreCommand_eval_degree (a : Data) (bits depth : List Bool) (t : ℕ)
    (ht : 0 < t) (hd : 0 < depth.length)
    (hv : CounterPrograms.value bits=t) (h : CoreInput bits depth a) :
    ∃ n ≤ coreBudget t depth.length bits.length, ∃ e : Data,
      ∃ (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
        (u : RingProgram.ScalarCode 3 t),
      Eval coreCommand n a e ∧
      CoreOutput t depth.length (IrreducibleSearch.data hd) M cache u e ∧
      (∀ i, i∉coreWritePorts → e.stacks i=a.stacks i) ∧
      e.stacks 204=depth := by
  obtain ⟨ns,raw,M,cache,u,lg,hs,ho,hns⟩ := scalarCall_eval a bits t hv ht h.scalarInput
  let a1 := embedState (registers 8 (by decide)) scalar a raw
  have hp (j : Fin 41) : a1.stacks (scalar j)=raw.stacks j :=
    embedState_stack _ _ _ _ scalar_injective j
  have hf (i : Fin 640) (hi : ¬∃ j,scalar j=i) : a1.stacks i=a.stacks i :=
    embedState_stack_frame _ _ _ _ _ hi
  have hm : a1.stacks 194=M.bits := by
    simpa [scalar,IdempotentPreparationProgram.Scalar.low] using
      (hp 5).trans (ho.prepared.rest.1 5)
  have hw : (a1.stacks 202).length=baseWidth 3 t := by
    have hb := ho.unchanged 12 (by decide)
    simpa [scalar,IdempotentPreparationProgram.bootStacks,RingProgram.ternary_baseWidth]
      using congrArg List.length ((hp 12).trans hb)
  have hz : a1.stacks 203=cache.zero.val := (hp 17).trans ho.prepared.zero
  have h1 : a1.stacks 498=cache.one.val := (hp 18).trans ho.prepared.one
  have hm1 : a1.stacks 508=cache.minusOne.val := (hp 28).trans ho.prepared.minusOne
  have hu : a1.stacks 507=u.val := (hp 27).trans ho.prepared.half
  have hprec : a1.stacks 212=List.replicate t true := by
    have hh := (hp 29).trans (ho.unchanged 29 (by decide))
    simpa [scalar,IdempotentPreparationProgram.bootStacks] using hh
  have he253 : a1.stacks 253=[] := (hf 253 (by decide)).trans h.halfEmpty
  have he639 : a1.stacks 639=[] := (hf 639 (by decide)).trans h.copyEmpty
  let a2 : Data := ⟨readRegs a1.regs 30 31 none,Function.update a1.stacks 253 (a1.stacks 507)⟩
  have hcopy : Eval (overwrite 507 253) (7*baseWidth 3 t+8) a1 a2 := by
    simpa [a2,he253,hu,u.property] using overwrite_eval 507 253 a1
      (by decide) (by decide) (by decide) he639
  let a3 := RegisterResetProgram.zeroed a2
  have hreset : Eval RegisterResetProgram.all 32 a2 a3 := RegisterResetProgram.all_eval a2
  have hsearch : projectState (registers 22 (by decide)) search a3 =
      IrreducibleSearchBootstrap.input depth := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      have hdis : ¬∃ i,scalar i=search j := by
        fin_cases j <;> decide
      have hn : search j≠253 := by fin_cases j <;> decide
      simp only [a3,a2,Function.comp_apply,Function.update_of_ne hn]
      rw [hf _ hdis]
      by_cases hj : j=14
      · subst j
        simpa [IrreducibleSearchBootstrap.input,StructuredProgram.ioState,search] using h.degree
      · simpa [IrreducibleSearchBootstrap.input,StructuredProgram.ioState,hj]
          using h.searchClean j hj
  obtain ⟨np,hnp,a4,hpad,hcoeff,hraw,hdepth,hpf⟩ := searchAndPad_eval a3 depth hd t ht
    hsearch (by simpa [a3,a2,RegisterResetProgram.zeroed] using hw)
    (by simpa [a3,a2,RegisterResetProgram.zeroed] using he639)
  have hcarry (i : Fin 640) (hs' : ¬∃ j,search j=i) (hi : i≠253) :
      a4.stacks i=a1.stacks i := by
    rw [hpf i hs']
    simp [a3,a2,hi]
  have hhalf : a4.stacks 253=u.val := by
    rw [hpf 253 (by decide)]
    simp [a3,a2,hu]
  have hseed0 : a4.stacks 538=[] := by
    rw [hcarry 538 (by decide) (by decide),hf 538 (by decide)]
    exact h.tableClean 0 (by decide)
  have hseed1 : a4.stacks 498=cache.one.val :=
    (hcarry 498 (by decide) (by decide)).trans h1
  have hcopy0 : a4.stacks 639=[] :=
    (hcarry 639 (by decide) (by decide)).trans he639
  let a5 : Data := ⟨readRegs a4.regs 30 31 none,Function.update a4.stacks 538 (a4.stacks 498)⟩
  have hload : Eval (overwrite 498 538) (7*baseWidth 3 t+8) a4 a5 := by
    simpa [a5,hseed0,hseed1,cache.one.property] using overwrite_eval 498 538 a4
      (by decide) (by decide) (by decide) hcopy0
  have ti : TableInput t depth.length (IrreducibleSearch.data hd) M cache a5 := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [a5] using (hcarry 194 (by decide) (by decide)).trans hm
    · simpa [a5] using (congrArg List.length (hcarry 202 (by decide) (by decide))).trans hw
    · simp [a5,hdepth]
    · simp [a5,hseed1]
    · simpa [a5] using (hcarry 203 (by decide) (by decide)).trans hz
    · simpa [a5] using (hcarry 508 (by decide) (by decide)).trans hm1
    · change a5.stacks 441 = RingProgramTable.wordBits
        (List.Vector.ofFn (RingProgram.liftCoefficientsRun t
          (IrreducibleSearch.data hd).coefficients).1).val
      rw [RingCoefficientLiftProgram.modelCoefficientBits]
      exact hcoeff
    · intro j hj
      have hj538 : LeafRingSetupProgram.table j≠538 := by
        fin_cases j <;> first | exact (hj (by decide)).elim | decide
      have hj253 : LeafRingSetupProgram.table j≠253 := by fin_cases j <;> decide
      have hd1 : ¬∃ i,search i=LeafRingSetupProgram.table j := by
        fin_cases j <;> first | exact (hj (by decide)).elim | decide
      have hd2 : ¬∃ i,scalar i=LeafRingSetupProgram.table j := by
        fin_cases j <;> first | exact (hj (by decide)).elim | decide
      simp only [a5,Function.update_of_ne hj538]
      rw [hcarry _ hd1 hj253,hf _ hd2]
      exact h.tableClean j (fun hj' => hj (List.mem_cons_of_mem 0 hj'))
  obtain ⟨nt,hnt,e,htable,het,hem,hew,hez,hed,heminus,hef⟩ := tableCall_produces t hd
    (IrreducibleSearch.data hd) M cache ho.prepared.zeroCanonical ho.prepared.oneCanonical a5 ti
  refine ⟨ns+(7*baseWidth 3 t+8)+(32+(np+((7*baseWidth 3 t+8)+nt))),?_,e,M,cache,u,?_,?_,?_,?_⟩
  · unfold coreBudget
    omega
  · simpa only [coreCommand,Nat.add_assoc] using hs.seq (hcopy.seq (hreset.seq (hpad.seq (hload.seq htable))))
  · refine ⟨hem.trans ti.modulus,?_,?_,hez,?_,?_,?_,?_,ho.prepared.inverse,
      ho.prepared.zeroCanonical,ho.prepared.oneCanonical,het⟩
    · exact (congrArg List.length hew).trans ti.width
    · exact (congrArg List.length hed).trans ti.degree
    · rw [hef 498 (by decide)]
      simpa [a5] using hseed1
    · exact heminus
    · rw [hef 253 (by decide)]
      simpa [a5] using hhalf
    · rw [hef 212 (by decide)]
      simpa [a5] using (hcarry 212 (by decide) (by decide)).trans hprec
  · intro i hi
    have hn253 : i≠253 := by
      intro he; subst i; exact hi (by simp [coreWritePorts])
    have hn538 : i≠538 := by
      intro he; subst i; exact hi (by simp [coreWritePorts])
    have hns : ¬∃ j,scalar j=i := by
      rintro ⟨j,rfl⟩; exact hi (by simp [coreWritePorts])
    have hnp : ¬∃ j,search j=i := by
      rintro ⟨j,rfl⟩; exact hi (by simp [coreWritePorts])
    have hnt : ¬∃ j,LeafRingSetupProgram.table j=i := by
      rintro ⟨j,rfl⟩; exact hi (by simp [coreWritePorts])
    rw [hef i hnt]
    change Function.update a4.stacks 538 (a4.stacks 498) i=a.stacks i
    rw [Function.update_of_ne hn538,hcarry i hnp hn253,hf i hns]

  · exact hed.trans (by simpa [a5] using hdepth)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Syntactic no-read/no-write certificate for the existing native ring
producer.  Hidden collector tapes do not affect its exact execution time. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Replay
open BitProgram StructuredCalls ProgramTapeReplay

theorem idempotents : AvoidsCmd hidden idempotentPhase := by
  have hc : ∀i∈idempotentStartPorts,¬hidden i := by
    intro i hi hh
    have h := hidden_bounds hh
    exact (collector_not_touched i h.1 h.2).2.1 hi
  have h : AvoidsCmd hidden idempotentCall := by
    apply avoids_call_lift_of_range
    intro i
    apply visible
    right
    change 340 ≤ 480+i.val
    omega
  exact ⟨clearPorts _ hc,overwrite 373 511 (by decide) (by decide),resetAll,h,
    overwrite 512 281 (by decide) (by decide)⟩

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Replay

end OAI.Algorithms
end


