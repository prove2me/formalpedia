-- Prove2me | Definitions.Def_OAIQ081S171
-- name    : OAIQ081S171
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:15:56.821092+00:00
-- url     : https://prove2.me/theorems/8ed97fc9-640d-4f04-b42f-bbc0c33c1dab
-- title:
--   Definitions bundle OAIQ081S171 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 7 definitions and 20 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.globalSize`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.selection`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ambient`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.exported`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.coreCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.command`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_FactorTableProgram`, `SubexponentialSAT_SqrtLogSpace_QueryReconstruction`, `SubexponentialSAT_SqrtLogSpace_ReconstructionNative`, `SubexponentialSAT_SqrtLog_PackingCallerProgramCleanup`, `SubexponentialSAT_SqrtLog_PackingCallerProgramCost`, `SubexponentialSAT_SqrtLog_PackingCallerProgramExport`, `SubexponentialSAT_SqrtLog_PackingCallerProgramExportFacts`, `SubexponentialSAT_SqrtLog_PackingCallerProgramIncidence`, `SubexponentialSAT_SqrtLog_PackingCallerProgramQuantitative`, `SubexponentialSAT_SqrtLog_PackingCallerProgramSelect`, `SubexponentialSAT_SqrtLog_PackingCallerProgramStage`, `SubexponentialSAT_SqrtLog_PackingCallerProgramState`, `SubexponentialSAT_SqrtLog_PackingCallerProgramWide`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputLoose`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`, `SubexponentialSAT_SqrtLog_PackingPrefixProgram`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyProgram`, `SubexponentialSAT_SqrtLog_ProducedQueryResourcesOrigin`, `SubexponentialSAT_Subexp_AssignmentInputProgram`, `SubexponentialSAT_Subexp_ScoreBuilderProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S157`, `OAIQ081S158`, `OAIQ081S159`, `OAIQ081S160`, `OAIQ081S161`, `OAIQ081S162` and `OAIQ081S163` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S176`, `OAIQ081S177`, `OAIQ081S178` and `OAIQ081S179`; the statement `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.chosen_scalar_input_cap_of_scope_resources`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S157
import Definitions.Def_OAIQ081S158
import Definitions.Def_OAIQ081S159
import Definitions.Def_OAIQ081S160
import Definitions.Def_OAIQ081S161
import Definitions.Def_OAIQ081S162
import Definitions.Def_OAIQ081S163

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

noncomputable def exported (a : OuterData) : OuterData :=
  embedState id basePort a (LeafProgram.Incidence.exported (projectState id basePort a))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
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

def command : Cmd 40 768 :=
  .seq LeafProgram.Count.reconstruct
    (.seq canonicalWideRead LeafProgram.Count.clearCaches)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative
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

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog
open DensePolynomialProgram LeafProgram
open LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def coreCommand : Cmd 40 768 :=
  .seq Count.Prepare.command ReconstructionNative.command

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ScoreBuilderProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The actual global candidate-score builder

Pair read plans are prepared once for the current processed position. The
candidate loop then executes the local collision enumeration and emits scores
in candidate order. A final fixed routine restores the temporary table ports.
-/

namespace SubexponentialSAT.Subexp.ScoreBuilderProgram

open BitProgram StructuredCalls

theorem command_eval (pre : PairPreparationProgram.Context)
    (ctx : CandidateScoreProgram.Context) (hc : ctx.Valid) (d : Data) (hi : InputFor pre ctx d) :
    ∃ n ≤ sourceBudget pre ctx - 1, ∃ regs,
      Eval command n d (resultState d regs (scoreBytes ctx)) := by
  obtain ⟨a, ha, hpre⟩ := preparation_eval pre d hi.preparation
  obtain ⟨b, hb, regs, hcan⟩ := candidates_eval pre ctx hc d hi.candidates
  have h0 : d.stacks 0 = [] := by
    simpa [PairPreparationProgram.inputState, preparationPorts] using (hi.preparation 0).symm
  have h40 : d.stacks 40 = [] := by
    simpa [PairPreparationProgram.inputState, preparationPorts] using (hi.preparation 29).symm
  have h41 : d.stacks 41 = [] := by
    simpa [PairPreparationProgram.inputState, preparationPorts] using (hi.preparation 25).symm
  have h42 : d.stacks 42 = [] := by
    simpa [PairPreparationProgram.inputState, preparationPorts] using (hi.preparation 26).symm
  have hfinish := finish_eval (scored pre ctx d regs)
    (by simp [scored, prepared, h0]) (by simp [scored, prepared, h42])
  have hend : finished (scored pre ctx d regs) =
      resultState d (readRegs regs 0 1 none) (scoreBytes ctx) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      by_cases h0j : j = 0
      · subst j; simp [ scored, prepared]
      by_cases h40j : j = 40
      · subst j; simp [ scored, prepared, h40]
      by_cases h41j : j = 41
      · subst j; simp [ scored, prepared, h41]
      by_cases h42j : j = 42
      · subst j; simp [ scored, prepared, h42]
      · simp [ scored, prepared, h0j, h40j, h41j, h42j]
  rw [hend] at hfinish
  refine ⟨a + (b + (6 * (scoreBytes ctx).length + 2 * (preparedBytes pre).length + 9)),
    ?_, readRegs regs 0 1 none, ?_⟩
  · unfold sourceBudget
    omega
  · have he := hpre.seq (hcan.seq hfinish)
    simpa [command, scored, prepared] using he

end SubexponentialSAT.Subexp.ScoreBuilderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Convert a physically scanned factor-index stream to incidence plans. -/


/-! Native per-variable incident-factor scan from the original scope stream. -/


/-! Fixed cleanup for the native scope-address scanner. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

namespace Clear
theorem command_eval (js : List (Fin 32)) (d : Data) (B : ℕ)
    (hB : ∀ j ∈ js, (d.stacks j).length ≤ B) :
    ∃ t e, t ≤ js.length*(2*B+3)+1 ∧ Eval (command js) t d e ∧
      (∀ j, e.stacks j = if j ∈ js then [] else d.stacks j) ∧
      (∀ i : Fin 16, i ≠ 0 → i ≠ 1 → e.regs i = d.regs i) := by
  induction js generalizing d with
  | nil => exact ⟨0,d,by simp,Eval.base (.skip d),by simp,by simp⟩
  | cons j js ih =>
      have hb : ∀ k ∈ js, ((after j d).stacks k).length ≤ B := by
        intro k hk
        by_cases h : k=j
        · simp [after,h]
        · simpa [after,h] using hB k (by simp [hk])
      obtain ⟨t,e,ht,he,hs,hr⟩ := ih (after j d) hb
      refine ⟨2*(d.stacks j).length+3+t,e,?_,(one_eval j d).seq he,?_,?_⟩
      · have hh := hB j (by simp)
        simp only [List.length_cons]
        nlinarith
      · intro k
        rw [hs]
        by_cases hkj : k=j <;> by_cases hmem : k ∈ js <;>
          simp [after,hkj,hmem]
      · intro i hi0 hi1
        simpa [after,readRegs,hi0,hi1] using hr i hi0 hi1
end Clear
end SubexponentialSAT.SqrtLog.PackingIncidenceInput


/-! Calls to the fixed record mapper inside the native scope scan. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Lift
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem command_eval (c : Cmd 6 9) (r : Fin 16 → Bool) (scopes : List (List ℕ))
    (n v z : ℕ) (mask out source payload out' source' : List Bool)
    (t : ℕ) (rf : Fin 6 → Bool)
    (he : Eval c t (Rows.data (r ∘ registers) v n source out payload)
      (Rows.data rf v n source' out' [])) :
    ∃ rr, Eval (command c) (t+1)
      (work r scopes n v z mask out source payload)
      (work rr scopes n v z mask out' source' []) ∧
      (∀ i : Fin 16, 6 ≤ i.val → rr i = r i) := by
  let a := work r scopes n v z mask out source payload
  let small := Rows.data (r ∘ registers) v n source out payload
  let smallOut := Rows.data rf v n source' out' []
  have hin : embedState registers ports a small = a := by
    apply embedState_eq_of_ports _ _ _ _ _ registers_injective ports_injective
    · intros; rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [a,small,Rows.data,work,Scan.data,ports]
    · intros; rfl
  let e := embedState registers ports a smallOut
  have hh := eval_call_lifted (compiled c 8 7) registers ports a
    registers_injective ports_injective (compiled_halt_trace he 8 7)
  rw [hin] at hh
  have hout : e = work e.regs scopes n v z mask out' source' [] := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    change e.stacks i = (work e.regs scopes n v z mask out' source' []).stacks i
    by_cases hi : ∃ k, ports k = i
    · obtain ⟨k,rfl⟩ := hi
      rw [show e.stacks (ports k) = smallOut.stacks k from
        embedState_stack registers ports a smallOut ports_injective k]
      fin_cases k <;> simp [smallOut,Rows.data,work,Scan.data,ports]
    · rw [show e.stacks i = a.stacks i from
        embedState_stack_frame registers ports a smallOut i hi]
      have h7 : i ≠ 7 := fun h => hi ⟨8,h.symm⟩
      have h12 : i ≠ 12 := fun h => hi ⟨2,h.symm⟩
      have h25 : i ≠ 25 := fun h => hi ⟨7,h.symm⟩
      simp [a,work,Scan.data,h7,h12,h25]
  change Eval (command c) (t+1) a e at hh
  rw [hout] at hh
  refine ⟨e.regs,hh,?_⟩
  intro i hi
  apply embedState_register_frame
  rintro ⟨k,hk⟩
  have hv := congrArg Fin.val hk
  have hlt := k.isLt
  change k.val = i.val at hv
  omega

theorem clean_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (mask out source : List Bool) :
    ∃ t rf, t ≤ cleanBound scopes v source ∧
      Eval clean t (work r scopes n v z mask out source [])
        (Scan.data rf scopes n v z mask out) ∧
      (∀ i : Fin 16, 2 ≤ i.val → rf i = r i) := by
  let a := work r scopes n v z mask out source []
  let B := v+scopes.length+(Scan.indices scopes v).length+source.length+1
  have hB : ∀ j ∈ ([2,5,7,9] : List (Fin 32)), (a.stacks j).length ≤ B := by
    intro j hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl <;>
      simp [a,work,Scan.data,Encoding.encodeNat,B] <;> omega
  obtain ⟨t,e,ht,he,hs,hr⟩ := Clear.command_eval [2,5,7,9] a B hB
  have hout : e = Scan.data e.regs scopes n v z mask out := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    rw [hs]
    fin_cases i <;> simp [a,work,Scan.data]
  rw [hout] at he
  refine ⟨t,e.regs,?_,he,?_⟩
  · dsimp [cleanBound,B] at *; omega
  · intro i hi
    exact hr i (by intro h; subst i; omega) (by intro h; subst i; omega)
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Lift


/-! One native low-variable step, including its uncovered neutral factor. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Step
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem peek_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (mask out : List Bool) :
    let source := Encoding.encodeList Rows.unary (Scan.indices scopes v).reverse
    let bit := decide (Scan.indices scopes v ≠ [])
    let rr := readRegs r 10 11 (some bit)
    Eval peek 2 (Lift.work r scopes n v z mask out source [])
      (Lift.work rr scopes n v z mask out source []) := by
  dsimp only
  have h := (Eval.base (StructuredProgram.Eval.atom (.pop (7 : Fin 32) 10 11)
    (Lift.work r scopes n v z mask out
      (Encoding.encodeList Rows.unary (Scan.indices scopes v).reverse) []))).seq
    (Eval.base (StructuredProgram.Eval.atom (.push (7 : Fin 32) 10) _))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  cases hh : (Scan.indices scopes v).reverse with
  | nil =>
      have he : Scan.indices scopes v = [] := List.reverse_eq_nil_iff.mp hh
      apply congrArg₂ StructuredProgram.State.mk <;> funext i <;> fin_cases i <;>
        simp [Lift.work,Scan.data,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg,execInstr,
          Encoding.encodeList,he,readRegs]
  | cons j js =>
      have he : Scan.indices scopes v ≠ [] := by intro h; simp [h] at hh
      apply congrArg₂ StructuredProgram.State.mk <;> funext i <;> fin_cases i <;>
        simp [Lift.work,Scan.data,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg,execInstr,
          Encoding.encodeList,he,readRegs]

theorem neutral_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (mask out source : List Bool) :
    ∃ t rf, t ≤ 7*z+Rows.callbackBound v n z+8 ∧
      Eval neutral t (Lift.work r scopes n v z mask out source [])
        (Lift.work rf scopes n v (z+1) mask (Rows.recordPrefix v n z ++ out) source []) ∧
      (∀ i : Fin 16, 6 ≤ i.val → rf i = r i) := by
  let a := Lift.work r scopes n v z mask out source []
  let b := Scan.copied 24 12 a
  have hc := Scan.copy_eval 24 12 (by decide) (by decide) (by decide) a
    (by simp [a,Lift.work,Scan.data])
  have hb : b = Lift.work b.regs scopes n v z mask out source (Rows.unary z) := by
    apply congrArg (StructuredProgram.State.mk b.regs)
    funext i; fin_cases i <;> simp [b,Scan.copied,StackRoutines.copyStacks,a,Lift.work,Scan.data]
  obtain ⟨t,rr,ht,he,_⟩ := Rows.callback_eval (b.regs ∘ Lift.registers) v n z source out
  obtain ⟨rf,hf,hr⟩ := Lift.command_eval Rows.callback b.regs scopes n v z mask out source
    (Rows.unary z) (Rows.recordPrefix v n z ++ out) source t rr he
  rw [← hb] at hf
  let c := Lift.work rf scopes n v z mask (Rows.recordPrefix v n z ++ out) source []
  have hi := TupleProgram.pushConst_eval (24 : Fin 32) (0 : Fin 16) true c
  let d := TupleProgram.pushedState 24 0 true c
  have hd : d = Lift.work d.regs scopes n v (z+1) mask (Rows.recordPrefix v n z ++ out) source [] := by
    apply congrArg (StructuredProgram.State.mk d.regs)
    funext i; fin_cases i <;>
      simp [d,c,Lift.work,Scan.data,List.replicate_succ]
  change Eval _ _ c d at hi
  rw [hd] at hi
  refine ⟨_,d.regs,?_,hc.seq (hf.seq hi),?_⟩
  · simpa [a,Lift.work,Scan.data] using (show 7*z+5+(t+1+2) ≤
      7*z+Rows.callbackBound v n z+8 by omega)
  · intro i h6
    have h0 : i ≠ 0 := by intro h; subst i; omega
    have h1 : i ≠ 1 := by intro h; subst i; omega
    have hh := hr i h6
    simpa [d,c,TupleProgram.pushedState,b,Scan.copied,a,Lift.work,readRegs,h0,h1] using hh

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Step


/-! Runtime high-mask loop for the original-address incidence stream. -/


/-! Count the physical scope stream before constructing native incidence plans. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInputProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical input construction for sequential type assignment

All parameters are unary stack data. The fixed program constructs the one-hot
word alphabet, reads its actual first word, derives its packed view, and builds
the exact seed range and dimensions expected by `AssignmentInitProgram`.
-/

namespace SubexponentialSAT.Subexp.AssignmentInputProgram

open BitProgram StructuredCalls SubexpSetupStorage AssignmentInputCall

theorem seedRange_eval (a : Data) (n : ℕ) (hc : Clean a)
    (h47 : a.stacks 47 = unary n) :
    Writes seedRange a 46 (AssignmentSeedRange.seedRecords n) (AssignmentSeedRange.budget n + 1) := by
  let pre := project (register (r := 5) (by decide)) (stack (s := 6) (by decide))
    (prepareState 31 work [(47, 12)] a)
  have hp : pre = AssignmentSeedRange.inputState pre.regs n := by
    apply congrArg (StructuredProgram.State.mk pre.regs)
    funext i
    have h := prepare_one_local (r := 5) (s := 6) (by decide) (by decide) a hc 47 0 i
    change pre.stacks i = _
    change pre.stacks i = _ at h
    rw [h]
    fin_cases i <;> simp [ h47]
  obtain ⟨ticks, htime, ht⟩ := AssignmentSeedRange.program_runsIn pre.regs n
  rw [← hp] at ht
  obtain ⟨b, he, hs, hb⟩ := call_eval AssignmentSeedRange.program
    (by decide) (by decide) [(47, 12)] 5 46 a (AssignmentSeedRange.outputState n)
    (by decide) (by decide) (by simp [mem_work]) (by simp) hc ht
  refine ⟨_, b, he, hs, hb, ?_⟩
  intro B ha hresult _
  have ho : Within (AssignmentSeedRange.outputState n) B := by
    intro j; fin_cases j <;> simp [AssignmentSeedRange.outputState, AssignmentSeedRange.state, hresult]
  have h := callCost_le (r := 5) (s := 6) (by decide) (by decide)
    [(47, 12)] 5 46 a _ ticks B (by decide) ha ho
  exact h.trans (Nat.add_le_add_right htime _)

end SubexponentialSAT.Subexp.AssignmentInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramCleanup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open PackingLoaderProgram

theorem clearLow_cost (outside : Store) (d : Small) :
    clearManyCost lowClearPorts (framed outside d)=clearLowBudget d := by
  unfold lowClearPorts
  rw [clear_cost_eq _ (List.Nodup.map lowPorts.injective (List.nodup_finRange _))]
  simp [clearLowBudget,List.map_map,Function.comp_def]

theorem clearLow_run (outside : Store) (d : Small) :
    ∃ rf, Eval clearLow (clearLowBudget d)
      (framed outside d) (framed outside (⟨rf,fun _=>[]⟩ : Small)) := by
  simpa [clearLow_cost] using clearLow_eval outside d

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramWide
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The caller's private64-stack workspace lies after the live native
parameter bank340..416, which must survive until ring setup. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem call_eval (c : Cmd 16 768) (a : Data) (b : Local) (t : ℕ)
    (h : Eval c t (project a) b) :
    ∃ e, Eval (call c) (t+1) a e ∧ e.stacks=b.stacks ∧
      (∀ i : Fin 40,16 ≤ i.val → e.regs i=a.regs i) := by
  have hc := eval_call_from_state (compiled c 684 133) registers id a
    registers.injective Function.injective_id (compiled_halt_trace h 684 133)
  refine ⟨_,hc,?_,?_⟩
  · funext i
    exact embedState_stack registers id a b Function.injective_id i
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change j.val=i.val at hv
    have := j.isLt
    omega

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramExport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid export of the computed word table, metadata, and original plans,
followed by erasure of the private bank and parking of the source masters. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem finish_eval (a : Data) (ht : a.stacks 684=[]) :
    ∃ b, Eval finish (finishCost (project a)+1) a b ∧
      b.stacks=(finished (project a)).stacks ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) :=
  call_eval finishLocal a _ _ (finishLocal_eval (project a) ht)

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramExportFacts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem finish_congr (a b : Local) (h : a.stacks=b.stacks) :
    (finished a).stacks=(finished b).stacks ∧ finishCost a=finishCost b := by
  obtain ⟨hc,hct⟩ := copyMany_congr exportPairs a b h
  obtain ⟨he,het⟩ := clearMany_congr privatePorts _ _ hc
  change (exported a).stacks=(exported b).stacks at he
  obtain ⟨hp,hpt⟩ := copyMany_congr LeafProgram.LayoutMasters.parkPairs _ _ he
  obtain ⟨hf,hft⟩ := clearMany_congr LeafProgram.LayoutMasters.lowPorts _ _ hp
  exact ⟨hf,by simp only [finishCost,exportCost,LeafProgram.LayoutMasters.parkCost,hct,het,hpt,hft]⟩

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramIncidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserve the physically generated owner/factor plans before the incidence
pair installer consumes them. The extra master is local port61. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open PackingLoaderProgram PackingIncidenceInput

theorem produced_setRegs (regs rs : Fin 16 → Bool) (scopes : List (List ℕ))
    (n : ℕ) (mask : List Bool) :
    setRegs (Install.produced regs scopes n mask) rs=Install.produced rs scopes n mask := by
  apply SubexponentialSAT.CounterForPrograms.data_ext
  · exact (produced_regs rs scopes n mask).symm
  · change (Install.produced regs scopes n mask).stacks=(Install.produced rs scopes n mask).stacks
    rw [Endpoint.produced_stacks,Endpoint.produced_stacks]

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingPrefixProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid prefix preparation. Raw unary inputs may contain arbitrary bits;
only their lengths matter. The persistent table and both counters survive. -/

namespace SubexponentialSAT.SqrtLog.PackingPrefixProgram

open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.Subexp

theorem multiply_eval (a : Data) (W h : ℕ)
    (hW : a.stacks 8 = unary W) (hh : a.stacks 5 = unary h) (htmp : a.stacks 7 = []) :
    ∃ n ≤ h * (7 * W + 7) + 3, ∃ regs : Fin 3 → Bool,
      Eval multiply n a ⟨regs,
        Function.update (Function.update a.stacks 5 []) 6 (unary (h * W) ++ a.stacks 6)⟩ := by
  let d := projectState id mulStack a
  obtain ⟨n, e, he, hn, hs⟩ := BasisTransposePlanProgram.multiply_eval W h d hW hh htmp
  have hl := eval_liftCommand_from_state BasisTransposePlanProgram.multiply 0 4 id mulStack a
    Function.injective_id mulStack_injective he
  let result : Data := ⟨e.regs,
    Function.update (Function.update a.stacks 5 []) 6 (unary (h * W) ++ a.stacks 6)⟩
  have hb : embedState id mulStack a e = result := by
    apply embedState_eq_of_ports id mulStack a _ _ Function.injective_id mulStack_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i
      rw [hs]
      fin_cases i <;> simp [result, d, projectState, mulStack, Function.comp_def, unary, BasisTransposePlanProgram.unary]
    · intro i hi
      have h5 : i ≠ 5 := fun h => hi ⟨5, by simpa [mulStack] using h.symm⟩
      have h6 : i ≠ 6 := fun h => hi ⟨4, by simpa [mulStack] using h.symm⟩
      simp [result, h5, h6]
  rw [hb] at hl
  exact ⟨n + 1, by omega, e.regs, hl⟩

end SubexponentialSAT.SqrtLog.PackingPrefixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputLoose
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The incidence scorer does not touch controller storage on ports 12--18. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput
open SubexponentialSAT.BitProgram SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp
open SubexponentialSAT.SqrtLog.PackingIncidenceProgram

theorem command_eval_loose {r Q : ℕ} (a : Word r Q) (tail fixed : List (Word r Q))
    (n M : ℕ) (raw : List PlanPair) (d : ScoreBuilderProgram.Data)
    (hm : LooseMemory a fixed n d)
    (hh : SequentialProgram.HighState (ScoreBuilderRawInput.environment 1 (a::tail) M raw)
      d.stacks) (hsize : n+1+fixed.length = M)
    (hp : ∀ pair ∈ raw, ValidRawPair M pair) :
    ∃ t ≤ runtimeBound M raw.length (a::tail).length (ReadPlan.wordWidth r Q),
      ∃ regs, SubexponentialSAT.StructuredCalls.Eval command t d
        (ScoreBuilderProgram.resultState d regs
          (ScoreBuilderProgram.scoreBytes (context (a::tail) a fixed n M raw d))) := by
  have hc := context_valid (a::tail) a fixed n M raw d hsize hm.width hm.processed hp
  obtain ⟨t, ht, regs, he⟩ := ScoreBuilderProgram.command_eval _ _ hc d
    (inputFor_of_loose a tail fixed n M raw d hm hh)
  have hb := boundedInputs a tail fixed n M raw (cleaned a tail d)
    (cleaned_memory a tail fixed n d hm) hsize hp
  rw [cleaned_context, cleaned_preparation] at hb
  have hb' := ScoreBuilderBounds.sourceBudget_le _ _ hc _ hb
    (by simp [context, ScoreBuilderRawInput.context, CandidateScoreRefinement.candidateContext]) rfl
  refine ⟨t, ?_, regs, he⟩
  exact (ht.trans (Nat.sub_le _ _)).trans (by
    simpa [runtimeBound, context, ScoreBuilderRawInput.context,
      CandidateScoreRefinement.candidateContext] using hb')

end SubexponentialSAT.SqrtLog.PackingIncidenceInput

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed finite command for the weighted packing-score producer.
Every candidate loop, prefix operation, and arithmetic operation is a linked
finite bit program; all varying data live on runtime stacks. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev command : Cmd 16 48 := .seq incidence (.seq heads weightAndMerge)

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramSelect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Run the concrete weighted selector while retaining the literal width and
alphabet for the native packing-layout suffix. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram

def selection : Code := .seq cacheInputs
  (.seq (.call (ProgramLinking.liftProgram
    (SequentialProgram.program PackingProgram.Assembly.command) id lowPorts))
    (.seq (saveHigh 8 62) clearLow))

theorem dataMass_bound (d : Small) (i : Fin 48) : (d.stacks i).length ≤ dataMass d := by
  unfold dataMass
  exact Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin 48 => (d.stacks j).length)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid copies from the actual query frontend's persistent master bank. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open PackingLoaderProgram PackingIncidenceInput
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem staged_bank (a : Local) (hbank : BankEmpty a)
    (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hscopes : a.stacks 718=Scan.scopeBits scopes)
    (hn : a.stacks 128=Scan.unary n) (hmask : a.stacks 719=mask) :
    projectState id ports (staged a)=
      framed (parameterStore a) (Install.input (staged a).regs scopes n mask) := by
  rw [Entry.install_eq]
  apply SubexponentialSAT.CounterForPrograms.data_ext
  · simp [projectState]
  · have hclear : ∀ p ∈ stagePairs, a.stacks p.2 = [] := by
      intro p hp
      simp only [stagePairs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact hbank _
    have hsep : ∀ p ∈ stagePairs, ∀ q ∈ stagePairs, p.1 ≠ q.2 := by
      intro p hp q hq
      simp only [stagePairs,List.mem_cons,List.not_mem_nil,or_false] at hp hq
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
    have hvalue (p : Fin 768 × Fin 768) (hp : p ∈ stagePairs) :
        (staged a).stacks p.2 = a.stacks p.1 := by
      exact copyMany_value stagePairs a (by decide) hclear hsep p hp
    have hframe (i : Fin 64)
        (hi : i ∉ [(32 : Fin 64),33,36,55,56,57,58,59]) :
        (staged a).stacks (ports i) = [] := by
      rw [show (staged a).stacks (ports i) = a.stacks (ports i) from copyMany_frame _ _ _ (by
        intro p hp
        simp only [stagePairs,List.mem_cons,List.not_mem_nil,or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp_all)]
      exact hbank i
    have h32 := hvalue ((718 : Fin 768),ports 32) (by simp [stagePairs])
    have h33 := hvalue ((128 : Fin 768),ports 33) (by simp [stagePairs])
    have h36 := hvalue ((719 : Fin 768),ports 36) (by simp [stagePairs])
    have h55 := hvalue ((720 : Fin 768),ports 55) (by simp [stagePairs])
    have h56 := hvalue ((709 : Fin 768),ports 56) (by simp [stagePairs])
    have h57 := hvalue ((722 : Fin 768),ports 57) (by simp [stagePairs])
    have h58 := hvalue ((723 : Fin 768),ports 58) (by simp [stagePairs])
    have h59 := hvalue ((721 : Fin 768),ports 59) (by simp [stagePairs])
    funext i
    fin_cases i <;> simp [projectState,framed_stack,parameterStore,Entry.sourceStacks,
      hscopes,hn,hmask,h32,h33,h36,h55,h56,h57,h58,h59,hframe]

theorem stage_eval (a : Data) (ht : a.stacks 684=[]) :
    ∃ b, Eval stage (copyManyCost stagePairs (project a)+1) a b ∧
      b.stacks=(staged (project a)).stacks ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) :=
  call_eval stageLocal a (staged (project a)) _ (stageLocal_eval (project a) ht)

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

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

theorem Sources.parameters {a : Wide.Data} {p : Problem} (h : Sources a p) :
    Parameters (Wide.parameterStore (Wide.project a)) p := by
  exact ⟨by simpa [Wide.parameterStore,Wide.project] using h.ambient,
    by simpa [Wide.parameterStore,Wide.project] using h.radius,
    by simpa [Wide.parameterStore,Wide.project] using h.coordinate,
    by simpa [Wide.parameterStore,Wide.project] using h.epsilon,
    by simpa [Wide.parameterStore,Wide.project] using h.incidence⟩

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem stageCost_le (a : Wide.Data) (B : ℕ) (h : WordBound B (Wide.project a)) :
    copyManyCost Wide.stagePairs (Wide.project a) ≤ 8*(7*B+5) :=
  copyManyCost_le Wide.stagePairs (Wide.project a) B stage_separated (fun p _hp=>h p.1)

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramQuantitative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial time and output space for the complete native packing
caller, including global staging, cleanup, and master-bank parking. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpSetupStorage

def globalSize (a : Wide.Data) (p : Problem) :=
  inputMass a+Bounds.scalarSize (Wide.parameterStore (Wide.project a)) p+1

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryResourcesOrigin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual selector provenance for a query.  This package includes every
trial (successful or not), the final selected rows, and an optional mark.
It carries no resource inequality about the resulting query. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open Filter
open scoped Topology
open Asymptotic HashSelectProgram LeafQueryFrontend LeafScopeResourceBounds HighIncidenceProgram

noncomputable section

abbrev ambient (q : Query) := BinaryArithmetic.toNat q.ambient

end
end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms
end


