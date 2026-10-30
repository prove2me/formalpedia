-- Prove2me | Definitions.Def_OAIQ081S132
-- name    : OAIQ081S132
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:42:13.180024+00:00
-- url     : https://prove2.me/theorems/808a8d76-df9f-47a9-8249-ece8bfd88df9
-- title:
--   Definitions bundle OAIQ081S132 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 18 definitions and 12 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.resetState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Endpoint.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Endpoint.builtStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install.frame`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install.withDepth`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgram.Install.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgram.Install.Input`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgram.pairInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.addDepth`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.finish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope.Finished`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.evaluate`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.OuterCode`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputProgram.wordAlphabet`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputProgram.wordWidth`, `OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderRawInput.environment`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_FactorTableProgram`, `SubexponentialSAT_SqrtLog_PackingHeadProgramCandidates`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputEndpoint`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputInstall`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgramInstall`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgramPairs`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramFinish`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyOrder`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyScopeBasic`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyScopeNative`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyScore`, `SubexponentialSAT_SubexpIncidencePlanPrimitives`, `SubexponentialSAT_SubexpIncidencePlanScan`, `SubexponentialSAT_SubexpScopeMembershipProgram`, `SubexponentialSAT_SubexpSetupStorageCost`, `SubexponentialSAT_Subexp_AssignmentInputProgram`, `SubexponentialSAT_Subexp_ScoreBuilderRawInput`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S100`, `OAIQ081S102`, `OAIQ081S106`, `OAIQ081S111`, `OAIQ081S112` and `OAIQ081S113` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S138`, `OAIQ081S147`, `OAIQ081S148`, `OAIQ081S149`, `OAIQ081S150` and `OAIQ081S151`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.shift_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashParameters.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds.prepareHead_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.stageCost_linear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.statsCall_eval` and `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchTypes.filter_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S100
import Definitions.Def_OAIQ081S102
import Definitions.Def_OAIQ081S106
import Definitions.Def_OAIQ081S111
import Definitions.Def_OAIQ081S112
import Definitions.Def_OAIQ081S113

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidencePlanPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed unary-counter and record-emission instructions for incidence plans. -/
namespace SubexponentialSAT.SubexpIncidencePlanPrimitives

open BitProgram StructuredCalls

/-- Emit the supplied unary index exactly when the actual membership flag
is set. The framed list is accumulated in reverse encounter order. -/
theorem emit_eval (selected : Bool) (bits : List Bool) (d : Data)
    (hp : d.stacks 1 = bits.reverse) (hf : d.regs 4 = selected) :
    Eval emit (SubexpNormalizeProgram.emitIfSelectedSteps selected bits + 1)
      d (emitted selected bits d) := by
  let a := SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) selected
    (d.stacks 6) (d.stacks 3) (d.stacks 7) bits.reverse
  let b := SubexpNormalizeProgram.filterState false true false
    (d.stacks 6) (d.stacks 3)
    (if selected then true :: (Encoding.frame bits ++ d.stacks 7) else d.stacks 7) []
  have ha : embedState emitReg emitStack d a = d := by
    apply embedState_eq_of_ports emitReg emitStack d d a emitReg_injective emitStack_injective
    · intro i
      fin_cases i <;> simp [a, emitReg, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.triple, hf]
    · intros; rfl
    · intro i
      fin_cases i <;> simp [a, emitStack, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple, hp]
    · intros; rfl
  have hb : embedState emitReg emitStack d b = emitted selected bits d := by
    apply embedState_eq_of_ports emitReg emitStack d (emitted selected bits d) b
      emitReg_injective emitStack_injective
    · intro i
      fin_cases i <;> simp [b, emitReg, emitted, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.triple]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
      have h4 : i ≠ 4 := fun h => hi ⟨2, h.symm⟩
      simp [emitted, h0, h1, h4]
    · intro i
      fin_cases i <;> simp [b, emitStack, emitted, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple]
    · intro i hi
      have h1 : i ≠ 1 := fun h => hi ⟨3, h.symm⟩
      have h7 : i ≠ 7 := fun h => hi ⟨2, h.symm⟩
      simp [emitted, h1, h7]
  have h := eval_call_lifted SubexpNormalizeProgram.emitIfSelectedProgram emitReg emitStack d
    emitReg_injective emitStack_injective
    (SubexpNormalizeProgram.emitIfSelected_trace selected bits
      (d.stacks 6) (d.stacks 3) (d.stacks 7) (d.regs 0) (d.regs 1))
  change Eval emit _ (embedState emitReg emitStack d a) (embedState emitReg emitStack d b) at h
  simpa only [ha, hb] using h

end SubexponentialSAT.SubexpIncidencePlanPrimitives

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeMembershipProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A concrete scope-membership subroutine for incidence-plan preparation.
The reversed scope record occupies stack 8 and the reversed query stack 2.
Stacks 0,1,3,4 are empty work ports; all remaining stacks are framed.
-/
namespace SubexponentialSAT.SubexpScopeMembershipProgram

open BitProgram StructuredCalls

/-- The only changed stack is the consumed payload on 8. Membership comes
from the actual encoded comparator and iterator, and outer loop registers survive. -/
theorem command_eval (query : List Bool) (records : List (List Bool)) (d : Data)
    (hp : d.stacks 8 = (Encoding.encodeList id records).reverse)
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = [])
    (h2 : d.stacks 2 = query.reverse) (h3 : d.stacks 3 = []) (h4 : d.stacks 4 = []) :
    ∃ (n : ℕ) (rf : Fin 10 → Bool),
      Eval command n d ⟨rf, Function.update d.stacks 8 []⟩ ∧
      rf 4 = decide (query ∈ records) ∧
      (∀ i : Fin 10, 7 ≤ i.val → rf i = d.regs i) ∧
      n ≤ 128 * (query.length + 1) * ((Encoding.encodeList id records).length + 1) := by
  have hs0 : (transferred d).stacks 0 = Encoding.encodeList id records := by
    simp [transferred, StackRoutines.transferStacks, hp, h0]
  obtain ⟨n, e, he, hn, hf, hs, ho, hq, hc, ht, hframe, hregs⟩ :=
    member_eval query records (transferred d) hs0
      (by simpa [transferred, StackRoutines.transferStacks] using h1)
      (by simpa [transferred, StackRoutines.transferStacks] using h2)
      (by simpa [transferred, StackRoutines.transferStacks] using h3)
      (by simpa [transferred, StackRoutines.transferStacks] using h4)
  let e1 := cleared 0 e
  let e2 := cleared 1 e1
  have ho' : e1.stacks 1 = [decide (query ∈ records)] := by simpa [e1, cleared] using ho
  have hclear1 : Eval (clear 1) 5 e1 e2 := by
    simpa only [ho', List.length_cons, List.length_nil] using clear_eval 1 e1
  have hend : e2 = (⟨e2.regs, Function.update d.stacks 8 []⟩ : Data) := by
    apply congrArg (StructuredProgram.State.mk e2.regs)
    funext i
    fin_cases i
    · simp [ e1, cleared, h0]
    · simp [ e1, cleared, h1]
    · simp [ e1, cleared, hq, transferred, StackRoutines.transferStacks]
    · simp [ e1, cleared, hc, h3]
    · simp [ e1, cleared, ht, h4]
    · simp [ e1, cleared, hframe 5 (by decide), transferred, StackRoutines.transferStacks]
    · simp [ e1, cleared, hframe 6 (by decide), transferred, StackRoutines.transferStacks]
    · simp [ e1, cleared, hframe 7 (by decide), transferred, StackRoutines.transferStacks]
    · simp [ e1, cleared, hframe 8 (by decide), transferred, StackRoutines.transferStacks]
    · simp [ e1, cleared, hframe 9 (by decide), transferred, StackRoutines.transferStacks]
  have hexec := (transfer_eval d).seq (he.seq ((clear_eval 0 e).seq hclear1))
  rw [hend] at hexec
  refine ⟨(3 * (d.stacks 8).length + 3) + (n + ((2 * (e.stacks 0).length + 3) + 5)),
    e2.regs, hexec, ?_, ?_, ?_⟩
  · simpa [e2, e1, cleared, readRegs] using hf
  · intro i hi
    have hi0 : i ≠ 0 := by intro h; subst i; contradiction
    have hi1 : i ≠ 1 := by intro h; subst i; contradiction
    simpa [e2, e1, cleared, readRegs, transferred, hi0, hi1] using hregs i hi
  · rw [hp, List.length_reverse]
    exact cost_bound hn hs

theorem scope_eval (v : ℕ) (scope : List ℕ) (d : Data)
    (hp : d.stacks 8 = (Encoding.encodeList Encoding.encodeNat scope).reverse)
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = [])
    (h2 : d.stacks 2 = (Encoding.encodeNat v).reverse)
    (h3 : d.stacks 3 = []) (h4 : d.stacks 4 = []) :
    ∃ (n : ℕ) (rf : Fin 10 → Bool),
      Eval command n d ⟨rf, Function.update d.stacks 8 []⟩ ∧
      rf 4 = decide (v ∈ scope) ∧
      (∀ i : Fin 10, 7 ≤ i.val → rf i = d.regs i) ∧
      n ≤ 128 * (v + 2) * ((Encoding.encodeList Encoding.encodeNat scope).length + 1) := by
  obtain ⟨n, rf, he, hf, hr, hn⟩ := command_eval (Encoding.encodeNat v)
    (scope.map Encoding.encodeNat) d
      (by simpa only [ExecCNFMembership.encodeList_map_encodeNat] using hp) h0 h1 h2 h3 h4
  refine ⟨n, rf, he, ?_, hr, ?_⟩
  · simpa only [encodeNat_mem] using hf
  · simpa only [Encoding.length_encodeNat, ExecCNFMembership.encodeList_map_encodeNat,
      Nat.add_assoc] using hn

end SubexponentialSAT.SubexpScopeMembershipProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidencePlanScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed finite scan of encoded scopes. No slot map is supplied as input:
the local slot order is the encounter order of incident factors. -/
namespace SubexponentialSAT.SubexpIncidencePlanScan

open BitProgram StructuredCalls
open SubexpIncidencePlanPrimitives

theorem callback_eval (regs : Fin 10 → Bool) (v j degree : ℕ)
    (scope : List ℕ) (source out : List Bool) :
    ∃ (n : ℕ) (rf : Fin 10 → Bool),
      Eval callback n (data regs v j source out (scopeBytes scope).reverse degree)
        (data rf v (j + 1) source
          (if v ∈ scope then pushIndex j out else out) []
          (degree + if v ∈ scope then 1 else 0)) ∧
      (∀ i : Fin 10, 7 ≤ i.val → rf i = regs i) ∧ n ≤ callbackBound v j scope := by
  let a := data regs v j source out (scopeBytes scope).reverse degree
  obtain ⟨nm, rm, hm, hf, hr, hn⟩ := SubexpScopeMembershipProgram.scope_eval v scope a
    rfl rfl rfl rfl rfl rfl
  let b : Data := ⟨rm, Function.update a.stacks 8 []⟩
  let c := addedDegree (decide (v ∈ scope)) b
  let e := copied 5 1 c
  let f := emitted (decide (v ∈ scope)) (unary j) e
  let g := incremented 5 f
  have ha := addDegree_eval b (decide (v ∈ scope)) hf
  have hc : c.stacks 3 = [] := by
    by_cases hs : v ∈ scope <;> simp [c, addedDegree, incremented, b, a, data, hs]
  have he := copy_eval 5 1 3 c (by decide) (by decide) (by decide) hc
  have hep : e.stacks 1 = (unary j).reverse := by
    by_cases hs : v ∈ scope <;>
      simp [e, copied, StackRoutines.copyStacks, c, addedDegree, incremented, b, a, data, hs]
  have hef : e.regs 4 = decide (v ∈ scope) := by
    by_cases hs : v ∈ scope <;>
      simp [e, copied, readRegs, c, addedDegree, incremented, b, hs, hf]
  have hemit := emit_eval (decide (v ∈ scope)) (unary j) e hep hef
  have hinc := increment_eval 5 f
  have hend : g = data g.regs v (j + 1) source
      (if v ∈ scope then pushIndex j out else out) []
      (degree + if v ∈ scope then 1 else 0) := by
    apply congrArg (StructuredProgram.State.mk g.regs)
    funext i
    fin_cases i <;> by_cases hs : v ∈ scope <;>
      simp [ incremented, f, emitted, e, copied, StackRoutines.copyStacks,
        c, addedDegree, b, a, data, pushIndex, hs, List.replicate_succ]
  have hrun := hm.seq (ha.seq (he.seq (hemit.seq hinc)))
  change Eval callback _ a g at hrun
  rw [hend] at hrun
  refine ⟨_, g.regs, hrun, ?_, ?_⟩
  · intro i hi
    have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
    have hi1 : i ≠ 1 := by intro h; subst i; simp at hi
    have hi4 : i ≠ 4 := by intro h; subst i; change 7 ≤ 4 at hi; omega
    by_cases hs : v ∈ scope <;>
      simpa [g, incremented, f, emitted, e, copied, readRegs, c, addedDegree,
        b, a, data, hi0, hi1, hi4, hs] using hr i hi
  · have h5 : (c.stacks 5).length = j := by
      by_cases hs : v ∈ scope <;>
        simp [c, addedDegree, incremented, b, a, data, hs]
    have hem := emit_cost (decide (v ∈ scope)) (unary j)
    simp only [List.length_replicate] at hem
    dsimp [callbackBound, scopeBytes] at *
    rw [h5]
    split <;> omega

theorem loop_eval (scopes : List (List ℕ)) (regs : Fin 10 → Bool)
    (v j degree : ℕ) (out suffix : List Bool) :
    ∃ (n : ℕ) (rf : Fin 10 → Bool),
      Eval (RecordPrograms.loop ports callback) n
        (RecordMappedPrograms.afterTag ports scopeBytes (data regs v j [] out [] degree)
          scopes suffix)
        (data rf v (j + scopes.length) suffix
          (indexPrefix (Subexp.IncidencePlanSpec.incidenceFrom v j scopes).reverse ++ out) []
          (degree + (Subexp.IncidencePlanSpec.incidenceFrom v j scopes).length)) ∧
      rf 7 = false ∧ rf 8 = true ∧ rf 9 = false ∧ n ≤ 1 + scanBudget v j scopes := by
  induction scopes generalizing regs j degree out with
  | nil =>
      let rf := Function.update (Function.update (Function.update regs 7 false) 8 true) 9 false
      refine ⟨1, rf, ?_, by simp [rf], by simp [rf], by simp [rf], by simp [scanBudget]⟩
      have h : (RecordMappedPrograms.afterTag ports scopeBytes
          (data regs v j [] out [] degree) [] suffix) = data rf v j suffix out [] degree := by
        exact state_data regs v j degree [] out [] false true false suffix []
      rw [h]
      simpa [RecordPrograms.loop, Subexp.IncidencePlanSpec.incidenceFrom, indexPrefix] using
        (Eval.while_false (test := ports.tag) (body := RecordPrograms.body ports callback)
          (a := data rf v j suffix out [] degree) (by simp [data, rf, ports]))
  | cons C Cs ih =>
      let tail := Encoding.encodeList scopeBytes Cs ++ suffix
      let ra := Function.update (Function.update (Function.update regs 7 false) 8 true) 9 false
      obtain ⟨nc, rc, hcb, hcr, hcn⟩ := callback_eval ra v j degree C tail out
      have hreader := RecordPrograms.reader_eval ports (data regs v j [] out [] degree)
        (scopeBytes C) tail [] true true false
      have hin : RecordMappedPrograms.afterTag ports scopeBytes (data regs v j [] out [] degree)
          (C :: Cs) suffix = RecordPrograms.state ports (data regs v j [] out [] degree)
            true true false (Encoding.frame (scopeBytes C) ++ tail) [] := rfl
      rw [← hin] at hreader
      simp only [List.append_nil] at hreader
      rw [state_data] at hreader
      let out' := if v ∈ C then pushIndex j out else out
      let degree' := degree + if v ∈ C then 1 else 0
      have hrc7 : rc 7 = false := by simpa [ra] using hcr 7 (by decide)
      have hrc8 : rc 8 = true := by simpa [ra] using hcr 8 (by decide)
      have hrc9 : rc 9 = false := by simpa [ra] using hcr 9 (by decide)
      have hstate : RecordPrograms.state ports (data rc v (j+1) [] out' [] degree')
          false true false tail [] = data rc v (j+1) tail out' [] degree' := by
        rw [state_data]
        congr 1
        funext i
        fin_cases i <;> simp [hrc7, hrc8, hrc9]
      have hpop := RecordMappedPrograms.pop_list_eval ports scopeBytes
        (data rc v (j+1) [] out' [] degree') Cs suffix false true
      change Eval _ _ (RecordPrograms.state ports _ false true false tail []) _ at hpop
      rw [hstate] at hpop
      have hbranch := Eval.ite_false (yes := RecordPrograms.atom (.set ports.tag false))
        (show (data rc v (j+1) tail out' [] degree').regs ports.found = false from hrc9) hpop
      have hbody := hreader.seq (hcb.seq hbranch)
      obtain ⟨nr, rr, hrest, hr7, hr8, hr9, hrn⟩ := ih rc (j+1) degree' out'
      have hg : (RecordMappedPrograms.afterTag ports scopeBytes
          (data regs v j [] out [] degree) (C::Cs) suffix).regs ports.tag = true := by
        simp [RecordMappedPrograms.afterTag]
      have hrun := Eval.while_true hg hbody hrest
      refine ⟨6 * (scopeBytes C).length + 4 + (nc + (1 + 1)) + nr + 1,
        rr, ?_, hr7, hr8, hr9, ?_⟩
      · by_cases hs : v ∈ C <;>
          simpa [RecordPrograms.loop, RecordPrograms.body,
            Subexp.IncidencePlanSpec.incidenceFrom, hs, out', degree', indexPrefix,
            pushIndex, List.reverse_cons, List.flatMap_append, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrun
      · simp only [scanBudget]
        omega

theorem command_eval (scopes : List (List ℕ)) (regs : Fin 10 → Bool)
    (v j degree : ℕ) (out suffix : List Bool) :
    ∃ (n : ℕ) (rf : Fin 10 → Bool),
      Eval command n
        (data regs v j (Encoding.encodeList scopeBytes scopes ++ suffix) out [] degree)
        (data rf v (j + scopes.length) suffix
          (indexPrefix (Subexp.IncidencePlanSpec.incidenceFrom v j scopes).reverse ++ out) []
          (degree + (Subexp.IncidencePlanSpec.incidenceFrom v j scopes).length)) ∧
      rf 7 = false ∧ rf 8 = true ∧ rf 9 = false ∧ n ≤ 3 + scanBudget v j scopes := by
  obtain ⟨n, rf, hl, h7, h8, h9, hn⟩ := loop_eval scopes regs v j degree out suffix
  have hs := RecordPrograms.set_found_eval ports (data regs v j [] out [] degree)
    (regs 7) (regs 8) (regs 9) false (Encoding.encodeList scopeBytes scopes ++ suffix) []
  have hp := RecordMappedPrograms.pop_list_eval ports scopeBytes (data regs v j [] out [] degree)
    scopes suffix (regs 7) (regs 8)
  have hrun := hs.seq (hp.seq hl)
  have hstart : RecordPrograms.state ports (data regs v j [] out [] degree)
      (regs 7) (regs 8) (regs 9) (Encoding.encodeList scopeBytes scopes ++ suffix) [] =
      data regs v j (Encoding.encodeList scopeBytes scopes ++ suffix) out [] degree := by
    rw [state_data]
    simp only [Function.update_eq_self]
  rw [hstart] at hrun
  exact ⟨1+(1+n), rf, hrun, h7, h8, h9, by omega⟩

end SubexponentialSAT.SubexpIncidencePlanScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupStorageCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Cost of the concrete setup storage instructions

Copying and cleanup are charged by the lengths of the words physically read.
The final stage bound is linear in a common word bound; its coefficients depend
only on the statically allocated ports and copy lists.
-/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem clearMany_wordBound {S : ℕ} (ps : List (Fin S)) (a : Data S) (B : ℕ)
    (ha : WordBound B a) : WordBound B (clearManyState ps a) := by
  intro i
  rw [clearMany_stacks]
  split
  · simp
  · exact ha i

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
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

abbrev OuterCode := Cmd 16 896

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadProgramCandidates
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed producer of all incremental head scores from the candidate alphabet
and actual flattened prior-head table. No selected pair records are inputs. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates
open SubexponentialSAT BitProgram StructuredCalls StackRoutines SubexpScanPrimitives
open Subexp

abbrev Data := State 8 12

def resetState (d : Data) : Data := ⟨fun i => decide (i=6),d.stacks⟩

end SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ScoreBuilderRawInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Score-builder inputs from physically generated raw pair plans

The runtime pair table is retained in its actual generated order. A
permutation proof connects that order to the mathematical vertex-pair list;
the code never decodes plans back to vertex identifiers.
-/

namespace SubexponentialSAT.Subexp.ScoreBuilderRawInput

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SlotAssignment

def environment {r Q : ℕ} (Δ : ℕ) (alphabet : List (Word r Q))
    (seedCount : ℕ) (rawPlans : List PairScoreProgram.PlanPair) : Fin 48 → List Bool :=
  ScoreBuilderProgram.environment
    (ProgramEncoding.encodeRecords (alphabet.map ReadPlan.encodeWord))
    (List.replicate (2 * (Δ + 1)) true)
    (PairScoreProgram.pairRecords rawPlans)
    (PairPreparationProgram.seedBytes seedCount) (SelectionTableProgram.unary seedCount)

end SubexponentialSAT.Subexp.ScoreBuilderRawInput

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceProgramPairs
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual depth-two tuple program builds all raw incidence-pair records.
Its input has one two-address record per incidence, not a quadratic table. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.Subexp

def pairInput (plans : List (List ℕ)) : SubexponentialSAT.StructuredProgram.State 10 9 :=
  ⟨fun _ => false, fun j =>
    if j = 1 then ProgramEncoding.encodeRecords (planAlphabet plans)
    else if j = 8 then [true, true] else []⟩

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

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
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem records_map (js : List ℕ) :
    ProgramEncoding.encodeRecords (js.map unary) = Encoding.encodeList unary js := by
  induction js with
  | nil => rfl
  | cons j js ih => simp [ProgramEncoding.encodeRecords,Encoding.encodeList] at ih ⊢; exact ih
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan


/-! Fixed cleanup for the native scope-address scanner. -/


/-! Calls to the fixed record mapper inside the native scope scan. -/


/-! One native low-variable step, including its uncovered neutral factor. -/


/-! Runtime high-mask loop for the original-address incidence stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem prefix_terminated (ps : List (List ℕ)) :
    recordPrefix ps ++ [false] = ProgramEncoding.encodeRecords
      (PackingIncidenceProgram.planAlphabet ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simpa [recordPrefix,PackingIncidenceProgram.planAlphabet,ProgramEncoding.encodeRecords,
        Encoding.encodeList,List.append_assoc] using congrArg
          (fun tail => (true :: Encoding.frame (Encoding.frame (CollisionStreamProgram.planBytes p))) ++ tail) ih

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop


/-! Count the physical scope stream before constructing native incidence plans. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceProgramInstall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid generation and installation of raw pairs from a linear plan stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram.Install
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev Data := State 16 48

def Input (plans : List (List ℕ)) (d : Data) : Prop :=
  (∀ i, d.stacks (ports i) = (pairInput plans).stacks i) ∧
  d.stacks 7 = [] ∧ d.stacks 45 = []

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram.Install

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputInstall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Raw scope bytes and a mask produce the actual installed incidence-pair table. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
abbrev Data := State 16 48

def frame (r : Fin 16 → Bool) : Data := ⟨r,fun _ => []⟩
def withDepth (d : Data) := TupleProgram.pushedState 27 0 true
  (TupleProgram.pushedState 27 0 true d)
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputEndpoint
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact five-port handoff from the native incidence producer to its loader. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Endpoint
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
abbrev Data := Install.Data

def builtStacks (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) : Fin 48 → List Bool :=
  fun j => if j=32 then Scan.scopeBits scopes else if j=33 then Scan.unary n
    else if j=34 then Scan.unary mask.length
    else if j=35 then Scan.unary (Semantics.factorCount scopes mask)
    else if j=20 then ProgramEncoding.encodeRecords
      (PackingIncidenceProgram.planAlphabet (Install.plans scopes n mask)) else []

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Endpoint

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInputProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

def wordAlphabet : Code := AssignmentInputCall.call TupleProgram.generateProgram
  (by decide) (by decide) [(7, 13), (2, 20)] 0 30

def wordWidth : Code := AssignmentInputCall.call BlockCopyProgram.program
  (by decide) (by decide) [(1, 12), (2, 15)] 1 10

end SubexponentialSAT.Subexp.AssignmentInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Install the packing scorer's depth and binary parameter bank after the
native alphabet/assignment producer has finished using its low workspace. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage SubexponentialSAT.Subexp
attribute [local simp] Fin.coe_ofNat_eq_mod

def addDepth : Code := .seq (TupleProgram.pushConst 34 0 true) (TupleProgram.pushConst 34 0 true)
def finish : Code := .seq addDepth (copyMany 31 parameterCopies)

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyScore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact values and uniform bounds for the two physically produced streams. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp

section Scores
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

def evaluate (alphabet : List (Word r Q)) (pairs : List (I × I))
    (indices : List (V ⊕ E)) (default : Word r Q) (heads s M n : ℕ)
    (fixed : List (Word r Q)) : ℕ :=
  match fixed with
  | [] => 0
  | candidate::prior => candidateScore ivar factor alphabet pairs indices default heads s M n prior candidate

end Scores
end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyOrder
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Equality of all candidate comparisons with the original rational score. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp SubexponentialSAT.SqrtLog.Packing

section Ordering
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ} [NeZero r]

omit [NeZero r] [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem sequentialIncidenceCount_eq (alphabet : List (Word r Q)) (pairs : List (I × I))
    (vertices : List V) (factors : List E) (default : Word r Q) (remaining : ℕ)
    (fixed : List (Word r Q)) :
    PackingHeadIncremental.sequentialIncidenceCount ivar factor alphabet pairs vertices factors default remaining fixed =
      PackingIncidenceProgram.incidenceNumerator ivar factor alphabet pairs
        (headsFirstIndices vertices factors) default remaining fixed := by
  let heads : List (Fin Q × V × V) := (List.finRange Q).flatMap (fun t =>
    (vertices.product vertices).map (fun p => (t,p.1,p.2)))
  have ht : PackingHeadIncremental.headTerms (I:=I) (Q:=Q) vertices = heads.map Sum.inr := by
    simp [PackingHeadIncremental.headTerms,heads,List.map_flatMap,List.map_map,Function.comp_def]
  unfold PackingHeadIncremental.sequentialIncidenceCount PackingIncidenceProgram.incidenceNumerator
  rw [ht,PackingIncidenceProgram.unweightedCounts_split]

end Ordering
end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyScopeBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Retain the final memory invariant of the checked sequential loop. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem program_memory {A : Type*} (encode : A → List Bool) (a : A) (tail : List A)
    (evaluate : ℕ → List A → ℕ) (builder : Cmd 16 48) (cost bound total : ℕ)
    (env : Fin 48 → List Bool)
    (hwidth : ∀ x, (encode x).length=(encode a).length)
    (hscore : ∀ n fixed x, n+1+fixed.length ≤ total → x∈a::tail → evaluate n (x::fixed) ≤ bound)
    (hbuilder : SequentialProgram.ScoreBuilderRefines encode a tail evaluate builder cost total env)
    (d : Data) (hm : SequentialProgram.Memory encode a tail total [] d.stacks)
    (hc : (d.stacks 11).length=total) (he : SequentialProgram.HighState env d.stacks) :
    ∃ e : Data, RunsIn (SequentialProgram.program builder)
      (total*(cost+SequentialProgram.selectionBudget (a::tail).length bound total (encode a).length+3)+3)
      (d.withPC (some (SequentialProgram.program builder).entry)) (e.withPC none) ∧
      SequentialProgram.Memory encode a tail 0
        (NaturalAssignment.assignNat a tail evaluate total []) e.stacks ∧
      e.stacks 11=[] ∧ SequentialProgram.HighState env e.stacks := by
  have hstep := SequentialProgram.stepRefines_of_scoreBuilder encode a tail evaluate builder
    cost bound total env hwidth hscore hbuilder
  obtain ⟨t,ht,e,hr,hem,hc',he'⟩ := SequentialProgram.loop_eval encode a tail evaluate builder
    (cost+SequentialProgram.selectionBudget (a::tail).length bound total (encode a).length)
    total env hstep total [] d (by simp) hm hc he
  exact ⟨e,⟨(1+t)+1,by omega,
    compiled_halt_trace ((SequentialProgram.peek_eval d).seq hr) 8 8⟩,hem,hc',he'⟩

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyScopeNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact output and preserved high metadata for the native-scope controller. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

def Finished (rows : List (List Bool)) (d e : Data) : Prop :=
  e.stacks 8=rows.flatten ∧ e.stacks 11=[] ∧
  e.stacks 9=d.stacks 9 ∧ (e.stacks 10).length=(d.stacks 10).length ∧
  (e.stacks 19).length=rows.length ∧
  (∀ j∈SequentialProgram.scratchPorts, e.stacks j=[]) ∧
  (∀ j : Fin 48,20 ≤ j.val→e.stacks j=d.stacks j)

theorem Finished.length_bound {rows : List (List Bool)} {d e : Data} {B : ℕ}
    (h : Finished rows d e) (hd : ∀ j,(d.stacks j).length ≤ B)
    (hb : rows.flatten.length ≤ B) (hr : rows.length ≤ B) :
    ∀ j,(e.stacks j).length ≤ B := by
  rcases h with ⟨ho,hc,ha,hw,hp,hs,hhi⟩
  intro j
  by_cases hj : 20 ≤ j.val
  · rw [hhi j hj]
    exact hd j
  · have hclass := (show ∀ j : Fin 48,j.val < 20 →
        j∈SequentialProgram.scratchPorts ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=19 by decide) j (by omega)
    rcases hclass with hscratch|rfl|rfl|rfl|rfl|rfl
    · rw [hs j hscratch]; simp
    · simpa only [ho] using hb
    · rw [ha]; exact hd 9
    · rw [hw]; exact hd 10
    · rw [hc]; simp
    · simpa only [hp] using hr

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope

end OAI.Algorithms
end


