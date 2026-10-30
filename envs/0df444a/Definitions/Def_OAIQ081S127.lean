-- Prove2me | Definitions.Def_OAIQ081S127
-- name    : OAIQ081S127
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:39:30.14155+00:00
-- url     : https://prove2.me/theorems/97e74c67-20fc-41f6-a2c3-8bcab858fdb7
-- title:
--   Definitions bundle OAIQ081S127 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 82 declarations of OpenAI's Lean: 61 definitions and 21 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Constants.input`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Constants.output`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Count.Prepare.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Count.Prepare.output`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Count.cachesCleared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Count.clearCaches`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Count.install`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Count.project`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.indicatorReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Incidence.exportResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Incidence.stage`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.planColor`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount.rankValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.CleanWork`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.clear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.clearPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.clearPortsCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.clearResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.clearedPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.copied`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.copiedPlan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.copyPlan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.copyPlanCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.overwrite`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.buildConstant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.constantBatch`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.constantCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.copied`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.copiedPlan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.nodeFramesCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.nodesCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.paddingCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.tableCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.wideState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.addressedPacking`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor.includeNode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor.scan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor.seq` and 21 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LeafParametersProgramBank`, `SubexponentialSAT_SqrtLog_LeafProgramConstants`, `SubexponentialSAT_SqrtLog_LeafProgramCount`, `SubexponentialSAT_SqrtLog_LeafProgramCountCorrect`, `SubexponentialSAT_SqrtLog_LeafProgramCountPrepare`, `SubexponentialSAT_SqrtLog_LeafProgramFactor`, `SubexponentialSAT_SqrtLog_LeafProgramIncidence`, `SubexponentialSAT_SqrtLog_LeafProgramLayoutMasters`, `SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteQueryPlan`, `SubexponentialSAT_SqrtLog_LeafProgramPreparedBranchCount`, `SubexponentialSAT_SqrtLog_LeafProgramQueryInput`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendConstants`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramBase`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramInterpolation`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_MomentsReadoutProgramState`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputAddressedProvenance`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputPackingTransport`, `SubexponentialSAT_SqrtLog_ReconstructionProgramCalls`, `SubexponentialSAT_SqrtLog_ReconstructionProgramCofactor`, `SubexponentialSAT_SqrtLog_ReconstructionProgramCofactorOuter`, `SubexponentialSAT_SqrtLog_ReconstructionProgramCofactorScan`, `SubexponentialSAT_SqrtLog_ReconstructionProgramControl`, `SubexponentialSAT_SqrtLog_ReconstructionProgramEntry`, `SubexponentialSAT_SqrtLog_ReconstructionProgramHorner`, `SubexponentialSAT_SqrtLog_ReconstructionProgramLocal`, `SubexponentialSAT_SqrtLog_ReconstructionProgramMiddle`, `SubexponentialSAT_SqrtLog_ReconstructionProgramScalar`, `SubexponentialSAT_SqrtLog_ReconstructionProgramScalarSteps`, `SubexponentialSAT_SqrtLog_ReconstructionProgramSetup`, `SubexponentialSAT_SqrtLog_RingProgramTableInitial`, `SubexponentialSAT_SubexpCRTOuterControl`, `SubexponentialSAT_SubexpCRTOuterFinish`, `SubexponentialSAT_SubexpCRTOuterSweep`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S100`, `OAIQ081S102`, `OAIQ081S106`, `OAIQ081S107`, `OAIQ081S108` and `OAIQ081S109` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S144`, `OAIQ081S145`, `OAIQ081S146` and `OAIQ081S152`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.add_rank`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor.scan_state_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Entry.prepare_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.controller_run_framed` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.initialize_run`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.canonical_wide_read`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.rawCommand_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor.scan_state_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Entry.prepare_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.controller_run_framed` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.initialize_run`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S100
import Definitions.Def_OAIQ081S102
import Definitions.Def_OAIQ081S106
import Definitions.Def_OAIQ081S107
import Definitions.Def_OAIQ081S108
import Definitions.Def_OAIQ081S109

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

open BitProgram StructuredCalls BinaryArithmetic

theorem power_eval (r : Regs) (w : Words) (a b o : Fin 64)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ t rf word,
      Eval (powerCmd a b o hoa hob) t (state r w)
        (state rf (Function.update w o word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w a) ^ BinaryArithmetic.toNat (w b) ∧
      word.length ≤ 1 + BinaryArithmetic.toNat (w b) * (w a).length ∧
      t ≤ PowerPrograms.runtimeBound (w a) (w b) + 9 * (w b).length + 8 := by
  have hv : PowerCalls.Valid (powerPorts a b o hoa hob) (state r w) := by
    constructor
    · simpa only [powerPorts, state_port] using ho
    · intro i
      have hi : 64 ≤ (work 7 (by decide) i).val := by
        change 64 ≤ 64 + i.val
        omega
      exact state_work r w (work 7 (by decide) i) hi
  obtain ⟨t, rf, word, he, hval, hlen, htime⟩ :=
    PowerCalls.powerAt_spec (powerPorts a b o hoa hob) (state r w) hv
  refine ⟨t, rf, word, ?_, ?_, ?_, ?_⟩
  · simpa only [powerCmd, powerPorts, state_update] using he
  · simpa only [powerPorts, state_port] using hval
  · simpa only [powerPorts, state_port] using hlen
  · simpa only [powerPorts, state_port] using htime


end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableInitial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

theorem literalStep_eval {B : ℕ} (s : Store) (regs : Fin 8 → Bool)
    (seed zeroWord : Word B) (hnew : s.newTail.length ≤ B) :
    ∃ n ≤ 19*B+16, Eval literalStep n
      (state regs {s with left := seed.val, zero := zeroWord.val})
      (state (readRegs regs 1 3 none) {s with left := zeroWord.val, zero := zeroWord.val, newTail := seed.val, output := seed.val.reverse ++ s.output}) := by
  let s0 := {s with left := seed.val, zero := zeroWord.val}
  let s1 := {s0 with newTail := []}
  let s2 := {s1 with newTail := seed.val}
  let s3 := {s2 with left := [], output := seed.val.reverse ++ s.output}
  let s4 := {s3 with left := zeroWord.val}
  let rr := readRegs regs 1 3 none
  have h1 := clear_store_eval s0 s1 regs 19 (by
    funext i; fin_cases i <;> simp [clearStacks, tapes, s1])
  have h2 := copy_store_eval s1 s2 rr 0 19 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s2, s1, s0])
  have h3 := transfer_store_eval s2 s3 rr 0 20 (by decide) (by
    funext i; fin_cases i <;> simp [transferStacks, tapes, s3, s2, s1, s0])
  have h4 := copy_store_eval s3 s4 rr 24 0 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s4, s3, s2, s1, s0])
  simp only [rr, readRegs_reset] at h2 h3 h4
  refine ⟨_, ?_, h1.seq (h2.seq (h3.seq h4))⟩
  simp [s0, s1, s2, s3, tapes]
  omega

abbrev literalEnd {B : ℕ} : ℕ → Word B → Word B → Word B
  | 0, seed, _ => seed
  | n+1, _, zeroWord => literalEnd n zeroWord zeroWord

abbrev literalLast {B : ℕ} : ℕ → Word B → Word B → List Bool → List Bool
  | 0, _, _, old => old
  | n+1, seed, zeroWord, _ => literalLast n zeroWord zeroWord seed.val

theorem literalLoop_eval {B : ℕ} (n : ℕ) (seed zeroWord : Word B)
    (s : Store) (regs : Fin 8 → Bool) (count : List Bool)
    (hcount : count.length = n) (hnew : s.newTail.length ≤ B) :
    ∃ m ≤ n*(19*B+18)+1, ∃ rf, Eval literalLoop m
      (state (readRegs regs 1 3 count.head?) {s with left := seed.val, zero := zeroWord.val, count := count.tail})
      (state rf {s with left := (literalEnd n seed zeroWord).val, zero := zeroWord.val, count := [], newTail := literalLast n seed zeroWord s.newTail, output := (literalBits n seed zeroWord).reverse ++ s.output}) := by
  induction n generalizing seed s regs count with
  | zero =>
    have hc : count = [] := List.length_eq_zero_iff.mp hcount
    subst count
    refine ⟨1, by simp, readRegs regs 1 3 none, ?_⟩
    apply Eval.while_false
    simp [ readRegs_present]
  | succ n ih =>
    cases count with
    | nil => simp at hcount
    | cons bit count =>
      have hc : count.length = n := by simpa using hcount
      obtain ⟨m, hm, hs⟩ := literalStep_eval {s with count := count}
        (readRegs regs 1 3 (some bit)) seed zeroWord hnew
      let s' := {s with newTail := seed.val, output := seed.val.reverse ++ s.output}
      have hp := popCount_eval {s' with left := zeroWord.val, zero := zeroWord.val, count := count}
        (readRegs (readRegs regs 1 3 (some bit)) 1 3 none)
      obtain ⟨k, hk, rf, hl⟩ := ih zeroWord s'
        (readRegs (readRegs regs 1 3 (some bit)) 1 3 none) count hc seed.property.le
      have he := Eval.while_true
        (show (state (readRegs regs 1 3 (some bit)) {s with left := seed.val, zero := zeroWord.val, count := count}).regs 3 = true by
          simp [ readRegs_present])
        (hs.seq hp) hl
      refine ⟨m+1+k+1, ?_, rf, ?_⟩
      · nlinarith
      · simpa only [literalLoop, literalBits, literalEnd, literalLast,
          List.head?_cons, List.tail_cons, List.reverse_append, List.append_assoc, s'] using he

theorem literalScan_eval {B : ℕ} (n : ℕ) (seed zeroWord : Word B)
    (s : Store) (regs : Fin 8 → Bool) (count : List Bool)
    (hcount : count.length = n) (hnew : s.newTail.length ≤ B) :
    ∃ m ≤ n*(19*B+18)+2, ∃ rf, Eval literalScan m
      (state regs {s with left := seed.val, zero := zeroWord.val, count := count})
      (state rf {s with left := (literalEnd n seed zeroWord).val, zero := zeroWord.val, count := [], newTail := literalLast n seed zeroWord s.newTail, output := (literalBits n seed zeroWord).reverse ++ s.output}) := by
  have hp := popCount_eval {s with left := seed.val, zero := zeroWord.val, count := count} regs
  obtain ⟨m, hm, rf, hl⟩ := literalLoop_eval n seed zeroWord s regs count hcount hnew
  exact ⟨1+m, by omega, rf, hp.seq hl⟩

theorem literalLast_length_le {B : ℕ} (n : ℕ) (seed zeroWord : Word B)
    (old : List Bool) (hold : old.length ≤ B) :
    (literalLast n seed zeroWord old).length ≤ B := by
  induction n generalizing seed old with
  | zero => exact hold
  | succ n ih => exact ih zeroWord seed.val seed.property.le


end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramConstants
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical dynamic-dimension constants. The same fixed loop emits a scalar
seed in coordinate zero followed by scalar zero in every other coordinate. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Constants

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing RingProgramTable

def input {B : ℕ} (s : Store) (seed zeroWord : Word B) : Store :=
  {s with left := seed.val, zero := zeroWord.val, count := [], newTail := [], output := [], vector := []}

def output {B : ℕ} (s : Store) (d : ℕ) (seed zeroWord : Word B) : Store :=
  {s with left := [], zero := zeroWord.val, count := [], newTail := [], output := [], vector := literalBits d seed zeroWord}

theorem command_eval {B : ℕ} (d : ℕ) (seed zeroWord : Word B)
    (s : Store) (regs : Fin 8 → Bool) (hd : s.degree.length = d) :
    ∃ n ≤ budget B d, ∃ finalRegs,
      Eval command n (state regs (input s seed zeroWord))
        (state finalRegs (output s d seed zeroWord)) := by
  let a := input s seed zeroWord
  let a1 := {a with count := s.degree}
  have hc := copy_store_eval a a1 regs 22 11 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, a1, a, input])
  obtain ⟨n,hn,rf,he⟩ := literalScan_eval d seed zeroWord a
    (readRegs regs 1 3 none) s.degree hd (by simp [a,input])
  let b := {a with left := (literalEnd d seed zeroWord).val, count := [], newTail := literalLast d seed zeroWord [], output := (literalBits d seed zeroWord).reverse}
  have he' : Eval literalScan n (state (readRegs regs 1 3 none) a1) (state rf b) := by
    simpa [a1,b,a,input] using he
  let c := {b with output := [], vector := literalBits d seed zeroWord}
  let e := {c with left := []}
  let f := {e with newTail := []}
  have ht := transfer_store_eval b c rf 20 15 (by decide) (by
    funext i; fin_cases i <;> simp [transferStacks,tapes,b,c,a,input])
  have hl := clear_store_eval c e (readRegs rf 1 3 none) 0 (by
    funext i; fin_cases i <;> simp [clearStacks,tapes,e])
  have hnew := clear_store_eval e f (readRegs rf 1 3 none) 19 (by
    funext i; fin_cases i <;> simp [clearStacks,tapes,f])
  simp only [readRegs_reset] at hl hnew
  have hlast : (literalLast d seed zeroWord []).length ≤ B :=
    literalLast_length_le d seed zeroWord [] (by simp)
  refine ⟨7*(tapes a 22).length+5 + (n + (3*(tapes b 20).length+3 +
    (2*(tapes c 0).length+3 + (2*(tapes e 19).length+3)))),?_,readRegs rf 1 3 none,?_⟩
  · change 7*s.degree.length+5 + (n + (3*(literalBits d seed zeroWord).reverse.length+3 +
      (2*(literalEnd d seed zeroWord).val.length+3 +
        (2*(literalLast d seed zeroWord []).length+3)))) ≤ budget B d
    have hend : (literalEnd d seed zeroWord).val.length = B := (literalEnd d seed zeroWord).property
    rw [hd,List.length_reverse,literalBits_length,hend]
    unfold budget
    nlinarith
  · simpa only [command,a,a1,b,c,e,f,input,output] using hc.seq (he'.seq (ht.seq (hl.seq hnew)))

theorem program_run {B : ℕ} (d : ℕ) (seed zeroWord : Word B)
    (s : Store) (regs : Fin 8 → Bool) (hd : s.degree.length = d) :
    ∃ finalRegs, RunsIn program (budget B d + 1)
      ((state regs (input s seed zeroWord)).withPC (some program.entry))
      ((state finalRegs (output s d seed zeroWord)).withPC none) := by
  obtain ⟨n,hn,rf,he⟩ := command_eval d seed zeroWord s regs hd
  exact ⟨rf,n+1,Nat.add_le_add_right hn 1,compiled_halt_trace he 0 15⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Constants

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

local infixr:55 " ;; " => seq

def clearMany : List (Fin 320) → Code
  | [] => .base .skip
  | src :: rest => clear src ;; clearMany rest

def buildJetWidth : Code :=
  copy 243 279 ;; resetThreeRegisters ;;
    .call (ProgramLinking.liftProgram Subexp.BlockCopyProgram.program
      threeRegisters blockCopyPorts)

def advance : Code :=
  copy 259 258 ;; clearMany [213,216,225,259] ;; incrementIndex

def cleanup : Code := clearMany [104,214,257,258,260,266,268,277]


def loadCurrent : Code := takeNode ;; copy 259 213 ;; copy 260 216 ;; takeJet

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterSweep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

open BitProgram StructuredCalls SubexpScanPrimitives

def sweepIteration (middle : Code) : Code :=
  .seq loadCurrent (.seq middle advance)

def sweepLoop (middle : Code) : Code :=
  .while 15 (.seq (sweepIteration middle) testNodes)

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Final cleanup and complete tape-loop costs for scalar reconstruction.
The arithmetic-middle premise below is an actual execution of a fixed command;
its concrete implementation is assembled separately from the CRT services. -/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open BitProgram StructuredCalls SubexpScanPrimitives
open scoped BigOperators

def loopAndCleanup (middle : Code) : Code :=
  .seq testNodes (.seq (sweepLoop middle) cleanup)

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

local infixr:55 " ;; " => seq

def initializeCode : Code :=
  copy 280 104 ;; copy 280 261 ;; countDimension ;; buildJetWidth ;;
  copy 256 214 ;; copy 256 257 ;; copy 265 266

end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-table outer Hermite traversal for arbitrary coefficient width.
Only the arithmetic middle is parameterized; this module charges all input
copying, node/jet transport, indexing, iteration and final cleanup. -/

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram

def controller (middle : Code) : Code := .seq initializeCode (loopAndCleanup middle)


end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramCalls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed invocation of the fixed lower-256 arithmetic controllers. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram

/-- The lower register bank is identical; compilation adds one paid return. -/
abbrev lowerCall (code : Cmd 16 256) (input output : Fin 256) : Code :=
  liftCommand code input output id localPorts

end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical preparation of the low scalar caches used by dense polynomial
addition. The high copies remain available to all native ring services. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Entry

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram

def prepare : Code := .seq (copy 194 5) (copy 202 10)

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Entry

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramCofactor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native scalar cofactor construction for the Hermite value at zero. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (LowFrame ServiceSpec binaryStep nativeRepeat replace loopReady)

def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

/-- Save the accumulator, form minus-node by actual multiplication, then
multiply the saved accumulator by that value J times. -/
def includeNode (multiply : Code) : Code :=
  replace 240 223 ;; replace 218 240 ;; replace 211 241 ;; binaryStep multiply ;;
  replace 240 219 ;; replace 223 240 ;; replace 219 241 ;; clear 223 ;;
  copy 243 246 ;; nativeRepeat (binaryStep multiply) ;; clear 241

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramCofactorScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (LowFrame ServiceSpec)

def scan (multiply : Code) : Code := SubexpNodeScanControl.command (includeNode multiply)

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramCofactorOuter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open CRTLocalProgram (ServiceSpec LowFrame)

def seq (a b : Code) : Code := .seq a b

end SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramHorner
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical staging of local CRT correction evaluation. The dense correction
is consumed from 244; its value at the retained point 263 is returned on 264. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open CRTLocalProgram (ServiceSpec LowFrame)

def seq (a b : Code) : Code := .seq a b

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner

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

def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

abbrev command (localCode : Cmd 16 256) : Code :=
  copy 277 192 ;; copy 243 193 ;; lowerCall localCode 225 244 ;; clearMany [192,193]

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Local

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed outer calls to the native scalar ring arithmetic. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open CRTLocalProgram (ServiceSpec LowFrame)

def seq_p0 (a b : Code) : Code := .seq a b

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramScalarSteps
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open CRTLocalProgram (ServiceSpec)

def seq_p1 (a b : Code) : Code := .seq a b

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramMiddle
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Composition of the physical arithmetic stages for one Hermite node. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open CRTLocalProgram (LowFrame ServiceSpec)

def seq (a b : Code) : Code := .seq a b

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One closed native count-recovery table: Hermite reconstruction over the
computed ring, integer readback, and reclamation of the two CRT entry caches.
Node-jet production and its semantic theorem are composed at the caller. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Count

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev clearCaches : Cmd 40 768 :=
  .seq (.call (StackRoutines.clearProgram 5 0 1)) (.call (StackRoutines.clearProgram 10 0 1))

def cachesCleared (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,Function.update (Function.update a.stacks 5 []) 10 []⟩

@[simp] theorem cachesCleared_five (a : Data) : (cachesCleared a).stacks 5 = [] := by
  simp [cachesCleared]
@[simp] theorem cachesCleared_ten (a : Data) : (cachesCleared a).stacks 10 = [] := by
  simp [cachesCleared]

end SubexponentialSAT.SqrtLog.LeafProgram.Count

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramCountCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed count recovery: the native Hermite program, the native first-word
reader, and physical reclamation of the CRT caches. The hypotheses describe
stored data and the polynomial, never an assumed arithmetic execution. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Count

open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open DensePolynomialProgram


noncomputable def install (frame : Data) (a : SubexpCRTOuterProgram.Data) : Data :=
  embedState crtRegisters crtStacks frame a

def project (a : Data) : SubexpCRTOuterProgram.Data :=
  projectState crtRegisters crtStacks a

end SubexponentialSAT.SqrtLog.LeafProgram.Count

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramCountPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual reclamation of node-work scratch before Hermite reconstruction.
The static port set includes both the native CRT work ports and the scalar/
polynomial arithmetic readiness ports, together with the reader temporaries. Runtime data are cleared by real
stack loops; persistent node and jet inputs remain outside this set. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Count.Prepare

open SubexponentialSAT BitProgram StructuredCalls

def output (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,
    BankRoutines.clearBankStacks ports (Function.update a.stacks 699 [])⟩

def budget (a : Data) : ℕ :=
  2*(a.stacks 699).length+6+3*ports.length+
    2*(ports.map (fun i => (a.stacks i).length)).sum

end SubexponentialSAT.SqrtLog.LeafProgram.Count.Prepare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramIncidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The selected-factor incidence service with a concrete source generator.
All ring/layout inputs are copied from persistent masters, and the complete
private worker is reclaimed after exporting the actual lookup table. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Incidence
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

abbrev stage : Cmd 16 768 := .seq (copyMany 684 pairs) SourceControls.cutoff
abbrev exportResult : Cmd 16 768 := .seq (copyCmd 561 62 684) (clearMany workerPorts)

end SubexponentialSAT.SqrtLog.LeafProgram.Incidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed per-assignment factor evaluation. Factors are dispatched by runtime
ID; hash rows are expanded and tested by the computed idempotent, the marked
clause is multiplied directly, and added neutral factors contribute one.
Every operation below is an actual finite instruction table or native loop. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls

def indicatorReady : Code := .seq (.base (.atom (.set 0 false)))
  (.seq (.base (.atom (.set 1 true))) (.base (.atom (.set 2 false))))

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end
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

theorem parkCost_le (a : LocalData) (B : ℕ) (h : WordBound B a)
    (hz : ∀ i,a.stacks (high i)=[]) : parkCost a ≤ 14*(9*B+8) := by
  have hc := copyManyCost_le parkPairs a B park_sep (fun p hp => h p.1)
  have hw := copyMany_wordBound parkPairs a B park_nodup
    (by intro p hp; simp only [parkPairs,List.mem_map,List.mem_finRange,true_and] at hp
        obtain ⟨i,rfl⟩ := hp; exact hz i) park_sep h
  have hd := clearManyCost_le lowPorts (copyManyState parkPairs a) B hw
  change copyManyCost parkPairs a ≤ 14*(7*B+5) at hc
  change clearManyCost lowPorts (copyManyState parkPairs a) ≤ 14*(2*B+3) at hd
  unfold parkCost
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed forty-stack workspace for the two runtime readout counters. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def wideState (regs : Fin 8 → Bool) (a : D) (h : High) : WideData :=
  ⟨regs,wideTapes a h⟩

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! Actual stack construction of the sparse key (u,z,empty support), followed
by the paid query cleanup and unary-index increment. -/


/-! One concrete (u,z) coefficient fetch, addition, and index advance. -/


/-! The U loop is driven by a real unary stack. Every visit invokes the
concrete key builder and dictionary scan; no callback is left abstract. -/


/-! Seed one Z accumulator from the cached zero vector and append the
completed coefficient to the output, paying for every copy and reversal. -/


/-! Runtime Z enumeration. Completed fixed-width coefficients are prepended
in reverse and are restored once by the final output transfer. -/


/-! Build the all-false support mask from the actual ambient shape stack.
The loop length is the ambient number of variables, including unused ones. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputPackingTransport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Changing only the displayed incidence-list length transports the same
packing; numeric positions, labels, metadata bytes, and matrix values agree. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes

variable {D E : ℕ} {U : Type*}

variable {r Q : ℕ}

def addressedPacking (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (P : PackingData (Semantics.Incidences scopes mask) U) :
    PackingData (Fin (addressedEntries scopes n mask).length) U :=
  reindexPacking (addressedEntries_length scopes n mask).symm P

@[simp] theorem addressedPacking_label (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (P : PackingData (Semantics.Incidences scopes mask) U)
    (i : Fin (addressedEntries scopes n mask).length) :
    (addressedPacking scopes n mask P).label i = P.label (addressedIndex scopes n mask i) := by
  rw [addressedPacking,reindexPacking_label]
  rfl

@[simp] theorem addressedPacking_entryNat (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (P : PackingData (Semantics.Incidences scopes mask) (UniversalType r Q 1))
    (A R : ℕ) (t : Fin Q) (i j : ℕ) :
    BucketProgram.ProducedRank.entryNat (addressedPacking scopes n mask P) A R t i j =
      BucketProgram.ProducedRank.entryNat P A R t i j := by
  exact reindexPacking_entryNat _ P A R t i j

end SubexponentialSAT.SqrtLog.PackingIncidenceInput

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendConstants
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

@[simp] theorem scopeReset_stacks (a : Data) : (scopeReset a).stacks = a.stacks := by
  rfl

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete source masters and reusable empty workspace at each marked
query boundary. The frontend's hypotheses follow after the paid reference
staging program; no serialized scope or arithmetic cache is an input. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

def CleanWork (a : Data) : Prop :=
  ∀i,¬Protected i → i≠321 → a.stacks i=[]

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputAddressedProvenance
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Lookup and label provenance for the actual ambient-offset plan records.
The lemmas apply to any exact list lookup, including the first matching plan. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput
open SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes PackingCallerProgram

@[simp] theorem addressedPacking_head (p : Problem) (a : Word p.r p.Q)
    (tail : List (Word p.r p.Q)) (i : Fin (addressedEntries p.scopes p.n p.mask).length) :
    ((addressedPacking p.scopes p.n p.mask (ProducedQueryRank.packing p a tail)).label i).head =
      ProducedQueryRank.words p a tail
        (.inl (ProducedQueryRank.owner p (addressedIndex p.scopes p.n p.mask i))) := by
  rw [addressedPacking_label]
  rfl

@[simp] theorem addressedPacking_slot (p : Problem) (a : Word p.r p.Q)
    (tail : List (Word p.r p.Q)) (i : Fin (addressedEntries p.scopes p.n p.mask).length) :
    ((addressedPacking p.scopes p.n p.mask (ProducedQueryRank.packing p a tail)).label i).slot 0 =
      ProducedQueryRank.words p a tail
        (.inr (ProducedQueryRank.factor p (addressedIndex p.scopes p.n p.mask i))) := by
  rw [addressedPacking_label]
  rfl

end SubexponentialSAT.SqrtLog.PackingIncidenceInput

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteQueryPlan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Head coherence, low-owner support, and factor colors for the exact
addressed query plan stream. No semantic plan relation is supplied. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open PackingCallerProgram PackingIncidenceInput

variable (p : Problem)

def planColor (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) (t : Fin p.Q) (f : ℕ) : Fin p.r :=
  if hf:f < p.factors then ProducedQueryRank.words p a tail (.inr ⟨f,hf⟩) t else ⟨0,p.hr⟩

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramPreparedBranchCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact original-coordinate interpretation of the physical high tuple.
The order is descending original ID, and every rank including the unique
empty tuple participates in the count. No coordinate compaction is used. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount
open HighIncidenceProgram
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

def rankValue (H : Finset (Fin n)) (hashes : List (SparseRow (Fin n) (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (r : ℕ) : ℕ :=
  if hr:r < 2^H.card then NodeSemantics.ternaryFixedHighCount H
    (Rank.highEquiv (Order.highOrder H) ⟨r,hr⟩) hashes marked clause else 0

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/- Component: LeafRingSetupProgramScalar.lean -/

/-! The first concrete stage of ring setup.  Only the runtime binary
precision is supplied.  The generated scalar cache remains exposed while
the extension-ring table and constants are built.  The idempotent producer
later uses a separately framed preparation, with its own charged cost. -/

/-! Actual irreducible search followed by coefficient padding.  The model
below is the one selected by the finite search, not a supplied polynomial. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpLiftRing


abbrev paddingCall : Cmd 32 640 :=
  liftCommand RingCoefficientLiftProgram.searchCommand 13 21
    (registers 22 (by decide)) search

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

/- Component: LeafRingSetupProgramTable.lean -/

/-! Table generation for the cache produced by the native scalar stage.
The cache is not replaced by a separately chosen mathematical cache. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open RingProgramTable

abbrev tableCall : Cmd 32 640 :=
  .call (ProgramLinking.liftProgram RingProgramTable.Machine.program
    (registers 8 (by decide)) table)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

/- Component: LeafRingSetupProgramNodes.lean -/

/-! Physical node generation and record framing at the ring-setup ports. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

open BitProgram StructuredCalls SubexpLiftRing

abbrev nodesCall : Cmd 32 640 :=
  .call (ProgramLinking.liftProgram RingNodeProgram.preparedProgram
    (registers 8 (by decide)) nodes)

abbrev nodeFramesCall : Cmd 32 640 :=
  .call (ProgramLinking.liftProgram SubexpTaylorFrames.program
    (registers 5 (by decide)) nodeFramePorts)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

/- Component: LeafRingSetupProgramConstants.lean -/

/-! Actual constant-vector and idempotent calls in the setup workspace. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing

abbrev constantCall (out : Fin 640) : Cmd 32 640 :=
  .call (ProgramLinking.liftProgram LeafProgram.Constants.program
    (registers 8 (by decide)) (constant out))

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

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
open BitProgram StructuredCalls SubexpQuarticRing StackRoutines

/-- The seed is copied from a retained scalar master before the actual
literal-vector constructor consumes it. -/
abbrev buildConstant (src out : Fin 640) : Cmd 32 640 :=
  .seq (overwrite src 538) (constantCall out)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpQuarticRing

/-- Generate the three dynamic-dimension constant vectors on their native
consumer ports.  Each scalar master remains available throughout. -/
abbrev constantBatch : Cmd 32 640 :=
  .seq (buildConstant 498 207) (.seq (buildConstant 508 211) (buildConstant 203 280))

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls StackRoutines

def copied (p : Fin 640 × Fin 640) (a : Data) : Data :=
  ⟨readRegs a.regs 30 31 none,Function.update a.stacks p.2 (a.stacks p.1)⟩

def copiedPlan : List (Fin 640 × Fin 640) → Data → Data
  | [],a => a
  | p::ps,a => copiedPlan ps (copied p a)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Paid staging of the native interpolation-cache producer in the wide
leaf machine. The private 320-tape bank is disjoint from all ring and
collector masters. Native table computation is followed by paid extraction
of all five outputs; the entire staging bank is then cleared. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation
open BitProgram StructuredCalls StackRoutines SubexpLiftRing SubexpQuarticRing
abbrev Data := StructuredProgram.State 40 768

abbrev clear (dst : Fin 768) : Cmd 40 768 :=
  .call (clearProgram dst 38 39)

abbrev copy (src dst : Fin 768) : Cmd 40 768 :=
  .call (copyProgram src dst 699 38 39)

theorem clear_eval (dst : Fin 768) (a : Data) :
    Eval (clear dst) (2*(a.stacks dst).length+3) a
      ⟨readRegs a.regs 38 39 none, Function.update a.stacks dst []⟩ :=
  Subexp.TupleProgram.clear_eval dst 38 39 a

abbrev overwrite (src dst : Fin 768) : Cmd 40 768 :=
  .seq (clear dst) (copy src dst)


def clearPorts : List (Fin 768) → Cmd 40 768
  | [] => .base .skip
  | p :: ps => .seq (clear p) (clearPorts ps)

def clearResult (a : Data) (p : Fin 768) : Data :=
  ⟨readRegs a.regs 38 39 none, Function.update a.stacks p []⟩

def clearedPorts : List (Fin 768) → Data → Data
  | [], a => a
  | p :: ps, a => clearedPorts ps (clearResult a p)

def clearPortsCost : List (Fin 768) → Data → ℕ
  | [], _ => 0
  | p :: ps, a => 2*(a.stacks p).length+3+clearPortsCost ps (clearResult a p)

theorem clearPorts_eval (ps : List (Fin 768)) (a : Data) :
    Eval (clearPorts ps) (clearPortsCost ps a) a (clearedPorts ps a) := by
  induction ps generalizing a with
  | nil => exact .base (.skip _)
  | cons p ps ih => exact (clear_eval p a).seq (ih _)

theorem clearedPorts_stacks (ps : List (Fin 768)) (a : Data) (i : Fin 768) :
    (clearedPorts ps a).stacks i = if i ∈ ps then [] else a.stacks i := by
  induction ps generalizing a with
  | nil => simp [clearedPorts]
  | cons p ps ih =>
    simp only [clearedPorts, ih, List.mem_cons, clearResult]
    by_cases hi : i=p
    · subst i
      simp
    · by_cases hm : i ∈ ps <;> simp [hi,hm]

theorem clearPortsCost_bound (ps : List (Fin 768)) (a : Data) (W : ℕ)
    (hw : ∀ p ∈ ps, (a.stacks p).length ≤ W) :
    clearPortsCost ps a ≤ ps.length*(2*W+3) := by
  induction ps generalizing a with
  | nil => simp [clearPortsCost]
  | cons p ps ih =>
    have hp := hw p (by simp)
    have htail : ∀ q ∈ ps, ((clearResult a p).stacks q).length ≤ W := by
      intro q hq
      by_cases h : q=p
      · simp [clearResult,h]
      · simpa [clearResult,h] using hw q (by simp [hq])
    have ht := ih (clearResult a p) htail
    simp only [clearPortsCost, List.length_cons]
    nlinarith


def copyPlan : List (Fin 768 × Fin 768) → Cmd 40 768
  | [] => .base .skip
  | p::ps => .seq (overwrite p.1 p.2) (copyPlan ps)

def copied (p : Fin 768 × Fin 768) (a : Data) : Data :=
  ⟨readRegs a.regs 38 39 none,Function.update a.stacks p.2 (a.stacks p.1)⟩

def copiedPlan : List (Fin 768 × Fin 768) → Data → Data
  | [],a => a
  | p::ps,a => copiedPlan ps (copied p a)

def copyPlanCost : List (Fin 768 × Fin 768) → Data → ℕ
  | [],_ => 0
  | p::ps,a => 2*(a.stacks p.2).length+7*(a.stacks p.1).length+8+
      copyPlanCost ps (copied p a)

theorem cleared_width (ps : List (Fin 768)) (a : Data) (W : ℕ)
    (hw : ∀i,(a.stacks i).length ≤ W) :
    ∀i,((clearedPorts ps a).stacks i).length ≤ W := by
  intro i; rw [clearedPorts_stacks]; split_ifs <;> simp_all

theorem cleared_register_frame (ps : List (Fin 768)) (a : Data)
    (i : Fin 40) (h38 : i≠38) (h39 : i≠39) :
    (clearedPorts ps a).regs i=a.regs i := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rw [clearedPorts,ih]
    simp [clearResult,readRegs,h38,h39]

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation

end OAI.Algorithms
end


