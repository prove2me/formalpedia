-- Prove2me | Definitions.Def_OAIQ081S128
-- name    : OAIQ081S128
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:40:02.926917+00:00
-- url     : https://prove2.me/theorems/ca121982-c719-4372-90e6-f6c5c2aacc9d
-- title:
--   Definitions bundle OAIQ081S128 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 44 declarations of OpenAI's Lean: 11 definitions, 2 inductive types or structures and 31 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.CoreInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.LowFrame.EmptyPreserved`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.constantStore`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.tableInputStore`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.callback`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.extend`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.TailCorrect`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.allPowerBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.initialData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.initialStore`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.literalLastWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.Code`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_HeadSumProgram`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramConstantBridge`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramLowFrame`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramTableBridge`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramArity`, `SubexponentialSAT_SqrtLog_MomentsProgramNormalize`, `SubexponentialSAT_SqrtLog_RingCoefficientLiftProgram`, `SubexponentialSAT_SqrtLog_RingProgramTableBridge`, `SubexponentialSAT_SqrtLog_RingProgramTableInitial`, `SubexponentialSAT_SqrtLog_RingProgramTableMachine`, `SubexponentialSAT_SqrtLog_RingProgramTableSemantics`, `SubexponentialSAT_SqrtLog_RingProgramTableSetup`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgram`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramBridge`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramOuter`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S100`, `OAIQ081S101`, `OAIQ081S102`, `OAIQ081S103`, `OAIQ081S104`, `OAIQ081S109` and `OAIQ081S110` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S145`, `OAIQ081S146` and `OAIQ081S151`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S100
import Definitions.Def_OAIQ081S101
import Definitions.Def_OAIQ081S102
import Definitions.Def_OAIQ081S103
import Definitions.Def_OAIQ081S104
import Definitions.Def_OAIQ081S109
import Definitions.Def_OAIQ081S110

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramNormalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms



namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def extend (d : Dictionary.Data) (source : List Bool) : Data :=
  ⟨d.regs,Fin.snoc d.stacks source⟩

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


end OAI.Algorithms
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

abbrev Code := Cmd 40 896


open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing TruncatedRingProgram


open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableInitial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

def literalLastWord {B : ℕ} : ℕ → Word B → Word B → Word B → Word B
  | 0, _, _, old => old
  | n+1, seed, zeroWord, _ => literalLastWord n zeroWord zeroWord seed

def initialData {B : ℕ} (d : ℕ) (oneWord zeroWord : Word B) : VectorData B d :=
  { coefficients := ⟨literalWords d oneWord zeroWord, literalWords_length d oneWord zeroWord⟩
    last := literalLastWord d oneWord zeroWord zeroWord }

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingCoefficientLiftProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! A fixed scanner widens consecutive two-bit coefficients using a runtime
width tape. The original width is preserved, and all bit movement is paid. -/


/-! Exact byte bridge from canonical F3 coefficients to the supplied-polynomial
ring model. The program itself has no degree or width parameter. -/
namespace SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.ModularArithmetic

 theorem pad_coefficient (t : ℕ) (ht : 0 < t) (a : ZMod 3) (width : List Bool)
    (hw : width.length=baseWidth 3 t) :
    padTo width (IrreducibleSearchProgram.coefficientWord a)=
      (RingProgram.liftCoefficientRun t a).1.val := by
  apply SubexponentialSAT.SubexpModulusConstruction.bits_eq_of_length_of_value
  · rw [padTo_length, hw]
    exact (RingProgram.liftCoefficientRun t a).1.property.symm
  · rw [ModularRingPrograms.padTo_value_of_lt,RingProgram.liftCoefficientRun_value t ht]
    · exact SubexpEnumerationPayload.scalarBits_value a
    · change BinaryArithmetic.toNat (SubexpEnumerationPayload.scalarBits a) < 2^width.length
      rw [SubexpEnumerationPayload.scalarBits_value,hw,RingProgram.ternary_baseWidth]
      have hp := Nat.pow_le_pow_right (show 1 ≤ 2 by omega) (show 2 ≤ 2*t by omega)
      have ha := a.val_lt
      norm_num at hp
      omega

theorem padded_coefficients (t : ℕ) (ht : 0 < t) (as : List (ZMod 3)) (width : List Bool)
    (hw : width.length=baseWidth 3 t) :
    padded width (as.map IrreducibleSearchProgram.coefficientWord)=
      (as.map (fun a => (RingProgram.liftCoefficientRun t a).1.val)).flatten := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [padded_cons, List.map_cons, List.flatten_cons, pad_coefficient t ht a width hw, ih]

theorem padded_ofFn (t : ℕ) (ht : 0 < t) {d : ℕ} (as : Fin d → ZMod 3)
    (width : List Bool) (hw : width.length=baseWidth 3 t) :
    padded width ((List.ofFn as).map IrreducibleSearchProgram.coefficientWord)=
      RingProgram.flat (RingProgram.liftCoefficientsRun t as).1 := by
  rw [padded_coefficients t ht _ width hw]
  simp only [RingProgram.flat,RingProgram.liftCoefficientsRun,RingProgram.tabulateRun_eq,
    List.map_ofFn]
  rfl

theorem coefficients_eval (t : ℕ) (ht : 0 < t) {d : ℕ} (as : Fin d → ZMod 3)
    (width : List Bool) (hw : width.length=baseWidth 3 t) (regs : Fin 8 → Bool) :
    ∃ rf, Eval command (d*(28*t+14)+5)
      (state regs (IrreducibleSearchProgram.coefficientArray (List.ofFn as)) width [] [] [] [] [])
      (state rf [] width [] [] [] [] (RingProgram.flat (RingProgram.liftCoefficientsRun t as).1)) := by
  have hw2 : 2 ≤ width.length := by rw [hw,RingProgram.ternary_baseWidth]; omega
  obtain ⟨rf,h⟩ := command_eval ((List.ofFn as).map IrreducibleSearchProgram.coefficientWord)
    width (by intro w hw; obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
              exact IrreducibleSearchProgram.coefficientWord_length a) hw2 regs
  rw [padded_ofFn t ht as width hw] at h
  have hc : ((List.ofFn as).map IrreducibleSearchProgram.coefficientWord).length*
      (14*width.length+14)+5=d*(28*t+14)+5 := by
    simp only [List.length_map,List.length_ofFn,hw,RingProgram.ternary_baseWidth]
    ring
  rw [hc] at h
  exact ⟨rf,by simpa only [IrreducibleSearchProgram.coefficientArray_flatten] using h⟩

end SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram


/-! Search-to-table ABI. The search has 22 registers and 28 stacks. In particular,
stack24 may contain unread candidates and is outside this adapter's ports. -/
namespace SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- The polynomial input appears on21, source13 is consumed, and all other
stacks (including the runtime width12, degree14, counts22 and candidates24)
are preserved. The exact result is the ring model's coefficient code. -/
theorem searchCommand_eval (t : ℕ) (ht : 0 < t) {d : ℕ} (as : Fin d → ZMod 3)
    (s : SearchData) (hready : SearchReady s)
    (hinput : s.stacks 13=IrreducibleSearchProgram.coefficientArray (List.ofFn as))
    (hwidth : (s.stacks 12).length=SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ e, Eval searchCommand (d*(28*t+14)+6) s e ∧
      e.stacks=Function.update (Function.update s.stacks 13 []) 21
        (RingProgram.flat (RingProgram.liftCoefficientsRun t as).1) ∧
      (∀ i, i ∉ Set.range searchRegisters → e.regs i=s.regs i) := by
  obtain ⟨h23,h15,h25,h26,h21⟩ := hready
  let a := projectState searchRegisters searchPorts s
  have ha : a=state a.regs (IrreducibleSearchProgram.coefficientArray (List.ofFn as))
      (s.stacks 12) [] [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [searchPorts,tapes,hinput,h23,h15,h25,h26,h21]
  obtain ⟨rf,h⟩ := coefficients_eval t ht as (s.stacks 12) hwidth a.regs
  rw [←ha] at h
  let b := state rf [] (s.stacks 12) [] [] [] []
    (RingProgram.flat (RingProgram.liftCoefficientsRun t as).1)
  let e := embedState searchRegisters searchPorts s b
  have he := eval_liftCommand_from_state command 0 6 searchRegisters searchPorts s
    searchRegisters_injective searchPorts_injective h
  have hb : b.stacks=Function.update (Function.update a.stacks 0 []) 6
      (RingProgram.flat (RingProgram.liftCoefficientsRun t as).1) := by
    rw [ha]
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  refine ⟨e,?_,?_,?_⟩
  · simpa [searchCommand,Nat.add_assoc] using he
  · change Function.extend searchPorts b.stacks s.stacks=_
    rw [hb,ProgramLinking.extend_update searchPorts_injective,
      ProgramLinking.extend_update searchPorts_injective]
    have hbase := congrArg StructuredProgram.State.stacks
      (embedState_project searchRegisters searchPorts s searchRegisters_injective searchPorts_injective)
    change Function.extend searchPorts a.stacks s.stacks=s.stacks at hbase
    rw [hbase]
    rfl
  · intro i hi
    exact embedState_register_frame searchRegisters searchPorts s b i hi

end SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def TailCorrect {B d : ℕ} (v : VectorData B d) : Prop :=
  v.coefficients.val.getLast? = some v.last

theorem literalWords_ofFn {B : ℕ} (n : ℕ) (oneWord zeroWord : Word B) :
    literalWords n oneWord zeroWord =
      List.ofFn (fun i : Fin n => if i.val = 0 then oneWord else zeroWord) := by
  induction n generalizing oneWord with
  | zero => rfl
  | succ n ih =>
    simp [literalWords, List.ofFn_succ, ih ]

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def initialStore {B d : ℕ} (s : Store) (c : List.Vector (Word B) d)
    (oneWord zeroWord minusOne : Word B) : Store :=
  {s with left := oneWord.val, source := [], saved := [], count := [], vector := [], coefficients := [], minusOne := minusOne.val, tail := [], newTail := [], output := [], polynomial := wordBits c.val, zero := zeroWord.val, powers := [], rounds := []}

def allPowerBits (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    {d : ℕ} (c : List.Vector (Word (baseWidth p t)) d)
    (oneWord zeroWord minusOne : Word (baseWidth p t)) : List Bool :=
  wordBits (initialData d oneWord zeroWord).coefficients.val ++
    generatedBits p t M zeroWord minusOne c (2*d-2) (initialData d oneWord zeroWord)

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramOuter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem kLoop_eval (rows : List (List Bool)) (s : Store) (regs : Fin 2 → Bool)
    (count : List Bool) (C : ℕ)
    (hp : s.powers = rows.flatten)
    (hw : ∀ row ∈ rows, row.length = s.width.length)
    (hword : s.word = []) (hindex : s.index = [])
    (hj : s.ji = []) (hcj : s.jc = []) (hi : s.ii = []) (hci : s.ic = [])
    (hcap : s.ki.length + count.length + 2*s.degree.length*s.degree.length ≤ C)
    (hv : ∀ k < count.length, ∀ i < s.degree.length, ∀ j < s.degree.length,
      s.ki.length+k+i*s.degree.length+j*s.degree.length < rows.length) :
    ∃ n ≤ count.length * (blockBudget s.width.length s.degree.length C + 2) + 1,
      ∃ rf idx, idx.length = s.ki.length + count.length ∧
      Eval kLoop n
        (state (readRegs regs 0 1 count.head?) {s with kc := count.tail})
        (state rf {s with
          kc := []
          ki := idx
          rev := (layoutBits rows s.degree.length s.ki.length count.length).reverse ++ s.rev}) := by
  induction count generalizing s regs with
  | nil =>
      refine ⟨1, by simp, readRegs regs 0 1 none, s.ki, by simp, ?_⟩
      simpa [layoutBits] using
        (Eval.while_false (body := .seq blockStep (pop 11))
          (a := state (readRegs regs 0 1 none) {s with kc := []})
          (by simp [state, readRegs_present]))
  | cons bit count ih =>
      let s1 : Store := {s with
        kc := count
        ki := false :: s.ki
        rev := (matrixBits rows s.degree.length s.ki.length s.degree.length).reverse ++ s.rev}
      have hcap0 : s.ki.length + 2*s.degree.length*s.degree.length ≤ C := by omega
      have hv0 : ∀ i < s.degree.length, ∀ j < s.degree.length,
          s.ki.length+i*s.degree.length+j*s.degree.length < rows.length := by
        intro i hi j hj
        simpa using hv 0 (by simp) i hi j hj
      obtain ⟨m, hm, r1, he⟩ := blockStep_eval rows {s with kc := count}
        (readRegs regs 0 1 (some bit)) C hp hw hword hindex hj hcj hi hci hcap0 hv0
      have he' : Eval blockStep m
          (state (readRegs regs 0 1 (some bit)) {s with kc := count}) (state r1 s1) := he
      have hr := kPop_eval s1 r1
      have hcap1 : s1.ki.length + count.length + 2*s1.degree.length*s1.degree.length ≤ C := by
        simpa [s1, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcap
      have hv1 : ∀ k < count.length, ∀ i < s1.degree.length, ∀ j < s1.degree.length,
          s1.ki.length+k+i*s1.degree.length+j*s1.degree.length < rows.length := by
        intro k hk i hi j hj
        have hh := hv (k+1) (by simpa using Nat.succ_lt_succ hk) i hi j hj
        simpa [s1, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
      obtain ⟨n, hn, rf, idx, hidx, hl⟩ := ih s1 r1 hp hw hword hindex hj hcj hi hci hcap1 hv1
      have ht := Eval.while_true
        (show (state (readRegs regs 0 1 (some bit)) {s with kc := count}).regs 1 = true by
          simp [state, readRegs_present]) (he'.seq hr) hl
      refine ⟨(m+1)+n+1, ?_, rf, idx, ?_, ?_⟩
      · simp only [s1, List.length_cons] at hm hn ⊢
        nlinarith
      · simp only [s1, List.length_cons] at hidx ⊢
        omega
      · simpa only [kLoop, s1, List.head?_cons, List.tail_cons, List.length_cons,
          layoutBits, List.reverse_append, List.append_assoc] using ht

theorem kScan_eval (rows : List (List Bool)) (s : Store) (regs : Fin 2 → Bool) (C : ℕ)
    (hp : s.powers = rows.flatten)
    (hw : ∀ row ∈ rows, row.length = s.width.length)
    (hword : s.word = []) (hindex : s.index = [])
    (hj : s.ji = []) (hcj : s.jc = []) (hi : s.ii = []) (hci : s.ic = [])
    (hcap : s.ki.length+s.kc.length+2*s.degree.length*s.degree.length ≤ C)
    (hv : ∀ k < s.kc.length, ∀ i < s.degree.length, ∀ j < s.degree.length,
      s.ki.length+k+i*s.degree.length+j*s.degree.length < rows.length) :
    ∃ n ≤ s.kc.length * (blockBudget s.width.length s.degree.length C + 2) + 2,
      ∃ rf idx, idx.length = s.ki.length+s.kc.length ∧
      Eval kScan n (state regs s)
        (state rf {s with
          kc := []
          ki := idx
          rev := (layoutBits rows s.degree.length s.ki.length s.kc.length).reverse ++ s.rev}) := by
  obtain ⟨n, hn, rf, idx, hidx, he⟩ :=
    kLoop_eval rows s regs s.kc C hp hw hword hindex hj hcj hi hci hcap hv
  exact ⟨1+n, by omega, rf, idx, hidx, (kPop_eval s regs).seq he⟩

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A uniform finite program transforming power-major scalar records into the
k-major multiplication table. No dimension changes its finite control. -/
namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem command_eval (rows : List (List Bool)) (degree width : List Bool) (regs : Fin 2 → Bool)
    (hw : ∀ row ∈ rows, row.length = width.length)
    (hn : degree.length*(2*degree.length-1) ≤ rows.length) :
    ∃ n ≤ budget degree.length width.length, ∃ rf,
      Eval command n (state regs (initial rows.flatten degree width))
        (state rf {(initial rows.flatten degree width) with
          out := layoutBits rows degree.length 0 degree.length}) := by
  obtain ⟨r1, h1⟩ := initialize_eval rows.flatten degree width regs
  let s := {(initial rows.flatten degree width) with kc := degree}
  have hv : ∀ k < s.kc.length, ∀ i < s.degree.length, ∀ j < s.degree.length,
      s.ki.length+k+i*s.degree.length+j*s.degree.length < rows.length := by
    intro k hk i hi j hj
    simpa [s, initial] using (table_index_lt degree.length k i j hk hi hj).trans_le hn
  obtain ⟨n, hn', r2, idx, hidx, h2⟩ := kScan_eval rows s r1
    (2*degree.length*degree.length+degree.length) rfl hw rfl rfl rfl rfl rfl rfl
    (by simp [s ]; omega) hv
  let t := {(initial rows.flatten degree width) with
    ki := idx
    rev := (layoutBits rows degree.length 0 degree.length).reverse}
  have h2' : Eval kScan n (state r1 s) (state r2 t) := by
    simpa [s, t, initial] using h2
  obtain ⟨r3, h3⟩ := finish_eval t r2
  have hlen := full_layout_length rows degree.length width.length hw hn
  have hil : idx.length = degree.length := by simpa [s, initial] using hidx
  refine ⟨(7*degree.length+5)+(n+(2*idx.length+3*(layoutBits rows degree.length 0 degree.length).length+6)),
    ?_, r3, ?_⟩
  · simp only [s ] at hn'
    dsimp [budget]
    rw [hil, hlen]
    nlinarith
  · simpa only [command, s, t, initial, List.length_reverse,
      List.reverse_reverse, List.append_nil] using h1.seq (h2'.seq h3)

/-- A real halted finite-table trace, including the terminal instruction. -/
theorem program_run (rows : List (List Bool)) (degree width : List Bool) (regs : Fin 2 → Bool)
    (hw : ∀ row ∈ rows, row.length = width.length)
    (hn : degree.length*(2*degree.length-1) ≤ rows.length) :
    ∃ rf, RunsIn program (budget degree.length width.length + 1)
      ((state regs (initial rows.flatten degree width)).withPC (some program.entry))
      ((state rf {(initial rows.flatten degree width) with
        out := layoutBits rows degree.length 0 degree.length}).withPC none) := by
  obtain ⟨n, hn', rf, he⟩ := command_eval rows degree width regs hw hn
  exact ⟨rf, n+1, by omega, compiled_halt_trace he 0 3⟩

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramBridge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.SubexpQuarticRing

theorem powerRecords_width {d B : ℕ} (P : ℕ → Fin d → Word B) (n : ℕ) :
    ∀ row ∈ powerRecords P n, row.length = B := by
  intro row hr
  rw [powerRecords_eq_ofFn] at hr
  obtain ⟨x, rfl⟩ := List.mem_ofFn.mp hr
  exact (P x.divNat.val x.modNat).property

theorem powerRecords_lookup {d B n : ℕ} (P : ℕ → Fin d → Word B)
    (a : Fin n) (k : Fin d) :
    wordAt (powerRecords P n) (a.val*d+k.val) = (P a.val k).val := by
  have hb : a.val*d+k.val < n*d := by nlinarith [a.isLt, k.isLt]
  have hd : 0 < d := (Nat.zero_le k.val).trans_lt k.isLt
  have hdiv : (a.val*d+k.val)/d = a.val := by
    rw [Nat.mul_comm a.val d, Nat.mul_add_div hd, Nat.div_eq_of_lt k.isLt]
    omega
  have hmod : (a.val*d+k.val)%d = k.val := by simp [Nat.mod_eq_of_lt k.isLt]
  simp only [wordAt, powerRecords_eq_ofFn, getElem!_pos, List.length_ofFn, hb,
    List.getElem_ofFn, Fin.divNat, Fin.modNat, hdiv]
  have hk : (⟨(a.val*d+k.val)%d, by omega⟩ : Fin d) = k := Fin.ext hmod
  simp only [hk]

theorem power_layout_eq_tableEncoding {d B : ℕ} (P : ℕ → Fin d → Word B) :
    layoutBits (powerRecords P (2*d-1)) d 0 d =
      RingTriple.tableEncoding (fun i j k => P (i.val+j.val) k) := by
  rw [layoutBits_eq_ofFn, RingTriple.tableEncoding]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext k
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  have ha : i.val+j.val < 2*d-1 := by omega
  have hidx : 0+k.val+i.val*d+j.val*d = (i.val+j.val)*d+k.val := by ring
  rw [hidx]
  exact powerRecords_lookup P ⟨i.val+j.val, ha⟩ k

/-- The consumer ABI is exactly RingTriple.tableEncoding, including every
zero coefficient and the k-major/i-next/j-fastest ordering. -/
theorem power_table_program_run {d B : ℕ} (P : ℕ → Fin d → Word B)
    (degree width : List Bool) (regs : Fin 2 → Bool)
    (hd : degree.length = d) (hw : width.length = B) :
    ∃ rf, RunsIn program (budget d B + 1)
      ((state regs (initial (powerRecords P (2*d-1)).flatten degree width)).withPC
        (some program.entry))
      ((state rf {(initial (powerRecords P (2*d-1)).flatten degree width) with
        out := RingTriple.tableEncoding (fun i j k => P (i.val+j.val) k)}).withPC none) := by
  have h := program_run (powerRecords P (2*d-1)) degree width regs
    (by simpa only [hw] using powerRecords_width P (2*d-1))
    (by simp [hd, Nat.mul_comm])
  simpa only [hd, hw, power_layout_eq_tableEncoding] using h

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableBridge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem vectorRecords_flat {B d : ℕ} (v : List.Vector (Word B) d) :
    (List.ofFn (fun i => (v.get i).val)).flatten = wordBits v.val := by
  change (List.ofFn ((Subtype.val : Word B → List Bool) ∘ v.get)).flatten = _
  rw [← List.map_ofFn, listOfFn_get]
  rfl

theorem powerRecords_succ {B d : ℕ} (P : ℕ → Fin d → Word B) (n : ℕ) :
    RingTableLayout.powerRecords P (n+1) =
      List.ofFn (fun i => (P 0 i).val) ++ RingTableLayout.powerRecords (fun j => P (j+1)) n := by
  simp only [RingTableLayout.powerRecords, List.ofFn_succ, List.flatten_cons, Fin.val_zero,
    Fin.val_succ]

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableMachine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable.Machine

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem layout_eval {B d : ℕ} (P : ℕ → Fin d → Word B)
    (s : Store) (regs : Fin 8 → Bool)
    (hp : s.powers = (RingTableLayout.powerRecords P (2*d-1)).flatten)
    (hd : s.degree.length = d) (hw : s.width.length = B) :
    ∃ n ≤ RingTableLayout.budget d B+1, ∃ rf, Eval layout n
      (state regs s [])
      (state rf s (RingTriple.tableEncoding (fun i j k => P (i.val+j.val) k))) := by
  obtain ⟨lr,n,hn,ht⟩ := RingTableLayout.power_table_program_run P s.degree s.width ![regs 1,regs 3] hd hw
  rw [← hp] at ht
  have he := eval_call_lifted RingTableLayout.program layoutRegisters layoutPorts
    (state regs s []) layoutRegisters_injective layoutPorts_injective ht
  have hi : embedState layoutRegisters layoutPorts (state regs s [])
      (RingTableLayout.state ![regs 1,regs 3]
        (RingTableLayout.initial s.powers s.degree s.width)) = state regs s [] := by
    simpa only [combineRegs_self] using embed_layout regs ![regs 1,regs 3] s [] []
  rw [hi] at he
  refine ⟨n,hn,combineRegs regs lr,?_⟩
  have hout := embed_layout regs lr s []
    (RingTriple.tableEncoding (fun i j k => P (i.val+j.val) k))
  rw [hout] at he
  simpa only [layout] using he

end SubexponentialSAT.SqrtLog.RingProgramTable.Machine

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramConstantBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpQuarticRing

/-- Reconstruct only the unconstrained fields of the constant generator's
local store.  Its service-owned scratch is checked separately below. -/
def constantStore (out : Fin 640) (a : Data) : RingProgramTable.Store where
  modulus := a.stacks (constant out 5)
  left := a.stacks 538
  source := a.stacks (constant out 9)
  saved := a.stacks (constant out 10)
  width := a.stacks (constant out 12)
  coefficients := a.stacks (constant out 16)
  minusOne := a.stacks (constant out 17)
  tail := a.stacks (constant out 18)
  polynomial := a.stacks (constant out 21)
  degree := a.stacks 204
  zero := a.stacks 203
  powers := a.stacks (constant out 25)
  rounds := a.stacks (constant out 26)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramTableBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical table-input projection and the exact native table-call bridge. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing RingProgramTable

def tableInputStore (a : LeafRingSetupProgram.Data) : Store where
  modulus := a.stacks 194
  width := a.stacks 202
  minusOne := a.stacks 508
  tail := []
  polynomial := a.stacks 441
  degree := a.stacks 204
  zero := a.stacks 203


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
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing StackRoutines

/-- These are input tape conditions, not supplied mathematical ring data.
The only numerical words needed by this phase are binary precision and
unary dimension.  The outer setup establishes the empty tapes by clearing. -/
structure CoreInput (bits depth : List Bool) (a : Data) : Prop where
  scalarInput : projectState (registers 8 (by decide)) scalar a =
    IdempotentPreparationProgram.inputData bits
  degree : a.stacks 204=depth
  searchClean : ∀ j : Fin 28, j≠14 → a.stacks (search j)=[]
  tableClean : ∀ j : Fin 42, j∉([5,12,17,21,22,24] : List (Fin 42)) →
    a.stacks (LeafRingSetupProgram.table j)=[]
  halfEmpty : a.stacks 253=[]
  copyEmpty : a.stacks 639=[]

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpQuarticRing SubexpLiftRing

/-- A bound on actual tape lengths follows from the compiled instruction
trace; it is not a cost annotation on an abstract computation. -/
theorem eval_stack_length_le {c : Cmd 32 640} {n : ℕ} {a e : Data}
    (he : Eval c n a e) (i : Fin 640) :
    (e.stacks i).length ≤ (a.stacks i).length+n+1 := by
  have h := Subexp.SequentialProgram.trace_stack_length_le
    (compiled_halt_trace he 0 0) i
  simpa only [StructuredProgram.State.withPC,Nat.add_assoc] using h

theorem eval_width_le {c : Cmd 32 640} {n W : ℕ} {a e : Data}
    (he : Eval c n a e) (hw : ∀ i,(a.stacks i).length ≤ W) :
    ∀ i,(e.stacks i).length ≤ W+n+1 := by
  intro i
  have hwi := hw i
  exact (eval_stack_length_le he i).trans (by omega)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramLowFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The ring producer can clear low arithmetic workspace, but never inserts
data there.  Thus initially blank low node-work tapes stay blank.  This is a
property of the existing program, not an additional cleanup operation. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.LowFrame
open BitProgram StructuredCalls

structure EmptyPreserved {r s : ℕ} (c : Cmd r s) (i : Fin s) : Prop where
  run : ∀ {n : ℕ} {a b : State r s}, Eval c n a b → a.stacks i=[] → b.stacks i=[]

theorem seq {r s : ℕ} {c d : Cmd r s} {i : Fin s}
    (hc : EmptyPreserved c i) (hd : EmptyPreserved d i) :
    EmptyPreserved (.seq c d) i := by
  constructor
  intro n a b h hz
  cases h with
  | seq h1 h2 => exact hd.run h2 (hc.run h1 hz)

theorem skip {r s : ℕ} (i : Fin s) : EmptyPreserved (.base (.skip : StructuredProgram.Cmd r s)) i := by
  constructor
  intro n a b h hz
  cases h with
  | base h => cases h; exact hz

theorem call {r s l : ℕ} (p : Program r s l) (i : Fin s)
    (hp : ∀ q c, c.stacks i=[] → (execInstr (p.code q) c).stacks i=[]) :
    EmptyPreserved (.call p) i := by
  constructor
  intro n a b h hz
  cases h with
  | call _ ht => exact trace_empty p i hp ht hz

theorem lifted {r s R S l : ℕ} (p : Program r s l)
    (reg : Fin r → Fin R) (stk : Fin s → Fin S) (i : Fin S)
    (hi : ∀ j, i≠stk j) :
    EmptyPreserved (.call (ProgramLinking.liftProgram p reg stk)) i := by
  apply call
  intro q c hz
  change (execInstr (ProgramLinking.relocateInstr reg stk id none (p.code q)) c).stacks i=[]
  cases p.code q <;> simp [ProgramLinking.relocateInstr,execInstr,hi,hz]

theorem highLift {r s l : ℕ} (p : Program r s l)
    (reg : Fin r → Fin 32) (stk : Fin s → Fin 640) (i : Fin 640)
    (hi : i.val < 190) (hs : ∀ j,190 ≤ (stk j).val) :
    EmptyPreserved (.call (ProgramLinking.liftProgram p reg stk)) i := by
  apply lifted
  intro j he
  have hv := congrArg Fin.val he
  have := hs j
  omega

theorem clear (dst i : Fin 640) : EmptyPreserved (LeafRingSetupProgram.clear dst) i := by
  apply call
  intro q c hz
  by_cases he : i=dst
  · subst i
    fin_cases q <;> simp [execInstr,hz]
  · fin_cases q <;> simp [execInstr,hz,he]

theorem copy (src dst i : Fin 640) (hi : i.val < 190)
    (hs : 190 ≤ src.val) (hd : 190 ≤ dst.val) :
    EmptyPreserved (LeafRingSetupProgram.copy src dst) i := by
  have hsrc : i≠src := by intro h; subst i; omega
  have hdst : i≠dst := by intro h; subst i; omega
  have htmp : i≠639 := by intro h; subst i; change (639:ℕ) < 190 at hi; omega
  apply call
  intro q c hz
  fin_cases q <;> simp [execInstr,hz,hsrc,hdst,htmp]

theorem overwrite (src dst i : Fin 640) (hi : i.val < 190)
    (hs : 190 ≤ src.val) (hd : 190 ≤ dst.val) :
    EmptyPreserved (LeafRingSetupProgram.overwrite src dst) i :=
  seq (clear dst i) (copy src dst i hi hs hd)

theorem clearPorts (ps : List (Fin 640)) (i : Fin 640) :
    EmptyPreserved (LeafRingSetupProgram.clearPorts ps) i := by
  induction ps with
  | nil => exact skip i
  | cons p ps ih => exact seq (clear p i) ih

theorem reset {r s : ℕ} (ps : List (Fin r)) (i : Fin s) :
    EmptyPreserved (RegisterResetProgram.clear ps) i := by
  induction ps with
  | nil => exact skip i
  | cons p ps ih =>
    unfold RegisterResetProgram.clear
    apply seq _ ih
    constructor
    intro n a b h hz
    cases h with
    | base h => cases h; exact hz

theorem resetAll (i : Fin 640) : EmptyPreserved (RegisterResetProgram.all : Cmd 32 640) i :=
  reset _ i

theorem unary (src dst i : Fin 640) (hi : i.val < 190)
    (hs : 190 ≤ src.val) (hd : 190 ≤ dst.val) :
    EmptyPreserved (LeafRingSetupProgram.unary src dst) i := by
  apply highLift _ _ _ i hi
  intro j
  unfold unaryPorts
  split_ifs <;> (try dsimp only) <;> omega

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.LowFrame

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramArity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime outer record fold computing the maximum masked scope length and
factor count, including empty scope records. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
def callback : Code := .seq transfer (.seq prepare (.seq scopeCall (.seq maxCall increment)))

def program := LeafProgram.foldProgram ports callback

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity

end OAI.Algorithms
end


