-- Prove2me | Definitions.Def_OAIQ081S087
-- name    : OAIQ081S087
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:10:17.291348+00:00
-- url     : https://prove2.me/theorems/b01f933e-0b4e-474e-8937-a4042f876ce4
-- title:
--   Definitions bundle OAIQ081S087 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 8 definitions and 12 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.NativeInstructionSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.nativeCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.nativeNewtonLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl.factorTest`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPrepareCount.state`, `OAI.Algorithms.SubexponentialSAT.SubexpOrderedTupleStep.reverseRecords`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLog_IdempotentProgramNative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentProgramNative.lean), [`SubexponentialSAT_SqrtLog_IdempotentTableEntryProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentTableEntryProgram.lean), [`SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramFrame`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentTableEntryProgramFrame.lean), [`SubexponentialSAT_SqrtLog_InterpolationCacheProgramBasic`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/InterpolationCacheProgramBasic.lean), [`SubexponentialSAT_SqrtLog_InterpolationCacheProgramCost`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/InterpolationCacheProgramCost.lean), [`SubexponentialSAT_SqrtLog_IrreducibleSearch`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IrreducibleSearch.lean), [`SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IrreducibleSearchNativeScan.lean), [`SubexponentialSAT_SqrtLog_IrreducibleSearchProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IrreducibleSearchProgram.lean), [`SubexponentialSAT_SqrtLog_LayoutFiberSumProgramBasic`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutFiberSumProgramBasic.lean), [`SubexponentialSAT_SqrtLog_PackingHeadProgramPrepareCount`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingHeadProgramPrepareCount.lean), [`SubexponentialSAT_SubexpOrderedTupleStep`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SubexpOrderedTupleStep.lean).
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S066`, `OAIQ081S067`, `OAIQ081S069`, `OAIQ081S070` and `OAIQ081S071` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S104`, `OAIQ081S105`, `OAIQ081S106` and `OAIQ081S108`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S066
import Definitions.Def_OAIQ081S067
import Definitions.Def_OAIQ081S069
import Definitions.Def_OAIQ081S070
import Definitions.Def_OAIQ081S071

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native Newton control, conditional only on explicitly supplied native
array-operation services. Each service hypothesis requires a real `Eval` of a
fixed finite command. The iteration count is stack data, not generated control.
This module does not claim that the array-service obligations are discharged. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost
open SubexponentialSAT.StructuredCalls

variable {C A : Type*} [CommRing A] {r s : ℕ}

def nativeCode (service : ArithmeticInstruction → Cmd r s) :
    List ArithmeticInstruction → Cmd r s
  | [] => .base .skip
  | i::is => .seq (service i) (nativeCode service is)

def NativeInstructionSpec (ops : RingProgram C)
    (p : CounterForPrograms.Ports r s)
    (service : ArithmeticInstruction → Cmd r s)
    (enc : Registers C → State r s → Prop) (bound : ℕ) : Prop :=
  ∀ i regs d, enc regs d → d.stacks p.scratch = [] →
    ∃ n e, n ≤ bound ∧ Eval (service i) n d e ∧
      enc (instructionRun ops i regs).1 e ∧
      e.stacks p.counter = d.stacks p.counter ∧ e.stacks p.scratch = []

theorem nativeCode_correct (ops : RingProgram C)
    (p : CounterForPrograms.Ports r s)
    (service : ArithmeticInstruction → Cmd r s)
    (enc : Registers C → State r s → Prop) (bound : ℕ)
    (spec : NativeInstructionSpec ops p service enc bound)
    (code : List ArithmeticInstruction) (regs : Registers C) (d : State r s)
    (hd : enc regs d) (hs : d.stacks p.scratch = []) :
    ∃ n e, n ≤ code.length*bound ∧ Eval (nativeCode service code) n d e ∧
      enc (codeRun ops code regs).1 e ∧
      e.stacks p.counter = d.stacks p.counter ∧ e.stacks p.scratch = [] := by
  induction code generalizing regs d with
  | nil => exact ⟨0,d,by simp,.base (.skip d),hd,rfl,hs⟩
  | cons i is ih =>
      obtain ⟨n,e,hn,he,henc,hcounter,hscratch⟩ := spec i regs d hd hs
      obtain ⟨m,f,hm,hf,hencf,hcounterf,hscratchf⟩ :=
        ih (instructionRun ops i regs).1 e henc hscratch
      refine ⟨n+m,f,?_,he.seq hf,hencf,?_,hscratchf⟩
      · simp only [List.length_cons]
        nlinarith
      · exact hcounterf.trans hcounter

/-- This command's finite syntax is independent of `t` and of `clog 2 t`. -/
abbrev nativeNewtonLoop (p : CounterForPrograms.Ports r s)
    (service : ArithmeticInstruction → Cmd r s) : Cmd r s :=
  CounterForPrograms.forCmd p (nativeCode service newtonCode)

end SubexponentialSAT.SqrtLog.IdempotentProgram

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.StructuredCalls

variable {C : Type*} {r s : ℕ}

/-- Strong form: the fixed native loop implements the exact functional array
state, not only its image under a semantic decoder. -/
theorem nativeNewtonLoop_exact (ops : RingProgram C)
    (p : CounterForPrograms.Ports r s)
    (service : ArithmeticInstruction → Cmd r s)
    (enc : Registers C → State r s → Prop) (bound : ℕ)
    (spec : NativeInstructionSpec ops p service enc bound)
    (frame : ∀ regs d e, CounterForPrograms.OutsideEq p d e → enc regs d → enc regs e)
    (regs : Registers C) (d : State r s) (hd : enc regs d)
    (hs : d.stacks p.scratch = []) :
    ∃ n e, Eval (nativeNewtonLoop p service) n d e ∧
      enc (codeRun ops (liftCode (CounterPrograms.value (d.stacks p.counter))) regs).1 e ∧
      n ≤ 7*CounterPrograms.value (d.stacks p.counter)*bound +
        (CounterPrograms.value (d.stacks p.counter)+1)*
          (16*(d.stacks p.counter).length+16) := by
  let I : ℕ → State r s → Prop := fun i e => enc (codeRun ops (liftCode i) regs).1 e
  have stable : CounterForPrograms.FrameStable p I := by
    intro i a b hab ha
    exact frame _ a b hab ha
  have body : CounterForPrograms.BodySpec p (nativeCode service newtonCode) I (fun _ => 7*bound) := by
    intro i a ha hscratch _
    obtain ⟨n,b,hn,hb,henc,hcounter,hscratch⟩ :=
      nativeCode_correct ops p service enc bound spec newtonCode
        (codeRun ops (liftCode i) regs).1 a ha hscratch
    refine ⟨n,b,by simpa only [newtonCode_length] using hn,hb,hcounter,hscratch,?_⟩
    change enc (codeRun ops (liftCode (i+1)) regs).1 b
    simpa only [liftCode, codeRun_append] using henc
  obtain ⟨n,e,he,hi,_,_,_,hn⟩ :=
    CounterForPrograms.for_correct p (nativeCode service newtonCode) I (fun _ => 7*bound)
      stable body d hs hd
  refine ⟨n,e,he,hi,?_⟩
  rw [constant_budget] at hn
  simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hn

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

open BitProgram StructuredCalls SubexpScanPrimitives

theorem scanI_eval (i : ℕ) (r : Fin 8 → Bool) (ys zs bs : List Bool) :
    Eval scanI (10*(i/3)+2*(i%3)+5)
      (data r (List.replicate i true) ys zs bs)
      (data (afterI r i) [] ys zs (List.replicate (3*(i/3)) true ++ bs)) := by
  have hr : Function.Injective scanIRegs := by decide
  have hs : Function.Injective scanIPorts := by decide
  let d := data r (List.replicate i true) ys zs bs
  have hi : embedState scanIRegs scanIPorts d
      ⟨r ∘ scanIRegs,![List.replicate i true,bs]⟩ = d := by
    apply embedState_eq _ _ hr hs
    · intro x; rfl
    · intro x; fin_cases x <;> rfl
    · intros; rfl
    · intros; rfl
  have ho : embedState scanIRegs scanIPorts d
      ⟨remainderRegs (i%3),![[],List.replicate (3*(i/3)) true ++ bs]⟩ =
      data (afterI r i) [] ys zs (List.replicate (3*(i/3)) true ++ bs) := by
    apply embedState_eq _ _ hr hs
    · intro x; fin_cases x <;> rfl
    · intro x; fin_cases x <;> rfl
    · intro x hx; fin_cases x <;>
        simp_all [afterI,scanIRegs,Fin.exists_fin_succ,data,d]
    · intro x hx; fin_cases x <;>
        simp_all [scanIPorts,Fin.exists_fin_succ,data,d]
  have he := eval_call_lifted scanProgram scanIRegs scanIPorts d hr hs
    (a := ⟨r ∘ scanIRegs,![List.replicate i true,bs]⟩)
    (b := ⟨remainderRegs (i%3),![[],List.replicate (3*(i/3)) true ++ bs]⟩)
    (scan_trace i (r ∘ scanIRegs) bs)
  simpa only [hi,ho] using he

theorem scanJ_eval (j : ℕ) (r : Fin 8 → Bool) (xs zs bs : List Bool) :
    Eval scanJ (10*(j/3)+2*(j%3)+5)
      (data r xs (List.replicate j true) zs bs)
      (data (afterJ r j) xs [] zs (List.replicate (3*(j/3)) true ++ bs)) := by
  have hr : Function.Injective scanJRegs := by decide
  have hs : Function.Injective scanJPorts := by decide
  let d := data r xs (List.replicate j true) zs bs
  have hi : embedState scanJRegs scanJPorts d
      ⟨r ∘ scanJRegs,![List.replicate j true,bs]⟩ = d := by
    apply embedState_eq _ _ hr hs
    · intro x; rfl
    · intro x; fin_cases x <;> rfl
    · intros; rfl
    · intros; rfl
  have ho : embedState scanJRegs scanJPorts d
      ⟨remainderRegs (j%3),![[],List.replicate (3*(j/3)) true ++ bs]⟩ =
      data (afterJ r j) xs [] zs (List.replicate (3*(j/3)) true ++ bs) := by
    apply embedState_eq _ _ hr hs
    · intro x; fin_cases x <;> rfl
    · intro x; fin_cases x <;> rfl
    · intro x hx; fin_cases x <;>
        simp_all [afterJ,scanJRegs,Fin.exists_fin_succ,data,d]
    · intro x hx; fin_cases x <;>
        simp_all [scanJPorts,Fin.exists_fin_succ,data,d]
  have he := eval_call_lifted scanProgram scanJRegs scanJPorts d hr hs
    (a := ⟨r ∘ scanJRegs,![List.replicate j true,bs]⟩)
    (b := ⟨remainderRegs (j%3),![[],List.replicate (3*(j/3)) true ++ bs]⟩)
    (scan_trace j (r ∘ scanJRegs) bs)
  simpa only [hi,ho] using he

theorem subtract_eval (a b : ℕ) (r : Fin 8 → Bool) (xs ys : List Bool) :
    ∃ steps rf bs, steps ≤ 4*a+4 ∧
      Eval subtract steps
        (data r xs ys (List.replicate b true) (List.replicate a true))
        (data (afterSub r rf) xs ys (List.replicate (b-a) true) bs) ∧
      rf 3 = decide (b < a) ∧ bs.length ≤ a := by
  have hr : Function.Injective subRegs := by decide
  have hs : Function.Injective subPorts := by decide
  obtain ⟨steps,rf,bs,hcost,htrace,hflag,hbs⟩ := subtract_trace a b (r ∘ subRegs)
  let d := data r xs ys (List.replicate b true) (List.replicate a true)
  have hi : embedState subRegs subPorts d
      ⟨r ∘ subRegs,![List.replicate a true,List.replicate b true]⟩ = d := by
    apply embedState_eq _ _ hr hs
    · intro x; rfl
    · intro x; fin_cases x <;> rfl
    · intros; rfl
    · intros; rfl
  have ho : embedState subRegs subPorts d
      ⟨rf,![bs,List.replicate (b-a) true]⟩ =
      data (afterSub r rf) xs ys (List.replicate (b-a) true) bs := by
    apply embedState_eq _ _ hr hs
    · intro x; fin_cases x <;> rfl
    · intro x; fin_cases x <;> rfl
    · intro x hx; fin_cases x <;>
        simp_all [afterSub,subRegs,Fin.exists_fin_succ,data,d]
    · intro x hx; fin_cases x <;>
        simp_all [subPorts,Fin.exists_fin_succ,data,d]
  refine ⟨steps,rf,bs,hcost,?_,hflag,hbs⟩
  have he := eval_call_lifted subtractProgram subRegs subPorts d hr hs
    (a := ⟨r ∘ subRegs,![List.replicate a true,List.replicate b true]⟩)
    (b := ⟨rf,![bs,List.replicate (b-a) true]⟩) htrace
  simpa only [hi,ho] using he

end SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentTableEntryProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native table-entry selector. The only input magnitudes are unary
stack data. Output registers 5,6,7 encode the six possible small coefficients. -/
namespace SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

open BitProgram StructuredCalls

theorem command_eval (i j k : ℕ) (r : Fin 8 → Bool) :
    ∃ steps rf zs bs, steps ≤ 8*(i+j)+32 ∧
      Eval command steps
        (data r (List.replicate i true) (List.replicate j true)
          (List.replicate k true) [])
        (data rf [] [] zs bs) ∧
      (∀ z, rf (outputPort z) = codeBits (entryCode i j k) z) ∧
      zs.length + bs.length ≤ i+j+k := by
  let r₁ := afterI r i
  let r₂ := afterJ r₁ j
  let a := 3*(i/3+j/3)
  have hI := scanI_eval i r (List.replicate j true) (List.replicate k true) []
  have hJ := scanJ_eval j r₁ [] (List.replicate k true) (List.replicate (3*(i/3)) true)
  have hsum : List.replicate (3*(j/3)) true ++ List.replicate (3*(i/3)) true =
      List.replicate a true := by
    rw [← List.replicate_add]
    congr 1
    dsimp [a]; omega
  simp only [List.append_nil] at hI
  rw [hsum] at hJ
  obtain ⟨ns,rs,bs,hs,he,hr,hbs⟩ := subtract_eval a k r₂ [] []
  let r₃ := afterSub r₂ rs
  have hf : ∃ nf rf zs, nf ≤ 18 ∧
      Eval finish nf (data r₃ [] [] (List.replicate (k-a) true) bs)
        (data rf [] [] zs bs) ∧
      (∀ z, rf (outputPort z) = codeBits (entryCode i j k) z) ∧
      zs.length ≤ k-a := by
    by_cases hka : k < a
    · have h7 : (data r₃ [] [] (List.replicate (k-a) true) bs).regs 7 = true := by
        simpa [data,r₃,afterSub,hka] using hr
      refine ⟨4,setOutput r₃ 0,List.replicate (k-a) true,by omega,
        Eval.ite_true h7 (emit_eval _ 0),?_,by simp⟩
      intro z; fin_cases z <;> simp [entryCode,show k < 3*(i/3+j/3) from hka,
        outputPort,setOutput]
    · have h7 : (data r₃ [] [] (List.replicate (k-a) true) bs).regs 7 = false := by
        simpa [data,r₃,afterSub,hka] using hr
      obtain ⟨nf,rf,zs,hn,hf,hbits,hz⟩ := select_eval
        ⟨i%3,Nat.mod_lt _ (by decide)⟩ ⟨j%3,Nat.mod_lt _ (by decide)⟩
        (k-a) r₃ [] [] bs rfl rfl rfl rfl
      refine ⟨nf+1,rf,zs,by omega,Eval.ite_false h7 hf,?_,hz⟩
      simpa [entryCode,show ¬ k < 3*(i/3+j/3) from hka,a] using hbits
  obtain ⟨nf,rf,zs,hfc,hfinish,hbits,hzs⟩ := hf
  refine ⟨(10*(i/3)+2*(i%3)+5)+((10*(j/3)+2*(j%3)+5)+(ns+nf)),rf,zs,bs,
    ?_,hI.seq (hJ.seq (he.seq hfinish)),hbits,?_⟩
  · have hi := scan_cost i
    have hj := scan_cost j
    have ha : a ≤ i+j := by dsimp [a]; omega
    omega
  · have ha : a ≤ i+j := by dsimp [a]; omega
    omega

/-- A real fixed instruction-table trace, including its final halt. -/
theorem program_trace (i j k : ℕ) (r : Fin 8 → Bool) :
    ∃ steps rf zs bs, steps ≤ 40*(i+j+k+1) ∧
      Trace program steps
        ((data r (List.replicate i true) (List.replicate j true)
          (List.replicate k true) []).withPC (some program.entry))
        ((data rf [] [] zs bs).withPC none) ∧
      (∀ z, rf (outputPort z) = codeBits (entryCode i j k) z) ∧
      zs.length + bs.length ≤ i+j+k := by
  obtain ⟨steps,rf,zs,bs,hc,he,hbits,hz⟩ := command_eval i j k r
  exact ⟨steps+1,rf,zs,bs,by omega,compiled_halt_trace he 0 2,hbits,hz⟩

end SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed local cache-producer instructions and framed native service calls.
The lower256 ports are the existing arithmetic ABI; controller streams and
copy scratch occupy disjoint higher ports. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives StackRoutines

abbrev Data := State 16 320

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadProgramPrepareCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Canonicalize an arbitrary unary counter by an actual fixed bit loop. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadProgramPrepareCount
open SubexponentialSAT BitProgram StructuredCalls

def state (regs : Fin 3 → Bool) (source out : List Bool) : State 3 2 :=
  ⟨regs,![source,out]⟩

theorem trace (regs : Fin 3 → Bool) (source out : List Bool) :
    Trace program (4*source.length+4) ((state regs source out).withPC (some program.entry))
      ((state (fun _ => false) [] (List.replicate source.length true++out)).withPC none) := by
  induction source generalizing regs out with
  | nil =>
    apply Computation.Trace.of_iterate
    simp [Function.iterate_succ_apply,step,program,state,StructuredProgram.State.withPC,execInstr,readRegs]
    first | done | (funext i; fin_cases i <;> simp)
  | cons bit source ih =>
    let next : Fin 3 → Bool := ![bit,true,true]
    have hc : Trace program 4 ((state regs (bit::source) out).withPC (some program.entry))
        ((state next source (true::out)).withPC (some program.entry)) := by
      apply Computation.Trace.of_iterate
      simp [Function.iterate_succ_apply,step,program,state,StructuredProgram.State.withPC,execInstr,readRegs,next]
      all_goals first | (constructor <;> (funext i; fin_cases i <;> simp)) | (funext i; fin_cases i <;> simp)
    have ht := hc.trans (ih next (true::out))
    convert ht using 1 <;> simp [List.replicate_succ',List.append_assoc] ; omega

end SubexponentialSAT.SqrtLog.PackingHeadProgramPrepareCount

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical table producer has polynomial cost in the node count,
residue cardinality, precision, and the native ring-operation bounds. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT SubexpLiftRing

theorem budget_polynomial (t d Q : ℕ) :
    budget t d Q+1 ≤ 1000*(Q+1)^2*(3^d+t+1)*
      (HornerProgram.Services.mulBudget (baseWidth 3 t) d+
        HornerProgram.Services.addBudget (baseWidth 3 t) d+d*baseWidth 3 t+1) := by
  let Km := HornerProgram.Services.mulBudget (baseWidth 3 t) d
  let Ka := HornerProgram.Services.addBudget (baseWidth 3 t) d
  let W := d*baseWidth 3 t
  have hi := inverseBudget_polynomial t d
  change inverseBudget t d ≤ 600*(3^d+t+1)*(Km+Ka+W+1) at hi
  have hj : negativeBudget t d+200*W+200 ≤ 400*(3^d+t+1)*(Km+Ka+W+1) := by
    change Km+40*W+51+200*W+200 ≤ _
    nlinarith only [Nat.zero_le (3^d*Km),Nat.zero_le (3^d*Ka),Nat.zero_le (3^d*W),
      Nat.zero_le (t*Km),Nat.zero_le (t*Ka),Nat.zero_le (t*W),Nat.zero_le Km,Nat.zero_le Ka,Nat.zero_le W,Nat.zero_le (3^d),Nat.zero_le t]
  have hsum : inverseBudget t d+negativeBudget t d+200*W+200 ≤
      1000*(3^d+t+1)*(Km+Ka+W+1) := by nlinarith only [hi,hj]
  calc budget t d Q+1 ≤ (Q+1)^2*(inverseBudget t d+negativeBudget t d+200*W+200) := budget_le_operations t d Q
    _ ≤ (Q+1)^2*(1000*(3^d+t+1)*(Km+Ka+W+1)) := Nat.mul_le_mul_left _ hsum
    _ = _ := by ring

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable arbitrary-degree irreducible search over F₃

Search all monic degree-`d` coefficient vectors and reject each candidate
which is the product of two nonconstant arrays of degree at most `d`.
The test uses explicit convolution. Mathematical finite-field existence
proves that the executable search succeeds for every positive `d`.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open Polynomial

theorem passes_iff {d : ℕ} (hd : 0 < d) (c : Fin d → F) :
    passes c = true ↔ Irreducible (QuarticSearch.poly c) := by
  rw [passes, List.all_eq_true]
  constructor
  · intro h
    refine ⟨Polynomial.not_isUnit_of_natDegree_pos _ (by simpa using hd), ?_⟩
    intro a b hab
    by_cases ha : IsUnit a
    · exact Or.inl ha
    by_cases hb : IsUnit b
    · exact Or.inr hb
    exfalso
    have hprod : a * b ≠ 0 := by rw [← hab]; exact (QuarticSearch.poly_monic c).ne_zero
    have ha0 : a ≠ 0 := left_ne_zero_of_mul hprod
    have hb0 : b ≠ 0 := right_ne_zero_of_mul hprod
    have hdeg : a.natDegree + b.natDegree = d := by
      rw [← Polynomial.natDegree_mul ha0 hb0, ← hab, QuarticSearch.poly_natDegree]
    have hap : 0 < a.natDegree :=
      Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic
        (QuarticSearch.poly_monic c) ha ⟨b, hab⟩
    have hbp : 0 < b.natDegree :=
      Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic
        (QuarticSearch.poly_monic c) hb ⟨a, by rw [mul_comm]; exact hab⟩
    let av := Polynomial.toFn (d + 1) a
    let bv := Polynomial.toFn (d + 1) b
    have hav : Polynomial.ofFn (d + 1) av = a :=
      Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
    have hbv : Polynomial.ofFn (d + 1) bv = b :=
      Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
    have hp := (pairPass_iff c av bv).mp (h (av, bv) (mem_factorPairs d av bv))
    exact hp (by simpa only [hav, hbv] using And.intro hap (And.intro hbp hab.symm))
  · intro h ab _
    apply (pairPass_iff c ab.1 ab.2).mpr
    rintro ⟨ha, hb, hab⟩
    rcases h.isUnit_or_isUnit hab.symm with hu | hu
    · exact Polynomial.not_isUnit_of_natDegree_pos _ ha hu
    · exact Polynomial.not_isUnit_of_natDegree_pos _ hb hu

theorem exists_passing {d : ℕ} (hd : 0 < d) : ∃ c ∈ candidates d, passes c = true := by
  obtain ⟨f, hm, hi, hn⟩ := SubexponentialSAT.FiniteField.exists_monic_irreducible 3 d (by omega)
  let c : Fin d → F := fun i => f.coeff i
  refine ⟨c, mem_candidates _ _, (passes_iff hd c).mpr ?_⟩
  simpa only [c, QuarticSearch.poly_of_coeff f hm hn] using hi

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpOrderedTupleStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! # A fixed Cartesian expansion in exact enumeration order -/

namespace SubexponentialSAT.SubexpOrderedTupleStep

open BitProgram StructuredCalls Subexp.TupleProgram SubexpOrderedTupleData
open Subexp.BlockSearchPreparation (restrictState lifted_call)

abbrev reverseRecords : Cmd 10 9 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.reverseRecordsProgram
    reverseRegisters reverseStacks)

end SubexponentialSAT.SubexpOrderedTupleStep

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed fixed-bit F₃ factor checker. The complete command is independent
of the degree. All coefficient addresses and loop bounds are runtime unary
words; source vectors are preserved and scratch stacks are discharged. -/


/-! Coefficient -/

/-! A fixed coefficient kernel: two preserved source arrays, a preserved
unary coefficient address plus one, and an output stack. Every copy, padded
prefix, coefficient reversal, multiply-add and cleanup is an actual call. -/


/-! CoefficientRun -/

/-! The closed, fixed-program boundary for one arbitrary convolution
coefficient. Its sources and runtime unary address are preserved and all
work stacks are empty again. -/


/-! ProductLift -/

/-! A framed invocation of the source-preserving coefficient kernel. The
extra stack stores the remaining runtime product length. -/


/-! Product -/

/-! A fixed outer loop runs the coefficient kernel at successively longer
unary addresses. Source arrays are preserved; all output coefficients are
physically written in decreasing degree order. -/


/-! ProductRun -/


/-! Monic -/

/-! Appending the implicit monic coefficient uses two physical transfers.
No input-dependent instruction table or uncharged array append is used. -/


/-! MonicAlgebra -/

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram

theorem coefficientArray_injective : Function.Injective coefficientArray :=
  StackEncoding.encodeDataStack_injective (SubexpEnumerationPayload.scalarCode 3)

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! CheckLift -/

/-! Framed calls to the physical Boolean predicates. -/


/-! PairProduct -/


/-! Candidate -/


/-! ProductCheck -/


/-! Pair -/

/-! Closed primitive pair test. All three source vectors and the runtime
unary degree are preserved. The return bit is exactly the scalar pairPass. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native irreducible-polynomial search: concrete factor callbacks,
saved universal scans, exact ordered candidate selection, and measured cost. -/

/-! A fixed factor-pair callback and universal scan. All checker arithmetic,
record extraction, array splitting, and cleanup use explicit bit programs. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

open BitProgram StructuredCalls IrreducibleSearchProgram
open Subexp.BlockSearchPreparation (restrictState lifted_call)
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

/-- This observer labels executions on valid records. The program never calls
it: the preceding measured arithmetic proof establishes the label. -/
noncomputable def factorTest {d : ℕ} (c : Fin d → IrreducibleSearch.F) : List Bool → Bool :=
  Function.extend pairEncode (IrreducibleSearch.pairPass c) (fun _ => false)

end SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

/-! Fixed first-success scan using the concrete saved factor checker. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native owner-fiber summation helpers. The remaining fiber is a stream of
actual unary index fields, never an array of precomputed matrix entries. -/
namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open RowSelectionProgram

abbrev Data := State 16 256

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end


