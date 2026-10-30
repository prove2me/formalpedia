-- Prove2me | Definitions.Def_OAIQ081S141
-- name    : OAIQ081S141
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:50:13.344851+00:00
-- url     : https://prove2.me/theorems/73ebda04-6217-4d34-abf0-e7af839ed3aa
-- title:
--   Definitions bundle OAIQ081S141 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 21 declarations of OpenAI's Lean: 9 definitions, 1 inductive type or structure and 11 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.cachedSignedValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.Runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.clear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.consumeCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.differenceValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.inverseCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.lowCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.negativeCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop.command`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLog_IdempotentPreparationProgramBoot`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentPreparationProgramBoot.lean), [`SubexponentialSAT_SqrtLog_IdempotentPreparationProgramModulus`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentPreparationProgramModulus.lean), [`SubexponentialSAT_SqrtLog_IdempotentProgramMachine`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentProgramMachine.lean), [`SubexponentialSAT_SqrtLog_IntegerRingLiftProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IntegerRingLiftProgram.lean), [`SubexponentialSAT_SqrtLog_IntegerRingLiftProgramCached`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IntegerRingLiftProgramCached.lean), [`SubexponentialSAT_SqrtLog_InterpolationCacheProgramBasic`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/InterpolationCacheProgramBasic.lean), [`SubexponentialSAT_SqrtLog_InterpolationCacheProgramCounts`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/InterpolationCacheProgramCounts.lean), [`SubexponentialSAT_SqrtLog_InterpolationCacheProgramFrame`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/InterpolationCacheProgramFrame.lean), [`SubexponentialSAT_SqrtLog_InterpolationCacheProgramModel`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/InterpolationCacheProgramModel.lean), [`SubexponentialSAT_SqrtLog_InterpolationCacheProgramNative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/InterpolationCacheProgramNative.lean), [`SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingIncidenceInputNative.lean).
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S116`, `OAIQ081S118`, `OAIQ081S119`, `OAIQ081S120`, `OAIQ081S121`, `OAIQ081S130` and `OAIQ081S131` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S154`, `OAIQ081S155`, `OAIQ081S156`, `OAIQ081S157` and `OAIQ081S159`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S116
import Definitions.Def_OAIQ081S118
import Definitions.Def_OAIQ081S119
import Definitions.Def_OAIQ081S120
import Definitions.Def_OAIQ081S121
import Definitions.Def_OAIQ081S130
import Definitions.Def_OAIQ081S131

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramModulus
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native production of the ternary modulus from runtime binary precision.
The output bytes themselves instantiate the prepared-modulus structure;
no canonical encoding or precomputed power is supplied to the machine. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpScanPrimitives

theorem modulusCommand_eval (d : Data) (ready : ModulusWorkspaceEmpty d) :
    ∃ (M : SubexpPreparedQuartic.Modulus 3 (BinaryArithmetic.toNat (d.stacks 31))), ∃ n rf,
      n ≤ 1001*(BinaryArithmetic.toNat (d.stacks 31)+(d.stacks 31).length+2)^2 ∧
      Eval modulusCommand n d ⟨rf,Function.update d.stacks 5 M.bits⟩ := by
  let words : SubexpBlockParameterProgram.Words := fun i =>
    if i = 1 then d.stacks 31 else []
  obtain ⟨n,rf,word,he,hv,hl,hn⟩ := LeafParametersProgram.Field.command_eval d.regs words
    (by simp [words]) (by simp [words])
  have hval : BinaryArithmetic.toNat word = 3 ^ BinaryArithmetic.toNat (d.stacks 31) := by
    simpa [words] using hv
  have hwidth : word.length ≤ SubexpLiftRing.baseWidth 3
      (BinaryArithmetic.toNat (d.stacks 31)) + 1 := by
    have ht : Nat.log 2 3 = 1 := (Nat.log_eq_one_iff').2 (by decide)
    simpa [words,SubexpLiftRing.baseWidth,ht,Nat.mul_comm,Nat.add_comm] using hl
  let M : SubexpPreparedQuartic.Modulus 3 (BinaryArithmetic.toNat (d.stacks 31)) :=
    ⟨word,hwidth,hval⟩
  let a := SubexpBlockParameterProgram.state d.regs words
  let b := SubexpBlockParameterProgram.state rf (Function.update words 2 word)
  have hproj : ∀ i, d.stacks (modulusPorts i) = a.stacks i := by
    intro i
    by_cases hi : i = 1
    · subst i
      simp [a,SubexpBlockParameterProgram.state,words,modulusPorts]
    · have hr := ready i hi
      fin_cases i <;> norm_num [a,SubexpBlockParameterProgram.state,words,
        modulusPorts,Function.update,Fin.ext_iff] at * <;> assumption
  have hstate : b.stacks = Function.update a.stacks 2 word := by
    have h := congrArg (fun q : StructuredProgram.State 8 22 => q.stacks)
      (SubexpBlockParameterProgram.state_update d.regs rf words 2 word)
    exact h.symm
  have hi : embedState id modulusPorts d a = d := by
    apply embedState_eq _ _ Function.injective_id modulusPorts_injective
    · intro i; rfl
    · exact hproj
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intros; rfl
  have hout : (embedState id modulusPorts d b).stacks = Function.update d.stacks 5 word := by
    funext j
    by_cases hj : ∃ i, modulusPorts i = j
    · obtain ⟨i,rfl⟩ := hj
      rw [embedState_stack _ _ _ _ modulusPorts_injective,hstate]
      by_cases hi : i = 2
      · subst i; simp [modulusPorts]
      · have htarget : modulusPorts i ≠ 5 := by
          intro h
          fin_cases i <;> simp [modulusPorts] at h hi
        rw [Function.update_of_ne hi,Function.update_of_ne htarget]
        exact (hproj i).symm
    · rw [embedState_stack_frame _ _ _ _ j hj]
      have hj5 : j ≠ 5 := fun h => hj ⟨2,by simpa [modulusPorts] using h.symm⟩
      simp [hj5]
  have run := eval_call_lifted LeafParametersProgram.Field.program id modulusPorts d
    Function.injective_id modulusPorts_injective (compiled_halt_trace he 1 2)
  have hb : embedState id modulusPorts d b =
      ⟨(embedState id modulusPorts d b).regs,Function.update d.stacks 5 word⟩ := state_ext rfl hout
  change Eval modulusCommand (n+1) (embedState id modulusPorts d a)
    (embedState id modulusPorts d b) at run
  rw [hi,hb] at run
  refine ⟨M,n+1,_,?_,run⟩
  have hp := LeafParametersProgram.Field.bound_polynomial (d.stacks 31)
  simp only [words,ite_true, if_true] at hn
  have hpos : 0 < (BinaryArithmetic.toNat (d.stacks 31)+(d.stacks 31).length+2)^2 := by
    positivity
  omega

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramBoot
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls

theorem boot_eval (bits : List Bool) (t : ℕ) (hv : CounterPrograms.value bits=t) (ht : 0 < t) :
    ∃ (M : SubexpPreparedQuartic.Modulus 3 t), ∃ logword cost rf,
      CounterPrograms.value logword = Nat.clog 2 t ∧ logword.length ≤ bits.length+1 ∧
      cost ≤ 2001*(t+bits.length+2)^2 ∧
      Eval boot cost (inputData bits) ⟨rf,bootStacks t bits M.bits logword⟩ := by
  obtain ⟨logword,nm,rm,hlog,hlen,hnm,hm⟩ := metadataFromBinary_eval (inputData bits)
    (by simp [inputData]) (by simp [inputData]) (by simp [inputData])
    (by simp [inputData]) (by simp [inputData]) (by simp [inputData])
    (by simp [inputData]) (by simp [inputData]) (by simp [inputData])
    (by simp [inputData]) (by simp [inputData]) (by simpa [inputData,hv] using ht)
  let a : Data := ⟨rm,metadataStacks (inputData bits).stacks logword⟩
  have ready : ModulusWorkspaceEmpty a := by
    intro i hi
    fin_cases i <;> simp_all [a,metadataStacks,inputData,modulusPorts]
  have ha31 : a.stacks 31 = bits := by simp [a,metadataStacks,inputData]
  have hav : BinaryArithmetic.toNat (a.stacks 31) = t := by
    rw [ha31,←CounterPrograms.value_eq_toNat,hv]
  obtain ⟨M,np,rp,hnp,hp⟩ := modulusCommand_eval a ready
  let M' : SubexpPreparedQuartic.Modulus 3 t :=
    ⟨M.bits,by simpa only [hav] using M.length_le,by simpa only [hav] using M.value⟩
  rw [hav,ha31] at hnp
  refine ⟨M',logword,nm+np,rp,?_,?_,?_,?_⟩
  · simpa [inputData,hv] using hlog
  · simpa [inputData] using hlen
  · simp only [inputData,Function.update_same,hv] at hnm
    nlinarith
  · have he := hm.seq hp
    simpa [boot,a,metadataStacks,bootStacks,inputData,hv,M'] using he

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramMachine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed four-array Newton machine. Its native services perform full dynamic
vector arithmetic, operand copying, and target replacement. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open BitProgram StructuredCalls SubexpSymbolicCost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem RegistersEncoded.update {B d : ℕ} {modulus width zero table degree : List Bool}
    {minusOne : RingProgram.Code (Word B) d}
    {regs : Registers (RingProgram.Code (Word B) d)} {state next : RegisterData}
    (h : RegistersEncoded modulus width zero table degree minusOne regs state)
    (dst : Fin 4) (value : RingProgram.Code (Word B) d)
    (hs : next.stacks = Function.update state.stacks (arrayRegister dst) (RingProgram.flat value)) :
    RegistersEncoded modulus width zero table degree minusOne (Function.update regs dst value) next := by
  constructor
  · intro i
    have hi : servicePorts i ≠ arrayRegister dst := by
      intro he
      have hv := congrArg Fin.val he
      have := i.isLt
      dsimp [servicePorts, arrayRegister] at hv
      omega
    rw [hs, Function.update_of_ne hi]
    exact h.context i
  · intro i
    rw [hs]
    by_cases hi : i = dst
    · subst i; simp
    · simp [Function.update_of_ne hi, arrayRegister_injective.ne hi, h.values]
  · have hi : (36 : Fin 41) ≠ arrayRegister dst := by
      intro he; have hv := congrArg Fin.val he; have := dst.isLt
      dsimp [arrayRegister] at hv; omega
    rw [hs, Function.update_of_ne hi]
    exact h.negativeUnit
  · have hi : (37 : Fin 41) ≠ arrayRegister dst := by
      intro he; have hv := congrArg Fin.val he; have := dst.isLt
      dsimp [arrayRegister] at hv; omega
    rw [hs, Function.update_of_ne hi]
    exact h.degree
  · have hi : (38 : Fin 41) ≠ arrayRegister dst := by
      intro he; have hv := congrArg Fin.val he; have := dst.isLt
      dsimp [arrayRegister] at hv; omega
    rw [hs, Function.update_of_ne hi]
    exact h.copyScratch

end SubexponentialSAT.SqrtLog.IdempotentProgram

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open BitProgram StructuredCalls SubexpSymbolicCost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- One fully measured register update, ready to instantiate with either
native arithmetic service. All source ports may coincide with the target. -/
theorem registerArrayStep {B dim : ℕ} (command : Cmd 8 32)
    (modulus width zero table degree : List Bool) (hd : degree.length = dim)
    (minusOne : RingProgram.Code (Word B) dim)
    (regs : Registers (RingProgram.Code (Word B) dim)) (state : RegisterData)
    (encoded : RegistersEncoded modulus width zero table degree minusOne regs state)
    (target : Fin 4) (left right : Fin 41)
    (x y value : RingProgram.Code (Word B) dim)
    (hl : 32 ≤ left.val) (hr : 32 ≤ right.val)
    (hl38 : left ≠ 38) (hr38 : right ≠ 38)
    (hx : state.stacks left = RingProgram.flat x)
    (hy : state.stacks right = RingProgram.flat y)
    (bound : ℕ)
    (hbound : bound ≤ max (RingScan.serviceAddBudget B dim) (RingScan.serviceMulBudget B dim))
    (run : ∀ flags : Fin 8 → Bool,
      ∃ n ≤ bound, ∃ rf, Eval command n
        (RingScan.serviceState flags modulus [] (RingProgram.flat x) (RingProgram.flat y)
          degree width zero table)
        (RingScan.serviceState rf modulus (RingProgram.flat value) [] [] [] width zero table)) :
    ∃ n next, n ≤ arithmeticBudget B dim ∧
      Eval (registerBinary (callService command) (arrayRegister target) left right) n state next ∧
      RegistersEncoded modulus width zero table degree minusOne
        (Function.update regs target value) next ∧
      next.stacks 39 = state.stacks 39 ∧ next.stacks 40 = state.stacks 40 := by
  obtain ⟨n, hn, rf, hrun⟩ := run (preparedOperands state left right).regs
  have ht : 32 ≤ (arrayRegister target).val := by dsimp [arrayRegister]; omega
  have ht38 : arrayRegister target ≠ 38 := by
    intro h; have hv := congrArg Fin.val h; have := target.isLt
    dsimp [arrayRegister] at hv; omega
  obtain ⟨next, hnext, hstacks⟩ := registerService_eval command state modulus width zero table degree
    (RingProgram.flat x) (RingProgram.flat y) (RingProgram.flat value)
    (arrayRegister target) left right n rf encoded.context encoded.degree hx hy encoded.copyScratch
    ht hl hr ht38 hl38 hr38 hrun
  refine ⟨_, next, ?_, hnext, encoded.update target value hstacks, ?_, ?_⟩
  · rw [encoded.values target, RingProgram.flat_length, RingProgram.flat_length,
      RingProgram.flat_length, RingProgram.flat_length, hd]
    unfold arithmeticBudget
    omega
  · rw [hstacks]
    have h39 : (39 : Fin 41) ≠ arrayRegister target := by
      intro h; have hv := congrArg Fin.val h; have := target.isLt
      dsimp [arrayRegister] at hv; omega
    exact Function.update_of_ne h39 _ _
  · rw [hstacks]
    have h40 : (40 : Fin 41) ≠ arrayRegister target := by
      intro h; have hv := congrArg Fin.val h; have := target.isLt
      dsimp [arrayRegister] at hv; omega
    exact Function.update_of_ne h40 _ _

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IntegerRingLiftProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed little-endian binary-to-ring scanner.  No natural-number value is
used by the program: each input bit conditionally adds the current place and
then doubles that place.  Arithmetic is supplied by finite native commands;
the concrete RingModel instantiation is in IntegerRingLiftProgramModel. -/
namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec LowFrame lowFrame_update lowFrame_refl
  callAt callAt_run CachePort)

theorem bitStep_eval {C : Type*} (base : Store) (encode : C → List Bool)
    (add : Code) (op : C → C → C) (K W : ℕ)
    (ha : ServiceSpec base encode add op K) (hw : ∀ a, (encode a).length ≤ W)
    (s : Store) (a p : C) (b : Bool) (hf : LowFrame base s) (hc : Clean s)
    (hacc : s 247 = encode a) (hplace : s 248 = encode p)
    (regs : Fin 16 → Bool) (hb : regs 0 = b) :
    ∃ n rf, n ≤ 2 * (K + 40 * W + 50) + 1 ∧
      Eval (bitStep add) n (⟨regs, s⟩ : Data)
        (⟨rf, Function.update (Function.update s 247 (encode (if b then op a p else a)))
          248 (encode (op p p))⟩ : Data) := by
  let a' := if b then op a p else a
  let s1 := Function.update s 247 (encode a')
  have hfirst : ∃ n rf, n ≤ K + 40 * W + 51 ∧
      Eval (.ite 0 (callAt add 247 248 247) (.base .skip)) n
        (⟨regs, s⟩ : Data) (⟨rf, s1⟩ : Data) := by
    cases b with
    | false =>
      have he : s1 = s := by simp [s1, a', ← hacc]
      refine ⟨1, regs, by omega, ?_⟩
      rw [he]
      exact .ite_false hb (.base (.skip _))
    | true =>
      obtain ⟨n, rf, hn, he⟩ := callAt_run base encode add op K W ha hw s a p
        247 248 247 (by unfold CachePort; decide) (by unfold CachePort; decide)
        (by unfold CachePort; decide) hf hacc hplace
        hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
        (by simpa [hacc] using hw a) regs
      exact ⟨n+1, rf, by omega, .ite_true hb he⟩
  obtain ⟨n1, r1, hn1, h1⟩ := hfirst
  have hf1 : LowFrame base s1 := lowFrame_update hf 247 (by decide) _
  have hc1 : Clean s1 := by simpa [s1, Clean] using hc
  obtain ⟨n2, r2, hn2, h2⟩ := callAt_run base encode add op K W ha hw s1 p p
    248 248 248 (by unfold CachePort; decide) (by unfold CachePort; decide)
    (by unfold CachePort; decide) hf1
    (by simp [s1, hplace]) (by simp [s1, hplace])
    hc1.1 hc1.2.1 hc1.2.2.1 hc1.2.2.2.1 hc1.2.2.2.2
    (by simpa [s1, hplace] using hw p) r1
  exact ⟨n1+n2, r2, by omega, h1.seq h2⟩

theorem popped_scanState {C : Type*} (base : Store) (encode : C → List Bool)
    (bs : List Bool) (a p : C) (regs : Fin 16 → Bool) :
    UnaryForPrograms.popped bitPorts (⟨regs, scanState base encode bs a p⟩ : Data) =
      (⟨readRegs regs 0 1 bs.head?, scanState base encode bs.tail a p⟩ : Data) := by
  apply SubexpScanPrimitives.state_ext
  · simp [UnaryForPrograms.popped, bitPorts, scanState]
  · funext i
    by_cases h246 : i = 246 <;> by_cases h247 : i = 247 <;> by_cases h248 : i = 248 <;>
      simp [UnaryForPrograms.popped, bitPorts, scanState, h246, h247, h248]

theorem scan_visits {C : Type*} (base : Store) (encode : C → List Bool)
    (add : Code) (op : C → C → C) (K W : ℕ)
    (ha : ServiceSpec base encode add op K) (hw : ∀ a, (encode a).length ≤ W)
    (hc : Clean base) (bs : List Bool) (a p : C) (regs : Fin 16 → Bool) :
    ∃ costs n rf, n ≤ bs.length * (2 * (K + 40 * W + 50) + 3) + 2 ∧
      UnaryForPrograms.Visits bitPorts (bitStep add) costs n
        (⟨regs, scanState base encode bs a p⟩ : Data)
        (⟨rf, scanState base encode [] (scan op bs a p).1 (scan op bs a p).2⟩ : Data) := by
  induction bs generalizing a p regs with
  | nil =>
    refine ⟨[], 2, readRegs regs 0 1 none, by simp, ?_⟩
    simpa only [popped_scanState, List.head?_nil, List.tail_nil, scan] using
      UnaryForPrograms.Visits.done (p := bitPorts) (body := bitStep add)
        (⟨regs, scanState base encode [] a p⟩ : Data) (by simp [scanState, bitPorts])
  | cons b bs ih =>
    let r0 := readRegs regs 0 1 (some b)
    obtain ⟨nb, rb, hnb, hb⟩ := bitStep_eval base encode add op K W ha hw
      (scanState base encode bs a p) a p b (frame_scanState base encode bs a p)
      (clean_scanState base encode bs a p hc) (by simp [scanState])
      (by simp [scanState]) r0 (by simp [r0, readRegs])
    have hs : Function.update (Function.update (scanState base encode bs a p)
        247 (encode (if b then op a p else a))) 248 (encode (op p p)) =
        scanState base encode bs (if b then op a p else a) (op p p) := by
      funext i
      by_cases h247 : i = 247 <;> by_cases h248 : i = 248 <;>
        simp [scanState, Function.update_apply, h247, h248]
    rw [hs] at hb
    obtain ⟨costs, nt, rt, hnt, ht⟩ := ih (if b then op a p else a) (op p p) rb
    refine ⟨nb :: costs, nb + nt + 2, rt, ?_, ?_⟩
    · simp only [List.length_cons]
      nlinarith
    · have h := UnaryForPrograms.Visits.step (p := bitPorts) (body := bitStep add)
        (d := (⟨regs, scanState base encode (b :: bs) a p⟩ : Data))
        (by simp [scanState, bitPorts])
        (by simpa only [popped_scanState, List.head?_cons, List.tail_cons, r0] using hb)
        (by simp [scanState, bitPorts, UnaryForPrograms.popped]) ht
      simpa only [scan] using h

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IntegerRingLiftProgramCached
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Cache-extensional interface for the same fixed integer-lift programs.
Setup may supply any represented zero, one and minus-one bytes whose decoded
values are correct. This avoids requiring its constant-vector construction
to equal a particular arithmetic expression byte for byte. -/
namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open CRTLocalProgram (lowFrame_refl)

def cachedSignedValue (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (zero one minusOne : ModelCode t d) (positive negative : List Bool) : ModelCode t d :=
  let ops := RingProgram.modelProgram t a M cache
  signedValue (fun x y => (ops.mulRun x y).1) (fun x y => (ops.addRun x y).1)
    zero one minusOne positive negative

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

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

def Runs (c : Code) (K : ℕ) (s out : Store) : Prop :=
  ∀ r : Fin 16 → Bool, ∃ n rf, n ≤ K ∧ Eval c n (⟨r,s⟩ : Data) ⟨rf,out⟩

theorem Runs.mono {c : Code} {K L : ℕ} {s out : Store} (h : Runs c K s out)
    (hKL : K ≤ L) : Runs c L s out := by
  intro r
  obtain ⟨n,rf,hn,he⟩ := h r
  exact ⟨n,rf,hn.trans hKL,he⟩

theorem Runs.seq {c e : Code} {K L : ℕ} {s mid out : Store}
    (hc : Runs c K s mid) (he : Runs e L mid out) : Runs (.seq c e) (K+L) s out := by
  intro r
  obtain ⟨n,rm,hn,en⟩ := hc r
  obtain ⟨m,rf,hm,em⟩ := he rm
  exact ⟨n+m,rf,Nat.add_le_add hn hm,en.seq em⟩

def clear (src : Fin 320) : Code := .call (clearProgram src 0 1)

abbrev lowCall (cmd : Cmd 16 256) : Code :=
  .call (ProgramLinking.liftProgram (compiled cmd 0 0) id low)

/-- The service is a real compiled finite subprogram. Its one changed low
port is installed back into the larger controller store; all higher streams
and every other low port are preserved. -/
theorem lowCall_run (cmd : Cmd 16 256) (K : ℕ) (s : Store) (i : Fin 256) (out : List Bool)
    (h : SubexpConvolutionControl.ExecutesIn cmd K (s ∘ low) (Function.update (s ∘ low) i out)) :
    Runs (lowCall cmd) (K+1) s (Function.update s (low i) out) := by
  intro r
  obtain ⟨n,rf,hn,he⟩ := h r
  let a : Data := ⟨r,s⟩
  let b : State 16 256 := ⟨rf,Function.update (s ∘ low) i out⟩
  have hc := eval_call_from_state (compiled cmd 0 0) id low a Function.injective_id
    low_injective (compiled_halt_trace he 0 0)
  have hbase : Function.extend low (s ∘ low) s=s := by
    exact congrArg StructuredProgram.State.stacks
      (embedState_project id low a Function.injective_id low_injective)
  have hs : (embedState id low a b).stacks=Function.update s (low i) out := by
    change Function.extend low (Function.update (s ∘ low) i out) s = _
    rw [ProgramLinking.extend_update low_injective,hbase]
  have hb : embedState id low a b=
      (⟨(embedState id low a b).regs,Function.update s (low i) out⟩ : Data) :=
    state_ext rfl hs
  change Eval (lowCall cmd) (n+1) a (embedState id low a b) at hc
  rw [hb] at hc
  exact ⟨n+1,_,Nat.add_le_add_right hn 1,hc⟩

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramCounts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid materialization of canonical unary word and table lengths. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def consumeCount (src dst : Fin 320) : Code :=
  .call (ProgramLinking.liftProgram PackingHeadProgramPrepareCount.program countRegisters (countPorts src dst))

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Values computed by the physical interpolation-cache producer. Every
entry is a typed output of an executable ring program. The uniform inverse
routine has an explicit zero-diagonal interpretation. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram

open SubexponentialSAT
open scoped BigOperators

def differenceValue (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne x y : Coeff t d) : Coeff t d :=
  CRTLocalProgram.NativeInverse.value t a M cache x y minusOne

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual finite arithmetic subprograms used in the cache scans. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing

def inverseCommand : Code := lowCall CRTLocalProgram.NativeInverse.command

def negativeCommand : Code := lowCall
  (CRTLocalProgram.callAt HornerProgram.Services.multiply 213 211 208)

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The controller's changing ports and the preserved arithmetic context. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT

structure Ready (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (s : Store) : Prop where
  native : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache) (s ∘ low)
  zero : s 104=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1
  one : s 207=RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1
  minus : s 211=RingProgram.flat minusOne
  exponent : (s 209).length=3^d-2
  precision : (s 212).length=t
  scratch : ∀i∈scratchPorts,s i=[]

theorem Ready.width {t d : ℕ} {a : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {minusOne : Coeff t d} {s : Store} (h : Ready t a M cache minusOne s) :
    (s 104).length=d*SubexpLiftRing.baseWidth 3 t := by
  rw [h.zero,RingProgram.flat_length]

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

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


/-! Calls to the fixed record mapper inside the native scope scan. -/


/-! One native low-variable step, including its uncovered neutral factor. -/


/-! Runtime high-mask loop for the original-address incidence stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
def command := UnaryForPrograms.forCmd ports body
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop


/-! Count the physical scope stream before constructing native incidence plans. -/

end OAI.Algorithms
end


