-- Prove2me | Definitions.Def_OAIQ081S156
-- name    : OAIQ081S156
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:01:09.627571+00:00
-- url     : https://prove2.me/theorems/ddbbce6e-9c01-4c44-ba48-6c972afba7d8
-- title:
--   Definitions bundle OAIQ081S156 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 33 declarations of OpenAI's Lean: 23 definitions, 2 inductive types or structures and 8 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgram.value`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery.value`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.BaseReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.CacheWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.Cached`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.MetadataReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.compareBlocks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.compareIndices`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.finish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.metadataFieldsLength`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.metadataStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.prepareSize`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.preparedStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.uncovered`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry.output`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerFinish.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerFinish.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerFinish.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerFinish.output`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisEntryCore.compare`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LayoutDenominatorProgram`, `SubexponentialSAT_SqrtLog_LayoutDenominatorProgramModel`, `SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQuery`, `SubexponentialSAT_SqrtLog_LayoutProgramEntryBank`, `SubexponentialSAT_SqrtLog_LayoutProgramEntryBankCache`, `SubexponentialSAT_SqrtLog_LayoutProgramEntryBankFrame`, `SubexponentialSAT_SqrtLog_LayoutProgramEntryBankFramePrepare`, `SubexponentialSAT_SqrtLog_LayoutProgramEntryBankFrameUncovered`, `SubexponentialSAT_SqrtLog_LayoutProgramEntryBankInner`, `SubexponentialSAT_SqrtLog_LayoutProgramIntegerCache`, `SubexponentialSAT_SqrtLog_LayoutProgramIntegerEntry`, `SubexponentialSAT_SqrtLog_LayoutProgramIntegerFinish`, `SubexponentialSAT_SqrtLog_LayoutProgramNumerator`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceBank`, `SubexponentialSAT_SubexpKernelControl`, `SubexponentialSAT_Subexp_GlobalBasisEntryCore`, `SubexponentialSAT_Subexp_PackingExtractionBlock`, `SubexponentialSAT_Subexp_PackingExtractionCallback`, `SubexponentialSAT_Subexp_PackingLeftoverStage`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S138`, `OAIQ081S141`, `OAIQ081S142`, `OAIQ081S143` and `OAIQ081S144` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S167`, `OAIQ081S168` and `OAIQ081S170`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.uncovered_cleanup_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.program_runsIn`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.uncovered_cleanup_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.program_runsIn`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S138
import Definitions.Def_OAIQ081S141
import Definitions.Def_OAIQ081S142
import Definitions.Def_OAIQ081S143
import Definitions.Def_OAIQ081S144

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutDenominatorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native exponentiation for the common layout denominator. The unary
row parameter is retained at239; the represented half starts at255 and one at250.
The output252 is computed by exactly `R-1` native multiplications. -/
namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec LowFrame lowFrame_update nativeRepeat binaryStep binary_repeat_state)

theorem powerCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply : Code) (mul : C → C → C) (K W : ℕ)
    (hm : ServiceSpec base encode multiply mul K) (hw : ∀ x, (encode x).length ≤ W)
    (s : Store) (half one : C) (hf : LowFrame base s)
    (hhalf : s 255 = encode half) (hone : s 250 = encode one)
    (h120 : s 120 = []) (h240 : s 240 = []) (h241 : s 241 = [])
    (h244 : s 244 = []) (h245 : s 245 = []) (h246 : s 246 = [])
    (h252 : s 252 = []) :
    ExecutesIn (powerCommand multiply) (powerBudget (s 239).length K W) s
      (Function.update (Function.update s 255 []) 252
        (encode (powerValue mul half one (s 239).length))) := by
  let out := powerValue mul half one (s 239).length
  let s1 := Function.update s 241 (encode half)
  let s2 := Function.update s1 240 (encode one)
  let s3 := Function.update s2 246 (s 239)
  let s4 := Function.update s2 246 (s 239).tail
  let s5 := Function.update s1 240 (encode out)
  let s6 := Function.update s5 252 (encode out)
  let s7 := Function.update s1 252 (encode out)
  let s8 := Function.update s 252 (encode out)
  have h1 : ExecutesIn (copy 255 241) (7*W+5) s s1 := by
    have h := copy_run 255 241 s (by decide) (by decide) (by decide) h120
    simp only [hhalf,h241,List.append_nil] at h
    exact h.mono (by have := hw half; omega)
  have h2 : ExecutesIn (copy 250 240) (7*W+5) s1 s2 := by
    have h := copy_run 250 240 s1 (by decide) (by decide) (by decide)
      (by simp [s1,h120])
    simpa [s2,s1,hone,h240] using h.mono (by simpa [s1,hone] using (Nat.add_le_add_right (Nat.mul_le_mul_left 7 (hw one)) 5))
  have h3 : ExecutesIn (copy 239 246) (7*(s 239).length+5) s2 s3 := by
    simpa [s3,s2,s1,h246] using copy_run 239 246 s2
      (by decide) (by decide) (by decide) (by simp [s2,s1,h120])
  have h4 : ExecutesIn (popToken 246) 1 s3 s4 := by
    simpa [s3,s4] using popToken_tail_run s3 246
  have hf4 : LowFrame base s4 := lowFrame_update
    (lowFrame_update (lowFrame_update hf 241 (by decide) _) 240 (by decide) _)
    246 (by decide) _
  have h5 : ExecutesIn (nativeRepeat (binaryStep multiply))
      (((s 239).length-1)*(K+8*W+11)+2) s4 s5 := by
    have h := binary_repeat_state base encode multiply mul K W hm hw s4 half one hf4
      (by simp [s4,s2,s1]) (by simp [s4,s2,s1])
      (by simp [s4,s2,s1,h244]) (by simp [s4,s2,s1,h245])
    have he : Function.update (Function.update s4 240
        (encode ((fun a => mul a half)^[(s4 246).length] one))) 246 [] = s5 := by
      funext i
      by_cases hi : i=240 <;> by_cases hj : i=246 <;>
        simp [s5,s4,s2,s1,out,powerValue,Function.update_apply,hi,hj,h246]
    rw [he] at h
    simpa only [s4,Function.update_self,List.length_tail] using h
  have h6 : ExecutesIn (copy 240 252) (7*W+5) s5 s6 := by
    have h := copy_run 240 252 s5 (by decide) (by decide) (by decide)
      (by simp [s5,s1,h120])
    simpa [s6,s5,s1,h252] using h.mono (by simpa [s5] using (Nat.add_le_add_right (Nat.mul_le_mul_left 7 (hw out)) 5))
  have h7 : ExecutesIn (clear 240) (2*W+3) s6 s7 := by
    have h := clear_run 240 s6
    have he : Function.update s6 240 [] = s7 := by
      funext i
      by_cases hi : i=240 <;> simp [s6,s5,s7,s1,Function.update_apply,hi,h240]
    rw [he] at h
    exact h.mono (by simpa [s6,s5] using (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hw out)) 3))
  have h8 : ExecutesIn (clear 241) (2*W+3) s7 s8 := by
    have h := clear_run 241 s7
    have he : Function.update s7 241 [] = s8 := by
      funext i
      by_cases hi : i=241 <;> simp [s7,s8,s1,Function.update_apply,hi,h241]
    rw [he] at h
    exact h.mono (by simpa [s7,s1] using (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hw half)) 3))
  have h9 : ExecutesIn (clear 255) (2*W+3) s8
      (Function.update (Function.update s 255 []) 252 (encode out)) := by
    have h := clear_run 255 s8
    have he : Function.update s8 255 [] =
        Function.update (Function.update s 255 []) 252 (encode out) := by
      funext i
      by_cases hi : i=255 <;> simp [s8,Function.update_apply,hi]
    rw [he] at h
    exact h.mono (by simpa [s8,hhalf] using (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hw half)) 3))
  exact (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq h9)))))))).mono
    (by unfold powerBudget; omega)

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutDenominatorProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete extension-ring denominator program. It first lifts the actual
scalar-half word, then runs the paid native multiplication loop. -/
namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing
open IntegerRingLiftProgram

def value (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (zero one minusOne : ModelCode t d) (half : List Bool) (R : ℕ) : ModelCode t d :=
  let ops := RingProgram.modelProgram t a M cache
  powerValue (fun x y => (ops.mulRun x y).1)
    (cachedSignedValue t a M cache zero one minusOne half []) one R

theorem value_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (zero one minusOne : ModelCode t d)
    (hz : (RingProgram.modelRing t ht hd a M cache).decode zero=0)
    (ho : (RingProgram.modelRing t ht hd a M cache).decode one=1)
    (hm : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (half : List Bool) (R : ℕ) :
    (RingProgram.modelRing t ht hd a M cache).decode (value t a M cache zero one minusOne half R) =
      (BinaryArithmetic.toNat half : a.O t)^(R-1) := by
  let ops := RingProgram.modelRing t ht hd a M cache
  have he := CRTLocalProgram.iterate_mul_decode ops.decode
    (fun x y => (ops.mulRun x y).1) ops.mul_correct
    (cachedSignedValue t a M cache zero one minusOne half []) one (R-1)
  have hx : ops.decode (cachedSignedValue t a M cache zero one minusOne half []) =
      (BinaryArithmetic.toNat half : a.O t) := by
    have hx := signedValue_decode ops.decode (fun x y => (ops.mulRun x y).1)
      (fun x y => (ops.addRun x y).1) ops.mul_correct ops.add_correct
      zero one minusOne hz ho hm half []
    change ops.decode (signedValue (fun x y => (ops.mulRun x y).1)
      (fun x y => (ops.addRun x y).1) zero one minusOne half []) = _
    simpa using hx
  rw [ho,one_mul,hx] at he
  exact he

theorem value_inverse (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (zero one minusOne : ModelCode t d)
    (hz : (RingProgram.modelRing t ht hd a M cache).decode zero=0)
    (ho : (RingProgram.modelRing t ht hd a M cache).decode one=1)
    (hm : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (u : RingProgram.ScalarCode 3 t)
    (hu : (2:ZMod (3^t))*wordValue 3 t u=1) (R : ℕ) :
    (RingProgram.modelRing t ht hd a M cache).decode (value t a M cache zero one minusOne u.val R) *
      (2:a.O t)^(R-1)=1 := by
  have hh : (BinaryArithmetic.toNat u.val : a.O t)*(2:a.O t)=1 := by
    have hm := congrArg (LiftRing.of (a.F t)) hu
    simpa [wordValue, map_mul, map_one, map_ofNat, mul_comm] using hm
  rw [value_decode t ht hd a M cache zero one minusOne hz ho hm u.val R,← mul_pow,hh,one_pow]

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A denominator constructor consuming the actual ring-setup certificate.
The inverse-half fact comes from that executed setup, and the power is then
computed by the fixed native multiplication loop in the private bank. -/
namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
open SubexpLiftRing SubexpQuarticRing IntegerRingLiftProgram

def value (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (u : RingProgram.ScalarCode 3 t) (R : ℕ) : ModelCode t d :=
  LayoutDenominatorProgram.value t model M cache
    (LeafProgram.Constants.constantCode d cache.zero cache.zero)
    (LeafProgram.Constants.constantCode d cache.one cache.zero)
    (LeafProgram.Constants.constantCode d cache.minusOne cache.zero) u.val R

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramIntegerFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Final physical defect conversion, preserving all caller inputs and
removing the temporary numerator pair. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.IntegerFinish

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp RowSelectionProgram
open UniversalEntry

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := State 10 64

def Ready (a : Data) : Prop := ∀ j : Fin 64, j∈[53,54,0,1,4,5,6] → a.stacks j=[]
def output (a : Data) (p n : List Bool) : Fin 64 → List Bool :=
  Function.update (Function.update (Function.update (Function.update a.stacks 53 p) 54 n) 50 []) 51 []

def budget (a : Data) : ℕ :=
  9*(a.stacks 50).length+2*(a.stacks 51).length+
    100*((a.stacks 51).length+(a.stacks 45).length+1)^2+19

end SubexponentialSAT.SqrtLog.LayoutProgram.IntegerFinish

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramNumerator
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete universal numerator evaluation from encoded type words and the
paid unsigned coefficient cache. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open UniversalEntry RowSelectionProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := State 10 64

variable {r Q : ℕ}

def state (c : Saved) (regs : Fin 10 → Bool) (t : Fin Q)
    (u y : UniversalType r Q 1) (uc hc : List Bool) (result : WordPair) : Data :=
  ⟨regs,Function.update (Function.update (Function.update (Function.update
    (baseStacks c t u y) 2 uc) 3 hc) 50 result.1) 51 result.2⟩

end SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramIntegerEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Literal integer universal constraints from the actual numerator program.
The outer anchor test also suppresses the clearing diagonal outside the joint. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open UniversalEntry RowSelectionProgram MatrixExtendedEntryProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := State 10 64

variable {r Q : ℕ}

def output (c : Saved) (regs : Fin 10 → Bool) (t : Fin Q) (u y : UniversalType r Q 1)
    (result : WordPair) : Data :=
  ⟨regs,Function.update (Function.update
    (Numerator.state c regs t u y [] [] ([],[])).stacks 53 result.1) 54 result.2⟩

end SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionCallback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One actual bucket-record callback: select its indexed vertex and emit it. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open BitProgram StructuredCalls MatrixProgramSupport

theorem callback_eval (key vertex : List Bool) (pre rest : List (List Bool))
    (c : Context) (hblock : c.block = List.replicate pre.length true)
    (regs : Fin 8 → Bool) :
    ∃ n ≤ callbackBudget (bucketWord key (pre ++ vertex :: rest)) c.block c.address,
      ∃ rf, Eval callback n
        (ready regs { c with payload := (bucketWord key (pre ++ vertex :: rest)).reverse })
        (ready (finishRegs rf) (emitted { c with payload := [] } key vertex)) := by
  let payload := bucketWord key (pre ++ vertex :: rest)
  let clean := { c with payload := [] }
  obtain ⟨a, ha, hsa⟩ := transfer_eval (8 : Fin 19) 0 (by decide)
    (ready regs { c with payload := payload.reverse })
  have hea : a = state a.regs clean payload [] [] [] [] [] [] [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hsa]
    funext i
    fin_cases i <;> simp [ready, state, clean, StackRoutines.transferStacks]
  rw [hea] at ha
  obtain ⟨b, hb, hsb⟩ := MatrixProgramSupport.copy_eval (10 : Fin 19) 2 9
    (by decide) (by decide) (by decide)
    (state a.regs clean payload [] [] [] [] [] [] []) rfl
  have heb : b = state b.regs clean payload [] (List.replicate pre.length true)
      [] [] [] [] [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hsb]
    funext i
    fin_cases i <;> simp [state, clean, StackRoutines.copyStacks, hblock]
  rw [heb] at hb
  obtain ⟨ns, hns, rs, hs⟩ := selectCall_eval key vertex pre rest b.regs clean
  obtain ⟨re, he⟩ := emitCall_eval clean key vertex rs
  have hf : Eval (.seq (.base (.atom (.set 5 false)))
      (.seq (.base (.atom (.set 6 true))) (.base (.atom (.set 7 false))))) 3
      (ready re (emitted clean key vertex))
      (ready (finishRegs re) (emitted clean key vertex)) :=
    (Eval.base (.atom _ _)).seq ((Eval.base (.atom _ _)).seq (Eval.base (.atom _ _)))
  let n := (3 * payload.length + 3) + ((7 * c.block.length + 5) +
    (ns + ((PackingEntryEmitter.commandCost vertex key c.block c.address + 1) + 3)))
  refine ⟨n, ?_, re, ?_⟩
  · have hp : payload.length = 2 * key.length + 1 +
        ((words pre).length + (2 * vertex.length + 1 + (words rest).length)) := by
      simp only [payload, bucketWord, PackingBucketSelect.words_append, words,
        List.length_append, Encoding.length_frame]
    dsimp only [n, callbackBudget, PackingEntryEmitter.commandCost]
    change ns ≤ 21 * (payload.length + 1) at hns
    change (3 * payload.length + 3) + ((7 * c.block.length + 5) +
      (ns + ((44 * vertex.length + 24 * key.length + 31 * c.block.length +
        15 * c.address.length + 115 + 1) + 3))) ≤
      100 * (payload.length + c.block.length + c.address.length + 2)
    omega
  · have hrun := ha.seq (hb.seq (hs.seq (he.seq hf)))
    change Eval callback
      ((3 * payload.reverse.length + 3) + ((7 * c.block.length + 5) +
        (ns + ((PackingEntryEmitter.commandCost vertex key c.block c.address + 1) + 3))))
      (ready regs { c with payload := payload.reverse })
      (ready (finishRegs re) (emitted clean key vertex)) at hrun
    simpa only [n, List.length_reverse] using hrun

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionBlock
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Scan the ordered type buckets for one complete block. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open BitProgram StructuredCalls MatrixProgramSupport

theorem callback_entry_eval (i : ℕ) (e : Entry) (hi : i < e.2.length)
    (c : Context) (hblock : c.block = List.replicate i true) (regs : Fin 8 → Bool) :
    ∃ n ≤ callbackBudget (entryWord e) c.block c.address, ∃ rf,
      Eval callback n (ready regs { c with payload := (entryWord e).reverse })
        (ready (finishRegs rf) (emitted { c with payload := [] } e.1 (entryVertex i e))) := by
  have htake : (e.2.take i).length = i := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hblock' : c.block = List.replicate (e.2.take i).length true := by
    simpa only [htake] using hblock
  simpa only [entry_split i e hi, entryWord] using
    callback_eval e.1 (entryVertex i e) (e.2.take i) (e.2.drop (i + 1)) c hblock' regs

theorem block_loop_eval (i : ℕ) (entries : List Entry) (c : Context)
    (hblock : c.block = List.replicate i true)
    (hentries : ∀ e ∈ entries, i < e.2.length)
    (regs : Fin 8 → Bool) (suffix : List Bool) :
    ∃ n ≤ 1 + blockBudget i entries c, ∃ rf,
      Eval (RecordPrograms.loop ports callback) n
        (RecordPrograms.afterTag ports (base regs c) (entries.map entryWord) suffix)
        (RecordPrograms.state ports (base rf (emitEntries i entries c)) false true false suffix []) := by
  induction entries generalizing c regs with
  | nil =>
    refine ⟨1, by simp [blockBudget], regs, ?_⟩
    simpa only [List.map_nil, emitEntries, List.foldl_nil, RecordPrograms.afterTag] using
      (Eval.while_false (body := RecordPrograms.body ports callback)
        (a := RecordPrograms.state ports (base regs c) false true false suffix []) (by simp))
  | cons e es ih =>
    let a := base regs c
    let tail := Encoding.encodeList id (es.map entryWord) ++ suffix
    have hr : Eval (RecordPrograms.reader ports) (6 * (entryWord e).length + 4)
        (RecordPrograms.afterTag ports a ((e :: es).map entryWord) suffix)
        (RecordPrograms.state ports a false true false tail (entryWord e).reverse) := by
      simpa only [List.map_cons, RecordPrograms.afterTag, List.append_nil] using
        RecordPrograms.reader_eval ports a (entryWord e) tail [] true true false
    obtain ⟨nc, hnc, rc, hc⟩ := callback_entry_eval i e (hentries e (by simp))
      { c with keys := tail, payload := [] } hblock (parserRegs regs false true false)
    let d := emitted c e.1 (entryVertex i e)
    let b := base (finishRegs rc) d
    have hcb : Eval callback nc
        (RecordPrograms.state ports a false true false tail (entryWord e).reverse)
        (RecordPrograms.state ports b false true false tail []) := by
      simpa only [a, b, base, parser_state, parserRegs_finish, d, emitted] using hc
    have hbranch : Eval
        (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
          (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
        (RecordPrograms.state ports b false true false tail [])
        (RecordPrograms.afterTag ports b (es.map entryWord) suffix) := by
      apply Eval.ite_false (by simp)
      exact RecordPrograms.pop_list_eval ports b (es.map entryWord) suffix false true
    obtain ⟨nr, hnr, rf, hrest⟩ := ih d hblock
      (fun x hx => hentries x (by simp [hx])) (finishRegs rc)
    have hrun := Eval.while_true
      (show (RecordPrograms.afterTag ports a ((e :: es).map entryWord) suffix).regs ports.tag = true
        by simp [RecordPrograms.afterTag]) (hr.seq (hcb.seq hbranch)) hrest
    refine ⟨(6 * (entryWord e).length + 4 + (nc + 2)) + nr + 1, ?_, rf, ?_⟩
    · dsimp only at hnc
      dsimp only [d] at hnr
      simp only [blockBudget]
      omega
    · simpa only [RecordPrograms.loop, RecordPrograms.body, a, b, d, emitEntries,
        List.foldl_cons] using hrun

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingLeftoverStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual generation of ascending vertex indices and the leftover scan in
the fixed packing controller. -/

namespace SubexponentialSAT.Subexp.PackingProgram

open BitProgram StructuredCalls PackingProgramSupport

theorem vertices_call_stacks (input : Input) (n D : ℕ)
    (c : PackingExtraction.Context) (regs : Fin 16 → Bool) :
    (install (by decide : 5 ≤ 16) (by decide : 6 ≤ 48)
      (PackingPlumbing.run verticesSetup (extractionOutputState input n c regs))
      (AssignmentSeedRange.outputState D)).stacks = fun i =>
        if i = 5 then AssignmentSeedRange.seedRecords D
        else (extractionOutputState input n c regs).stacks i := by
  funext i
  fin_cases i <;>
    simp [install, PackingPlumbing.run, verticesSetup, PackingPlumbing.Op.next,
      extractionOutputState, inputState, AssignmentSeedRange.outputState,
      AssignmentSeedRange.state, StackRoutines.copyStacks, Fin.coe_ofNat_eq_mod]

end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GlobalBasisEntryCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete framed-word, comparison, and scalar-cell services for the
global matrix entry callback. Register 6 is the persistent row-kind flag. -/

namespace SubexponentialSAT.Subexp.GlobalBasisEntryCore

open BitProgram StructuredCalls SubexpScanPrimitives

def compare (left right : Fin 32) : Code :=
  .seq (copy left 17) (.seq (copy right 28) (.seq sealCall (pop 27)))

end SubexponentialSAT.Subexp.GlobalBasisEntryCore

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete incidence-entry program. Its read-only cache bank is200..211,
its input indices252/253, and the returned signed pair254/255. Ports212..251
belong to the caller and are outside every local subroutine map. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def compareBlocks : Code := liftCommand (GlobalBasisEntryCore.compare 0 1) 0 1 id blockPorts
def compareIndices : Code := liftCommand (GlobalBasisEntryCore.compare 0 1) 0 1 id indexPorts

def uncovered : Code := .seq compareIndices
  (.ite 7 (TupleProgram.pushConst 254 0 true) (.base .skip))

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def BaseReady (a : Data) : Prop :=
  (∀ j : Fin 256, j.val < 200 → a.stacks j=[]) ∧ a.stacks 254=[] ∧ a.stacks 255=[]

def metadataStacks (a : Data) (mr mc : GlobalBasisMetadata.Metadata) : Fin 256 → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update a.stacks 64 mr.block) 65 mr.typeCode)
      66 mr.rank) 67 mc.block) 68 mc.typeCode) 69 mc.rank

def prepareSize (a : Data) : ℕ :=
  (a.stacks 202).length+(a.stacks 203).length+(a.stacks 204).length+
  (a.stacks 205).length+(a.stacks 206).length+(a.stacks 207).length+
  (a.stacks 208).length+(a.stacks 209).length+(a.stacks 210).length+
  (a.stacks 211).length+(a.stacks 65).length+(a.stacks 68).length

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankFrameUncovered
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def metadataFieldsLength (a : Data) : ℕ :=
  ∑ i ∈ metadataIndices,(a.stacks (i.castAdd 56)).length
def MetadataReady (a : Data) : Prop :=
  ∀ j : Fin 256, j.val < 200 → (j.val < 64 ∨ 70 ≤ j.val) → a.stacks j=[]

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankFramePrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

def preparedStacks (a : Data) : Fin 256 → List Bool :=
  Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update
  (Function.update a.stacks 42 (a.stacks 202)) 43 (a.stacks 203))
    44 (a.stacks 204)) 45 (a.stacks 205)) 47 (a.stacks 206)) 48 (a.stacks 207))
    21 (a.stacks 208)) 22 (a.stacks 209)) 37 (a.stacks 210)) 26 (a.stacks 211))
    23 (a.stacks 65)) 24 (a.stacks 68)) 25 [true]

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankInner
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual cached universal-entry call, including all physical staging,
export and cleanup. The caller's private fiber-loop bank is unrestricted. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open RowSelectionProgram

variable {r Q : ℕ}

structure Cached (a : Data) (c : Numerator.Saved) (t : Fin Q)
    (u y : UniversalType r Q 1) : Prop where
  low : ∀ j : Fin 256, j.val < 64 → a.stacks j=[]
  temp : a.stacks 199=[]
  posEmpty : a.stacks 254=[]
  negEmpty : a.stacks 255=[]
  hp : a.stacks 202=c.hp
  hn : a.stacks 203=c.hn
  hw : a.stacks 204=c.width
  hpos : a.stacks 205=c.power.1
  hneg : c.power.2=[]
  hr : a.stacks 206=c.r
  ha : a.stacks 207=c.a
  colors : a.stacks 208=List.replicate r true
  nodes : a.stacks 209=List.replicate Q true
  node : a.stacks 210=List.replicate t.val true
  typeWidth : a.stacks 211=List.replicate (Q*r) true
  rowType : a.stacks 65=CollisionProgram.encodeType u
  colType : a.stacks 68=CollisionProgram.encodeType y

def finish (a : Data) (regs : Fin 16 → Bool) (result : WordPair) : Data :=
  ⟨regs,fun j => if j.val < 200 then [] else if j=255 then result.2
    else if j=254 then result.1 else a.stacks j⟩

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankCache
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q : ℕ}

/-- The persistent cache fields. There is deliberately no condition on the
caller's private accumulator and queue ports212..251. -/
structure CacheWords (a : Data) (c : Numerator.Saved) (t : Fin Q) : Prop where
  hp : a.stacks 202=c.hp
  hn : a.stacks 203=c.hn
  hw : a.stacks 204=c.width
  hpos : a.stacks 205=c.power.1
  hneg : c.power.2=[]
  hr : a.stacks 206=c.r
  ha : a.stacks 207=c.a
  colors : a.stacks 208=List.replicate r true
  nodes : a.stacks 209=List.replicate Q true
  node : a.stacks 210=List.replicate t.val true
  typeWidth : a.stacks 211=List.replicate (Q*r) true

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramIntegerCache
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid reusable integer-cache initialization. The runtime parameters A, R
and common width remain on20/21/22. Outputs are H-positive0, H-negative1,
binary clearing denominator2, and retained local width19. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open RowSelectionProgram LayoutProgramScalar

def state (regs : Fin 8 → Bool) (a r width la lr lw p n power counter : List Bool) : Data :=
  ⟨regs,![p,n,power,[],[],[],[],[],[],[],[],[],[],[],[],[],[],la,lr,lw,a,r,width,counter]⟩

end SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache

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

@[simp] theorem counterWord_setCounter (i : Fin 3) (word : Word) (a : Accumulator) :
    counterWord i (setCounter i word a) = word := by
  fin_cases i <;> simp [counterWord, setCounter]

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

/-! ## Forward-output service boundary -/

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual packed source dispatch. This program constructs each polynomial
source from computed metadata and raw scalar caches, not a supplied polynomial
table. The owner-fiber source sum is a separate outer traversal. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev Data := State 16 320

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end


