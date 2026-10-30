-- Prove2me | Definitions.Def_OAIQ081S117
-- name    : OAIQ081S117
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:31:11.853375+00:00
-- url     : https://prove2.me/theorems/466f5ca0-efcf-4a72-933d-979fa8b5bec7
-- title:
--   Definitions bundle OAIQ081S117 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 10 definitions and 20 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.conversion`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.unaryCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.unaryCopy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell.Coeff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.RingAdapter.NativeSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTriple.blocks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTriple.coordinateRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTriple.matrices`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_CodeParametersProgramUnary`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramCell`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramBranches`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`, `SubexponentialSAT_SqrtLog_ReconstructionProgramRing`, `SubexponentialSAT_SqrtLog_RingProgramFold`, `SubexponentialSAT_SqrtLog_RingScanBridge`, `SubexponentialSAT_SqrtLog_RingScanContractBridge`, `SubexponentialSAT_SqrtLog_RingScanService`, `SubexponentialSAT_SqrtLog_RingScanServiceAdd`, `SubexponentialSAT_SqrtLog_RingScanServiceLifts`, `SubexponentialSAT_SqrtLog_RingTripleBridge`, `SubexponentialSAT_SqrtLog_RingTripleExpand`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S100`, `OAIQ081S101` and `OAIQ081S102` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S138`, `OAIQ081S139`, `OAIQ081S143`, `OAIQ081S144` and `OAIQ081S147`; the statement `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell.updateCell_eval`; the proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell.updateCell_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S100
import Definitions.Def_OAIQ081S101
import Definitions.Def_OAIQ081S102

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeParametersProgramUnary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Production sparse-code parameter program. Fixed arithmetic, minimum,
metadata identities and unary materialization are checked in one unit. -/

/-! Arithmetic identities used by the physical sparse-code parameter program. -/


/-! A concrete minimum operation used between two straight-line arithmetic
stages. The comparison consumes only two explicitly copied temporary words. -/


/-! Fixed finite arithmetic instructions for all sparse-code search metadata.
Ports 0 and 1 contain m and B. Outputs: q=5, D=9, t=11, tD=12,
local distance=15, r=18, rD=19, N=21. Unary conversion is a separate,
explicitly paid stage. -/


/-! Explicit paid binary-to-unary copies for code-search metadata. -/
namespace SubexponentialSAT.SqrtLog.CodeParametersProgram

open BitProgram StructuredCalls BinaryArithmetic LeafParametersProgram.Bank

abbrev conversion (o : Fin 64) : Cmd 8 77 :=
  liftCommand CounterConversions.unaryCmd 0 1 smallRegs (conversionPorts o)

abbrev unaryCopy (a o : Fin 64) : Cmd 8 77 := .seq (copyCmd a 62) (conversion o)

abbrev unaryCommand : Cmd 8 77 :=
  .seq (unaryCopy 9 24) <| .seq (unaryCopy 11 25) <| .seq (unaryCopy 12 26) <|
  .seq (unaryCopy 15 27) <| .seq (unaryCopy 18 28) <| .seq (unaryCopy 19 29) <|
  unaryCopy 21 30

end SubexponentialSAT.SqrtLog.CodeParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramCell
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native update of one arbitrary-degree ring coefficient in a persistent
flat polynomial array. Every scan, copy, and scalar addition is paid. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives
open SubexponentialSAT.SubexpJetCellProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev Coeff := DensePolynomialProgram.Coeff


end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramBranches
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime Boolean branch initialization and exhaustive odometer traces.
The only parameter in the enumeration command is its fixed real callback.
The high dimension is data, not finite control. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Code := Cmd 2 2

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches

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

abbrev Data := State 16 32
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan


/-! Fixed cleanup for the native scope-address scanner. -/


/-! Calls to the fixed record mapper inside the native scope scan. -/


/-! One native low-variable step, including its uncovered neutral factor. -/


/-! Runtime high-mask loop for the original-address incidence stream. -/


/-! Count the physical scope stream before constructing native incidence plans. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramRing
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source-preserving CRT adapters for the native arbitrary-degree ring
programs. The adapter is a fixed finite table. Its cost includes three input
copies, the actual native trace, output copying and cleanup. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.RingAdapter

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (LowFrame ServiceSpec)

/-- This contract refers to the actual native program trace. -/
abbrev NativeSpec {C : Type*} {l : ℕ} (base : _root_.OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store) (encode : C → List Bool)
    (p : Program 8 32 l) (op : C → C → C) (K : ℕ) : Prop :=
  ∀ (regs : Fin 8 → Bool) (a b : C), ∃ rf,
    RunsIn p K
      ((⟨regs, initialNative base (encode a) (encode b)⟩ : State 8 32).withPC (some p.entry))
      ((⟨rf, finalNative base (encode (op a b))⟩ : State 8 32).withPC none)

theorem nativeCall_run {C : Type*} {l : ℕ}
    (base : _root_.OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store) (encode : C → List Bool) (p : Program 8 32 l)
    (op : C → C → C) (K : ℕ) (hnative : NativeSpec base encode p op K)
    (s : _root_.OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store) (a b : C)
    (hinput : ∀ i, s (ports i) = initialNative base (encode a) (encode b) i) :
    ExecutesIn (nativeCall p) K s (callResult s (encode (op a b))) := by
  intro regs
  let d : Data := ⟨regs, s⟩
  let localIn := projectState registers ports d
  obtain ⟨rf, n, hn, ht⟩ := hnative localIn.regs a b
  have hi : localIn.stacks = initialNative base (encode a) (encode b) := funext hinput
  let localOut : State 8 32 := ⟨rf, finalNative base (encode (op a b))⟩
  have trace : Trace p n (localIn.withPC (some p.entry)) (localOut.withPC none) := by
    simpa only [localOut, ← hi] using ht
  have hr := eval_call_from_state p registers ports d registers.injective ports.injective trace
  have hout : localOut.stacks = Function.update (Function.update
      (Function.update (Function.update localIn.stacks 8 []) 9 []) 11 []) 0 (encode (op a b)) := by
    rw [hi]
    funext i
    fin_cases i <;> simp [localOut, finalNative, initialNative, nativeStacks]
  have hbase : Function.extend ports localIn.stacks d.stacks = d.stacks :=
    congrArg StructuredProgram.State.stacks (embedState_project registers ports d registers.injective ports.injective)
  have hs : (embedState registers ports d localOut).stacks = callResult s (encode (op a b)) := by
    change Function.extend ports localOut.stacks d.stacks = _
    rw [hout, ProgramLinking.extend_update ports.injective,
      ProgramLinking.extend_update ports.injective, ProgramLinking.extend_update ports.injective,
      ProgramLinking.extend_update ports.injective, hbase]
    rfl
  have he : embedState registers ports d localOut =
      (⟨(embedState registers ports d localOut).regs, callResult s (encode (op a b))⟩ : Data) :=
    SubexpScanPrimitives.state_ext rfl hs
  rw [he] at hr
  exact ⟨n, _, hn, hr⟩

theorem command_spec {C : Type*} {l : ℕ}
    (base : _root_.OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store) (encode : C → List Bool) (p : Program 8 32 l)
    (op : C → C → C) (K W : ℕ) (hready : Ready base)
    (hnative : NativeSpec base encode p op K) (hw : ∀ a, (encode a).length ≤ W) :
    ServiceSpec base encode (command p) op (K + 23 * W + 7 * (base 204).length + 23) := by
  intro s a b hf ha hb ho ht
  have hs (i : Fin 32) : s (ports i) = finalNative base [] i :=
    (hf (ports i) (ports_low i)).trans (hready.2 i)
  have h120 : s 120 = [] := (hf 120 (by decide)).trans hready.1
  have h128 : s 128 = [] := by simpa [ports, finalNative, nativeStacks] using hs 0
  have h136 : s 136 = [] := by simpa [ports, finalNative, nativeStacks] using hs 8
  have h137 : s 137 = [] := by simpa [ports, finalNative, nativeStacks] using hs 9
  have h139 : s 139 = [] := by simpa [ports, finalNative, nativeStacks] using hs 11
  have h204 : s 204 = base 204 := hf 204 (by decide)
  let s1 := Function.update s 136 (encode a)
  let s2 := Function.update s1 137 (encode b)
  let s3 := Function.update s2 139 (base 204)
  let s4 := Function.update s 128 (encode (op a b))
  let s5 := Function.update s4 244 (encode (op a b))
  have h1 : ExecutesIn (copy 240 136) (7 * (encode a).length + 5) s s1 := by
    simpa only [ha, h136, List.append_nil, s1] using
      copy_run 240 136 s (by decide) (by decide) (by decide) h120
  have h2 : ExecutesIn (copy 241 137) (7 * (encode b).length + 5) s1 s2 := by
    have h := copy_run 241 137 s1 (by decide) (by decide) (by decide)
      (by simp [s1, h120])
    simpa [s1, s2, hb, h137] using h
  have h3 : ExecutesIn (copy 204 139) (7 * (base 204).length + 5) s2 s3 := by
    have h := copy_run 204 139 s2 (by decide) (by decide) (by decide)
      (by simp [s2, s1, h120])
    simpa [s3, s2, s1, h204, h139] using h
  have hin : ∀ i, s3 (ports i) = initialNative base (encode a) (encode b) i := by
    intro i
    have h := hs i
    fin_cases i <;> simp_all [s3, s2, s1, ports, initialNative, finalNative, nativeStacks]
  have he : callResult s3 (encode (op a b)) = s4 := by
    funext i
    by_cases h1 : i = 136 <;> by_cases h2 : i = 137 <;>
      by_cases h3 : i = 139 <;> by_cases h4 : i = 128 <;>
      simp [callResult, s3, s2, s1, s4, h1, h2, h3, h4,
        h136, h137, h139]
  have h4 : ExecutesIn (nativeCall p) K s3 s4 := by
    simpa only [he] using nativeCall_run base encode p op K hnative s3 a b hin
  have h5 : ExecutesIn (copy 128 244) (7 * (encode (op a b)).length + 5) s4 s5 := by
    have h := copy_run 128 244 s4 (by decide) (by decide) (by decide)
      (by simp [s4, h120])
    simpa [s5, s4, ho] using h
  have h6 : ExecutesIn (clear 128) (2 * (encode (op a b)).length + 3) s5
      (Function.update s 244 (encode (op a b))) := by
    have h := clear_run 128 s5
    have he : Function.update s5 128 [] = Function.update s 244 (encode (op a b)) := by
      funext i
      by_cases h1 : i = 128 <;> by_cases h2 : i = 244 <;>
        simp [s5, s4, h1, h2, h128]
    rw [he] at h
    simpa [s5, s4] using h
  have h := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))
  apply h.mono
  have hwa := hw a
  have hwb := hw b
  have hwc := hw (op a b)
  omega

end SubexponentialSAT.SqrtLog.ReconstructionProgram.RingAdapter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramFold
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A : Type*} [CommRing A]

theorem coordinateMulRun_eq_dot (ops : RingProgram C) {d : ℕ}
    (table : Fin d → Fin d → Fin d → C) (x y : Code C d) (k : Fin d) :
    coordinateMulRun ops table x y k = dotTriplesRun ops (coordinateTriples table x y k) := by
  simp [coordinateMulRun, dotTriplesRun, coordinateTriples, List.map_flatten,
    List.map_ofFn, Function.comp_def]

section Words

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.BinaryArithmetic

variable (p t : ℕ) [Fact p.Prime]
variable (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t) (cache : ScalarCache p t)

theorem accumulateTriplesRun_canonical (xs : List (Triple (ScalarCode p t)))
    (z : ScalarCode p t) (hz : BinaryArithmetic.toNat z.val < p^t) :
    BinaryArithmetic.toNat (accumulateTriplesRun (scalarProgram p t M cache) xs z).1.val < p^t := by
  induction xs generalizing z with
  | nil => exact hz
  | cons x xs ih =>
    apply ih
    exact SubexponentialSAT.SubexpPreparedQuartic.wordAdd_canonical p t M _ _

theorem dotTriplesRun_canonical (xs : List (Triple (ScalarCode p t)))
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) :
    BinaryArithmetic.toNat (dotTriplesRun (scalarProgram p t M cache) xs).1.val < p^t := by
  cases xs with
  | nil => exact hz
  | cons x xs => exact sumRun_canonical p t M cache _ _

/-- A left-to-right streaming accumulator agrees byte-for-byte with the
callback's right-associated sum, not only after semantic decoding. -/
theorem accumulateTriplesRun_eq_dot (xs : List (Triple (ScalarCode p t)))
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) :
    (accumulateTriplesRun (scalarProgram p t M cache) xs cache.zero).1 =
      (dotTriplesRun (scalarProgram p t M cache) xs).1 := by
  apply word_eq_of_value p t
  · exact accumulateTriplesRun_canonical p t M cache xs cache.zero hz
  · exact dotTriplesRun_canonical p t M cache xs hz
  · have ha := accumulateTriplesRun_correct (scalarRing p t M cache) xs cache.zero
    have hd := dotTriplesRun_correct (scalarRing p t M cache) xs
    change wordValue p t _ = wordValue p t _
    change wordValue p t _ = wordValue p t cache.zero + _ at ha
    rw [cache.zero_correct, zero_add] at ha
    exact ha.trans hd.symm

end Words
end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanBridge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact byte interfaces between the semantic ring callbacks and fixed native
flat-stack scanners. Materializing the input vectors/triples is a separate,
explicitly charged caller operation. -/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- The flat input/output of the native scanner is precisely the semantic
coefficient-vector add callback, including exact canonical result words. -/
theorem addRun_native (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (x y : RingProgram.Code (Word (baseWidth p t)) d)
    (regs : Fin 8 → Bool) (count width : List Bool)
    (hcount : count.length = d) (hwidth : width.length = baseWidth p t) :
    ∃ finalRegs, RunsIn addVectorProgram
      (d * (6000 * (baseWidth p t + 1)^2 + 34 * baseWidth p t + 29) + 6)
      ((addState regs M.bits [] [] (RingProgram.flat x) (RingProgram.flat y) [] count width).withPC
        (some addVectorProgram.entry))
      ((addState finalRegs M.bits
        (RingProgram.flat (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1)
        [] [] [] [] [] width).withPC none) := by
  obtain ⟨rf, hrun⟩ := addVectorProgram_run p t M
    (List.ofFn fun i : Fin d => (x i, y i)) regs count width
    (by simpa using hcount) hwidth
  refine ⟨rf, ?_⟩
  simp only [List.length_ofFn, leftBits_map, rightBits_map, sumBits_map,
    List.map_ofFn] at hrun
  simpa only [Function.comp_def, Prod.fst, Prod.snd, RingProgram.flat,
    RingProgram.addRun, RingProgram.tabulateRun_eq, RingProgram.scalarProgram] using hrun

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanContractBridge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Whole-vector native multiplication after explicitly paid triple expansion. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem multiplicationBlocks_uniform {d B : ℕ}
    (table : Fin d → Fin d → Fin d → Word B) (x y : RingProgram.Code (Word B) d)
    (b : List (WordTriple B)) (hb : b ∈ multiplicationBlocks table x y) : b.length = d*d := by
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hb
  exact RingProgram.coordinateTriples_length table x y k

theorem contractBits_map (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (seed : Word (baseWidth p t))
    (blocks : List (List (WordTriple (baseWidth p t)))) :
    contractBits p t M seed blocks =
      (blocks.map fun b => (foldTriples p t M seed b).val).flatten := by
  induction blocks with
  | nil => rfl
  | cons b bs ih => simp only [contractBits, List.map_cons, List.flatten_cons, ih]

theorem contractBits_mulRun (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (x y : RingProgram.Code (Word (baseWidth p t)) d) :
    contractBits p t M cache.zero (multiplicationBlocks table x y) =
      RingProgram.flat (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1 := by
  simp only [contractBits_map, multiplicationBlocks, List.map_ofFn,
    RingProgram.flat, RingProgram.mulRun, RingProgram.tabulateRun_eq]
  congr 2
  funext k
  dsimp only [Function.comp_apply]
  rw [foldTriples_eq_accumulate p t M cache,
    RingProgram.accumulateTriplesRun_eq_dot p t M cache _ hz,
    ← RingProgram.coordinateMulRun_eq_dot]

/-- A fixed native instruction table computes the complete bilinear product
from a k-major triple stream. All contraction work is charged. The input
format does not claim that generating the stream or table is free. -/
theorem mulRun_contract_native (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (x y : RingProgram.Code (Word (baseWidth p t)) d)
    (regs : Fin 8 → Bool) (width suffix outer inner : List Bool)
    (ho : outer.length = d) (hi : inner.length = d*d) (hw : width.length = baseWidth p t) :
    ∃ rf, RunsIn contractVectorProgram
      (d * (d*d * (18000 * (baseWidth p t + 1)^2 + 48 * baseWidth p t + 51)
        + 13 * baseWidth p t + 18) + 6)
      ((contractState regs M.bits [] (blockBits (multiplicationBlocks table x y) ++ suffix)
        [] width outer inner cache.zero.val []).withPC (some contractVectorProgram.entry))
      ((contractState rf M.bits
        (RingProgram.flat (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1)
        suffix [] width [] inner cache.zero.val []).withPC none) := by
  obtain ⟨rf, hr⟩ := contractVectorProgram_run p t M (multiplicationBlocks table x y)
    cache.zero regs width suffix outer inner (by simpa using ho)
    (fun b hb => hi.trans (multiplicationBlocks_uniform table x y b hb).symm) hw
  refine ⟨rf, ?_⟩
  simpa only [multiplicationBlocks_length, hi, contractBits_mulRun p t M cache hz] using hr

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleExpand
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

theorem matrixStep_eval (B : ℕ) (s : Store) (rows : List (Row B))
    (tail : List Bool) (regs : Fin 2 → Bool)
    (hfit : MatrixFits s rows) (hw : s.width.length = B) :
    ∃ n ≤ 200 * (s.degree.length + 1)^2 * (B + 1), ∃ regs',
      Eval matrixStep n
        (state regs {s with xs := [], ys := [], held := [], table := tableBits rows ++ tail, ic := [], jc := []})
        (state regs' {s with xs := [], ys := [], held := [], table := tail, ic := [], jc := [], out := (matrixBits rows).reverse ++ s.out}) := by
  obtain ⟨r₁, hs⟩ := startMatrix_eval
    {s with ys := [], held := [], table := tableBits rows ++ tail, jc := []} regs
  obtain ⟨n, hn, r₂, hi⟩ := iScan_eval B s rows tail s.degree r₁ hfit.2.1 hfit.2.2 hw
  refine ⟨7 * s.x.length + 7 * s.degree.length + 10 + n, ?_, r₂, ?_⟩
  · have hxl : s.x.length = s.degree.length * B := by
      rw [← hfit.1, xBits_length, ← hfit.2.1]
    rw [← hfit.2.1] at hn
    nlinarith [sq_nonneg (s.degree.length : ℤ)]
  · have hi' := hi
    rw [hfit.1] at hi'
    exact hs.seq hi'

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleBridge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The input/output of the dynamic expander is exactly the k-major table and
triple stream used by the native ring contraction. `List.ofFn` below describes
the serialized input and theorem; the fixed program builds the repeated stream
by actual counted loops and paid source copies. -/
namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpQuarticRing

def coordinateRows {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B)
    (x y : RingProgram.Code (Word B) d) (k : Fin d) : List (Row B) :=
  List.ofFn fun i : Fin d => (x i, List.ofFn fun j : Fin d => (y j, table i j k))

def matrices {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B)
    (x y : RingProgram.Code (Word B) d) : List (List (Row B)) :=
  List.ofFn fun k : Fin d => coordinateRows table x y k

def blocks {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B)
    (x y : RingProgram.Code (Word B) d) : List (List (RingScan.WordTriple B)) :=
  List.ofFn fun k : Fin d => RingProgram.coordinateTriples table x y k

theorem table_encoding {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B)
    (x y : RingProgram.Code (Word B) d) :
    allTableBits (matrices table x y) = tableEncoding table := by
  simp [allTableBits_map, matrices, coordinateRows, tableBits_map,
    rightBits_map, List.map_ofFn, tableEncoding, Function.comp_def]

theorem matrices_fit {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B)
    (x y : RingProgram.Code (Word B) d) (degree width : List Bool)
    (hd : degree.length = d) :
    ∀ m ∈ matrices table x y,
      MatrixFits (layout (RingProgram.flat x) (RingProgram.flat y) degree width) m := by
  intro m hm
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hm
  refine ⟨?_, ?_, ?_⟩
  · simp [coordinateRows, xBits_map, List.map_ofFn, RingProgram.flat, layout, Function.comp_def]
  · simpa [coordinateRows, layout] using hd
  · intro r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    constructor
    · simp [leftBits_map, List.map_ofFn, RingProgram.flat, layout, Function.comp_def]
    · simpa [layout] using hd

theorem rowBits_eq_triples {B : ℕ} (x : Word B) (pairs : List (Word B × Word B)) :
    rowBits x.val pairs = RingScan.tripleBits (rowTriples (x, pairs)) := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih => simpa [rowBits, rowTriples, RingScan.tripleBits, List.append_assoc] using ih

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanServiceAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- Common service ABI for addition. Caller context is preserved by a fixed
program lift, and every coefficient operation is included in the bound. -/
theorem serviceAdd_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (x y : RingProgram.Code (Word (baseWidth p t)) d) (regs : Fin 8 → Bool)
    (degree width table : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t) :
    ∃ n ≤ serviceAddBudget (baseWidth p t) d, ∃ rf, Eval serviceAdd n
      (serviceState regs M.bits [] (RingProgram.flat x) (RingProgram.flat y) degree width cache.zero.val table)
      (serviceState rf M.bits
        (RingProgram.flat (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1)
        [] [] [] width cache.zero.val table) := by
  obtain ⟨rf, n, hn, ht⟩ := addRun_native p t M cache x y regs degree width hd hw
  have he := eval_call_lifted addVectorProgram id serviceAddPorts
    (serviceState regs M.bits [] (RingProgram.flat x) (RingProgram.flat y) degree width cache.zero.val table)
    Function.injective_id serviceAddPorts_injective ht
  exact ⟨n, hn, rf, by simpa only [embed_serviceAdd] using he⟩

theorem serviceAddProgram_run (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (x y : RingProgram.Code (Word (baseWidth p t)) d) (regs : Fin 8 → Bool)
    (degree width table : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t) :
    ∃ rf, RunsIn serviceAddProgram (serviceAddBudget (baseWidth p t) d + 1)
      ((serviceState regs M.bits [] (RingProgram.flat x) (RingProgram.flat y) degree width cache.zero.val table).withPC
        (some serviceAddProgram.entry))
      ((serviceState rf M.bits
        (RingProgram.flat (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1)
        [] [] [] width cache.zero.val table).withPC none) := by
  obtain ⟨n, hn, rf, ht⟩ := serviceAdd_eval p t M cache x y regs degree width table hd hw
  exact ⟨rf, n+1, Nat.add_le_add_right hn 1, compiled_halt_trace ht 8 0⟩

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanServiceLifts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem serviceContract_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (x y : RingProgram.Code (Word (baseWidth p t)) d) (regs : Fin 8 → Bool)
    (width outer inner : List Bool)
    (ho : outer.length = d) (hi : inner.length = d*d) (hw : width.length = baseWidth p t) :
    ∃ n ≤ d*(d*d*(18000*(baseWidth p t+1)^2+48*baseWidth p t+51)+13*baseWidth p t+18)+6,
      ∃ rf, Eval serviceContract n
      (serviceWorkState regs ⟨M.bits, [], [], blockBits (multiplicationBlocks table x y),
        [], width, cache.zero.val, RingTriple.tableEncoding table, outer, inner, [], [], []⟩)
      (serviceWorkState rf ⟨M.bits,
        RingProgram.flat (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1,
        [], [], [], width, cache.zero.val, RingTriple.tableEncoding table, [], inner, [], [], []⟩) := by
  obtain ⟨rf, n, hn, ht⟩ := mulRun_contract_native p t M cache hz table x y regs width [] outer inner ho hi hw
  simp only [List.append_nil] at ht
  let s : ServiceStore := ⟨M.bits, [], [], blockBits (multiplicationBlocks table x y),
        [], width, cache.zero.val, RingTriple.tableEncoding table, outer, inner, [], [], []⟩
  let a := contractState regs s.modulus [] s.y [] s.width s.outer s.inner s.zero []
  let b := contractState rf s.modulus
    (RingProgram.flat (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1)
    [] [] s.width [] s.inner s.zero []
  have he := eval_call_lifted contractVectorProgram id serviceContractPorts (serviceWorkState regs s)
    Function.injective_id serviceContractPorts_injective (a := a) (b := b) ht
  dsimp only [a, b] at he
  rw [embed_contract_service, embed_contract_service] at he
  exact ⟨n, hn, rf, by simpa only [s] using he⟩


end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanService
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed native service for arbitrary-degree coefficient-ring products. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem tripleBits_length {B : ℕ} (triples : List (WordTriple B)) :
    (tripleBits triples).length = triples.length * (3*B) := by
  induction triples with
  | nil => simp [tripleBits]
  | cons x xs ih =>
      have h1 : x.1.val.length = B := x.1.property
      have h2 : x.2.1.val.length = B := x.2.1.property
      have h3 : x.2.2.val.length = B := x.2.2.property
      simp [tripleBits, ih, h1, h2, h3]
      ring

theorem blockBits_length_uniform {B m : ℕ} (blocks : List (List (WordTriple B)))
    (hm : ∀ b ∈ blocks, b.length = m) :
    (blockBits blocks).length = blocks.length * (m*(3*B)) := by
  induction blocks with
  | nil => simp [blockBits]
  | cons b bs ih =>
      have hb := hm b (by simp)
      have hs := ih (fun b hb => hm b (by simp [hb]))
      simp only [blockBits, List.length_append, tripleBits_length, hb, hs, List.length_cons]
      ring

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end


