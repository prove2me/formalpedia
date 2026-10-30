-- Prove2me | Definitions.Def_OAIQ081S138
-- name    : OAIQ081S138
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:46:57.008351+00:00
-- url     : https://prove2.me/theorems/66ccf7f6-0374-42ac-9bf3-4d1f53e568d8
-- title:
--   Definitions bundle OAIQ081S138 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 17 declarations of OpenAI's Lean: 3 definitions and 14 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.ScaleBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.scale`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.initializeWorker`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLogSpace_FactorTableProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableProgram.lean), [`SubexponentialSAT_SqrtLog_CRTLocalProgramDifference`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramDifference.lean), [`SubexponentialSAT_SqrtLog_CRTLocalProgramHorner`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramHorner.lean), [`SubexponentialSAT_SqrtLog_CRTLocalProgramInverse`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramInverse.lean), [`SubexponentialSAT_SqrtLog_CRTLocalProgramInverseComplete`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramInverseComplete.lean), [`SubexponentialSAT_SqrtLog_CRTLocalProgramInverseTrace`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramInverseTrace.lean), [`SubexponentialSAT_SqrtLog_CRTLocalProgramLoops`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramLoops.lean), [`SubexponentialSAT_SqrtLog_HornerProgramServices`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HornerProgramServices.lean), [`SubexponentialSAT_SqrtLog_LeafParametersProgramNative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafParametersProgramNative.lean), [`SubexponentialSAT_SqrtLog_RingTripleBridge`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RingTripleBridge.lean), [`SubexponentialSAT_SubexpPolynomialIterationControl`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SubexpPolynomialIterationControl.lean).
--
--   **Imports.** It imports the bundles `OAIQ081S116`, `OAIQ081S117` and `OAIQ081S132` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S153` and `OAIQ081S156`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.correctionCommand_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.includeNodeCommand_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.inverseConstantsCommand_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor.scan_state_run`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ081S116
import Definitions.Def_OAIQ081S117
import Definitions.Def_OAIQ081S132

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

theorem matrixBits_eq_triples {B : ℕ} (rows : List (Row B)) :
    matrixBits rows = RingScan.tripleBits (matrixTriples rows) := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    simp only [matrixBits, matrixTriples, List.map_cons, List.flatten_cons, tripleBits_append]
    rw [rowBits_eq_triples, ih]
    rfl

theorem allTripleBits_eq_blocks {B : ℕ} (ms : List (List (Row B))) :
    allTripleBits ms = RingScan.blockBits (ms.map matrixTriples) := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp [allTripleBits, RingScan.blockBits, matrixBits_eq_triples, ih]

theorem matrixTriples_coordinateRows {B d : ℕ}
    (table : Fin d → Fin d → Fin d → Word B) (x y : RingProgram.Code (Word B) d) (k : Fin d) :
    matrixTriples (coordinateRows table x y k) = RingProgram.coordinateTriples table x y k := by
  simp [matrixTriples, coordinateRows, rowTriples, List.map_ofFn,
    RingProgram.coordinateTriples, Function.comp_def]

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPolynomialIterationControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Reusing the polynomial multiplication workspace in a runtime-counted
loop. The output on 244 is moved back to accumulator 240, with all temporary
bits erased. The loop itself is the verified unary controller. -/

namespace SubexponentialSAT.SubexpPolynomialIterationControl

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpPolynomialServiceControl (transfer transfer_run)

theorem repeat_run {S : Type*} (base : Store) (encode : S → List Bool)
    (iteration : Code) (f : S → S) (K : ℕ)
    (hstep : ∀ a counter, ExecutesIn iteration K (ready base encode a counter)
      (ready base encode (f a) counter)) (counter : List Bool) (a : S) :
    ExecutesIn (repeatLoop iteration) (counter.length * (K + 2) + 2)
      (ready base encode a counter) (ready base encode ((f^[counter.length]) a) []) := by
  intro regs
  obtain ⟨costs, n, regs', hv, hn⟩ := repeat_visits base encode iteration f K hstep counter regs a
  exact ⟨n, regs', hn, hv.eval⟩

end SubexponentialSAT.SubexpPolynomialIterationControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramLoops
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native loops used by independent-precision local Hermite CRT.

The arithmetic argument is a finite `Cmd`, never a semantic instruction.
`ServiceSpec` is the exact trace contract discharged by the native represented
ring/array callbacks. All iteration counts remain on runtime stack 246.
-/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem binary_repeat_run {C : Type*} (base : Store) (encode : C → List Bool)
    (code : Code) (op : C → C → C) (K W : ℕ)
    (hspec : ServiceSpec base encode code op K)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (factor seed : C) (hfactor : base 241 = encode factor)
    (h244 : base 244 = []) (h245 : base 245 = []) (counter : List Bool) :
    ExecutesIn (nativeRepeat (binaryStep code))
      (counter.length * (K + 8 * W + 11) + 2)
      (loopReady base encode seed counter)
      (loopReady base encode ((fun a => op a factor)^[counter.length] seed) []) := by
  have hstep (a : C) (count : List Bool) :
      ExecutesIn (binaryStep code) (K + 8 * W + 9)
        (loopReady base encode a count)
        (loopReady base encode (op a factor) count) := by
    have h := binaryStep_run base encode code op K W hspec hwidth
      (loopReady base encode a count) a factor
      (lowFrame_loopReady base encode a count)
      (by simp [loopReady, SubexpPolynomialIterationControl.ready])
      (by simpa [loopReady, SubexpPolynomialIterationControl.ready] using hfactor)
      (by simpa [loopReady, SubexpPolynomialIterationControl.ready] using h244)
      (by simpa [loopReady, SubexpPolynomialIterationControl.ready] using h245)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext i
    by_cases hi : i = 240 <;> by_cases hc : i = 246 <;>
      simp [loopReady, SubexpPolynomialIterationControl.ready, hi, hc]
  simpa only [nativeRepeat, loopReady,
    show K + 8 * W + 9 + 2 = K + 8 * W + 11 by omega] using
    SubexpPolynomialIterationControl.repeat_run base encode (binaryStep code)
      (fun a => op a factor) (K + 8 * W + 9) hstep counter seed

theorem binary_repeat_state {C : Type*} (base : Store) (encode : C → List Bool)
    (code : Code) (op : C → C → C) (K W : ℕ)
    (hspec : ServiceSpec base encode code op K)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (factor seed : C) (hf : LowFrame base s)
    (hseed : s 240 = encode seed) (hfactor : s 241 = encode factor)
    (h244 : s 244 = []) (h245 : s 245 = []) :
    ExecutesIn (nativeRepeat (binaryStep code))
      ((s 246).length * (K + 8 * W + 11) + 2) s
      (Function.update (Function.update s 240
        (encode ((fun a => op a factor)^[(s 246).length] seed))) 246 []) := by
  have h := binary_repeat_run s encode code op K W (serviceSpec_frame hspec hf)
    hwidth factor seed hfactor h244 h245 (s 246)
  have hi : loopReady s encode seed (s 246) = s := by
    simp [loopReady, SubexpPolynomialIterationControl.ready, ← hseed]
  rw [hi] at h
  exact h

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramHorner
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native fixed-control Horner iteration, shared by scalar nilpotent repair
and the independently truncated local polynomial inverse. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem hornerCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (z one seed : C) (hfactor : base 241 = encode z)
    (hone : base 220 = encode one) (hz : base 222 = encode z)
    (h120 : base 120 = []) (h244 : base 244 = []) (h245 : base 245 = [])
    (counter : List Bool) :
    ExecutesIn (hornerCommand multiply add)
      (counter.length * (Km + Ka + 34 * W + 36) + 2)
      (loopReady base encode seed counter)
      (loopReady base encode ((hornerValue mulOp addOp z one)^[counter.length] seed) []) := by
  have hstep (a : C) (count : List Bool) :
      ExecutesIn (hornerStep multiply add) (Km + Ka + 34 * W + 34)
        (loopReady base encode a count)
        (loopReady base encode (hornerValue mulOp addOp z one a) count) := by
    have h := hornerStep_run base encode multiply add mulOp addOp Km Ka W hm ha hwidth
      (loopReady base encode a count) a z one (lowFrame_loopReady base encode a count)
      (by simp [loopReady, SubexpPolynomialIterationControl.ready])
      (by simpa [loopReady, SubexpPolynomialIterationControl.ready] using hfactor)
      (by simpa [loopReady, SubexpPolynomialIterationControl.ready] using hone)
      (by simpa [loopReady, SubexpPolynomialIterationControl.ready] using hz)
      (by simpa [loopReady, SubexpPolynomialIterationControl.ready] using h120)
      (by simpa [loopReady, SubexpPolynomialIterationControl.ready] using h244)
      (by simpa [loopReady, SubexpPolynomialIterationControl.ready] using h245)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext i
    by_cases hi : i = 240 <;> by_cases hc : i = 246 <;>
      simp [loopReady, SubexpPolynomialIterationControl.ready, hi, hc]
  simpa only [hornerCommand, nativeRepeat, loopReady,
      show Km + Ka + 34 * W + 34 + 2 = Km + Ka + 34 * W + 36 by omega] using
    SubexpPolynomialIterationControl.repeat_run base encode (hornerStep multiply add)
      (hornerValue mulOp addOp z one) (Km + Ka + 34 * W + 34) hstep counter seed

theorem hornerCommand_state {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (z one seed : C) (hf : LowFrame base s)
    (hseed : s 240 = encode seed) (hfactor : s 241 = encode z)
    (hone : s 220 = encode one) (hz : s 222 = encode z)
    (h120 : s 120 = []) (h244 : s 244 = []) (h245 : s 245 = []) :
    ExecutesIn (hornerCommand multiply add)
      ((s 246).length * (Km + Ka + 34 * W + 36) + 2) s
      (Function.update (Function.update s 240
        (encode ((hornerValue mulOp addOp z one)^[(s 246).length] seed))) 246 []) := by
  have h := hornerCommand_run s encode multiply add mulOp addOp Km Ka W
    (serviceSpec_frame hm hf) (serviceSpec_frame ha hf) hwidth z one seed
    hfactor hone hz h120 h244 h245 (s 246)
  have hi : loopReady s encode seed (s 246) = s := by
    simp [loopReady, SubexpPolynomialIterationControl.ready, ← hseed]
  rw [hi] at h
  exact h

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramInverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native residue-power preparation with dynamic extension degree and ring
precision. Stack 209 contains a unary residue-size-minus-two exponent;
stack 212 independently contains the unary ring precision. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem seedCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply : Code) (mulOp : C → C → C) (K W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp K)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (a one : C) (hf : LowFrame base s)
    (ha : s 205 = encode a) (hone : s 207 = encode one)
    (h120 : s 120 = []) (h208 : s 208 = [])
    (h240 : s 240 = []) (h241 : s 241 = [])
    (h244 : s 244 = []) (h245 : s 245 = []) (h246 : s 246 = []) :
    ExecutesIn (seedCommand multiply)
      (((s 209).length + 1) * (K + 50 * W + 100)) s
      (seedState s encode a ((fun x => mulOp x a)^[(s 209).length] one)) := by
  let b := ((fun x => mulOp x a)^[(s 209).length] one)
  let s1 := Function.update s 240 (encode one)
  let s2 := Function.update s1 241 (encode a)
  let s3 := Function.update s2 246 (s 209)
  let s4 := Function.update s2 240 (encode b)
  have hf1 : LowFrame base s1 := lowFrame_update hf 240 (by decide) _
  have hf2 : LowFrame base s2 := lowFrame_update hf1 241 (by decide) _
  have hf3 : LowFrame base s3 := lowFrame_update hf2 246 (by decide) _
  have h1 : ExecutesIn (replace 207 240) (9 * W + 8) s s1 := by
    simpa [s1, hone] using replace_bounded s 207 240 W
      (by decide) (by decide) (by decide) h120
      (by simpa [hone] using hwidth one) (by simp [h240])
  have h2 : ExecutesIn (replace 205 241) (9 * W + 8) s1 s2 := by
    simpa [s1, s2, ha] using replace_bounded s1 205 241 W
      (by decide) (by decide) (by decide) (by simp [s1, h120])
      (by simpa [s1, ha] using hwidth a) (by simp [s1, h241])
  have h3 : ExecutesIn (replace 209 246) (7 * (s 209).length + 8) s2 s3 := by
    simpa [s3, s2, s1, h246] using replace_run s2 209 246
      (by decide) (by decide) (by decide) (by simp [s2, s1, h120])
  have h4 : ExecutesIn (nativeRepeat (binaryStep multiply))
      ((s 209).length * (K + 8 * W + 11) + 2) s3 s4 := by
    have h := binary_repeat_state base encode multiply mulOp K W hm hwidth
      s3 a one hf3 (by simp [s3, s2, s1]) (by simp [s3, s2])
      (by simp [s3, s2, s1, h244]) (by simp [s3, s2, s1, h245])
    have hc : (s3 246).length = (s 209).length := by simp [s3]
    rw [hc] at h
    have he : Function.update (Function.update s3 240 (encode b)) 246 [] = s4 := by
      funext i
      by_cases hi : i = 240 <;> by_cases hj : i = 246 <;>
        simp [s4, s3, s2, s1, Function.update_apply, hi, hj, h246]
    change ExecutesIn _ _ s3 (Function.update (Function.update s3 240 (encode b)) 246 []) at h
    rw [he] at h
    exact h
  have h5 : ExecutesIn (replace 240 208) (9 * W + 8) s4 (seedState s encode a b) := by
    have h := replace_bounded s4 240 208 W
      (by decide) (by decide) (by decide) (by simp [s4, s2, s1, h120])
      (by simpa [s4] using hwidth b) (by simp [s4, s2, s1, h208])
    have he : Function.update s4 208 (s4 240) = seedState s encode a b := by
      funext i
      by_cases hi : i = 240 <;> by_cases hj : i = 241 <;> by_cases hk : i = 208 <;>
        simp [s4, s2, s1, seedState, hi, hj, hk]
    rw [he] at h
    exact h
  have h := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  apply h.mono
  nlinarith

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramInverseTrace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem repairCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (z b zero one : C) (hf : LowFrame base s)
    (hacc : s 240 = encode z) (hright : s 241 = encode one)
    (hone : s 207 = encode one) (hzero : s 104 = encode zero)
    (hb : s 208 = encode b) (hz : s 222 = encode z)
    (h120 : s 120 = []) (h220 : s 220 = [])
    (h244 : s 244 = []) (h245 : s 245 = []) (h246 : s 246 = []) :
    ExecutesIn (repairCommand multiply add)
      (((s 212).length+1)*(Km+Ka+150*W+200)) s
      (repairState s encode
        (mulOp ((hornerValue mulOp addOp z one)^[(s 212).length] zero) b)) := by
  let g := ((hornerValue mulOp addOp z one)^[(s 212).length] zero)
  let v := mulOp g b
  let s1 := Function.update s 240 (encode zero)
  let s2 := Function.update s1 241 (encode z)
  let s3 := Function.update s2 220 (encode one)
  let s4 := Function.update s3 246 (s 212)
  let s5 := Function.update s3 240 (encode g)
  let s6 := Function.update s5 241 (encode b)
  let s7 := Function.update s6 240 (encode v)
  let s8 := Function.update s7 208 (encode v)
  have hf1 : LowFrame base s1 := lowFrame_update hf 240 (by decide) _
  have hf2 : LowFrame base s2 := lowFrame_update hf1 241 (by decide) _
  have hf3 : LowFrame base s3 := lowFrame_update hf2 220 (by decide) _
  have hf4 : LowFrame base s4 := lowFrame_update hf3 246 (by decide) _
  have hf5 : LowFrame base s5 := lowFrame_update hf3 240 (by decide) _
  have hf6 : LowFrame base s6 := lowFrame_update hf5 241 (by decide) _
  have h1 : ExecutesIn (replace 104 240) (9*W+8) s s1 := by
    simpa [s1, hzero] using replace_bounded s 104 240 W
      (by decide) (by decide) (by decide) h120
      (by simpa [hzero] using hwidth zero) (by simpa [hacc] using hwidth z)
  have h2 : ExecutesIn (replace 222 241) (9*W+8) s1 s2 := by
    simpa [s2, s1, hz] using replace_bounded s1 222 241 W
      (by decide) (by decide) (by decide) (by simp [s1, h120])
      (by simpa [s1, hz] using hwidth z) (by simpa [s1, hright] using hwidth one)
  have h3 : ExecutesIn (replace 207 220) (9*W+8) s2 s3 := by
    simpa [s3, s2, s1, hone] using replace_bounded s2 207 220 W
      (by decide) (by decide) (by decide) (by simp [s2, s1, h120])
      (by simpa [s2, s1, hone] using hwidth one) (by simp [s2, s1, h220])
  have h4 : ExecutesIn (replace 212 246) (7*(s 212).length+8) s3 s4 := by
    simpa [s4, s3, s2, s1, h246] using replace_run s3 212 246
      (by decide) (by decide) (by decide) (by simp [s3, s2, s1, h120])
  have h5 : ExecutesIn (hornerCommand multiply add)
      ((s 212).length*(Km+Ka+34*W+36)+2) s4 s5 := by
    have h := hornerCommand_state base encode multiply add mulOp addOp Km Ka W hm ha hwidth
      s4 z one zero hf4 (by simp [s4, s3, s2, s1]) (by simp [s4, s3, s2])
      (by simp [s4, s3]) (by simp [s4, s3, s2, s1, hz])
      (by simp [s4, s3, s2, s1, h120]) (by simp [s4, s3, s2, s1, h244])
      (by simp [s4, s3, s2, s1, h245])
    have hc : (s4 246).length = (s 212).length := by simp [s4]
    rw [hc] at h
    have he : Function.update (Function.update s4 240 (encode g)) 246 [] = s5 := by
      funext i
      by_cases hi : i = 240 <;> by_cases hj : i = 246 <;>
        simp [s5, s4, s3, s2, s1, Function.update_apply, hi, hj, h246]
    change ExecutesIn _ _ s4 (Function.update (Function.update s4 240 (encode g)) 246 []) at h
    rw [he] at h
    exact h
  have h6 : ExecutesIn (replace 208 241) (9*W+8) s5 s6 := by
    simpa [s6, s5, s3, s2, s1, hb] using replace_bounded s5 208 241 W
      (by decide) (by decide) (by decide) (by simp [s5, s3, s2, s1, h120])
      (by simpa [s5, s3, s2, s1, hb] using hwidth b)
      (by simpa [s5, s3, s2] using hwidth z)
  have h7 : ExecutesIn (binaryStep multiply) (Km+8*W+9) s6 s7 :=
    binaryStep_run base encode multiply mulOp Km W hm hwidth s6 g b hf6
      (by simp [s6, s5]) (by simp [s6])
      (by simp [s6, s5, s3, s2, s1, h244]) (by simp [s6, s5, s3, s2, s1, h245])
  have h8 : ExecutesIn (replace 240 208) (9*W+8) s7 s8 := by
    simpa [s8, s7] using replace_bounded s7 240 208 W
      (by decide) (by decide) (by decide) (by simp [s7, s6, s5, s3, s2, s1, h120])
      (by simpa [s7] using hwidth v)
      (by simpa [s7, s6, s5, s3, s2, s1, hb] using hwidth b)
  have h9 : ExecutesIn (SubexpLocalCRTSetup.clearMany [220,222,240,241]) (4*(2*W+3))
      s8 (repairState s encode v) := by
    have h := SubexpLocalCRTSetup.clearMany_run [220,222,240,241] s8 W (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · simpa [s8, s7, s6, s5, s3] using hwidth one
      · simpa [s8, s7, s6, s5, s3, s2, s1, hz] using hwidth z
      · simpa [s8, s7] using hwidth v
      · simpa [s8, s7, s6] using hwidth b)
    have he : SubexpLocalCRTSetup.cleared [220,222,240,241] s8 = repairState s encode v := by
      funext i
      simp only [repairState, SubexpLocalCRTSetup.cleared_apply]
      by_cases hi : i ∈ ([220,222,240,241] : List (Fin 256))
      · simp [hi]
      · simp only [ite_eq_right hi]
        have h220 : i ≠ 220 := by intro h; exact hi (by simp [h])
        have h222 : i ≠ 222 := by intro h; exact hi (by simp [h])
        have h240 : i ≠ 240 := by intro h; exact hi (by simp [h])
        have h241 : i ≠ 241 := by intro h; exact hi (by simp [h])
        simp [s8, s7, s6, s5, s3, s2, s1, Function.update_apply, h220, h240, h241]
    rw [he] at h
    exact h
  have h := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq h9)))))))
  apply h.mono
  nlinarith

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramInverseComplete
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete native scalar inversion. The counter on 212 is independent of
the later polynomial-jet counter on 243. The only changed persistent port is
208. No inverse, residue-field enumeration, or ring-element enumeration is
an instruction of the compiled program. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem inverseCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (a zero one minusOne : C) (hf : LowFrame base s)
    (ha0 : s 205 = encode a) (hz0 : s 104 = encode zero)
    (ho0 : s 207 = encode one) (hn0 : s 211 = encode minusOne)
    (h120 : s 120 = []) (h208 : s 208 = [])
    (h220 : s 220 = []) (h222 : s 222 = [])
    (h240 : s 240 = []) (h241 : s 241 = [])
    (h244 : s 244 = []) (h245 : s 245 = []) (h246 : s 246 = []) :
    ExecutesIn (inverseCommand multiply add)
      (inverseBudget (s 209).length (s 212).length Km Ka W) s
      (Function.update s 208 (encode (inverseValue mulOp addOp zero one minusOne a
        (s 209).length (s 212).length))) := by
  let b := ((fun x => mulOp x a)^[(s 209).length] one)
  let z := defectValue mulOp addOp a b minusOne one
  let v := mulOp ((hornerValue mulOp addOp z one)^[(s 212).length] zero) b
  let s1 := seedState s encode a b
  let s2 := defectState s1 encode z one
  have hf1 : LowFrame base s1 :=
    lowFrame_update (lowFrame_update (lowFrame_update hf 240 (by decide) _)
      241 (by decide) _) 208 (by decide) _
  have hf2 : LowFrame base s2 :=
    lowFrame_update (lowFrame_update (lowFrame_update hf1 240 (by decide) _)
      241 (by decide) _) 222 (by decide) _
  have h1 : ExecutesIn (seedCommand multiply)
      (((s 209).length+1)*(Km+50*W+100)) s s1 :=
    seedCommand_run base encode multiply mulOp Km W hm hwidth s a one hf
      ha0 ho0 h120 h208 h240 h241 h244 h245 h246
  have h2 : ExecutesIn (defectCommand multiply add) (2*Km+Ka+60*W+60) s1 s2 :=
    defectCommand_run base encode multiply add mulOp addOp Km Ka W hm ha hwidth
      s1 a b minusOne one hf1
      (by simp [s1, seedState]) (by simp [s1, seedState])
      (by simp [s1, seedState, ho0]) (by simp [s1, seedState, hn0])
      (by simp [s1, seedState, h120]) (by simp [s1, seedState, h222])
      (by simp [s1, seedState, h244]) (by simp [s1, seedState, h245])
  have h3 : ExecutesIn (repairCommand multiply add)
      (((s 212).length+1)*(Km+Ka+150*W+200)) s2 (Function.update s 208 (encode v)) := by
    have h := repairCommand_run base encode multiply add mulOp addOp Km Ka W hm ha hwidth
      s2 z b zero one hf2
      (by simp [s2, defectState]) (by simp [s2, defectState])
      (by simp [s2, defectState, s1, seedState, ho0])
      (by simp [s2, defectState, s1, seedState, hz0])
      (by simp [s2, defectState, s1, seedState]) (by simp [s2, defectState])
      (by simp [s2, defectState, s1, seedState, h120])
      (by simp [s2, defectState, s1, seedState, h220])
      (by simp [s2, defectState, s1, seedState, h244])
      (by simp [s2, defectState, s1, seedState, h245])
      (by simp [s2, defectState, s1, seedState, h246])
    have hc : (s2 212).length = (s 212).length := by simp [s2, defectState, s1, seedState]
    rw [hc] at h
    have he : repairState s2 encode v = Function.update s 208 (encode v) := by
      funext i
      by_cases h220i : i = 220 <;> by_cases h222i : i = 222 <;>
        by_cases h240i : i = 240 <;> by_cases h241i : i = 241 <;> by_cases h208i : i = 208 <;>
        simp [repairState, SubexpLocalCRTSetup.cleared_apply, s2, defectState,
          s1, seedState, h220i, h222i, h240i, h241i,
          h220, h222, h240, h241, h208i]
    change ExecutesIn _ _ s2 (repairState s2 encode v) at h
    rw [he] at h
    exact h
  have h := h1.seq (h2.seq h3)
  apply h.mono
  dsimp only [inverseBudget]
  nlinarith

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramDifference
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A physical inverse builder for a difference of two supplied nodes. The
residue exponent and nilpotence precision are the independent runtime inputs
209 and 212; no loop enumerates the lifted ring. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem differenceInverseCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka) (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (theta other zero one minusOne : C) (hf : LowFrame base s)
    (htheta : s 213 = encode theta) (hother : s 218 = encode other)
    (hzero : s 104 = encode zero) (hone : s 207 = encode one)
    (hminus : s 211 = encode minusOne) (h120 : s 120 = [])
    (h205 : s 205 = []) (h208 : s 208 = []) (h219 : s 219 = [])
    (h220 : s 220 = []) (h222 : s 222 = []) (h240 : s 240 = []) (h241 : s 241 = [])
    (h244 : s 244 = []) (h245 : s 245 = []) (h246 : s 246 = []) :
    ExecutesIn (differenceInverseCommand multiply add)
      (inverseBudget (s 209).length (s 212).length Km Ka W + Km+Ka+102*W+113) s
      (Function.update s 208 (encode (inverseValue mulOp addOp zero one minusOne
        (differenceValue mulOp addOp theta other minusOne) (s 209).length (s 212).length))) := by
  let delta := differenceValue mulOp addOp theta other minusOne
  let v := inverseValue mulOp addOp zero one minusOne delta (s 209).length (s 212).length
  let s1 := Function.update s 205 (encode delta)
  let s2 := Function.update s1 208 (encode v)
  have h1 : ExecutesIn (differenceCommand multiply add) (Km+Ka+100*W+110) s s1 :=
    differenceCommand_run base encode multiply add mulOp addOp Km Ka W hm ha hwidth
      s theta other minusOne hf htheta hother hminus h120 h205 h219 h240 h241 h244 h245
  have h2 : ExecutesIn (inverseCommand multiply add)
      (inverseBudget (s 209).length (s 212).length Km Ka W) s1 s2 := by
    have h := inverseCommand_run base encode multiply add mulOp addOp Km Ka W hm ha hwidth
      s1 delta zero one minusOne (lowFrame_update hf 205 (by decide) _)
      (by simp [s1]) (by simp [s1, hzero]) (by simp [s1, hone]) (by simp [s1, hminus])
      (by simp [s1, h120]) (by simp [s1, h208]) (by simp [s1, h220]) (by simp [s1, h222])
      (by simp [s1, h240]) (by simp [s1, h241]) (by simp [s1, h244])
      (by simp [s1, h245]) (by simp [s1, h246])
    simpa only [s2, s1, Function.update_of_ne (show (209 : Fin 256) ≠ 205 by decide),
      Function.update_of_ne (show (212 : Fin 256) ≠ 205 by decide)] using h
  have h3 : ExecutesIn (clear 205) (2*W+3) s2 (Function.update s 208 (encode v)) := by
    have h := clear_run 205 s2
    have he : Function.update s2 205 [] = Function.update s 208 (encode v) := by
      funext i
      by_cases hi : i = 205 <;> simp [s2, s1, Function.update_apply, hi, h205]
    rw [he] at h
    apply h.mono
    simp [s2, s1]
    have hw := hwidth delta
    omega
  exact (h1.seq (h2.seq h3)).mono (by omega)

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgramServices
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fully discharged native binary services for arbitrary coefficient-vector
length. Shared by Horner, local CRT and dense polynomial services. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram.Services

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open CRTLocalProgram (ServiceSpec)

theorem add_native_spec (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (base : Store)
    (h : NativeReady p t M cache table base) :
    ReconstructionProgram.RingAdapter.NativeSpec base (RingProgram.flat (d := d) (B := baseWidth p t)) RingScan.serviceAddProgram
      (fun x y => (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1)
      (RingScan.serviceAddBudget (baseWidth p t) d + 1) := by
  intro regs x y
  obtain ⟨rf, hr⟩ := RingScan.serviceAddProgram_run p t M cache x y regs
    (base 204) (base 202) (base 201) h.degree h.width
  refine ⟨rf, ?_⟩
  simpa only [ReconstructionProgram.RingAdapter.initialNative, ReconstructionProgram.RingAdapter.finalNative, nativeStacks_eq, h.modulus, h.zero,
    RingScan.serviceState, RingScan.serviceWorkState] using hr

theorem add_spec (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (base : Store)
    (h : NativeReady p t M cache table base) :
    ServiceSpec base (RingProgram.flat (d := d) (B := baseWidth p t)) add
      (fun x y => (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1)
      (addBudget (baseWidth p t) d) := by
  have hs := ReconstructionProgram.RingAdapter.command_spec base (RingProgram.flat (d := d) (B := baseWidth p t)) RingScan.serviceAddProgram
    (fun x y => (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1)
    (RingScan.serviceAddBudget (baseWidth p t) d + 1) (d * baseWidth p t) h.workspace
    (add_native_spec p t M cache table base h) (fun a => (RingProgram.flat_length a).le)
  convert hs using 1 <;> simp only [add, addBudget, h.degree] ; omega

end SubexponentialSAT.SqrtLog.HornerProgram.Services

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

def initializeWorker : OuterCode := SubexpSetupStorage.clearMany entryPorts

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native runtime leaf parameter production, integer guards, and paid setup.
The former composition modules are import-only compatibility shims. -/


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramBankRoots -/

/-! A fixed ten-comparison bit guard. All operands are runtime binary words.
This module states their data relation separately from parameter production. -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit

/-- Only these numeric values control loops or increase representation length.
The numeric result of a power is deliberately absent. -/
def scale (m : Model) : Instr → ℕ
  | .load _ bits => bits.length
  | .pow _ b _ _ _ => m.val b
  | .sqrt a _ _ => m.val a
  | .addConst _ k => k
  | _ => 2

def ScaleBound (B : ℕ) : List Instr → Model → Prop
  | [],_ => True
  | i::is,m => scale m i ≤ B ∧ ScaleBound B is (next m i)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayoutCost -/


end OAI.Algorithms
end


