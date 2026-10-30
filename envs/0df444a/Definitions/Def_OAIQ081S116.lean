-- Prove2me | Definitions.Def_OAIQ081S116
-- name    : OAIQ081S116
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:29:13.11101+00:00
-- url     : https://prove2.me/theorems/58345e60-439b-4e0b-b54f-be4414f0a97f
-- title:
--   Definitions bundle OAIQ081S116 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 10 definitions, 2 inductive types or structures and 15 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Native.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.NativeInverse.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.NativeInverse.value`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.Services.NativeReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.saveOld`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.AdmissibleCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout.powerCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTriple.matrixTriples`, `OAI.Algorithms.SubexponentialSAT.SubexpPolynomialIterationControl.state`, `OAI.Algorithms.SubexponentialSAT.UnaryForPrograms.Visits`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_CRTLocalProgram`, `SubexponentialSAT_SqrtLog_CRTLocalProgramCall`, `SubexponentialSAT_SqrtLog_CRTLocalProgramDifference`, `SubexponentialSAT_SqrtLog_CRTLocalProgramHorner`, `SubexponentialSAT_SqrtLog_CRTLocalProgramInverseTrace`, `SubexponentialSAT_SqrtLog_CRTLocalProgramLoops`, `SubexponentialSAT_SqrtLog_CRTLocalProgramNative`, `SubexponentialSAT_SqrtLog_CRTLocalProgramNativeInverse`, `SubexponentialSAT_SqrtLog_HornerProgramServices`, `SubexponentialSAT_SqrtLog_LayoutBinomialProgramCell`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`, `SubexponentialSAT_SqrtLog_RingTripleBridge`, `SubexponentialSAT_SubexpPolynomialIterationControl`, `SubexponentialSAT_UnaryForPrograms`.
--
--   **Imports.** It imports the bundles `OAIQ081S100`, `OAIQ081S101` and `OAIQ081S102` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S138`, `OAIQ081S139`, `OAIQ081S140`, `OAIQ081S141`, `OAIQ081S142`, `OAIQ081S144`, `OAIQ081S147`, `OAIQ081S148` and `OAIQ081S151`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Native.command_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localCommand_run`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localCommand_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.prepareLocalInverse_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.command_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowLoop_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.zeroRows_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.initializeTarget_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.loadCoordinate_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_scan_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.origin_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.command_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgram.Padding.streaming_run`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ081S100
import Definitions.Def_OAIQ081S101
import Definitions.Def_OAIQ081S102

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_UnaryForPrograms
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control unary-counted callbacks

The counter is a Boolean stack whose length is the iteration count. Its bits
are ignored. The controller pops before each callback and tests the presence
flag; callbacks preserve the remaining counter tail and may clobber all
registers. Every observation contains an actual callback evaluation.
-/

namespace SubexponentialSAT.UnaryForPrograms

open BitProgram StructuredProgram
open CounterForPrograms (budgetSum)

variable {R S : ℕ}

theorem pop_eval (p : Ports R S) (d : Data R S) :
    StructuredCalls.Eval (popCmd p) 1 d (popped p d) := .base (.atom _ _)

inductive Visits (p : Ports R S) (body : StructuredCalls.Cmd R S) :
    List ℕ → ℕ → Data R S → Data R S → Prop
  | done (d : Data R S) (hempty : d.stacks p.counter = []) :
      Visits p body [] 2 d (popped p d)
  | step {d e f : Data R S} {nb nt : ℕ} {costs : List ℕ}
      (hne : d.stacks p.counter ≠ [])
      (hbody : StructuredCalls.Eval body nb (popped p d) e)
      (hcounter : e.stacks p.counter = (popped p d).stacks p.counter)
      (tail : Visits p body costs nt e f) :
      Visits p body (nb :: costs) (nb + nt + 2) d f

theorem Visits.loop_eval {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {costs : List ℕ} {n : ℕ} {d e : Data R S} (h : Visits p body costs n d e) :
    ∃ m, n = 1 + m ∧ StructuredCalls.Eval (loopCmd p body) m (popped p d) e := by
  induction h with
  | done d he =>
      exact ⟨1, rfl, .while_false (by simp [he])⟩
  | @step d e f nb nt costs hne hb hc ht ih =>
      obtain ⟨m, hm, he⟩ := ih
      have hf : (popped p d).regs p.flag = true := by
        rw [popped_flag]
        cases hw : d.stacks p.counter with
        | nil => exact False.elim (hne hw)
        | cons b bs => rfl
      refine ⟨(nb + 1) + m + 1, by omega, ?_⟩
      exact .while_true hf (hb.seq (pop_eval p e)) he

theorem Visits.eval {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {costs : List ℕ} {n : ℕ} {d e : Data R S} (h : Visits p body costs n d e) :
    StructuredCalls.Eval (forCmd p body) n d e := by
  obtain ⟨m, hm, he⟩ := h.loop_eval
  rw [hm]
  exact (pop_eval p d).seq he

end SubexponentialSAT.UnaryForPrograms

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

theorem commit_run (s : Store) (out : List Bool) (h244 : s 244 = []) (h245 : s 245 = []) :
    ExecutesIn commit (2 * (s 240).length + 6 * out.length + 9)
      (Function.update s 244 out) (Function.update s 240 out) := by
  let s₁ := Function.update (Function.update s 244 out) 240 []
  let s₂ := Function.update (Function.update s 240 []) 245 out.reverse
  have h₁ : ExecutesIn (clear 240) (2 * (s 240).length + 3)
      (Function.update s 244 out) s₁ := by
    simpa [s₁] using clear_run 240 (Function.update s 244 out)
  have he₂ : Function.update (Function.update s₁ 244 []) 245
      ((s₁ 244).reverse ++ s₁ 245) = s₂ := by
    funext j
    by_cases h : j = 244 <;> simp [s₁, s₂, h, h244, h245, Function.update_apply]
  have h₂ : ExecutesIn (transfer 244 245) (3 * out.length + 3) s₁ s₂ := by
    have h := transfer_run 244 245 s₁ (by decide)
    rw [he₂] at h
    simpa [s₁] using h
  have he₃ : Function.update (Function.update s₂ 245 []) 240
      ((s₂ 245).reverse ++ s₂ 240) = Function.update s 240 out := by
    funext j
    by_cases h : j = 245 <;> by_cases h240 : j = 240 <;>
      simp [s₂, h, h240, h245 ]
  have h₃ : ExecutesIn (transfer 245 240) (3 * out.length + 3) s₂
      (Function.update s 240 out) := by
    have h := transfer_run 245 240 s₂ (by decide)
    rw [he₃] at h
    simpa [s₂] using h
  have h := h₁.seq (h₂.seq h₃)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | ring

theorem step_run (service : Code) (K : ℕ) (s : Store) (out : List Bool)
    (h244 : s 244 = []) (h245 : s 245 = [])
    (hservice : ExecutesIn service K s (Function.update s 244 out)) :
    ExecutesIn (step service) (K + 2 * (s 240).length + 6 * out.length + 9)
      s (Function.update s 240 out) := by
  have h := hservice.seq (commit_run s out h244 h245)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | ring

abbrev state {S : Type*} (base : Store) (encode : S → List Bool) (regs : Fin 16 → Bool)
    (a : S) (counter : List Bool) : Data := ⟨regs, ready base encode a counter⟩

theorem popped_state {S : Type*} (base : Store) (encode : S → List Bool)
    (regs : Fin 16 → Bool) (a : S) (counter : List Bool) :
    UnaryForPrograms.popped counterPorts (state base encode regs a counter) =
      state base encode (readRegs regs 0 1 counter.head?) a counter.tail := by
  apply SubexpScanPrimitives.state_ext
  · rfl
  · simp [UnaryForPrograms.popped, ready, counterPorts]

/-- Exact observations of every invocation of the fixed iteration command.
The only component premise is its actual instruction trace and cost. -/
theorem repeat_visits {S : Type*} (base : Store) (encode : S → List Bool)
    (iteration : Code) (f : S → S) (K : ℕ)
    (hstep : ∀ a counter, ExecutesIn iteration K (ready base encode a counter)
      (ready base encode (f a) counter)) (counter : List Bool) :
    ∀ (regs : Fin 16 → Bool) (a : S), ∃ costs n regs',
      UnaryForPrograms.Visits counterPorts iteration costs n
        (state base encode regs a counter)
        (state base encode regs' ((f^[counter.length]) a) []) ∧
      n ≤ counter.length * (K + 2) + 2 := by
  induction counter with
  | nil =>
      intro regs a
      refine ⟨[], 2, readRegs regs 0 1 none, ?_, by simp⟩
      simpa only [popped_state, List.head?_nil, List.tail_nil, List.length_nil,
        Function.iterate_zero_apply] using
        UnaryForPrograms.Visits.done (p := counterPorts) (body := iteration)
          (state base encode regs a []) rfl
  | cons bit counter ih =>
      intro regs a
      obtain ⟨nb, rb, hnb, hb⟩ := hstep a counter (readRegs regs 0 1 (some bit))
      obtain ⟨costs, nt, rt, ht, hnt⟩ := ih rb (f a)
      refine ⟨nb :: costs, nb + nt + 2, rt, ?_, ?_⟩
      · have h := UnaryForPrograms.Visits.step
          (p := counterPorts) (body := iteration)
          (d := state base encode regs a (bit :: counter))
          (by simp [ ready, counterPorts])
          (by simpa only [popped_state, List.head?_cons, List.tail_cons] using hb)
          (by simp [ ready, counterPorts, UnaryForPrograms.popped]) ht
        simpa only [List.length_cons, Function.iterate_succ_apply] using h
      · simp only [List.length_cons]
        nlinarith

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

theorem binaryStep_run {C : Type*} (base : Store) (encode : C → List Bool)
    (code : Code) (op : C → C → C) (K W : ℕ)
    (hspec : ServiceSpec base encode code op K)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (a b : C) (hf : LowFrame base s)
    (ha : s 240 = encode a) (hb : s 241 = encode b)
    (h244 : s 244 = []) (h245 : s 245 = []) :
    ExecutesIn (binaryStep code) (K + 8 * W + 9) s
      (Function.update s 240 (encode (op a b))) := by
  have h := SubexpPolynomialIterationControl.step_run code K s
    (encode (op a b)) h244 h245 (hspec s a b hf ha hb h244 h245)
  apply h.mono
  rw [ha]
  have h1 := hwidth a
  have h2 := hwidth (op a b)
  omega

theorem replace_run (s : Store) (src dst : Fin 256)
    (hsd : src ≠ dst) (hs : src ≠ 120) (hd : dst ≠ 120)
    (h120 : s 120 = []) :
    ExecutesIn (replace src dst)
      (2 * (s dst).length + 7 * (s src).length + 8)
      s (Function.update s dst (s src)) := by
  have h1 := clear_run dst s
  have h2 := copy_run src dst (Function.update s dst []) hsd hs (Ne.symm hd)
    (by simpa [Ne.symm hd] using h120)
  have he : Function.update (Function.update s dst []) dst
      ((Function.update s dst []) src ++ (Function.update s dst []) dst) =
      Function.update s dst (s src) := by simp [hsd]
  rw [he] at h2
  have h := h1.seq h2
  convert h using 1
  · rfl
  · simp [hsd]
    ring

theorem replace_bounded (s : Store) (src dst : Fin 256) (W : ℕ)
    (hsd : src ≠ dst) (hs : src ≠ 120) (hd : dst ≠ 120)
    (h120 : s 120 = []) (hsrc : (s src).length ≤ W) (hdst : (s dst).length ≤ W) :
    ExecutesIn (replace src dst) (9 * W + 8) s (Function.update s dst (s src)) :=
  (replace_run s src dst hsd hs hd h120).mono (by omega)

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

theorem hornerStep_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (a z one : C) (hf : LowFrame base s)
    (hacc : s 240 = encode a) (hfactor : s 241 = encode z)
    (hone : s 220 = encode one) (hz : s 222 = encode z)
    (h120 : s 120 = []) (h244 : s 244 = []) (h245 : s 245 = []) :
    ExecutesIn (hornerStep multiply add) (Km + Ka + 34 * W + 34) s
      (Function.update s 240 (encode (hornerValue mulOp addOp z one a))) := by
  let p := mulOp a z
  let v := addOp p one
  let s1 := Function.update s 240 (encode p)
  let s2 := Function.update s1 241 (encode one)
  let s3 := Function.update s2 240 (encode v)
  have hf1 : LowFrame base s1 := lowFrame_update hf 240 (by decide) _
  have hf2 : LowFrame base s2 := lowFrame_update hf1 241 (by decide) _
  have h1 : ExecutesIn (binaryStep multiply) (Km + 8 * W + 9) s s1 :=
    binaryStep_run base encode multiply mulOp Km W hm hwidth s a z hf
      hacc hfactor h244 h245
  have h2 : ExecutesIn (replace 220 241) (9 * W + 8) s1 s2 := by
    have h := replace_run s1 220 241 (by decide) (by decide) (by decide)
      (by simp [s1, h120])
    have he : Function.update s1 241 (s1 220) = s2 := by simp [s2, s1, hone]
    rw [he] at h
    apply h.mono
    simp only [s1, Function.update_of_ne (show (241 : Fin 256) ≠ 240 by decide),
      Function.update_of_ne (show (220 : Fin 256) ≠ 240 by decide), hfactor, hone]
    have hwz := hwidth z
    have hwo := hwidth one
    omega
  have h3 : ExecutesIn (binaryStep add) (Ka + 8 * W + 9) s2 s3 :=
    binaryStep_run base encode add addOp Ka W ha hwidth s2 p one hf2
      (by simp [s2, s1]) (by simp [s2])
      (by simp [s2, s1, h244]) (by simp [s2, s1, h245])
  have h4 : ExecutesIn (replace 222 241) (9 * W + 8) s3
      (Function.update s 240 (encode v)) := by
    have h := replace_run s3 222 241 (by decide) (by decide) (by decide)
      (by simp [s3, s2, s1, h120])
    have he : Function.update s3 241 (s3 222) = Function.update s 240 (encode v) := by
      funext i
      by_cases hi : i = 241 <;> by_cases ha : i = 240 <;>
        simp [s3, s2, s1, hi, ha, hz, hfactor]
    rw [he] at h
    apply h.mono
    simp [s3, s2, s1, hz]
    have hwz := hwidth z
    have hwo := hwidth one
    omega
  have h := h1.seq (h2.seq (h3.seq h4))
  convert h using 1 <;> first | omega | rfl

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

theorem defectCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (a b minusOne one : C) (hf : LowFrame base s)
    (hacc : s 240 = encode b) (hright : s 241 = encode a)
    (hone : s 207 = encode one) (hminus : s 211 = encode minusOne)
    (h120 : s 120 = []) (h222 : s 222 = [])
    (h244 : s 244 = []) (h245 : s 245 = []) :
    ExecutesIn (defectCommand multiply add) (2*Km + Ka + 60*W + 60) s
      (defectState s encode (defectValue mulOp addOp a b minusOne one) one) := by
  let p := mulOp b a
  let n := mulOp p minusOne
  let z := addOp n one
  let s1 := Function.update s 240 (encode p)
  let s2 := Function.update s1 241 (encode minusOne)
  let s3 := Function.update s2 240 (encode n)
  let s4 := Function.update s3 241 (encode one)
  let s5 := Function.update s4 240 (encode z)
  have hf1 : LowFrame base s1 := lowFrame_update hf 240 (by decide) _
  have hf2 : LowFrame base s2 := lowFrame_update hf1 241 (by decide) _
  have hf3 : LowFrame base s3 := lowFrame_update hf2 240 (by decide) _
  have hf4 : LowFrame base s4 := lowFrame_update hf3 241 (by decide) _
  have h1 : ExecutesIn (binaryStep multiply) (Km+8*W+9) s s1 :=
    binaryStep_run base encode multiply mulOp Km W hm hwidth s b a hf
      hacc hright h244 h245
  have h2 : ExecutesIn (replace 211 241) (9*W+8) s1 s2 := by
    simpa [s2, s1, hminus] using replace_bounded s1 211 241 W
      (by decide) (by decide) (by decide) (by simp [s1, h120])
      (by simpa [s1, hminus] using hwidth minusOne)
      (by simpa [s1, hright] using hwidth a)
  have h3 : ExecutesIn (binaryStep multiply) (Km+8*W+9) s2 s3 :=
    binaryStep_run base encode multiply mulOp Km W hm hwidth s2 p minusOne hf2
      (by simp [s2, s1]) (by simp [s2])
      (by simp [s2, s1, h244]) (by simp [s2, s1, h245])
  have h4 : ExecutesIn (replace 207 241) (9*W+8) s3 s4 := by
    simpa [s4, s3, s2, s1, hone] using replace_bounded s3 207 241 W
      (by decide) (by decide) (by decide) (by simp [s3, s2, s1, h120])
      (by simpa [s3, s2, s1, hone] using hwidth one)
      (by simpa [s3, s2] using hwidth minusOne)
  have h5 : ExecutesIn (binaryStep add) (Ka+8*W+9) s4 s5 :=
    binaryStep_run base encode add addOp Ka W ha hwidth s4 n one hf4
      (by simp [s4, s3]) (by simp [s4])
      (by simp [s4, s3, s2, s1, h244]) (by simp [s4, s3, s2, s1, h245])
  have h6 : ExecutesIn (replace 240 222) (9*W+8) s5
      (defectState s encode z one) := by
    have h := replace_bounded s5 240 222 W
      (by decide) (by decide) (by decide) (by simp [s5, s4, s3, s2, s1, h120])
      (by simpa [s5] using hwidth z) (by simp [s5, s4, s3, s2, s1, h222])
    have he : Function.update s5 222 (s5 240) = defectState s encode z one := by
      funext i
      by_cases h240 : i = 240 <;> by_cases h241 : i = 241 <;> by_cases h222 : i = 222 <;>
        simp [s5, s4, s3, s2, s1, defectState, h240, h241, h222]
    rw [he] at h
    exact h
  exact (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))).mono (by omega)

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed native binary calls at arbitrary persistent ports. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem callAt_run {C : Type*} (base : Store) (encode : C → List Bool)
    (code : Code) (op : C → C → C) (K W : ℕ)
    (hspec : ServiceSpec base encode code op K)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (a b : C) (left right dst : Fin 256)
    (hl : CachePort left) (hr : CachePort right) (hd : CachePort dst)
    (hf : LowFrame base s) (ha : s left = encode a) (hb : s right = encode b)
    (h120 : s 120 = []) (h240 : s 240 = []) (h241 : s 241 = [])
    (h244 : s 244 = []) (h245 : s 245 = []) (hdlen : (s dst).length ≤ W) :
    ExecutesIn (callAt code left right dst) (K+40*W+50) s
      (Function.update s dst (encode (op a b))) := by
  rcases hl with ⟨hlow, hl240, hl241, hl244, hl245⟩
  rcases hr with ⟨hrow, hr240, hr241, hr244, hr245⟩
  rcases hd with ⟨hdow, hd240, hd241, hd244, hd245⟩
  have hl120 : left ≠ 120 := by intro h; subst left; norm_num [Fin.coe_ofNat_eq_mod] at hlow
  have hr120 : right ≠ 120 := by intro h; subst right; norm_num [Fin.coe_ofNat_eq_mod] at hrow
  have hd120 : dst ≠ 120 := by intro h; subst dst; norm_num [Fin.coe_ofNat_eq_mod] at hdow
  let s1 := Function.update s 240 (encode a)
  let s2 := Function.update s1 241 (encode b)
  let s3 := Function.update s2 244 (encode (op a b))
  let s4 := Function.update s 244 (encode (op a b))
  let s5 := Function.update s4 dst (encode (op a b))
  have hf1 : LowFrame base s1 := lowFrame_update hf 240 (by decide) _
  have hf2 : LowFrame base s2 := lowFrame_update hf1 241 (by decide) _
  have h1 : ExecutesIn (replace left 240) (9*W+8) s s1 := by
    simpa [s1, ha] using replace_bounded s left 240 W hl240 hl120 (by decide) h120
      (by simpa [ha] using hwidth a) (by simp [h240])
  have h2 : ExecutesIn (replace right 241) (9*W+8) s1 s2 := by
    simpa [s2, s1, hr240, hb] using replace_bounded s1 right 241 W hr241 hr120 (by decide)
      (by simp [s1, h120]) (by simpa [s1, hr240, hb] using hwidth b)
      (by simp [s1, h241])
  have h3 : ExecutesIn code K s2 s3 := hspec s2 a b hf2
    (by simp [s2, s1]) (by simp [s2]) (by simp [s2, s1, h244])
    (by simp [s2, s1, h245])
  have h4 : ExecutesIn (SubexpLocalCRTSetup.clearMany [240,241]) (2*(2*W+3)) s3 s4 := by
    have h := SubexpLocalCRTSetup.clearMany_run [240,241] s3 W (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · simpa [s3, s2, s1] using hwidth a
      · simpa [s3, s2] using hwidth b)
    have he : SubexpLocalCRTSetup.cleared [240,241] s3 = s4 := by
      funext i
      by_cases h240i : i = 240 <;> by_cases h241i : i = 241 <;>
        simp [SubexpLocalCRTSetup.cleared_apply, s4, s3, s2, s1,
          Function.update_apply, h240i, h241i, h240, h241]
    simpa only [he, List.length_cons, List.length_nil] using h
  have h5 : ExecutesIn (replace 244 dst) (9*W+8) s4 s5 := by
    simpa [s5, s4] using replace_bounded s4 244 dst W (Ne.symm hd244) (by decide) hd120
      (by simp [s4, h120]) (by simpa [s4] using hwidth (op a b))
      (by simpa [s4, hd244] using hdlen)
  have h6 : ExecutesIn (clear 244) (2*W+3) s5
      (Function.update s dst (encode (op a b))) := by
    have h := clear_run 244 s5
    have he : Function.update s5 244 [] = Function.update s dst (encode (op a b)) := by
      funext i
      by_cases hi : i = 244 <;>
        simp [s5, s4, Function.update_apply, hi, h244, Ne.symm hd244]
    rw [he] at h
    apply h.mono
    simp [s5, s4, Ne.symm hd244]
    have hw := hwidth (op a b)
    omega
  exact (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))).mono (by omega)

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

theorem differenceCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka) (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (theta other minusOne : C) (hf : LowFrame base s)
    (htheta : s 213 = encode theta) (hother : s 218 = encode other)
    (hminus : s 211 = encode minusOne) (h120 : s 120 = []) (h205 : s 205 = [])
    (h219 : s 219 = []) (h240 : s 240 = []) (h241 : s 241 = [])
    (h244 : s 244 = []) (h245 : s 245 = []) :
    ExecutesIn (differenceCommand multiply add) (Km+Ka+100*W+110) s
      (Function.update s 205 (encode (differenceValue mulOp addOp theta other minusOne))) := by
  let neg := mulOp other minusOne
  let delta := addOp theta neg
  let s1 := Function.update s 219 (encode neg)
  let s2 := Function.update s1 205 (encode delta)
  have hf1 : LowFrame base s1 := lowFrame_update hf 219 (by decide) _
  have h1 : ExecutesIn (callAt multiply 218 211 219) (Km+40*W+50) s s1 :=
    callAt_run base encode multiply mulOp Km W hm hwidth s other minusOne 218 211 219
      (by decide) (by decide) (by decide) hf hother hminus h120 h240 h241 h244 h245
      (by simp [h219])
  have h2 : ExecutesIn (callAt add 213 219 205) (Ka+40*W+50) s1 s2 :=
    callAt_run base encode add addOp Ka W ha hwidth s1 theta neg 213 219 205
      (by decide) (by decide) (by decide) hf1 (by simp [s1, htheta]) (by simp [s1])
      (by simp [s1, h120]) (by simp [s1, h240]) (by simp [s1, h241])
      (by simp [s1, h244]) (by simp [s1, h245]) (by simp [s1, h205])
  have h3 : ExecutesIn (clear 219) (2*W+3) s2 (Function.update s 205 (encode delta)) := by
    have h := clear_run 219 s2
    have he : Function.update s2 219 [] = Function.update s 205 (encode delta) := by
      funext i
      by_cases hi : i = 219 <;> simp [s2, s1, Function.update_apply, hi, h219]
    rw [he] at h
    apply h.mono
    simp [s2, s1]
    have hw := hwidth neg
    omega
  exact (h1.seq (h2.seq h3)).mono (by omega)

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed native local-Hermite controller. Ring precision is read from212
and jet order from243. Protected polynomial service metadata192/193 are
prepared by the caller. All arithmetic calls are ordinary finite programs. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

local infixr:55 " ;; " => seq_p0

def localCommand (sm sa pm pa : Code) : Code :=
  test 243 15 ;; .ite 15 (positiveLocal sm sa pm pa) (.base .skip)

end SubexponentialSAT.SqrtLog.CRTLocalProgram

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

def matrixTriples {B : ℕ} (rows : List (Row B)) : List (RingScan.WordTriple B) :=
  (rows.map rowTriples).flatten

end SubexponentialSAT.SqrtLog.RingTriple

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

/-- Persistent native arithmetic metadata and a clean private workspace. -/
structure NativeReady (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (base : Store) : Prop where
  workspace : ReconstructionProgram.RingAdapter.Ready base
  modulus : base 194 = M.bits
  width : (base 202).length = baseWidth p t
  zero : base 203 = cache.zero.val
  table : base 201 = RingTriple.tableEncoding table
  degree : (base 204).length = d

end SubexponentialSAT.SqrtLog.HornerProgram.Services

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual native scalar and polynomial programs instantiate every local
service. The remaining hypotheses concern bytes and clean workspace. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open DensePolynomialProgram

 def command : Code := localCommand HornerProgram.Services.multiply HornerProgram.Services.add
    Fixed.mulCommand AddService.command

end SubexponentialSAT.SqrtLog.CRTLocalProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramNativeInverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A standalone native inverse of a node difference. The exponent is the
residue-field cardinality minus two; the separate repair loop has length t. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram.NativeInverse
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing

def command : Code := differenceInverseCommand
  HornerProgram.Services.multiply HornerProgram.Services.add

def value (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (theta other minusOne : RingProgram.Code (RingProgram.ScalarCode 3 t) d) :=
  let ops := RingProgram.modelProgram t a M cache
  let mul := fun x y => (ops.mulRun x y).1
  let add := fun x y => (ops.addRun x y).1
  inverseValue mul add ops.zeroRun.1 ops.oneRun.1 minusOne
    (differenceValue mul add theta other minusOne) (3^d-2) t

end SubexponentialSAT.SqrtLog.CRTLocalProgram.NativeInverse

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutBinomialProgramCell
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Consolidated fixed-control binomial-cache implementation. Component module
paths re-export this file so all interfaces remain stable. -/

/-! A Pascal cell saves the old entry, adds and emits the new entry, then
restores the saved entry as the carry. Every copy and clear is paid. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar
open SubexponentialSAT.Subexp.MatrixProgramSupport

abbrev saveOld : Cmd 8 18 := copy 2 14 13

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! One paid Pascal row pass over the framed cache. -/

/-! A fixed while loop consumes the runtime unary iteration count. -/

/-! A fixed loop builds the initial zero cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/

/-! One fixed program builds the complete unsigned binomial row from the unary
runtime parameters h and R. No coefficient or initial cache is free input. -/

/-! A fixed component routine copies the runtime width, pads or truncates one
word, and consumes that word into a reverse output buffer. -/

/-! Generic framed unsigned rows are converted to flat signed-component
arrays at a supplied runtime width. Both output arrays are physically built.
-/

/-! Finish the generic cache adapter by reversing both physically accumulated
arrays. The common width is preserved for downstream indexed reads. -/

/-! Value and shape contracts for the generic adapter and binomial row. -/

/-! Complete fixed-control binomial cache construction. The three parameters
are runtime unary stacks; the output consists of actual flat fixed-width
positive and negative arrays in increasing column order. -/

end OAI.Algorithms
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

open BitProgram StructuredCalls BinaryArithmetic Bank

def AdmissibleCode : List Instr → Model → Prop
  | [],_ => True
  | i::is,m => Admissible m i ∧ AdmissibleCode is (next m i)

@[simp] theorem admissibleCode_append (xs ys : List Instr) (m : Model) :
    AdmissibleCode (xs++ys) m ↔ AdmissibleCode xs m ∧ AdmissibleCode ys (result xs m) := by
  induction xs generalizing m with
  | nil => simp [AdmissibleCode,result]
  | cons x xs ih => simp [AdmissibleCode,result,ih,and_assoc]

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayout -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

abbrev powerCode : List Instr := [
  .mul 8 21 30 (by decide) (by decide),
  .pow 18 30 31 (by decide) (by decide)]

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayoutReady -/


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
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev Data := State 6 9
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows


/-! Native per-variable incident-factor scan from the original scope stream. -/


/-! Fixed cleanup for the native scope-address scanner. -/


/-! Calls to the fixed record mapper inside the native scope scan. -/


/-! One native low-variable step, including its uncovered neutral factor. -/


/-! Runtime high-mask loop for the original-address incidence stream. -/


/-! Count the physical scope stream before constructing native incidence plans. -/

end OAI.Algorithms
end


