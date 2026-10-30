-- Prove2me | Definitions.Def_OAIQ081S155
-- name    : OAIQ081S155
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:01:34.537615+00:00
-- url     : https://prove2.me/theorems/2ea01c55-d2f7-44e7-b26b-82b9c376fd13
-- title:
--   Definitions bundle OAIQ081S155 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 33 declarations of OpenAI's Lean: 21 definitions, 1 inductive type or structure and 11 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.modelScaledCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.modelSignedCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.naturalCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.scaledCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.signedCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.differenceBytes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.differenceTable`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.finalStore`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.inverseScan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.inverseTable`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.mapLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.mapScan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.mapStep`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.negativeScan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.negativeTable`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.pairLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.pairScan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.pairStep`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.rowBytes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.rowScan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.scanMaster`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.RingCaches`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_IntegerRingLiftProgram`, `SubexponentialSAT_SqrtLog_IntegerRingLiftProgramModel`, `SubexponentialSAT_SqrtLog_IntegerRingLiftProgramNatural`, `SubexponentialSAT_SqrtLog_IntegerRingLiftProgramScale`, `SubexponentialSAT_SqrtLog_IntegerRingLiftProgramSigned`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgram`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramBasic`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramCounts`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramFrame`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramPairs`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramPass`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramRows`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramScan`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramTables`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S139`, `OAIQ081S140`, `OAIQ081S141`, `OAIQ081S142` and `OAIQ081S143` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S166`, `OAIQ081S167`, `OAIQ081S168` and `OAIQ081S169`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S139
import Definitions.Def_OAIQ081S140
import Definitions.Def_OAIQ081S141
import Definitions.Def_OAIQ081S142
import Definitions.Def_OAIQ081S143

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

theorem scanCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (add : Code) (op : C → C → C) (K W : ℕ)
    (ha : ServiceSpec base encode add op K) (hw : ∀ a, (encode a).length ≤ W)
    (hc : Clean base) (bs : List Bool) (a p : C) :
    ExecutesIn (scanCommand add) (bs.length * (2 * (K + 40 * W + 50) + 3) + 2)
      (scanState base encode bs a p)
      (scanState base encode [] (scan op bs a p).1 (scan op bs a p).2) := by
  intro regs
  obtain ⟨costs, n, rf, hn, he⟩ := scan_visits base encode add op K W ha hw hc bs a p regs
  exact ⟨n, rf, hn, he.eval⟩

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IntegerRingLiftProgramNatural
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec LowFrame lowFrame_update serviceSpec_frame)

def naturalCommand (add : Code) : Code :=
  .seq (copy 249 247) (.seq (copy 250 248) (.seq (scanCommand add) (clear 248)))

theorem naturalCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (add : Code) (op : C → C → C) (K W : ℕ)
    (ha : ServiceSpec base encode add op K) (hw : ∀ a, (encode a).length ≤ W)
    (s : Store) (zero one : C) (hf : LowFrame base s) (hc : Clean s)
    (hz : s 249 = encode zero) (ho : s 250 = encode one)
    (h247 : s 247 = []) (h248 : s 248 = []) :
    ExecutesIn (naturalCommand add) (naturalBudget (s 246).length K W) s
      (Function.update (Function.update s 246 []) 247
        (encode (naturalValue op zero one (s 246)))) := by
  let a := naturalValue op zero one (s 246)
  let p := (scan op (s 246) zero one).2
  let s1 := Function.update s 247 (encode zero)
  let s2 := Function.update s1 248 (encode one)
  let s3 := scanState s2 encode [] a p
  have h1 : ExecutesIn (copy 249 247) (7*W+5) s s1 := by
    have h := copy_run 249 247 s (by decide) (by decide) (by decide) hc.1
    simp only [hz, h247, List.append_nil] at h
    exact h.mono (by have := hw zero; omega)
  have h2 : ExecutesIn (copy 250 248) (7*W+5) s1 s2 := by
    have h := copy_run 250 248 s1 (by decide) (by decide) (by decide)
      (by simp [s1, hc.1])
    have hs : s1 250 = encode one := by simp [s1, ho]
    have he : s1 248 = [] := by simp [s1, h248]
    simp only [hs, he, List.append_nil] at h
    exact h.mono (by have := hw one; omega)
  have hf2 : LowFrame base s2 := lowFrame_update
    (lowFrame_update hf 247 (by decide) _) 248 (by decide) _
  have hc2 : Clean s2 := by simpa [s2, s1, Clean] using hc
  have hi : scanState s2 encode (s 246) zero one = s2 := by
    funext i
    by_cases h246 : i = 246 <;> by_cases h247' : i = 247 <;> by_cases h248' : i = 248 <;>
      simp [scanState, s2, s1, h246, h247', h248']
  have h3 : ExecutesIn (scanCommand add)
      ((s 246).length * (2*(K+40*W+50)+3)+2) s2 s3 := by
    have h := scanCommand_run s2 encode add op K W (serviceSpec_frame ha hf2) hw
      hc2 (s 246) zero one
    rw [hi] at h
    exact h
  have he : Function.update s3 248 [] =
      Function.update (Function.update s 246 []) 247 (encode a) := by
    funext i
    by_cases h246 : i = 246 <;> by_cases h247' : i = 247 <;> by_cases h248' : i = 248 <;>
      simp [s3, scanState, s2, s1, h246, h247', h248', h248]
  have h4 : ExecutesIn (clear 248) (2*W+3) s3
      (Function.update (Function.update s 246 []) 247 (encode a)) := by
    have h := clear_run 248 s3
    rw [he] at h
    exact h.mono (by have := hw p; simp [s3, scanState]; omega)
  have h := h1.seq (h2.seq (h3.seq h4))
  exact h.mono (by unfold naturalBudget; omega)

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IntegerRingLiftProgramSigned
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec LowFrame lowFrame_update callAt callAt_run)

/-- Inputs253/254 are retained. Caches249/250/251 hold zero/one/minus-one.
Only output255 changes;246/247/248 and native service scratch start and end empty. -/
def signedCommand (multiply add : Code) : Code :=
  .seq (copy 253 246) (.seq (naturalCommand add)
    (.seq (copy 247 255) (.seq (clear 247) (.seq (copy 254 246)
      (.seq (naturalCommand add) (.seq (callAt multiply 247 251 247)
        (.seq (callAt add 255 247 255) (clear 247))))))))

theorem signedCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka) (hw : ∀ a, (encode a).length ≤ W)
    (s : Store) (zero one minusOne : C) (hf : LowFrame base s) (hc : Clean s)
    (hz : s 249 = encode zero) (ho : s 250 = encode one) (hn : s 251 = encode minusOne)
    (h246 : s 246 = []) (h247 : s 247 = []) (h248 : s 248 = []) (h255 : s 255 = []) :
    ExecutesIn (signedCommand multiply add)
      (signedBudget ((s 253).length + (s 254).length) Km Ka W) s
      (Function.update s 255 (encode (signedValue mulOp addOp zero one minusOne (s 253) (s 254)))) := by
  let p := naturalValue addOp zero one (s 253)
  let n := naturalValue addOp zero one (s 254)
  let neg := mulOp n minusOne
  let out := addOp p neg
  let s1 := Function.update s 246 (s 253)
  let s2 := Function.update s 247 (encode p)
  let s3 := Function.update s2 255 (encode p)
  let s4 := Function.update s 255 (encode p)
  let s5 := Function.update s4 246 (s 254)
  let s6 := Function.update s4 247 (encode n)
  let s7 := Function.update s4 247 (encode neg)
  let s8 := Function.update s7 255 (encode out)
  have hf1 : LowFrame base s1 := lowFrame_update hf 246 (by decide) _
  have hf4 : LowFrame base s4 := lowFrame_update hf 255 (by decide) _
  have hf5 : LowFrame base s5 := lowFrame_update hf4 246 (by decide) _
  have hf6 : LowFrame base s6 := lowFrame_update hf4 247 (by decide) _
  have hf7 : LowFrame base s7 := lowFrame_update hf4 247 (by decide) _
  have h1 : ExecutesIn (copy 253 246) (7*(s 253).length+5) s s1 := by
    simpa [s1, h246] using copy_run 253 246 s (by decide) (by decide) (by decide) hc.1
  have h2 : ExecutesIn (naturalCommand add) (naturalBudget (s 253).length Ka W) s1 s2 := by
    have h := naturalCommand_run base encode add addOp Ka W ha hw s1 zero one hf1
      (by simpa [Clean, s1] using hc) (by simp [s1, hz]) (by simp [s1, ho])
      (by simp [s1, h247]) (by simp [s1, h248])
    have he : Function.update (Function.update s1 246 []) 247
        (encode (naturalValue addOp zero one (s1 246))) = s2 := by
      simp [s1, s2, p, ← h246]
    rw [he] at h
    simpa only [s1, Function.update_self] using h
  have h3 : ExecutesIn (copy 247 255) (7*W+5) s2 s3 := by
    have h := copy_run 247 255 s2 (by decide) (by decide) (by decide) (by simp [s2, hc.1])
    simp only [s2, Function.update_self, Function.update_of_ne (show (255 : Fin 256) ≠ 247 by decide),
      h255, List.append_nil] at h
    exact h.mono (by have := hw p; omega)
  have h4 : ExecutesIn (clear 247) (2*W+3) s3 s4 := by
    have h := clear_run 247 s3
    have he : Function.update s3 247 [] = s4 := by
      funext i
      by_cases hi : i = 247 <;> simp [s3, s2, s4, Function.update_apply, hi, h247]
    rw [he] at h
    exact h.mono (by have := hw p; simp [s3, s2]; omega)
  have h5 : ExecutesIn (copy 254 246) (7*(s 254).length+5) s4 s5 := by
    have h := copy_run 254 246 s4 (by decide) (by decide) (by decide) (by simp [s4, hc.1])
    simpa [s5, s4, h246] using h
  have h6 : ExecutesIn (naturalCommand add) (naturalBudget (s 254).length Ka W) s5 s6 := by
    have h := naturalCommand_run base encode add addOp Ka W ha hw s5 zero one hf5
      (by simpa [Clean, s5, s4] using hc) (by simp [s5, s4, hz]) (by simp [s5, s4, ho])
      (by simp [s5, s4, h247]) (by simp [s5, s4, h248])
    have he : Function.update (Function.update s5 246 []) 247
        (encode (naturalValue addOp zero one (s5 246))) = s6 := by
      funext i
      by_cases hi : i = 246 <;> by_cases hj : i = 247 <;>
        simp [s5, s4, s6, n, Function.update_apply, hi, hj, h246]
    rw [he] at h
    simpa only [s5, Function.update_self] using h
  have h7 : ExecutesIn (callAt multiply 247 251 247) (Km+40*W+50) s6 s7 := by
    have h := callAt_run base encode multiply mulOp Km W hm hw s6 n minusOne
      247 251 247 (by unfold CRTLocalProgram.CachePort; decide) (by unfold CRTLocalProgram.CachePort; decide) (by unfold CRTLocalProgram.CachePort; decide) hf6
      (by simp [s6]) (by simp [s6, s4, hn])
      (by simp [s6, s4, hc.1]) (by simp [s6, s4, hc.2.1])
      (by simp [s6, s4, hc.2.2.1]) (by simp [s6, s4, hc.2.2.2.1])
      (by simp [s6, s4, hc.2.2.2.2]) (by simpa [s6] using hw n)
    simpa [s6, s7, neg] using h
  have h8 : ExecutesIn (callAt add 255 247 255) (Ka+40*W+50) s7 s8 :=
    callAt_run base encode add addOp Ka W ha hw s7 p neg
      255 247 255 (by unfold CRTLocalProgram.CachePort; decide) (by unfold CRTLocalProgram.CachePort; decide) (by unfold CRTLocalProgram.CachePort; decide) hf7
      (by simp [s7, s4]) (by simp [s7])
      (by simp [s7, s4, hc.1]) (by simp [s7, s4, hc.2.1])
      (by simp [s7, s4, hc.2.2.1]) (by simp [s7, s4, hc.2.2.2.1])
      (by simp [s7, s4, hc.2.2.2.2]) (by simpa [s7, s4] using hw p)
  have h9 : ExecutesIn (clear 247) (2*W+3) s8 (Function.update s 255 (encode out)) := by
    have h := clear_run 247 s8
    have he : Function.update s8 247 [] = Function.update s 255 (encode out) := by
      funext i
      by_cases hi : i = 247 <;> by_cases hj : i = 255 <;>
        simp [s8, s7, s4, hi, hj, h247]
    rw [he] at h
    exact h.mono (by have := hw neg; simp [s8, s7]; omega)
  have h := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq h9)))))))
  apply h.mono
  simp only [signedBudget, naturalBudget]
  ring_nf
  omega

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IntegerRingLiftProgramScale
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec LowFrame lowFrame_update callAt callAt_run)

/-- The source-row convention: negate the signed lift times cached inverse
denominator252. Both the denominator and minus-one251 are retained. -/
def scaledCommand (multiply add : Code) : Code :=
  .seq (signedCommand multiply add) (.seq (callAt multiply 255 252 255)
    (callAt multiply 255 251 255))

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IntegerRingLiftProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete, fixed native programs lifting a pair of arbitrary little-endian
binary words to the actual RingModel. There is no integer-lifting callback.
The only runtime constants are explicit represented ring caches. -/
namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open CRTLocalProgram (lowFrame_refl)

def modelSignedCommand : Code := signedCommand HornerProgram.Services.multiply HornerProgram.Services.add
def modelScaledCommand : Code := scaledCommand HornerProgram.Services.multiply HornerProgram.Services.add

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

theorem copy_run (s : Store) (src dst : Fin 320) (hsd : src≠dst)
    (hs : src≠270) (hd : (270 : Fin 320)≠dst) (ht : s 270=[]) :
    Runs (copy src dst) (7*(s src).length+5) s (Function.update s dst (s src++s dst)) := by
  intro r
  exact ⟨_,readRegs r 0 1 none,le_rfl,copy_eval (⟨r,s⟩ : Data) src dst 270 0 1 hsd hs hd (by decide) ht⟩

theorem clear_run (s : Store) (src : Fin 320) :
    Runs (clear src) (2*(s src).length+3) s (Function.update s src []) := by
  intro r
  refine ⟨_,readRegs r 0 1 none,le_rfl,Eval.call _ ?_⟩
  have h := halt_after_trace _ (clearProgram_trace src (0 : Fin 16) 1 r s) 2 rfl rfl
  simpa [clearResult,clearProgram,clearStacks,StructuredProgram.State.withPC,Nat.add_assoc] using h

theorem emit_run (s : Store) (src dst : Fin 320) (hne : src≠dst) :
    Runs (emit src dst) (3*(s src).length+3) s
      (Function.update (Function.update s src []) dst ((s src).reverse++s dst)) := by
  intro r
  exact ⟨_,readRegs r 0 1 none,le_rfl,transfer_eval (⟨r,s⟩ : Data) src dst 0 1 hne (by decide)⟩

theorem reverse_run (s : Store) (src : Fin 320) (h270 : src≠270) (h271 : src≠271)
    (ht270 : s 270=[]) (ht271 : s 271=[]) :
    Runs (reverse src) (9*(s src).length+7) s (Function.update s src (s src).reverse) := by
  intro r
  exact ⟨_,readRegs r 0 1 none,le_rfl,reverse_eval (⟨r,s⟩ : Data) src 270 271 0 1
    h270 h271 (by decide) (by decide) ht270 ht271⟩

theorem take_run (s : Store) (src dst : Fin 320)
    (distinct : Function.Injective (![104,270,271,src,dst] : Fin 5 → Fin 320))
    (bits rest : List Bool) (hsrc : s src=bits++rest) (hw : (s 104).length=bits.length)
    (h270 : s 270=[]) (h271 : s 271=[]) :
    Runs (take src dst) (14*bits.length+11) s
      (Function.update (Function.update s src rest) dst (bits++s dst)) := by
  intro r
  exact ⟨_,readRegs r 0 1 none,le_rfl,takeWord_eval (⟨r,s⟩ : Data)
    104 270 271 src dst 0 1 distinct (by decide) bits rest hsrc h270 h271 hw⟩

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

theorem consumeCount_run (src dst : Fin 320) (hne : src≠dst) (s : Store) :
    Runs (consumeCount src dst) (4*(s src).length+4) s
      (Function.update (Function.update s src []) dst (List.replicate (s src).length true++s dst)) := by
  intro r
  have hr : Function.Injective countRegisters := Fin.castAdd_injective _ _
  have hp : Function.Injective (countPorts src dst) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [countPorts]
  let a : Data := ⟨r,s⟩
  let out := Function.update (Function.update s src []) dst (List.replicate (s src).length true++s dst)
  let b := PackingHeadProgramPrepareCount.state (fun _ => false) [] (List.replicate (s src).length true++s dst)
  have ht := PackingHeadProgramPrepareCount.trace (r ∘ countRegisters) (s src) (s dst)
  have hproject : projectState countRegisters (countPorts src dst) a =
      PackingHeadProgramPrepareCount.state (r ∘ countRegisters) (s src) (s dst) := by
    apply state_ext
    · rfl
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  have he := eval_call_from_state PackingHeadProgramPrepareCount.program countRegisters
    (countPorts src dst) a hr hp (by rw [hproject]; exact ht)
  have hb : embedState countRegisters (countPorts src dst) a b=
      (⟨(embedState countRegisters (countPorts src dst) a b).regs,out⟩ : Data) := by
    apply embedState_eq_of_ports countRegisters (countPorts src dst) a _ b hr hp
    · intro i; exact embedState_register countRegisters (countPorts src dst) a b hr i
    · intro i hi; exact embedState_register_frame countRegisters (countPorts src dst) a b i hi
    · intro i; fin_cases i <;> simp [out,b,PackingHeadProgramPrepareCount.state,countPorts,hne]
    · intro i hi
      have hs : i≠src := by intro h; apply hi; exact ⟨0,by simpa [countPorts] using h.symm⟩
      have hd : i≠dst := by intro h; apply hi; exact ⟨1,by simpa [countPorts] using h.symm⟩
      change out i=s i
      simp [out,hs,hd]
  change Eval (consumeCount src dst) (4*(s src).length+4) a
    (embedState countRegisters (countPorts src dst) a b) at he
  rw [hb] at he
  exact ⟨_,_,le_rfl,he⟩

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The controller's changing ports and the preserved arithmetic context. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT

theorem Ready.frame {t d : ℕ} {a : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {minusOne : Coeff t d} {base s : Store} (h : Ready t a M cache minusOne base)
    (hf : Frame base s) : Ready t a M cache minusOne s := by
  have hn := h.native.frame (s := s ∘ low) (by
    intro i hi
    apply hf (low i)
    intro hh
    have := controllerPorts_lower hh
    change 208 ≤ i.val at this
    omega)
  refine ⟨hn,?_,?_,?_,?_,?_,?_⟩
  · exact (hf 104 (by decide)).trans h.zero
  · exact (hf 207 (by decide)).trans h.one
  · exact (hf 211 (by decide)).trans h.minus
  · rw [hf 209 (by decide)]; exact h.exponent
  · rw [hf 212 (by decide)]; exact h.precision
  · intro i hi
    rw [hf i (by
      simp only [scratchPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]
    exact h.scratch i hi

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed-width physical map scan. The service is an ordinary finite
subprogram, and its output is transferred into the actual packed table. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls StackRoutines

local infixr:55 " ;; " => seq_p2

def mapStep (src dst arg : Fin 320) (service : Code) : Code :=
  take src arg ;; service ;; emit 208 dst ;; clear arg

def mapLoop (src dst arg : Fin 320) (service : Code) : Code :=
  .while 15 (mapStep src dst arg service ;; peek src)

def mapScan (src dst arg : Fin 320) (service : Code) : Code :=
  peek src ;; mapLoop src dst arg service

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramPass
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Packed scans starting from a preserved node master. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls

def scanMaster (src dst arg : Fin 320) (service : Code) : Code :=
  .seq (copy 256 src) (mapScan src dst arg service)

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native scans for inverse nodes, negative nodes, and a complete row of
pairwise difference inverses. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexpLiftRing

theorem Ready.update_controller {t d : ℕ} {a : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {minusOne : Coeff t d} {s : Store} (h : Ready t a M cache minusOne s)
    (i : Fin 320) (v : List Bool) (hi : i∈controllerPorts) :
    Ready t a M cache minusOne (Function.update s i v) :=
  h.frame ((Frame.refl s).update i v hi)

def inverseScan : Code := scanMaster 257 259 213 inverseCommand
def negativeScan : Code := scanMaster 257 260 213 negativeCommand
def rowScan : Code := scanMaster 258 261 218 inverseCommand

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramPairs
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Nested native scans producing the full row-major difference-inverse
array. Every diagonal cell is computed by the same total inverse routine. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls StackRoutines
open SubexpLiftRing
local infixr:55 " ;; " => seq_p1

def pairStep : Code := take 257 213 ;; rowScan ;; clear 213
def pairLoop : Code := .while 15 (pairStep ;; peek 257)
def pairScan : Code := copy 256 257 ;; peek 257 ;; pairLoop

def rowBytes (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (xs : List (Coeff t d)) (x : Coeff t d) : List Bool :=
  xs.flatMap fun y => RingProgram.flat (differenceValue t a M cache minusOne x y)

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramTables
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete ordered native tables; all working streams are empty again. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexpLiftRing
local infixr:55 " ;; " => seq_p3

def inverseTable : Code := copy 104 218 ;; inverseScan ;; clear 218 ;; reverse 259
def negativeTable : Code := negativeScan ;; reverse 260
def differenceTable : Code := pairScan ;; reverse 261

def differenceBytes (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (xs : List (Coeff t d)) :=
  xs.flatMap (rowBytes t a M cache minusOne xs)

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A single fixed native interpolation-cache producer. The only data
inputs are the actual node stream and already prepared ring constants.
No inverse, negative, or pairwise table is supplied to this program. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexpLiftRing

def finalStore (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (xs : List (Coeff t d)) (s : Store) : Store :=
  Function.update (Function.update (Function.update (Function.update (Function.update s
    259 (inverseBytes t a M cache minusOne xs))
    260 (negativeBytes t a M cache minusOne xs))
    261 (differenceBytes t a M cache minusOne xs))
    262 (List.replicate (xs.length*(d*baseWidth 3 t)) true))
    263 (List.replicate (d*baseWidth 3 t) true)

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

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
open BitProgram StructuredCalls SubexpQuarticRing SubexpLiftRing

/-- Persistent ring data. The private scalar masters are deliberately not
part of this contract: later private Newton preparation may reuse them. -/
structure RingCaches (t d : ℕ) (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (u : RingProgram.ScalarCode 3 t) (a : Data) : Prop where
  modulus : a.stacks 194=M.bits
  width : (a.stacks 202).length=baseWidth 3 t
  degree : (a.stacks 204).length=d
  scalarZero : a.stacks 203=cache.zero.val
  table : a.stacks 201=RingProgramTable.modelTable t model M cache
  precision : a.stacks 212=List.replicate t true
  half : a.stacks 253=u.val
  inverse : (2 : ZMod (3^t))*wordValue 3 t u=1
  canonical : BinaryArithmetic.toNat cache.zero.val < 3^t
  fullZero : a.stacks 280=RingProgramTable.literalBits d cache.zero cache.zero
  fullOne : a.stacks 207=RingProgramTable.literalBits d cache.one cache.zero
  fullMinusOne : a.stacks 211=RingProgramTable.literalBits d cache.minusOne cache.zero
  readoutZero : a.stacks 190=a.stacks 280
  aliasZero : a.stacks 249=a.stacks 280
  aliasOne : a.stacks 250=a.stacks 207
  aliasMinusOne : a.stacks 251=a.stacks 211

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end


