-- Prove2me | Definitions.Def_OAIQ081S167
-- name    : OAIQ081S167
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:09:22.938128+00:00
-- url     : https://prove2.me/theorems/e85c91b8-bf1b-4e60-91e2-a5a826d9830d
-- title:
--   Definitions bundle OAIQ081S167 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 4 definitions and 12 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.CompareReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.EmitterClean`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.lowStore`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout.guardedCode`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLog_IdempotentPreparationProgramEncoded`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentPreparationProgramEncoded.lean), [`SubexponentialSAT_SqrtLog_IntegerRingLiftProgramCached`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IntegerRingLiftProgramCached.lean), [`SubexponentialSAT_SqrtLog_InterpolationCacheProgramCounts`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/InterpolationCacheProgramCounts.lean), [`SubexponentialSAT_SqrtLog_InterpolationCacheProgramFrame`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/InterpolationCacheProgramFrame.lean), [`SubexponentialSAT_SqrtLog_InterpolationCacheProgramNative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/InterpolationCacheProgramNative.lean), [`SubexponentialSAT_SqrtLog_InterpolationCacheProgramScan`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/InterpolationCacheProgramScan.lean), [`SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameEmitter`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceBankFrameEmitter.lean), [`SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameReady`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceBankFrameReady.lean), [`SubexponentialSAT_SqrtLog_LayoutProgramSourceDispatch`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceDispatch.lean), [`SubexponentialSAT_SqrtLog_LeafParametersProgramNative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafParametersProgramNative.lean), [`SubexponentialSAT_SubexpKernelControl`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SubexpKernelControl.lean), [`SubexponentialSAT_Subexp_PackingExtractionBlock`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/PackingExtractionBlock.lean).
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S153`, `OAIQ081S154`, `OAIQ081S155` and `OAIQ081S156` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S173` and `OAIQ081S174`; the statement `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.uncovered_cleanup`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S153
import Definitions.Def_OAIQ081S154
import Definitions.Def_OAIQ081S155
import Definitions.Def_OAIQ081S156

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramEncoded
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open SubexpQuarticRing

attribute [local instance] OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.instFactPrimeOfNatNat_solutions_2
theorem finished_encoded (t : ℕ) (ht : 0 < t) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t)
    (d e : Data) (hp : Scalar.Prepared t M cache u d)
    (h12 : d.stacks 12=List.replicate (2*t) true)
    (h37 : d.stacks 37=List.replicate (3*t) true)
    (he : e.stacks=finishedStacks d.stacks t
      (IdempotentProgram.tableTape (IdempotentProgram.tableCode (t := t) (RingProgram.scalarProgram 3 t M cache)))) :
    IdempotentProgram.RegistersEncoded M.bits (List.replicate (2*t) true) cache.zero.val
      (RingTriple.tableEncoding (IdempotentProgram.tableCode (t := t) (RingProgram.scalarProgram 3 t M cache)))
      (List.replicate (3*t) true)
      (IdempotentProgram.minusOneRun (RingProgram.scalarProgram 3 t M cache) t).1
      (initialRegisters t M cache u) e := by
  have h5 : d.stacks 5=M.bits := hp.rest.1 5
  have hz : d.stacks 17=cache.zero.val := prepared_zero t M cache u d hp
  have hi : d.stacks 30 ++ d.stacks 31 ++ d.stacks 27 ++
      Subexp.BlockCopyProgram.copies (3*t-3) (d.stacks 17) =
      RingProgram.flat (IdempotentProgram.initialRun (RingProgram.scalarProgram 3 t M cache) t u).1 := by
    rw [initialRun_flat _ t ht u]
    simp [hp.twice,hp.minusThree,hp.half,hz,RingProgram.scalarProgram]
  have hm : d.stacks 28 ++ Subexp.BlockCopyProgram.copies (3*t-1) (d.stacks 17) =
      RingProgram.flat (IdempotentProgram.minusOneRun (RingProgram.scalarProgram 3 t M cache) t).1 := by
    rw [minusOneRun_flat 3 t M cache ht hp.zeroCanonical hp.minusOneCanonical]
    rw [hp.minusOne,hz]
  rw [←IdempotentProgram.tableTape_eq_encoding]
  constructor
  · intro i
    fin_cases i <;>
      simp [he,finishedStacks,arrayStacks,preparationDiscard,IdempotentProgram.servicePorts,
        RingScan.serviceState,RingScan.serviceWorkState,RingScan.serviceTapes,h5,h12,hz]
  · intro i
    fin_cases i <;>
      simpa [he,finishedStacks,arrayStacks,preparationDiscard,IdempotentProgram.arrayRegister,
        initialRegisters] using hi
  · simpa [he,finishedStacks,arrayStacks,preparationDiscard] using hm
  · simp [he,finishedStacks,arrayStacks,preparationDiscard,h37]
  · simp [he,finishedStacks,preparationDiscard]

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

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

theorem cachedSignedCommand_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (zero one minusOne : ModelCode t d) (s : Store) (h : CachedReady t a M cache zero one minusOne s) :
    ExecutesIn modelSignedCommand (modelSignedBudget ((s 253).length + (s 254).length) t d) s
      (Function.update s 255 (RingProgram.flat
        (cachedSignedValue t a M cache zero one minusOne (s 253) (s 254)))) := by
  exact signedCommand_run s RingProgram.flat HornerProgram.Services.multiply HornerProgram.Services.add
    (fun x y => ((RingProgram.modelProgram t a M cache).mulRun x y).1)
    (fun x y => ((RingProgram.modelProgram t a M cache).addRun x y).1)
    (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
    (HornerProgram.Services.addBudget (baseWidth 3 t) d) (d * baseWidth 3 t)
    (HornerProgram.Services.multiply_spec 3 t M cache hz (modelTable t a M cache) s h.native)
    (HornerProgram.Services.add_spec 3 t M cache (modelTable t a M cache) s h.native)
    (fun x => (RingProgram.flat_length x).le) s zero one minusOne (lowFrame_refl s)
    h.clean h.zero h.one h.minusOne h.bits h.accumulator h.place h.output

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

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

theorem countCopy_run (src dst : Fin 320) (s : Store)
    (hs : src≠272) (hs270 : src≠270) (hd : dst≠272)
    (ht : s 270=[]) (hw : s 272=[]) (ho : s dst=[]) :
    Runs (countCopy src dst) (11*(s src).length+9) s
      (Function.update s dst (List.replicate (s src).length true)) := by
  let mid := Function.update s 272 (s src)
  have h1 : Runs (copy src 272) (7*(s src).length+5) s mid := by
    simpa only [mid,hw,List.append_nil] using copy_run s src 272 hs hs270 (by decide) ht
  have h2 := consumeCount_run 272 dst hd.symm mid
  have he : Function.update (Function.update mid 272 []) dst
      (List.replicate (mid 272).length true++mid dst) =
      Function.update s dst (List.replicate (s src).length true) := by
    simp only [mid,Function.update_same,Function.update_idem,Function.update_of_ne hd,ho,List.append_nil]
    rw [← hw,Function.update_eq_self]
  rw [he] at h2
  have h := h1.seq h2
  exact h.mono (by simp [mid]; omega)

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

theorem inverseCommand_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (s : Store)
    (hr : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache) (s ∘ low))
    (x y minusOne : Coeff t d)
    (hx : s 213=RingProgram.flat x) (hy : s 218=RingProgram.flat y)
    (hzero : s 104=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hone : s 207=RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (hm : s 211=RingProgram.flat minusOne)
    (hq : (s 209).length=3^d-2) (ht : (s 212).length=t)
    (hc : ∀i∈CRTLocalProgram.NativeInverse.work, s (low i)=[]) :
    Runs inverseCommand (inverseBudget t d) s
      (Function.update s 208 (RingProgram.flat (differenceValue t a M cache minusOne x y))) := by
  exact lowCall_run _ _ s 208 _ (CRTLocalProgram.NativeInverse.command_run
    t a M cache hz (s ∘ low) hr x y minusOne hx hy hzero hone hm hq ht hc)

theorem negativeCommand_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (s : Store)
    (hr : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache) (s ∘ low))
    (x minusOne : Coeff t d) (hx : s 213=RingProgram.flat x) (hm : s 211=RingProgram.flat minusOne)
    (hc : ∀i∈([208,240,241,244,245] : List (Fin 320)), s i=[]) :
    Runs negativeCommand (negativeBudget t d) s
      (Function.update s 208 (RingProgram.flat (negativeValue t a M cache minusOne x))) := by
  have h := CRTLocalProgram.callAt_run (s ∘ low) RingProgram.flat
    HornerProgram.Services.multiply
    (fun x y => ((RingProgram.modelProgram t a M cache).mulRun x y).1)
    (HornerProgram.Services.mulBudget (baseWidth 3 t) d) (d*baseWidth 3 t)
    (HornerProgram.Services.multiply_spec 3 t M cache hz (HornerProgram.modelTable t a M cache) (s ∘ low) hr)
    (fun x => (RingProgram.flat_length x).le) (s ∘ low) x minusOne 213 211 208
    (by decide) (by decide) (by decide) (CRTLocalProgram.lowFrame_refl _) hx hm
    hr.workspace.1 (hc 240 (by simp)) (hc 241 (by simp)) (hc 244 (by simp)) (hc 245 (by simp))
    (by change (s 208).length ≤ d*baseWidth 3 t; rw [hc 208 (by simp)]; exact Nat.zero_le _)
  exact lowCall_run _ _ s 208 _ h

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

theorem Ready.inverse_run {t d : ℕ} {a : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {minusOne : Coeff t d} {s : Store} (h : Ready t a M cache minusOne s)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (x y : Coeff t d)
    (hx : s 213=RingProgram.flat x) (hy : s 218=RingProgram.flat y) (hr : s 208=[]) :
    Runs inverseCommand (inverseBudget t d) s
      (Function.update s 208 (RingProgram.flat (differenceValue t a M cache minusOne x y))) := by
  apply inverseCommand_run t a M cache hz s h.native x y minusOne hx hy h.zero h.one h.minus h.exponent h.precision
  intro i hi
  simp only [CRTLocalProgram.NativeInverse.work,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact hr | exact h.scratch _ (by decide)

theorem Ready.negative_run {t d : ℕ} {a : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {minusOne : Coeff t d} {s : Store} (h : Ready t a M cache minusOne s)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (x : Coeff t d)
    (hx : s 213=RingProgram.flat x) (hr : s 208=[]) :
    Runs negativeCommand (negativeBudget t d) s
      (Function.update s 208 (RingProgram.flat (negativeValue t a M cache minusOne x))) := by
  apply negativeCommand_run t a M cache hz s h.native x minusOne hx h.minus
  intro i hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl
  all_goals first | exact hr | exact h.scratch _ (by decide)

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

theorem mapStep_run {C : Type*} (encode : C → List Bool) (f : C → C) (W K : ℕ)
    (hwidth : ∀x,(encode x).length=W) (src dst arg : Fin 320) (hp : MapPorts src dst arg)
    (service : Code) (P : Store → Prop)
    (stable : ∀s i v,P s → i∈([src,dst,arg,208] : List (Fin 320)) → P (Function.update s i v))
    (hspec : ∀s x,P s → s arg=encode x → s 208=[] →
      Runs service K s (Function.update s 208 (encode (f x))))
    (s : Store) (x : C) (rest : List Bool) (hP : P s)
    (hsrc : s src=encode x++rest) (harg : s arg=[]) (hresult : s 208=[])
    (h104 : (s 104).length=W) (h270 : s 270=[]) (h271 : s 271=[]) :
    Runs (mapStep src dst arg service) (K+19*W+17) s
      (Function.update (Function.update s src rest) dst ((encode (f x)).reverse++s dst)) := by
  have hsarg : src≠arg := hp.ne (by decide : (3:Fin 7)≠5)
  have hsd : src≠dst := hp.ne (by decide : (3:Fin 7)≠4)
  have hs208 : src≠208 := hp.ne (by decide : (3:Fin 7)≠6)
  have hdarg : dst≠arg := hp.ne (by decide : (4:Fin 7)≠5)
  have hd208 : dst≠208 := hp.ne (by decide : (4:Fin 7)≠6)
  have ha208 : arg≠208 := hp.ne (by decide : (5:Fin 7)≠6)
  have htake : Function.Injective (![104,270,271,src,arg] : Fin 5 → Fin 320) := by
    intro i j hij
    have hh : (![104,270,271,src,arg] : Fin 5 → Fin 320) =
        (![104,270,271,src,dst,arg,208] : Fin 7 → Fin 320) ∘
          (![0,1,2,3,5] : Fin 5 → Fin 7) := by funext k; fin_cases k <;> rfl
    rw [hh] at hij
    exact (by decide : Function.Injective (![0,1,2,3,5] : Fin 5 → Fin 7)) (hp hij)
  let s1 := Function.update (Function.update s src rest) arg (encode x)
  let s2 := Function.update s1 208 (encode (f x))
  let s3 := Function.update (Function.update s2 208 []) dst ((encode (f x)).reverse++s dst)
  have h1 : Runs (take src arg) (14*W+11) s s1 := by
    simpa only [s1,harg,List.append_nil,hwidth] using
      take_run s src arg htake (encode x) rest hsrc (h104.trans (hwidth x).symm) h270 h271
  have hP1 : P s1 := stable _ arg _ (stable _ src _ hP (by simp)) (by simp)
  have h2 : Runs service K s1 s2 := hspec s1 x hP1 (by simp [s1])
    (by simp [s1,Ne.symm ha208,Ne.symm hs208,hresult])
  have h3 : Runs (emit 208 dst) (3*W+3) s2 s3 := by
    simpa [s3,s2,s1,hd208,hdarg,Ne.symm hsd,hwidth] using emit_run s2 208 dst hd208.symm
  have h4 : Runs (clear arg) (2*W+3) s3 (Function.update s3 arg []) := by
    simpa [s3,s2,s1,ha208,Ne.symm hdarg,hwidth] using clear_run s3 arg
  have hout : Function.update s3 arg [] =
      Function.update (Function.update s src rest) dst ((encode (f x)).reverse++s dst) := by
    funext j
    by_cases ha : j=arg
    · subst j
      simp [s3,s2,s1,Ne.symm hdarg,Ne.symm hsarg,harg]
    · by_cases hr : j=208
      · subst j
        simp [s3,s2,s1,Ne.symm ha208,Ne.symm hd208,Ne.symm hs208,hresult]
      · simp [s3,s2,s1,Function.update_apply,ha,hr]
  have hh := h1.seq (h2.seq (h3.seq h4))
  rw [hout] at hh
  exact hh.mono (by omega)

/-- The scan preserves the full caller store except its consumed source and
its reverse accumulator. The output values are produced by the service. -/
theorem mapLoop_run {C : Type*} (encode : C → List Bool) (f : C → C) (W K : ℕ)
    (hW : 0 < W) (hwidth : ∀x,(encode x).length=W)
    (src dst arg : Fin 320) (hp : MapPorts src dst arg)
    (service : Code) (P : Store → Prop)
    (stable : ∀s i v,P s → i∈([src,dst,arg,208] : List (Fin 320)) → P (Function.update s i v))
    (hspec : ∀s x,P s → s arg=encode x → s 208=[] →
      Runs service K s (Function.update s 208 (encode (f x))))
    (s : Store) (xs : List C) (hP : P s) (hsrc : s src=xs.flatMap encode)
    (harg : s arg=[]) (hresult : s 208=[])
    (h104 : (s 104).length=W) (h270 : s 270=[]) (h271 : s 271=[])
    (r : Fin 16 → Bool) :
    ∃n rf,n ≤ xs.length*(K+19*W+19)+1 ∧
      Eval (mapLoop src dst arg service) n
        (⟨readRegs r 0 15 (s src).head?,s⟩ : Data)
        ⟨rf,Function.update (Function.update s src []) dst
          ((xs.flatMap fun x => encode (f x)).reverse++s dst)⟩ := by
  induction xs generalizing s r with
  | nil =>
      have hz : s src=[] := hsrc
      refine ⟨1,readRegs r 0 15 none,by simp,?_⟩
      have hu : Function.update s src []=s := by simpa only [hz] using Function.update_eq_self src s
      simp only [List.flatMap_nil,List.reverse_nil,List.nil_append,hu,Function.update_eq_self]
      simpa only [mapLoop, hz,List.head?_nil] using
        (Eval.while_false (body := mapStep src dst arg service ;; peek src)
          (a := (⟨readRegs r 0 15 none,s⟩ : Data)) (by simp [readRegs]))
  | cons x xs ih =>
      have hsarg : src≠arg := hp.ne (by decide : (3:Fin 7)≠5)
      have hsd : src≠dst := hp.ne (by decide : (3:Fin 7)≠4)
      have hs208 : src≠208 := hp.ne (by decide : (3:Fin 7)≠6)
      have hdarg : dst≠arg := hp.ne (by decide : (4:Fin 7)≠5)
      have hd208 : dst≠208 := hp.ne (by decide : (4:Fin 7)≠6)
      let mid := Function.update (Function.update s src (xs.flatMap encode)) dst
        ((encode (f x)).reverse++s dst)
      obtain ⟨n,rm,hn,he⟩ := mapStep_run encode f W K hwidth src dst arg hp service P stable hspec
        s x (xs.flatMap encode) hP hsrc harg hresult h104 h270 h271
        (readRegs r 0 15 (s src).head?)
      have hPm : P mid := stable _ dst _ (stable _ src _ hP (by simp)) (by simp)
      have hsm : mid src=xs.flatMap encode := by simp [mid,hsd]
      have ham : mid arg=[] := by simp [mid,Ne.symm hdarg,Ne.symm hsarg,harg]
      have hrm : mid 208=[] := by simp [mid,Ne.symm hd208,Ne.symm hs208,hresult]
      have hkeep (i : Fin 320) (hi : i=104 ∨ i=270 ∨ i=271) : mid i=s i := by
        rcases hi with rfl|rfl|rfl
        · simp only [mid,Function.update_of_ne (show (104:Fin 320)≠dst from hp.ne (by decide : (0:Fin 7)≠4)),Function.update_of_ne (show (104:Fin 320)≠src from hp.ne (by decide : (0:Fin 7)≠3))]
        · simp only [mid,Function.update_of_ne (show (270:Fin 320)≠dst from hp.ne (by decide : (1:Fin 7)≠4)),Function.update_of_ne (show (270:Fin 320)≠src from hp.ne (by decide : (1:Fin 7)≠3))]
        · simp only [mid,Function.update_of_ne (show (271:Fin 320)≠dst from hp.ne (by decide : (2:Fin 7)≠4)),Function.update_of_ne (show (271:Fin 320)≠src from hp.ne (by decide : (2:Fin 7)≠3))]
      obtain ⟨m,rf,hm,ht⟩ := ih mid hPm hsm ham hrm
        (by simpa only [hkeep 104 (by simp)] using h104)
        ((hkeep 270 (by simp)).trans h270) ((hkeep 271 (by simp)).trans h271) rm
      have hg : (readRegs r 0 15 (s src).head?) 15=true := by
        have he0 : encode x≠[] := fun hh => by have := hwidth x; simp [hh] at this; omega
        rw [hsrc,List.flatMap_cons]
        cases hh : encode x with
        | nil => exact (he0 hh).elim
        | cons b bs => simp [readRegs]
      have hloop := Eval.while_true hg (he.seq (peek_eval mid rm src)) ht
      refine ⟨n+1+m+1,rf,?_,?_⟩
      · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
        omega
      · have hfinal : Function.update (Function.update mid src []) dst
            ((xs.flatMap fun x => encode (f x)).reverse++mid dst) =
            Function.update (Function.update s src []) dst
              (((x::xs).flatMap fun x => encode (f x)).reverse++s dst) := by
          funext i
          by_cases hi : i=dst
          · subst i; simp [mid,List.reverse_append,List.append_assoc]
          · by_cases hj : i=src
            · subst i; simp [mid,hsd]
            · simp [mid,hi,hj]
        rw [hfinal] at hloop
        exact hloop

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

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

/-- A complete ordered bucket pass emits one actual vertex from every type. -/
theorem blockCommand_eval (i : ℕ) (entries : List Entry) (c : Context)
    (hblock : c.block = List.replicate i true)
    (hentries : ∀ e ∈ entries, i < e.2.length) (regs : Fin 8 → Bool) (suffix : List Bool) :
    ∃ n ≤ 3 + blockBudget i entries c, ∃ rf, Eval blockCommand n
      (ready regs { c with
        keys := ProgramEncoding.encodeRecords (entries.map entryWord) ++ suffix
        payload := [] })
      (ready rf { (emitEntries i entries c) with keys := suffix, payload := [] }) := by
  let a := base regs c
  obtain ⟨n, hn, rf, he⟩ := block_loop_eval i entries c hblock hentries regs suffix
  have hset := RecordPrograms.set_found_eval ports a (regs 5) (regs 6) (regs 7) false
    (ProgramEncoding.encodeRecords (entries.map entryWord) ++ suffix) []
  have hpop := RecordPrograms.pop_list_eval ports a (entries.map entryWord) suffix (regs 5) (regs 6)
  have hrun := hset.seq (hpop.seq he)
  refine ⟨1 + (1 + n), by omega, parserRegs rf false true false, ?_⟩
  simpa only [blockCommand, RecordPrograms.iterate, a, base, parser_state,
    parserRegs_self] using hrun

end SubexponentialSAT.Subexp.PackingExtraction

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

@[simp] theorem setCounter_same (i : Fin 3) (a : Accumulator) :
    setCounter i (counterWord i a) a = a := by
  fin_cases i <;> cases a <;> rfl

@[simp] theorem setCounter_setCounter (i : Fin 3) (x y : Word) (a : Accumulator) :
    setCounter i x (setCounter i y a) = setCounter i x a := by
  fin_cases i <;> rfl

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

/-! ## Forward-output service boundary -/

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameEmitter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def EmitterClean (a : Data) : Prop :=
  ∀ j : Fin 320, 256 ≤ j.val → j.val < 288 → j≠274 → a.stacks j=[]

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameReady
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete pre-state invariants for source dispatch. Metadata lookup and
whole-store comparisons preserve these low-bank arithmetic inputs. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open IntegerRingLiftProgram

def lowStore (a : Data) : Fin 256 → List Bool :=
  (projectState id vectorPorts a).stacks

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceDispatch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native control branches for source-polynomial lookup. Every literal and
conditional is executed; the universal-branch premise is an actual trace of
that fixed command and is supplied by the native table/emitter composition. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def CompareReady (a : Data) : Prop :=
  a.stacks 301=[] ∧ a.stacks 302=[] ∧ a.stacks 303=[] ∧ a.stacks 307=[]

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

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


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout

open Circuit Bank BinaryArithmetic Asymptotic

def guardedCode := code++GuardSetup.code

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramDispatchCost -/


end OAI.Algorithms
end


