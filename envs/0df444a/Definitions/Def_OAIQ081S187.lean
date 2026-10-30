-- Prove2me | Definitions.Def_OAIQ081S187
-- name    : OAIQ081S187
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:42:35.834755+00:00
-- url     : https://prove2.me/theorems/bc5beaf5-8e01-4183-9559-6f46a06e4fd1
-- title:
--   Definitions bundle OAIQ081S187 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 3 definitions and 6 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.hashBranchBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.tableBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.rawCommand`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallbackNative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorAssignmentCallbackNative.lean), [`SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureHeadLoaderCore.lean), [`SubexponentialSAT_SqrtLog_LeafRingSetupProgramDegree`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafRingSetupProgramDegree.lean), [`SubexponentialSAT_SqrtLog_LeafRingSetupProgramDegreeWide`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafRingSetupProgramDegreeWide.lean), [`SubexponentialSAT_SqrtLog_PackingCallerProgramCore`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingCallerProgramCore.lean), [`SubexponentialSAT_SqrtLog_PackingCallerProgramSelect`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingCallerProgramSelect.lean), [`SubexponentialSAT_SqrtLog_PackingProgramAssemblyScopeNative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingProgramAssemblyScopeNative.lean).
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S181`, `OAIQ081S182`, `OAIQ081S183`, `OAIQ081S184` and `OAIQ081S185` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S189` and `OAIQ081S190`; the statement `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.raw_eval`; the proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.raw_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S181
import Definitions.Def_OAIQ081S182
import Definitions.Def_OAIQ081S183
import Definitions.Def_OAIQ081S184
import Definitions.Def_OAIQ081S185

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallbackNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete physical inputs for the streamed factor callback. The source
context is the actual q.ctx, and the dispatcher determines every selected row
and clause. These predicates contain stored words and finite size bounds only.
Their construction from the actual loader/cache run remains an integration step. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open FactorAssignmentProgram
open Subexp.ConstructivePacking MulticolorTypes LayoutProgram DensePolynomialProgram

noncomputable section

variable {r Q n d A S : ℕ} {q : Factor.Spec r Q n d}
  {one seed : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d}
  {a : FactorAssignmentProgram.Data} {f : ℕ}

/-- The explicit paid ordinary-branch cost, on the exact dispatched state. -/
def hashBranchBudget (q : Factor.Spec r Q n d) (A S width : ℕ)
    (a : FactorAssignmentProgram.Data) (f : ℕ) (hf : f < q.rows.length) (rf : Fin 8 → Bool) : ℕ :=
  7 * (f + 1) + 7 +
    FactorAssignmentBranches.tableTime q.p q.u q.J n A S (fetched q a f rf) f +
    (9 * ((fetched q a f rf).stacks 154).length + 11 +
      HashInputProgram.Loop.uniformBudget q.p.t (d-1) q.bitWidth
        ((fetched q a f rf).stacks 707) q.clauses q.rows[f].length +
      FactorEvaluationSpace.serviceBudget (baseWidth 3 q.p.t) d n q.u q.J
        width q.rows[f].length q.digits.length)

/-- Uniform source-table work: the actual staged high-mask word is bounded
by the entry's physical word cap, independently of dispatcher registers. -/
def tableBudget (q : Factor.Spec r Q n d) (A S : ℕ) : ℕ :=
  1000000 * (A + n +
    FactorTableNative.specializedLiteralWork q.p q.u q.J n S (1029*A+99) +
    FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d + 1)^2

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed head-loader table uses the actual integer entry program. Its
physical matrix view follows LeafHeadSetupProgramHead/MatrixRun exactly, while
its controller emits one matrix and never constructs assignment tables. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

def rawCommand : Code :=
  stage (LayoutMatrixProgram.program entry) id (by decide) matrixInputs rawOutputs

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The complete fixed producer preserves the actual unary-true degree
word generated by numeric serialization. No byte shape is inferred from length. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls LeafParametersProgram SubexpLiftRing SubexpQuarticRing

theorem producerCommand_eval_degree (a : Data) (m : Circuit.Model)
    (w : Bank.Words) (r : Bank.Regs) (hs : Circuit.Shape m w)
    (ha : projectState (registers 8 (by decide)) parameters a=Bank.state r w)
    (initialWidth V bankWidth : ℕ)
    (hinit : ∀ i,(a.stacks i).length ≤ initialWidth)
    (hv : ∀ i,(Circuit.result Serialization.code m).val i ≤ V)
    (hw : ∀ i,(Circuit.result Serialization.code m).len i ≤ bankWidth)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34) :
    ∃ n ≤ producerBudget m initialWidth V bankWidth, ∃ e : Data,
      ∃ (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
        (cache : RingProgram.ScalarCache 3 (m.val 33))
        (u : RingProgram.ScalarCode 3 (m.val 33)),
      Eval producerCommand n a e ∧ Produced m hd M cache u e ∧
      (∀ i,320 ≤ i.val → i.val < 340 → e.stacks i=a.stacks i) ∧
      e.stacks 204=List.replicate (m.val 34) true := by
  let b0 := numberBudget m initialWidth V bankWidth
  let b1 := coreBudget (m.val 33) (m.val 34) bankWidth
  let w1 := initialWidth+b0+b1+1
  let b2 := constantsBudget w1 (baseWidth 3 (m.val 33)) (m.val 34)
  let w2 := w1+b2+1
  let b3 := nodesBudget w2 (m.val 33) (m.val 34) (m.val 21)
  let w3 := w2+b3+1
  let b4 := idempotentBudget (m.val 33) w3
  let w4 := w3+b4+1
  obtain ⟨n0,hn0,a0,w',he0,hshape,hinput,h191,h209,h243,h296,hbank,hcollector⟩ :=
    numberPhase_eval a m w r hs ha initialWidth V bankWidth (fun i _ => hinit i) hv hw
  have hval (i : Fin 64) (hi44 : i≠44) (hi45 : i≠45) :
      BinaryArithmetic.toNat (w' i)=m.val i :=
    (hshape.1 i).trans (Serialization.frame m i hi44 hi45)
  let depth := List.replicate (m.val 34) true
  have hdp : 0 < depth.length := by simpa [depth] using hd
  have hcoreInput : CoreInput (w' 33) depth a0 := by
    simpa [depth,hval 34 (by decide) (by decide)] using hinput
  have htword : CounterPrograms.value (w' 33)=m.val 33 := by
    simpa only [CounterPrograms.value_eq_toNat] using hval 33 (by decide) (by decide)
  obtain ⟨n1,hn1,a1,M,cache,u,he1,hcore,hcoreframe,hdegree1⟩ :=
    coreCommand_eval_degree a0 (w' 33) depth (m.val 33) ht hdp htword hcoreInput
  have hcore' : CoreOutput (m.val 33) (m.val 34) (IrreducibleSearch.data hd) M cache u a1 := by
    exact hcore.reindex (by simp [depth]) hdp hd
  have hn1' : n1 ≤ b1 := by
    simp only [depth,List.length_replicate] at hn1
    apply hn1.trans
    have hlen := (hshape.2 33).trans (hw 33)
    dsimp [b1]
    unfold coreBudget scalarBudget
    gcongr
  have hwidth1 : ∀ i,(a1.stacks i).length ≤ w1 := by
    intro i
    have hh := eval_width_le (he0.seq he1) hinit i
    dsimp [w1,b0]
    omega
  have hmeta1 (i : Fin 640) (hi : i∉coreWritePorts) : a1.stacks i=a0.stacks i := hcoreframe i hi
  obtain ⟨n2,hn2,a2,he2,hcache2,hcf⟩ := constantsPhase_produces a1 hcore' w1 hwidth1
  have hwidth2 : ∀ i,(a2.stacks i).length ≤ w2 := by
    intro i
    have hh := eval_width_le he2 hwidth1 i
    dsimp [w2,b2]
    omega
  have hmeta2 (i : Fin 640) (hi : i∉constantStartPorts)
      (hj : i∉([190,249,250,251] : List (Fin 640))) (hk : i∉coreWritePorts) :
      a2.stacks i=a0.stacks i := (hcf i ⟨hi,hj⟩).trans (hmeta1 i hk)
  have hq2 : BinaryArithmetic.toNat (a2.stacks 361)=m.val 21 := by
    rw [hmeta2 361 (by decide) (by decide) (by decide)]
    rw [show a0.stacks 361=w' 21 from hbank 21]
    exact hval 21 (by decide) (by decide)
  have hc2 : a2.stacks 296=List.replicate (m.val 21) true := by
    rw [hmeta2 296 (by decide) (by decide) (by decide),h296,hval 21 (by decide) (by decide)]
  have hz2 : a2.stacks 203=List.replicate (baseWidth 3 (m.val 33)) false :=
    hcache2.scalarZero.trans (IdempotentPreparationProgram.Scalar.canonical_zero_bytes _ _ hcache2.canonical)
  have hw2 : (a2.stacks 280).length=(m.val 34)*baseWidth 3 (m.val 33) := by
    rw [hcache2.fullZero,←LeafProgram.Constants.constantCode_flat,RingProgram.flat_length]
  obtain ⟨n3,hn3,a3,he3,hflat,hframed,hnf⟩ := nodesPhase_eval a2 (m.val 33) (m.val 34)
    (m.val 21) w2 ht hwidth2 hz2 hcache2.degree hq2 hc2 hw2
  have hcache3 := hcache2.frame (e:=a3) (by
    intro i hi
    apply hnf
    simp only [ringCachePorts,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
  have hwidth3 : ∀ i,(a3.stacks i).length ≤ w3 := by
    intro i
    have hh := eval_width_le he3 hwidth2 i
    dsimp [w3,b3]
    omega
  have ht3 : CounterPrograms.value (a3.stacks 373)=m.val 33 := by
    rw [hnf 373 (by decide),hmeta2 373 (by decide) (by decide) (by decide)]
    rw [show a0.stacks 373=w' 33 from hbank 33]
    exact htword
  obtain ⟨n4,hn4,a4,MI,cacheI,uI,he4,hidem,hiinv,hif⟩ :=
    idempotentPhase_eval a3 (m.val 33) w3 ht ht3 hwidth3
  have hcache4 := hcache3.frame (e:=a4) (by
    intro i hi
    apply hif
    simp only [ringCachePorts,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
  have hwidth4 : ∀ i,(a4.stacks i).length ≤ w4 := by
    intro i
    have hh := eval_width_le he4 hwidth3 i
    dsimp [w4,b4]
    omega
  obtain ⟨e,he5,hcache5,hnative,hclean,hff⟩ := finalCleanup_produces a4 hcache4
  have hn5 := clearPortsCost_bound finalDiscard a4 w4 (fun i _ => hwidth4 i)
  have hmeta (i : Fin 640) (hfin : i∉finalDiscard) (hid : i∉idempotentStartPorts)
      (hnd : i∉296::nodesStartPorts) (hcs : i∉constantStartPorts)
      (halias : i∉([190,249,250,251] : List (Fin 640))) (hco : i∉coreWritePorts) :
      e.stacks i=a0.stacks i :=
    (hff i hfin).trans ((hif i hid).trans ((hnf i hnd).trans (hmeta2 i hcs halias hco)))
  refine ⟨n0+n1+n2+n3+n4+(clearPortsCost finalDiscard a4+32),?_,e,M,cache,u,?_,?_,?_,?_⟩
  · change _ ≤ b0+b1+b2+b3+b4+finalDiscard.length*(2*w4+3)+32
    omega
  · simpa only [producerCommand,Nat.add_assoc] using
      he0.seq (he1.seq (he2.seq (he3.seq (he4.seq he5))))
  · refine ⟨hcache5,hnative,?_,?_,?_,?_,?_,?_,hclean⟩
    · rw [hmeta 191 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),h191,
        hval 0 (by decide) (by decide)]
    · rw [hmeta 209 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),h209,hshape.1 44]
    · rw [hmeta 243 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),h243,
        hval 42 (by decide) (by decide)]
    · rw [hff 256 (by decide),hif 256 (by decide),hflat]
    · rw [hff 300 (by decide),hif 300 (by decide),hframed]
    · exact ⟨MI,cacheI,uI,(hff 281 (by decide)).trans hidem,hiinv⟩
  · intro i hlo hhi
    obtain ⟨hf,hi,hn,hc,ha,hk⟩ := collector_not_touched i hlo hhi
    exact (hmeta i hf hi hn hc ha hk).trans (hcollector i hlo hhi)

  · have hf := (hff 204 (by decide)).trans
      ((hif 204 (by decide)).trans ((hnf 204 (by decide)).trans
        ((hcf 204 ⟨by decide,by decide⟩).trans hdegree1)))
    simpa only [depth] using hf

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramDegreeWide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact unary degree bytes of the existing producer, attached to an
arbitrary actual execution by deterministic endpoint uniqueness. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls LeafParametersProgram

theorem producerWideCall_degree
    (base out : StructuredProgram.State 40 768) (n : ℕ)
    (he : Eval producerWideCall n base out)
    (m : Circuit.Model) (w : Bank.Words) (r : Bank.Regs)
    (hs : Circuit.Shape m w)
    (ha : projectState (registers 8 (by decide)) parameters
      (projectState wideRegisters wideStacks base)=Bank.state r w)
    (W V L : ℕ) (hinit : ∀ i,(base.stacks i).length ≤ W)
    (hv : ∀ i,(Circuit.result Serialization.code m).val i ≤ V)
    (hw : ∀ i,(Circuit.result Serialization.code m).len i ≤ L)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34) :
    out.stacks 204=List.replicate (m.val 34) true := by
  let a := projectState wideRegisters wideStacks base
  obtain ⟨nc,hnc,e,M,cache,u,hec,hp,hcollector,hdegree⟩ :=
    producerCommand_eval_degree a m w r hs ha W V L
      (fun j => hinit (wideStacks j)) hv hw ht hd
  have hrun := compiled_halt_trace hec (parameters 0) 300
  have hwide : Eval producerWideCall (nc+1) base
      (embedState wideRegisters wideStacks base e) :=
    eval_call_from_state producerProgram wideRegisters wideStacks base
      wideRegisters_injective wideStacks_injective hrun
  have heq := SubexpPrimeProgram.eval_result_unique he hwide 0 0
  rw [heq]
  exact (embedState_stack wideRegisters wideStacks base e
    wideStacks_injective 204).trans hdegree

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyScopeNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact output and preserved high metadata for the native-scope controller. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem run_output (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) (hmask : mask.length ≤ n)
    {r Q : ℕ} [NeZero r] (a : Word r Q) (tail : List (Word r Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) (s : ℕ) (hs : 0 < s)
    (nb sb mb rb : List Bool) (hn : SubexponentialSAT.BinaryArithmetic.toNat nb=n)
    (hsb : SubexponentialSAT.BinaryArithmetic.toNat sb=s)
    (hmb : SubexponentialSAT.BinaryArithmetic.toNat mb=(PackingIncidenceInput.Semantics.nativeEntries scopes mask).length)
    (hrb : SubexponentialSAT.BinaryArithmetic.toNat rb=r)
    (d : Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail
      (n+PackingIncidenceInput.Semantics.factorCount scopes mask) [] d.stacks)
    (hc : (d.stacks 11).length=n+PackingIncidenceInput.Semantics.factorCount scopes mask)
    (he : SequentialProgram.HighState (env scopes n mask a tail nb sb mb rb) d.stacks) :
    ∃ e : Data, RunsIn (SequentialProgram.program Assembly.command)
      (cost scopes n mask a tail s nb sb mb rb)
      (d.withPC (some (SequentialProgram.program Assembly.command).entry)) (e.withPC none) ∧
      Finished (rows scopes n mask hmask a tail s hs (NeZero.pos r)) d e := by
  obtain ⟨e,ht,hmem,hc',he'⟩ := run scopes n mask hmask a tail haN haC s hs
    nb sb mb rb hn hsb hmb hrb d hm hc he
  refine ⟨e,ht,?_,hc',hmem.alphabet.trans hm.alphabet.symm,
    hmem.width.trans hm.width.symm,?_,hmem.scratch,?_⟩
  · simpa [rows] using hmem.assignment
  · simpa only [rows,List.length_map,List.length_reverse] using hmem.processed
  · intro j hj
    exact (he' j hj).trans (he j hj).symm

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramSelect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Run the concrete weighted selector while retaining the literal width and
alphabet for the native packing-layout suffix. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram

theorem selection_eval (outside : Store) (d : Small)
    (h52 : outside 52=[]) (h53 : outside 53=[]) (h54 : outside 54=[]) (h62 : outside 62=[])
    (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) (hmask : mask.length ≤ n)
    {r Q : ℕ} [NeZero r] (a : Word r Q) (tail : List (Word r Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) (s : ℕ) (hs : 0 < s)
    (hn : SubexponentialSAT.BinaryArithmetic.toNat (outside 56)=n)
    (hsb : SubexponentialSAT.BinaryArithmetic.toNat (outside 57)=s)
    (hmb : SubexponentialSAT.BinaryArithmetic.toNat (outside 58)=
      (PackingIncidenceInput.Semantics.nativeEntries scopes mask).length)
    (hrb : SubexponentialSAT.BinaryArithmetic.toNat (outside 59)=r)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail
      (n+PackingIncidenceInput.Semantics.factorCount scopes mask) [] d.stacks)
    (hc : (d.stacks 11).length=n+PackingIncidenceInput.Semantics.factorCount scopes mask)
    (he : SequentialProgram.HighState
      (PackingProgram.Assembly.Scope.env scopes n mask a tail
        (outside 56) (outside 57) (outside 58) (outside 59)) d.stacks) :
    let rows := PackingProgram.Assembly.Scope.rows scopes n mask hmask a tail s hs (NeZero.pos r)
    ∃ t rf, t ≤ selectionBudget d rows
      (PackingProgram.Assembly.Scope.cost scopes n mask a tail s
        (outside 56) (outside 57) (outside 58) (outside 59)) ∧
      Eval selection t (framed outside d)
        (framed (Function.update (cached outside (d.stacks 10) (d.stacks 39)) 62 rows.flatten)
          (⟨rf,fun _=>[]⟩ : Small)) := by
  dsimp only
  let rows := PackingProgram.Assembly.Scope.rows scopes n mask hmask a tail s hs (NeZero.pos r)
  let saved := cached outside (d.stacks 10) (d.stacks 39)
  obtain ⟨rc,hcache⟩ := cacheInputs_eval outside d h52 h53 h54
  obtain ⟨e,⟨nt,hnt,ht⟩,hfinished⟩ := PackingProgram.Assembly.Scope.run_output scopes n mask hmask
    a tail haN haC s hs (outside 56) (outside 57) (outside 58) (outside 59)
    hn hsb hmb hrb (setRegs d rc) hm hc he
  have hcall := framed_call (SequentialProgram.program PackingProgram.Assembly.command) saved ht
  obtain ⟨rs,hsave⟩ := saveHigh_eval saved e 8 62 (by decide) (by decide)
    (by simpa [saved] using h52) (by simpa [saved,cached] using h62)
  have hrows : e.stacks 8=rows.flatten := hfinished.1
  rw [hrows] at hsave
  obtain ⟨rf,hclear⟩ := clearLow_run (Function.update saved 62 rows.flatten) (setRegs e rs)
  have hinput : ∀ i,((setRegs d rc).stacks i).length ≤ selectionSize d rows := by
    intro i
    have h := dataMass_bound d i
    dsimp [setRegs,selectionSize]
    omega
  have hb := PackingProgram.Assembly.Scope.Finished.length_bound (rows := rows) (B := selectionSize d rows) hfinished
    hinput
    (by dsimp [selectionSize]; omega) (by dsimp [selectionSize]; omega)
  have hclean := clearLowBudget_le (setRegs e rs) (selectionSize d rows) hb
  refine ⟨(7*(d.stacks 10).length+5+(7*(d.stacks 39).length+5))+
      (nt+((7*rows.flatten.length+5)+clearLowBudget (setRegs e rs))),rf,?_,?_⟩
  · dsimp only [rows] at hclean ⊢
    dsimp only [selectionBudget]
    omega
  · exact hcache.seq (hcall.seq (hsave.seq hclear))

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! All local computation is now composed: native plans and pairs, actual
word selection, and the native layout metadata suffix. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

theorem core_eval (outside : Store) (p : Problem) (hp : Parameters outside p)
    (hw : Workspace outside) (regs : Fin 16 → Bool)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (hrows : (a::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes p.r p.Q)
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) :
    ∃ t rf, t+1 ≤ coreBudget outside p a tail ∧ Eval core t
      (framed outside (Install.input regs p.scopes p.n p.mask))
      (framed (outputStore outside p a tail) (⟨rf,fun _=>[]⟩ : Small)) := by
  let : NeZero p.r := ⟨Nat.ne_of_gt p.hr⟩
  obtain ⟨tp,rp,htp,hpRun⟩ := produce_eval outside regs p.scopes p.n p.mask hw.temp hw.plans
  obtain ⟨tl,rl,htl,hl⟩ := PackingLoaderProgram.command_eval (planStore outside p) rp
    (Scan.scopeBits p.scopes) p.n p.mask.length p.factors (PairScoreProgram.pairRecords p.raw)
    (by simpa [planStore] using hw.scopes)
    (by simpa [planStore,hp.radius] using p.hr)
  have hinput : rawInput (planStore outside p) rp (Scan.scopeBits p.scopes) p.n
      p.mask.length p.factors (PairScoreProgram.pairRecords p.raw) =
      framed (planStore outside p) (Endpoint.result rp p.scopes p.n p.mask) := rfl
  have hl' : Eval PackingLoaderProgram.command tl
      (framed (planStore outside p) (Endpoint.result rp p.scopes p.n p.mask))
      (framed (loadedStore outside p) (ready outside p rl)) := by
    rw [← hinput]
    simpa [loadedStore,planStore,ready,
      Problem.factors,Problem.raw,PackingProgram.Assembly.Scope.raw,hp.radius,hp.coordinate]
      using hl
  have hm := ready_memory rl a tail hrows p.n p.factors
    (PairScoreProgram.pairRecords p.raw) (outside 56) (outside 57) (outside 58) (outside 59)
  have hc := ready_remaining rl p.r p.Q p.n p.factors
    (PairScoreProgram.pairRecords p.raw) (outside 56) (outside 57) (outside 58) (outside 59)
  have he := ready_high rl a tail hrows p.n p.factors p.raw
    (outside 56) (outside 57) (outside 58) (outside 59)
  obtain ⟨ts,rs,hts,hsRun⟩ := selection_eval (loadedStore outside p) (ready outside p rl)
    (by simpa [loadedStore,planStore] using hw.temp)
    (by simpa [loadedStore,planStore] using hw.width)
    (by simpa [loadedStore,planStore] using hw.alphabet)
    (by simpa [loadedStore,planStore] using hw.words)
    p.scopes p.n p.mask p.mask_le a tail haN haC p.s p.hs
    (by simpa [loadedStore,planStore] using hp.ambient)
    (by simpa [loadedStore,planStore] using hp.epsilon)
    (by simpa [loadedStore,planStore,Problem.incidences] using hp.incidence)
    (by simpa [loadedStore,planStore] using hp.radius)
    hm hc (by simpa [loadedStore,planStore,ready,PackingProgram.Assembly.Scope.env,Problem.raw,
      Problem.factors] using he)
  have h10 : (ready outside p rl).stacks 10=List.replicate (p.Q*p.r) true := by
    simp [ready,readyLocal,AssignmentInitProgram.outputState,AssignmentInitProgram.state,
      PackingLoaderProgram.context,AssignmentInputProgram.context,AssignmentInputProgram.unary]
  have h39 : (ready outside p rl).stacks 39=
      ProgramEncoding.encodeRecords (AssignmentAlphabetSemantics.wordBytes p.r p.Q) := by
    simp [ready,readyLocal,AssignmentInitProgram.outputState,AssignmentInitProgram.state,
      PackingLoaderProgram.context,AssignmentInputProgram.context]
  have hsRun' : Eval selection ts (framed (loadedStore outside p) (ready outside p rl))
      (framed (selectedStore outside p a tail) (⟨rs,fun _=>[]⟩ : Small)) := by
    simpa only [h10,h39,selectedStore,Problem.words,PackingProgram.Assembly.Scope.rows] using hsRun
  obtain ⟨tf,rf,htf,hf⟩ := suffix_eval (selectedStore outside p a tail) rs (p.spec a tail)
    (p.spec_depth a tail)
    (by simpa [selectedStore,cached,loadedStore,planStore] using hw.temp)
    (by simpa [selectedStore,cached,loadedStore,planStore] using hw.metadata)
    (by simpa [selectedStore,cached,loadedStore,planStore] using hp.incidence)
    (by simp [selectedStore,cached])
    (by simp [selectedStore,cached])
    (by rw [p.spec_plans]; simp [selectedStore,cached,loadedStore,planStore])
    (by simp [selectedStore])
  refine ⟨tp+(tl+(ts+tf)),rf,?_,hpRun.seq (hl'.seq (hsRun'.seq hf))⟩
  have hreadyBudget (rows : List (List Bool)) (cost : ℕ) :
      selectionBudget (ready outside p rl) rows cost =
        selectionBudget (ready outside p (fun _=>false)) rows cost := rfl
  rw [hreadyBudget] at hts
  have hts' : ts ≤ selectionBudget (ready outside p (fun _=>false))
      ((p.words a tail).map ReadPlan.encodeWord)
      (PackingProgram.Assembly.Scope.cost p.scopes p.n p.mask a tail p.s
        (outside 56) (outside 57) (outside 58) (outside 59)) := by
    simpa [selectionBudget,selectionSize,dataMass,ready,loadedStore,planStore,
      Problem.words,PackingProgram.Assembly.Scope.rows] using hts
  unfold coreBudget
  omega

theorem core_run (outside : Store) (p : Problem) (hp : Parameters outside p)
    (hw : Workspace outside) (regs : Fin 16 → Bool)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (hrows : (a::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes p.r p.Q)
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) :
    ∃ rf, RunsIn coreProgram (coreBudget outside p a tail)
      ((framed outside (Install.input regs p.scopes p.n p.mask)).withPC (some coreProgram.entry))
      ((framed (outputStore outside p a tail) (⟨rf,fun _=>[]⟩ : Small)).withPC none) := by
  obtain ⟨t,rf,ht,he⟩ := core_eval outside p hp hw regs a tail hrows haN haC
  exact ⟨rf,t+1,ht,compiled_halt_trace he 32 63⟩

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end


